const VERSION = '1.0.1';

const dropZone = document.getElementById('drop-zone');
const fileInput = document.getElementById('file-input');
const status = document.getElementById('status');
const canvas = document.getElementById('mapCanvas');
const openGpxButton = document.getElementById('open-gpx-button');
const undoButton = document.getElementById('undo-button');
const redoButton = document.getElementById('redo-button');
const zoomOriginButton = document.getElementById('zoom-origin-button');
const saveDownloadButton = document.getElementById('save-download-button');
const discardCloseButton = document.getElementById('discard-close-button');
const ctx = canvas.getContext('2d');
const progressSlider = document.getElementById('progress-slider');

// slider render scheduling
let _sliderRaf = null;
function scheduleSliderRender() {
  if (_sliderRaf) cancelAnimationFrame(_sliderRaf);
  _sliderRaf = requestAnimationFrame(() => { _sliderRaf = null; renderCurrentTrack(); });
}

function updateProgressSliderLimits(triggerRender = true, toMax = false) {
  if (!progressSlider) return;
  progressSlider.max = currentTrackPoints ? currentTrackPoints.length - 1 : 0;
  if (toMax)
    progressSlider.value = progressSlider.max;
  else
    progressSlider.value = progressSlider.value > progressSlider.max ? progressSlider.max : progressSlider.value;
  if (triggerRender) scheduleSliderRender();
}

let currentTrackPoints = [];
let originalTrackPointCount = 0;
let loadedFileName = '';
let originalMetadataXml = '';
const selectedPointIds = new Set();
const historyState = {
  undo: [],
  redo: [],
};
const viewport = {
  scale: 1,
  offsetX: 0,
  offsetY: 0,
  originX: 0,
  originY: 0,
};

const activePointers = new Map();
let dragStart = null;
let pinchStart = null;
let isPanning = false;
let selectionBox = null;
let selectedMoveStart = null;
let suppressClick = false;
const dragThreshold = 8;
const pointSelectionRadius = 16;
let currentMoveDrag = null;
let lastClickTime = 0;
let lastClickX = 0;
let lastClickY = 0;

function clamp(value, min, max) {
  return Math.min(Math.max(value, min), max);
}

// Web Mercator (EPSG:3857) helpers
const WEB_MERCATOR_HALF_WORLD = 20037508.342789244;
function lonToMercX(lon) {
  return (lon * WEB_MERCATOR_HALF_WORLD) / 180;
}

function latToMercY(lat) {
  const y = Math.log(Math.tan((90 + lat) * Math.PI / 360)) / (Math.PI / 180);
  return (y * WEB_MERCATOR_HALF_WORLD) / 180;
}

function mercXToLon(x) {
  return (x / WEB_MERCATOR_HALF_WORLD) * 180;
}

function mercYToLat(y) {
  const yDeg = (y / WEB_MERCATOR_HALF_WORLD) * 180;
  const lat = (180 / Math.PI) * (2 * Math.atan(Math.exp(yDeg * Math.PI / 180)) - Math.PI / 2);
  return lat;
}

function screenToWorld(x, y) {
  return {
    x: (x - viewport.offsetX) / viewport.scale + viewport.originX,
    y: viewport.originY - (y - viewport.offsetY) / viewport.scale,
  };
}

function worldToScreen(x, y) {
  return {
    x: (x - viewport.originX) * viewport.scale + viewport.offsetX,
    y: (viewport.originY - y) * viewport.scale + viewport.offsetY,
  };
}

function getPointerDistance(a, b) {
  return Math.hypot(b.x - a.x, b.y - a.y);
}

function getPointerMidpoint(a, b) {
  return {
    x: (a.x + b.x) / 2,
    y: (a.y + b.y) / 2,
  };
}

function getCanvasPoint(event) {
  const rect = canvas.getBoundingClientRect();
  return {
    x: (event.clientX - rect.left) * (canvas.width / rect.width),
    y: (event.clientY - rect.top) * (canvas.height / rect.height),
  };
}

function setStatus(message, isError = false) {
  status.textContent = message;
  status.style.color = isError ? '#b91c1c' : '#374151';
}

function setAppVisible(hasFile) {
  dropZone.classList.toggle('has-file', hasFile);
}

function cloneTrackPoints(trackPoints) {
  return trackPoints.map((point) => ({ ...point }));
}

function rebuildTrackLinks(trackPoints) {
  for (let i = 0; i < trackPoints.length; i += 1) {
    trackPoints[i].id = i;
    trackPoints[i].prev = i > 0 ? trackPoints[i - 1] : null;
    trackPoints[i].next = i < trackPoints.length - 1 ? trackPoints[i + 1] : null;
  }
}

function snapshotTrackState() {
  return {
    points: cloneTrackPoints(currentTrackPoints),
    selected: Array.from(selectedPointIds),
    progressSlidervalue: progressSlider.value,
    progressSlidermax: progressSlider.max,
  };
}

function restoreTrackState(snapshot) {
  if (!snapshot) {
    return;
  }

  currentTrackPoints = cloneTrackPoints(snapshot.points);
  rebuildTrackLinks(currentTrackPoints);
  selectedPointIds.clear();
  snapshot.selected.forEach((id) => selectedPointIds.add(id));
  renderCurrentTrack();
  if (loadedFileName) {
    updateStatusText(loadedFileName);
  }
  progressSlider.value = snapshot.progressSlidervalue;
  progressSlider.max = snapshot.progressSlidermax;
  updateProgressSliderLimits();
}

function updateHistoryButtons() {
  undoButton.disabled = historyState.undo.length === 0;
  redoButton.disabled = historyState.redo.length === 0;
  updateBeforeUnloadWarning();
}

function recordHistorySnapshot() {
  historyState.undo.push(snapshotTrackState());
  historyState.redo = [];
  updateHistoryButtons();
}

function undoLastAction() {
  if (!historyState.undo.length) {
    return;
  }

  const current = snapshotTrackState();
  const previous = historyState.undo.pop();
  historyState.redo.push(current);
  restoreTrackState(previous);
  updateHistoryButtons();
}

function redoLastAction() {
  if (!historyState.redo.length) {
    return;
  }

  const current = snapshotTrackState();
  const next = historyState.redo.pop();
  historyState.undo.push(current);
  restoreTrackState(next);
  updateHistoryButtons();
}

function isMacOS() {
  return navigator.platform.toUpperCase().includes('MAC');
}

function matchesShortcut(event, key, requireShift = false) {
  const usesMetaModifier = isMacOS() ? event.metaKey : event.ctrlKey;

  return usesMetaModifier
    && event.key.toLowerCase() === key.toLowerCase()
    && !!event.shiftKey === !!requireShift
    && !event.altKey;
}

function hasPendingEdits() {
  return historyState.undo.length > 0 || historyState.redo.length > 0;
}

function updateBeforeUnloadWarning() {
  if (hasPendingEdits()) {
    window.onbeforeunload = function (event) {
      event.preventDefault();
      event.returnValue = '';
      return '';
    };
  } else {
    window.onbeforeunload = null;
  }
}

function isSupportedFile(file) {
  if (!file) {
    return false;
  }

  const name = file.name.toLowerCase();
  return name.endsWith('.gpx');
}

function extractOriginalMetadata(xmlDoc) {
  const metadataNode = xmlDoc.getElementsByTagName('metadata')[0];
  return metadataNode ? metadataNode.outerHTML : '';
}

function parseGpxTrack(xmlText) {
  const parser = new DOMParser();
  const xmlDoc = parser.parseFromString(xmlText, 'application/xml');
  const parseError = xmlDoc.querySelector('parsererror');

  if (parseError) {
    throw new Error('Invalid GPX XML');
  }

  originalMetadataXml = extractOriginalMetadata(xmlDoc);

  const trackPoints = [...xmlDoc.querySelectorAll('trkpt')].map((node, index) => {
    const lat = Number(node.getAttribute('lat'));
    const lon = Number(node.getAttribute('lon'));
    const eleText = node.querySelector('ele');
    const elevation = eleText ? Number(eleText.textContent.trim()) : null;

    return {
      id: index,
      latitude: lat,
      longitude: lon,
      mercX: lonToMercX(lon),
      mercY: latToMercY(lat),
      elevation: elevation,
      prev: null,
      next: null,
    };
  });

  for (let i = 1; i < trackPoints.length; i += 1) {
    trackPoints[i - 1].next = trackPoints[i];
    trackPoints[i].prev = trackPoints[i - 1];
  }

  return trackPoints;
}

function resizeCanvasToDisplay() {
  const displayWidth = Math.max(1, Math.round(canvas.clientWidth || canvas.width || 1000));
  const displayHeight = Math.max(1, Math.round(canvas.clientHeight || canvas.height || 500));

  if (canvas.width !== displayWidth || canvas.height !== displayHeight) {
    canvas.width = displayWidth;
    canvas.height = displayHeight;
  }
}

function getProjectedPoints(trackPoints) {
  return trackPoints.map((point) => {
    const screen = worldToScreen(point.mercX, point.mercY);
    return { ...point, x: screen.x, y: screen.y };
  });
}

function renderTrack(trackPoints) {
  ctx.clearRect(0, 0, canvas.width, canvas.height);

  drawMapTiles(ctx);

  if (!trackPoints.length) {
    ctx.fillStyle = '#111827';
    ctx.font = '16px Arial';
    ctx.fillText('No track points available.', 20, 30);
    return;
  }

  let points = getProjectedPoints(trackPoints);
  for (let i = 0; i < points.length; i++) {
    const point = points[i];

    ctx.beginPath();
    ctx.arc(point.x, point.y, 3.5, 0, Math.PI * 2);
    ctx.fillStyle = '#880000';
    ctx.fill();

    if (selectedPointIds.has(point.id)) {
      ctx.beginPath();
      ctx.arc(point.x, point.y, 7, 0, Math.PI * 2);
      ctx.strokeStyle = '#facc15';
      ctx.lineWidth = 3;
      ctx.stroke();
    }

    if (i > 0) {
      const prev_point = points[i - 1];
      ctx.strokeStyle = '#ff0000';
      ctx.lineWidth = 2.5;
      ctx.beginPath();
      ctx.moveTo(prev_point.x, prev_point.y);
      ctx.lineTo(point.x, point.y);
      ctx.stroke();
    }

    if (i >= progressSlider.value) {
      let j = i + 1;
      for (; j < points.length; j++) {
        selectedPointIds.forEach((pointId) => {
          if (pointId == points[j].id) {
            selectedPointIds.delete(pointId);
          }
        });
      }
      break;
    }
  }

  if (selectionBox) {
    const { x, y, w, h } = selectionBox;
    ctx.strokeStyle = '#111827';
    ctx.lineWidth = 1;
    ctx.setLineDash([6, 6]);
    ctx.strokeRect(x, y, w, h);
    ctx.setLineDash([]);
  }

  const start = points[0];
  const end = points[points.length - 1];

  ctx.fillStyle = '#880000';
  ctx.font = '24px Arial';
  ctx.fillText('Start', start.x + 8, start.y - 8);
  if (progressSlider.value == points.length - 1) {
    ctx.fillText('End', end.x + 8, end.y - 8);
  }
}

function updateStatusText(fileName) {
  const currentCount = currentTrackPoints.length;
  const originalCount = originalTrackPointCount || currentCount;

  setStatus(`${fileName} - Original: ${originalCount} Points - Now: ${currentCount} Points`);
}

function handleGpxText(text, fileName) {
  loadedFileName = fileName;
  originalMetadataXml = '';
  historyState.undo = [];
  historyState.redo = [];

  try {
    const trackPoints = parseGpxTrack(text);

    if (!trackPoints.length) {
      originalTrackPointCount = 0;
      currentTrackPoints = [];
      selectedPointIds.clear();
      setAppVisible(false);
      setStatus('No GPX track points found in the file.', true);
      return;
    }

    currentTrackPoints = trackPoints;
    originalTrackPointCount = trackPoints.length;
    selectedPointIds.clear();
    setAppVisible(true);
    fitTrackToView();
    updateProgressSliderLimits(true, true);
    renderTrack(trackPoints);
    updateStatusText(fileName);
    updateHistoryButtons();
  } catch (error) {
    setAppVisible(false);
    setStatus('The selected file is not valid GPX.', true);
    console.error(error);
  }
}

function loadFile(file) {
  if (!isSupportedFile(file)) {
    alert('Please drop a .gpx file.');
    setStatus('Please drop a .gpx file.', true);
    return;
  }

  const reader = new FileReader();

  reader.onload = function (event) {
    const text = event.target.result || '';
    handleGpxText(text, file.name);
  };

  reader.onerror = function () {
    setStatus('The file could not be read.', true);
  };

  reader.readAsText(file);

  historyState.undo = [];
  historyState.redo = [];
}

function renderCurrentTrack() {
  updateProgressSliderLimits(false);
  if (currentTrackPoints.length) {
    renderTrack(currentTrackPoints);
  }
}

function togglePointSelection(pointId, isShiftSelection) {
  recordHistorySnapshot();

  if (isShiftSelection) {
    if (selectedPointIds.has(pointId)) {
      selectedPointIds.delete(pointId);
    } else {
      selectedPointIds.add(pointId);
    }
    renderCurrentTrack();
    return;
  }

  if (selectedPointIds.has(pointId)) {
    selectedPointIds.delete(pointId);
  } else {
    selectedPointIds.clear();
    selectedPointIds.add(pointId);
  }

  renderCurrentTrack();
}

function getTrackCanvasBounds(trackPoints) {
  const minLat = Math.min(...trackPoints.map((point) => point.latitude));
  const maxLat = Math.max(...trackPoints.map((point) => point.latitude));
  const minLon = Math.min(...trackPoints.map((point) => point.longitude));
  const maxLon = Math.max(...trackPoints.map((point) => point.longitude));

  const latRange = Math.max(maxLat - minLat, 0.000001);
  const lonRange = Math.max(maxLon - minLon, 0.000001);

  const xs = trackPoints.map((point) => ((point.longitude - minLon) / lonRange) * canvas.width);
  const ys = trackPoints.map((point) => ((point.latitude - minLat) / latRange) * canvas.height);

  return {
    minX: Math.min(...xs),
    maxX: Math.max(...xs),
    minY: Math.min(...ys),
    maxY: Math.max(...ys),
  };
}

function getMinZoomScale() {
  if (!currentTrackPoints.length) {
    return 1 / 1.15;
  }

  // Ensure canvas size is up to date
  resizeCanvasToDisplay();

  // Use same margin as fitTrackToView so "fit" and min zoom match
  const margin = 0.12;
  const ranges = getTrackLatLonRanges(currentTrackPoints);

  const usableWidth = canvas.width * (1 - margin * 2);
  const usableHeight = canvas.height * (1 - margin * 2);

  // Compute scale as pixels per mercator meter
  const minScale = Math.min(usableWidth / ranges.mercWidth, usableHeight / ranges.mercHeight);

  return Math.max(minScale, 1e-12);
}

function getMaxZoomScale() {
  // Ensure maxScale is always larger than minScale to avoid inverted clamps
  const min = getMinZoomScale();
  // Allow up to a generous zoom-in factor relative to fit scale
  const factor = 50;
  const max = Math.max(min * factor, min + 1, 100);
  return max;
}

function fitTrackToView() {
  if (!currentTrackPoints.length) {
    return;
  }

  resizeCanvasToDisplay();
  const ranges = getTrackLatLonRanges(currentTrackPoints);
  const margin = 0.12;
  const usableWidth = canvas.width * (1 - margin * 2);
  const usableHeight = canvas.height * (1 - margin * 2);
  const scale = Math.min(usableWidth / ranges.mercWidth, usableHeight / ranges.mercHeight);

  viewport.originX = ranges.minMercX;
  // originY is the top (max) mercator Y so that screen Y increases downward
  viewport.originY = ranges.maxMercY;
  viewport.scale = scale;

  const centerX = (ranges.minMercX + ranges.maxMercX) / 2;
  const centerY = (ranges.minMercY + ranges.maxMercY) / 2;
  viewport.offsetX = canvas.width / 2 - (centerX - ranges.minMercX) * scale;
  // offsetY aligns center by accounting that worldToScreen uses originY - y
  viewport.offsetY = canvas.height / 2 - (viewport.originY - centerY) * scale;
}

function setZoomAtPoint(nextScale, targetX, targetY) {
  const minScale = getMinZoomScale();
  const maxScale = getMaxZoomScale();

  if (nextScale <= minScale) {
    fitTrackToView();
    renderCurrentTrack();
    return;
  }

  const worldBefore = screenToWorld(targetX, targetY);
  const nextScaleClamped = clamp(nextScale, minScale, maxScale);

  // compute offsets so the world point under the screen cursor remains fixed
  // worldToScreen(x,y): sx = (x - originX)*scale + offsetX
  //                      sy = (originY - y)*scale + offsetY
  viewport.scale = nextScaleClamped;
  viewport.offsetX = targetX - (worldBefore.x - viewport.originX) * viewport.scale;
  viewport.offsetY = targetY - (viewport.originY - worldBefore.y) * viewport.scale;

  renderCurrentTrack();
}

function zoomToCurrentTrackOriginView() {
  if (!currentTrackPoints.length) {
    return;
  }

  fitTrackToView();
  renderCurrentTrack();
}

function getEditedFileName(fileName) {
  if (!fileName) {
    return 'Route EDITED.gpx';
  }

  const dotIndex = fileName.lastIndexOf('.');
  if (dotIndex <= 0) {
    return `${fileName} EDITED.gpx`;
  }

  return `${fileName.slice(0, dotIndex)} EDITED${fileName.slice(dotIndex)}`;
}

function promptForSaveFileName() {
  const defaultName = getEditedFileName(loadedFileName || 'route.gpx');
  const userInput = window.prompt('Save route as:', defaultName);
  if (userInput === null) {
    return null;
  }

  const trimmed = userInput.trim();
  return trimmed || defaultName;
}

function buildCurrentTrackGpxXml() {
  if (!currentTrackPoints.length) {
    return null;
  }

  const metadataBlock = originalMetadataXml ? `  ${originalMetadataXml.replace(/\n/g, '\n  ')}\n` : '';
  const lines = [
    '<?xml version="1.0" encoding="UTF-8"?>',
    `<gpx version="1.1" creator="ReRoute ${VERSION}" xmlns="http://www.topografix.com/GPX/1/1">`,
    metadataBlock.trim() ? metadataBlock.trim() : '',
    '  <trk>',
    '    <trkseg>',
  ];

  currentTrackPoints.forEach((point) => {
    const lat = Number(point.latitude).toFixed(8);
    const lon = Number(point.longitude).toFixed(8);
    const elevation = point.elevation == null ? '' : `\n      <ele>${Number(point.elevation).toFixed(3)}</ele>`;
    lines.push(`    <trkpt lat="${lat}" lon="${lon}">${elevation}\n    </trkpt>`);
  });

  lines.push('    </trkseg>');
  lines.push('  </trk>');
  lines.push('</gpx>');

  return lines.filter((line) => line !== '').join('\n');
}

function saveCurrentTrackAsGpx() {
  if (!currentTrackPoints.length) {
    setStatus('There is no route to save yet.', true);
    return;
  }

  const xmlText = buildCurrentTrackGpxXml();
  if (!xmlText) {
    return;
  }

  const safeFileName = promptForSaveFileName();
  if (!safeFileName) {
    return;
  }

  const blob = new Blob([xmlText], { type: 'application/gpx+xml;charset=utf-8' });
  const url = URL.createObjectURL(blob);
  const anchor = document.createElement('a');
  anchor.href = url;
  anchor.download = safeFileName;
  document.body.appendChild(anchor);
  anchor.click();
  anchor.remove();
  URL.revokeObjectURL(url);
  setStatus(`${safeFileName} downloaded`);

  historyState.undo = [];
  historyState.redo = [];
  updateHistoryButtons();
}

function selectPointsInBox(box, additive = false) {
  if (!currentTrackPoints.length || !box) {
    return;
  }

  const points = getProjectedPoints(currentTrackPoints);
  const selected = new Set(additive ? Array.from(selectedPointIds) : []);

  points.forEach((point) => {
    const withinX = point.x >= Math.min(box.x, box.x + box.w) && point.x <= Math.max(box.x, box.x + box.w);
    const withinY = point.y >= Math.min(box.y, box.y + box.h) && point.y <= Math.max(box.y, box.y + box.h);

    if (withinX && withinY) {
      selected.add(point.id);
    }
  });

  recordHistorySnapshot();

  selectedPointIds.clear();
  selected.forEach((id) => selectedPointIds.add(id));

  renderCurrentTrack();
}

function deleteSelectedPoints() {
  if (!currentTrackPoints.length || selectedPointIds.size === 0) {
    return;
  }

  recordHistorySnapshot();
  updateProgressSliderLimits();

  progressSlider.value -= selectedPointIds.size;
  if (progressSlider.value < 0) progressSlider.value = 0;

  const remaining = currentTrackPoints.filter((point) => !selectedPointIds.has(point.id));

  const fileName = loadedFileName || 'GPX';

  if (remaining.length === 0) {
    currentTrackPoints = [];
    selectedPointIds.clear();
    renderCurrentTrack();
    setStatus(`${fileName} - Original: ${originalTrackPointCount} - Now: 0`);
    return;
  }

  const rebuiltPoints = remaining.map((point, index) => ({
    ...point,
    id: index,
    prev: null,
    next: null,
  }));

  for (let i = 1; i < rebuiltPoints.length; i += 1) {
    rebuiltPoints[i - 1].next = rebuiltPoints[i];
    rebuiltPoints[i].prev = rebuiltPoints[i - 1];
  }

  currentTrackPoints = rebuiltPoints;

  selectedPointIds.clear();
  renderCurrentTrack();
  setStatus(`${fileName} - Original: ${originalTrackPointCount} - Now: ${currentTrackPoints.length}`);
  updateStatusText(fileName);
}

function getTrackLatLonRanges(trackPoints) {
  const minLat = Math.min(...trackPoints.map((point) => point.latitude));
  const maxLat = Math.max(...trackPoints.map((point) => point.latitude));
  const minLon = Math.min(...trackPoints.map((point) => point.longitude));
  const maxLon = Math.max(...trackPoints.map((point) => point.longitude));

  const minMercX = Math.min(...trackPoints.map((p) => p.mercX));
  const maxMercX = Math.max(...trackPoints.map((p) => p.mercX));
  const minMercY = Math.min(...trackPoints.map((p) => p.mercY));
  const maxMercY = Math.max(...trackPoints.map((p) => p.mercY));

  return {
    minLat,
    maxLat,
    minLon,
    maxLon,
    latRange: Math.max(maxLat - minLat, 0.000001),
    lonRange: Math.max(maxLon - minLon, 0.000001),
    minMercX,
    maxMercX,
    minMercY,
    maxMercY,
    mercWidth: Math.max(maxMercX - minMercX, 1e-12),
    mercHeight: Math.max(maxMercY - minMercY, 1e-12),
  };
}

function getPointerDragDeltaInGeo(startPointer, endPointer) {
  if (!currentTrackPoints.length) {
    return { deltaLat: 0, deltaLon: 0 };
  }

  const startX = startPointer.x ?? startPointer.pointerX ?? 0;
  const startY = startPointer.y ?? startPointer.pointerY ?? 0;
  const endX = endPointer.x ?? endPointer.pointerX ?? 0;
  const endY = endPointer.y ?? endPointer.pointerY ?? 0;

  const startWorld = screenToWorld(startX, startY);
  const endWorld = screenToWorld(endX, endY);

  return {
    deltaMercX: endWorld.x - startWorld.x,
    deltaMercY: endWorld.y - startWorld.y,
  };
}

function moveSelectedPointsByDelta(deltaLat, deltaLon) {
  if (!currentTrackPoints.length || selectedPointIds.size === 0) {
    return;
  }

  // deltaX/deltaY are in mercator meters
  const deltaX = deltaLat;
  const deltaY = deltaLon;
  if (deltaX === 0 && deltaY === 0) {
    return;
  }

  const updated = currentTrackPoints.map((point) => {
    if (!selectedPointIds.has(point.id)) {
      return point;
    }

    const newMercX = point.mercX + deltaX;
    const newMercY = point.mercY + deltaY;

    return {
      ...point,
      mercX: newMercX,
      mercY: newMercY,
      latitude: mercYToLat(newMercY),
      longitude: mercXToLon(newMercX),
    };
  });

  currentTrackPoints = updated;
  renderCurrentTrack();
}

function isPointerOnSelectedPoint(pointer) {
  if (!currentTrackPoints.length) {
    return false;
  }

  const projected = getProjectedPoints(currentTrackPoints);
  return projected.some((point) => {
    const distance = Math.hypot(pointer.x - point.x, pointer.y - point.y);
    return selectedPointIds.has(point.id) && distance <= pointSelectionRadius;
  });
}

function isPointerOnRouteSegment(pointer) {
  if (!currentTrackPoints.length) {
    return false;
  }

  const projected = getProjectedPoints(currentTrackPoints);

  for (let i = 0; i < projected.length - 1; i += 1) {
    const a = projected[i];
    const b = projected[i + 1];
    const dx = b.x - a.x;
    const dy = b.y - a.y;
    const segmentLengthSquared = dx * dx + dy * dy || 1;
    const projection = clamp(((pointer.x - a.x) * dx + (pointer.y - a.y) * dy) / segmentLengthSquared, 0, 1);
    const projectedX = a.x + dx * projection;
    const projectedY = a.y + dy * projection;
    const distance = Math.hypot(pointer.x - projectedX, pointer.y - projectedY);

    if (distance <= 16) {
      return true;
    }
  }

  return false;
}

function updateCanvasCursor(pointer) {
  if (!pointer) {
    canvas.style.cursor = 'default';
    return;
  }

  const onSelectedPoint = isPointerOnSelectedPoint(pointer);
  const onRouteLine = isPointerOnRouteSegment(pointer);

  if (isPanning) {
    canvas.style.cursor = 'grab';
    return;
  }

  if (onSelectedPoint) {
    canvas.style.cursor = 'move';
    return;
  }

  canvas.style.cursor = onRouteLine ? 'crosshair' : 'default';
}

function insertPointOnTrack(pointer) {
  if (!currentTrackPoints.length) {
    return null;
  }

  recordHistorySnapshot();

  const points = getProjectedPoints(currentTrackPoints);
  let closest = null;

  for (let i = 0; i < points.length - 1; i += 1) {
    const a = points[i];
    const b = points[i + 1];
    const dx = b.x - a.x;
    const dy = b.y - a.y;
    const segmentLengthSquared = dx * dx + dy * dy || 1;
    const projection = clamp(((pointer.x - a.x) * dx + (pointer.y - a.y) * dy) / segmentLengthSquared, 0, 1);
    const projectedX = a.x + dx * projection;
    const projectedY = a.y + dy * projection;
    const distance = Math.hypot(pointer.x - projectedX, pointer.y - projectedY);

    if (!closest || distance < closest.distance) {
      closest = {
        distance,
        index: i,
        t: projection,
      };
    }
  }

  if (!closest || closest.distance > 16) {
    return null;
  }

  const previousPoint = currentTrackPoints[closest.index];
  const nextPoint = currentTrackPoints[closest.index + 1];
  const t = closest.t;
  // interpolate in mercator space for geographic correctness
  const lat = null;
  const lon = null;
  const mercX = previousPoint.mercX + (nextPoint.mercX - previousPoint.mercX) * t;
  const mercY = previousPoint.mercY + (nextPoint.mercY - previousPoint.mercY) * t;
  const interpLat = mercYToLat(mercY);
  const interpLon = mercXToLon(mercX);

  let elevation = null;
  if (previousPoint.elevation != null && nextPoint.elevation != null) {
    elevation = previousPoint.elevation + (nextPoint.elevation - previousPoint.elevation) * t;
  } else if (previousPoint.elevation != null) {
    elevation = previousPoint.elevation;
  } else if (nextPoint.elevation != null) {
    elevation = nextPoint.elevation;
  }

  const newPoint = {
    id: currentTrackPoints.length,
    latitude: interpLat,
    longitude: interpLon,
    mercX: mercX,
    mercY: mercY,
    elevation,
    prev: previousPoint,
    next: nextPoint,
  };

  const updated = currentTrackPoints.slice();
  updated.splice(closest.index + 1, 0, newPoint);

  for (let i = 0; i < updated.length; i += 1) {
    updated[i].id = i;
    updated[i].prev = i > 0 ? updated[i - 1] : null;
    updated[i].next = i < updated.length - 1 ? updated[i + 1] : null;
  }

  currentTrackPoints = updated;
  originalTrackPointCount = currentTrackPoints.length;
  selectedPointIds.clear();
  selectedPointIds.add(newPoint.id);
  updateProgressSliderLimits();
  if (progressSlider.value < progressSlider.max)
    progressSlider.value++;
  renderCurrentTrack();
  updateStatusText('GPX');
  return newPoint;
}

canvas.addEventListener('wheel', function (event) {
  event.preventDefault();
  const pointer = getCanvasPoint(event);
  const delta = event.deltaY < 0 ? 1.12 : 0.88;
  setZoomAtPoint(viewport.scale * delta, pointer.x, pointer.y);
}, { passive: false });

canvas.addEventListener('pointerdown', function (event) {
  event.preventDefault();
  canvas.setPointerCapture(event.pointerId);
  const pointer = getCanvasPoint(event);
  activePointers.set(event.pointerId, { x: pointer.x, y: pointer.y });
  suppressClick = false;

  const wantsPan = event.shiftKey || event.code === 'Space' || event.key === ' ';
  const hitSelectedPoint = getProjectedPoints(currentTrackPoints).find((point) => {
    const distance = Math.hypot(pointer.x - point.x, pointer.y - point.y);
    return selectedPointIds.has(point.id) && distance <= pointSelectionRadius;
  });

  if (activePointers.size === 1) {
    dragStart = {
      x: pointer.x,
      y: pointer.y,
      offsetX: viewport.offsetX,
      offsetY: viewport.offsetY,
    };
    pinchStart = null;
    selectionBox = null;
    selectedMoveStart = null;
    currentMoveDrag = null;

    if (hitSelectedPoint && selectedPointIds.has(hitSelectedPoint.id)) {
      selectedMoveStart = {
        x: pointer.x,
        y: pointer.y,
      };
      // Record a single snapshot for the drag start; will be used for undo
      recordHistorySnapshot();
      currentMoveDrag = { moved: false };
    } else if (wantsPan) {
      selectionBox = {
        x: pointer.x,
        y: pointer.y,
        w: 0,
        h: 0,
        additive: !!event.shiftKey,
      };
    }
  }

  if (activePointers.size === 2) {
    const [first, second] = [...activePointers.values()];
    pinchStart = {
      center: getPointerMidpoint(first, second),
      distance: getPointerDistance(first, second),
      scale: viewport.scale,
    };
    selectionBox = null;
    selectedMoveStart = null;
  }

  updateCanvasCursor({ ...pointer, shiftKey: event.shiftKey, code: event.code, key: event.key });
});

canvas.addEventListener('click', function (event) {
  if (suppressClick) {
    suppressClick = false;
    return;
  }

  if (isPanning || !currentTrackPoints.length) {
    isPanning = false;
    return;
  }

  const pointer = getCanvasPoint(event);
  const points = getProjectedPoints(currentTrackPoints);
  const clickedPoint = points.reduce((closest, point) => {
    const distance = Math.hypot(pointer.x - point.x, pointer.y - point.y);
    if (distance <= pointSelectionRadius && (!closest || distance < closest.distance)) {
      return { point, distance };
    }
    return closest;
  }, null);

  // Custom double-click detection: two clicks in quick succession near same location
  const now = Date.now();
  const clickDist = Math.hypot(pointer.x - lastClickX, pointer.y - lastClickY);
  const isDouble = lastClickTime && (now - lastClickTime) < 350 && clickDist < 20;
  lastClickTime = now;
  lastClickX = pointer.x;
  lastClickY = pointer.y;

  if (isDouble) {
    lastClickTime = 0;
    if (!clickedPoint) {
      event.preventDefault();
      const nextScale = clamp(viewport.scale * 1.6, getMinZoomScale(), getMaxZoomScale());
      setZoomAtPoint(nextScale, pointer.x, pointer.y);
    }
    return;
  }

  if (clickedPoint) {
    if (event.shiftKey) {
      togglePointSelection(clickedPoint.point.id, true);
    } else if (!selectedPointIds.has(clickedPoint.point.id)) {
      recordHistorySnapshot();
      selectedPointIds.clear();
      selectedPointIds.add(clickedPoint.point.id);
      renderCurrentTrack();
    }
    return;
  }

  const inserted = insertPointOnTrack(pointer);
  if (inserted) {
    return;
  }

  selectedPointIds.clear();
  renderCurrentTrack();
});

// NOTE: native dblclick behavior removed; using click-based double-click detection below.

canvas.addEventListener('pointermove', function (event) {
  if (!activePointers.has(event.pointerId)) {
    return;
  }

  const pointer = getCanvasPoint(event);
  activePointers.set(event.pointerId, { x: pointer.x, y: pointer.y });
  updateCanvasCursor({ ...pointer, shiftKey: event.shiftKey, code: event.code, key: event.key });

  if (activePointers.size === 1 && dragStart) {
    const dx = pointer.x - dragStart.x;
    const dy = pointer.y - dragStart.y;
    const wantsPan = event.shiftKey || event.code === 'Space' || event.key === ' ';

    if (selectedMoveStart && selectedPointIds.size > 0 && !wantsPan) {
      suppressClick = true;
      const nextDelta = getPointerDragDeltaInGeo(selectedMoveStart, pointer);
      if (nextDelta.deltaMercX !== 0 || nextDelta.deltaMercY !== 0) {
        if (currentMoveDrag) {
          currentMoveDrag.moved = true;
        }
        moveSelectedPointsByDelta(nextDelta.deltaMercX, nextDelta.deltaMercY);
        selectedMoveStart.x = pointer.x;
        selectedMoveStart.y = pointer.y;
      }
      return;
    }

    if (wantsPan) {
      if (selectionBox && (Math.abs(dx) > 1 || Math.abs(dy) > 1)) {
        suppressClick = true;
      }
      selectionBox = {
        x: dragStart.x,
        y: dragStart.y,
        w: dx,
        h: dy,
        additive: !!event.shiftKey,
      };
      renderCurrentTrack();
      return;
    }

    if (!isPanning && (Math.abs(dx) > dragThreshold || Math.abs(dy) > dragThreshold)) {
      isPanning = true;
      suppressClick = true;
    }

    if (isPanning) {
      viewport.offsetX = dragStart.offsetX + dx;
      viewport.offsetY = dragStart.offsetY + dy;
      renderCurrentTrack();
    }
  }

  if (activePointers.size >= 2 && pinchStart) {
    isPanning = true;
    suppressClick = true;
    selectionBox = null;
    const [first, second] = [...activePointers.values()];
    const nextCenter = getPointerMidpoint(first, second);
    const nextDistance = getPointerDistance(first, second);
    const newScale = pinchStart.scale * (nextDistance / Math.max(pinchStart.distance, 0.0001));

    const centerWorld = screenToWorld(pinchStart.center.x, pinchStart.center.y);
    const minScale = getMinZoomScale();
    const maxScale = getMaxZoomScale();

    if (newScale <= minScale) {
      fitTrackToView();
      renderCurrentTrack();
      pinchStart.center = nextCenter;
      pinchStart.distance = nextDistance;
      return;
    }

    const clamped = clamp(newScale, minScale, maxScale);
    // compute offsets so the world point at pinchStart.center remains fixed
    viewport.scale = clamped;
    viewport.offsetX = pinchStart.center.x - (centerWorld.x - viewport.originX) * viewport.scale;
    viewport.offsetY = pinchStart.center.y - (viewport.originY - centerWorld.y) * viewport.scale;

    viewport.offsetX += nextCenter.x - pinchStart.center.x;
    viewport.offsetY += nextCenter.y - pinchStart.center.y;
    pinchStart.center = nextCenter;
    pinchStart.distance = nextDistance;
    renderCurrentTrack();
  }
});

function endPointer(event) {
  activePointers.delete(event.pointerId);

  if (activePointers.size === 0) {
    if (selectionBox && (Math.abs(selectionBox.w) > 2 || Math.abs(selectionBox.h) > 2)) {
      selectPointsInBox(selectionBox, !!selectionBox.additive);
    }
    selectionBox = null;
    dragStart = null;
    pinchStart = null;
    // If we recorded a snapshot at drag start but no movement occurred, remove it
    if (currentMoveDrag && !currentMoveDrag.moved) {
      historyState.undo.pop();
      updateHistoryButtons();
    }
    currentMoveDrag = null;
    selectedMoveStart = null;
    isPanning = false;
    renderCurrentTrack();
    return;
  }

  if (activePointers.size === 1) {
    const [remainingPointer] = [...activePointers.values()];
    dragStart = {
      x: remainingPointer.x,
      y: remainingPointer.y,
      offsetX: viewport.offsetX,
      offsetY: viewport.offsetY,
    };
    pinchStart = null;
    selectedMoveStart = null;
    currentMoveDrag = null;
    isPanning = false;
  }

  updateCanvasCursor({ x: canvas.width / 2, y: canvas.height / 2, shiftKey: false, code: '', key: '' });
}

canvas.addEventListener('pointerup', endPointer);
canvas.addEventListener('pointercancel', endPointer);
window.addEventListener('keydown', function (event) {
  if (event.key === 'Backspace' || event.code === 'Backspace') {
    if (selectedPointIds.size > 0) {
      event.preventDefault();
      deleteSelectedPoints();
    }
    return;
  }

  if (matchesShortcut(event, 's')) {
    if (currentTrackPoints.length) {
      event.preventDefault();
      saveCurrentTrackAsGpx();
    }
    return;
  }

  if (matchesShortcut(event, '0')) {
    if (currentTrackPoints.length) {
      event.preventDefault();
      zoomToCurrentTrackOriginView();
    }
    return;
  }

  if (matchesShortcut(event, 'z')) {
    event.preventDefault();
    undoLastAction();
    return;
  }

  if (matchesShortcut(event, 'z', true)) {
    event.preventDefault();
    redoLastAction();
    return;
  }

  if (event.code === 'Space' || event.key === 'Shift') {
    renderCurrentTrack();
    updateCanvasCursor({ x: canvas.width / 2, y: canvas.height / 2, shiftKey: event.shiftKey || event.code === 'Space' || event.key === ' ', code: event.code, key: event.key });
  }
});
window.addEventListener('keyup', function (event) {
  if (event.code === 'Space' || event.key === 'Shift') {
    renderCurrentTrack();
    updateCanvasCursor({ x: canvas.width / 2, y: canvas.height / 2, shiftKey: false, code: event.code, key: event.key });
  }
});
canvas.addEventListener('pointerleave', function (event) {
  if (event.pointerType !== 'mouse' || event.buttons !== 0) {
    return;
  }
  endPointer(event);
  canvas.style.cursor = 'default';
});

window.addEventListener('resize', function () {
  resizeCanvasToDisplay();
  if (currentTrackPoints.length) {
    fitTrackToView();
    renderCurrentTrack();
  }
});

['dragenter', 'dragover'].forEach(function (eventName) {
  window.addEventListener(eventName, function (event) {
    event.preventDefault();
    dropZone.classList.add('dragging');
  });
});

['dragleave', 'drop'].forEach(function (eventName) {
  window.addEventListener(eventName, function (event) {
    event.preventDefault();
    dropZone.classList.remove('dragging');
  });
});

window.addEventListener('drop', function (event) {
  event.preventDefault();
  const file = event.dataTransfer && event.dataTransfer.files && event.dataTransfer.files[0];
  if (!file) {
    return;
  }

  if (hasPendingEdits()) {
    const proceed = window.confirm('There are unsaved edits. Discard changes and load the new file?');
    if (!proceed) {
      return;
    }
  }

  loadFile(file);
});

openGpxButton.addEventListener('click', function () {
  fileInput.click();
});

fileInput.addEventListener('change', function (event) {
  const file = event.target.files && event.target.files[0];
  loadFile(file);
});

undoButton.addEventListener('click', function () {
  undoLastAction();
});

redoButton.addEventListener('click', function () {
  redoLastAction();
});

zoomOriginButton.addEventListener('click', function () {
  zoomToCurrentTrackOriginView();
});

saveDownloadButton.addEventListener('click', function () {
  saveCurrentTrackAsGpx();
});

discardCloseButton.addEventListener('click', function () {
  const confirmed = window.confirm('Discard the current route and close the editor?');
  if (confirmed) {
    window.location.reload();
  }
});

resizeCanvasToDisplay();
setAppVisible(false);
updateHistoryButtons();

// Initialize slider limits and wire input events
updateProgressSliderLimits(false);
if (progressSlider) {
  progressSlider.addEventListener('input', () => scheduleSliderRender());
  progressSlider.addEventListener('change', () => scheduleSliderRender());
}


// Tile management
const tileCache = new Map();
const TILE_SIZE = 256;

// Swiss WMTS layer names (defaults; may be overridden by GetCapabilities discovery)
let swissLayer25k = 'ch.swisstopo.pixelkarte-farbe-pk25.noscale';

// Attempt to discover available Swiss WMTS layers via GetCapabilities
async function discoverSwissLayers() {
  try {
    const capsUrl = 'https://wmts.geo.admin.ch/1.0.0/WMTSCapabilities.xml';
    const resp = await fetch(capsUrl);
    if (!resp.ok) {
      console.warn('Failed to fetch WMTS capabilities', resp.status);
      return;
    }
    const text = await resp.text();
    const parser = new DOMParser();
    const xml = parser.parseFromString(text, 'application/xml');
    const idNodes = [...xml.querySelectorAll('Layer > Identifier')];
    const ids = idNodes.map((n) => n.textContent.trim());
    console.debug('Discovered WMTS layer identifiers:', ids);
  } catch (e) {
    console.warn('Error discovering Swiss WMTS layers', e);
  }
}

// Kick off WMTS layer discovery (non-blocking)
discoverSwissLayers().catch(() => { });

function getTileUrl(z, x, y, layer) {
  const chosenLayer = layer || swissLayer25k;
  const time = 'current';
  const tileMatrixSet = '3857';
  const idx = Math.abs(x + y) % 3;
  return `https://wmts${idx}.geo.admin.ch/1.0.0/${chosenLayer}/default/${time}/${tileMatrixSet}/${z}/${x}/${y}.jpeg`;
}

function loadTile(z, x, y, providerKey) {
  const key = `${providerKey}:${z}:${x}:${y}`;
  if (tileCache.has(key)) return tileCache.get(key);

  const img = new Image();
  img.crossOrigin = 'Anonymous';
  const parts = providerKey.split(':');
  const layer = parts.length > 1 ? parts[1] : undefined;
  const url = getTileUrl(z, x, y, layer);
  img.src = url;
  img.onload = function () { renderCurrentTrack(); };
  img.onerror = function (e) { console.warn('Tile load error', url, e); renderCurrentTrack(); };
  tileCache.set(key, img);
  return img;
}

function drawMapTiles(ctx) {
  if (!canvas.width || !canvas.height) return;

  // determine visible mercator bounds
  const topLeft = screenToWorld(0, 0);
  const bottomRight = screenToWorld(canvas.width, canvas.height);

  const minX = Math.min(topLeft.x, bottomRight.x);
  const maxX = Math.max(topLeft.x, bottomRight.x);
  const minY = Math.min(topLeft.y, bottomRight.y);
  const maxY = Math.max(topLeft.y, bottomRight.y);

  // choose zoom level based on viewport.scale and WebMercator world size
  const zFloat = Math.log2((viewport.scale * 2 * WEB_MERCATOR_HALF_WORLD) / TILE_SIZE);
  // Choose zoom level conservatively: pick ceil of zFloat so tiles aren't oversized
  let z = Math.max(0, Math.min(17, Math.ceil(zFloat)));

  const tilesPerWorld = Math.pow(2, z);
  const tileMercSize = (2 * WEB_MERCATOR_HALF_WORLD) / tilesPerWorld;

  // choose swiss layer based on viewport.scale thresholds
  // Use the user's hardcoded high-resolution layer for all zooms
  let chosenLayer = swissLayer25k;
  const providerKey = `swiss:${chosenLayer}`;

  const tileXMin = Math.floor((minX + WEB_MERCATOR_HALF_WORLD) / tileMercSize);
  const tileXMax = Math.floor((maxX + WEB_MERCATOR_HALF_WORLD) / tileMercSize);
  const tileYMax = Math.floor((WEB_MERCATOR_HALF_WORLD - minY) / tileMercSize);
  const tileYMin = Math.floor((WEB_MERCATOR_HALF_WORLD - maxY) / tileMercSize);

  for (let tx = tileXMin; tx <= tileXMax; tx += 1) {
    for (let ty = tileYMin; ty <= tileYMax; ty += 1) {
      if (tx < 0 || ty < 0 || tx >= tilesPerWorld || ty >= tilesPerWorld) continue;
      const img = loadTile(z, tx, ty, providerKey);

      const tileMinMercX = -WEB_MERCATOR_HALF_WORLD + tx * tileMercSize;
      const tileMaxMercY = WEB_MERCATOR_HALF_WORLD - ty * tileMercSize;
      const tileMinMercY = tileMaxMercY - tileMercSize;

      // top-left corner of the tile in world mercator coords is (tileMinMercX, tileMaxMercY)
      const topLeft = worldToScreen(tileMinMercX, tileMaxMercY);
      const screenX = topLeft.x;
      const screenY = topLeft.y;
      const screenSize = tileMercSize * viewport.scale;

      try {
        if (img && img.complete && img.naturalWidth && img.naturalHeight) {
          ctx.drawImage(img, screenX, screenY, screenSize, screenSize);
        } else {
          // draw a subtle filled placeholder while tiles load or on error
          ctx.fillStyle = '#f2f4f6';
          ctx.fillRect(screenX, screenY, screenSize, screenSize);
        }
      } catch (e) {
        // ignore draw errors but draw subtle placeholder
        ctx.fillStyle = '#f2f4f6';
        ctx.fillRect(screenX, screenY, screenSize, screenSize);
      }
    }
  }

  // Debug overlay: show chosen zoom and scale info
  if (0) {
    ctx.fillStyle = 'rgba(255,255,255,0.8)';
    ctx.fillRect(8, 8, 260, 92);
    ctx.fillStyle = '#111827';
    ctx.font = '12px Arial';
    const tilesPerWorld = Math.pow(2, z);
    const tileMercSize = (2 * WEB_MERCATOR_HALF_WORLD) / tilesPerWorld;
    ctx.fillText(`z=${z} tileMerc=${Math.round(tileMercSize)}m`, 12, 26);
    ctx.fillText(`viewport.scale=${viewport.scale.toFixed(4)} px/m`, 12, 44);
    ctx.fillText(`tileScreenPx=${(tileMercSize * viewport.scale).toFixed(1)} px`, 12, 62);
    if (currentTrackPoints.length) {
      const ranges = getTrackLatLonRanges(currentTrackPoints);
      ctx.fillText(`mercWidth=${Math.round(ranges.mercWidth)} m`, 12, 80);
    }
    if (chosenLayer) {
      ctx.fillText(`layer=${chosenLayer}`, 12, 98);
    }
  }
}
