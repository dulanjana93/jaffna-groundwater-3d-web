import * as THREE from 'three';
import { GLTFLoader }     from 'three/addons/loaders/GLTFLoader.js';
import { OrbitControls }  from 'three/addons/controls/OrbitControls.js';
import { EffectComposer } from 'three/addons/postprocessing/EffectComposer.js';
import { RenderPass }     from 'three/addons/postprocessing/RenderPass.js';
import { OutlinePass }    from 'three/addons/postprocessing/OutlinePass.js';

// ── STATE ──────────────────────────────────────────────────────────────
let scene, renderer, camera, controls, composer, outlinePass;
let oceanParts = [], cloudMeshes = [], interactiveBlocks = [];
let oceanBottomRoot = null;
let oceanTopRoot = null;
let propsModel; // <--- Add this here
let baseGround, baseWithHoles;
let currentStage = 1, isIsolated = false;
let isRainy = false;

let labelP1, labelP2, arrowPump1Left, arrowPump1Right;
let pump1ArrowsRising = false;
let lastPumpStation1Val = 0;

const pumpData = { p1_t:0, p1_c:0, p2_t:0, p2_c:0, speed:0.04 };
const cloudMat = new THREE.MeshStandardMaterial({ color:0x8C8C8C, transparent:true, opacity:0 });

// ── MODEL SETTINGS (shared across all tabs, sea.html-compatible) ────────
let isSettingsMode = false;
let settingsStageBefore = 1;
const PRESET_STORAGE_KEY = 'jaffnaModelPresets_v1';
const DEFAULT_MODEL_SETTINGS = {
  waveHeight: 0.14,
  waveFreq: 2.8,
  waveSpeed: 2.0,
  rainCount: 600,
  rainLength: 0.40,
  windX: 1.5,
  windZ: 0.0,
  rainTop: 3.2,
  rainBottom: -1.0,
  key4: 0,
  key5: 0,
  drySeason: 1,
  cloudOpacity: 0
};
let modelSettings = { ...DEFAULT_MODEL_SETTINGS };
let activePresetSlot = -1;
let presetSlots = [null, null, null, null];

const sharedWaveUniforms = {
  uTime: { value: 0 },
  uWaveHeight: { value: DEFAULT_MODEL_SETTINGS.waveHeight },
  uWaveFrequency: { value: DEFAULT_MODEL_SETTINGS.waveFreq },
  uWaveSpeed: { value: DEFAULT_MODEL_SETTINGS.waveSpeed }
};

let morphTargetsCollection = [];
let cloudMaterialsCollection = [cloudMat];
let rainLines = null;
const maxRaindrops = 1500;
let individualSpeeds = new Float32Array(maxRaindrops);
const rainBaseSpeedMultiplier = 6.0;
const rainBounds = {
  minX: -8, maxX: 8,
  minY: DEFAULT_MODEL_SETTINGS.rainBottom,
  maxY: DEFAULT_MODEL_SETTINGS.rainTop,
  minZ: -8, maxZ: 8
};

// --- SHADER COMPILER ENGINE (same as sea.html) ---
function applyUnifiedWaveShader(material, targetColorHex) {
  material.color.setHex(targetColorHex);
  material.roughness = 0.15;
  material.metalness = 0.1;
  material.transparent = true;
  material.opacity = 0.85;

  material.onBeforeCompile = (shader) => {
    shader.uniforms.uTime = sharedWaveUniforms.uTime;
    shader.uniforms.uWaveHeight = sharedWaveUniforms.uWaveHeight;
    shader.uniforms.uWaveFrequency = sharedWaveUniforms.uWaveFrequency;
    shader.uniforms.uWaveSpeed = sharedWaveUniforms.uWaveSpeed;

    shader.vertexShader = `
      attribute float _surface;
      attribute float surface;
      uniform float uTime;
      uniform float uWaveHeight;
      uniform float uWaveFrequency;
      uniform float uWaveSpeed;
    \n` + shader.vertexShader;

    shader.vertexShader = shader.vertexShader.replace(
      '#include <begin_vertex>',
      `
      #include <begin_vertex>
      
      float mask = max(_surface, surface);
      
      if(mask == 0.0) {
          mask = step(0.9, normal.y);
      }

      if (mask > 0.0) {
          float wave = sin(position.x * uWaveFrequency + uTime * uWaveSpeed) * cos(position.z * uWaveFrequency * 0.9 + uTime * uWaveSpeed * 1.1);
          transformed.y += wave * uWaveHeight * mask;
      }
      `
    );
  };
}

function registerMorphTargets(root) {
  root.traverse(c => {
    if (c.isMesh && c.morphTargetDictionary) morphTargetsCollection.push(c);
  });
}

function resetRaindrop(positions, index) {
  const x = THREE.MathUtils.randFloat(rainBounds.minX, rainBounds.maxX);
  const y = THREE.MathUtils.randFloat(rainBounds.minY, rainBounds.maxY);
  const z = THREE.MathUtils.randFloat(rainBounds.minZ, rainBounds.maxZ);
  individualSpeeds[index] = THREE.MathUtils.randFloat(0.7, 1.4);
  const baseIdx = index * 6;
  positions[baseIdx] = x;
  positions[baseIdx + 1] = y;
  positions[baseIdx + 2] = z;
  positions[baseIdx + 3] = x - modelSettings.windX * modelSettings.rainLength * 0.1;
  positions[baseIdx + 4] = y - modelSettings.rainLength;
  positions[baseIdx + 5] = z - modelSettings.windZ * modelSettings.rainLength * 0.1;
}

function createRainEngine() {
  if (rainLines) return;
  const positions = new Float32Array(maxRaindrops * 6);
  for (let i = 0; i < maxRaindrops; i++) resetRaindrop(positions, i);
  const geometry = new THREE.BufferGeometry();
  geometry.setAttribute('position', new THREE.BufferAttribute(positions, 3));
  const material = new THREE.LineBasicMaterial({
    color: 0x8bb8e2,
    transparent: true,
    opacity: 0.5,
    depthWrite: false
  });
  rainLines = new THREE.LineSegments(geometry, material);
  rainLines.visible = false;
  scene.add(rainLines);
  rainLines.geometry.setDrawRange(0, modelSettings.rainCount * 2);
}

function updateRainEngine(deltaTime) {
  if (!rainLines || !rainLines.visible) return;
  const positions = rainLines.geometry.attributes.position.array;
  const sharedBaseSpeed = sharedWaveUniforms.uWaveSpeed.value * rainBaseSpeedMultiplier;
  for (let i = 0; i < maxRaindrops; i++) {
    const baseIdx = i * 6;
    const customFallSpeed = sharedBaseSpeed * individualSpeeds[i];
    positions[baseIdx]     -= modelSettings.windX * customFallSpeed * 0.1 * deltaTime;
    positions[baseIdx + 1] -= customFallSpeed * deltaTime;
    positions[baseIdx + 2] -= modelSettings.windZ * customFallSpeed * 0.1 * deltaTime;
    if (positions[baseIdx + 1] < rainBounds.minY) {
      positions[baseIdx + 1] = rainBounds.maxY;
      positions[baseIdx]     = THREE.MathUtils.randFloat(rainBounds.minX, rainBounds.maxX);
      positions[baseIdx + 2] = THREE.MathUtils.randFloat(rainBounds.minZ, rainBounds.maxZ);
      individualSpeeds[i] = THREE.MathUtils.randFloat(0.7, 1.4);
    }
    positions[baseIdx + 3] = positions[baseIdx]     - (modelSettings.windX * modelSettings.rainLength * 0.15);
    positions[baseIdx + 4] = positions[baseIdx + 1] - modelSettings.rainLength;
    positions[baseIdx + 5] = positions[baseIdx + 2] - (modelSettings.windZ * modelSettings.rainLength * 0.15);
  }
  rainLines.geometry.attributes.position.needsUpdate = true;
}

function setMorphByName(keyName, value) {
  morphTargetsCollection.forEach(mesh => {
    if (!mesh.morphTargetDictionary || !mesh.morphTargetInfluences) return;
    const index = mesh.morphTargetDictionary[keyName];
    if (index !== undefined) mesh.morphTargetInfluences[index] = value;
  });
  oceanParts.forEach(m => setMorph(m, keyName, value));
}

function applyModelSettings(settings, { syncUI = true, syncPumps = true } = {}) {
  modelSettings = { ...DEFAULT_MODEL_SETTINGS, ...settings };

  sharedWaveUniforms.uWaveHeight.value = modelSettings.waveHeight;
  sharedWaveUniforms.uWaveFrequency.value = modelSettings.waveFreq;
  sharedWaveUniforms.uWaveSpeed.value = modelSettings.waveSpeed;

  rainBounds.minY = modelSettings.rainBottom;
  rainBounds.maxY = modelSettings.rainTop;
  if (rainLines) {
    rainLines.geometry.setDrawRange(0, modelSettings.rainCount * 2);
    rainLines.visible = isSettingsMode
      ? modelSettings.rainCount > 0
      : (isRainy && modelSettings.rainCount > 0);
  }

  setMorphByName('Key 4', modelSettings.key4);
  setMorphByName('Key 5', modelSettings.key5);
  setMorphByName('dry season', modelSettings.drySeason);

  cloudMaterialsCollection.forEach(mat => { mat.opacity = modelSettings.cloudOpacity; });
  cloudMat.opacity = modelSettings.cloudOpacity;

  if (syncPumps) {
    pumpData.p1_t = modelSettings.key4;
    pumpData.p1_c = modelSettings.key4;
    pumpData.p2_t = modelSettings.key5;
    pumpData.p2_c = modelSettings.key5;
    const d1 = document.getElementById('dialP1');
    const d2 = document.getElementById('dialP2');
    if (d1) d1.value = modelSettings.key4;
    if (d2) d2.value = modelSettings.key5;
    if (typeof refreshPumpUI === 'function') {
      try { refreshPumpUI(); } catch (_) {}
    }
  }

  if (syncUI) syncSettingsUIFromState();
}

function syncSettingsUIFromState() {
  const map = [
    ['ms-wave-height', 'ms-wave-height-val', 'waveHeight', v => v.toFixed(2)],
    ['ms-wave-freq', 'ms-wave-freq-val', 'waveFreq', v => v.toFixed(1)],
    ['ms-wave-speed', 'ms-wave-speed-val', 'waveSpeed', v => v.toFixed(1)],
    ['ms-rain-count', 'ms-rain-count-val', 'rainCount', v => String(Math.round(v))],
    ['ms-rain-length', 'ms-rain-length-val', 'rainLength', v => v.toFixed(2)],
    ['ms-wind-x', 'ms-wind-x-val', 'windX', v => v.toFixed(1)],
    ['ms-wind-z', 'ms-wind-z-val', 'windZ', v => v.toFixed(1)],
    ['ms-rain-top', 'ms-rain-top-val', 'rainTop', v => v.toFixed(1)],
    ['ms-rain-bottom', 'ms-rain-bottom-val', 'rainBottom', v => v.toFixed(1)],
    ['ms-shape-key-4', 'ms-shape-key-4-val', 'key4', v => v.toFixed(2)],
    ['ms-shape-key-5', 'ms-shape-key-5-val', 'key5', v => v.toFixed(2)],
    ['ms-shape-key-dry', 'ms-shape-key-dry-val', 'drySeason', v => v.toFixed(2)],
    ['ms-cloud-opacity', 'ms-cloud-opacity-val', 'cloudOpacity', v => v.toFixed(2)],
  ];
  map.forEach(([id, valId, key, fmt]) => {
    const input = document.getElementById(id);
    const label = document.getElementById(valId);
    if (!input || !label) return;
    input.value = modelSettings[key];
    label.textContent = fmt(modelSettings[key]);
  });
}

function readSettingsFromUI() {
  return {
    waveHeight: parseFloat(document.getElementById('ms-wave-height').value),
    waveFreq: parseFloat(document.getElementById('ms-wave-freq').value),
    waveSpeed: parseFloat(document.getElementById('ms-wave-speed').value),
    rainCount: parseInt(document.getElementById('ms-rain-count').value, 10),
    rainLength: parseFloat(document.getElementById('ms-rain-length').value),
    windX: parseFloat(document.getElementById('ms-wind-x').value),
    windZ: parseFloat(document.getElementById('ms-wind-z').value),
    rainTop: parseFloat(document.getElementById('ms-rain-top').value),
    rainBottom: parseFloat(document.getElementById('ms-rain-bottom').value),
    key4: parseFloat(document.getElementById('ms-shape-key-4').value),
    key5: parseFloat(document.getElementById('ms-shape-key-5').value),
    drySeason: parseFloat(document.getElementById('ms-shape-key-dry').value),
    cloudOpacity: parseFloat(document.getElementById('ms-cloud-opacity').value),
  };
}

function loadPresetsFromStorage() {
  try {
    const raw = localStorage.getItem(PRESET_STORAGE_KEY);
    if (!raw) return;
    const data = JSON.parse(raw);
    if (Array.isArray(data.slots)) {
      presetSlots = [0, 1, 2, 3].map(i => data.slots[i] || null);
    }
    if (typeof data.activeSlot === 'number') activePresetSlot = data.activeSlot;
  } catch (_) {}
}

function savePresetsToStorage() {
  localStorage.setItem(PRESET_STORAGE_KEY, JSON.stringify({
    slots: presetSlots,
    activeSlot: activePresetSlot
  }));
}

function renderPresetSlots() {
  const wrap = document.getElementById('msPresets');
  if (!wrap) return;
  wrap.innerHTML = '';
  for (let i = 0; i < 4; i++) {
    const slot = presetSlots[i];
    const el = document.createElement('div');
    el.className = 'ms-preset' + (activePresetSlot === i ? ' active' : '');
    el.innerHTML = `
      <div class="ms-preset-label">Preset ${i + 1}</div>
      <div class="ms-preset-status">${slot ? (slot.savedAt || 'Saved') : 'Empty'}</div>
      <div class="ms-preset-actions">
        <button type="button" data-act="load" data-slot="${i}" ${slot ? '' : 'disabled'}>Load</button>
        <button type="button" data-act="save" data-slot="${i}">Save</button>
      </div>`;
    wrap.appendChild(el);
  }
  wrap.querySelectorAll('button').forEach(btn => {
    btn.addEventListener('click', () => {
      const slot = parseInt(btn.dataset.slot, 10);
      if (btn.dataset.act === 'save') savePreset(slot);
      else if (btn.dataset.act === 'load') loadPreset(slot);
    });
  });
}

function savePreset(slotIndex) {
  const settings = readSettingsFromUI();
  const now = new Date();
  const savedAt = now.toLocaleString(undefined, {
    month: 'short', day: 'numeric', hour: '2-digit', minute: '2-digit'
  });
  presetSlots[slotIndex] = { settings, savedAt };
  activePresetSlot = slotIndex;
  applyModelSettings(settings);
  savePresetsToStorage();
  renderPresetSlots();
}

function loadPreset(slotIndex) {
  const slot = presetSlots[slotIndex];
  if (!slot || !slot.settings) return;
  activePresetSlot = slotIndex;
  applyModelSettings(slot.settings);
  savePresetsToStorage();
  renderPresetSlots();
}

window.resetModelSettings = function() {
  activePresetSlot = -1;
  applyModelSettings({ ...DEFAULT_MODEL_SETTINGS });
  savePresetsToStorage();
  renderPresetSlots();
};

function bindModelSettingsControls() {
  const bind = (id, valId, key, parse, fmt, extra) => {
    const input = document.getElementById(id);
    const label = document.getElementById(valId);
    if (!input) return;
    input.addEventListener('input', (e) => {
      const val = parse(e.target.value);
      label.textContent = fmt(val);
      modelSettings[key] = val;
      if (extra) extra(val);
      else applyModelSettings(modelSettings, { syncUI: false });
    });
  };

  bind('ms-wave-height', 'ms-wave-height-val', 'waveHeight', parseFloat, v => v.toFixed(2), (v) => {
    sharedWaveUniforms.uWaveHeight.value = v;
  });
  bind('ms-wave-freq', 'ms-wave-freq-val', 'waveFreq', parseFloat, v => v.toFixed(1), (v) => {
    sharedWaveUniforms.uWaveFrequency.value = v;
  });
  bind('ms-wave-speed', 'ms-wave-speed-val', 'waveSpeed', parseFloat, v => v.toFixed(1), (v) => {
    sharedWaveUniforms.uWaveSpeed.value = v;
  });
  bind('ms-rain-count', 'ms-rain-count-val', 'rainCount', v => parseInt(v, 10), v => String(v), (v) => {
    if (rainLines) {
      rainLines.geometry.setDrawRange(0, v * 2);
      rainLines.visible = v > 0;
    }
  });
  bind('ms-rain-length', 'ms-rain-length-val', 'rainLength', parseFloat, v => v.toFixed(2));
  bind('ms-wind-x', 'ms-wind-x-val', 'windX', parseFloat, v => v.toFixed(1));
  bind('ms-wind-z', 'ms-wind-z-val', 'windZ', parseFloat, v => v.toFixed(1));
  bind('ms-rain-top', 'ms-rain-top-val', 'rainTop', parseFloat, v => v.toFixed(1), (v) => {
    rainBounds.maxY = v;
  });
  bind('ms-rain-bottom', 'ms-rain-bottom-val', 'rainBottom', parseFloat, v => v.toFixed(1), (v) => {
    rainBounds.minY = v;
  });
  bind('ms-shape-key-4', 'ms-shape-key-4-val', 'key4', parseFloat, v => v.toFixed(2), (v) => {
    setMorphByName('Key 4', v);
    pumpData.p1_t = v; pumpData.p1_c = v;
  });
  bind('ms-shape-key-5', 'ms-shape-key-5-val', 'key5', parseFloat, v => v.toFixed(2), (v) => {
    setMorphByName('Key 5', v);
    pumpData.p2_t = v; pumpData.p2_c = v;
  });
  bind('ms-shape-key-dry', 'ms-shape-key-dry-val', 'drySeason', parseFloat, v => v.toFixed(2), (v) => {
    setMorphByName('dry season', v);
  });
  bind('ms-cloud-opacity', 'ms-cloud-opacity-val', 'cloudOpacity', parseFloat, v => v.toFixed(2), (v) => {
    cloudMaterialsCollection.forEach(mat => { mat.opacity = v; });
    cloudMat.opacity = v;
  });
}

window.toggleModelSettings = function(force) {
  const open = force === undefined ? !isSettingsMode : !!force;
  isSettingsMode = open;
  const btn = document.getElementById('btnModelSettings');
  const panel = document.getElementById('modelSettingsPanel');
  if (btn) btn.classList.toggle('active', open);
  if (panel) panel.classList.toggle('open', open);
  document.body.classList.toggle('settings-mode', open);

  if (open) {
    settingsStageBefore = currentStage;
    if (isIsolated) {
      isIsolated = false;
      scene.children.forEach(c => {
        if (c.userData._v !== undefined) {
          c.visible = c.userData._v;
          delete c.userData._v;
        }
      });
      const bic = document.getElementById('blockInfoCard');
      if (bic) bic.style.display = 'none';
      const btnExit = document.getElementById('btnExit');
      if (btnExit) btnExit.style.display = 'none';
      const ui = document.getElementById('uiPanel');
      if (ui) ui.style.opacity = '1';
    }
    // Show full main model, hide infrastructure-only variant
    if (baseGround) baseGround.visible = true;
    if (baseWithHoles) baseWithHoles.visible = false;
    interactiveBlocks.forEach(b => b.visible = false);
    if (labelP1) labelP1.visible = false;
    if (labelP2) labelP2.visible = false;
    if (arrowPump1Left) arrowPump1Left.visible = false;
    if (arrowPump1Right) arrowPump1Right.visible = false;
    outlinePass.selectedObjects = [];
    createRainEngine();
    applyModelSettings(modelSettings, { syncUI: true, syncPumps: true });
    if (rainLines) rainLines.visible = modelSettings.rainCount > 0;
    flyTo(22, 14, 22, 0, 0, 0);
    renderPresetSlots();
  } else {
    if (rainLines) rainLines.visible = isRainy && modelSettings.rainCount > 0;
    setStage(settingsStageBefore || 1);
  }
};

loadPresetsFromStorage();
bindModelSettingsControls();
renderPresetSlots();
if (activePresetSlot >= 0 && presetSlots[activePresetSlot]) {
  modelSettings = { ...DEFAULT_MODEL_SETTINGS, ...presetSlots[activePresetSlot].settings };
}

// ── LIGHTNING / THUNDER (climate tab — 3D rain comes from cloud rainLines) ─
let thunderTimeout = null;

function createTextPlane(text) {
  const canvas = document.createElement('canvas');
  const ctx = canvas.getContext('2d');
  canvas.width = 512;
  canvas.height = 256;

  // Background box
  ctx.fillStyle = 'rgba(15, 39, 68, 0.85)'; 
  ctx.roundRect(10, 10, 492, 236, 20);
  ctx.fill();

  // Border
  ctx.strokeStyle = '#2e9fd4';
  ctx.lineWidth = 12;
  ctx.stroke();

  // Text
  ctx.fillStyle = '#ffffff';
  ctx.font = 'bold 70px Outfit, sans-serif';
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.fillText(text, canvas.width / 2, canvas.height / 2);

  const texture = new THREE.CanvasTexture(canvas);
  
  // Use PlaneGeometry instead of Sprite
  // Side: THREE.DoubleSide allows you to see the label from the back too!
  const geometry = new THREE.PlaneGeometry(4, 2); 
  const material = new THREE.MeshBasicMaterial({ 
    map: texture, 
    transparent: true, 
    side: THREE.DoubleSide 
  });
  
  const mesh = new THREE.Mesh(geometry, material);
  return mesh;
}

function createImagePlane(url, width = 1.2, height = 1.2) {
  const geometry = new THREE.PlaneGeometry(width, height);
  const material = new THREE.MeshBasicMaterial({
    transparent: true,
    side: THREE.DoubleSide,
    depthWrite: false,
  });
  const mesh = new THREE.Mesh(geometry, material);
  mesh.visible = false;

  new THREE.TextureLoader().load(url, (texture) => {
    texture.colorSpace = THREE.SRGBColorSpace;
    material.map = texture;
    material.needsUpdate = true;
  });

  return mesh;
}

function startThunder() {
  if (thunderTimeout) clearTimeout(thunderTimeout);
  scheduleThunder();
}

function stopThunder() {
  if (thunderTimeout) { clearTimeout(thunderTimeout); thunderTimeout = null; }
  const flash = document.getElementById('lightning');
  if (flash) flash.style.background = 'rgba(210,235,255,0)';
}

function scheduleThunder() {
  const delay = 3500 + Math.random() * 6000;
  thunderTimeout = setTimeout(() => {
    if (!isRainy) return;
    doLightning();
    scheduleThunder();
  }, delay);
}

function doLightning() {
  const flash = document.getElementById('lightning');
  // Two-phase flash: bright then dim
  flash.style.background = 'rgba(210,235,255,0.22)';
  setTimeout(() => { flash.style.background = 'rgba(210,235,255,0.08)'; }, 60);
  setTimeout(() => { flash.style.background = 'rgba(210,235,255,0.18)'; }, 120);
  setTimeout(() => { flash.style.background = 'rgba(210,235,255,0)'; }, 250);

  // Thunder sound via Web Audio (soft rumble)
  try {
    const ctx = new (window.AudioContext || window.webkitAudioContext)();
    const buf = ctx.createBuffer(1, ctx.sampleRate * 2.5, ctx.sampleRate);
    const data = buf.getChannelData(0);
    for (let i = 0; i < data.length; i++) {
      const t = i / ctx.sampleRate;
      const env = Math.exp(-t * 1.4);
      data[i] = (Math.random() * 2 - 1) * env * 0.35;
    }
    const src = ctx.createBufferSource();
    src.buffer = buf;
    const lp = ctx.createBiquadFilter();
    lp.type = 'lowpass'; lp.frequency.value = 180;
    src.connect(lp); lp.connect(ctx.destination);
    src.start();
  } catch(e) { /* audio not available */ }
}

// ── WEATHER TOGGLE (global, called from HTML) ──────────────────────────
const drySeasonAnim = { value: 1 };
let waterLevelArrowsVisible = false;
const _wlaBox = new THREE.Box3();
const _wlaPt = new THREE.Vector3();

function updateWaterLevelArrowPositions() {
  if (!waterLevelArrowsVisible || !camera) return;
  const leftEl = document.getElementById('wlaLeft');
  const appEl = document.getElementById('app');
  const root = oceanBottomRoot || oceanTopRoot || baseGround;
  if (!leftEl || !appEl || !root) return;

  _wlaBox.setFromObject(root);
  // Left end of the freshwater / aquifer model (min X edge, mid height/depth)
  const midY = (_wlaBox.min.y + _wlaBox.max.y) * 0.5;
  const midZ = (_wlaBox.min.z + _wlaBox.max.z) * 0.5;
  _wlaPt.set(_wlaBox.min.x, midY, midZ).project(camera);
  if (_wlaPt.z > 1) return; // behind camera

  const rect = appEl.getBoundingClientRect();
  const sx = (_wlaPt.x * 0.5 + 0.5) * rect.width;
  const sy = (-_wlaPt.y * 0.5 + 0.5) * rect.height;
  leftEl.style.left = `${sx}px`;
  leftEl.style.top = `${sy}px`;
}

function showWaterLevelArrows(rising) {
  const el = document.getElementById('waterLevelArrows');
  const label = document.getElementById('wlaLabel');
  if (!el) return;
  el.classList.remove('rising', 'falling', 'show');
  el.classList.add(rising ? 'rising' : 'falling', 'show');
  el.setAttribute('aria-hidden', 'false');
  if (label) label.textContent = rising ? 'FRESHWATER RISING' : 'FRESHWATER FALLING';
  waterLevelArrowsVisible = true;
  updateWaterLevelArrowPositions();
}

function hideWaterLevelArrows() {
  const el = document.getElementById('waterLevelArrows');
  if (!el) return;
  el.classList.remove('show', 'rising', 'falling');
  el.setAttribute('aria-hidden', 'true');
  waterLevelArrowsVisible = false;
}

window.toggleWeather = function() {
  isRainy = !isRainy;
  const track = document.getElementById('toggleTrack');
  const thumb = document.getElementById('toggleThumb');
  const label = document.getElementById('seasonLabel');

  if (isRainy) {
    track.classList.add('rainy');
    thumb.textContent = '🌧';
    label.textContent = 'RAINY SEASON';
    createRainEngine();
    if (rainLines) {
      rainLines.visible = modelSettings.rainCount > 0;
      rainLines.geometry.setDrawRange(0, modelSettings.rainCount * 2);
    }
    startThunder();
    modelSettings.cloudOpacity = Math.max(modelSettings.cloudOpacity, 0.6);
    gsap.to(scene.background, { r:0.04, g:0.08, b:0.14, duration:1.8 });
    if (scene.fog) { gsap.to(scene.fog.color, { r:0.04, g:0.08, b:0.14, duration:1.8 }); gsap.to(scene.fog, { density:0.022, duration:1.8 }); }
  } else {
    track.classList.remove('rainy');
    thumb.textContent = '☀';
    label.textContent = 'DRY SEASON';
    stopThunder();
    if (rainLines) rainLines.visible = false;
    modelSettings.cloudOpacity = 0;
    gsap.to(scene.background, { r:0.941, g:0.961, b:0.980, duration:1.8 });
    if (scene.fog) { gsap.to(scene.fog.color, { r:0.867, g:0.910, b:0.949, duration:1.8 }); gsap.to(scene.fog, { density:0.008, duration:1.8 }); }
  }

  // Animate freshwater level over 3s (do not snap drySeason before the tween)
  const dryTarget = isRainy ? 0 : 1;
  const isRising = isRainy;
  showWaterLevelArrows(isRising);
  drySeasonAnim.value = modelSettings.drySeason;
  gsap.killTweensOf(drySeasonAnim);
  gsap.to(drySeasonAnim, {
    value: dryTarget,
    duration: 3,
    ease: 'power1.inOut',
    onUpdate: () => {
      modelSettings.drySeason = drySeasonAnim.value;
      setMorphByName('dry season', drySeasonAnim.value);
    },
    onComplete: () => {
      modelSettings.drySeason = dryTarget;
      setMorphByName('dry season', dryTarget);
      hideWaterLevelArrows();
      syncSettingsUIFromState();
    }
  });

  gsap.to(cloudMat, { opacity: modelSettings.cloudOpacity, duration:1.6 });
  syncSettingsUIFromState();
};

// ── OCEAN TOGGLE (global, called from HTML) ────────────────────────────
let isOceanVisible = true;

function fadeOceanRoot(root, toVisible) {
  if (!root) return;
  root.traverse(c => {
    if (!c.isMesh) return;
    if (c.material._origTransparent === undefined)
      c.material._origTransparent = c.material.transparent;
    if (toVisible) {
      c.visible = true;
      c.material.transparent = true;
      gsap.to(c.material, {
        opacity: 1, duration: 0.85,
        onComplete: () => { c.material.transparent = c.material._origTransparent || false; }
      });
    } else {
      c.material.transparent = true;
      gsap.to(c.material, {
        opacity: 0, duration: 0.85,
        onComplete: () => { c.visible = false; }
      });
    }
  });
}

window.toggleOcean = function() {
  isOceanVisible = !isOceanVisible;
  const track = document.getElementById('oceanTrack');
  const thumb = document.getElementById('oceanThumb');
  const label = document.getElementById('oceanLabel');
  const covPct = document.getElementById('oceanCovPct');
  const covBar = document.getElementById('oceanCovBar');
  const alert  = document.getElementById('oceanHiddenAlert');

  if (!isOceanVisible) {
    track.classList.add('off');
    thumb.textContent = '🫧';
    label.textContent = 'OCEAN OFF';
    fadeOceanRoot(oceanBottomRoot, false);
    fadeOceanRoot(oceanTopRoot,    false);
    if (covPct) covPct.textContent = '0%';
    if (covBar) { covBar.style.width = '0%'; covBar.className = 'gauge-bar-fill fill-danger'; }
    if (alert)  alert.style.display = 'flex';
  } else {
    track.classList.remove('off');
    thumb.textContent = '🌊';
    label.textContent = 'OCEAN ON';
    fadeOceanRoot(oceanBottomRoot, true);
    fadeOceanRoot(oceanTopRoot,    true);
    if (covPct) covPct.textContent = '100%';
    if (covBar) { covBar.style.width = '100%'; covBar.className = 'gauge-bar-fill fill-safe'; }
    if (alert)  alert.style.display = 'none';
  }
};

// ── BLOCK META ─────────────────────────────────────────────────────────
const BLOCK_META = [
  {
    name:'Pump Infrastructure A',
    desc:'Primary extraction facility serving the Valikamam aquifer. Houses high-lift motorised pumps replacing traditional pulley systems. Critical northern distribution node.',
    tags:['Valikamam Zone','High-Lift Pump','Primary']
  },
  {
    name:'Distribution Hub B',
    desc:'Central monitoring hub linking the Thenmaradchchi aquifer to the municipal network. Monitors salinity TDS and water table in real time.',
    tags:['Thenmaradchchi','Monitoring','Distribution']
  },
  {
    name:'Treatment Station C',
    desc:'Secondary treatment addressing elevated nitrate from agrochemicals in the Vadamaradchchi aquifer. Includes multi-stage sand filtration.',
    tags:['Vadamaradchchi','Nitrate Filter','Treatment']
  }
];

// ── EXPOSE GLOBALS ─────────────────────────────────────────────────────
window.enterApp = enterApp;
window.setStage = setStage;
window.goHome = goHome;

// ── GO HOME ────────────────────────────────────────────────────────────
function goHome() {
  window.location.reload();
}

// ── INTRO → APP ────────────────────────────────────────────────────────
function enterApp() {
  document.getElementById('startBtn').disabled = true;
  document.getElementById('app').classList.add('show');
  setProgress(5, 'Initialising renderer…', 'Setting up WebGL context');
  requestAnimationFrame(() => {
    init();
    document.getElementById('app').classList.add('visible');
  });
}

function setProgress(pct, label, detail) {
  document.getElementById('bfill').style.width = pct + '%';
  document.getElementById('ptext').textContent = label;
  document.getElementById('ltext').textContent = label.toUpperCase();
  document.getElementById('lbar').style.width  = pct + '%';
  if (detail) document.getElementById('ldetail').textContent = detail;
}

// ── THREE INIT ────────────────────────────────────────────────────────
function init() {
  scene = new THREE.Scene();
  scene.background = new THREE.Color(0xf0f5fa);   /* bright white-blue sky */
  scene.fog = new THREE.FogExp2(0xdde8f2, 0.008); /* very light fog */

  camera = new THREE.PerspectiveCamera(40, window.innerWidth/window.innerHeight, 0.1, 1000);
  camera.position.set(28, 18, 28);

  renderer = new THREE.WebGLRenderer({ antialias:true });
  renderer.setSize(window.innerWidth, window.innerHeight);
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.toneMapping = THREE.ACESFilmicToneMapping;
  renderer.toneMappingExposure = 1.1;
  document.getElementById('cvs-wrap').appendChild(renderer.domElement);

  scene.add(new THREE.AmbientLight(0xffffff, 3));
  scene.add(new THREE.HemisphereLight(0xfaf5ee, 0xc8d8e8, 1.6));
  const sun = new THREE.DirectionalLight(0xfff8f0, 3.5);
  sun.position.set(20, 40, 20); scene.add(sun);
  const fill = new THREE.DirectionalLight(0xc8d8f0, 1.2);
  fill.position.set(-20, 10, -20); scene.add(fill);

  composer = new EffectComposer(renderer);
  composer.addPass(new RenderPass(scene, camera));
  outlinePass = new OutlinePass(new THREE.Vector2(window.innerWidth, window.innerHeight), scene, camera);
  outlinePass.visibleEdgeColor.set('#0f5fa0');
  outlinePass.edgeStrength = 14;
  outlinePass.edgeThickness = 2.5;
  outlinePass.edgeGlow = 0.2;
  composer.addPass(outlinePass);

  controls = new OrbitControls(camera, renderer.domElement);
  controls.enableDamping = true;
  controls.dampingFactor = 0.07;
  controls.maxPolarAngle = Math.PI * 0.84;
  controls.minDistance = 2;
  controls.maxDistance = 90;

  window.addEventListener('resize', () => {
    camera.aspect = window.innerWidth / window.innerHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(window.innerWidth, window.innerHeight);
    composer.setSize(window.innerWidth, window.innerHeight);
  });

  loadAssets();
  setupInteractions();
  animate();
}

function setupLabels() {
  labelP1 = createTextPlane("PUMP 2: 0%");
  labelP1.position.set(5, -.6, -1); 
  labelP1.scale.set(.5,.5,.5);
  labelP1.rotation.y = Math.PI / 2; 
  labelP1.visible = false;
  scene.add(labelP1);

  labelP2 = createTextPlane("PUMP 1: 0%");
  labelP2.position.set(5, -.6, 4); 
  labelP2.scale.set(.5,.5,.5);
  labelP2.rotation.y = Math.PI / 2;
  labelP2.visible = false;
  scene.add(labelP2);

  // Yellow arrows under PUMP 1 — tune each arrow's leftPx / gapPx independently
  // leftPx: + = screen-left (+Z), − = screen-right (−Z)  |  gapPx: space below label → arrow top
  arrowPump1Left = createImagePlane('assets/images/arrow_left-pump1.png', 1.1, 1.1);
  arrowPump1Left.userData.planeH = 1.1;
  arrowPump1Left.userData.leftPx = 160;
  arrowPump1Left.userData.gapPx = 80;
  arrowPump1Left.rotation.y = Math.PI / 2;
  arrowPump1Left.visible = false;
  scene.add(arrowPump1Left);

  arrowPump1Right = createImagePlane('assets/images/arrow_right_pump1.png', 1.1, 1.1);
  arrowPump1Right.userData.planeH = 1.1;
  arrowPump1Right.userData.leftPx = 50;
  arrowPump1Right.userData.gapPx = 60;
  arrowPump1Right.rotation.y = Math.PI / 2;
  arrowPump1Right.visible = false;
  scene.add(arrowPump1Right);

  placeArrowsRelativeToPump1();
}

/** Place each PUMP 1 arrow from its own leftPx / gapPx (no mirroring). */
function placeArrowsRelativeToPump1() {
  if (!labelP2 || !camera) return;

  const labelHalfH = (2 * labelP2.scale.y) / 2;
  const dist = camera.position.distanceTo(labelP2.position);
  const vFov = THREE.MathUtils.degToRad(camera.fov);
  const worldPerPx = (2 * Math.tan(vFov / 2) * dist) / window.innerHeight;

  const place = (arrow) => {
    if (!arrow) return;
    const leftPx = arrow.userData.leftPx ?? 0;
    const gapPx = arrow.userData.gapPx ?? 0;
    const arrowHalfH = (arrow.userData.planeH || 1.1) / 2;
    const baseY = labelP2.position.y - labelHalfH - gapPx * worldPerPx - arrowHalfH;

    arrow.userData.baseX = labelP2.position.x;
    arrow.userData.baseY = baseY;
    arrow.userData.baseZ = labelP2.position.z + leftPx * worldPerPx;

    arrow.position.x = arrow.userData.baseX;
    arrow.position.z = arrow.userData.baseZ;
    // Y set in animatePump1Arrows (bob while rising)
    if (!pump1ArrowsRising) arrow.position.y = baseY;
  };

  place(arrowPump1Left);
  place(arrowPump1Right);
}

/** Pump Station 1 = dialP2 / pumpData.p2 — show arrows only while increasing. */
function syncPump1ArrowVisibility(nextVal) {
  const prev = lastPumpStation1Val;
  if (nextVal > prev + 0.0005) {
    pump1ArrowsRising = true;
  } else if (nextVal < prev - 0.0005 || nextVal <= 0) {
    pump1ArrowsRising = false;
  }
  lastPumpStation1Val = nextVal;

  const show = currentStage === 3 && !isSettingsMode && pump1ArrowsRising;
  if (arrowPump1Left) arrowPump1Left.visible = show;
  if (arrowPump1Right) arrowPump1Right.visible = show;
}

/** GIF-style loop: slide up, then snap back. */
function animatePump1Arrows(elapsed) {
  if (!pump1ArrowsRising) return;
  const cycle = (elapsed * 0.85) % 1; // 0→1 (slower loop)
  const bob = cycle * 0.4; // rise ~0.4 world units then reset

  [arrowPump1Left, arrowPump1Right].forEach((arrow) => {
    if (!arrow || arrow.userData.baseY === undefined) return;
    arrow.position.y = arrow.userData.baseY + bob;
  });
}


function updatePlaneText(mesh, newText) {
  const canvas = mesh.material.map.image;
  const ctx = canvas.getContext('2d');

  ctx.clearRect(0, 0, canvas.width, canvas.height);

  ctx.fillStyle = 'rgba(15, 39, 68, 0.85)';
  ctx.roundRect(10, 10, 492, 236, 20);
  ctx.fill();

  ctx.strokeStyle = '#2e9fd4';
  ctx.lineWidth = 12;
  ctx.stroke();

  ctx.fillStyle = '#ffffff';
  ctx.font = 'bold 70px Outfit, sans-serif';
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.fillText(newText, canvas.width / 2, canvas.height / 2);

  mesh.material.map.needsUpdate = true;
}

// ── LOAD ASSETS ───────────────────────────────────────────────────────
function loadAssets() {
  const loader = new GLTFLoader();  
  let done = 0;
  const FILES = [
    { url:'assets/models/gnd-compressed.glb',            label:'Ground terrain',         pct:14 },
    { url:'assets/models/base-with-holes-compressed.glb', label:'Subsurface base',        pct:27 },
    { url:'assets/models/block-1-compressed.glb',         label:'Infrastructure block 1', pct:40 },
    { url:'assets/models/block-2-compressed.glb',         label:'Infrastructure block 2', pct:52 },
    { url:'assets/models/block-3-compressed.glb',         label:'Infrastructure block 3', pct:64 },
    { url:'assets/models/salt.glb',                       label:'Saltwater layer',        pct:75 },
    { url:'assets/models/fresh.glb',                      label:'Freshwater layer',       pct:86 },
    { url:'assets/models/clouds-compressed.glb',          label:'Atmosphere layer',       pct:95 },
    { url:'assets/models/props.glb',                      label:'objects',                pct:100 },
  ];
  const total = FILES.length;
  FILES.forEach(({ url, label, pct }) => {
    loader.load(url,
      (gltf) => { done++; setProgress(pct,label+' loaded',url); handleGLB(url,gltf.scene); if(done>=total) finishLoad(); },
      undefined,
      ()     => { done++; setProgress(pct,label+' skipped',url); if(done>=total) finishLoad(); }
    );
  });
}

function handleGLB(url, root) {
  const file = url.split('/').pop();
  if      (file.startsWith('ground') || file.startsWith('gnd'))     { baseGround=root; scene.add(root); }
  else if (file.startsWith('base-with') || file.startsWith('base_with'))  { baseWithHoles=root; root.visible=false; scene.add(root); }
  else if (file.startsWith('block-') || file.startsWith('block_'))     { root.visible=false; root.userData.isInteractable=true; interactiveBlocks.push(root); scene.add(root); }
  else if (file.startsWith('salt'))  {
    oceanTopRoot = root;
    root.traverse(c => {
      if (c.isMesh) {
        applyUnifiedWaveShader(c.material, 0x1a7fc1);
        if (c.morphTargetDictionary) {
          oceanParts.push(c);
          morphTargetsCollection.push(c);
          setMorph(c, 'dry season', modelSettings.drySeason);
        }
      }
    });
    scene.add(root);
  }
  else if (file.startsWith('fresh')) {
    oceanBottomRoot = root;
    root.traverse(c => {
      if (!c.isMesh) return;
      applyUnifiedWaveShader(c.material, 0x2e9fd4);
      if (c.morphTargetDictionary) {
        oceanParts.push(c);
        morphTargetsCollection.push(c);
      }
    });
    scene.add(root);
  }
  else if (file.startsWith('clouds')) {
    root.traverse(c => {
      if (!c.isMesh) return;
      c.material = cloudMat;
      cloudMeshes.push(c);
      if (c.material && !cloudMaterialsCollection.includes(c.material)) {
        cloudMaterialsCollection.push(c.material);
      }
    });
    scene.add(root);
  }
  else if (file.startsWith('props')) {
    propsModel = root;
    registerMorphTargets(root);
    scene.add(root);
  }
}

function finishLoad() {

  setProgress(100, 'All systems ready', 'Launching 3D environment');
  
  // Call your label setup here!
  setupLabels();
  createRainEngine();
  applyModelSettings(modelSettings, { syncUI: true, syncPumps: true });

  setTimeout(() => { 
    document.getElementById('intro').classList.add('out'); 
    document.getElementById('loader').classList.add('gone'); 
    setStage(1); 
  }, 650);

}

// ── STAGE SWITCHING ───────────────────────────────────────────────────
function setStage(s) {
  if (isSettingsMode) {
    // Exit settings chrome without recursive setStage
    isSettingsMode = false;
    document.body.classList.remove('settings-mode');
    const btn = document.getElementById('btnModelSettings');
    const panel = document.getElementById('modelSettingsPanel');
    if (btn) btn.classList.remove('active');
    if (panel) panel.classList.remove('open');
  }

  // Requirement #2: If we are leaving Ocean View (Stage 1) 
  // and the ocean was turned off, turn it back on automatically.
  if (currentStage === 1 && s !== 1) {
    if (typeof oceanOff !== 'undefined' && oceanOff === true) {
      toggleOcean(); 
    }
  }

  currentStage = s;

  // 1. Update UI Tab States
  document.querySelectorAll('.tab').forEach((t, i) => t.classList.toggle('active', i + 1 === s));

  // 2. Toggle Left and Right Panel Visibility (Re-mapped to new order)
  // New Map: 1=Ocean(s4), 2=Climate(s1), 3=Pumping(s2), 4=Infrastructure(s3)
  const panelMap = { 1: '4', 2: '1', 3: '2', 4: '3' };
  const targetSuffix = panelMap[s];

  ['lp-s1', 'lp-s2', 'lp-s3', 'lp-s4'].forEach(id => {
    const el = document.getElementById(id);
    if (el) el.classList.add('hidden');
  });
  ['rp-s1', 'rp-s2', 'rp-s3', 'rp-s4'].forEach(id => {
    const el = document.getElementById(id);
    if (el) el.classList.add('hidden');
  });

  document.getElementById('lp-s' + targetSuffix).classList.remove('hidden');
  document.getElementById('rp-s' + targetSuffix).classList.remove('hidden');

  // 3. Toggle Control Group Visibility (Re-mapped)
  document.getElementById('cs4').className = (s === 1) ? 'ctrl-group' : 'hidden'; // Ocean
  document.getElementById('cs1').className = (s === 2) ? 'ctrl-group' : 'hidden'; // Climate

  const cs2 = document.getElementById('cs2'); // Pumping
  if (s === 3) { cs2.className = ''; cs2.style.display = 'flex'; }
  else         { cs2.className = 'hidden'; }

  document.getElementById('cs3').className = (s === 4) ? 'ctrl-group' : 'hidden'; // Infrastructure

  // 4. Toggle 3D Labels (Pumping labels now show on stage 3)
  if (labelP1) labelP1.visible = (s === 3);
  if (labelP2) labelP2.visible = (s === 3);
  // Arrows only while Pump Station 1 is being increased
  if (s !== 3) {
    pump1ArrowsRising = false;
    if (arrowPump1Left) arrowPump1Left.visible = false;
    if (arrowPump1Right) arrowPump1Right.visible = false;
  } else {
    syncPump1ArrowVisibility(pumpData.p2_t);
  }

  // 5. Handle 3D Object Visibility (Infrastructure specific logic moved to stage 4)
  if (baseGround)     baseGround.visible    = (s !== 4);
  if (baseWithHoles)  baseWithHoles.visible = (s === 4);
  if (propsModel)     propsModel.visible    = true;
  interactiveBlocks.forEach(b => b.visible = (s === 4));

  // 6. Update Post-Processing (Outline for Infrastructure)
  outlinePass.selectedObjects = (s === 4) ? interactiveBlocks : [];

  // 7. Camera Reset (Re-mapped positions)
  if (s === 1) flyTo(11.26, 4.22, 13.45, -0.5, 0.63, 0.31);// Ocean View Position
  if (s === 2) flyTo(22, 14, 22, 0, 0, 0); // Climate Position
  if (s === 3) flyTo(18,  5,  5, 4, -2, -.5); // Pumping Position
  if (s === 4) flyTo(22, 14, 22, 0, 0, 0); // Infrastructure PositionflyTo(9.18, 4.04, 10.34, -1.76, -1.54, 2.79);

  // Keep model settings applied on every tab
  applyModelSettings(modelSettings, { syncUI: false, syncPumps: false });
  if (rainLines) rainLines.visible = isRainy && modelSettings.rainCount > 0;
}
function flyTo(x,y,z,tx,ty,tz){
  gsap.to(camera.position,{x,y,z,duration:1.6,ease:'power2.inOut'});
  gsap.to(controls.target,{x:tx,y:ty,z:tz,duration:1.6,onUpdate:()=>controls.update()});
}

// ── INTERACTIONS ──────────────────────────────────────────────────────
function setupInteractions(){
  const ray = new THREE.Raycaster(), mouse = new THREE.Vector2();
  // Ignore cube opens after orbit/tilt: only select on a near-stationary click
  const CLICK_MAX_MOVE_PX = 6;
  let pointerDown = null;

  const canvas = renderer.domElement;

  canvas.addEventListener('pointerdown', (e) => {
    if (e.button !== 0) return;
    pointerDown = { x: e.clientX, y: e.clientY };
  });

  canvas.addEventListener('pointerup', (e) => {
    if (e.button !== 0 || !pointerDown) return;
    const dx = e.clientX - pointerDown.x;
    const dy = e.clientY - pointerDown.y;
    const moved = Math.hypot(dx, dy);
    pointerDown = null;

    // Drag / camera orbit — do not open a cube
    if (moved > CLICK_MAX_MOVE_PX) return;
    if (currentStage !== 4 || isIsolated) return;

    mouse.x = (e.clientX / window.innerWidth) * 2 - 1;
    mouse.y = -(e.clientY / window.innerHeight) * 2 + 1;
    ray.setFromCamera(mouse, camera);

    const hits = ray.intersectObjects(interactiveBlocks, true);
    if (hits.length > 0) {
      let obj = hits[0].object;
      while (obj.parent && !obj.userData.isInteractable) {
        obj = obj.parent;
      }
      isolate(obj, interactiveBlocks.indexOf(obj));
    }
  });

  canvas.addEventListener('pointercancel', () => { pointerDown = null; });
  canvas.addEventListener('pointerleave', () => { pointerDown = null; });

  document.getElementById('btnExit').onclick=deIsolate;
  document.getElementById('dialP1').oninput=(e)=>{pumpData.p1_t=parseFloat(e.target.value);refreshPumpUI();};
  document.getElementById('dialP2').oninput=(e)=>{
    pumpData.p2_t=parseFloat(e.target.value);
    syncPump1ArrowVisibility(pumpData.p2_t);
    refreshPumpUI();
  };
}

function refreshPumpUI(){
  const p1=Math.round(pumpData.p1_t*100), p2=Math.round(pumpData.p2_t*100);
  const combined=Math.round((pumpData.p1_t+pumpData.p2_t)/2*100);
  document.getElementById('pval1').textContent=p1;
  document.getElementById('pval2').textContent=p2;
  document.getElementById('pbar1').style.width=p1+'%';
  document.getElementById('pbar2').style.width=p2+'%';
  document.getElementById('pbar1').className='gauge-bar-fill '+(p1>70?'fill-danger':p1>40?'fill-warn':'fill-safe');
  document.getElementById('pbar2').className='gauge-bar-fill '+(p2>70?'fill-danger':p2>40?'fill-warn':'fill-safe');
  document.getElementById('loadPct').textContent=combined+'%';
  document.getElementById('loadBar').style.width=combined+'%';
  document.getElementById('loadBar').className='gauge-bar-fill '+(combined>65?'fill-danger':combined>35?'fill-warn':'fill-safe');
  const alert=document.getElementById('intrusionAlert');
  if(combined>60) alert.classList.add('show'); else alert.classList.remove('show');

  if(labelP2) updatePlaneText(labelP1, `PUMP 2: ${p1}%`);
  if(labelP1) updatePlaneText(labelP2, `PUMP 1: ${p2}%`);
}

// ── ISOLATION ────────────────────────────────────────────────────────
function isolate(obj,idx){
  isIsolated=true;
  outlinePass.selectedObjects=[obj];
  scene.children.forEach(c=>{
    if(c.isLight) return;
    if(c!==obj){if(c.userData._v===undefined)c.userData._v=c.visible; c.visible=false;}
  });
  const box=new THREE.Box3().setFromObject(obj);
  const center=box.getCenter(new THREE.Vector3());
  const size=box.getSize(new THREE.Vector3());
  const max=Math.max(size.x,size.y,size.z);
  flyTo(center.x+max*2.2,center.y+max*1.4,center.z+max*2.2,center.x,center.y,center.z);

  const meta=BLOCK_META[idx]||BLOCK_META[0];
  document.getElementById('biName').textContent=meta.name;
  document.getElementById('biDesc').textContent=meta.desc;
  document.getElementById('biTags').innerHTML=meta.tags.map(t=>`<span class="bi-tag">${t}</span>`).join('');
  // Show info card in left panel (inside lp-s3, below Ground Stratigraphy)
  document.getElementById('blockInfoCard').style.display='block';
  document.getElementById('btnExit').style.display='block';
  document.getElementById('uiPanel').style.opacity='0.35';
  document.getElementById('contextBar').textContent='INSPECTING STRUCTURE  ·  CLICK EXIT PREVIEW TO RETURN';
}

function deIsolate(){
  isIsolated=false;
  outlinePass.selectedObjects=interactiveBlocks;
  scene.children.forEach(c=>{if(c.userData._v!==undefined){c.visible=c.userData._v;delete c.userData._v;}});
  document.getElementById('blockInfoCard').style.display='none';
  document.getElementById('btnExit').style.display='none';
  document.getElementById('uiPanel').style.opacity='1';
  setStage(4);
}

function setMorph(m,k,v){ const i=m.morphTargetDictionary?.[k]; if(i!==undefined)m.morphTargetInfluences[i]=v; }

const settingsClock = new THREE.Clock();

function animate(){
  requestAnimationFrame(animate);

  const delta = settingsClock.getDelta();
  sharedWaveUniforms.uTime.value = settingsClock.getElapsedTime();
  updateRainEngine(delta);

  // In settings mode, Key 4/5 come from modelSettings; otherwise pumps drive them
  if (isSettingsMode) {
    setMorphByName('Key 4', modelSettings.key4);
    setMorphByName('Key 5', modelSettings.key5);
  } else {
    oceanParts.forEach(m => {
      setMorph(m, 'Key 4', pumpData.p1_c);
      setMorph(m, 'Key 5', pumpData.p2_c);
    });
    pumpData.p1_c += (pumpData.p1_t - pumpData.p1_c) * pumpData.speed;
    pumpData.p2_c += (pumpData.p2_t - pumpData.p2_c) * pumpData.speed;
    modelSettings.key4 = pumpData.p1_c;
    modelSettings.key5 = pumpData.p2_c;
  }

  controls.update();
  updateWaterLevelArrowPositions();
  if (currentStage === 3) {
    placeArrowsRelativeToPump1();
    animatePump1Arrows(settingsClock.getElapsedTime());
  }
  composer.render();
}

// ── INTRO 3D MODEL VIEWER ─────────────────────────────────────────────
(function initIntroModel() {
  const canvas = document.getElementById('introModelCanvas');
  const wrap   = document.getElementById('introModelWrap');
  if (!canvas || !wrap) return;

  // Read actual CSS size after layout
  function getWH() {
    const r = wrap.getBoundingClientRect();
    const w = r.width  || 480;
    const h = r.height || 480;
    return { w: Math.max(w, 100), h: Math.max(h, 100) };
  }

  let { w: W, h: H } = getWH();

  const iScene  = new THREE.Scene();
  const iCamera = new THREE.PerspectiveCamera(36, W / H, 0.01, 200);
  iCamera.position.set(0, 6, 16);
  iCamera.lookAt(0, 0, 0);

  const iRenderer = new THREE.WebGLRenderer({ canvas, antialias: true, alpha: true });
  iRenderer.setPixelRatio(window.devicePixelRatio);
  iRenderer.setSize(W, H);
  iRenderer.toneMapping = THREE.ACESFilmicToneMapping;
  iRenderer.toneMappingExposure = 1.2;

  iScene.add(new THREE.AmbientLight(0xffffff, 2.2));
  const iSun = new THREE.DirectionalLight(0xfff8f0, 3.0);
  iSun.position.set(10, 20, 10); iScene.add(iSun);
  const iFill = new THREE.DirectionalLight(0xc8d8f0, 1.4);
  iFill.position.set(-10, 5, -10); iScene.add(iFill);
  const iRim = new THREE.DirectionalLight(0x7ec8e8, 0.8);
  iRim.position.set(0, -5, -10); iScene.add(iRim);

  let introModel = null;
  let autoAngle  = 0;
  let mouseTarget  = { x: 0, y: 0 };
  let mouseCurrent = { x: 0, y: 0 };

  const iLoader = new GLTFLoader();
  iLoader.load('assets/models/peninsula.glb',
    (gltf) => {
      introModel = gltf.scene;
      const box    = new THREE.Box3().setFromObject(introModel);
      const center = box.getCenter(new THREE.Vector3());
      const size   = box.getSize(new THREE.Vector3());
      const scale  = 8 / Math.max(size.x, size.y, size.z);
      introModel.scale.setScalar(scale);
      introModel.position.set(-center.x*scale, -center.y*scale - 1, -center.z*scale);
      iScene.add(introModel);
    },
    undefined,
    () => {
      const mesh = new THREE.Mesh(
        new THREE.SphereGeometry(3.5, 32, 32),
        new THREE.MeshStandardMaterial({ color:0x1a7fc1, roughness:0.6, metalness:0.2 })
      );
      introModel = mesh;
      iScene.add(mesh);
    }
  );

  // Track mouse over full window for smooth parallax
  window.addEventListener('mousemove', (e) => {
    mouseTarget.x = (e.clientX / window.innerWidth  - 0.5) * 2;
    mouseTarget.y = (e.clientY / window.innerHeight - 0.5) * 2;
  });

  window.addEventListener('resize', () => {
    const s = getWH();
    W = s.w; H = s.h;
    iCamera.aspect = W / H;
    iCamera.updateProjectionMatrix();
    iRenderer.setSize(W, H);
  });

  function introAnimate() {
    requestAnimationFrame(introAnimate);
    mouseCurrent.x += (mouseTarget.x - mouseCurrent.x) * 0.05;
    mouseCurrent.y += (mouseTarget.y - mouseCurrent.y) * 0.05;
    autoAngle += 0.004;
    if (introModel) {
      introModel.rotation.y = autoAngle + mouseCurrent.x * 0.55;
      introModel.rotation.x = mouseCurrent.y * -0.3;
    }
    iRenderer.render(iScene, iCamera);
  }
  introAnimate();
})();

// // Camera Inspector Logic
// const posDisplay = document.getElementById('cam-pos');
// const rotDisplay = document.getElementById('cam-rot');

// function updateCameraInspector() {
//   if (camera) {
//     const p = camera.position;
//     const r = camera.rotation;
    
//     // Formatting to 2 decimal places for easy copying
//     posDisplay.innerText = `${p.x.toFixed(2)}, ${p.y.toFixed(2)}, ${p.z.toFixed(2)}`;
//     rotDisplay.innerText = `${r.x.toFixed(2)}, ${r.y.toFixed(2)}, ${r.z.toFixed(2)}`;
//   }
//   requestAnimationFrame(updateCameraInspector);
// }

// // Start the inspector loop
// updateCameraInspector();

