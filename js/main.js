import * as THREE from 'three';
import { GLTFLoader }     from 'three/addons/loaders/GLTFLoader.js';
import { OrbitControls }  from 'three/addons/controls/OrbitControls.js';
import { EffectComposer } from 'three/addons/postprocessing/EffectComposer.js';
import { RenderPass }     from 'three/addons/postprocessing/RenderPass.js';
import { OutlinePass }    from 'three/addons/postprocessing/OutlinePass.js';

// ── STATE ──────────────────────────────────────────────────────────────
let scene, renderer, camera, controls, composer, outlinePass;
let oceanParts = [], cloudMeshes = [], interactiveBlocks = [];
// Pollution/Recharge variant pairs: compressed = recharge, duplicate = pollution
const blockVariants = {
  1: { root: null, duplicate: null, mode: 'recharge' },
  2: { root: null, duplicate: null, mode: 'recharge' },
};
let isolatedVariantBlockId = null; // 1 | 2 | null
let oceanBottomRoot = null;
let oceanTopRoot = null;
let propsModel; // <--- Add this here
let cloudsRoot = null;
let baseGround, baseWithHoles;
let currentStage = 1, isIsolated = false;
let isRainy = false;

let labelP1, labelP2, arrowPump1Left, arrowPump2Right;
let pump1ArrowsRising = false;
let lastPumpStation1Val = 0;
let pump1ArrowFramesLeft = [];   // HTMLImageElement[250] — assets/arrow_frames/1
let pump1ArrowFramesReady = false;
let pump2ArrowsRising = false;
let lastPumpStation2Val = 0;
let pump2ArrowFramesRight = [];  // HTMLImageElement[250] — assets/arrow_frames/2
let pump2ArrowFramesReady = false;
const PUMP_ARROW_FRAME_COUNT = 250;
const PUMP_ARROW_FRAME_FPS = 24; // ~10s per full loop (slower = lower)

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
  rainEnabled: true,
  rainCount: 600,
  rainLength: 0.40,
  windX: 1.5,
  windZ: 0.0,
  rainTop: 3.2,
  rainBottom: -1.0,
  rainMinX: -8,
  rainMaxX: 8,
  key4: 0,
  key5: 0,
  drySeason: 1,
  cloudsEnabled: true,
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
  minX: DEFAULT_MODEL_SETTINGS.rainMinX,
  maxX: DEFAULT_MODEL_SETTINGS.rainMaxX,
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

function applyRainVisibility() {
  if (!rainLines) return;
  const wantRain = !!modelSettings.rainEnabled && modelSettings.rainCount > 0;
  rainLines.visible = isSettingsMode ? wantRain : (isRainy && wantRain);
  rainLines.geometry.setDrawRange(0, modelSettings.rainCount * 2);
}

function applySceneAtmosphere(dark, duration = 1.2) {
  if (!scene || !scene.background) return;
  gsap.killTweensOf(scene.background);
  if (scene.fog) {
    gsap.killTweensOf(scene.fog.color);
    gsap.killTweensOf(scene.fog);
  }
  if (dark) {
    gsap.to(scene.background, { r: 0.04, g: 0.08, b: 0.14, duration });
    if (scene.fog) {
      gsap.to(scene.fog.color, { r: 0.04, g: 0.08, b: 0.14, duration });
      gsap.to(scene.fog, { density: 0.022, duration });
    }
  } else {
    gsap.to(scene.background, { r: 0.941, g: 0.961, b: 0.980, duration });
    if (scene.fog) {
      gsap.to(scene.fog.color, { r: 0.867, g: 0.910, b: 0.949, duration });
      gsap.to(scene.fog, { density: 0.008, duration });
    }
  }
}

function applySettingsRainAtmosphere(duration = 1.2) {
  if (!isSettingsMode) return;
  applySceneAtmosphere(!!modelSettings.rainEnabled, duration);
}

function applyCloudVisibility() {
  if (cloudsRoot) cloudsRoot.visible = !!modelSettings.cloudsEnabled;
  cloudMeshes.forEach(m => { m.visible = !!modelSettings.cloudsEnabled; });
  const opacity = modelSettings.cloudsEnabled ? modelSettings.cloudOpacity : 0;
  cloudMaterialsCollection.forEach(mat => { mat.opacity = opacity; });
  cloudMat.opacity = opacity;
}

function applyRainBoundsFromSettings() {
  rainBounds.minX = modelSettings.rainMinX;
  rainBounds.maxX = modelSettings.rainMaxX;
  rainBounds.minY = modelSettings.rainBottom;
  rainBounds.maxY = modelSettings.rainTop;
}

function applyModelSettings(settings, { syncUI = true, syncPumps = true } = {}) {
  modelSettings = { ...DEFAULT_MODEL_SETTINGS, ...settings };

  sharedWaveUniforms.uWaveHeight.value = modelSettings.waveHeight;
  sharedWaveUniforms.uWaveFrequency.value = modelSettings.waveFreq;
  sharedWaveUniforms.uWaveSpeed.value = modelSettings.waveSpeed;

  applyRainBoundsFromSettings();
  applyRainVisibility();
  applyCloudVisibility();
  if (isSettingsMode) applySettingsRainAtmosphere(0.6);

  setMorphByName('Key 4', modelSettings.key4);
  setMorphByName('Key 5', modelSettings.key5);
  setMorphByName('dry season', modelSettings.drySeason);

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
    ['ms-rain-min-x', 'ms-rain-min-x-val', 'rainMinX', v => v.toFixed(1)],
    ['ms-rain-max-x', 'ms-rain-max-x-val', 'rainMaxX', v => v.toFixed(1)],
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

  const rainEnabledEl = document.getElementById('ms-rain-enabled');
  const cloudsEnabledEl = document.getElementById('ms-clouds-enabled');
  const rainEnabledLabel = document.getElementById('ms-rain-enabled-label');
  const cloudsEnabledLabel = document.getElementById('ms-clouds-enabled-label');
  if (rainEnabledEl) rainEnabledEl.checked = !!modelSettings.rainEnabled;
  if (cloudsEnabledEl) cloudsEnabledEl.checked = !!modelSettings.cloudsEnabled;
  if (rainEnabledLabel) rainEnabledLabel.textContent = modelSettings.rainEnabled ? 'On' : 'Off';
  if (cloudsEnabledLabel) cloudsEnabledLabel.textContent = modelSettings.cloudsEnabled ? 'On' : 'Off';
}

function readSettingsFromUI() {
  return {
    waveHeight: parseFloat(document.getElementById('ms-wave-height').value),
    waveFreq: parseFloat(document.getElementById('ms-wave-freq').value),
    waveSpeed: parseFloat(document.getElementById('ms-wave-speed').value),
    rainEnabled: !!document.getElementById('ms-rain-enabled')?.checked,
    rainCount: parseInt(document.getElementById('ms-rain-count').value, 10),
    rainLength: parseFloat(document.getElementById('ms-rain-length').value),
    windX: parseFloat(document.getElementById('ms-wind-x').value),
    windZ: parseFloat(document.getElementById('ms-wind-z').value),
    rainTop: parseFloat(document.getElementById('ms-rain-top').value),
    rainBottom: parseFloat(document.getElementById('ms-rain-bottom').value),
    rainMinX: parseFloat(document.getElementById('ms-rain-min-x').value),
    rainMaxX: parseFloat(document.getElementById('ms-rain-max-x').value),
    key4: parseFloat(document.getElementById('ms-shape-key-4').value),
    key5: parseFloat(document.getElementById('ms-shape-key-5').value),
    drySeason: parseFloat(document.getElementById('ms-shape-key-dry').value),
    cloudsEnabled: !!document.getElementById('ms-clouds-enabled')?.checked,
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
    modelSettings.rainCount = v;
    applyRainVisibility();
  });
  bind('ms-rain-length', 'ms-rain-length-val', 'rainLength', parseFloat, v => v.toFixed(2));
  bind('ms-wind-x', 'ms-wind-x-val', 'windX', parseFloat, v => v.toFixed(1));
  bind('ms-wind-z', 'ms-wind-z-val', 'windZ', parseFloat, v => v.toFixed(1));
  bind('ms-rain-top', 'ms-rain-top-val', 'rainTop', parseFloat, v => v.toFixed(1), (v) => {
    modelSettings.rainTop = v;
    rainBounds.maxY = v;
  });
  bind('ms-rain-bottom', 'ms-rain-bottom-val', 'rainBottom', parseFloat, v => v.toFixed(1), (v) => {
    modelSettings.rainBottom = v;
    rainBounds.minY = v;
  });
  bind('ms-rain-min-x', 'ms-rain-min-x-val', 'rainMinX', parseFloat, v => v.toFixed(1), (v) => {
    modelSettings.rainMinX = v;
    rainBounds.minX = v;
  });
  bind('ms-rain-max-x', 'ms-rain-max-x-val', 'rainMaxX', parseFloat, v => v.toFixed(1), (v) => {
    modelSettings.rainMaxX = v;
    rainBounds.maxX = v;
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
    modelSettings.cloudOpacity = v;
    applyCloudVisibility();
  });

  const rainEnabledEl = document.getElementById('ms-rain-enabled');
  if (rainEnabledEl) {
    rainEnabledEl.addEventListener('change', (e) => {
      modelSettings.rainEnabled = !!e.target.checked;
      const lbl = document.getElementById('ms-rain-enabled-label');
      if (lbl) lbl.textContent = modelSettings.rainEnabled ? 'On' : 'Off';
      applyRainVisibility();
      applySettingsRainAtmosphere();
    });
  }
  const cloudsEnabledEl = document.getElementById('ms-clouds-enabled');
  if (cloudsEnabledEl) {
    cloudsEnabledEl.addEventListener('change', (e) => {
      modelSettings.cloudsEnabled = !!e.target.checked;
      const lbl = document.getElementById('ms-clouds-enabled-label');
      if (lbl) lbl.textContent = modelSettings.cloudsEnabled ? 'On' : 'Off';
      applyCloudVisibility();
    });
  }
}

window.toggleModelSettings = function(force) {
  if (isIsolated) {
    showPreviewExitWarning();
    return;
  }

  const open = force === undefined ? !isSettingsMode : !!force;
  isSettingsMode = open;
  const btn = document.getElementById('btnModelSettings');
  const panel = document.getElementById('modelSettingsPanel');
  if (btn) btn.classList.toggle('active', open);
  if (panel) panel.classList.toggle('open', open);
  document.body.classList.toggle('settings-mode', open);

  if (open) {
    settingsStageBefore = currentStage;
    // Show full main model, hide infrastructure-only variant
    if (baseGround) baseGround.visible = true;
    if (baseWithHoles) baseWithHoles.visible = false;
    interactiveBlocks.forEach(b => b.visible = false);
    if (labelP1) labelP1.visible = false;
    if (labelP2) labelP2.visible = false;
    if (arrowPump1Left) arrowPump1Left.visible = false;
    if (arrowPump2Right) arrowPump2Right.visible = false;
    outlinePass.selectedObjects = [];
    createRainEngine();
    applyModelSettings(modelSettings, { syncUI: true, syncPumps: true });
    applySettingsRainAtmosphere(0.9);
    flyTo(22, 14, 22, 0, 0, 0);
    renderPresetSlots();
  } else {
    applyRainVisibility();
    applySceneAtmosphere(!!isRainy, 0.9);
    setStage(settingsStageBefore || 1);
  }
};

loadPresetsFromStorage();
bindModelSettingsControls();
bindBlockModeControls();
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

/** Plane driven by a webp frame sequence (single reusable texture). */
function createFrameAnimPlane(width = 1.1, height = 1.1) {
  const geometry = new THREE.PlaneGeometry(width, height);
  const texture = new THREE.Texture();
  texture.colorSpace = THREE.SRGBColorSpace;
  texture.minFilter = THREE.LinearFilter;
  texture.magFilter = THREE.LinearFilter;
  texture.generateMipmaps = false;

  const material = new THREE.MeshBasicMaterial({
    map: texture,
    transparent: true,
    side: THREE.DoubleSide,
    depthWrite: false,
    depthTest: false, // keep arrows visible over the diorama
  });
  const mesh = new THREE.Mesh(geometry, material);
  mesh.visible = false;
  mesh.renderOrder = 10;
  mesh.userData.animTexture = texture;
  mesh.userData.frameIndex = -1;
  return mesh;
}

function loadArrowFrameSequence(folder) {
  const frames = new Array(PUMP_ARROW_FRAME_COUNT);
  const loadOne = (i) => new Promise((resolve) => {
    const n = String(i).padStart(4, '0');
    const img = new Image();
    img.decoding = 'async';
    let done = false;
    const finish = () => { if (!done) { done = true; resolve(img); } };
    img.onload = () => { frames[i - 1] = img; finish(); };
    img.onerror = finish;
    img.src = `assets/arrow_frames/${folder}/${n}.webp`;
    // Avoid hanging forever if a request never settles
    setTimeout(finish, 8000);
  });

  // Load first frame immediately, then the rest in small batches
  return loadOne(1).then(async () => {
    const batchSize = 12;
    for (let start = 2; start <= PUMP_ARROW_FRAME_COUNT; start += batchSize) {
      const batch = [];
      for (let i = start; i < start + batchSize && i <= PUMP_ARROW_FRAME_COUNT; i++) {
        batch.push(loadOne(i));
      }
      await Promise.all(batch);
    }
    return frames;
  });
}

function preloadPump1ArrowFrames() {
  // Ready as soon as frame 0 exists so UI isn't blocked by 250 loads
  const n = '0001';
  const img0 = new Image();
  img0.decoding = 'async';
  img0.onload = () => {
    pump1ArrowFramesLeft[0] = img0;
    pump1ArrowFramesReady = true;
    setArrowFrame(arrowPump1Left, pump1ArrowFramesLeft, 0);
    syncPump1ArrowVisibility(lastPumpStation1Val);
  };
  img0.src = `assets/arrow_frames/1/${n}.webp`;

  loadArrowFrameSequence('1').then((left) => {
    pump1ArrowFramesLeft = left;
    pump1ArrowFramesReady = !!left[0];
    if (pump1ArrowFramesReady) {
      setArrowFrame(arrowPump1Left, pump1ArrowFramesLeft, 0);
      syncPump1ArrowVisibility(lastPumpStation1Val);
    }
  });
}

function preloadPump2ArrowFrames() {
  const n = '0001';
  const img0 = new Image();
  img0.decoding = 'async';
  img0.onload = () => {
    pump2ArrowFramesRight[0] = img0;
    pump2ArrowFramesReady = true;
    setArrowFrame(arrowPump2Right, pump2ArrowFramesRight, 0);
    syncPump2ArrowVisibility(lastPumpStation2Val);
  };
  img0.src = `assets/arrow_frames/2/${n}.webp`;

  loadArrowFrameSequence('2').then((right) => {
    pump2ArrowFramesRight = right;
    pump2ArrowFramesReady = !!right[0];
    if (pump2ArrowFramesReady) {
      setArrowFrame(arrowPump2Right, pump2ArrowFramesRight, 0);
      syncPump2ArrowVisibility(lastPumpStation2Val);
    }
  });
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
  if (label) label.textContent = rising ? 'Freshwater Rising' : 'Freshwater Falling';
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
    label.textContent = 'Rainy Season';
    createRainEngine();
    applyRainVisibility();
    startThunder();
    modelSettings.cloudOpacity = Math.max(modelSettings.cloudOpacity, 0.6);
    applyCloudVisibility();
    applySceneAtmosphere(true, 1.8);
  } else {
    track.classList.remove('rainy');
    thumb.textContent = '☀';
    label.textContent = 'Dry Season';
    stopThunder();
    applyRainVisibility();
    modelSettings.cloudOpacity = 0;
    applyCloudVisibility();
    applySceneAtmosphere(false, 1.8);
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

  const cloudOpacityTarget = modelSettings.cloudsEnabled ? modelSettings.cloudOpacity : 0;
  gsap.to(cloudMat, { opacity: cloudOpacityTarget, duration:1.6 });
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

function prepareRootForFade(root) {
  if (!root) return;
  root.traverse(c => {
    if (!c.isMesh || !c.material) return;
    const mats = Array.isArray(c.material) ? c.material : [c.material];
    mats.forEach(mat => {
      if (mat._fadePrepared) return;
      mat._fadePrepared = true;
      mat._origTransparent = mat.transparent;
      mat._origOpacity = mat.opacity !== undefined ? mat.opacity : 1;
    });
  });
}

function fadeRoot(root, toVisible, duration = 0.85) {
  if (!root) return;
  prepareRootForFade(root);
  if (toVisible) root.visible = true;
  root.traverse(c => {
    if (!c.isMesh || !c.material) return;
    const mats = Array.isArray(c.material) ? c.material : [c.material];
    mats.forEach(mat => {
      gsap.killTweensOf(mat);
      const targetOpacity = mat._origOpacity !== undefined ? mat._origOpacity : 1;
      if (toVisible) {
        c.visible = true;
        mat.transparent = true;
        if (mat.opacity === undefined || mat.opacity < 0.01) mat.opacity = 0;
        gsap.to(mat, {
          opacity: targetOpacity,
          duration,
          onComplete: () => {
            mat.transparent = mat._origTransparent || false;
            mat.opacity = targetOpacity;
          }
        });
      } else {
        mat.transparent = true;
        gsap.to(mat, {
          opacity: 0,
          duration,
          onComplete: () => { c.visible = false; }
        });
      }
    });
  });
}

function syncBlockModeUI(mode) {
  const btnPollution = document.getElementById('btnPollution');
  const btnRecharge = document.getElementById('btnRecharge');
  if (btnPollution) {
    const on = mode === 'pollution';
    btnPollution.classList.toggle('active', on);
    btnPollution.setAttribute('aria-pressed', on ? 'true' : 'false');
  }
  if (btnRecharge) {
    const on = mode === 'recharge';
    btnRecharge.classList.toggle('active', on);
    btnRecharge.setAttribute('aria-pressed', on ? 'true' : 'false');
  }
}

function setBlockVariantMode(blockId, mode, { animate = true } = {}) {
  const pair = blockVariants[blockId];
  if (!pair || !pair.root || !pair.duplicate) return;
  if (mode !== 'pollution' && mode !== 'recharge') return;
  pair.mode = mode;
  if (isolatedVariantBlockId === blockId) syncBlockModeUI(mode);

  const showPollution = mode === 'pollution';
  if (animate) {
    fadeRoot(pair.root, !showPollution);
    fadeRoot(pair.duplicate, showPollution);
  } else {
    prepareRootForFade(pair.root);
    prepareRootForFade(pair.duplicate);
    pair.root.visible = !showPollution;
    pair.duplicate.visible = showPollution;
    [pair.root, pair.duplicate].forEach((root, i) => {
      const show = i === 0 ? !showPollution : showPollution;
      root.traverse(c => {
        if (!c.isMesh || !c.material) return;
        const mats = Array.isArray(c.material) ? c.material : [c.material];
        mats.forEach(mat => {
          gsap.killTweensOf(mat);
          const targetOpacity = mat._origOpacity !== undefined ? mat._origOpacity : 1;
          mat.opacity = show ? targetOpacity : 0;
          mat.transparent = show ? (mat._origTransparent || false) : true;
          c.visible = show;
        });
      });
    });
  }

  if (isIsolated && isolatedVariantBlockId === blockId) {
    outlinePass.selectedObjects = [showPollution ? pair.duplicate : pair.root];
  }
}

function resetAllBlockVariants({ animate = false } = {}) {
  Object.keys(blockVariants).forEach(id => {
    const pair = blockVariants[id];
    if (!pair.root || !pair.duplicate) return;
    setBlockVariantMode(Number(id), 'recharge', { animate });
    pair.duplicate.visible = false;
  });
}

function showBlockModeUI(show) {
  const modeBar = document.getElementById('csBlockMode');
  const infoCard = document.getElementById('blockInfoCard');
  const rp = document.getElementById('rp-s3');
  const cs3 = document.getElementById('cs3');
  const uiPanel = document.getElementById('uiPanel');
  const contextBar = document.getElementById('contextBar');

  if (modeBar) {
    if (show) {
      modeBar.className = 'ctrl-group block-mode-bar';
    } else {
      modeBar.className = 'hidden ctrl-group block-mode-bar';
    }
  }

  if (show) {
    if (infoCard) infoCard.style.display = 'none';
    if (rp) rp.classList.add('hidden');
    if (cs3) cs3.className = 'hidden';
    if (uiPanel) uiPanel.style.opacity = '1';
    if (contextBar) contextBar.style.display = 'none';
  } else {
    if (rp && currentStage === 4) rp.classList.remove('hidden');
    if (cs3 && currentStage === 4 && !isIsolated) cs3.className = 'ctrl-group';
    if (contextBar) contextBar.style.display = '';
  }
}

function bindBlockModeControls() {
  const btnPollution = document.getElementById('btnPollution');
  const btnRecharge = document.getElementById('btnRecharge');
  if (btnPollution) {
    btnPollution.addEventListener('click', () => {
      if (!isolatedVariantBlockId) return;
      setBlockVariantMode(isolatedVariantBlockId, 'pollution');
    });
  }
  if (btnRecharge) {
    btnRecharge.addEventListener('click', () => {
      if (!isolatedVariantBlockId) return;
      setBlockVariantMode(isolatedVariantBlockId, 'recharge');
    });
  }
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
    label.textContent = 'Ocean Off';
    fadeOceanRoot(oceanBottomRoot, false);
    fadeOceanRoot(oceanTopRoot,    false);
    if (covPct) covPct.textContent = '0%';
    if (covBar) { covBar.style.width = '0%'; covBar.className = 'gauge-bar-fill fill-danger'; }
    if (alert)  alert.style.display = 'flex';
  } else {
    track.classList.remove('off');
    thumb.textContent = '🌊';
    label.textContent = 'Ocean On';
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
  if (isIsolated) {
    showPreviewExitWarning();
    return;
  }
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
  document.getElementById('ltext').textContent = label;
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
  labelP1 = createTextPlane("Pump 2: 0%");
  labelP1.position.set(5, -.6, -1); 
  labelP1.scale.set(.5,.5,.5);
  labelP1.rotation.y = Math.PI / 2; 
  labelP1.visible = false;
  scene.add(labelP1);

  labelP2 = createTextPlane("Pump 1: 0%");
  labelP2.position.set(5, -.6, 4); 
  labelP2.scale.set(.5,.5,.5);
  labelP2.rotation.y = Math.PI / 2;
  labelP2.visible = false;
  scene.add(labelP2);

  const arrowSize = 2.4;

  // ── PUMP 1 ARROW POSITION (edit these) ─────────────────────────────
  // offsetLeft : bigger = further LEFT of the PUMP 1 label
  // offsetGap  : bigger = lower; smaller/negative = higher
  arrowPump1Left = createFrameAnimPlane(arrowSize, arrowSize);
  arrowPump1Left.userData.planeH = arrowSize;
  arrowPump1Left.userData.offsetLeft = 1.4;
  arrowPump1Left.userData.offsetGap = 0.1;
  arrowPump1Left.visible = false;
  // Cancel label scale (0.5) so arrow keeps its world size; share label rotation via parent
  arrowPump1Left.scale.setScalar(1 / labelP2.scale.x);
  labelP2.add(arrowPump1Left);

  // ── PUMP 2 ARROW POSITION (edit these) ─────────────────────────────
  // offsetLeft : bigger = further LEFT of the PUMP 2 label
  // offsetGap  : bigger = lower / further BELOW the label
  //              smaller or negative = HIGHER (closer to the label)
  arrowPump2Right = createFrameAnimPlane(arrowSize, arrowSize);
  arrowPump2Right.userData.planeH = arrowSize;
  arrowPump2Right.userData.offsetLeft = 1.5;
  arrowPump2Right.userData.offsetGap = -1.2; // raised up (was 0.1)
  arrowPump2Right.userData.targetLabel = 'p2'; // labelP1 mesh shows "PUMP 2"
  arrowPump2Right.visible = false;
  scene.add(arrowPump2Right);

  placePumpArrows();
  preloadPump1ArrowFrames();
  preloadPump2ArrowFrames();
}

/** Place pump arrows in label-local / label-world space (fixed offsets — independent of zoom). */
function placePumpArrowOnLabel(label, arrow, { parented = true } = {}) {
  if (!label || !arrow) return;

  const offsetLeft = arrow.userData.offsetLeft ?? 0;
  const offsetGap = arrow.userData.offsetGap ?? 0;
  const arrowHalfW = (arrow.userData.planeH || 2.4) / 2;
  const labelHalfHWorld = (2 * label.scale.y) / 2;

  if (parented) {
    const s = label.scale.y || 1;
    const labelHalfHLocal = 1;
    arrow.position.set(
      -offsetLeft / s,
      -(labelHalfHLocal + offsetGap / s + arrowHalfW / s),
      0.25 / s
    );
    return;
  }

  // Scene-space: match label transform, then offset in label local axes
  label.updateWorldMatrix(true, false);
  const pos = new THREE.Vector3();
  const quat = new THREE.Quaternion();
  label.matrixWorld.decompose(pos, quat, new THREE.Vector3());

  const local = new THREE.Vector3(
    -offsetLeft,
    -(labelHalfHWorld + offsetGap + arrowHalfW),
    0.25
  );
  local.applyQuaternion(quat);
  arrow.position.copy(pos).add(local);
  arrow.quaternion.copy(quat);
}

function placePumpArrows() {
  placePumpArrowOnLabel(labelP2, arrowPump1Left, { parented: true });
  placePumpArrowOnLabel(labelP1, arrowPump2Right, { parented: false });
}

/** Pump Station 1 = dialP2 / pumpData.p2 — show arrow while value > 0 (up or down). */
function syncPump1ArrowVisibility(nextVal) {
  lastPumpStation1Val = nextVal;
  pump1ArrowsRising = nextVal > 0.0005;

  const show = currentStage === 3 && !isSettingsMode && pump1ArrowsRising && pump1ArrowFramesReady;
  if (arrowPump1Left) arrowPump1Left.visible = show;
}

/** Pump Station 2 = dialP1 / pumpData.p1 — show arrow while value > 0 (up or down). */
function syncPump2ArrowVisibility(nextVal) {
  lastPumpStation2Val = nextVal;
  pump2ArrowsRising = nextVal > 0.0005;

  const show = currentStage === 3 && !isSettingsMode && pump2ArrowsRising && pump2ArrowFramesReady;
  if (arrowPump2Right) arrowPump2Right.visible = !!show;
}

function setArrowFrame(arrow, frames, index) {
  if (!arrow || !frames?.length) return;
  // Skip holes if a frame hasn't loaded yet
  let img = frames[index];
  if (!img) {
    for (let i = index; i >= 0; i--) {
      if (frames[i]) { img = frames[i]; break; }
    }
  }
  if (!img) return;
  const tex = arrow.userData.animTexture || arrow.material.map;
  if (!tex) return;
  if (arrow.userData.frameIndex === index && tex.image === img) return;
  tex.image = img;
  tex.needsUpdate = true;
  arrow.userData.animTexture = tex;
  arrow.material.map = tex;
  arrow.userData.frameIndex = index;
}

/** Play webp frame sequences for visible pump arrows. */
function animatePumpArrows(elapsed) {
  const frameIndex = Math.floor(elapsed * PUMP_ARROW_FRAME_FPS) % PUMP_ARROW_FRAME_COUNT;
  if (pump1ArrowsRising && pump1ArrowFramesReady) {
    if (arrowPump1Left) arrowPump1Left.visible = currentStage === 3 && !isSettingsMode;
    setArrowFrame(arrowPump1Left, pump1ArrowFramesLeft, frameIndex);
  }
  if (pump2ArrowsRising && pump2ArrowFramesReady) {
    if (arrowPump2Right) arrowPump2Right.visible = currentStage === 3 && !isSettingsMode;
    setArrowFrame(arrowPump2Right, pump2ArrowFramesRight, frameIndex);
  }
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
    { url:'assets/models/block-1-compressed.glb',         label:'Infrastructure block 1', pct:32 },
    { url:'assets/models/block-1-duplicate.glb',          label:'Block 1 pollution variant', pct:40 },
    { url:'assets/models/block-2-compressed.glb',         label:'Infrastructure block 2', pct:48 },
    { url:'assets/models/block-2-duplicate.glb',          label:'Block 2 pollution variant', pct:56 },
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
  else if (/^block-[12]-duplicate/.test(file) || /^block_[12]_duplicate/.test(file)) {
    const idMatch = file.match(/block[-_](\d)[-_]duplicate/);
    const blockId = idMatch ? Number(idMatch[1]) : null;
    if (!blockId || !blockVariants[blockId]) return;
    blockVariants[blockId].duplicate = root;
    root.visible = false;
    root.userData.isBlockVariant = true;
    root.userData.blockPairId = blockId;
    prepareRootForFade(root);
    scene.add(root);
  }
  else if (file.startsWith('block-') || file.startsWith('block_')) {
    root.visible = false;
    root.userData.isInteractable = true;
    if (/^block-1-compressed/.test(file) || /^block_1_compressed/.test(file)) {
      blockVariants[1].root = root;
      root.userData.blockPairId = 1;
      prepareRootForFade(root);
    } else if (/^block-2-compressed/.test(file) || /^block_2_compressed/.test(file)) {
      blockVariants[2].root = root;
      root.userData.blockPairId = 2;
      prepareRootForFade(root);
    }
    interactiveBlocks.push(root);
    scene.add(root);
  }
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
    cloudsRoot = root;
    root.traverse(c => {
      if (!c.isMesh) return;
      c.material = cloudMat;
      cloudMeshes.push(c);
      if (c.material && !cloudMaterialsCollection.includes(c.material)) {
        cloudMaterialsCollection.push(c.material);
      }
    });
    scene.add(root);
    applyCloudVisibility();
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
let previewWarnTimer = null;

function showPreviewExitWarning() {
  const el = document.getElementById('previewWarn');
  if (!el) return;
  el.textContent = 'Please Exit Preview First';
  el.classList.add('show');
  if (previewWarnTimer) clearTimeout(previewWarnTimer);
  previewWarnTimer = setTimeout(() => el.classList.remove('show'), 2600);
}

function setStage(s) {
  // Cube isolate preview: must click EXIT PREVIEW before changing tabs
  if (isIsolated) {
    showPreviewExitWarning();
    return;
  }

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
    pump2ArrowsRising = false;
    if (arrowPump1Left) arrowPump1Left.visible = false;
    if (arrowPump2Right) arrowPump2Right.visible = false;
  } else {
    syncPump1ArrowVisibility(pumpData.p2_t);
    syncPump2ArrowVisibility(pumpData.p1_t);
  }

  // 5. Handle 3D Object Visibility (Infrastructure specific logic moved to stage 4)
  if (baseGround)     baseGround.visible    = (s !== 4);
  if (baseWithHoles)  baseWithHoles.visible = (s === 4);
  if (propsModel)     propsModel.visible    = true;
  interactiveBlocks.forEach(b => b.visible = (s === 4));
  resetAllBlockVariants({ animate: false });
  if (s !== 4) {
    Object.values(blockVariants).forEach(pair => {
      if (pair.root) pair.root.visible = false;
      if (pair.duplicate) pair.duplicate.visible = false;
    });
  }

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
  // Bottom UI: "Pump Station 1" = dialP2 → 3D PUMP 1 arrow
  //             "Pump Station 2" = dialP1 → 3D PUMP 2 arrow
  const dialP1 = document.getElementById('dialP1');
  const dialP2 = document.getElementById('dialP2');
  const onPumpDial = (dial, apply) => {
    const handler = (e) => apply(parseFloat(e.target.value));
    dial.addEventListener('input', handler);
    dial.addEventListener('change', handler);
  };
  onPumpDial(dialP1, (v) => {
    pumpData.p1_t = v;
    syncPump2ArrowVisibility(v);
    refreshPumpUI();
  });
  onPumpDial(dialP2, (v) => {
    pumpData.p2_t = v;
    syncPump1ArrowVisibility(v);
    refreshPumpUI();
  });
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

  if(labelP2) updatePlaneText(labelP1, `Pump 2: ${p1}%`);
  if(labelP1) updatePlaneText(labelP2, `Pump 1: ${p2}%`);
}

// ── ISOLATION ────────────────────────────────────────────────────────
function isolate(obj,idx){
  isIsolated=true;
  isolatedVariantBlockId = (obj && obj.userData && obj.userData.blockPairId) || null;
  const pair = isolatedVariantBlockId ? blockVariants[isolatedVariantBlockId] : null;
  outlinePass.selectedObjects=[obj];
  scene.children.forEach(c=>{
    if(c.isLight) return;
    // Keep both variants available while inspecting a pollution/recharge block
    if (pair && (c === pair.root || c === pair.duplicate)) {
      if(c.userData._v===undefined) c.userData._v = c.visible;
      return;
    }
    if(c!==obj){if(c.userData._v===undefined)c.userData._v=c.visible; c.visible=false;}
  });

  if (pair) {
    setBlockVariantMode(isolatedVariantBlockId, 'recharge', { animate: false });
    showBlockModeUI(true);
  } else {
    showBlockModeUI(false);
  }

  const focusObj = (pair && pair.mode === 'pollution' && pair.duplicate)
    ? pair.duplicate
    : obj;
  const box=new THREE.Box3().setFromObject(focusObj);
  const center=box.getCenter(new THREE.Vector3());
  const size=box.getSize(new THREE.Vector3());
  const max=Math.max(size.x,size.y,size.z);
  flyTo(center.x+max*2.2,center.y+max*1.4,center.z+max*2.2,center.x,center.y,center.z);

  const meta=BLOCK_META[idx]||BLOCK_META[0];
  document.getElementById('biName').textContent=meta.name;
  document.getElementById('biDesc').textContent=meta.desc;
  document.getElementById('biTags').innerHTML=meta.tags.map(t=>`<span class="bi-tag">${t}</span>`).join('');
  // Variant blocks use Pollution/Recharge bottom buttons; others use structure info card
  document.getElementById('blockInfoCard').style.display = pair ? 'none' : 'block';
  document.getElementById('btnExit').style.display='block';
  document.getElementById('uiPanel').style.opacity = pair ? '1' : '0.35';
  document.getElementById('contextBar').textContent='Inspecting Structure  ·  Click Exit Preview to Return';
}

function deIsolate(){
  isIsolated=false;
  if (isolatedVariantBlockId) {
    setBlockVariantMode(isolatedVariantBlockId, 'recharge', { animate: false });
    const pair = blockVariants[isolatedVariantBlockId];
    if (pair && pair.duplicate) pair.duplicate.visible = false;
    showBlockModeUI(false);
  }
  isolatedVariantBlockId = null;
  outlinePass.selectedObjects=interactiveBlocks;
  scene.children.forEach(c=>{if(c.userData._v!==undefined){c.visible=c.userData._v;delete c.userData._v;}});
  Object.values(blockVariants).forEach(pair => {
    if (pair.duplicate) pair.duplicate.visible = false;
  });
  document.getElementById('blockInfoCard').style.display='none';
  document.getElementById('btnExit').style.display='none';
  document.getElementById('uiPanel').style.opacity='1';
  document.getElementById('contextBar').textContent='Orbit · Scroll to Zoom · Drag to Rotate';
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
    placePumpArrows();
    animatePumpArrows(settingsClock.getElapsedTime());
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

