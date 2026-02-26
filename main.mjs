// ═══════════════════════════════════════════════════════════════════════════════
// CAPTURE THE FLAG — State-of-the-Art Reactive Agent Architecture
// Reference: docs/strategy.md
// ═══════════════════════════════════════════════════════════════════════════════

// ─── IMPORTS ─────────────────────────────────────────────────────────────────
import {
  getObjectsByPrototype,
  findClosestByPath,
  findClosestByRange,
  findInRange,
  getRange,
  getDirection,
  getTicks,
  getCpuTime,
  getTerrainAt,
  getObjectById,
} from 'game/utils';

import { searchPath, CostMatrix } from 'game/path-finder';

import {
  Creep,
  Flag,
  StructureTower,
  StructureContainer,
  StructureSpawn,
  StructureExtension,
  Source,
} from 'game/prototypes';

import { arenaInfo } from 'game';
import { Visual } from 'game/visual';

import {
  ATTACK,
  RANGED_ATTACK,
  HEAL,
  MOVE,
  CARRY,
  WORK,
  TOUGH,
  RESOURCE_ENERGY,
  TOWER_RANGE,
  TOWER_COOLDOWN,
  TERRAIN_WALL,
  TERRAIN_SWAMP,
  ATTACK_POWER,
  RANGED_ATTACK_POWER,
  HEAL_POWER,
  RANGED_HEAL_POWER,
  OK,
} from 'game/constants';

import { BodyPart } from 'arena/season_2/capture_the_flag/basic';

// ─── ROLE CONSTANTS ──────────────────────────────────────────────────────────
const ROLE_VANGUARD  = 'vanguard';
const ROLE_RANGER    = 'ranger';
const ROLE_MEDIC     = 'medic';
const ROLE_SENTINEL  = 'sentinel';

// ─── CONFIGURATION ──────────────────────────────────────────────────────────
const RETREAT_HP_RATIO         = 0.30;
const INFLUENCE_REFRESH_TICKS  = 3;
const ROLE_REEVAL_TICKS        = 30;
const BODYPART_DEVIATE_RANGE   = 3;
const KITE_FLEE_RANGE          = 3;
const EMERGENCY_FLEE_RANGE     = 10;
const SENTINEL_PATROL_RANGE    = 4;
const TOWER_THREAT_WEIGHT      = 0.20;
const ENEMY_THREAT_RADIUS      = 6;

// Phase boundaries (ticks)
const PHASE_EXPAND_END    = 150;
const PHASE_CONSOLIDATE   = 500;
const PHASE_ASSAULT_END   = 1500;
const TICK_LIMIT           = 2000;

// Tower charging: how full (%) a tower must be before we stop charging it
const TOWER_CHARGE_THRESHOLD = 0.8; // 80% full → stop wasting time, go fight
// Max range at which a creep deviates to charge a tower opportunistically
const TOWER_CHARGE_RANGE     = 8;

// ─── PERSISTENT STATE (survives across ticks) ────────────────────────────────
const creepRoles       = new Map();   // id → role string
const towerChargeState = new Map();   // id → 'WITHDRAW' | 'DELIVER'
const towerChargeTarget= new Map();   // id → tower id being charged
let influenceMatrix    = null;
let lastInfluenceTick  = -Infinity;
let initialized        = false;

// ─── DIAGNOSTIC / METRICS STATE ────────────────────────────────────────────────
const diag = {
  startRoster:      null,    // snapshot of initial role counts
  spawnEvents:      [],      // {tick, body, role}
  deathEvents:      [],      // {tick, role, hp}
  flagEvents:       [],      // {tick, type:'capture'|'lose', flag}
  actionCounts:     {},      // role → {move,attack,heal,harvest,idle}
  cpuSamples:       [],      // ns per tick
  idleTicks:        {},      // creep.id → count of idle ticks
  lastFlagSnapshot: null,    // previous tick's flag my/enemy counts
  gameDumped:       false,
};

// ─── PER-TICK WORLD STATE (refreshed every tick) ─────────────────────────────
let myCreeps      = [];
let enemies       = [];
let allFlags      = [];
let myFlag        = null;
let enemyFlags    = [];
let neutralFlags  = [];
let allTowers     = [];
let myTowers      = [];
let enemyTowers   = [];
let containers    = [];
let bodyParts     = [];
let allSources    = [];  // Source objects (energy wells near towers)
let tick          = 0;
// per-tick action tracking (for idle detection)
const tickActions = new Map(); // creep.id → action string this tick

// ═══════════════════════════════════════════════════════════════════════════════
//  1 · SENSE LAYER — World State Refresh
// ═══════════════════════════════════════════════════════════════════════════════

function refreshWorldState() {
  tick = getTicks();
  tickActions.clear();

  // ── Creeps ────────────────────────────────────────────
  const allCreeps = getObjectsByPrototype(Creep);
  const prevMyIds = new Set(myCreeps.map(c => c.id));
  myCreeps = allCreeps.filter(c => c.my);
  enemies  = allCreeps.filter(c => !c.my);

  // Death detection: creeps that vanished since last tick
  const aliveIds = new Set(myCreeps.map(c => c.id));
  for (const id of prevMyIds) {
    if (!aliveIds.has(id)) {
      const role = creepRoles.get(id) || 'unknown';
      diag.deathEvents.push({ tick, id, role });
      creepRoles.delete(id);
      towerChargeState.delete(id);
      towerChargeTarget.delete(id);
    }
  }

  // ── Flags ─────────────────────────────────────────────
  allFlags     = getObjectsByPrototype(Flag);
  myFlag       = allFlags.find(f => f.my === true) || null;
  enemyFlags   = allFlags.filter(f => f.my === false);
  neutralFlags = allFlags.filter(f => f.my === undefined);

  // Flag capture/loss detection
  const curMy  = allFlags.filter(f => f.my === true).length;
  const curEn  = allFlags.filter(f => f.my === false).length;
  if (diag.lastFlagSnapshot) {
    const { my: prevMy, enemy: prevEn } = diag.lastFlagSnapshot;
    if (curMy > prevMy)  diag.flagEvents.push({ tick, type: 'capture', myCount: curMy });
    if (curMy < prevMy)  diag.flagEvents.push({ tick, type: 'lose',    myCount: curMy });
    if (curEn > prevEn)  diag.flagEvents.push({ tick, type: 'enemy_captured', enemyCount: curEn });
  }
  diag.lastFlagSnapshot = { my: curMy, enemy: curEn };

  // ── Structures ────────────────────────────────────────
  allTowers    = getObjectsByPrototype(StructureTower);
  myTowers     = allTowers.filter(t => t.my === true);
  enemyTowers  = allTowers.filter(t => t.my === false);
  containers   = getObjectsByPrototype(StructureContainer);
  // Sources exist near towers — all sources regardless of ownership
  allSources   = getObjectsByPrototype(Source);

  bodyParts  = getObjectsByPrototype(BodyPart);
}

// ═══════════════════════════════════════════════════════════════════════════════
//  2 · BODY INTROSPECTION HELPERS
// ═══════════════════════════════════════════════════════════════════════════════

function countParts(creep, type) {
  return creep.body.filter(p => p.type === type).length;
}

function countActive(creep, type) {
  return creep.body.filter(p => p.type === type && p.hits > 0).length;
}

function hasActive(creep, type) {
  return creep.body.some(p => p.type === type && p.hits > 0);
}

// ═══════════════════════════════════════════════════════════════════════════════
//  3 · ROLE CLASSIFICATION & ASSIGNMENT
// ═══════════════════════════════════════════════════════════════════════════════

function classifyCreep(creep) {
  const a = countParts(creep, ATTACK);
  const r = countParts(creep, RANGED_ATTACK);
  const h = countParts(creep, HEAL);

  // Medic: primarily HEAL
  if (h > 0 && h >= a && h >= r) return ROLE_MEDIC;

  // Ranger: primarily RANGED_ATTACK
  if (r > 0 && r >= a) return ROLE_RANGER;

  // Vanguard: primarily ATTACK (or any combat creep)
  if (a > 0) return ROLE_VANGUARD;

  // Fallbacks based on any part
  if (h > 0) return ROLE_MEDIC;
  if (r > 0) return ROLE_RANGER;

  // CARRY-only or TOUGH-only creeps: treat as vanguard (they can charge towers
  // opportunistically via tryTowerCharge but still participate in flag captures)
  return ROLE_VANGUARD;
}

function assignRoles() {
  const counts = {
    [ROLE_VANGUARD]: 0, [ROLE_RANGER]: 0, [ROLE_MEDIC]: 0, [ROLE_SENTINEL]: 0,
  };

  for (const creep of myCreeps) {
    const role = classifyCreep(creep);
    creepRoles.set(creep.id, role);
    counts[role]++;
  }

  // Snapshot initial roster for diagnostics
  if (!diag.startRoster) {
    diag.startRoster = { ...counts, total: myCreeps.length };
    for (const role of Object.keys(counts)) {
      diag.actionCounts[role] = { move: 0, attack: 0, heal: 0, harvest: 0, idle: 0 };
    }
    console.log(`[INIT T${tick}] Roster: ${JSON.stringify(diag.startRoster)}`);
  }

  // Promote 1 vanguard to sentinel for home flag defense
  if (counts[ROLE_SENTINEL] === 0) {
    const pool = myCreeps
      .filter(c => creepRoles.get(c.id) === ROLE_VANGUARD)
      .sort((a, b) => countParts(b, TOUGH) - countParts(a, TOUGH));
    if (pool.length > 2 && myFlag) {
      const sentinel = pool.reduce((best, c) =>
        getRange(c, myFlag) < getRange(best, myFlag) ? c : best
      );
      creepRoles.set(sentinel.id, ROLE_SENTINEL);
      counts[ROLE_SENTINEL]++;
      counts[ROLE_VANGUARD]--;
    }
  }
}

function reevaluateRoles() {
  // Prune dead creeps
  const aliveIds = new Set(myCreeps.map(c => c.id));
  for (const id of creepRoles.keys()) {
    if (!aliveIds.has(id)) {
      creepRoles.delete(id);
      towerChargeState.delete(id);
      towerChargeTarget.delete(id);
    }
  }

  const counts = {};
  for (const role of creepRoles.values()) {
    counts[role] = (counts[role] || 0) + 1;
  }

  // No vanguards? Promote strongest ranger
  if (!counts[ROLE_VANGUARD] && (counts[ROLE_RANGER] || 0) > 1) {
    const rangers = myCreeps.filter(c => creepRoles.get(c.id) === ROLE_RANGER);
    const best = rangers.sort((a, b) => countParts(b, ATTACK) - countParts(a, ATTACK))[0];
    if (best) creepRoles.set(best.id, ROLE_VANGUARD);
  }

  // No medics? Convert a ranger that has HEAL parts
  if (!counts[ROLE_MEDIC] && (counts[ROLE_RANGER] || 0) > 2) {
    const candidates = myCreeps.filter(c =>
      creepRoles.get(c.id) === ROLE_RANGER && countParts(c, HEAL) > 0
    );
    if (candidates.length > 0) {
      const best = candidates.sort((a, b) => countParts(b, HEAL) - countParts(a, HEAL))[0];
      creepRoles.set(best.id, ROLE_MEDIC);
    }
  }

  // Sentinel died? Promote nearest to flag
  if (!counts[ROLE_SENTINEL] && myFlag) {
    const pool = myCreeps.filter(c => {
      const r = creepRoles.get(c.id);
      return r === ROLE_VANGUARD || r === ROLE_RANGER;
    });
    if (pool.length > 3) {
      const closest = pool.reduce((b, c) =>
        getRange(c, myFlag) < getRange(b, myFlag) ? c : b
      );
      creepRoles.set(closest.id, ROLE_SENTINEL);
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  4 · THREAT ASSESSMENT ENGINE
// ═══════════════════════════════════════════════════════════════════════════════

function threatScore(enemy) {
  const atk = countActive(enemy, ATTACK);
  const rng = countActive(enemy, RANGED_ATTACK);
  const hea = countActive(enemy, HEAL);
  return (atk * ATTACK_POWER) + (rng * RANGED_ATTACK_POWER) + (hea * HEAL_POWER)
       + (enemy.hits / enemy.hitsMax);
}

/**
 * Focus-fire target selection with kill-priority heuristic.
 * Order: kill-secured → healers → lowest HP ratio → highest threat.
 */
function selectFocusTarget(fromPos, eligible) {
  if (eligible.length === 0) return null;
  if (eligible.length === 1) return eligible[0];

  return eligible.slice().sort((a, b) => {
    // 1. Kill-secured (< 100 HP)
    const aLow = a.hits <= 100;
    const bLow = b.hits <= 100;
    if (aLow !== bLow) return aLow ? -1 : 1;

    // 2. Healers first (remove sustain)
    const aH = countActive(a, HEAL) > 0;
    const bH = countActive(b, HEAL) > 0;
    if (aH !== bH) return aH ? -1 : 1;

    // 3. Lowest HP ratio
    const rA = a.hits / a.hitsMax;
    const rB = b.hits / b.hitsMax;
    if (rA !== rB) return rA - rB;

    // 4. Highest threat
    return threatScore(b) - threatScore(a);
  })[0];
}

// ═══════════════════════════════════════════════════════════════════════════════
//  5 · INFLUENCE MAP (CostMatrix-Based Potential Field)
// ═══════════════════════════════════════════════════════════════════════════════

function buildInfluenceMap() {
  const cm = new CostMatrix();

  // ── Enemy threat field ─────────────────────────────────
  for (const enemy of enemies) {
    const t = Math.max(1, threatScore(enemy));
    for (let dx = -ENEMY_THREAT_RADIUS; dx <= ENEMY_THREAT_RADIUS; dx++) {
      for (let dy = -ENEMY_THREAT_RADIUS; dy <= ENEMY_THREAT_RADIUS; dy++) {
        const nx = enemy.x + dx;
        const ny = enemy.y + dy;
        if (nx < 0 || nx > 99 || ny < 0 || ny > 99) continue;
        const dist = Math.max(Math.abs(dx), Math.abs(dy));
        if (dist > ENEMY_THREAT_RADIUS) continue;
        if (getTerrainAt({ x: nx, y: ny }) === TERRAIN_WALL) continue;
        const penalty = Math.min(200, Math.floor(t / (dist + 1) * 0.4));
        const base = getTerrainAt({ x: nx, y: ny }) === TERRAIN_SWAMP ? 10 : 2;
        cm.set(nx, ny, Math.min(254, Math.max(cm.get(nx, ny), base + penalty)));
      }
    }
  }

  // ── Enemy tower danger zone ────────────────────────────
  for (const tower of enemyTowers) {
    const energy = tower.store ? tower.store.getUsedCapacity(RESOURCE_ENERGY) : 0;
    if (energy <= 0) continue;
    for (let dx = -TOWER_RANGE; dx <= TOWER_RANGE; dx++) {
      for (let dy = -TOWER_RANGE; dy <= TOWER_RANGE; dy++) {
        const nx = tower.x + dx;
        const ny = tower.y + dy;
        if (nx < 0 || nx > 99 || ny < 0 || ny > 99) continue;
        const dist = Math.max(Math.abs(dx), Math.abs(dy));
        if (dist > TOWER_RANGE) continue;
        if (getTerrainAt({ x: nx, y: ny }) === TERRAIN_WALL) continue;
        const dmg = Math.max(0, 1000 - 50 * (dist - 1));
        const penalty = Math.min(200, Math.floor(dmg * TOWER_THREAT_WEIGHT));
        cm.set(nx, ny, Math.min(254, Math.max(cm.get(nx, ny), penalty)));
      }
    }
  }

  // ── Ally stacking avoidance ────────────────────────────
  for (const ally of myCreeps) {
    const cur = cm.get(ally.x, ally.y);
    cm.set(ally.x, ally.y, Math.min(254, cur + 4));
  }

  influenceMatrix   = cm;
  lastInfluenceTick = tick;
}

function getInfluenceMap() {
  if (!influenceMatrix || tick - lastInfluenceTick >= INFLUENCE_REFRESH_TICKS) {
    buildInfluenceMap();
  }
  return influenceMatrix;
}

function pathOpts(flee = false) {
  return {
    costMatrix: getInfluenceMap(),
    flee,
    plainCost: 2,
    swampCost: 10,
    maxOps: 2000,
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//  6 · PHASE CONTROLLER
// ═══════════════════════════════════════════════════════════════════════════════

function getPhase() {
  if (tick <= PHASE_EXPAND_END)  return 1;
  if (tick <= PHASE_CONSOLIDATE) return 2;
  if (tick <= PHASE_ASSAULT_END) return 3;
  return 4;
}

function myFlagCount()    { return allFlags.filter(f => f.my === true).length; }
function enemyFlagCount() { return allFlags.filter(f => f.my === false).length; }

// ═══════════════════════════════════════════════════════════════════════════════
//  7 · RETREAT PROTOCOL (Behavior Layer 5)
// ═══════════════════════════════════════════════════════════════════════════════

function shouldRetreat(creep) {
  return creep.hits < creep.hitsMax * RETREAT_HP_RATIO;
}

function executeRetreat(creep) {
  // Self-heal if possible (takes the action slot)
  if (hasActive(creep, HEAL)) {
    creep.heal(creep);
  } else if (hasActive(creep, RANGED_ATTACK)) {
    // Shoot while running
    const inR3 = findInRange(creep, enemies, 3);
    if (inR3.length >= 3) creep.rangedMassAttack();
    else if (inR3.length > 0) creep.rangedAttack(inR3[0]);
  }

  // Flee from nearby enemies
  const nearby = findInRange(creep, enemies, 7);
  if (nearby.length > 0) {
    const result = searchPath(
      creep,
      nearby.map(e => ({ pos: e, range: EMERGENCY_FLEE_RANGE })),
      pathOpts(true),
    );
    if (result.path.length > 0) {
      const nx = result.path[0];
      creep.move(getDirection(nx.x - creep.x, nx.y - creep.y));
      return;
    }
  }

  // Fallback: run to own flag
  if (myFlag) creep.moveTo(myFlag);
}

// ═══════════════════════════════════════════════════════════════════════════════
//  8 · BODY PART COLLECTION (Behavior Layer 1)
// ═══════════════════════════════════════════════════════════════════════════════

function tryPickupBodyPart(creep) {
  if (bodyParts.length === 0) return false;

  // Already on same tile → collected automatically
  const onTile = bodyParts.filter(bp => bp.x === creep.x && bp.y === creep.y);
  if (onTile.length > 0) return true;

  // Deviate slightly if close
  const nearby = findInRange(creep, bodyParts, BODYPART_DEVIATE_RANGE);
  if (nearby.length === 0) return false;

  const prio = { [HEAL]: 4, [ATTACK]: 3, [RANGED_ATTACK]: 2, [MOVE]: 1 };
  nearby.sort((a, b) => (prio[b.type] || 0) - (prio[a.type] || 0));
  creep.moveTo(nearby[0]);
  return true;
}

// ═══════════════════════════════════════════════════════════════════════════════
//  9 · OBJECTIVE SELECTOR — phase-aware target
// ═══════════════════════════════════════════════════════════════════════════════

function getObjective(creep, role) {
  const phase = getPhase();

  // Phase 1: rush neutral flags
  if (phase === 1) {
    if (neutralFlags.length > 0) return findClosestByRange(creep, neutralFlags);
    if (enemyFlags.length > 0)   return findClosestByRange(creep, enemyFlags);
    return myFlag;
  }

  // Phase 2-3: push enemy flags
  if (phase === 2 || phase === 3) {
    if (enemyFlags.length > 0)   return findClosestByRange(creep, enemyFlags);
    if (neutralFlags.length > 0) return findClosestByRange(creep, neutralFlags);
    return myFlag;
  }

  // Phase 4: endgame clock management
  const myF = myFlagCount();
  const enF = enemyFlagCount();

  if (myF > enF) {
    // Ahead → defend captured positions
    if (role === ROLE_VANGUARD) {
      const captured = allFlags.filter(f => f.my === true && f !== myFlag);
      if (captured.length > 0) return findClosestByRange(creep, captured);
    }
    return myFlag;
  }

  // Behind or tied → rush weakest-defended enemy flag
  if (enemyFlags.length > 0) {
    return enemyFlags.reduce((best, f) => {
      const dBest = myCreeps.reduce((s, c) => s + getRange(c, best), 0);
      const dF    = myCreeps.reduce((s, c) => s + getRange(c, f), 0);
      return dF < dBest ? f : best;
    });
  }
  if (neutralFlags.length > 0) return findClosestByRange(creep, neutralFlags);
  return myFlag;
}

// ═══════════════════════════════════════════════════════════════════════════════
//  ACTION RECORDING HELPER
// ═══════════════════════════════════════════════════════════════════════════════
function recordAction(creep, action) {
  tickActions.set(creep.id, action);
  const role = creepRoles.get(creep.id) || 'unknown';
  if (!diag.actionCounts[role]) {
    diag.actionCounts[role] = { move: 0, attack: 0, heal: 0, harvest: 0, idle: 0 };
  }
  const key = (['move','attack','heal','harvest'].includes(action)) ? action : 'idle';
  diag.actionCounts[role][key]++;
}

// ═══════════════════════════════════════════════════════════════════════════════
//  10b · OPPORTUNISTIC TOWER CHARGING (modular, called by all behaviors)
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * If this creep has CARRY parts and there is a nearby tower that needs energy,
 * deviate to fill it from the closest Source. Returns true and records action
 * if the creep is actively charging; returns false otherwise so the caller
 * can continue with its normal behavior.
 *
 * Strategy:
 *   - Any creep with CARRY can charge a tower.
 *   - Towers near a Source form a self-contained charge loop:
 *       Source → withdraw → deliver to tower → repeat until tower full.
 *   - Once the nearest friendly tower is >= TOWER_CHARGE_THRESHOLD full,
 *     the creep stops charging and resumes its combat role.
 *   - We only deviate if the tower or source is within TOWER_CHARGE_RANGE tiles.
 */
function tryTowerCharge(creep) {
  if (!hasActive(creep, CARRY)) return false;

  const energy   = creep.store ? (creep.store.getUsedCapacity(RESOURCE_ENERGY) || 0) : 0;
  const free     = creep.store ? (creep.store.getFreeCapacity(RESOURCE_ENERGY) || 0) : 0;
  const capacity = energy + free;
  if (capacity === 0) return false;

  // Find nearest friendly tower that needs energy
  const hungerTowers = myTowers.filter(t => {
    const cap  = t.store ? t.store.getCapacity(RESOURCE_ENERGY)    : 0;
    const used = t.store ? t.store.getUsedCapacity(RESOURCE_ENERGY) : 0;
    return cap > 0 && (used / cap) < TOWER_CHARGE_THRESHOLD;
  });
  if (hungerTowers.length === 0) {
    // All towers sufficiently charged — clear any lingering charge state
    towerChargeState.delete(creep.id);
    towerChargeTarget.delete(creep.id);
    return false;
  }

  const nearestTower = findClosestByRange(creep, hungerTowers);
  if (!nearestTower) return false;

  // Only deviate if we are within range of the tower or already in charge mode
  const inChargeMode = towerChargeState.has(creep.id);
  const distToTower  = getRange(creep, nearestTower);
  if (!inChargeMode && distToTower > TOWER_CHARGE_RANGE) return false;

  // Find the Source nearest to this tower (each tower has its own Source)
  const sourcesWithEnergy = allSources.filter(s => s.energy > 0);
  const nearestSource = sourcesWithEnergy.length > 0
    ? findClosestByRange(nearestTower, sourcesWithEnergy)
    : null;

  let state = towerChargeState.get(creep.id) || 'WITHDRAW';

  // FSM transitions
  if (state === 'WITHDRAW') {
    if (free <= 0) { state = 'DELIVER'; towerChargeState.set(creep.id, state); }
    else if (!nearestSource || nearestSource.energy === 0) {
      // Source depleted — if we already carry something, deliver it
      if (energy > 0) { state = 'DELIVER'; towerChargeState.set(creep.id, state); }
      else { towerChargeState.delete(creep.id); return false; } // nothing to do
    }
  }
  if (state === 'DELIVER' && energy <= 0) {
    state = 'WITHDRAW'; towerChargeState.set(creep.id, state);
    // Check if tower is now sufficiently charged
    const used = nearestTower.store ? nearestTower.store.getUsedCapacity(RESOURCE_ENERGY) : 0;
    const cap  = nearestTower.store ? nearestTower.store.getCapacity(RESOURCE_ENERGY)    : 1;
    if ((used / cap) >= TOWER_CHARGE_THRESHOLD) {
      towerChargeState.delete(creep.id);
      towerChargeTarget.delete(creep.id);
      return false; // tower is charged — resume combat
    }
  }

  towerChargeState.set(creep.id, state);
  towerChargeTarget.set(creep.id, nearestTower.id);

  if (state === 'WITHDRAW') {
    if (!nearestSource) return false;
    if (getRange(creep, nearestSource) <= 1) {
      creep.withdraw(nearestSource, RESOURCE_ENERGY);
      recordAction(creep, 'harvest');
    } else {
      creep.moveTo(nearestSource, pathOpts());
      recordAction(creep, 'move');
    }
  } else {
    if (getRange(creep, nearestTower) <= 1) {
      creep.transfer(nearestTower, RESOURCE_ENERGY);
      recordAction(creep, 'harvest');
    } else {
      creep.moveTo(nearestTower, pathOpts());
      recordAction(creep, 'move');
    }
  }
  return true;
}

// ═══════════════════════════════════════════════════════════════════════════════
//  11 · BEHAVIOR — Vanguard (Melee DPS + Flag Capture)
// ═══════════════════════════════════════════════════════════════════════════════

function behaviorVanguard(creep) {
  // L5 — Emergency retreat
  if (shouldRetreat(creep)) { executeRetreat(creep); recordAction(creep, 'move'); return; }

  // La — Opportunistic tower charging (only if no enemies nearby)
  const nearbyEnemies = findInRange(creep, enemies, 8);
  if (nearbyEnemies.length === 0 && tryTowerCharge(creep)) return;

  // L4/L3 — Melee combat: attack adjacent enemies
  const adj = findInRange(creep, enemies, 1);
  if (adj.length > 0) {
    const target = selectFocusTarget(creep, adj);
    if (target) {
      creep.attack(target);
      creep.moveTo(target); // chase the target
      recordAction(creep, 'attack');
    }
    return;
  }

  // Charge nearby enemies (2–5 range)
  const nearby = findInRange(creep, enemies, 5);
  if (nearby.length > 0) {
    const target = selectFocusTarget(creep, nearby);
    if (target) {
      creep.moveTo(target, pathOpts());
      // Ranged attack while closing if available
      if (hasActive(creep, RANGED_ATTACK)) {
        const inR3 = findInRange(creep, enemies, 3);
        if (inR3.length >= 3) {
          creep.rangedMassAttack();
        } else if (inR3.length > 0) {
          creep.rangedAttack(selectFocusTarget(creep, inR3) || inR3[0]);
        }
      }
      recordAction(creep, 'attack');
      return;
    }
  }

  // L1 — BodyPart pickup
  if (tryPickupBodyPart(creep)) { recordAction(creep, 'move'); return; }

  // L2 — Advance toward objective
  const obj = getObjective(creep, ROLE_VANGUARD);
  if (obj) { creep.moveTo(obj, pathOpts()); recordAction(creep, 'move'); }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  11 · BEHAVIOR — Ranger (Ranged DPS + Kiting Micro)
// ═══════════════════════════════════════════════════════════════════════════════

function behaviorRanger(creep) {
  // L5 — Emergency retreat
  if (shouldRetreat(creep)) { executeRetreat(creep); recordAction(creep, 'move'); return; }

  const inR1 = findInRange(creep, enemies, 1);
  const inR3 = findInRange(creep, enemies, 3);

  // La — Opportunistic tower charging (only if area is clear)
  if (inR1.length === 0 && inR3.length === 0 && tryTowerCharge(creep)) return;

  // L4 — Kiting: enemies too close → retreat + shoot
  if (inR1.length > 0) {
    const result = searchPath(
      creep,
      inR1.map(e => ({ pos: e, range: KITE_FLEE_RANGE })),
      pathOpts(true),
    );
    if (result.path.length > 0) {
      const nx = result.path[0];
      creep.move(getDirection(nx.x - creep.x, nx.y - creep.y));
    }
    if (inR3.length >= 3) {
      creep.rangedMassAttack();
    } else {
      const t = selectFocusTarget(creep, inR1);
      if (t) creep.rangedAttack(t);
    }
    recordAction(creep, 'attack');
    return;
  }

  // L3 — Optimal range: hold + fire
  if (inR3.length > 0) {
    if (inR3.length >= 3) {
      creep.rangedMassAttack();
    } else {
      const t = selectFocusTarget(creep, inR3);
      if (t) creep.rangedAttack(t);
    }
    // Maintain distance ≥ 3 from nearest enemy
    const nearest = findClosestByRange(creep, inR3);
    if (nearest && creep.getRangeTo(nearest) < 3) {
      const result = searchPath(
        creep,
        [{ pos: nearest, range: KITE_FLEE_RANGE }],
        pathOpts(true),
      );
      if (result.path.length > 0) {
        const nx = result.path[0];
        creep.move(getDirection(nx.x - creep.x, nx.y - creep.y));
      }
    }
    recordAction(creep, 'attack');
    return;
  }

  // L1 — BodyPart pickup
  if (tryPickupBodyPart(creep)) { recordAction(creep, 'move'); return; }

  // L2 — Advance toward objective
  const phase = getPhase();
  if (phase === 4 && myFlagCount() > enemyFlagCount() && myFlag) {
    creep.moveTo(myFlag, pathOpts());
  } else {
    const obj = getObjective(creep, ROLE_RANGER);
    if (obj) creep.moveTo(obj, pathOpts());
  }
  recordAction(creep, 'move');
}

// ═══════════════════════════════════════════════════════════════════════════════
//  12 · BEHAVIOR — Medic (Triage Healing Protocol)
// ═══════════════════════════════════════════════════════════════════════════════

function behaviorMedic(creep) {
  // L5 — Self-preservation: self-heal + flee
  if (shouldRetreat(creep)) {
    if (hasActive(creep, HEAL)) creep.heal(creep);
    const nearby = findInRange(creep, enemies, 6);
    if (nearby.length > 0) {
      const result = searchPath(
        creep,
        nearby.map(e => ({ pos: e, range: EMERGENCY_FLEE_RANGE })),
        pathOpts(true),
      );
      if (result.path.length > 0) {
        const nx = result.path[0];
        creep.move(getDirection(nx.x - creep.x, nx.y - creep.y));
      }
    } else if (myFlag) {
      creep.moveTo(myFlag);
    }
    recordAction(creep, 'move');
    return;
  }

  // La — Opportunistic tower charging when area is safe
  const nearbyEnemies = findInRange(creep, enemies, 6);
  if (nearbyEnemies.length === 0) {
    const damaged = myCreeps.filter(c => c.id !== creep.id && c.hits < c.hitsMax);
    if (damaged.length === 0 && tryTowerCharge(creep)) return;
  }

  // L3 — Triage: find best heal target
  const damaged = myCreeps.filter(c => c.id !== creep.id && c.hits < c.hitsMax);

  if (damaged.length > 0) {
    const scored = damaged.map(ally => {
      const dmgPct    = (1 - ally.hits / ally.hitsMax) * 100;
      const role      = creepRoles.get(ally.id);
      const roleBonus = (role === ROLE_VANGUARD || role === ROLE_SENTINEL) ? 20 : 0;
      const dist      = creep.getRangeTo(ally);
      const adjBonus  = dist <= 1 ? 10 : 0;
      return { ally, score: dmgPct + roleBonus + adjBonus, dist };
    });
    scored.sort((a, b) => b.score - a.score);
    const best = scored[0];

    if (best.dist <= 1) {
      creep.heal(best.ally);
      creep.moveTo(best.ally);
    } else if (best.dist <= 3) {
      creep.rangedHeal(best.ally);
      creep.moveTo(best.ally);
    } else {
      creep.moveTo(best.ally, pathOpts());
      // Opportunistic heal on another nearby ally while walking
      const adjAllies  = findInRange(creep, damaged, 1);
      const nearAllies = findInRange(creep, damaged, 3);
      if (adjAllies.length > 0) {
        creep.heal(adjAllies[0]);
      } else if (nearAllies.length > 0) {
        creep.rangedHeal(nearAllies[0]);
      }
    }
    recordAction(creep, 'heal');
    return;
  }

  // Self-heal if hurt
  if (creep.hits < creep.hitsMax && hasActive(creep, HEAL)) {
    creep.heal(creep);
    recordAction(creep, 'heal');
    return;
  }

  // L1 — BodyPart pickup
  if (tryPickupBodyPart(creep)) { recordAction(creep, 'move'); return; }

  // L0 — Follow squad: stay near combat creeps (deathball cohesion)
  const combatants = myCreeps.filter(c => {
    const r = creepRoles.get(c.id);
    return r === ROLE_VANGUARD || r === ROLE_RANGER;
  });
  if (combatants.length > 0) {
    const nearest = findClosestByRange(creep, combatants);
    if (nearest && creep.getRangeTo(nearest) > 2) {
      creep.moveTo(nearest, pathOpts());
    }
  }
  recordAction(creep, 'move');
}

// ═══════════════════════════════════════════════════════════════════════════════
//  15 · BEHAVIOR — Sentinel (Home Flag Defense)
// ═══════════════════════════════════════════════════════════════════════════════

function behaviorSentinel(creep) {
  if (!myFlag) { behaviorVanguard(creep); return; }

  const selfDamaged = creep.hits < creep.hitsMax;

  // Enemies threatening our flag
  const threatsNearFlag = findInRange(myFlag, enemies, 8);
  const adj  = findInRange(creep, enemies, 1);
  const inR3 = findInRange(creep, enemies, 3);

  let actionTaken = false;

  // Prefer melee if adjacent
  if (adj.length > 0 && hasActive(creep, ATTACK)) {
    const target = selectFocusTarget(creep, adj);
    if (target) { creep.attack(target); actionTaken = true; }
  }
  // Ranged if not in melee
  if (!actionTaken && inR3.length > 0 && hasActive(creep, RANGED_ATTACK)) {
    if (inR3.length >= 3) {
      creep.rangedMassAttack();
      actionTaken = true;
    } else {
      const target = selectFocusTarget(creep, inR3);
      if (target) { creep.rangedAttack(target); actionTaken = true; }
    }
  }
  // Self-heal if no combat action
  if (!actionTaken && selfDamaged && hasActive(creep, HEAL)) {
    creep.heal(creep);
    actionTaken = true;
  }

  // Opportunistic tower charging when calm
  if (!actionTaken && threatsNearFlag.length === 0) {
    if (tryTowerCharge(creep)) return;
  }

  // Movement: intercept threats or patrol near flag
  if (threatsNearFlag.length > 0) {
    const closest = findClosestByRange(creep, threatsNearFlag);
    if (closest) creep.moveTo(closest, pathOpts());
  } else if (creep.getRangeTo(myFlag) > SENTINEL_PATROL_RANGE) {
    creep.moveTo(myFlag, pathOpts());
  }

  recordAction(creep, actionTaken ? 'attack' : 'move');
}

// ═══════════════════════════════════════════════════════════════════════════════
//  16 · TOWER CONTROLLER
// ═══════════════════════════════════════════════════════════════════════════════

function towerController() {
  for (const tower of myTowers) {
    const energy = tower.store ? tower.store.getUsedCapacity(RESOURCE_ENERGY) : 0;
    if (energy <= 0 || tower.cooldown > 0) continue;

    const enemiesInRange = findInRange(tower, enemies, TOWER_RANGE);

    if (enemiesInRange.length > 0) {
      // Kill-secured targets first, then closest (max damage via falloff)
      const killable = enemiesInRange.filter(e => e.hits <= 200);
      const target = killable.length > 0
        ? findClosestByRange(tower, killable)
        : findClosestByRange(tower, enemiesInRange);
      if (target) { tower.attack(target); continue; }
    }

    // Heal damaged allies in range
    const alliesInRange = findInRange(tower, myCreeps, TOWER_RANGE);
    const damagedAllies = alliesInRange.filter(c => c.hits < c.hitsMax);
    if (damagedAllies.length > 0) {
      damagedAllies.sort((a, b) => (a.hits / a.hitsMax) - (b.hits / b.hitsMax));
      tower.heal(damagedAllies[0]);
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//  17 · PULL CHAIN — Fast Deployment Helper
// ═══════════════════════════════════════════════════════════════════════════════

function tryPullChain(fast, slow, destination) {
  if (!hasActive(fast, MOVE) || fast.fatigue > 0) return false;
  if (getRange(slow, destination) <= 1) return false;

  if (getRange(fast, slow) <= 1) {
    fast.pull(slow);
    fast.moveTo(destination, pathOpts());
    slow.moveTo(fast);
    return true;
  }
  fast.moveTo(slow, pathOpts());
  return true;
}

// ═══════════════════════════════════════════════════════════════════════════════
//  18 · DIAGNOSTICS & METRICS
// ═══════════════════════════════════════════════════════════════════════════════

const DIAG_INTERVAL = 100; // print compact log every N ticks

// Compact per-interval summary
function tickLog() {
  if (tick % DIAG_INTERVAL !== 0 && tick !== 1) return;

  const cpu = Math.round(getCpuTime() / 1e6); // ms
  diag.cpuSamples.push(cpu);

  const roles = {};
  for (const r of creepRoles.values()) roles[r] = (roles[r] || 0) + 1;

  // Tower energy status
  const towerStatus = myTowers.map(t => {
    const used = t.store ? t.store.getUsedCapacity(RESOURCE_ENERGY) : 0;
    const cap  = t.store ? t.store.getCapacity(RESOURCE_ENERGY)    : 0;
    return `${used}/${cap}`;
  }).join(' ');

  const srcE = allSources.reduce((s, src) => s + src.energy, 0);
  const myF  = allFlags.filter(f => f.my === true).length;
  const enF  = allFlags.filter(f => f.my === false).length;
  const neuF = allFlags.filter(f => f.my === undefined).length;

  console.log(
    `[T${tick}] CPU=${cpu}ms alive=${myCreeps.length} enemies=${enemies.length}` +
    ` flags(my=${myF} en=${enF} neu=${neuF})` +
    ` towers=[${towerStatus}] srcE=${srcE}` +
    ` roles=${JSON.stringify(roles)}`
  );
}

// Detect creeps that had no recorded action this tick
function detectAndLogIdle() {
  for (const creep of myCreeps) {
    if (creep.spawning) continue;
    if (!tickActions.has(creep.id)) {
      // behavior ran but didn’t call recordAction — count as idle
      const role = creepRoles.get(creep.id) || 'unknown';
      diag.idleTicks[creep.id] = (diag.idleTicks[creep.id] || 0) + 1;
      if (!diag.actionCounts[role]) {
        diag.actionCounts[role] = { move: 0, attack: 0, heal: 0, harvest: 0, idle: 0 };
      }
      diag.actionCounts[role].idle++;
      // Warn only once every 20 idle ticks so we don’t spam
      if (diag.idleTicks[creep.id] % 20 === 1) {
        console.log(`[IDLE T${tick}] creep ${creep.id.slice(-4)} role=${role} idleTicks=${diag.idleTicks[creep.id]}`);
      }
    }
  }
}

// Draw Visual overlays: role labels + HP bars
function drawVisuals() {
  const vis = new Visual(1, false);
  for (const creep of myCreeps) {
    if (creep.spawning) continue;
    const role = (creepRoles.get(creep.id) || '?')[0].toUpperCase();
    const hpRatio = creep.hits / creep.hitsMax;
    const color = hpRatio > 0.6 ? '#00ff88' : hpRatio > 0.3 ? '#ffaa00' : '#ff3333';
    vis.text(role, { x: creep.x, y: creep.y - 0.6 }, { font: '0.4', color: '#ffffff', opacity: 0.85 });
    // HP bar
    vis.rect({ x: creep.x - 0.5, y: creep.y + 0.4 }, 1, 0.15, { fill: '#333333', opacity: 0.7, stroke: undefined });
    vis.rect({ x: creep.x - 0.5, y: creep.y + 0.4 }, hpRatio, 0.15, { fill: color, opacity: 0.9, stroke: undefined });
  }
  // Source energy bars
  for (const src of getObjectsByPrototype(Source)) {
    const ratio = src.energy / src.energyCapacity;
    vis.rect({ x: src.x - 0.5, y: src.y + 0.4 }, ratio, 0.15, { fill: '#ffff00', opacity: 0.7, stroke: undefined });
    vis.text(`${src.energy}`, { x: src.x, y: src.y - 0.6 }, { font: '0.35', color: '#ffff88', opacity: 0.9 });
  }
}

// Full end-of-game diagnostic dump
function dumpEndGameDiag() {
  if (diag.gameDumped) return;
  diag.gameDumped = true;

  const myF  = allFlags.filter(f => f.my === true).length;
  const enF  = allFlags.filter(f => f.my === false).length;
  const neuF = allFlags.filter(f => f.my === undefined).length;

  const cpuAvg = diag.cpuSamples.length
    ? Math.round(diag.cpuSamples.reduce((a,b)=>a+b,0) / diag.cpuSamples.length)
    : 0;
  const cpuMax = diag.cpuSamples.length ? Math.max(...diag.cpuSamples) : 0;

  // Count total idle ticks
  const totalIdle = Object.values(diag.idleTicks).reduce((a,b)=>a+b,0);

  console.log('=== CTF END-OF-MATCH DIAGNOSTICS ===');
  console.log(`Tick: ${tick} | Survivors: ${myCreeps.length} | Flags: my=${myF} enemy=${enF} neutral=${neuF}`);
  console.log(`Start roster: ${JSON.stringify(diag.startRoster)}`);
  console.log(`Death events (${diag.deathEvents.length}): ` + diag.deathEvents.map(e => `T${e.tick}:${e.role}`).join(' | '));
  console.log(`Flag events (${diag.flagEvents.length}): ` + diag.flagEvents.map(e => `T${e.tick}:${e.type}`).join(' | '));
  console.log(`Total idle creep-ticks: ${totalIdle}`);
  console.log(`CPU samples: avg=${cpuAvg}ms max=${cpuMax}ms over ${diag.cpuSamples.length} intervals`);
  console.log('Action counts by role:');
  for (const [role, counts] of Object.entries(diag.actionCounts)) {
    console.log(`  ${role}: ${JSON.stringify(counts)}`);
  }
  console.log('=== END DIAGNOSTICS ===');
}
// ═══════════════════════════════════════════════════════════════════════════════

// ═══════════════════════════════════════════════════════════════════════════════
//  19 · MAIN LOOP — Per-Tick Orchestrator
// ═══════════════════════════════════════════════════════════════════════════════

export function loop() {
  // ─── SENSE ──────────────────────────────────────────────
  refreshWorldState();

  // ─── INITIALIZATION (first tick) ────────────────────────
  if (!initialized) {
    assignRoles();
    buildInfluenceMap();
    initialized = true;
  }

  // ─── PERIODIC ROLE RE-EVALUATION ────────────────────────
  if (tick > 1 && tick % ROLE_REEVAL_TICKS === 0) {
    reevaluateRoles();
  }

  // ─── REFRESH INFLUENCE MAP ─────────────────────────────
  getInfluenceMap();

  // ─── REFRESH TOWER LIST (captures change ownership) ────
  myTowers = allTowers.filter(t => t.my === true);

  // ─── TOWER ACTIONS ──────────────────────────────────────
  towerController();

  // ─── CREEP ACTIONS ──────────────────────────────────────
  for (const creep of myCreeps) {
    if (creep.spawning) continue;
    const role = creepRoles.get(creep.id);

    switch (role) {
      case ROLE_VANGUARD:  behaviorVanguard(creep);  break;
      case ROLE_RANGER:    behaviorRanger(creep);    break;
      case ROLE_MEDIC:     behaviorMedic(creep);     break;
      case ROLE_SENTINEL:  behaviorSentinel(creep);  break;
      default:             behaviorVanguard(creep);  break;
    }
  }

  // ─── DIAGNOSTICS ────────────────────────────────────────
  detectAndLogIdle();
  tickLog();
  drawVisuals();

  // ─── END-OF-GAME DUMP ───────────────────────────────────
  const isLastTick = tick >= (arenaInfo.ticksLimit - 1);
  const allDead    = myCreeps.length === 0 && initialized;
  if (isLastTick || allDead) {
    dumpEndGameDiag();
  }
}