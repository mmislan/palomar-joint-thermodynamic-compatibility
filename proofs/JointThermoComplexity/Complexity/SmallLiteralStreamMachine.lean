module
public import proofs.JointThermoComplexity.Complexity.SmallLiteralStreamCode
public import proofs.JointThermoComplexity.Complexity.NaturalSkip

set_option autoImplicit false
@[expose] public section

/-! Finite control reads binary magnitude pairs and emits constant arithmetic fragments. -/

namespace JointThermoComplexity.Complexity.SmallLiteralStreamMachine
open _root_.Complexity _root_.Complexity.TM HeaderAt SmallLiteralStream
variable {w : ℕ}

inductive State where
  | marker | bit
  | chunk : Bool → Fin 23 → State
  | base : Fin 6 → State
  | done
  deriving DecidableEq

instance : Fintype State where
  elems := ({.marker, .bit, .done} ∪ Finset.univ.image (fun p : Bool × Fin 23 => State.chunk p.1 p.2)) ∪
    Finset.univ.image State.base
  complete s := by cases s <;> simp

def chunkState (b : Bool) (q : Fin ((chunk b).length + 1)) : State :=
  if q.val = (chunk b).length then .marker else .chunk b ⟨q.val, by have := (chunk_bound b).2; omega⟩

def baseState (q : Fin (base.length + 1)) : State :=
  if q.val = base.length then .done else .base ⟨q.val, by have := base_length; omega⟩

def advance (q : State) (_si : Γ) (sw : Fin w → Γ) (so : Γ) :
    State × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (q, (fun j => readBackWrite (sw j)), readBackWrite so, .right, (fun j => idleDir (sw j)), idleDir so)

def action (q : State) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    State × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 := match q with
  | .marker => match si with
    | .one => advance .bit si sw so
    | .zero => advance (.base 0) si sw so
    | _ => allReadBack (.base 0) si sw so
  | .bit => match si with
    | .zero => advance (.chunk false 0) si sw so
    | .one => advance (.chunk true 0) si sw so
    | _ => allReadBack (.base 0) si sw so
  | .chunk b i =>
      if h : i.val < (chunk b).length then
        IntegerMachine.mapAction (chunkState b) ((emitBitsTM (n := w) (chunk b)).δ ⟨i.val, by omega⟩ si sw so)
      else allReadBack .marker si sw so
  | .base i =>
      if h : i.val < base.length then
        IntegerMachine.mapAction baseState ((emitBitsTM (n := w) base).δ ⟨i.val, by omega⟩ si sw so)
      else allReadBack .done si sw so
  | .done => allReadBack .done si sw so

def machine (w : ℕ) : TM w where
  Q := State
  qstart := .marker
  qhalt := .done
  δ := action
  δ_right_of_start q si sw so := by
    cases q with
    | marker =>
      cases si <;> first
        | exact rightOfStart_allReadBack _ sw so
        | exact ⟨fun _ => rfl, fun _ h => idleDir_right_of_start h, idleDir_right_of_start⟩
    | bit =>
      cases si <;> first
        | exact rightOfStart_allReadBack _ sw so
        | exact ⟨fun _ => rfl, fun _ h => idleDir_right_of_start h, idleDir_right_of_start⟩
    | chunk b i =>
      dsimp only [action]
      split
      · exact (emitBitsTM (n := w) (chunk b)).δ_right_of_start _ si sw so
      · exact rightOfStart_allReadBack si sw so
    | base i =>
      dsimp only [action]
      split
      · exact (emitBitsTM (n := w) base).δ_right_of_start _ si sw so
      · exact rightOfStart_allReadBack si sw so
    | done => exact rightOfStart_allReadBack si sw so

def chunkCfg (b : Bool) (c : Cfg w (emitBitsTM (n := w) (chunk b)).Q) : Cfg w (machine w).Q :=
  ⟨chunkState b c.state, c.input, c.work, c.output⟩

def baseCfg (c : Cfg w (emitBitsTM (n := w) base).Q) : Cfg w (machine w).Q :=
  ⟨baseState c.state, c.input, c.work, c.output⟩

theorem chunk_step (b : Bool) {c d : Cfg w (emitBitsTM (n := w) (chunk b)).Q}
    (h : (emitBitsTM (n := w) (chunk b)).step c = some d) :
    (machine w).step (chunkCfg b c) = some (chunkCfg b d) := by
  have hn := state_ne_qhalt_of_step h
  have hv : c.state.val ≠ (chunk b).length := fun he => hn (Fin.ext he)
  have hc : c.state.val < (chunk b).length := by have := c.state.isLt; omega
  simp only [TM.step, hn, ↓reduceIte] at h
  have hd := Option.some.inj h
  subst d
  simp only [TM.step, machine, chunkCfg, chunkState, hv, ↓reduceIte, action, hc, ↓reduceDIte,
    IntegerMachine.mapAction]
  rfl

theorem base_step {c d : Cfg w (emitBitsTM (n := w) base).Q}
    (h : (emitBitsTM (n := w) base).step c = some d) : (machine w).step (baseCfg c) = some (baseCfg d) := by
  have hn := state_ne_qhalt_of_step h
  have hv : c.state.val ≠ base.length := fun he => hn (Fin.ext he)
  have hc : c.state.val < base.length := by have := c.state.isLt; omega
  simp only [TM.step, hn, ↓reduceIte] at h
  have hd := Option.some.inj h
  subst d
  simp only [TM.step, machine, baseCfg, baseState, hv, ↓reduceIte, action, hc, ↓reduceDIte,
    IntegerMachine.mapAction]
  rfl

theorem chunk_reaches (b : Bool) {c d : Cfg w (emitBitsTM (n := w) (chunk b)).Q} {t : ℕ}
    (h : (emitBitsTM (n := w) (chunk b)).reachesIn t c d) :
    (machine w).reachesIn t (chunkCfg b c) (chunkCfg b d) :=
  reachesIn_map (tm := emitBitsTM (chunk b)) (tm' := machine w) (chunkCfg b) (fun _ _ => chunk_step b) h

theorem base_reaches {c d : Cfg w (emitBitsTM (n := w) base).Q} {t : ℕ}
    (h : (emitBitsTM (n := w) base).reachesIn t c d) : (machine w).reachesIn t (baseCfg c) (baseCfg d) :=
  reachesIn_map (tm := emitBitsTM base) (tm' := machine w) baseCfg (fun _ _ => base_step) h

end JointThermoComplexity.Complexity.SmallLiteralStreamMachine

#print axioms JointThermoComplexity.Complexity.SmallLiteralStreamMachine.chunk_reaches
#print axioms JointThermoComplexity.Complexity.SmallLiteralStreamMachine.base_reaches
