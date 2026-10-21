module
public import proofs.JointThermoComplexity.Complexity.SmallCoefficientControl
public import proofs.JointThermoComplexity.Complexity.NaturalSkip
public import proofs.JointThermoComplexity.Complexity.FixedOutput

set_option autoImplicit false
@[expose] public section

/-! Constant finite control consumes one signed field and emits its bounded coefficient. -/

namespace JointThermoComplexity.Complexity.SmallCoefficientMachine
open _root_.Complexity _root_.Complexity.TM HeaderAt SmallCoefficientControl
variable {w : ℕ}

inductive State where
  | sign
  | marker : Bool → Magnitude → State
  | payload : Bool → Magnitude → State
  | emit : Bool → Magnitude → Fin 7 → State
  | done
  deriving DecidableEq

instance : Fintype State where
  elems := ((({.sign, .done} ∪ Finset.univ.image (fun p : Bool × Magnitude => State.marker p.1 p.2)) ∪
    Finset.univ.image (fun p : Bool × Magnitude => State.payload p.1 p.2)) ∪
    Finset.univ.image (fun p : Bool × Magnitude × Fin 7 => State.emit p.1 p.2.1 p.2.2))
  complete s := by cases s <;> simp

def emitState (negate negative : Bool) (m : Magnitude) (q : Fin ((word negate negative m).length + 1)) : State :=
  if q.val = (word negate negative m).length then .done else .emit negative m ⟨q.val, by have := word_bound negate negative m; omega⟩

def advance (q : State) (_si : Γ) (sw : Fin w → Γ) (so : Γ) :
    State × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (q, (fun j => readBackWrite (sw j)), readBackWrite so, .right, (fun j => idleDir (sw j)), idleDir so)

def action (negate : Bool) (q : State) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    State × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 := match q with
  | .sign => match si with
    | .zero => advance (.marker false .empty) si sw so
    | .one => advance (.marker true .empty) si sw so
    | _ => allReadBack (.emit false .bad 0) si sw so
  | .marker negative m => match si with
    | .one => advance (.payload negative m) si sw so
    | .zero => advance (.emit negative m 0) si sw so
    | _ => allReadBack (.emit negative .bad 0) si sw so
  | .payload negative m => match si with
    | .zero => advance (.marker negative (push m false)) si sw so
    | .one => advance (.marker negative (push m true)) si sw so
    | _ => allReadBack (.emit negative .bad 0) si sw so
  | .emit negative m i =>
      if h : i.val < (word negate negative m).length then
        IntegerMachine.mapAction (emitState negate negative m)
          ((emitBitsTM (n := w) (word negate negative m)).δ ⟨i.val, by omega⟩ si sw so)
      else allReadBack .done si sw so
  | .done => allReadBack .done si sw so

def machine (negate : Bool) (w : ℕ) : TM w where
  Q := State
  qstart := .sign
  qhalt := .done
  δ := action negate
  δ_right_of_start q si sw so := by
    cases q with
    | sign =>
      cases si <;> first
        | exact rightOfStart_allReadBack _ sw so
        | exact ⟨fun _ => rfl, fun _ h => idleDir_right_of_start h, idleDir_right_of_start⟩
    | marker negative m =>
      cases si <;> first
        | exact rightOfStart_allReadBack _ sw so
        | exact ⟨fun _ => rfl, fun _ h => idleDir_right_of_start h, idleDir_right_of_start⟩
    | payload negative m =>
      cases si <;> first
        | exact rightOfStart_allReadBack _ sw so
        | exact ⟨fun _ => rfl, fun _ h => idleDir_right_of_start h, idleDir_right_of_start⟩
    | emit negative m i =>
      dsimp only [action]
      split
      · exact (emitBitsTM (n := w) (word negate negative m)).δ_right_of_start _ si sw so
      · exact rightOfStart_allReadBack si sw so
    | done => exact rightOfStart_allReadBack si sw so

def emitCfg (negate negative : Bool) (m : Magnitude)
    (c : Cfg w (emitBitsTM (n := w) (word negate negative m)).Q) : Cfg w (machine negate w).Q :=
  ⟨emitState negate negative m c.state, c.input, c.work, c.output⟩

theorem emit_step (negate negative : Bool) (m : Magnitude)
    {c d : Cfg w (emitBitsTM (n := w) (word negate negative m)).Q}
    (h : (emitBitsTM (n := w) (word negate negative m)).step c = some d) :
    (machine negate w).step (emitCfg negate negative m c) = some (emitCfg negate negative m d) := by
  have hn := state_ne_qhalt_of_step h
  have hv : c.state.val ≠ (word negate negative m).length := fun he => hn (Fin.ext he)
  have hc : c.state.val < (word negate negative m).length := by have := c.state.isLt; omega
  simp only [TM.step, hn, ↓reduceIte] at h
  have hd := Option.some.inj h
  subst d
  simp only [TM.step, machine, emitCfg, emitState, hv, ↓reduceIte, action, hc, ↓reduceDIte,
    IntegerMachine.mapAction]
  rfl

theorem emit_reaches (negate negative : Bool) (m : Magnitude)
    {c d : Cfg w (emitBitsTM (n := w) (word negate negative m)).Q} {t : ℕ}
    (h : (emitBitsTM (n := w) (word negate negative m)).reachesIn t c d) :
    (machine negate w).reachesIn t (emitCfg negate negative m c) (emitCfg negate negative m d) :=
  reachesIn_map (tm := emitBitsTM (word negate negative m)) (tm' := machine negate w)
    (emitCfg negate negative m) (fun _ _ => emit_step negate negative m) h

end JointThermoComplexity.Complexity.SmallCoefficientMachine

#print axioms JointThermoComplexity.Complexity.SmallCoefficientMachine.emit_reaches
