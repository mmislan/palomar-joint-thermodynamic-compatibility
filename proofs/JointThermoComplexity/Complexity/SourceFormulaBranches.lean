module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaPairCall
public import proofs.JointThermoComplexity.Complexity.SourceFormulaCounter

set_option autoImplicit false
@[expose] public section

/-! Actual formula branches select their operation before a nested term parse overwrites tag bits. -/

namespace JointThermoComplexity.Complexity.SourceFormulaBranches
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters SourceFormulaScan
variable {n : ℕ}

def afterLeaf (arity L v : ℕ) (before input : List Bool) : SourceTermLoopState.State :=
  ⟨before ++ (SourceTermPair.state arity L input).before, (SourceTermPair.state arity L input).input,
    if (SourceTermPair.state arity L input).valid then v else v + 1, (SourceTermPair.state arity L input).valid⟩

def leafMachine (d : Layout n) : TM (n + 2) := seqTM (SourceFormulaPairCall.machine d) (SourceFormulaCounter.decrementIf d)
def timeBound (L v : ℕ) : ℕ := 34 * L ^ 2 + 93 * L + 2 * v + 46

theorem leaf_hoareTime (d : Layout n) (L arity v : ℕ) (ha : arity.bits.length ≤ L)
    (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R) :
    (leafMachine d).HoareTime (Inv d L arity emitted R ⟨before, input, v + 1, true⟩)
      (Inv d L arity emitted R (afterLeaf arity L v before input)) (timeBound L v) := by
  have hp := SourceFormulaPairCall.hoareTime d L arity (v + 1) ha before input emitted hlen R hR
  have hc := SourceFormulaCounter.decrementIf_hoareTime d L arity v (SourceTermPair.state arity L input).valid
    (before ++ (SourceTermPair.state arity L input).before) (SourceTermPair.state arity L input).input emitted R hR
  have hfull := seqTM_hoareTime (SourceFormulaPairCall.machine d) (SourceFormulaCounter.decrementIf d) hp (by
    rintro inp work out ⟨hc, hr, hv, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr, hv, hf⟩) hc
  exact hfull.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by
    unfold timeBound SourceFormulaPairCall.timeBound
    omega)

def bodyState (arity L v : ℕ) (bits before input : List Bool) : SourceTermLoopState.State :=
  ⟨before ++ SourceFormulaToken.bodyTaken arity L bits input, SourceFormulaToken.bodyRest arity L bits input,
    if SourceFormulaToken.bodyAccepted arity L bits input then v + (classify bits).children else v + 1,
    SourceFormulaToken.bodyAccepted arity L bits input⟩

def machine (d : Layout n) (bits : List Bool) : TM (n + 2) := match classify bits with
  | .eq | .lt => leafMachine d
  | .truth | .falsity => SourceFormulaCounter.move d false
  | .conj | .disj => SourceFormulaCounter.move d true
  | .invalid => SourceTermToken.setStatus (NaturalScanBuffer.flag n) false

theorem hoareTime (d : Layout n) (bits : List Bool) (L arity v : ℕ) (ha : arity.bits.length ≤ L)
    (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R) :
    (machine d bits).HoareTime (Inv d L arity emitted R ⟨before, input, v + 1, true⟩)
      (Inv d L arity emitted R (bodyState arity L v bits before input)) (timeBound L v) := by
  cases hk : classify bits with
  | truth =>
    have h := SourceFormulaCounter.move_hoareTime d false L arity v true before input emitted R hR
    simpa only [machine, bodyState, SourceFormulaToken.bodyTaken, SourceFormulaToken.bodyRest, SourceFormulaToken.bodyAccepted,
      hk, Kind.children, SourceFormulaCounter.moveCount, ↓reduceIte, Bool.false_eq_true, Nat.add_zero, List.append_nil] using
      h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold timeBound; omega : 2 * v + 12 ≤ timeBound L v)
  | falsity =>
    have h := SourceFormulaCounter.move_hoareTime d false L arity v true before input emitted R hR
    simpa only [machine, bodyState, SourceFormulaToken.bodyTaken, SourceFormulaToken.bodyRest, SourceFormulaToken.bodyAccepted,
      hk, Kind.children, SourceFormulaCounter.moveCount, ↓reduceIte, Bool.false_eq_true, Nat.add_zero, List.append_nil] using
      h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold timeBound; omega : 2 * v + 12 ≤ timeBound L v)
  | eq =>
    simpa only [machine, bodyState, afterLeaf, SourceFormulaToken.bodyTaken, SourceFormulaToken.bodyRest,
      SourceFormulaToken.bodyAccepted, hk, Kind.children, Nat.add_zero] using
      leaf_hoareTime d L arity v ha before input emitted hlen R hR
  | lt =>
    simpa only [machine, bodyState, afterLeaf, SourceFormulaToken.bodyTaken, SourceFormulaToken.bodyRest,
      SourceFormulaToken.bodyAccepted, hk, Kind.children, Nat.add_zero] using
      leaf_hoareTime d L arity v ha before input emitted hlen R hR
  | conj =>
    have h := SourceFormulaCounter.move_hoareTime d true L arity v true before input emitted R hR
    simpa only [machine, bodyState, SourceFormulaToken.bodyTaken, SourceFormulaToken.bodyRest, SourceFormulaToken.bodyAccepted,
      hk, Kind.children, SourceFormulaCounter.moveCount, ↓reduceIte, List.append_nil] using
      h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold timeBound; omega : 2 * v + 12 ≤ timeBound L v)
  | disj =>
    have h := SourceFormulaCounter.move_hoareTime d true L arity v true before input emitted R hR
    simpa only [machine, bodyState, SourceFormulaToken.bodyTaken, SourceFormulaToken.bodyRest, SourceFormulaToken.bodyAccepted,
      hk, Kind.children, SourceFormulaCounter.moveCount, ↓reduceIte, List.append_nil] using
      h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold timeBound; omega : 2 * v + 12 ≤ timeBound L v)
  | invalid =>
    have h := SourceFormulaCounter.status_hoareTime d L arity (v + 1) true false before input emitted R hR
    simpa only [machine, bodyState, SourceFormulaToken.bodyTaken, SourceFormulaToken.bodyRest, SourceFormulaToken.bodyAccepted,
      hk, Kind.children, Bool.false_eq_true, ↓reduceIte, List.append_nil] using
      h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold timeBound; omega : 1 ≤ timeBound L v)

def dispatchMachine (d : Layout n) : TM (n + 2) :=
  SourceTagDispatch.machine (List.ofFn (fun i => (d.tags i).castSucc)) (machine d)

theorem dispatch_hoareTime (d : Layout n) (bits : List Bool) (hbits : bits.length = 3)
    (L arity v : ℕ) (ha : arity.bits.length ≤ L) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R) :
    (dispatchMachine d).HoareTime
      (fun inp work out => Inv d L arity emitted R ⟨before, input, v + 1, true⟩ inp work out ∧
        SourceTagDispatch.Reads (List.ofFn (fun i => (d.tags i).castSucc)) bits work)
      (Inv d L arity emitted R (bodyState arity L v bits before input)) (timeBound L v + 6) := by
  let P : (Fin (n + 2) → Tape) → Prop := fun work => Ready d L arity R work ∧
    IsReg (v + 1) (work d.formulaPending.castSucc) ∧ (work (NaturalScanBuffer.flag n)).read = Γ.one
  let Q : (Fin (n + 2) → Tape) → Prop := fun work => Ready d L arity R work ∧
    IsReg (bodyState arity L v bits before input).pending (work d.formulaPending.castSucc) ∧
    (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (bodyState arity L v bits before input).valid
  have h := SourceTagDispatch.hoareTime (List.ofFn (fun i => (d.tags i).castSucc)) bits
    (by simpa only [List.length_ofFn] using hbits) (machine d) before input emitted
    (bodyState arity L v bits before input).before (bodyState arity L v bits before input).input emitted P Q (timeBound L v)
    (hoareTime d bits L arity v ha before input emitted hlen R hR)
  exact h.consequence (by
    rintro inp work out ⟨⟨hc, hr, hv, hf⟩, ht⟩
    exact ⟨hc, ⟨hr, hv, hf⟩, ht⟩) (fun _ _ _ h => h) (by simp only [List.length_ofFn]; omega)

end JointThermoComplexity.Complexity.SourceFormulaBranches

#print axioms JointThermoComplexity.Complexity.SourceFormulaBranches.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceFormulaBranches.dispatch_hoareTime
