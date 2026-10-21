module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaLoopState
public import proofs.JointThermoComplexity.Complexity.FlagBranchNonone

set_option autoImplicit false
@[expose] public section

/-! Sticky rejection and completion guards around the actual formula-head machine. -/

namespace JointThermoComplexity.Complexity.SourceFormulaLoopBody
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters
open SourceTermLoopState (State)
open SourceFormulaLoopState
variable {n : ℕ}

def Extra (d : Layout n) (L arity : ℕ) (R : (Fin (n + 1) → Tape) → Prop)
    (s : State) (work : Fin (n + 2) → Tape) : Prop :=
  Ready d L arity R work ∧ IsReg s.pending (work d.formulaPending.castSucc) ∧
    (work (NaturalScanBuffer.flag n)).read = Γ.ofBool s.valid

def pendingMachine (d : Layout n) : TM (n + 2) :=
  FlagBranch.machine d.formulaPending.castSucc (SourceFormulaStep.machine d) (emitBitsTM [])

def machine (d : Layout n) : TM (n + 2) :=
  FlagBranch.machine (NaturalScanBuffer.flag n) (pendingMachine d) (emitBitsTM [])

theorem noop_hoareTime (d : Layout n) (L arity : ℕ) (emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (s : State) :
    (emitBitsTM (n := n + 2) []).HoareTime (Inv d L arity emitted R s) (Inv d L arity emitted R s) 0 := by
  have h := FixedOutput.hoareTime [] s.before s.input emitted (Extra d L arity R s)
  exact h.consequence (by rintro inp work out ⟨hc, hr, hp⟩; exact ⟨hc, hr.base.safe, hr, hp⟩)
    (by simpa only [List.append_nil] using fun _ _ _ h => ⟨h.1, h.2.2⟩) le_rfl

theorem pending_hoareTime (d : Layout n) (L arity P count : ℕ) (hcount : count ≤ P)
    (ha : arity.bits.length ≤ L) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R) :
    (pendingMachine d).HoareTime (Inv d L arity emitted R ⟨before, input, count, true⟩)
      (Inv d L arity emitted R (step arity L ⟨before, input, count, true⟩))
      (34 * L ^ 2 + 93 * L + 2 * P + 61) := by
  cases count with
  | zero =>
    let s : State := ⟨before, input, 0, true⟩
    have hb := FlagBranchNonone.hoareTime d.formulaPending.castSucc (SourceFormulaStep.machine d) (emitBitsTM [])
      before input emitted before input emitted (Extra d L arity R s) (Extra d L arity R s)
      0 (noop_hoareTime d L arity emitted R s)
    exact hb.consequence (by
      rintro inp work out h
      refine ⟨h, ?_⟩
      have hv := h.2.2.1.read_eq
      change (work d.formulaPending.castSucc).read = Γ.blank at hv
      rw [hv]
      decide) (fun _ _ _ h => h) (by omega)
  | succ v =>
    let s : State := ⟨before, input, v + 1, true⟩
    have hs := SourceFormulaStep.hoareTime d L arity v ha true before input emitted hlen R hR
    have hyes : (SourceFormulaStep.machine d).HoareTime (Inv d L arity emitted R s)
        (Inv d L arity emitted R (step arity L s)) (SourceFormulaStep.timeBound L v) := hs
    have hb := FlagBranchRun.yes_hoareTime d.formulaPending.castSucc (SourceFormulaStep.machine d) (emitBitsTM [])
      before input emitted (step arity L s).before (step arity L s).input emitted
      (Extra d L arity R s) (Extra d L arity R (step arity L s)) (SourceFormulaStep.timeBound L v) hyes
    exact hb.consequence (by
      rintro inp work out h
      refine ⟨h, ?_⟩
      have hv := h.2.2.1.read_eq
      simpa only [s, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] using hv)
      (fun _ _ _ h => h) (by rw [SourceFormulaStep.timeBound_eq]; omega)

theorem hoareTime (d : Layout n) (L arity P : ℕ) (ha : arity.bits.length ≤ L)
    (emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop) (s : State)
    (hlen : s.input.length ≤ L) (hcount : s.pending ≤ P) (hR : Stable d R) :
    (machine d).HoareTime (Inv d L arity emitted R s) (Inv d L arity emitted R (step arity L s))
      (34 * L ^ 2 + 93 * L + 2 * P + 62) := by
  cases s with
  | mk before input count valid =>
    cases valid with
    | false =>
      let s : State := ⟨before, input, count, false⟩
      have hb := FlagBranchRun.no_hoareTime (NaturalScanBuffer.flag n) (pendingMachine d) (emitBitsTM [])
        before input emitted before input emitted (Extra d L arity R s) (Extra d L arity R s)
        0 (noop_hoareTime d L arity emitted R s)
      exact hb.consequence (fun _ _ _ h => ⟨h, h.2.2.2⟩) (fun _ _ _ h => h) (by omega)
    | true =>
      let s : State := ⟨before, input, count, true⟩
      have hpending := pending_hoareTime d L arity P count hcount ha before input emitted hlen R hR
      have hb := FlagBranchRun.yes_hoareTime (NaturalScanBuffer.flag n) (pendingMachine d) (emitBitsTM [])
        before input emitted (step arity L s).before (step arity L s).input emitted
        (Extra d L arity R s) (Extra d L arity R (step arity L s))
        (34 * L ^ 2 + 93 * L + 2 * P + 61) hpending
      exact hb.consequence (fun _ _ _ h => ⟨h, h.2.2.2⟩) (fun _ _ _ h => h) (by omega)

end JointThermoComplexity.Complexity.SourceFormulaLoopBody

#print axioms JointThermoComplexity.Complexity.SourceFormulaLoopBody.pending_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceFormulaLoopBody.hoareTime
