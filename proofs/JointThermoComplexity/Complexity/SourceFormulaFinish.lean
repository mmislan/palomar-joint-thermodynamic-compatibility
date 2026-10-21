module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaLoop

set_option autoImplicit false
@[expose] public section

/-! Final formula status is the retained verdict conjoined with pending-count exhaustion. -/

namespace JointThermoComplexity.Complexity.SourceFormulaFinish
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters
open SourceTermLoopState (State)
open SourceFormulaLoopBody (Extra)
variable {n : ℕ}

def finishState (s : State) : State := {s with valid := s.valid && decide (s.pending = 0)}

def machine (d : Layout n) : TM (n + 2) :=
  FlagBranch.machine d.formulaPending.castSucc (SourceTermToken.setStatus (NaturalScanBuffer.flag n) false) (emitBitsTM [])

theorem hoareTime (d : Layout n) (L arity : ℕ) (emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (s : State) (hR : Stable d R) :
    (machine d).HoareTime (Inv d L arity emitted R s) (Inv d L arity emitted R (finishState s)) 2 := by
  cases s with
  | mk before input count valid =>
    cases count with
    | zero =>
      let s : State := ⟨before, input, 0, valid⟩
      have hb := FlagBranchNonone.hoareTime d.formulaPending.castSucc (SourceTermToken.setStatus (NaturalScanBuffer.flag n) false)
        (emitBitsTM []) before input emitted before input emitted (Extra d L arity R s) (Extra d L arity R s)
        0 (SourceFormulaLoopBody.noop_hoareTime d L arity emitted R s)
      exact hb.consequence (by
        intro inp work out h
        refine ⟨h, ?_⟩
        have hv := h.2.2.1.read_eq
        change (work d.formulaPending.castSucc).read = Γ.blank at hv
        rw [hv]
        decide) (by
          rintro inp work out ⟨hc, hr, hp, hf⟩
          exact ⟨hc, hr, hp, by simpa only [s, finishState, decide_true, Bool.and_true] using hf⟩) le_rfl
    | succ v =>
      let s : State := ⟨before, input, v + 1, valid⟩
      have hy := SourceFormulaCounter.status_hoareTime d L arity (v + 1) valid false before input emitted R hR
      have hb := FlagBranchRun.yes_hoareTime d.formulaPending.castSucc (SourceTermToken.setStatus (NaturalScanBuffer.flag n) false)
        (emitBitsTM []) before input emitted before input emitted
        (Extra d L arity R s) (Extra d L arity R {s with valid := false}) 1 hy
      exact hb.consequence (by
        intro inp work out h
        refine ⟨h, ?_⟩
        have hv := h.2.2.1.read_eq
        simpa only [s, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] using hv) (by
          rintro inp work out ⟨hc, hr, hp, hf⟩
          exact ⟨hc, hr, hp, by
            simpa only [s, finishState, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, decide_false, Bool.and_false] using hf⟩) le_rfl

end JointThermoComplexity.Complexity.SourceFormulaFinish

#print axioms JointThermoComplexity.Complexity.SourceFormulaFinish.hoareTime
