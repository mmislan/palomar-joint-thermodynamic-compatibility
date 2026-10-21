module
public import proofs.JointThermoComplexity.Complexity.SourceTermLoop

set_option autoImplicit false
@[expose] public section

/-! The actual final status is valid AND pending=0, including zero-fuel inputs. -/

namespace JointThermoComplexity.Complexity.SourceTermFinish
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceIndexField SourceTermLoopState
open SourceTermLoopBody (Inv Extra)
variable {n : ℕ}

def finishState (s : State) : State := {s with valid := s.valid && decide (s.pending = 0)}

def machine (pending : Fin (n + 1)) : TM (n + 2) :=
  FlagBranch.machine pending.castSucc (SourceTermToken.setStatus (NaturalScanBuffer.flag n) false) (emitBitsTM [])

theorem clear_hoareTime (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1))
    (hs : SourceTermTagRead.Separate ports left right)
    (sep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n))
    (hp : SourcePendingFrame.Separate ports pending left right) (L arity : ℕ) (emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (s : State)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ i, j ≠ ports i) → j ≠ pending → work' j = work j) → R work → R work') :
    (SourceTermToken.setStatus (NaturalScanBuffer.flag n) false).HoareTime
      (Inv ports pending left right L arity emitted R s)
      (Inv ports pending left right L arity emitted R {s with valid := false}) 1 := by
  let RT : (Fin (n + 1) → Tape) → Prop := fun work => IsReg s.pending (work pending) ∧
    (∀ i, (work (ports i)).head = 1) ∧ R work
  have hRT : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n → work' j = work j) →
      RT work → RT work' := by
    rintro work work' hw ⟨hv, hh, hr⟩
    exact ⟨by simpa only [hw pending hp.left hp.right hp.flag] using hv,
      fun i => by simpa only [hw (ports i) (hs.left i) (hs.right i) (hs.flag i)] using hh i,
      hR _ _ (fun j hl hr hf _ _ => hw j hl hr hf) hr⟩
  have h := SourceTermFields.constant_hoareTime false L left right sep arity s.before s.input emitted RT hRT
  exact h.consequence (by
    rintro inp work out ⟨hc, hr, hv, hh, _hf⟩
    exact ⟨hc, ⟨hr.safe, hr.markers, hr.encoded, hr.candidate, hr.arityBits, hr.arityZero, hr.flagHead, hv, hh, hr.frame⟩⟩) (by
    rintro inp work out ⟨hc, hr, hf⟩
    exact ⟨hc, ⟨hr.safe, hr.markers, hr.encoded, hr.candidate, hr.arityBits, hr.arityZero, hr.flagHead, hr.frame.2.2⟩,
      hr.frame.1, hr.frame.2.1, hf⟩) le_rfl

theorem hoareTime (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1))
    (hs : SourceTermTagRead.Separate ports left right)
    (sep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n))
    (hp : SourcePendingFrame.Separate ports pending left right) (L arity : ℕ) (emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (s : State)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ i, j ≠ ports i) → j ≠ pending → work' j = work j) → R work → R work') :
    (machine pending).HoareTime (Inv ports pending left right L arity emitted R s)
      (Inv ports pending left right L arity emitted R (finishState s)) 2 := by
  cases s with
  | mk before input count valid =>
    cases count with
    | zero =>
      let s : State := ⟨before, input, 0, valid⟩
      have hb := FlagBranchNonone.hoareTime pending.castSucc (SourceTermToken.setStatus (NaturalScanBuffer.flag n) false)
        (emitBitsTM []) before input emitted before input emitted
        (Extra ports pending left right L arity R s) (Extra ports pending left right L arity R s) 0
        (SourceTermLoopBody.noop_hoareTime ports pending left right L arity emitted R s)
      exact hb.consequence (by
        intro inp work out h
        refine ⟨h, ?_⟩
        have hv := h.2.2.1.read_eq
        change (work pending.castSucc).read = Γ.blank at hv
        rw [hv]
        decide) (by
          rintro inp work out ⟨hc, hr, hp, hh, hf⟩
          exact ⟨hc, hr, hp, hh, by simpa only [s, finishState, decide_true, Bool.and_true] using hf⟩) le_rfl
    | succ v =>
      let s : State := ⟨before, input, v + 1, valid⟩
      have hy := clear_hoareTime ports pending left right hs sep hp L arity emitted R s hR
      have hb := FlagBranchRun.yes_hoareTime pending.castSucc (SourceTermToken.setStatus (NaturalScanBuffer.flag n) false)
        (emitBitsTM []) before input emitted before input emitted
        (Extra ports pending left right L arity R s) (Extra ports pending left right L arity R {s with valid := false}) 1 hy
      exact hb.consequence (by
        intro inp work out h
        refine ⟨h, ?_⟩
        have hv := h.2.2.1.read_eq
        simpa only [s, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] using hv) (by
          rintro inp work out ⟨hc, hr, hp, hh, hf⟩
          exact ⟨hc, hr, hp, hh, by
            simpa only [s, finishState, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, decide_false, Bool.and_false] using hf⟩) le_rfl

end JointThermoComplexity.Complexity.SourceTermFinish

#print axioms JointThermoComplexity.Complexity.SourceTermFinish.hoareTime
