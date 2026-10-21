module
public import proofs.JointThermoComplexity.Complexity.BinaryScratchRestore

set_option autoImplicit false
@[expose] public section

/-! A reusable binary accumulator update. Sum into scratch, clear the old
accumulator, restore the sum there and clear scratch for the next update. -/

namespace JointThermoComplexity.Complexity.BinaryAccumulator
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork cast_ne_last)
variable {w : ℕ}

def machine (acc source : Fin w) : TM (w + 1) :=
  seqTM (seqTM (BinaryAddBuffer.machine acc source) (BinaryBufferReset.machine acc.castSucc))
    (BinaryScratchRestore.machine acc)

theorem hoareTime (acc source : Fin w) (hne : acc ≠ source) (m n : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ acc → next j = work j) → R work → R next) :
    (machine acc source).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register m (work acc.castSucc) ∧ Register n (work source.castSucc) ∧
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register (m + n) (work acc.castSucc) ∧ Register n (work source.castSucc) ∧
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (13 * m.bits.length + 10 * n.bits.length + 57) := by
  have hcast : acc.castSucc ≠ source.castSucc := by
    intro he
    apply hne
    apply Fin.ext
    exact congrArg (fun x : Fin (w + 1) => x.val) he
  let S : (Fin (w + 1) → Tape) → Prop := fun work =>
    Register (m + n) (work (Fin.last w)) ∧ Register n (work source.castSucc) ∧ R (oldWork work)
  have hS : ∀ work next, (∀ j, j ≠ acc.castSucc → next j = work j) → S work → S next := by
    rintro work next he ⟨hv, hn, hx⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [he (Fin.last w) (cast_ne_last acc).symm]; exact hv
    · rw [he source.castSucc hcast.symm]; exact hn
    · apply hR (oldWork work) (oldWork next) _ hx
      intro j hj
      apply he j.castSucc
      intro hej
      apply hj
      apply Fin.ext
      exact congrArg (fun x : Fin (w + 1) => x.val) hej
  let T : (Fin w → Tape) → Prop := fun work => Register n (work source) ∧ R work
  have hT : ∀ work next, (∀ j, j ≠ acc → next j = work j) → T work → T next := by
    rintro work next he ⟨hn, hx⟩
    exact ⟨by rw [he source hne.symm]; exact hn, hR work next he hx⟩
  have ha := BinaryAddBuffer.natural_hoareTime acc source hne m n before input emitted R
  have hc := BinaryBufferReset.hoareTime acc.castSucc m.bits before input emitted S hS
  have hr := BinaryScratchRestore.hoareTime acc (m + n) before input emitted T hT
  have hac := seqTM_hoareTime _ _ ha (by
    rintro inp work out ⟨hc, hs, hm, hn, hv, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hm.1.2, hm.2, by rw [hm.1.1]; omega, hv, hn, hx⟩) hc
  have hf := seqTM_hoareTime _ _ hac (by
    rintro inp work out ⟨hc, hs, hz, hv, hn, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, CountTape.empty_prefix_of_zero hz, hz.cell0, hv, hn, hx⟩) hr
  apply hf.consequence (fun _ _ _ hp => hp)
  · rintro inp work out ⟨hc, hs, hv, hb, hz, hn, hx⟩
    exact ⟨hc, hs, hv, hn, hb, hz, hx⟩
  · have hbits := BinaryAddBuffer.sum_bits_length m n
    omega

end JointThermoComplexity.Complexity.BinaryAccumulator

#print axioms JointThermoComplexity.Complexity.BinaryAccumulator.machine
#print axioms JointThermoComplexity.Complexity.BinaryAccumulator.hoareTime
