module
public import proofs.JointThermoComplexity.Complexity.BooleanBufferAt
public import proofs.JointThermoComplexity.Complexity.BinaryBufferReset

set_option autoImplicit false
@[expose] public section

/-! Replace reusable bounded binary contents with an actual fixed-count Boolean input vector. -/

namespace JointThermoComplexity.Complexity.BooleanBufferLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (e : Fin (w + 1) ≃ Fin (w + 1)) (r : Fin w) : TM (w + 1) :=
  seqTM (BinaryBufferReset.machine (CountSumAt.destination e)) (BooleanBufferAt.machine e r)

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (r : Fin w)
    (old bits before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → R work → R work') :
    (machine e r).HoareTime
      (fun inp work out => Cursor before (bits ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work (CountSumAt.destination e)).HasBinaryContent old ∧ (work (CountSumAt.destination e)).cells 0 = Γ.start ∧
        (work (CountSumAt.destination e)).head ≤ old.length + 1 ∧
        IsReg bits.length (work (BooleanBufferAt.fuel e r)) ∧ R work)
      (fun inp work out => Cursor (before ++ bits) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work (CountSumAt.destination e)).HasBinaryPrefix bits ∧ (work (CountSumAt.destination e)).cells 0 = Γ.start ∧
        IsReg bits.length (work (BooleanBufferAt.fuel e r)) ∧ R work)
      (3 * old.length + 4 * bits.length + 12) := by
  let P : (Fin (w + 1) → Tape) → Prop := fun work => IsReg bits.length (work (BooleanBufferAt.fuel e r)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hf, hr⟩
    exact ⟨by simpa only [hw _ (BooleanBufferAt.fuel_ne_destination e r)] using hf, hR work work' hw hr⟩
  have hc := BinaryBufferReset.hoareTime (CountSumAt.destination e) old before (bits ++ tail) emitted P hP
  have hb := BooleanBufferAt.hoareTime e r bits before tail emitted R hR
  have hs := SafeExecution.hoareTime (BooleanBufferAt.machine e r) _ _ (4 * bits.length + 2) hb (by
    rintro inp work out ⟨hcur, _, _, _, _⟩ j
    exact (hcur.works j).2)
  have hseq := seqTM_hoareTime (BinaryBufferReset.machine (CountSumAt.destination e)) (BooleanBufferAt.machine e r) hc (by
    rintro inp work out ⟨hcur, hsafe, hz, hf, hr⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨⟨hcur, CountTape.empty_prefix_of_zero hz, hz.cell0, hf, hr⟩, hsafe⟩) hs
  exact hseq.consequence (fun _ _ _ hp => hp) (by
    rintro inp work out ⟨⟨hcur, hp, hz, hf, hr⟩, hsafe⟩
    exact ⟨hcur, hsafe, hp, hz, hf, hr⟩) (by omega)

end JointThermoComplexity.Complexity.BooleanBufferLoad

#print axioms JointThermoComplexity.Complexity.BooleanBufferLoad.hoareTime
