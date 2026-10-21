module
public import proofs.JointThermoComplexity.Complexity.GateTallyScan

set_option autoImplicit false
@[expose] public section

/-! Canonical exponent gate tally in actual encoded-prefix time, with a stable frame. -/

namespace JointThermoComplexity.Complexity.GateTally
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (idx : Fin w) : TM w := GateTallyMachine.machine idx

theorem hoareTime (idx : Fin w) (bits : List Bool) (count : ℕ) (before tail emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before (BitCodec.encodeBits bits ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryPrefix (List.replicate count true) ∧
        (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.encodeBits bits) tail emitted inp work out ∧
        (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix (List.replicate (count + ExactGateCount.bitsCost bits) true) ∧
        (work idx).cells 0 = Γ.start ∧ R work) (2 * bits.length + 1) := by
  rintro inp work out ⟨hc, hs, hp, hz, hr⟩
  obtain ⟨e, t, ht, hreach, hhalt, heCur, hePrefix, heZero, heOther⟩ :=
    GateTallyScan.scan bits before tail emitted count idx ⟨some false, inp, work, out⟩ rfl hc hp hz
  have heSafe : ∀ j, Parked (e.work j) := by
    intro j
    by_cases hj : j = idx
    · subst j
      exact ⟨by rw [hePrefix.1]; omega, Tape.cells_ne_start_of_hasBinaryPrefix hePrefix⟩
    · rw [heOther j hj]
      exact hs j
  exact ⟨e, t, ht, hreach, hhalt, heCur, heSafe, hePrefix, heZero, hR work e.work heOther hr⟩

theorem natural_hoareTime (idx : Fin w) (exponent count : ℕ) (before tail emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode exponent ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryPrefix (List.replicate count true) ∧
        (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode exponent) tail emitted inp work out ∧
        (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix (List.replicate (count + ExactGateCount.bitsCost exponent.bits) true) ∧
        (work idx).cells 0 = Γ.start ∧ R work) (BitCodec.naturalCode exponent).length := by
  simpa only [BitCodec.naturalCode, BitCodec.encodeBits_length] using hoareTime idx exponent.bits count before tail emitted R hR

end JointThermoComplexity.Complexity.GateTally

#print axioms JointThermoComplexity.Complexity.GateTally.natural_hoareTime
