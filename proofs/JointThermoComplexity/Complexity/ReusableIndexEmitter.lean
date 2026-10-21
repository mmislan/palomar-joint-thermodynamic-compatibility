module
public import proofs.JointThermoComplexity.Complexity.IndexEmitter
public import proofs.JointThermoComplexity.Complexity.BinaryClear

set_option autoImplicit false
@[expose] public section

/-! Canonical bounded-index output with the scratch tape cleared for reuse. -/

namespace JointThermoComplexity.Complexity.ReusableIndexEmitter
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun

variable {w : ℕ}

def machine (fuel scratch : Fin w) : TM w :=
  seqTM (IndexEmitter.machine fuel scratch) (clearWorkTM scratch)

def timeBound (v : ℕ) : ℕ := v * (2 * v + 6) + 6 * v + 14

theorem timeBound_eq (v : ℕ) : timeBound v = 2 * v ^ 2 + 12 * v + 14 := by
  unfold timeBound
  ring1

theorem hoareTime (fuel scratch : Fin w) (hne : fuel ≠ scratch) (v : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ fuel → j ≠ scratch → work' j = work j) → R work → R work') :
    (machine fuel scratch).HoareTime
      (fun inp work out => IsReg v (work fuel) ∧ Cursor before input emitted inp work out ∧
        Register 0 (work scratch) ∧ R work)
      (fun inp work out => IsReg v (work fuel) ∧ Cursor before input (emitted ++ BitCodec.naturalCode v) inp work out ∧
        Register 0 (work scratch) ∧ R work) (timeBound v) := by
  let RP : (Fin w → Tape) → Prop := fun work => IsReg v (work fuel) ∧ R work
  have hRP : ∀ work work', (∀ j, j ≠ scratch → work' j = work j) → RP work → RP work' := by
    rintro work work' hw ⟨hf, hr⟩
    exact ⟨by simpa only [hw fuel hne] using hf, hR work work' (fun j _ hj => hw j hj) hr⟩
  have he := IndexEmitter.hoareTime fuel scratch hne v before input emitted R hR
  have hc := BinaryClear.natural_hoareTime scratch v before input (emitted ++ BitCodec.naturalCode v) RP hRP
  have hseq := seqTM_hoareTime (IndexEmitter.machine fuel scratch) (clearWorkTM scratch) he (by
    rintro inp work out ⟨hf, hcur, hs, hr⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨hcur, hs, hf, hr⟩) hc
  apply HoareTime.mono_bound (b := IndexEmitter.timeBound v + 1 + (2 * v.bits.length + 5))
  · apply HoareTime.strengthen_post hseq
    rintro inp work out ⟨hcur, hs, hf, hr⟩
    exact ⟨hf, hcur, hs, hr⟩
  · have hn := BinaryIncrementControl.bits_length_le v
    unfold IndexEmitter.timeBound timeBound
    omega

end JointThermoComplexity.Complexity.ReusableIndexEmitter

#print axioms JointThermoComplexity.Complexity.ReusableIndexEmitter.hoareTime
