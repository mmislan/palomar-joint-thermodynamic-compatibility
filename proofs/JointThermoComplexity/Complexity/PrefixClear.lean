module
public import proofs.JointThermoComplexity.Complexity.BinaryPrefixRewind
public import proofs.JointThermoComplexity.Complexity.BinaryClear
public import proofs.JointThermoComplexity.Complexity.SafeExecution
public import proofs.JointThermoComplexity.Complexity.CountTape

set_option autoImplicit false
@[expose] public section

/-! Clear the parser's completed copied-prefix tape and return a canonical empty register. -/

namespace JointThermoComplexity.Complexity.PrefixClear
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun

variable {w : ℕ}

def machine (idx : Fin w) : TM w := seqTM (rewindWorkTM idx) (clearWorkTM idx)

theorem hoareTime (idx : Fin w) (bits : List Bool) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work idx) ∧ R work) (3 * bits.length + 9) := by
  have hr := BinaryPrefixRewind.hoareTime idx bits before input emitted R hR
  have hc := BinaryClear.hoareTime idx bits before input emitted R hR
  have hsafe := SafeExecution.hoareTime (clearWorkTM idx) _ _ _ hc (by
    rintro inp work out ⟨hcur, _, _⟩ j
    exact (hcur.works j).2)
  have hseq := seqTM_hoareTime (rewindWorkTM idx) (clearWorkTM idx) hr (by
    rintro inp work out ⟨hcur, hs, hp, hz, hR⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨⟨hcur, hp, hz, hR⟩, hs⟩) hsafe
  exact hseq.consequence (fun _ _ _ h => h)
    (fun _ _ _ ⟨⟨hcur, hreg, hR⟩, hs⟩ => ⟨hcur, hs,
      CountTape.register_of_string (by simpa only [List.replicate_zero, Nat.zero_bits] using hreg.1) hreg.2, hR⟩) (by omega)

end JointThermoComplexity.Complexity.PrefixClear

#print axioms JointThermoComplexity.Complexity.PrefixClear.hoareTime
