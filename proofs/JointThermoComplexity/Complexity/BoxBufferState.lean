module
public import proofs.JointThermoComplexity.Complexity.CountTape

set_option autoImplicit false
@[expose] public section

/-! A reusable binary-buffer invariant covering initial unary addresses and later literal contents. -/

namespace JointThermoComplexity.Complexity.BoxBufferState
open _root_.Complexity
open _root_.Complexity.TM

def Reusable (L : ℕ) (t : Tape) : Prop :=
  ∃ bits : List Bool, bits.length ≤ 4 * L ∧ t.HasBinaryContent bits ∧
    t.cells 0 = Γ.start ∧ t.head ≤ bits.length + 1

def Stored (bits : List Bool) (t : Tape) : Prop := t.HasBinaryPrefix bits ∧ t.cells 0 = Γ.start

theorem of_register {L v : ℕ} {t : Tape} (hv : v ≤ 4 * L) (h : IsReg v t) : Reusable L t := by
  have hs := CountTape.string_of_register h
  exact ⟨List.replicate v true, by simpa only [List.length_replicate] using hv,
    hs.2, h.cell0, by rw [h.head_eq, List.length_replicate]; omega⟩

theorem Stored.reusable {L : ℕ} {bits : List Bool} {t : Tape}
    (h : Stored bits t) (hlen : bits.length ≤ 4 * L) : Reusable L t :=
  ⟨bits, hlen, h.1.2, h.2, h.1.1.le⟩

end JointThermoComplexity.Complexity.BoxBufferState

#print axioms JointThermoComplexity.Complexity.BoxBufferState.of_register
