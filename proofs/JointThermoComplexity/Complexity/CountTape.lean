module
public import proofs.JointThermoComplexity.Complexity.FixedOutput

set_option autoImplicit false
@[expose] public section

/-! Exact agreement between bounded unary registers and tapes of repeated true bits. -/

namespace JointThermoComplexity.Complexity.CountTape
open _root_.Complexity
open _root_.Complexity.TM

theorem string_of_register {v : ℕ} {t : Tape} (h : IsReg v t) :
    t.HasBinaryString (List.replicate v true) := by
  refine ⟨h.head_eq, ?_, ?_⟩
  · intro i hi
    simp only [List.length_replicate] at hi
    rw [h.cells_one hi]
    simp [Γ.ofBool]
  · intro i hi
    simp only [List.length_replicate] at hi
    exact h.cells_blank (by omega)

theorem register_of_string {v : ℕ} {t : Tape}
    (h : t.HasBinaryString (List.replicate v true)) (hz : t.cells 0 = Γ.start) : IsReg v t := by
  refine ⟨h.1, hz, ?_, ?_⟩
  · intro i hi
    have hb := h.2.1 i (by simpa only [List.length_replicate] using hi)
    simpa only [List.getElem_replicate, Γ.ofBool] using hb
  · intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact h.2.2 i (by simp only [List.length_replicate]; omega)

theorem empty_prefix_of_zero {t : Tape} (h : IsReg 0 t) : t.HasBinaryPrefix [] := by
  have hs := string_of_register h
  simpa only [List.replicate_zero, Tape.HasBinaryString, Tape.HasBinaryPrefix, List.length_nil] using hs

end JointThermoComplexity.Complexity.CountTape

#print axioms JointThermoComplexity.Complexity.CountTape.register_of_string
