module
public import proofs.JointThermoComplexity.Complexity.BinaryTape

set_option autoImplicit false
@[expose] public section

/-! Erase exactly the last raw binary cell without changing lower digits or the blank tail. -/

namespace JointThermoComplexity.Complexity.BinaryEraseLast
open _root_.Complexity

theorem content {t : Tape} (xs : List Bool) (b : Bool) (hc : t.HasBinaryContent (xs ++ [b]))
    (hh : t.head = xs.length + 1) : (t.write Γ.blank).HasBinaryContent xs := by
  have hn : t.head ≠ 0 := by omega
  refine ⟨?_, ?_⟩
  · intro i hi
    have hne : i + 1 ≠ t.head := by omega
    simp only [Tape.write, hn, ↓reduceIte, Function.update_of_ne hne]
    rw [hc.1 i (by simp only [List.length_append, List.length_singleton]; omega)]
    simp only [List.getElem_append_left hi]
  · intro i hi
    by_cases he : i = xs.length
    · subst i
      simp [Tape.write, hh]
    · have hne : i + 1 ≠ t.head := by omega
      simp only [Tape.write, hn, ↓reduceIte, Function.update_of_ne hne]
      exact hc.2 i (by simp only [List.length_append, List.length_singleton]; omega)

end JointThermoComplexity.Complexity.BinaryEraseLast

#print axioms JointThermoComplexity.Complexity.BinaryEraseLast.content
