module
public import proofs.JointThermoComplexity.Complexity.HeaderAt
public import proofs.JointThermoComplexity.Complexity.BinaryTape

set_option autoImplicit false
@[expose] public section

/-! Read and advance a prepared input cursor without emitting copied input. -/

namespace JointThermoComplexity.Complexity.InputCursor
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ} {before remaining emitted : List Bool} {inp out : Tape} {work : Fin w → Tape}

theorem read_bit (bit : Bool) (h : Cursor before (bit :: remaining) emitted inp work out) :
    inp.read = Γ.ofBool bit :=
  BinaryTape.read_cons before remaining bit (BinaryTape.content_of_cells h.cells) h.head

theorem consume (bit : Bool) (h : Cursor before (bit :: remaining) emitted inp work out) :
    Cursor (before ++ [bit]) remaining emitted (inp.move .right) work out := by
  refine ⟨?_, ?_, h.works, h.tapePrefix, h.zero⟩
  · simpa only [Tape.move_cells, List.append_assoc, List.singleton_append] using h.cells
  · simp [Tape.move, h.head, List.length_append, Nat.add_assoc]

theorem update_work (h : Cursor before remaining emitted inp work out) (idx : Fin w) (t : Tape)
    (ht : t.read ≠ Γ.start ∧ 1 ≤ t.head) :
    Cursor before remaining emitted inp (Function.update work idx t) out := by
  refine ⟨h.cells, h.head, ?_, h.tapePrefix, h.zero⟩
  intro j
  by_cases hj : j = idx
  · subst j
    simpa only [Function.update_self] using ht
  · simpa only [Function.update_of_ne hj] using h.works j

end JointThermoComplexity.Complexity.InputCursor

#print axioms JointThermoComplexity.Complexity.InputCursor.consume
