module
public import proofs.JointThermoComplexity.Complexity.BitCodec
public import proofs.Complexitylib.Models.TuringMachine.Tape.Encoding

set_option autoImplicit false
@[expose] public section

/-! Local in-place binary edits with exact initialized contents. -/

namespace JointThermoComplexity.Complexity.BinaryTape
open _root_.Complexity

theorem content_of_cells {t : Tape} {bits : List Bool}
    (h : t.cells = (Tape.init (bits.map Γ.ofBool)).cells) : t.HasBinaryContent bits := by
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [h]
    exact Tape.init_ofBool_cells_lt bits i hi
  · intro i hi
    rw [h]
    exact Tape.init_ofBool_cells_ge bits i hi

theorem cells_of_content {t : Tape} {bits : List Bool} (h : t.HasBinaryContent bits)
    (hz : t.cells 0 = Γ.start) : t.cells = (Tape.init (bits.map Γ.ofBool)).cells := by
  have hp : ({head := bits.length + 1, cells := t.cells} : Tape).HasBinaryPrefix bits := ⟨rfl, h⟩
  exact hp.cells_eq_init hz

theorem read_cons {t : Tape} (before rest : List Bool) (bit : Bool)
    (hc : t.HasBinaryContent (before ++ bit :: rest)) (hh : t.head = before.length + 1) : t.read = Γ.ofBool bit := by
  rw [Tape.read, hh, hc.1 before.length (by simp)]
  simp

theorem read_end {t : Tape} (before : List Bool) (hc : t.HasBinaryContent before)
    (hh : t.head = before.length + 1) : t.read = Γ.blank := by
  rw [Tape.read, hh]
  exact hc.2 before.length le_rfl

theorem overwrite {t : Tape} (before rest : List Bool) (old bit : Bool)
    (hc : t.HasBinaryContent (before ++ old :: rest)) (hh : t.head = before.length + 1) :
    (t.write (Γ.ofBool bit)).HasBinaryContent (before ++ bit :: rest) := by
  have h := hc.write_set bit hh (by simp)
  simpa only [List.set_append_right _ _ le_rfl, Nat.sub_self, List.set_cons_zero] using h

theorem append {t : Tape} (before : List Bool) (bit : Bool)
    (hc : t.HasBinaryContent before) (hh : t.head = before.length + 1) :
    (t.write (Γ.ofBool bit)).HasBinaryContent (before ++ [bit]) := hc.write_append bit hh

end JointThermoComplexity.Complexity.BinaryTape

#print axioms JointThermoComplexity.Complexity.BinaryTape.overwrite
#print axioms JointThermoComplexity.Complexity.BinaryTape.cells_of_content
