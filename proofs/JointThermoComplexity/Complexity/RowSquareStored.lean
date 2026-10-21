module
public import proofs.JointThermoComplexity.Complexity.RowSquareWords

set_option autoImplicit false
@[expose] public section

/-! Canonical stored-row pieces are exactly the encoded homogeneous terms.
Only the selected term's raw monomial is inspected; unused slot data is irrelevant.
-/

namespace JointThermoComplexity.Complexity.RowSquareStored
open EquationRowControl RowSquareControl RowSquareWords

def sourcePiece (scale : ℕ) (a : ℤ × List ℕ) : Option WordTerm :=
  if a.2.length ≤ 2 then some (BitCodec.integerCode a.1,
    a.2.map (fun v => BitCodec.naturalCode (2 * v)) ++
      List.replicate (2 - a.2.length) (BitCodec.naturalCode (2 * scale))) else none

def sourcePieces (scale : ℕ) (row : List (ℤ × List ℕ)) : List WordTerm :=
  row.flatMap (fun a => (sourcePiece scale a).toList)

theorem stored_piece (s : State) (i : Fin 3) (old : Term) (a : ℤ × List ℕ) (scale : ℕ)
    (hs : s.terms i = stored old a) (hp : present s (requirements i) = true) :
    piece s scale.bits i = sourcePiece scale a := by
  simp only [piece, hp, ↓reduceIte, hs]
  rcases a with ⟨z, _ | ⟨u, _ | ⟨v, _ | ⟨q, rest⟩⟩⟩⟩ <;>
    simp [sourcePiece, stored, MonomialPrefixControl.expected, degree, coordinates, template,
      WordPolynomialProgram.refCode, WordPolynomialProgram.instruction, WordCodeProgram.code,
      values_word, values_scale, hs, BinaryCoordinateReplay.natural_code]

theorem visited (s : State) (row : List (ℤ × List ℕ)) (suffix : List Bool) (hr : row.length ≤ 3)
    (i : Fin 3) (a : ℤ × List ℕ) (hi : row[i.val]? = some a) :
    (expected s row suffix).terms i = stored (s.terms i) a ∧ present (expected s row suffix) (requirements i) = true := by
  rcases row with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, rest⟩⟩⟩
  · fin_cases i <;> simp at hi
  · fin_cases i <;> simp_all [expected, slots, present, requirements, stored]
  · fin_cases i <;> simp_all [expected, slots, present, requirements, stored]
  · have he : rest = [] := by simp only [List.length_cons] at hr; exact List.length_eq_zero_iff.mp (by omega)
    subst rest
    fin_cases i <;> simp_all [expected, slots, present, requirements, stored]

theorem unvisited (s : State) (row : List (ℤ × List ℕ)) (suffix : List Bool) (hr : row.length ≤ 3)
    (i : Fin 3) (hi : row[i.val]? = none) : present (expected s row suffix) (requirements i) = false := by
  rcases row with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, rest⟩⟩⟩
  · fin_cases i <;> simp [expected, slots, present, requirements]
  · fin_cases i <;> simp_all [expected, slots, present, requirements, stored]
  · fin_cases i <;> simp_all [expected, slots, present, requirements, stored]
  · have he : rest = [] := by simp only [List.length_cons] at hr; exact List.length_eq_zero_iff.mp (by omega)
    subst rest
    fin_cases i <;> simp_all

theorem piece_expected (s : State) (row : List (ℤ × List ℕ)) (suffix : List Bool) (hr : row.length ≤ 3)
    (scale : ℕ) (i : Fin 3) :
    piece (expected s row suffix) scale.bits i = row[i.val]?.bind (sourcePiece scale) := by
  cases hi : row[i.val]? with
  | none => simp only [piece, unvisited s row suffix hr i hi, Bool.false_eq_true, ↓reduceIte, Option.bind_none]
  | some a =>
    obtain ⟨hs, hp⟩ := visited s row suffix hr i a hi
    exact stored_piece (expected s row suffix) i (s.terms i) a scale hs hp

theorem pieces_expected (s : State) (row : List (ℤ × List ℕ)) (suffix : List Bool) (hr : row.length ≤ 3) (scale : ℕ) :
    pieces (expected s row suffix) scale.bits = sourcePieces scale row := by
  unfold pieces fromSlots
  simp_rw [piece_expected s row suffix hr scale]
  have hf : List.finRange 3 = [0, 1, 2] := by decide
  rw [hf]
  rcases row with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, rest⟩⟩⟩
  · simp [sourcePieces]
  · simp [sourcePieces]
  · simp [sourcePieces]
  · have he : rest = [] := by simp only [List.length_cons] at hr; exact List.length_eq_zero_iff.mp (by omega)
    subst rest
    simp [sourcePieces]

end JointThermoComplexity.Complexity.RowSquareStored

#print axioms JointThermoComplexity.Complexity.RowSquareStored.stored_piece
#print axioms JointThermoComplexity.Complexity.RowSquareStored.pieces_expected
