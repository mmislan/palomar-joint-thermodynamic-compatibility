module
public import proofs.JointThermoComplexity.Complexity.EquationSystemCodec

set_option autoImplicit false
@[expose] public section

/-! Encoded length bounds the declared arity, row count and every valid coordinate. -/

namespace JointThermoComplexity.Complexity.EquationCodeBounds
open FiniteCodec EquationSystemCodec

theorem list_length_lower {α : Type} (A : Codec α) (xs : List α) :
    xs.length + 1 ≤ (SparseListCodec.listCode A xs).length := by
  induction xs with
  | nil => simp [SparseListCodec.listCode]
  | cons a xs ih =>
    simp only [SparseListCodec.listCode, List.length_cons, List.length_append]
    omega

theorem framing (p : Data) : p.arity + p.rows.length + 2 ≤ (code p).length := by
  have h := list_length_lower (SparsePolynomialCodec.polynomial p.arity) p.rows
  change p.rows.length + 1 ≤ ((rowsCodec p.arity).code p.rows).length at h
  rw [code, List.length_append, SparseListCodec.unaryCode_length]
  omega

theorem arity_le_length (p : Data) : p.arity ≤ (code p).length := by have := framing p; omega

theorem rows_le_length (p : Data) : p.rows.length ≤ (code p).length := by have := framing p; omega

theorem length_pos (p : Data) : 0 < (code p).length := by have := framing p; omega

theorem coordinate_lt_length (p : Data) (v : Fin p.arity) : v.val < (code p).length :=
  v.isLt.trans_le (arity_le_length p)

theorem decoded_framing {input : List Bool} {p : Data} (h : decode input = some p) :
    p.arity + p.rows.length + 2 ≤ input.length := by
  rw [decode_sound h]
  exact framing p

end JointThermoComplexity.Complexity.EquationCodeBounds

#print axioms JointThermoComplexity.Complexity.EquationCodeBounds.framing
#print axioms JointThermoComplexity.Complexity.EquationCodeBounds.coordinate_lt_length
#print axioms JointThermoComplexity.Complexity.EquationCodeBounds.decoded_framing
