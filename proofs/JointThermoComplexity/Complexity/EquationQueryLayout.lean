module
public import proofs.JointThermoComplexity.Complexity.FormulaSpanLoop

set_option autoImplicit false
@[expose] public section

/-! Main traversal uses ports0..7, subtree queries8..15, other scratch begins at16. -/

namespace JointThermoComplexity.Complexity.EquationQueryLayout

def main (i : Fin 8) : Fin 32 := ⟨i.val, by omega⟩
def query (i : Fin 8) : Fin 32 := ⟨i.val + 8, by omega⟩

def exchange (j : Fin 32) : Fin 32 :=
  ⟨if j.val < 8 then j.val + 8 else if j.val < 16 then j.val - 8 else j.val,
    by split <;> first | omega | (split <;> omega)⟩

theorem exchange_involution : Function.Involutive exchange := by unfold Function.Involutive; decide

def permutation : Fin 32 ≃ Fin 32 where
  toFun := exchange
  invFun := exchange
  left_inv := exchange_involution
  right_inv := exchange_involution

theorem main_to_query : ∀ i, permutation (main i) = query i := by decide
theorem query_to_main : ∀ i, permutation (query i) = main i := by decide
theorem high_fixed : ∀ j : Fin 32, 16 ≤ j.val → permutation j = j := by decide

theorem main_term_outside : ∀ i, TermSpanRegisters.Outside 25 (permutation.symm (main i)) ∧
    permutation.symm (main i) ≠ TermSpanRegisters.fuel 25 := by unfold TermSpanRegisters.Outside; decide

theorem main_formula_outside : ∀ i, FormulaSpanRegisters.Outside 24 (permutation.symm (main i)) ∧
    permutation.symm (main i) ≠ FormulaSpanLoop.fuel 24 := by
  unfold FormulaSpanRegisters.Outside TermSpanRegisters.Outside
  decide

theorem high_term_outside : ∀ j : Fin 32, 16 ≤ j.val →
    TermSpanRegisters.Outside 25 (permutation.symm j) ∧
      permutation.symm j ≠ TermSpanRegisters.fuel 25 := by unfold TermSpanRegisters.Outside; decide

theorem high_formula_outside : ∀ j : Fin 32, 16 ≤ j.val →
    FormulaSpanRegisters.Outside 24 (permutation.symm j) ∧
      permutation.symm j ≠ FormulaSpanLoop.fuel 24 := by
  unfold FormulaSpanRegisters.Outside TermSpanRegisters.Outside
  decide

theorem physical_query_ports :
    permutation (TermSpanRegisters.pending 25) = (⟨11, by decide⟩ : Fin 32) ∧
    permutation (TermSpanRegisters.fuel 25) = (⟨12, by decide⟩ : Fin 32) ∧
    permutation (TermSpanRegisters.nodeCounter 25) = (⟨13, by decide⟩ : Fin 32) ∧
    permutation (TermSpanRegisters.flag 25) = (⟨14, by decide⟩ : Fin 32) ∧
    permutation (FormulaSpanRegisters.formulaPending 24) = (⟨15, by decide⟩ : Fin 32) := by decide

end JointThermoComplexity.Complexity.EquationQueryLayout

#print axioms JointThermoComplexity.Complexity.EquationQueryLayout.physical_query_ports
#print axioms JointThermoComplexity.Complexity.EquationQueryLayout.high_formula_outside
