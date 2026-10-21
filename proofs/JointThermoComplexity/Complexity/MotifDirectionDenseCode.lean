module
public import proofs.JointThermoComplexity.Complexity.MotifDirectionClause
public import proofs.JointThermoComplexity.Complexity.CurrentDenseCode

set_option autoImplicit false
@[expose] public section

/-! Exact dense mask/flag clauses and canonical right-nested direction allFin serialization. -/

namespace JointThermoComplexity.Complexity.MotifDirectionDenseCode
open RealSyntax CurrentTraversal

variable {n arity : ℕ}

def formula (mask flags : Fin n → Bool) (indices : Fin n → Fin arity) : Formula arity :=
  NetworkFormula.allFin (fun i => if mask i then NetworkFormula.directionFormula (flags i) (indices i) else .truth)

def clauses (mask flags : Fin n → Bool) (indices : Fin n → Fin arity) : List (List Bool) :=
  List.ofFn (fun i => MotifDirectionClause.word (mask i) (flags i) (indices i))

theorem clauses_length (mask flags : Fin n → Bool) (indices : Fin n → Fin arity) :
    (clauses mask flags indices).length = n := by simp only [clauses, List.length_ofFn]

theorem clause_at (mask flags : Fin n → Bool) (indices : Fin n → Fin arity) (i : Fin n) :
    (clauses mask flags indices)[i.val]'(by rw [clauses_length]; exact i.isLt) =
      MotifDirectionClause.word (List.ofFn mask)[i.val] (List.ofFn flags)[i.val] (indices i) := by
  simp only [clauses, List.getElem_ofFn]

theorem output_eq (mask flags : Fin n → Bool) (indices : Fin n → Fin arity) :
    output (clauses mask flags indices) ++ [false, false, false] = (formula mask flags indices).code := by
  have ht := CurrentDenseCode.conjoin_code
    (List.ofFn (fun i : Fin n => if mask i then NetworkFormula.directionFormula (flags i) (indices i) else .truth))
  simpa only [formula, NetworkFormula.allFin, clauses, MotifDirectionClause.word, MaskedDirectionOutput.word,
    List.map_ofFn, Function.comp_def] using ht.symm

end JointThermoComplexity.Complexity.MotifDirectionDenseCode

#print axioms JointThermoComplexity.Complexity.MotifDirectionDenseCode.output_eq
