module
public import proofs.JointThermoComplexity.Complexity.ActivityStep
public import proofs.JointThermoComplexity.Complexity.CurrentDenseCode

set_option autoImplicit false
@[expose] public section

/-! Exact right-nested activity-positivity formula and its clause-word serialization. -/

namespace JointThermoComplexity.Complexity.ActivityCode
open RealSyntax CurrentTraversal

def formula {n arity : ℕ} (indices : Fin n → Fin arity) : Formula arity :=
  NetworkFormula.allFin (fun i => .lt (.int 0) (.var (indices i)))

def clauses {n arity : ℕ} (indices : Fin n → Fin arity) : List (List Bool) :=
  List.ofFn (fun i => ActivityStep.word (indices i))

theorem clauses_length {n arity : ℕ} (indices : Fin n → Fin arity) : (clauses indices).length = n := by
  simp only [clauses, List.length_ofFn]

theorem clause_at {n arity : ℕ} (indices : Fin n → Fin arity) (i : Fin n) :
    (clauses indices)[i.val]'(by rw [clauses_length]; exact i.isLt) = ActivityStep.word (indices i) := by
  simp only [clauses, List.getElem_ofFn]

theorem output_eq {n arity : ℕ} (indices : Fin n → Fin arity) :
    output (clauses indices) ++ [false, false, false] = (formula indices).code := by
  have ht := CurrentDenseCode.conjoin_code (List.ofFn (fun i : Fin n => (Formula.lt (.int 0) (.var (indices i)))))
  simpa only [formula, NetworkFormula.allFin, clauses, ActivityStep.word, List.map_ofFn, Function.comp_def] using ht.symm

end JointThermoComplexity.Complexity.ActivityCode

#print axioms JointThermoComplexity.Complexity.ActivityCode.output_eq
