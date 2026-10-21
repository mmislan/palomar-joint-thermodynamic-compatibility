module
public import proofs.JointThermoComplexity.Complexity.BoxRecordTraversal
public import proofs.JointThermoComplexity.Complexity.CurrentDenseCode

set_option autoImplicit false
@[expose] public section

/-! Dense optional-box records and exact right-nested allFin box-clause serialization. -/

namespace JointThermoComplexity.Complexity.BoxDenseCode
open RealSyntax NetworkData CurrentTraversal

def formula {n arity : ℕ} (boxes : Fin n → Option ClosedBox) (indices : Fin n → Fin arity) : Formula arity :=
  NetworkFormula.allFin (fun i => NetworkFormula.boxFormula (boxes i) (indices i))

def clauses {n arity : ℕ} (boxes : Fin n → Option ClosedBox) (indices : Fin n → Fin arity) : List (List Bool) :=
  List.ofFn (fun i => BoxStep.word (boxes i) (indices i))

theorem clauses_length {n arity : ℕ} (boxes : Fin n → Option ClosedBox) (indices : Fin n → Fin arity) :
    (clauses boxes indices).length = n := by simp only [clauses, List.length_ofFn]

theorem clause_at {n arity : ℕ} (boxes : Fin n → Option ClosedBox) (indices : Fin n → Fin arity) (i : Fin n) :
    (clauses boxes indices)[i.val]'(by rw [clauses_length]; exact i.isLt) =
      BoxStep.word (List.ofFn boxes)[i.val] (indices i) := by
  simp only [clauses, List.getElem_ofFn]

theorem finiteFunction_code {n : ℕ} (boxes : Fin n → Option ClosedBox) :
    (FiniteCodec.finiteFunction (FiniteCodec.optional DataCodec.box) n).code boxes =
      BoxRecordTraversal.code (List.ofFn boxes) :=
  FiniteCodec.functionCode_eq_flatMap (FiniteCodec.optional DataCodec.box) boxes

theorem output_eq {n arity : ℕ} (boxes : Fin n → Option ClosedBox) (indices : Fin n → Fin arity) :
    output (clauses boxes indices) ++ [false, false, false] = (formula boxes indices).code := by
  have ht := CurrentDenseCode.conjoin_code (List.ofFn (fun i : Fin n => NetworkFormula.boxFormula (boxes i) (indices i)))
  simpa only [formula, NetworkFormula.allFin, clauses, BoxStep.word, List.map_ofFn, Function.comp_def] using ht.symm

end JointThermoComplexity.Complexity.BoxDenseCode

#print axioms JointThermoComplexity.Complexity.BoxDenseCode.output_eq
