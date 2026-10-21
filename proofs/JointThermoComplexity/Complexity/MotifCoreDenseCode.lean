module
public import proofs.JointThermoComplexity.Complexity.MotifCoreStep
public import proofs.JointThermoComplexity.Complexity.CurrentDenseCode

set_option autoImplicit false
@[expose] public section

/-! Ordered complete-core words followed by truth are exactly the existing motif allFin block. -/

namespace JointThermoComplexity.Complexity.MotifCoreDenseCode
open RealSyntax CurrentTraversal

def formula (Q : NetworkCodec.Input) : Formula (NetworkMembership.arity Q.network) :=
  NetworkFormula.allFin (MotifCompleteBody.formula Q)

def clauses (Q : NetworkCodec.Input) : List (List Bool) := List.ofFn (fun a => MotifCoreStep.word Q a)

theorem clauses_length (Q : NetworkCodec.Input) : (clauses Q).length = Q.coreCount := by simp only [clauses, List.length_ofFn]

theorem clause_at (Q : NetworkCodec.Input) (a : Fin Q.coreCount) :
    (clauses Q)[a.val]'(by rw [clauses_length]; exact a.isLt) = MotifCoreStep.word Q a := by
  simp only [clauses, List.getElem_ofFn]

theorem output_eq (Q : NetworkCodec.Input) :
    output (clauses Q) ++ [false, false, false] = (formula Q).code := by
  have ht := CurrentDenseCode.conjoin_code (List.ofFn (MotifCompleteBody.formula Q))
  simpa only [formula, NetworkFormula.allFin, clauses, MotifCoreStep.word, List.map_ofFn, Function.comp_def] using ht.symm

end JointThermoComplexity.Complexity.MotifCoreDenseCode

#print axioms JointThermoComplexity.Complexity.MotifCoreDenseCode.output_eq
