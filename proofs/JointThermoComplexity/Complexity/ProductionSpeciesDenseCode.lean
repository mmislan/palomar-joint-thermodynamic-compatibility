module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesStep
public import proofs.JointThermoComplexity.Complexity.CurrentDenseCode

set_option autoImplicit false
@[expose] public section

/-! Ordered species-step words and final truth are exactly the existing production allFin formula. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesDenseCode
open RealSyntax CurrentTraversal

def formula (Q : NetworkCodec.Input) (a : Fin Q.coreCount) : Formula (NetworkMembership.arity Q.network) :=
  NetworkFormula.allFin (ProductionSpeciesClause.formula Q a)

def clauses (Q : NetworkCodec.Input) (a : Fin Q.coreCount) : List (List Bool) :=
  List.ofFn (fun s => ProductionSpeciesStep.word Q a s)

theorem clauses_length (Q : NetworkCodec.Input) (a : Fin Q.coreCount) :
    (clauses Q a).length = Q.speciesCount := by simp only [clauses, List.length_ofFn]

theorem clause_at (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (s : Fin Q.speciesCount) :
    (clauses Q a)[s.val]'(by rw [clauses_length]; exact s.isLt) = ProductionSpeciesStep.word Q a s := by
  simp only [clauses, List.getElem_ofFn]

theorem output_eq (Q : NetworkCodec.Input) (a : Fin Q.coreCount) :
    output (clauses Q a) ++ [false, false, false] = (formula Q a).code := by
  have ht := CurrentDenseCode.conjoin_code (List.ofFn (ProductionSpeciesClause.formula Q a))
  simpa only [formula, NetworkFormula.allFin, clauses, ProductionSpeciesStep.word, List.map_ofFn, Function.comp_def] using ht.symm

theorem formula_eq (Q : NetworkCodec.Input) (a : Fin Q.coreCount) :
    formula Q a = NetworkFormula.allFin (fun s => if s ∈ (Q.network.motifs a).species then
      .lt (.int 0) (NetworkFormula.productionTerm Q.network a s (NetworkMembership.currentIndex Q.network)) else .truth) := rfl

end JointThermoComplexity.Complexity.ProductionSpeciesDenseCode

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesDenseCode.output_eq
#print axioms JointThermoComplexity.Complexity.ProductionSpeciesDenseCode.formula_eq
