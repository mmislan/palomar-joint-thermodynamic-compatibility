module
public import proofs.JointThermoComplexity.Complexity.ProductionReactionStep
public import proofs.JointThermoComplexity.Complexity.CurrentTraversal

set_option autoImplicit false
@[expose] public section

/-! Ordered add/selected-term words followed by integer zero are exactly the existing right-associated production sum code. -/

namespace JointThermoComplexity.Complexity.ProductionDenseCode
open RealSyntax CurrentTraversal

variable {arity : ℕ}

theorem addTerms_code (terms : List (Term arity)) :
    (NetworkFormula.addTerms terms).code =
      output (terms.map (fun t => ProductionReactionStep.addTag ++ t.code)) ++ ProductionSelectedTerm.zeroCode := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
    change [false, true, false] ++ t.code ++ (NetworkFormula.addTerms terms).code = _
    rw [ih]
    simp only [output, List.map_cons, List.flatMap_cons, id_eq, ProductionReactionStep.addTag, List.append_assoc]

def term (Q : NetworkCodec.Input) (s : Fin Q.speciesCount) (mask : Fin Q.reactionCount → Bool) :
    Term (NetworkMembership.arity Q.network) :=
  NetworkFormula.sumFin (fun i => ProductionSelectedTerm.term (mask i) Q i s)

def clauses (Q : NetworkCodec.Input) (s : Fin Q.speciesCount) (mask : Fin Q.reactionCount → Bool) : List (List Bool) :=
  List.ofFn (fun i => ProductionReactionStep.word Q i s (mask i))

theorem clauses_length (Q : NetworkCodec.Input) (s : Fin Q.speciesCount) (mask : Fin Q.reactionCount → Bool) :
    (clauses Q s mask).length = Q.reactionCount := by simp only [clauses, List.length_ofFn]

theorem clause_at (Q : NetworkCodec.Input) (s : Fin Q.speciesCount) (mask : Fin Q.reactionCount → Bool) (i : Fin Q.reactionCount) :
    (clauses Q s mask)[i.val]'(by rw [clauses_length]; exact i.isLt) =
      ProductionReactionStep.word Q i s (List.ofFn mask)[i.val] := by
  simp only [clauses, List.getElem_ofFn]

theorem output_eq (Q : NetworkCodec.Input) (s : Fin Q.speciesCount) (mask : Fin Q.reactionCount → Bool) :
    output (clauses Q s mask) ++ ProductionSelectedTerm.zeroCode = (term Q s mask).code := by
  have ht := addTerms_code (List.ofFn (fun i : Fin Q.reactionCount => ProductionSelectedTerm.term (mask i) Q i s))
  simpa only [term, NetworkFormula.sumFin, clauses, ProductionReactionStep.word, List.map_ofFn, Function.comp_def] using ht.symm

theorem term_eq_production (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (s : Fin Q.speciesCount) :
    term Q s (fun i => decide (i ∈ (Q.network.motifs a).reactions)) =
      NetworkFormula.productionTerm Q.network a s (NetworkMembership.currentIndex Q.network) := by
  simp [term, ProductionSelectedTerm.term, ProductionTermOutput.term, NetworkFormula.productionTerm]

end JointThermoComplexity.Complexity.ProductionDenseCode

#print axioms JointThermoComplexity.Complexity.ProductionDenseCode.addTerms_code
#print axioms JointThermoComplexity.Complexity.ProductionDenseCode.output_eq
#print axioms JointThermoComplexity.Complexity.ProductionDenseCode.term_eq_production
