module
public import proofs.JointThermoComplexity.Complexity.BoxContinuation
public import proofs.JointThermoComplexity.Complexity.ActivitySuffix

set_option autoImplicit false
@[expose] public section

/-! The exact remaining sentence suffix after activity positivity and the complete rational-box block. -/

namespace JointThermoComplexity.Complexity.BoxSuffix
open RealSyntax NetworkFormula NetworkMembership

def formula (Q : NetworkCodec.Input) : Formula (arity Q.network) :=
  allFin (fun a => .conj
    (allFin (fun i => if i ∈ (Q.network.motifs a).reactions then
      directionFormula (Q.network.forward i) (currentIndex Q.network i) else .truth))
    (allFin (fun s => if s ∈ (Q.network.motifs a).species then
      .lt (.int 0) (productionTerm Q.network a s (currentIndex Q.network)) else .truth)))

theorem activity_suffix_code (Q : NetworkCodec.Input) :
    (ActivitySuffix.formula Q).code = BoxContinuation.word Q ++ (formula Q).code := rfl

end JointThermoComplexity.Complexity.BoxSuffix

#print axioms JointThermoComplexity.Complexity.BoxSuffix.activity_suffix_code
