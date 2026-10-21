module
public import proofs.JointThermoComplexity.Complexity.ActivityContinuation

set_option autoImplicit false
@[expose] public section

/-! Identify the exact constraint suffix after the leading activity-positivity block. -/

namespace JointThermoComplexity.Complexity.ActivitySuffix
open RealSyntax NetworkFormula NetworkMembership

def formula (Q : NetworkCodec.Input) : Formula (arity Q.network) :=
  .conj (allFin (fun s => boxFormula (Q.network.boxes s) (activityIndex Q.network s)))
    (allFin (fun a => .conj
      (allFin (fun i => if i ∈ (Q.network.motifs a).reactions then
        directionFormula (Q.network.forward i) (currentIndex Q.network i) else .truth))
      (allFin (fun s => if s ∈ (Q.network.motifs a).species then
        .lt (.int 0) (productionTerm Q.network a s (currentIndex Q.network)) else .truth))))

theorem constraints_code (Q : NetworkCodec.Input) :
    (constraintsFormula Q.network (activityIndex Q.network) (currentIndex Q.network)).code =
      ActivityContinuation.word Q ++ (formula Q).code := rfl

end JointThermoComplexity.Complexity.ActivitySuffix

#print axioms JointThermoComplexity.Complexity.ActivitySuffix.constraints_code
