module
public import proofs.JointThermoComplexity.Complexity.ChemicalPromiseProblem
public import proofs.JointThermoComplexity.Complexity.NetworkFormulaFP

set_option autoImplicit false
@[expose] public section

/-! The total supplied-motif feasibility language separates the chemical YES
and NO sets. This requires no algorithm for deciding the PAC promise. -/

namespace JointThermoComplexity.Complexity.ChemicalPromiseMembership
open ChemicalPromiseProblem

theorem member (boxed : Bool) : (problem boxed).Member := by
  refine ⟨NetworkCodec.TotalFeasibility, NetworkFormulaFP.totalFeasibility_mem_ExistsR, ?_, ?_⟩
  · rintro input ⟨Q, hQ, _hd, hf⟩
    exact ⟨Q, hQ, hf⟩
  · apply Set.disjoint_left.mpr
    rintro input ⟨Q, hQ, hf⟩ ⟨R, hR, _hd, hn⟩
    have he : Q = R := Option.some.inj (hQ.symm.trans hR)
    subst R
    exact hn hf

end JointThermoComplexity.Complexity.ChemicalPromiseMembership

#print axioms JointThermoComplexity.Complexity.ChemicalPromiseMembership.member
