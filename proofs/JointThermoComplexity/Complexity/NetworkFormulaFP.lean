module
public import proofs.JointThermoComplexity.Complexity.NetworkFormulaEmitter
public import proofs.JointThermoComplexity.Complexity.RealComplexity
public import proofs.Complexitylib.Asymptotics

set_option autoImplicit false
@[expose] public section

/-! Unconditional binary-TM polynomial time for the actual total formula map and existential-real membership of total supplied-motif feasibility. -/

namespace JointThermoComplexity.Complexity.NetworkFormulaFP
open Polynomial

def code (input : List Bool) : List Bool := (NetworkCodec.toSentence input).code

noncomputable def runtimePolynomial : Polynomial ℕ :=
  4 * X ^ 6 + 436 * X ^ 5 + 1288 * X ^ 4 + 1998 * X ^ 3 + 1976 * X ^ 2 + 1252 * X + 326

theorem polynomial_eval (L : ℕ) : runtimePolynomial.eval L = NetworkFormulaEmitter.timeBound L := by
  rw [NetworkFormulaEmitter.timeBound_eq]
  simp [runtimePolynomial]

theorem code_mem_FP : code ∈ _root_.Complexity.FP := by
  refine ⟨runtimePolynomial.natDegree, 22, NetworkFormulaEmitter.machine 0, NetworkFormulaEmitter.timeBound,
    NetworkFormulaEmitter.computesInTime 0, ?_⟩
  exact _root_.Complexity.BigO.of_polynomial_bound runtimePolynomial (fun L => (polynomial_eval L).symm.le)

theorem totalFeasibility_mem_ExistsR : RealComplexity.ExistsR NetworkCodec.TotalFeasibility :=
  ⟨code, code_mem_FP, NetworkCodec.toSentence_correct⟩

end JointThermoComplexity.Complexity.NetworkFormulaFP

#print axioms JointThermoComplexity.Complexity.NetworkFormulaFP.polynomial_eval
#print axioms JointThermoComplexity.Complexity.NetworkFormulaFP.code_mem_FP
#print axioms JointThermoComplexity.Complexity.NetworkFormulaFP.totalFeasibility_mem_ExistsR
