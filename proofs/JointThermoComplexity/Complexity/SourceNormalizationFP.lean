module
public import proofs.JointThermoComplexity.Complexity.SourceNormalizationMachine
public import proofs.JointThermoComplexity.Complexity.RealComplexity
public import proofs.Complexitylib.Asymptotics

set_option autoImplicit false
@[expose] public section

/-! Unconditional binary-TM polynomial time for the actual total source normalization map. -/

namespace JointThermoComplexity.Complexity.SourceNormalizationFP
open Polynomial

def code (input : List Bool) : List Bool := (SourceNormalization.normalize input).code

noncomputable def runtimePolynomial : Polynomial ℕ := 34 * X ^ 3 + 97 * X ^ 2 + 87 * X + 54

theorem polynomial_eval (L : ℕ) : runtimePolynomial.eval L = SourceNormalizationMachine.timeBound L := by
  simp [runtimePolynomial, SourceNormalizationMachine.timeBound]

theorem code_mem_FP : code ∈ _root_.Complexity.FP := by
  refine ⟨runtimePolynomial.natDegree, 11, SourceNormalizationMachine.machine, SourceNormalizationMachine.timeBound,
    SourceNormalizationMachine.computesInTime, ?_⟩
  exact _root_.Complexity.BigO.of_polynomial_bound runtimePolynomial (fun L => (polynomial_eval L).symm.le)

theorem preserves_ETR (input : List Bool) : code input ∈ RealSyntax.ETR ↔ input ∈ RealSyntax.ETR := by
  change (SourceNormalization.normalize input).code ∈ RealSyntax.ETR ↔ _
  rw [RealSyntax.code_mem_ETR_iff, SourceNormalization.normalize_satisfiable_iff]

theorem output_valid (input : List Bool) :
    RealSyntax.decodeSentence (code input) = some (SourceNormalization.normalize input) := RealSyntax.decodeSentence_code _

end JointThermoComplexity.Complexity.SourceNormalizationFP

#print axioms JointThermoComplexity.Complexity.SourceNormalizationFP.code_mem_FP
#print axioms JointThermoComplexity.Complexity.SourceNormalizationFP.preserves_ETR
