module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxEmitter
public import proofs.JointThermoComplexity.Complexity.ReductionComposition

set_option autoImplicit false
@[expose] public section

/-! Polynomial time for the total small-literal source normalization, via actual binary Turing machines. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxFP
open Polynomial

noncomputable def runtimePolynomial : Polynomial ℕ := 16 * X ^ 2 + 59 * X + 21

theorem polynomial_eval (L : ℕ) : runtimePolynomial.eval L = SmallSyntaxEmitter.timeBound L := by
  simp [runtimePolynomial, SmallSyntaxEmitter.timeBound]

theorem raw_code_mem_FP : SmallSyntaxControl.code ∈ _root_.Complexity.FP := by
  refine ⟨runtimePolynomial.natDegree, 6, SmallSyntaxEmitter.machine, SmallSyntaxEmitter.timeBound,
    SmallSyntaxEmitter.computesInTime, ?_⟩
  exact _root_.Complexity.BigO.of_polynomial_bound runtimePolynomial (fun L => (polynomial_eval L).symm.le)

def code (input : List Bool) : List Bool := (SourceSmallLiterals.normalizeSmall input).code

theorem code_mem_FP : code ∈ _root_.Complexity.FP := by
  have h := _root_.Complexity.mem_FP_comp SourceNormalizationFP.code_mem_FP raw_code_mem_FP
  have heq : SmallSyntaxControl.code ∘ SourceNormalizationFP.code = code := by
    funext input
    exact SmallSyntaxCorrect.normalized_code input
  rw [heq] at h
  exact h

theorem preserves_ETR (input : List Bool) : code input ∈ RealSyntax.ETR ↔ input ∈ RealSyntax.ETR := by
  change (SourceSmallLiterals.normalizeSmall input).code ∈ RealSyntax.ETR ↔ _
  rw [RealSyntax.code_mem_ETR_iff, SourceSmallLiterals.normalizeSmall_satisfiable]

theorem output_valid (input : List Bool) :
    RealSyntax.decodeSentence (code input) = some (SourceSmallLiterals.normalizeSmall input) :=
  RealSyntax.decodeSentence_code _

theorem output_height (input : List Bool) :
    (SourceSmallLiterals.normalizeSmall input).formula.literalHeight ≤ 2 :=
  SourceSmallLiterals.normalizeSmall_height input

theorem output_length (input : List Bool) : (code input).length ≤ 11 * (input.length + 4) :=
  SourceSmallLiterals.normalizeSmall_code_length input

end JointThermoComplexity.Complexity.SmallSyntaxFP

#print axioms JointThermoComplexity.Complexity.SmallSyntaxFP.raw_code_mem_FP
#print axioms JointThermoComplexity.Complexity.SmallSyntaxFP.code_mem_FP
#print axioms JointThermoComplexity.Complexity.SmallSyntaxFP.preserves_ETR
