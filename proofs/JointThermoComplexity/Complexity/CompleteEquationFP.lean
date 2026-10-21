module
public import proofs.JointThermoComplexity.Complexity.CompleteEquationMachine

set_option autoImplicit false
@[expose] public section

/-! Polynomial time for the complete total equation serializer, including source normalization. -/

namespace JointThermoComplexity.Complexity.CompleteEquationFP

theorem raw_code_mem_FP : CompleteEquationMachine.code ∈ _root_.Complexity.FP := by
  refine ⟨CompleteEquationMachine.runtimePolynomial.natDegree, 32, CompleteEquationMachine.machine,
    CompleteEquationMachine.timeBound, CompleteEquationMachine.computesInTime, ?_⟩
  exact _root_.Complexity.BigO.of_polynomial_bound CompleteEquationMachine.runtimePolynomial (fun _ => le_rfl)

def code (input : List Bool) : List Bool := CompleteEquationMachine.code (SmallSyntaxFP.code input)

theorem code_mem_FP : code ∈ _root_.Complexity.FP := by
  have h := _root_.Complexity.mem_FP_comp SmallSyntaxFP.code_mem_FP raw_code_mem_FP
  change (CompleteEquationMachine.code ∘ SmallSyntaxFP.code) ∈ _root_.Complexity.FP
  exact h

end JointThermoComplexity.Complexity.CompleteEquationFP

#print axioms JointThermoComplexity.Complexity.CompleteEquationFP.raw_code_mem_FP
#print axioms JointThermoComplexity.Complexity.CompleteEquationFP.code_mem_FP
