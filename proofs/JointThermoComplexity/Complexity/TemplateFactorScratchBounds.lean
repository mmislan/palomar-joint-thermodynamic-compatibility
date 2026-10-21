module
public import proofs.JointThermoComplexity.Complexity.TemplateFactorPipeline
public import proofs.JointThermoComplexity.Complexity.BinaryBufferReset

set_option autoImplicit false
@[expose] public section

/-! Bit-length bounds for resetting the template factor scratch buffer. The
bound depends on source bit length and a static template constant. -/

namespace JointThermoComplexity.Complexity.TemplateFactorScratchBounds

theorem product_bits (k v : ℕ) : (k * v).bits.length ≤ v.bits.length + k := by
  rw [← BinaryScaleCanonical.multiply_bits]
  exact BinaryScaleCanonical.length_multiply k v.bits

theorem valueAfter_bits (right : Bool) (k v : ℕ) :
    (RationalFactorEmission.valueAfter right (k * v)).bits.length ≤ v.bits.length + k + 1 := by
  have hp := product_bits k v
  cases right
  · have hi := BinaryIncrementControl.length_increment (k * v).bits
    rw [BinaryIncrementControl.increment_bits] at hi
    change (k * v + 1).bits.length ≤ v.bits.length + k + 1
    omega
  · change (k * v).bits.length ≤ v.bits.length + k + 1
    omega

end JointThermoComplexity.Complexity.TemplateFactorScratchBounds

#print axioms JointThermoComplexity.Complexity.TemplateFactorScratchBounds.product_bits
#print axioms JointThermoComplexity.Complexity.TemplateFactorScratchBounds.valueAfter_bits
