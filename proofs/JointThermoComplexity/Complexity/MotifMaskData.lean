module
public import proofs.JointThermoComplexity.Complexity.BoxTraversalData

set_option autoImplicit false
@[expose] public section

/-! Exact supplied mask and shared orientation vectors, including their indexed bit meanings. -/

namespace JointThermoComplexity.Complexity.MotifMaskData
open NetworkData FiniteCodec

variable {n r c : ℕ}

def species (a : Motif n r) : List Bool := (DataCodec.finset n).code a.species
def reactions (a : Motif n r) : List Bool := (DataCodec.finset r).code a.reactions

theorem boolean_code {v : ℕ} (f : Fin v → Bool) : functionCode boolean f = List.ofFn f := by
  rw [functionCode_eq_flatMap]
  change (List.ofFn f).flatMap (fun bit => [bit]) = List.ofFn f
  simp

theorem species_eq (a : Motif n r) : species a = List.ofFn (fun i => decide (i ∈ a.species)) :=
  boolean_code _

theorem reactions_eq (a : Motif n r) : reactions a = List.ofFn (fun i => decide (i ∈ a.reactions)) :=
  boolean_code _

theorem species_length (a : Motif n r) : (species a).length = n := MaskCodecBridge.finset_code_length a.species

theorem reactions_length (a : Motif n r) : (reactions a).length = r := MaskCodecBridge.finset_code_length a.reactions

theorem motif_code (a : Motif n r) : (DataCodec.motif n r).code a = species a ++ reactions a := rfl

theorem species_at (a : Motif n r) (i : Fin n) :
    (species a)[i.val]'(by rw [species_length]; exact i.isLt) = decide (i ∈ a.species) := by
  simp [species_eq]

theorem reactions_at (a : Motif n r) (i : Fin r) :
    (reactions a)[i.val]'(by rw [reactions_length]; exact i.isLt) = decide (i ∈ a.reactions) := by
  simp [reactions_eq]

theorem forward_eq (Q : NetworkCodec.Input) : BoxTraversalData.forward Q = List.ofFn Q.network.forward :=
  boolean_code _

end JointThermoComplexity.Complexity.MotifMaskData

#print axioms JointThermoComplexity.Complexity.MotifMaskData.motif_code
#print axioms JointThermoComplexity.Complexity.MotifMaskData.species_at
#print axioms JointThermoComplexity.Complexity.MotifMaskData.reactions_at
#print axioms JointThermoComplexity.Complexity.MotifMaskData.forward_eq
