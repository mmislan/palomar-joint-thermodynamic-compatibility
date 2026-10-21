module
public import proofs.JointThermoComplexity.Complexity.FixedWordsSkip
public import proofs.JointThermoComplexity.Complexity.NetworkTallyData
public import proofs.JointThermoComplexity.Complexity.MaskCodecBridge

set_option autoImplicit false
@[expose] public section

/-! The exact canonical motif, direction and optional-box slices after the reaction table. -/

namespace JointThermoComplexity.Complexity.BoxTraversalData
open FiniteCodec

def motifs (Q : NetworkCodec.Input) : List (List Bool) :=
  List.ofFn (fun i => (DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs i))

def forward (Q : NetworkCodec.Input) : List Bool :=
  (finiteFunction boolean Q.reactionCount).code Q.network.forward

def boxes (Q : NetworkCodec.Input) : List Bool :=
  (finiteFunction (optional DataCodec.box) Q.speciesCount).code Q.network.boxes

theorem motif_length {n r : ℕ} (a : NetworkData.Motif n r) :
    ((DataCodec.motif n r).code a).length = n + r := by
  change ((DataCodec.finset n).code a.species ++ (DataCodec.finset r).code a.reactions).length = n + r
  rw [List.length_append, MaskCodecBridge.finset_code_length, MaskCodecBridge.finset_code_length]

theorem motifs_width (Q : NetworkCodec.Input) :
    ∀ bits ∈ motifs Q, bits.length = Q.speciesCount + Q.reactionCount := by
  intro bits hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  exact motif_length (Q.network.motifs i)

theorem motifs_count (Q : NetworkCodec.Input) : (motifs Q).length = Q.coreCount := by
  simp only [motifs, List.length_ofFn]

theorem motifs_code (Q : NetworkCodec.Input) :
    (finiteFunction (DataCodec.motif Q.speciesCount Q.reactionCount) Q.coreCount).code Q.network.motifs =
      FixedWordsSkip.code (motifs Q) := by
  change functionCode (DataCodec.motif Q.speciesCount Q.reactionCount) Q.network.motifs = _
  rw [functionCode_eq_flatMap]
  change (List.ofFn Q.network.motifs).flatMap (DataCodec.motif Q.speciesCount Q.reactionCount).code =
    (List.ofFn ((DataCodec.motif Q.speciesCount Q.reactionCount).code ∘ Q.network.motifs)).flatMap id
  rw [← List.map_ofFn, List.flatMap_map]
  rfl

theorem forward_length (Q : NetworkCodec.Input) : (forward Q).length = Q.reactionCount :=
  BooleanVector.code_length Q.network.forward

theorem tail_split (Q : NetworkCodec.Input) :
    NetworkTallyData.tail Q = FixedWordsSkip.code (motifs Q) ++ (forward Q ++ boxes Q) := by
  unfold NetworkTallyData.tail
  rw [motifs_code]
  simp only [forward, boxes, List.append_assoc]

end JointThermoComplexity.Complexity.BoxTraversalData

#print axioms JointThermoComplexity.Complexity.BoxTraversalData.tail_split
