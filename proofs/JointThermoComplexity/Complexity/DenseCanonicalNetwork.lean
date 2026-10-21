module
public import proofs.JointThermoComplexity.Complexity.DenseCanonicalSuffix
public import proofs.JointThermoComplexity.Complexity.DenseNetworkFP

set_option autoImplicit false
@[expose] public section

/-! The actual total binary-Turing emitter agrees with the original complete
chemical network code on every canonical degree-four source. -/

namespace JointThermoComplexity.Complexity.DenseCanonicalNetwork
open RationalLiteralNetwork RationalBranchData

def tail {e N : ℕ} (boxed : Bool) (L R : Data (Fin e) N) : List Bool :=
  FiniteCodec.functionCode (DataCodec.motif (speciesCount e N N) (reactionCount N N)) (network boxed L R).motifs ++
    FiniteCodec.functionCode FiniteCodec.boolean (network boxed L R).forward ++
    FiniteCodec.functionCode (FiniteCodec.optional DataCodec.box) (network boxed L R).boxes

theorem input_parts {e N : ℕ} (boxed : Bool) (L R : Data (Fin e) N) :
    (input boxed L R).code =
      (RealSyntax.binderCode (speciesCount e N N) ++ RealSyntax.binderCode (reactionCount N N) ++ RealSyntax.binderCode 2 ++
        FiniteCodec.functionCode (DataCodec.reaction (speciesCount e N N)) (network boxed L R).reactions) ++ tail boxed L R := by
  let header := RealSyntax.binderCode (speciesCount e N N) ++ RealSyntax.binderCode (reactionCount N N) ++ RealSyntax.binderCode 2
  let rc := FiniteCodec.functionCode (DataCodec.reaction (speciesCount e N N)) (network boxed L R).reactions
  let mc := FiniteCodec.functionCode (DataCodec.motif (speciesCount e N N) (reactionCount N N)) (network boxed L R).motifs
  let fc := FiniteCodec.functionCode FiniteCodec.boolean (network boxed L R).forward
  let bc := FiniteCodec.functionCode (FiniteCodec.optional DataCodec.box) (network boxed L R).boxes
  change header ++ ((rc ++ mc) ++ (fc ++ bc)) = (header ++ rc) ++ ((mc ++ fc) ++ bc)
  simp only [List.append_assoc]

theorem suffix_of_external (boxed : Bool) (n e N : ℕ) (he : e = DenseDimensionProgram.external boxed n)
    (L R : Data (Fin e) N) : DenseNetworkSuffix.word boxed n N = tail boxed L R := by
  subst e
  exact DenseCanonicalSuffix.tail_code boxed n N L R

theorem input_with_suffix (boxed : Bool) (n e N : ℕ) (he : e = DenseDimensionProgram.external boxed n)
    (L R : Data (Fin e) N) :
    (input boxed L R).code =
      (RealSyntax.binderCode (speciesCount e N N) ++ RealSyntax.binderCode (reactionCount N N) ++ RealSyntax.binderCode 2 ++
        FiniteCodec.functionCode (DataCodec.reaction (speciesCount e N N)) (network boxed L R).reactions) ++
      DenseNetworkSuffix.word boxed n N := by
  rw [input_parts, suffix_of_external boxed n e N he L R]

theorem twoPass_code (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (hp : SparseInteger.DegreeLE 4 p.payload) :
    DenseTwoPass.word boxed (SparsePolynomialCodec.code p) =
      SparseDimensionWords.header boxed p.arity (FinitePositiveCoordinates.data boxed p).payload.length ++
      FiniteCodec.functionCode (DataCodec.reaction (speciesCount
        (RationalPolynomialNetwork.externalCount boxed (FinitePositiveCoordinates.data boxed p))
        (FinitePositiveCoordinates.data boxed p).payload.length (FinitePositiveCoordinates.data boxed p).payload.length))
        (RationalPolynomialNetwork.network boxed (FinitePositiveCoordinates.data boxed p)).reactions := by
  simp only [DenseTwoPass.word, DenseTwoPass.leftWord]
  rw [DenseCanonicalBranch.branch_code boxed false p hp, DenseCanonicalBranch.branch_code boxed true p hp,
    DenseCanonicalControl.arity_code, DenseCanonicalControl.total_code boxed p hp,
    List.append_assoc, ← DenseCanonicalBranch.reactions_code]

theorem word_code (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (hp : SparseInteger.DegreeLE 4 p.payload) :
    DenseNetworkEmitter.word boxed (SparsePolynomialCodec.code p) =
      RationalPolynomialNetwork.code boxed (FinitePositiveCoordinates.data boxed p) := by
  unfold DenseNetworkEmitter.word
  rw [twoPass_code boxed p hp, DenseCanonicalControl.arity_code,
    DenseCanonicalControl.total_code boxed p hp, DenseCanonicalControl.header_code]
  exact (input_with_suffix boxed p.arity
    (RationalPolynomialNetwork.externalCount boxed (FinitePositiveCoordinates.data boxed p))
    (FinitePositiveCoordinates.data boxed p).payload.length (DenseCanonicalControl.external_count boxed p)
    (RationalPolynomialNetwork.left boxed (FinitePositiveCoordinates.data boxed p))
    (RationalPolynomialNetwork.right boxed (FinitePositiveCoordinates.data boxed p))).symm

theorem word_mem_FP (boxed : Bool) : DenseNetworkEmitter.word boxed ∈ _root_.Complexity.FP :=
  DenseNetworkFP.word_mem_FP boxed

end JointThermoComplexity.Complexity.DenseCanonicalNetwork

#print axioms JointThermoComplexity.Complexity.DenseCanonicalNetwork.word_code
#print axioms JointThermoComplexity.Complexity.DenseCanonicalNetwork.word_mem_FP
