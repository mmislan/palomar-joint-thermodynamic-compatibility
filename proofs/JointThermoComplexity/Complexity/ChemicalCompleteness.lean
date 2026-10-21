module
public import proofs.JointThermoComplexity.Complexity.DenseCanonicalNetwork
public import proofs.JointThermoComplexity.Complexity.StrictSourceHardness
public import proofs.JointThermoComplexity.Complexity.RationalPolynomialPromise
public import proofs.JointThermoComplexity.Complexity.ChemicalPromiseMembership

set_option autoImplicit false
@[expose] public section

/-! Unconditional existential-real completeness for exactly two supplied valid
PACs, with globally shared activities, fixed positive rational factors at most
two, prescribed boxed intervals and side molecularity six/eight. Both source
verdicts satisfy the same chemical promise. Costs use actual binary Turing FP. -/

namespace JointThermoComplexity.Complexity.ChemicalCompleteness
open RealComplexity

theorem emitter_yes (boxed : Bool) (input : List Bool)
    (hi : input ∈ (StrictPositivityProblem.problem boxed).yes) :
    DenseNetworkEmitter.word boxed input ∈ (ChemicalPromiseProblem.problem boxed).yes := by
  obtain ⟨p, hd, hp, hpos⟩ := hi
  rw [SparsePolynomialCodec.decode_sound hd, DenseCanonicalNetwork.word_code boxed p hp.2.1]
  exact (RationalPolynomialPromise.yes_iff boxed p hp).mpr hpos

theorem emitter_no (boxed : Bool) (input : List Bool)
    (hi : input ∈ (StrictPositivityProblem.problem boxed).no) :
    DenseNetworkEmitter.word boxed input ∈ (ChemicalPromiseProblem.problem boxed).no := by
  obtain ⟨p, hd, hp, hneg⟩ := hi
  rw [SparsePolynomialCodec.decode_sound hd, DenseCanonicalNetwork.word_code boxed p hp.2.1]
  exact (RationalPolynomialPromise.no_iff boxed p hp).mpr hneg

def reduction (boxed : Bool) : List Bool → List Bool :=
  DenseNetworkEmitter.word boxed ∘ StrictSourceHardness.map boxed

theorem reduction_mem_FP (boxed : Bool) : reduction boxed ∈ _root_.Complexity.FP :=
  _root_.Complexity.mem_FP_comp (StrictSourceHardness.map_mem_FP boxed) (DenseCanonicalNetwork.word_mem_FP boxed)

theorem yes_of_source (boxed : Bool) (input : List Bool) (hi : input ∈ RealSyntax.ETR) :
    reduction boxed input ∈ (ChemicalPromiseProblem.problem boxed).yes :=
  emitter_yes boxed _ (StrictSourceHardness.yes_of_source boxed input hi)

theorem no_of_source (boxed : Bool) (input : List Bool) (hi : input ∉ RealSyntax.ETR) :
    reduction boxed input ∈ (ChemicalPromiseProblem.problem boxed).no :=
  emitter_no boxed _ (StrictSourceHardness.no_of_source boxed input hi)

theorem etr_reduction (boxed : Bool) :
    PolyReducesToPromise RealSyntax.ETR (ChemicalPromiseProblem.problem boxed) :=
  ⟨reduction boxed, reduction_mem_FP boxed, yes_of_source boxed, no_of_source boxed⟩

theorem lands_in_promise (boxed : Bool) (input : List Bool) :
    reduction boxed input ∈ (ChemicalPromiseProblem.problem boxed).yes ∪
      (ChemicalPromiseProblem.problem boxed).no := by
  classical
  by_cases hi : input ∈ RealSyntax.ETR
  · exact Or.inl (yes_of_source boxed input hi)
  · exact Or.inr (no_of_source boxed input hi)

theorem output_domain (boxed : Bool) (input : List Bool) :
    ∃ Q, NetworkCodec.decode (reduction boxed input) = some Q ∧ ChemicalPromiseProblem.Domain boxed Q := by
  rcases lands_in_promise boxed input with h | h
  · obtain ⟨Q, hQ, hD, _⟩ := h
    exact ⟨Q, hQ, hD⟩
  · obtain ⟨Q, hQ, hD, _⟩ := h
    exact ⟨Q, hQ, hD⟩

theorem yes_iff (boxed : Bool) (input : List Bool) :
    reduction boxed input ∈ (ChemicalPromiseProblem.problem boxed).yes ↔ input ∈ RealSyntax.ETR := by
  classical
  constructor
  · intro hy
    by_contra hn
    exact Set.disjoint_left.mp (ChemicalPromiseProblem.problem boxed).disjoint hy (no_of_source boxed input hn)
  · exact yes_of_source boxed input

theorem no_iff (boxed : Bool) (input : List Bool) :
    reduction boxed input ∈ (ChemicalPromiseProblem.problem boxed).no ↔ input ∉ RealSyntax.ETR := by
  constructor
  · intro hn hi
    exact Set.disjoint_left.mp (ChemicalPromiseProblem.problem boxed).disjoint (yes_of_source boxed input hi) hn
  · exact no_of_source boxed input

theorem complete (boxed : Bool) : (ChemicalPromiseProblem.problem boxed).Complete :=
  ⟨ChemicalPromiseMembership.member boxed, hard_of_ETR_reduction (etr_reduction boxed)⟩

theorem boxed_complete : (ChemicalPromiseProblem.problem true).Complete := complete true
theorem unboxed_complete : (ChemicalPromiseProblem.problem false).Complete := complete false

end JointThermoComplexity.Complexity.ChemicalCompleteness

#print axioms JointThermoComplexity.Complexity.ChemicalCompleteness.reduction_mem_FP
#print axioms JointThermoComplexity.Complexity.ChemicalCompleteness.output_domain
#print axioms JointThermoComplexity.Complexity.ChemicalCompleteness.etr_reduction
#print axioms JointThermoComplexity.Complexity.ChemicalCompleteness.boxed_complete
#print axioms JointThermoComplexity.Complexity.ChemicalCompleteness.unboxed_complete
