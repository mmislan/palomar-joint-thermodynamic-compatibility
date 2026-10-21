module
public import proofs.JointThermoComplexity.Complexity.FiniteEquationEncoding
public import proofs.JointThermoComplexity.Complexity.ReductionComposition

set_option autoImplicit false
@[expose] public section

/-! Unconditional binary polynomial hardness of small quadratic integer equation systems.

The promise is a transparent property of parsed equation data. It includes
positive arity, at most three stored terms and raw coefficient weight at most
five per equation, and quadratic algebraic interpretation. Both source verdicts
land in this domain. No source representation or hardness certificate is part
of the promise. This is an intermediate hard problem, not chemical completeness.
-/

namespace JointThermoComplexity.Complexity.FiniteEquationHardness
open SparseInteger RealSyntax RealComplexity

def Domain (p : EquationSystemCodec.Data) : Prop :=
  0 < p.arity ∧ ∀ q ∈ p.rows, SparseCircuit.RawBound 5 q ∧ (interpret q).totalDegree ≤ 2

def yes : BitLanguage := {input | ∃ p, EquationSystemCodec.decode input = some p ∧
  Domain p ∧ FiniteEquationSemantics.Feasible p.rows}

def no : BitLanguage := {input | ∃ p, EquationSystemCodec.decode input = some p ∧
  Domain p ∧ ¬ FiniteEquationSemantics.Feasible p.rows}

def problem : PromiseProblem where
  yes := yes
  no := no
  disjoint := Set.disjoint_left.mpr (by
    rintro input ⟨p, hp, _, hpf⟩ ⟨q, hq, _, hqf⟩
    have he : p = q := Option.some.inj (hp.symm.trans hq)
    subst q
    exact hqf hpf)

theorem data_domain (input : List Bool) : Domain (FiniteEquationEncoding.data input) :=
  ⟨FiniteEquationEncoding.arity_pos input, fun q hq =>
    ⟨FiniteEquationEncoding.raw_bound input q hq, FiniteEquationEncoding.equation_degree input q hq⟩⟩

theorem yes_of_source (input : List Bool) (hi : input ∈ ETR) : FiniteEquationEncoding.code input ∈ yes :=
  ⟨_, FiniteEquationEncoding.decode input, data_domain input, (FiniteEquationEncoding.feasible_iff input).mp hi⟩

theorem no_of_source (input : List Bool) (hi : input ∉ ETR) : FiniteEquationEncoding.code input ∈ no :=
  ⟨_, FiniteEquationEncoding.decode input, data_domain input,
    fun hf => hi ((FiniteEquationEncoding.feasible_iff input).mpr hf)⟩

theorem etr_reduction : PolyReducesToPromise ETR problem :=
  ⟨FiniteEquationEncoding.code, FiniteEquationEncoding.code_mem_FP, yes_of_source, no_of_source⟩

theorem hard : problem.Hard := hard_of_ETR_reduction etr_reduction

theorem yes_iff (input : List Bool) : FiniteEquationEncoding.code input ∈ yes ↔ input ∈ ETR := by
  constructor
  · rintro ⟨p, hp, _, hf⟩
    have he : FiniteEquationEncoding.data input = p :=
      Option.some.inj ((FiniteEquationEncoding.decode input).symm.trans hp)
    subst p
    exact (FiniteEquationEncoding.feasible_iff input).mpr hf
  · exact yes_of_source input

theorem no_iff (input : List Bool) : FiniteEquationEncoding.code input ∈ no ↔ input ∉ ETR := by
  constructor
  · rintro ⟨p, hp, _, hf⟩ hi
    have he : FiniteEquationEncoding.data input = p :=
      Option.some.inj ((FiniteEquationEncoding.decode input).symm.trans hp)
    subst p
    exact hf ((FiniteEquationEncoding.feasible_iff input).mp hi)
  · exact no_of_source input

theorem malformed_outside {input : List Bool} (h : EquationSystemCodec.decode input = none) :
    input ∉ yes ∪ no := by
  rintro (⟨p, hp, _, _⟩ | ⟨p, hp, _, _⟩) <;> simp [h] at hp

end JointThermoComplexity.Complexity.FiniteEquationHardness

#print axioms JointThermoComplexity.Complexity.FiniteEquationHardness.etr_reduction
#print axioms JointThermoComplexity.Complexity.FiniteEquationHardness.hard
#print axioms JointThermoComplexity.Complexity.FiniteEquationHardness.yes_iff
#print axioms JointThermoComplexity.Complexity.FiniteEquationHardness.no_iff
