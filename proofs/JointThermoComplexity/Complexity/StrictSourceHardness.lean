module
public import proofs.JointThermoComplexity.Complexity.StrictPositivityProblem
public import proofs.JointThermoComplexity.Complexity.StrictSourceFP
public import proofs.JointThermoComplexity.Complexity.FiniteStrictSemantics
public import proofs.JointThermoComplexity.Complexity.ReductionComposition

set_option autoImplicit false
@[expose] public section

/-! Unconditional binary polynomial hardness of degree-four integer strict
positivity, over the open half cube and over all reals. Both source verdicts
land in the bounded-coefficient promise. The implementation is the actual
total binary transducer, composed with the actual finite-equation encoder. -/

namespace JointThermoComplexity.Complexity.StrictSourceHardness
open RealSyntax RealComplexity

theorem semantic_iff (boxed : Bool) (p : EquationSystemCodec.Data)
    (hp : FiniteEquationHardness.Domain p) :
    FiniteEquationSemantics.Feasible p.rows ↔
      StrictPositivityProblem.Positive boxed (StrictPositivityProblem.data boxed p) := by
  cases boxed
  · exact FiniteStrictSemantics.allReal_iff p hp
  · exact FiniteStrictSemantics.bounded_iff p hp

theorem strict_output_code (boxed : Bool) (p : EquationSystemCodec.Data)
    (hp : FiniteEquationHardness.Domain p) :
    StrictSourceFP.output boxed (EquationSystemCodec.code p) = StrictPositivityProblem.code boxed p := by
  rw [StrictSourceFP.output_code boxed p hp]
  cases boxed <;> rfl

def map (boxed : Bool) (input : List Bool) : List Bool :=
  StrictSourceFP.output boxed (FiniteEquationEncoding.code input)

theorem map_mem_FP (boxed : Bool) : map boxed ∈ _root_.Complexity.FP :=
  _root_.Complexity.mem_FP_comp FiniteEquationEncoding.code_mem_FP (StrictSourceFP.output_mem_FP boxed)

theorem map_code (boxed : Bool) (input : List Bool) :
    map boxed input = StrictPositivityProblem.code boxed (FiniteEquationEncoding.data input) :=
  strict_output_code boxed _ (FiniteEquationHardness.data_domain input)

theorem yes_of_source (boxed : Bool) (input : List Bool) (hi : input ∈ ETR) :
    map boxed input ∈ (StrictPositivityProblem.problem boxed).yes := by
  rw [map_code]
  exact StrictPositivityProblem.yes_code boxed _ (FiniteEquationHardness.data_domain input)
    ((semantic_iff boxed _ (FiniteEquationHardness.data_domain input)).mp
      ((FiniteEquationEncoding.feasible_iff input).mp hi))

theorem no_of_source (boxed : Bool) (input : List Bool) (hi : input ∉ ETR) :
    map boxed input ∈ (StrictPositivityProblem.problem boxed).no := by
  rw [map_code]
  apply StrictPositivityProblem.no_code boxed _ (FiniteEquationHardness.data_domain input)
  intro hpos
  exact hi ((FiniteEquationEncoding.feasible_iff input).mpr
    ((semantic_iff boxed _ (FiniteEquationHardness.data_domain input)).mpr hpos))

theorem etr_reduction (boxed : Bool) :
    PolyReducesToPromise ETR (StrictPositivityProblem.problem boxed) :=
  ⟨map boxed, map_mem_FP boxed, yes_of_source boxed, no_of_source boxed⟩

theorem hard (boxed : Bool) : (StrictPositivityProblem.problem boxed).Hard :=
  hard_of_ETR_reduction (etr_reduction boxed)

theorem lands_in_promise (boxed : Bool) (input : List Bool) :
    map boxed input ∈ (StrictPositivityProblem.problem boxed).yes ∪
      (StrictPositivityProblem.problem boxed).no := by
  classical
  by_cases hi : input ∈ ETR
  · exact Or.inl (yes_of_source boxed input hi)
  · exact Or.inr (no_of_source boxed input hi)

theorem yes_iff (boxed : Bool) (input : List Bool) :
    map boxed input ∈ (StrictPositivityProblem.problem boxed).yes ↔ input ∈ ETR := by
  classical
  constructor
  · intro hy
    by_contra hn
    exact Set.disjoint_left.mp (StrictPositivityProblem.problem boxed).disjoint
      hy (no_of_source boxed input hn)
  · exact yes_of_source boxed input

theorem no_iff (boxed : Bool) (input : List Bool) :
    map boxed input ∈ (StrictPositivityProblem.problem boxed).no ↔ input ∉ ETR := by
  constructor
  · intro hn hi
    exact Set.disjoint_left.mp (StrictPositivityProblem.problem boxed).disjoint
      (yes_of_source boxed input hi) hn
  · exact no_of_source boxed input

end JointThermoComplexity.Complexity.StrictSourceHardness

#print axioms JointThermoComplexity.Complexity.StrictSourceHardness.map_mem_FP
#print axioms JointThermoComplexity.Complexity.StrictSourceHardness.etr_reduction
#print axioms JointThermoComplexity.Complexity.StrictSourceHardness.hard
#print axioms JointThermoComplexity.Complexity.StrictSourceHardness.lands_in_promise
#print axioms JointThermoComplexity.Complexity.StrictSourceHardness.yes_iff
#print axioms JointThermoComplexity.Complexity.StrictSourceHardness.no_iff
