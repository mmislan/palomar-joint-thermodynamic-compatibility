module
public import proofs.JointThermoComplexity.Complexity.RealSyntax
public import proofs.Complexitylib.Classes.P.Defs

set_option autoImplicit false
@[expose] public section

/-!
# Binary existential-real complexity and promise problems

Polynomial reductions use Complexitylib's actual multitape binary Turing-machine
`FP` definition. The ETR language is the independently decoded real-formula
language. The real complexity class is its closure under polynomial reductions.
Promise membership uses a separating ordinary language; hardness must send both
source YES and source NO inputs into their respective promised sets.

These are standard definitions, not a substitute for a chemical membership,
hard-source, implementation-time, or completeness proof. No reaction-network
statement is assumed or defined into the class.
-/

namespace JointThermoComplexity.Complexity.RealComplexity

abbrev BitLanguage := Set (List Bool)

/-- Karp reduction, with computation measured on the existing binary TM model.
This has the same defining expression as Complexitylib's `MapReducesPoly`;
its NP-specific umbrella module is not needed for the present definitions. -/
def PolyReduces (L K : BitLanguage) : Prop :=
  ∃ f : List Bool → List Bool, f ∈ _root_.Complexity.FP ∧
    ∀ input, input ∈ L ↔ f input ∈ K

def ExistsR (L : BitLanguage) : Prop := PolyReduces L RealSyntax.ETR

structure PromiseProblem where
  yes : BitLanguage
  no : BitLanguage
  disjoint : Disjoint yes no

def PromiseProblem.Member (P : PromiseProblem) : Prop :=
  ∃ separator : BitLanguage, ExistsR separator ∧
    P.yes ⊆ separator ∧ Disjoint separator P.no

def PolyReducesToPromise (L : BitLanguage) (P : PromiseProblem) : Prop :=
  ∃ f : List Bool → List Bool, f ∈ _root_.Complexity.FP ∧
    (∀ input, input ∈ L → f input ∈ P.yes) ∧
    (∀ input, input ∉ L → f input ∈ P.no)

def PromiseProblem.Hard (P : PromiseProblem) : Prop :=
  ∀ L : BitLanguage, ExistsR L → PolyReducesToPromise L P

def PromiseProblem.Complete (P : PromiseProblem) : Prop := P.Member ∧ P.Hard

/-- A promise reduction must land inside the promise even on source NO inputs. -/
theorem promise_reduction_lands_in_promise {L : BitLanguage} {P : PromiseProblem}
    (h : PolyReducesToPromise L P) :
    ∃ f : List Bool → List Bool, f ∈ _root_.Complexity.FP ∧
      ∀ input, f input ∈ P.yes ∪ P.no := by
  classical
  obtain ⟨f, hf, hyes, hno⟩ := h
  refine ⟨f, hf, fun input => ?_⟩
  by_cases hi : input ∈ L
  · exact Or.inl (hyes input hi)
  · exact Or.inr (hno input hi)

/-- Disjointness turns the two required implications into exact verdicts. -/
theorem promise_reduction_verdicts {L : BitLanguage} {P : PromiseProblem}
    (h : PolyReducesToPromise L P) :
    ∃ f : List Bool → List Bool, f ∈ _root_.Complexity.FP ∧
      (∀ input, input ∈ L ↔ f input ∈ P.yes) ∧
      (∀ input, input ∉ L ↔ f input ∈ P.no) := by
  classical
  obtain ⟨f, hf, hyes, hno⟩ := h
  have apart : ∀ input, ¬ (f input ∈ P.yes ∧ f input ∈ P.no) := by
    intro input hi
    exact Set.disjoint_left.mp P.disjoint hi.1 hi.2
  refine ⟨f, hf, ?_, ?_⟩
  · intro input
    constructor
    · exact hyes input
    · intro hy
      by_contra hn
      exact apart input ⟨hy, hno input hn⟩
  · intro input
    constructor
    · exact hno input
    · intro hn hi
      exact apart input ⟨hyes input hi, hn⟩

end JointThermoComplexity.Complexity.RealComplexity

#print axioms Complexity.FP
#print axioms JointThermoComplexity.Complexity.RealComplexity.ExistsR
#print axioms JointThermoComplexity.Complexity.RealComplexity.PromiseProblem.Complete
#print axioms JointThermoComplexity.Complexity.RealComplexity.promise_reduction_verdicts
