module
public import proofs.JointThermoComplexity.Complexity.NetworkCodec
public import proofs.JointThermoComplexity.Complexity.LiteralBridge
public import proofs.JointThermoComplexity.Complexity.RealComplexity

set_option autoImplicit false
@[expose] public section

/-! The chemical promise is stated directly on decoded literal data. It neither
requires a reduction certificate nor recognizes PAC status algorithmically. -/

namespace JointThermoComplexity.Complexity.ChemicalPromiseProblem
open RealComplexity NetworkData
open scoped BigOperators

def internalBox : ClosedBox := ⟨⟨1, 4, by decide⟩, ⟨1, 2, by decide⟩⟩
def externalBox : ClosedBox := ⟨⟨1, 2, by decide⟩, ⟨1, 1, by decide⟩⟩

def PrescribedBoxes (boxed : Bool) (Q : NetworkCodec.Input) : Prop :=
  if boxed then
    (∀ a s, s ∈ (Q.network.motifs a).species → Q.network.boxes s = some internalBox) ∧
    (∀ s, (∀ a, s ∉ (Q.network.motifs a).species) → Q.network.boxes s = some externalBox)
  else ∀ s, Q.network.boxes s = none

def Domain (boxed : Bool) (Q : NetworkCodec.Input) : Prop :=
  Q.coreCount = 2 ∧
  (∀ a, (LiteralBridge.toMotif Q.network a).IsPAC) ∧
  (∀ r, 0 < ((Q.network.reactions r).numerator : ℝ) / (Q.network.reactions r).denominator ∧
    ((Q.network.reactions r).numerator : ℝ) / (Q.network.reactions r).denominator ≤ 2) ∧
  PrescribedBoxes boxed Q ∧
  ∀ r, (∑ s, (Q.network.reactions r).reactant s) ≤ (if boxed then 6 else 8) ∧
    (∑ s, (Q.network.reactions r).product s) ≤ (if boxed then 6 else 8)

def yes (boxed : Bool) : BitLanguage :=
  {input | ∃ Q, NetworkCodec.decode input = some Q ∧ Domain boxed Q ∧ Q.network.Feasible}

def no (boxed : Bool) : BitLanguage :=
  {input | ∃ Q, NetworkCodec.decode input = some Q ∧ Domain boxed Q ∧ ¬ Q.network.Feasible}

def problem (boxed : Bool) : PromiseProblem where
  yes := yes boxed
  no := no boxed
  disjoint := Set.disjoint_left.mpr (by
    rintro input ⟨Q, hQ, _hdQ, hyes⟩ ⟨R, hR, _hdR, hno⟩
    have he : Q = R := Option.some.inj (hQ.symm.trans hR)
    subst R
    exact hno hyes)

theorem code_yes_iff (boxed : Bool) (Q : NetworkCodec.Input) :
    Q.code ∈ yes boxed ↔ Domain boxed Q ∧ Q.network.Feasible := by
  simp [yes]

theorem code_no_iff (boxed : Bool) (Q : NetworkCodec.Input) :
    Q.code ∈ no boxed ↔ Domain boxed Q ∧ ¬ Q.network.Feasible := by
  simp [no]

end JointThermoComplexity.Complexity.ChemicalPromiseProblem

#print axioms JointThermoComplexity.Complexity.ChemicalPromiseProblem.Domain
#print axioms JointThermoComplexity.Complexity.ChemicalPromiseProblem.problem
#print axioms JointThermoComplexity.Complexity.ChemicalPromiseProblem.code_yes_iff
#print axioms JointThermoComplexity.Complexity.ChemicalPromiseProblem.code_no_iff
