module
public import proofs.JointThermoComplexity.Complexity.FiniteStrictBounds
public import proofs.JointThermoComplexity.Complexity.RealComplexity

set_option autoImplicit false
@[expose] public section

/-! A transparent degree-four integer strict-positivity promise, with bounded
stored coefficients. Its definition contains neither reductions nor certificates. -/

namespace JointThermoComplexity.Complexity.StrictPositivityProblem
open SparseInteger SparsePolynomialCodec RealComplexity

def Domain (p : PolynomialData) : Prop :=
  0 < p.arity ∧ DegreeLE 4 p.payload ∧ CoefficientsLE 409600 p.payload

def Box {n : ℕ} (x : Fin n → ℝ) : Prop := ∀ i, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2

def Positive (boxed : Bool) (p : PolynomialData) : Prop :=
  if boxed then ∃ x : Fin p.arity → ℝ, Box x ∧ 0 < (interpret p.payload).eval₂ (Int.castRingHom ℝ) x
  else ∃ x : Fin p.arity → ℝ, 0 < (interpret p.payload).eval₂ (Int.castRingHom ℝ) x

def yes (boxed : Bool) : BitLanguage := {input | ∃ p, decode input = some p ∧ Domain p ∧ Positive boxed p}
def no (boxed : Bool) : BitLanguage := {input | ∃ p, decode input = some p ∧ Domain p ∧ ¬ Positive boxed p}

def problem (boxed : Bool) : PromiseProblem where
  yes := yes boxed
  no := no boxed
  disjoint := Set.disjoint_left.mpr (by
    rintro input ⟨p, hp, _hpd, hpos⟩ ⟨q, hq, _hqd, hneg⟩
    have he : p = q := Option.some.inj (hp.symm.trans hq)
    subst q
    exact hneg hpos)

def data (boxed : Bool) (p : EquationSystemCodec.Data) : PolynomialData :=
  if boxed then FiniteStrictData.boundedData p else FiniteStrictData.allRealData p

def code (boxed : Bool) (p : EquationSystemCodec.Data) : List Bool := SparsePolynomialCodec.code (data boxed p)

theorem data_domain (boxed : Bool) (p : EquationSystemCodec.Data) (hp : FiniteEquationHardness.Domain p) :
    Domain (data boxed p) := by
  cases boxed
  · exact ⟨FiniteStrictData.variableCount_pos p, FiniteStrictData.allReal_degree p,
      FiniteStrictBounds.allReal_coefficients p hp⟩
  · exact ⟨FiniteStrictData.variableCount_pos p, FiniteStrictData.bounded_degree p,
      FiniteStrictBounds.bounded_coefficients p hp⟩

theorem decode_code (boxed : Bool) (p : EquationSystemCodec.Data) :
    decode (code boxed p) = some (data boxed p) := SparsePolynomialCodec.decode_code _

theorem yes_code (boxed : Bool) (p : EquationSystemCodec.Data) (hp : FiniteEquationHardness.Domain p)
    (h : Positive boxed (data boxed p)) : code boxed p ∈ yes boxed := ⟨_, decode_code boxed p, data_domain boxed p hp, h⟩

theorem no_code (boxed : Bool) (p : EquationSystemCodec.Data) (hp : FiniteEquationHardness.Domain p)
    (h : ¬ Positive boxed (data boxed p)) : code boxed p ∈ no boxed := ⟨_, decode_code boxed p, data_domain boxed p hp, h⟩

end JointThermoComplexity.Complexity.StrictPositivityProblem

#print axioms JointThermoComplexity.Complexity.StrictPositivityProblem.problem
#print axioms JointThermoComplexity.Complexity.StrictPositivityProblem.data_domain
