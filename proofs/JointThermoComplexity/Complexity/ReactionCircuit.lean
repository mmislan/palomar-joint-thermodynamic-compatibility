module
public import proofs.JointThermoComplexity.Complexity.MonomialCircuit

set_option autoImplicit false
@[expose] public section

/-!
# Fixed rational literal reactions

Positive integer numerator and denominator data are fixed before activities are
chosen. The circuit computes the numerator of the current. A later formula can
equate this output with denominator times a shared current variable, avoiding
division gates and expansion of binary exponents.
-/

namespace JointThermoComplexity.Complexity.ReactionCircuit
open RealCircuit
open scoped BigOperators

structure Reaction (n : ℕ) where
  reactant : Fin n → ℕ
  product : Fin n → ℕ
  numerator : ℕ
  denominator : ℕ
  numerator_pos : 0 < numerator
  denominator_pos : 0 < denominator

variable {n k : ℕ}

def Reaction.difference (r : Reaction n) (ρ : Fin n → ℝ) : ℝ :=
  (∏ i, ρ i ^ r.reactant i) - ∏ i, ρ i ^ r.product i

noncomputable def Reaction.current (r : Reaction n) (ρ : Fin n → ℝ) : ℝ :=
  (r.numerator : ℝ) / r.denominator * r.difference ρ

def Reaction.gateCost (r : Reaction n) : ℕ :=
  6 + MonomialCircuit.gateCost (MonomialCircuit.denseTerms r.reactant) +
    MonomialCircuit.gateCost (MonomialCircuit.denseTerms r.product)

structure State (n : ℕ) where
  size : ℕ
  circuit : Circuit n size
  output : Fin size

def State.value (s : State n) (ρ : Fin n → ℝ) : ℝ := s.circuit.eval ρ s.output

def build (c : Circuit n k) (r : Reaction n) : State n :=
  let left := MonomialCircuit.build c (MonomialCircuit.denseTerms r.reactant)
  let right := MonomialCircuit.build left.circuit (MonomialCircuit.denseTerms r.product)
  let lhs := Fin.castLE (MonomialCircuit.build_size_ge left.circuit
    (MonomialCircuit.denseTerms r.product)) left.accumulator
  let negative := right.circuit.snoc (.neg right.accumulator)
  let difference := negative.snoc (.add lhs.castSucc (Fin.last right.size))
  let coefficient := difference.snoc (.constant (r.numerator : ℤ))
  ⟨right.size + 4, coefficient.snoc
    (.mul (Fin.last (right.size + 1)).castSucc (Fin.last (right.size + 2))),
    Fin.last (right.size + 3)⟩

theorem build_value (c : Circuit n k) (r : Reaction n) (ρ : Fin n → ℝ) :
    (build c r).value ρ = (r.difference ρ) * r.numerator := by
  have hl := MonomialCircuit.build_value c (MonomialCircuit.denseTerms r.reactant) ρ
  have hr := MonomialCircuit.build_value
    (MonomialCircuit.build c (MonomialCircuit.denseTerms r.reactant)).circuit
    (MonomialCircuit.denseTerms r.product) ρ
  have hk := MonomialCircuit.build_preserves
    (MonomialCircuit.build c (MonomialCircuit.denseTerms r.reactant)).circuit
    (MonomialCircuit.denseTerms r.product)
    (MonomialCircuit.build c (MonomialCircuit.denseTerms r.reactant)).accumulator ρ
  simp only [MonomialCircuit.State.value] at hl hr
  simp only [build, State.value, Circuit.eval_snoc_last, Step.eval,
    Circuit.eval_snoc_castSucc, Int.cast_natCast]
  rw [hk, hl, hr, MonomialCircuit.eval_denseTerms, MonomialCircuit.eval_denseTerms]
  rfl

theorem build_size_ge (c : Circuit n k) (r : Reaction n) : k ≤ (build c r).size := by
  have hl := MonomialCircuit.build_size_ge c (MonomialCircuit.denseTerms r.reactant)
  have hr := MonomialCircuit.build_size_ge
    (MonomialCircuit.build c (MonomialCircuit.denseTerms r.reactant)).circuit
    (MonomialCircuit.denseTerms r.product)
  simp only [build]
  omega

theorem build_size_le (c : Circuit n k) (r : Reaction n) :
    (build c r).size ≤ k + r.gateCost := by
  have hl := MonomialCircuit.build_size_le c (MonomialCircuit.denseTerms r.reactant)
  have hr := MonomialCircuit.build_size_le
    (MonomialCircuit.build c (MonomialCircuit.denseTerms r.reactant)).circuit
    (MonomialCircuit.denseTerms r.product)
  simp only [build, Reaction.gateCost]
  omega

theorem build_preserves (c : Circuit n k) (r : Reaction n) (i : Fin k) (ρ : Fin n → ℝ) :
    (build c r).circuit.eval ρ (Fin.castLE (build_size_ge c r) i) = c.eval ρ i := by
  let left := MonomialCircuit.build c (MonomialCircuit.denseTerms r.reactant)
  let right := MonomialCircuit.build left.circuit (MonomialCircuit.denseTerms r.product)
  let li := Fin.castLE (MonomialCircuit.build_size_ge c
    (MonomialCircuit.denseTerms r.reactant)) i
  let ri := Fin.castLE (MonomialCircuit.build_size_ge left.circuit
    (MonomialCircuit.denseTerms r.product)) li
  have hi : Fin.castLE (build_size_ge c r) i = ri.castSucc.castSucc.castSucc.castSucc := by
    apply Fin.ext
    rfl
  rw [hi]
  simp only [build, Circuit.eval_snoc_castSucc]
  change right.circuit.eval ρ ri = c.eval ρ i
  rw [MonomialCircuit.build_preserves, MonomialCircuit.build_preserves]

theorem denominator_mul_current (r : Reaction n) (ρ : Fin n → ℝ) :
    (r.denominator : ℝ) * r.current ρ = r.difference ρ * r.numerator := by
  have hq : (r.denominator : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt r.denominator_pos
  unfold Reaction.current
  calc
    _ = ((r.numerator : ℝ) / r.denominator * r.denominator) * r.difference ρ := by ac_rfl
    _ = (r.numerator : ℝ) * r.difference ρ := by rw [div_mul_cancel₀ _ hq]
    _ = _ := mul_comm _ _

theorem current_equation_iff (r : Reaction n) (ρ : Fin n → ℝ) (j : ℝ) :
    (r.denominator : ℝ) * j = r.difference ρ * r.numerator ↔ j = r.current ρ := by
  rw [← denominator_mul_current]
  have hq : (r.denominator : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt r.denominator_pos
  constructor
  · exact mul_left_cancel₀ hq
  · intro h
    rw [h]

end JointThermoComplexity.Complexity.ReactionCircuit

#print axioms JointThermoComplexity.Complexity.ReactionCircuit.build_value
#print axioms JointThermoComplexity.Complexity.ReactionCircuit.build_size_le
#print axioms JointThermoComplexity.Complexity.ReactionCircuit.build_preserves
#print axioms JointThermoComplexity.Complexity.ReactionCircuit.current_equation_iff
