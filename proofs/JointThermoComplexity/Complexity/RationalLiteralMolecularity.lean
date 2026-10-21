module
public import proofs.JointThermoComplexity.Complexity.RationalPolynomialNetwork

set_option autoImplicit false
@[expose] public section

/-! Side molecularity counts every stored atom, including catalytic padding.
The bounds apply to each reaction in the actual finite serialized network. -/

namespace JointThermoComplexity.Complexity.RationalLiteralMolecularity
open RationalBranchData RationalLiteralNetwork SparseInteger RawChemicalPolynomial
open scoped BigOperators
variable {e n m d : ℕ}

theorem sum_atom (a : Species e n m) (k : ℕ) : (∑ s, RationalLiteralNetwork.atom a k s) = k := by
  simp only [RationalLiteralNetwork.atom, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem sum_padding (γ : Fin e → ℕ) : (∑ s : Species e n m, padding γ s) = ∑ a, γ a := by
  simp [padding, Fintype.sum_sum_type]

theorem powers_bound (b : Data (Fin e) n) (hb : ∀ i, (∑ a, b.exponent i a) ≤ d)
    (i : Fin (n + 2)) : (∑ a, b.powers i a) ≤ d := by
  unfold Data.powers
  split_ifs
  · simp only [Finset.sum_const_zero, Nat.zero_le]
  · exact hb _

theorem raw_bounds (L : Data (Fin e) n) (R : Data (Fin e) m)
    (hL : ∀ i, (∑ a, L.exponent i a) ≤ d) (hR : ∀ i, (∑ a, R.exponent i a) ≤ d)
    (r : Reaction n m) :
    (∑ s, reactantRaw L R r s) ≤ 2 + d ∧ (∑ s, productRaw L R r s) ≤ 2 + d := by
  cases r with
  | inl i =>
    have hp := powers_bound L hL i
    have hg : gain n i ≤ 2 := by unfold gain; split_ifs <;> omega
    simp only [reactantRaw, productRaw, Finset.sum_add_distrib, sum_atom, sum_padding]
    omega
  | inr i =>
    have hp := powers_bound R hR i
    have hg : gain m i ≤ 2 := by unfold gain; split_ifs <;> omega
    simp only [reactantRaw, productRaw, Finset.sum_add_distrib, sum_atom, sum_padding]
    omega

theorem finite_bounds (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m)
    (hL : ∀ i, (∑ a, L.exponent i a) ≤ d) (hR : ∀ i, (∑ a, R.exponent i a) ≤ d)
    (r : Fin (reactionCount n m)) :
    (∑ s, ((network boxed L R).reactions r).reactant s) ≤ 2 + d ∧
      (∑ s, ((network boxed L R).reactions r).product s) ≤ 2 + d := by
  have ha : (∑ s, ((network boxed L R).reactions r).reactant s) =
      ∑ s : Species e n m, reactantRaw L R ((reactionNumbering n m).symm r) s := by
    simpa only [network, reaction, Equiv.symm_apply_apply] using
      ((speciesNumbering e n m).sum_comp (fun s => ((network boxed L R).reactions r).reactant s)).symm
  have hb : (∑ s, ((network boxed L R).reactions r).product s) =
      ∑ s : Species e n m, productRaw L R ((reactionNumbering n m).symm r) s := by
    simpa only [network, reaction, Equiv.symm_apply_apply] using
      ((speciesNumbering e n m).sum_comp (fun s => ((network boxed L R).reactions r).product s)).symm
  rw [ha, hb]
  exact raw_bounds L R hL hR _

theorem boxed_left_degree {V : Type} [Fintype V] [DecidableEq V] (p : Poly V) (hp : DegreeLE 4 p)
    (i : Fin (p.length + 1)) : (∑ v, (RationalPolynomialBranches.boxedLeft p).exponent i v) ≤ 4 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [RationalPolynomialBranches.boxedLeft]
  · exact exponent_bound p hp j

theorem boxed_right_degree {V : Type} [Fintype V] [DecidableEq V] (p : Poly V) (hp : DegreeLE 4 p)
    (i : Fin (p.length + 1)) : (∑ v, (RationalPolynomialBranches.boxedRight p).exponent i v) ≤ 4 := by
  exact boxed_left_degree p hp i

theorem unboxed_left_degree {V : Type} [Fintype V] [DecidableEq V] (p : Poly V) (hp : DegreeLE 4 p)
    (i : Fin (p.length + 1)) : (∑ v, (RationalPolynomialBranches.unboxedLeft p).exponent i v) ≤ 4 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [RationalPolynomialBranches.unboxedLeft, Fintype.sum_option]
  · simpa only [RationalPolynomialBranches.unboxedLeft, Fin.cases_succ,
      Fintype.sum_option, zero_add] using exponent_bound p hp j

theorem unboxed_right_degree {V : Type} [Fintype V] [DecidableEq V] (p : Poly V) (hp : DegreeLE 4 p)
    (i : Fin (p.length + 1)) : (∑ v, (RationalPolynomialBranches.unboxedRight p).exponent i v) ≤ 4 := by
  exact unboxed_left_degree p hp i

theorem left_degree (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) (hp : DegreeLE 4 p.payload)
    (i : Fin (p.payload.length + 1)) : (∑ a, (RationalPolynomialNetwork.left boxed p).exponent i a) ≤ 4 := by
  cases boxed
  · change (∑ a, (RationalPolynomialBranches.unboxedLeft p.payload).exponent i (finSuccEquiv p.arity a)) ≤ 4
    rw [(finSuccEquiv p.arity).sum_comp]
    exact unboxed_left_degree p.payload hp i
  · exact boxed_left_degree p.payload hp i

theorem right_degree (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) (hp : DegreeLE 4 p.payload)
    (i : Fin (p.payload.length + 1)) : (∑ a, (RationalPolynomialNetwork.right boxed p).exponent i a) ≤ 4 := by
  cases boxed
  · change (∑ a, (RationalPolynomialBranches.unboxedRight p.payload).exponent i (finSuccEquiv p.arity a)) ≤ 4
    rw [(finSuccEquiv p.arity).sum_comp]
    exact unboxed_right_degree p.payload hp i
  · exact boxed_right_degree p.payload hp i

theorem polynomial_bounds (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) (hp : DegreeLE 4 p.payload)
    (r : Fin (reactionCount p.payload.length p.payload.length)) :
    (∑ s, ((RationalPolynomialNetwork.network boxed p).reactions r).reactant s) ≤ 6 ∧
      (∑ s, ((RationalPolynomialNetwork.network boxed p).reactions r).product s) ≤ 6 :=
  finite_bounds boxed _ _ (left_degree boxed p hp) (right_degree boxed p hp) r

theorem normalized_bounds (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) (hp : StrictPositivityProblem.Domain p)
    (r : Fin (reactionCount (FinitePositiveCoordinates.data boxed p).payload.length
      (FinitePositiveCoordinates.data boxed p).payload.length)) :
    (∑ s, ((RationalPolynomialNetwork.network boxed (FinitePositiveCoordinates.data boxed p)).reactions r).reactant s) ≤
        (if boxed then 6 else 8) ∧
      (∑ s, ((RationalPolynomialNetwork.network boxed (FinitePositiveCoordinates.data boxed p)).reactions r).product s) ≤
        (if boxed then 6 else 8) := by
  have h := polynomial_bounds boxed _ (FinitePositiveCoordinates.data_domain boxed p hp).2.1 r
  cases boxed <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

end JointThermoComplexity.Complexity.RationalLiteralMolecularity

#print axioms JointThermoComplexity.Complexity.RationalLiteralMolecularity.raw_bounds
#print axioms JointThermoComplexity.Complexity.RationalLiteralMolecularity.finite_bounds
#print axioms JointThermoComplexity.Complexity.RationalLiteralMolecularity.polynomial_bounds
#print axioms JointThermoComplexity.Complexity.RationalLiteralMolecularity.normalized_bounds
