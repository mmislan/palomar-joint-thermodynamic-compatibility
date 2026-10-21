module
public import proofs.JointThermoComplexity.PolynomialFrontend

set_option autoImplicit false
@[expose] public section

/-! Output properties of the emitted two-core source used in the publication:
flux feasibility of every output (the relaxed `MultiPAC` predicate), positive
production of every internal species under the union of all reactions at
every state where both supplied cores are productive, zero net change of every
external catalyst, and the factor bound `0 < b ≤ 2` for the polynomial
emitters. -/

namespace JointThermoComplexity.Emitted
open ThermoCoreCompatibility ThermoCoreCompatibility.Hypergraph
open scoped BigOperators
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E] {n m : ℕ}

/-! ### Flux feasibility of every output -/

theorem productive_pos {S R : Type*} [DecidableEq S] [DecidableEq R]
    {Q : ReversibleCRN S R} {k : ℕ} (T : CycleIn Q k) (v : R → ℝ)
    (h : T.motif.Productive v) : ∀ i, 0 < v (T.edge i) := by
  obtain ⟨ha,hg⟩ := (T.productive_iff_chain v).mp h
  exact chain_positive (fun i => v (T.edge i)) ha hg

omit [Fintype E] in
/-- Every emitted family, including every NO instance, admits one signed flux
vector that is positive on every reaction and productive for both cores. -/
theorem family_multiPAC (L : Branch E n) (R : Branch E m) : (family L R).MultiPAC := by
  obtain ⟨_,vL,hL⟩ := (leftCycle L R).isPAC.1
  obtain ⟨_,vR,hR⟩ := (rightCycle L R).isPAC.1
  have pL := productive_pos (leftCycle L R) vL hL
  have pR := productive_pos (rightCycle L R) vR hR
  let v : Reaction n m → ℝ := Sum.elim (fun i => vL (.inl i)) (fun i => vR (.inr i))
  have cL := ((leftCycle L R).productive_iff_chain vL).mp hL
  have cR := ((rightCycle L R).productive_iff_chain vR).mp hR
  refine ⟨v,?_,?_⟩
  · intro r
    cases r with
    | inl i => simpa [family, v, leftCycle] using pL i
    | inr i => simpa [family, v, rightCycle] using pR i
  · intro b
    cases b
    · simp only [family, Bool.false_eq_true, ↓reduceIte]
      exact ((leftCycle L R).productive_iff_chain v).mpr cL
    · simp only [family, ↓reduceIte]
      exact ((rightCycle L R).productive_iff_chain v).mpr cR

/-! ### Union production -/

/-- Net production of a species under all reactions of the emitted source. -/
def unionProduction (L : Branch E n) (R : Branch E m) (v : Reaction n m → ℝ)
    (s : Species E n m) : ℝ :=
  ∑ r, ((source L R).stoich s r : ℝ) * v r

omit [Fintype E] in
theorem stoich_left (L : Branch E n) (R : Branch E m) (s : Species E n m) (i : Fin (n+2)) :
    ((source L R).stoich s (.inl i) : ℝ) =
      (atom (leftVertex (finRotate (n+2) i)) (cycleGain n i) s : ℝ) -
        (atom (leftVertex i) 1 s : ℝ) := by
  simp only [ReversibleCRN.stoich, source]
  push_cast
  ring

omit [Fintype E] in
theorem stoich_right (L : Branch E n) (R : Branch E m) (s : Species E n m) (i : Fin (m+2)) :
    ((source L R).stoich s (.inr i) : ℝ) =
      (atom (rightVertex (finRotate (m+2) i)) (cycleGain m i) s : ℝ) -
        (atom (rightVertex i) 1 s : ℝ) := by
  simp only [ReversibleCRN.stoich, source]
  push_cast
  ring

omit [Fintype E] in
theorem atom_other {S : Type*} [DecidableEq S] (a s : S) (k : ℕ) (h : s ≠ a) :
    (atom a k s : ℝ) = 0 := by
  simp [atom, h]

/-- The left-core part of the union sum. -/
def leftPart (L : Branch E n) (R : Branch E m) (v : Reaction n m → ℝ) (s : Species E n m) : ℝ :=
  ∑ i, ((source L R).stoich s (.inl i) : ℝ) * v (.inl i)

/-- The right-core part of the union sum. -/
def rightPart (L : Branch E n) (R : Branch E m) (v : Reaction n m → ℝ) (s : Species E n m) : ℝ :=
  ∑ i, ((source L R).stoich s (.inr i) : ℝ) * v (.inr i)

omit [Fintype E] in
theorem union_split (L : Branch E n) (R : Branch E m) (v : Reaction n m → ℝ) (s : Species E n m) :
    unionProduction L R v s = leftPart L R v s + rightPart L R v s := by
  unfold unionProduction leftPart rightPart
  rw [Fintype.sum_sum_type]

omit [Fintype E] in
theorem leftPart_eq_motif (L : Branch E n) (R : Branch E m) (v : Reaction n m → ℝ)
    (s : Species E n m) :
    leftPart L R v s =
      ∑ r ∈ (leftCycle L R).motif.reactions, ((source L R).stoich s r : ℝ) * v r := by
  unfold leftPart
  change _ = ∑ r ∈ Finset.univ.image Sum.inl, _
  rw [Finset.sum_image (fun a _ b _ h => Sum.inl_injective h)]

omit [Fintype E] in
theorem rightPart_eq_motif (L : Branch E n) (R : Branch E m) (v : Reaction n m → ℝ)
    (s : Species E n m) :
    rightPart L R v s =
      ∑ r ∈ (rightCycle L R).motif.reactions, ((source L R).stoich s r : ℝ) * v r := by
  unfold rightPart
  change _ = ∑ r ∈ Finset.univ.image Sum.inr, _
  rw [Finset.sum_image (fun a _ b _ h => Sum.inr_injective h)]

omit [Fintype E] in
theorem leftPart_outside (L : Branch E n) (R : Branch E m) (v : Reaction n m → ℝ)
    (s : Species E n m) (hs : ∀ j, s ≠ leftVertex j) : leftPart L R v s = 0 := by
  unfold leftPart
  apply Finset.sum_eq_zero
  intro i _
  rw [stoich_left, atom_other _ _ _ (hs _), atom_other _ _ _ (hs _)]
  ring

omit [Fintype E] in
theorem rightPart_outside (L : Branch E n) (R : Branch E m) (v : Reaction n m → ℝ)
    (s : Species E n m) (hs : ∀ j, s ≠ rightVertex j) : rightPart L R v s = 0 := by
  unfold rightPart
  apply Finset.sum_eq_zero
  intro i _
  rw [stoich_right, atom_other _ _ _ (hs _), atom_other _ _ _ (hs _)]
  ring

omit [Fintype E] in
theorem leftPart_nonneg (L : Branch E n) (R : Branch E m) (v : Reaction n m → ℝ)
    (hL : (leftCycle L R).motif.Productive v) (s : Species E n m) : 0 ≤ leftPart L R v s := by
  by_cases hs : ∃ j, s = leftVertex j
  · obtain ⟨j,rfl⟩ := hs
    rw [leftPart_eq_motif]
    exact le_of_lt (hL _ (by simp [CycleIn.motif, leftCycle]))
  · push Not at hs
    rw [leftPart_outside L R v s hs]

omit [Fintype E] in
theorem rightPart_nonneg (L : Branch E n) (R : Branch E m) (v : Reaction n m → ℝ)
    (hR : (rightCycle L R).motif.Productive v) (s : Species E n m) : 0 ≤ rightPart L R v s := by
  by_cases hs : ∃ j, s = rightVertex j
  · obtain ⟨j,rfl⟩ := hs
    rw [rightPart_eq_motif]
    exact le_of_lt (hR _ (by simp [CycleIn.motif, rightCycle]))
  · push Not at hs
    rw [rightPart_outside L R v s hs]

omit [Fintype E] in
/-- Whenever both supplied cores are productive, every internal species of
either core is strictly produced by the union of all reactions. -/
theorem union_production_pos (L : Branch E n) (R : Branch E m) (v : Reaction n m → ℝ)
    (hL : (leftCycle L R).motif.Productive v) (hR : (rightCycle L R).motif.Productive v)
    (s : Species E n m)
    (hs : s ∈ (leftCycle L R).motif.species ∨ s ∈ (rightCycle L R).motif.species) :
    0 < unionProduction L R v s := by
  rw [union_split]
  have h₁ := leftPart_nonneg L R v hL s
  have h₂ := rightPart_nonneg L R v hR s
  rcases hs with hs | hs
  · have : 0 < leftPart L R v s := by rw [leftPart_eq_motif]; exact hL s hs
    linarith
  · have : 0 < rightPart L R v s := by rw [rightPart_eq_motif]; exact hR s hs
    linarith

omit [Fintype E] [DecidableEq E] in
theorem external_ne_left (e : E) (j : Fin (n+2)) :
    (external e : Species E n m) ≠ leftVertex j := by
  simp [external, leftVertex]

omit [Fintype E] [DecidableEq E] in
theorem external_ne_right (e : E) (j : Fin (m+2)) :
    (external e : Species E n m) ≠ rightVertex j := by
  unfold rightVertex
  split_ifs <;> simp [external]

omit [Fintype E] in
/-- External catalysts have identically zero net stoichiometric change. -/
theorem union_production_external (L : Branch E n) (R : Branch E m) (v : Reaction n m → ℝ)
    (e : E) : unionProduction L R v (external e) = 0 := by
  rw [union_split, leftPart_outside L R v _ (external_ne_left e),
    rightPart_outside L R v _ (external_ne_right e)]
  ring

/-- Every compatible state of the emitted source also produces every internal
species under the union of all its reactions. -/
theorem compatible_union_production (L : Branch E n) (R : Branch E m) (u : E → ℝ)
    (h : Compatible L R u) :
    ∃ z : Species E n m → ℝ, (∀ s, 0 < z s) ∧ (∀ e, z (external e) = u e) ∧
      (∀ r, 0 < (source L R).current z r) ∧
      (∀ s, s ∈ (leftCycle L R).motif.species ∨ s ∈ (rightCycle L R).motif.species →
        0 < unionProduction L R ((source L R).current z) s) ∧
      (∀ e, unionProduction L R ((source L R).current z) (external e) = 0) := by
  obtain ⟨z,hz,he,hj,hL,hR⟩ := h
  exact ⟨z,hz,he,hj,fun s hs => union_production_pos L R _ hL hR s hs,
    fun e => union_production_external L R _ e⟩

/-! ### Factor bounds -/

omit [Fintype E] [DecidableEq E] in
theorem barrier_le_of_coeff (b : Branch E n) (c : ℝ) (hc : 0 < c)
    (h : ∀ i, c ≤ b.coefficient i) (hc1 : c ≤ 1) (i : Fin (n+2)) :
    b.barrier i ≤ 1/c := by
  unfold Branch.barrier
  split_ifs
  · rw [le_div_iff₀ hc]; linarith
  · exact one_div_le_one_div_of_le hc (h _)

omit [DecidableEq E] in
theorem offsetBound_ge_one {k : ℕ} (c : Fin k→ℝ) (γ : Fin k→E→ℕ) : 1 ≤ offsetBound c γ := by
  have h : 0≤∑i,(c i+|c i|+1)*∏e,(2:ℝ)^γ i e := by
    apply Finset.sum_nonneg
    intro i _
    have hc:=neg_abs_le (c i)
    apply mul_nonneg (by linarith)
    exact Finset.prod_nonneg (fun _ _=>by positivity)
  unfold offsetBound
  linarith

/-- All kinetic factors of the boxed emitter lie in `(0,2]`. -/
theorem boxed_barriers_le_two {k : ℕ} (c : Fin k→ℝ) (γ : Fin k→E→ℕ) :
    let L:=polynomialLeft (offsetBound c γ) (offsetBound_pos c γ) c γ
    let R:=polynomialRight (offsetBound c γ) (offsetBound_pos c γ) c γ
    ∀ r, 0 < (source L R).barrier r ∧ (source L R).barrier r ≤ 2 := by
  intro L R r
  refine ⟨(source L R).barrier_pos r,?_⟩
  have hK := offsetBound_ge_one c γ
  cases r with
  | inl i =>
    have hb := barrier_le_of_coeff L 1 one_pos (by
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa [L, polynomialLeft, offsetBranch] using hK
      · simp only [L, polynomialLeft, offsetBranch, Fin.cases_succ]
        linarith [abs_nonneg (c j)]) le_rfl i
    change L.barrier i ≤ 2
    linarith
  | inr i =>
    have hb := barrier_le_of_coeff R (1/2) (by norm_num) (by
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [R, polynomialRight, halfBranch, offsetBranch, Fin.cases_zero]
        linarith
      · simp only [R, polynomialRight, halfBranch, offsetBranch, Fin.cases_succ]
        have := neg_abs_le (c j)
        linarith) (by norm_num) i
    change R.barrier i ≤ 2
    norm_num at hb
    linarith

omit [Fintype E] in
/-- All kinetic factors of the unboxed emitter lie in `(0,2]`. -/
theorem unboxed_barriers_le_two {k : ℕ} (c : Fin k→ℝ) (γ : Fin k→E→ℕ) :
    ∀ r, 0 < (source (unboxedLeft c γ) (unboxedRight c γ)).barrier r ∧
      (source (unboxedLeft c γ) (unboxedRight c γ)).barrier r ≤ 2 := by
  intro r
  refine ⟨(source _ _).barrier_pos r,?_⟩
  cases r with
  | inl i =>
    have hb := barrier_le_of_coeff (unboxedLeft c γ) 1 one_pos (by
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [unboxedLeft, variableOffsetBranch]
      · simp only [unboxedLeft, variableOffsetBranch, Fin.cases_succ]
        linarith [abs_nonneg (c j)]) le_rfl i
    change (unboxedLeft c γ).barrier i ≤ 2
    linarith
  | inr i =>
    have hb := barrier_le_of_coeff (unboxedRight c γ) (1/2) (by norm_num) (by
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [unboxedRight, halfBranch, variableOffsetBranch]
      · simp only [unboxedRight, halfBranch, variableOffsetBranch, Fin.cases_succ]
        have := neg_abs_le (c j)
        linarith) (by norm_num) i
    change (unboxedRight c γ).barrier i ≤ 2
    norm_num at hb
    linarith

end
end JointThermoComplexity.Emitted

#print axioms JointThermoComplexity.Emitted.family_multiPAC
#print axioms JointThermoComplexity.Emitted.compatible_union_production
#print axioms JointThermoComplexity.Emitted.boxed_barriers_le_two
#print axioms JointThermoComplexity.Emitted.unboxed_barriers_le_two

#print axioms JointThermoComplexity.Emitted.family_multiPAC

#print axioms JointThermoComplexity.Emitted.compatible_union_production

#print axioms JointThermoComplexity.Emitted.boxed_barriers_le_two

#print axioms JointThermoComplexity.Emitted.unboxed_barriers_le_two
