module
public import proofs.JointThermoComplexity.Complexity.ChemicalPromiseProblem
public import proofs.JointThermoComplexity.Complexity.RationalLiteralMolecularity

set_option autoImplicit false
@[expose] public section

/-! The normalized emitter satisfies every structural promise independently of
the source verdict. Motif species are exactly the internally boxed species. -/

namespace JointThermoComplexity.Complexity.RationalPolynomialPromise
open RationalBranchData RationalLiteralNetwork
variable {e n m : ℕ}

theorem left_mem (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) (i : Fin (n + 2)) :
    speciesNumbering e n m (leftVertex i) ∈ ((network boxed L R).motifs 0).species := by
  simp [network, leftMotif]

theorem right_mem (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) (i : Fin (m + 2)) :
    speciesNumbering e n m (rightVertex i) ∈ ((network boxed L R).motifs 1).species := by
  simp [network, rightMotif]

theorem left_vertex_box (L : Data (Fin e) n) (R : Data (Fin e) m) (i : Fin (n + 2)) :
    (network true L R).boxes (speciesNumbering e n m (leftVertex i)) = some ChemicalPromiseProblem.internalBox := by
  simp [network, boxes, leftVertex, internalBox, ChemicalPromiseProblem.internalBox]

theorem right_vertex_box (L : Data (Fin e) n) (R : Data (Fin e) m) (i : Fin (m + 2)) :
    (network true L R).boxes (speciesNumbering e n m (rightVertex i)) = some ChemicalPromiseProblem.internalBox := by
  simp only [network, boxes, Equiv.symm_apply_apply]
  unfold rightVertex
  split_ifs <;> rfl

theorem prescribed_boxes (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) :
    ChemicalPromiseProblem.PrescribedBoxes boxed (input boxed L R) := by
  cases boxed
  · change ∀ s, (network false L R).boxes s = none
    intro s
    rfl
  · change (∀ a s, s ∈ ((network true L R).motifs a).species →
        (network true L R).boxes s = some ChemicalPromiseProblem.internalBox) ∧
      (∀ s, (∀ a, s ∉ ((network true L R).motifs a).species) →
        (network true L R).boxes s = some ChemicalPromiseProblem.externalBox)
    constructor
    · intro a s hs
      fin_cases a
      · change s ∈ (leftMotif e n m).species at hs
        obtain ⟨i, _hi, he⟩ := Finset.mem_image.mp hs
        rw [← he]
        exact left_vertex_box L R i
      · change s ∈ (rightMotif e n m).species at hs
        obtain ⟨i, _hi, he⟩ := Finset.mem_image.mp hs
        rw [← he]
        exact right_vertex_box L R i
    · intro s hs
      obtain ⟨s, rfl⟩ := (speciesNumbering e n m).surjective s
      cases s with
      | inl i => exact False.elim (hs 0 (left_mem true L R i))
      | inr s => cases s with
        | inl a =>
          simp [network, boxes, externalBox, ChemicalPromiseProblem.externalBox]
        | inr j =>
          have he : rightVertex (e := e) (n := n) (⟨j.val + 2, by omega⟩ : Fin (m + 2)) =
              Sum.inr (Sum.inr j) := RationalLiteralBoxes.right_private j
          have hm := right_mem true L R (⟨j.val + 2, by omega⟩ : Fin (m + 2))
          rw [he] at hm
          exact False.elim (hs 1 hm)

theorem domain (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) (hp : StrictPositivityProblem.Domain p) :
    ChemicalPromiseProblem.Domain boxed (RationalPolynomialNetwork.input boxed (FinitePositiveCoordinates.data boxed p)) := by
  refine ⟨rfl, RationalPolynomialNetwork.supplied_PACs boxed _,
    RationalPolynomialNetwork.factor_bounds boxed _, prescribed_boxes boxed _ _, ?_⟩
  intro r
  exact RationalLiteralMolecularity.normalized_bounds boxed p hp r

theorem yes_iff (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) (hp : StrictPositivityProblem.Domain p) :
    RationalPolynomialNetwork.code boxed (FinitePositiveCoordinates.data boxed p) ∈ ChemicalPromiseProblem.yes boxed ↔
      StrictPositivityProblem.Positive boxed p := by
  unfold RationalPolynomialNetwork.code
  rw [ChemicalPromiseProblem.code_yes_iff]
  exact (and_iff_right (domain boxed p hp)).trans (RationalPolynomialNetwork.normalized_semantics boxed p hp)

theorem no_iff (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) (hp : StrictPositivityProblem.Domain p) :
    RationalPolynomialNetwork.code boxed (FinitePositiveCoordinates.data boxed p) ∈ ChemicalPromiseProblem.no boxed ↔
      ¬ StrictPositivityProblem.Positive boxed p := by
  unfold RationalPolynomialNetwork.code
  rw [ChemicalPromiseProblem.code_no_iff]
  exact (and_iff_right (domain boxed p hp)).trans (not_congr (RationalPolynomialNetwork.normalized_semantics boxed p hp))

end JointThermoComplexity.Complexity.RationalPolynomialPromise

#print axioms JointThermoComplexity.Complexity.RationalPolynomialPromise.prescribed_boxes
#print axioms JointThermoComplexity.Complexity.RationalPolynomialPromise.domain
#print axioms JointThermoComplexity.Complexity.RationalPolynomialPromise.yes_iff
#print axioms JointThermoComplexity.Complexity.RationalPolynomialPromise.no_iff
