module
public import proofs.JointThermoComplexity.Complexity.SparseSectionData
public import proofs.JointThermoComplexity.Complexity.FiniteGeneratedEnergy
public import proofs.JointThermoComplexity.Complexity.FiniteRowEnergyLoop

set_option autoImplicit false
@[expose] public section

/-! Exact full finite strict-polynomial section order. Original rows, scale
initial/edges, circles and error initial/edges concatenate literally after the
selected leading term. The final codec terminator is added exactly once.
-/

namespace JointThermoComplexity.Complexity.FiniteStrictSections
open SparseInteger EquationSystemCodec FiniteStrictData FiniteStrictNumbering FiniteGeneratedEnergy
open SparseSectionData NumberedTermEquations

def circles (p : Data) (j : Fin (scaleCoordinateCount p)) : Poly (Fin (variableCount p)) :=
  paddedContribution p (circleIndex p ((scaleCoordinateEnumeration p).symm j))

def paddedParts (p : Data) : Fin (paddedEquationCount p) → Poly (Fin (variableCount p)) :=
  Fin.append (Fin.append (FiniteRowSquare.contribution p)
    (Fin.append (fun _ : Fin 1 => paddedContribution p (scaleInitialIndex p))
      (fun j => paddedContribution p (scaleEdgeIndex p j)))) (circles p)

def scaleEnergy (p : Data) : Poly (Fin (variableCount p)) :=
  paddedContribution p (scaleInitialIndex p) ++ (List.ofFn (fun j => paddedContribution p (scaleEdgeIndex p j))).flatten
def circleEnergy (p : Data) : Poly (Fin (variableCount p)) := (List.ofFn (circles p)).flatten
def errorEnergy (p : Data) : Poly (Fin (variableCount p)) :=
  errorContribution p 0 ++ (List.ofFn (fun j : Fin (thresholdCount p) => errorContribution p j.succ)).flatten

theorem original_contribution (p : Data) (j : OriginalIndices p) :
    paddedContribution p (originalIndex p j) = FiniteRowSquare.contribution p j := by
  rw [padded_literal, ← FiniteRowSquare.contribution_literal]

theorem padded_family (p : Data) : paddedContribution p = paddedParts p := by
  unfold paddedParts
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro a
    erw [Fin.append_left]
    refine Fin.addCases ?_ ?_ a
    · intro j
      erw [Fin.append_left]
      have he : ((j.castAdd (1 + scaleCount p)).castAdd (scaleCoordinateCount p)) = originalIndex p j := by
        apply Fin.ext
        rw [original_index_val]
        rfl
      erw [he, original_contribution]
    · intro a
      erw [Fin.append_right]
      refine Fin.addCases ?_ ?_ a
      · intro u
        erw [Fin.append_left]
        congr 1
        apply Fin.ext
        rw [scale_initial_val]
        have hu : u.val = 0 := by omega
        change p.rows.length + u.val = p.rows.length
        omega
      · intro j
        erw [Fin.append_right]
        congr 1
  · intro j
    erw [Fin.append_right]
    unfold circles
    congr 1
    apply Fin.ext
    rw [circle_val, Equiv.apply_symm_apply]
    rfl

theorem padded_order (p : Data) : (List.ofFn (paddedContribution p)).flatten =
    FiniteRowEnergyLoop.energy p ++ scaleEnergy p ++ circleEnergy p := by
  rw [padded_family]
  unfold paddedParts
  erw [ofFn_append, ofFn_append, ofFn_append, ofFn_single]
  simp only [List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, FiniteRowEnergyLoop.energy, scaleEnergy, circleEnergy, List.append_assoc]

private theorem flatten_ofFn_succ {V : Type} (k : ℕ) (q : Fin (k + 1) → Poly V) :
    (List.ofFn q).flatten = q 0 ++ (List.ofFn (fun j => q j.succ)).flatten := by
  rw [List.ofFn_succ]
  rfl

theorem error_order (p : Data) : (List.ofFn (errorContribution p)).flatten = errorEnergy p :=
  flatten_ofFn_succ (thresholdCount p) (errorContribution p)

theorem padded_energy_literal (p : Data) : relabel (variableEnumeration p)
    (neg (scale 256 (relabel Sum.inl (SparseStrictPolynomial.energy (energyFamily p))))) =
      (List.ofFn (paddedContribution p)).flatten := by
  let F : Poly (PaddedCoordinates p) → Poly (Fin (variableCount p)) :=
    fun q => relabel (variableEnumeration p) (neg (scale 256 (relabel Sum.inl q)))
  have hf := map_sumFamily F rfl (by intro a b; simp only [F, neg, scale, relabel, List.map_append])
    (fun j => square (energyFamily p j))
  change F (SparseStrictPolynomial.sumFamily (fun j => square (energyFamily p j))) = _
  have he : (fun j => F (square (energyFamily p j))) = paddedContribution p := by
    funext j
    exact (padded_literal p j).symm
  exact hf.trans (congrArg (fun q : Fin (paddedEquationCount p) → Poly (Fin (variableCount p)) => (List.ofFn q).flatten) he)

theorem error_energy_literal (p : Data) : relabel (variableEnumeration p)
    (neg (scale 400 (relabel Sum.inr (SparseStrictPolynomial.error (thresholdCount p))))) =
      (List.ofFn (errorContribution p)).flatten := by
  let F : Poly (Fin (thresholdCount p + 1)) → Poly (Fin (variableCount p)) :=
    fun q => relabel (variableEnumeration p) (neg (scale 400 (relabel Sum.inr q)))
  have hf := map_sumFamily F rfl (by intro a b; simp only [F, neg, scale, relabel, List.map_append])
    (fun j => square (SparseStrictPolynomial.edge (thresholdCount p) j))
  change F (SparseStrictPolynomial.sumFamily (fun j => square (SparseStrictPolynomial.edge (thresholdCount p) j))) = _
  have he : (fun j => F (square (SparseStrictPolynomial.edge (thresholdCount p) j))) = errorContribution p := by
    funext j
    exact (error_literal p j).symm
  exact hf.trans (congrArg (fun q : Fin (thresholdCount p + 1) → Poly (Fin (variableCount p)) => (List.ofFn q).flatten) he)

private theorem relabel_sub_sub {V W : Type} (f : V → W) (a b c : Poly V) :
    relabel f (sub (sub a b) c) = relabel f a ++ relabel f (neg b) ++ relabel f (neg c) := by
  simp only [sub, add, neg, relabel, List.map_append]

private theorem bounded_relabel {V W : Type} {n : ℕ} (q : Fin n → Poly V) (k : ℕ)
    (f : V ⊕ Fin (k + 1) → W) : relabel f (SparseStrictPolynomial.bounded q k) =
      relabel f (scale 256 (square (atom (.inr (Fin.last k))))) ++
      relabel f (neg (scale 256 (relabel Sum.inl (SparseStrictPolynomial.energy q)))) ++
      relabel f (neg (scale 400 (relabel Sum.inr (SparseStrictPolynomial.error k)))) :=
  relabel_sub_sub f _ _ _

private theorem allReal_relabel {V W : Type} {n : ℕ} (q : Fin n → Poly V) (k : ℕ)
    (f : V ⊕ Fin (k + 1) → W) : relabel f (SparseStrictPolynomial.allReal q k) =
      relabel f (scale 256
        (product (square (atom (Sum.inr (Fin.last k))))
          (sub (constant 1) (square (atom (Sum.inr (Fin.last k))))))) ++
      relabel f (neg (scale 256 (relabel Sum.inl (SparseStrictPolynomial.energy q)))) ++
      relabel f (neg (scale 400 (relabel Sum.inr (SparseStrictPolynomial.error k)))) :=
  relabel_sub_sub f _ _ _

theorem bounded_data (p : Data) : bounded p =
    boxedLead p ++ FiniteRowEnergyLoop.energy p ++ scaleEnergy p ++ circleEnergy p ++ errorEnergy p := by
  unfold bounded boundedUnnumbered
  rw [bounded_relabel, ← boxed_lead_literal, padded_energy_literal, error_energy_literal,
    padded_order, error_order]
  simp only [List.append_assoc]

theorem allReal_data (p : Data) : allReal p =
    unboxedLead p ++ FiniteRowEnergyLoop.energy p ++ scaleEnergy p ++ circleEnergy p ++ errorEnergy p := by
  unfold allReal allRealUnnumbered
  rw [allReal_relabel, ← unboxed_lead_literal, padded_energy_literal, error_energy_literal,
    padded_order, error_order]
  simp only [List.append_assoc]

theorem bounded_code (p : Data) : boundedCode p = SparseListCodec.unaryCode (variableCount p) ++
    (FiniteRowSquare.finiteEntries (boxedLead p) ++ FiniteRowSquare.finiteEntries (FiniteRowEnergyLoop.energy p) ++
      FiniteRowSquare.finiteEntries (scaleEnergy p) ++ FiniteRowSquare.finiteEntries (circleEnergy p) ++
      FiniteRowSquare.finiteEntries (errorEnergy p)) ++ [false] := by
  unfold boundedCode SparsePolynomialCodec.code boundedData
  rw [← FiniteRowSquare.finiteEntries_codec, bounded_data]
  simp only [FiniteRowEnergyLoop.finiteEntries_append, List.append_assoc]

theorem allReal_code (p : Data) : allRealCode p = SparseListCodec.unaryCode (variableCount p) ++
    (FiniteRowSquare.finiteEntries (unboxedLead p) ++ FiniteRowSquare.finiteEntries (FiniteRowEnergyLoop.energy p) ++
      FiniteRowSquare.finiteEntries (scaleEnergy p) ++ FiniteRowSquare.finiteEntries (circleEnergy p) ++
      FiniteRowSquare.finiteEntries (errorEnergy p)) ++ [false] := by
  unfold allRealCode SparsePolynomialCodec.code allRealData
  rw [← FiniteRowSquare.finiteEntries_codec, allReal_data]
  simp only [FiniteRowEnergyLoop.finiteEntries_append, List.append_assoc]

end JointThermoComplexity.Complexity.FiniteStrictSections

#print axioms JointThermoComplexity.Complexity.FiniteStrictSections.padded_order
#print axioms JointThermoComplexity.Complexity.FiniteStrictSections.bounded_data
#print axioms JointThermoComplexity.Complexity.FiniteStrictSections.allReal_data
#print axioms JointThermoComplexity.Complexity.FiniteStrictSections.bounded_code
#print axioms JointThermoComplexity.Complexity.FiniteStrictSections.allReal_code
