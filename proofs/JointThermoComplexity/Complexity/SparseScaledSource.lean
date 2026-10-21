module
public import proofs.JointThermoComplexity.Complexity.SparseScaledSystem
public import proofs.JointThermoComplexity.Complexity.NumericSparseSource

set_option autoImplicit false
@[expose] public section

/-! # Executable numbered source system with a common positive scale

The chain length is an explicit natural parameter. Source equivalence holds
for every length; the separately proved quantitative schedule is needed to
obtain the bounded witness used by the circle-padded strict construction.
-/

namespace JointThermoComplexity.Complexity.SparseScaledSource
open RealSyntax SparseInteger SourceCoordinateEnumeration

abbrev OriginalIndices (s : Sentence) := Fin (NumericSparseSource.equations s).length
abbrev Coordinates (s : Sentence) (m : ℕ) := Fin (sourceCount s) ⊕ Fin (m + 1)
abbrev Indices (s : Sentence) (m : ℕ) := OriginalIndices s ⊕ (Unit ⊕ Fin m)

def original (s : Sentence) (j : OriginalIndices s) : Poly (Fin (sourceCount s)) :=
  (NumericSparseSource.equations s)[j.val]'j.isLt

def family (s : Sentence) (m : ℕ) : Indices s m → Poly (Coordinates s m) :=
  SparseScaledSystem.family (original s) m

theorem original_degree (s : Sentence) (j : OriginalIndices s) : (interpret (original s j)).totalDegree ≤ 2 :=
  NumericSparseSource.equation_degree s _ (List.getElem_mem j.isLt)

theorem original_holds_iff (s : Sentence) (x : Fin (sourceCount s) → ℝ) :
    (∀ j, (interpret (original s j)).eval₂ (Int.castRingHom ℝ) x = 0) ↔
      ∀ p ∈ NumericSparseSource.equations s, (interpret p).eval₂ (Int.castRingHom ℝ) x = 0 := by
  constructor
  · intro h
    exact List.forall_mem_iff_getElem.mpr (fun i hi => h ⟨i, hi⟩)
  · intro h j
    exact h _ (List.getElem_mem j.isLt)

theorem source_iff_scaled_root (s : Sentence) (m : ℕ) :
    s.Satisfiable ↔ ∃ v : Coordinates s m → ℝ,
      ∀ j, (interpret (family s m j)).eval₂ (Int.castRingHom ℝ) v = 0 := by
  change s.Satisfiable ↔ ∃ v, ∀ j,
    (interpret (SparseScaledSystem.family (original s) m j)).eval₂ (Int.castRingHom ℝ) v = 0
  rw [SparseScaledSystem.common_root_iff (original s) (original_degree s) m]
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := (NumericSparseSource.satisfiable_iff s).mp hs
    exact ⟨x, (original_holds_iff s x).mpr hx⟩
  · rintro ⟨x, hx⟩
    exact (NumericSparseSource.satisfiable_iff s).mpr ⟨x, (original_holds_iff s x).mp hx⟩

theorem interpret_family (s : Sentence) (m : ℕ) (j : Indices s m) :
    interpret (family s m j) = ScaledQuadraticSystem.family (fun j => interpret (original s j)) m j :=
  SparseScaledSystem.interpret_family (original s) m j

theorem family_raw_degree (s : Sentence) (m : ℕ) (j : Indices s m) : DegreeLE 2 (family s m j) :=
  SparseScaledSystem.family_degree (original s) m j

theorem coordinate_count (s : Sentence) (m : ℕ) :
    Fintype.card (Coordinates s m) ≤ 5 * s.code.length + m + 1 := by
  change Fintype.card (Fin (sourceCount s) ⊕ Fin (m + 1)) ≤ _
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have h := NumericSparseSource.coordinate_count s
  omega

theorem equation_count (s : Sentence) (m : ℕ) :
    Fintype.card (Indices s m) ≤ 4 * s.code.length + m + 2 := by
  change Fintype.card (Fin (NumericSparseSource.equations s).length ⊕ (Unit ⊕ Fin m)) ≤ _
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  have h := NumericSparseSource.equation_count s
  omega

end JointThermoComplexity.Complexity.SparseScaledSource

#print axioms JointThermoComplexity.Complexity.SparseScaledSource.family
#print axioms JointThermoComplexity.Complexity.SparseScaledSource.source_iff_scaled_root
#print axioms JointThermoComplexity.Complexity.SparseScaledSource.family_raw_degree
#print axioms JointThermoComplexity.Complexity.SparseScaledSource.coordinate_count
#print axioms JointThermoComplexity.Complexity.SparseScaledSource.equation_count
