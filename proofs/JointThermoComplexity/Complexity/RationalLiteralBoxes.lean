module
public import proofs.JointThermoComplexity.Complexity.RationalLiteralNetwork

set_option autoImplicit false
@[expose] public section

/-! Exact finite-box constraints and their source-coordinate interpretation. -/

namespace JointThermoComplexity.Complexity.RationalLiteralBoxes
open RationalLiteralNetwork
variable {e n m : ℕ}

def Internal (x : ℝ) : Prop := (1 / 4 : ℝ) ≤ x ∧ x ≤ 1 / 2
def External (x : ℝ) : Prop := (1 / 2 : ℝ) ≤ x ∧ x ≤ 1

def Bounds (boxed : Bool) (x : Species e n m → ℝ) : Prop :=
  if boxed then ∀ s : Species e n m, match s with
    | .inr (.inl _) => External (x s)
    | _ => Internal (x s)
  else True

theorem internal_contains (x : ℝ) : internalBox.Contains x ↔ Internal x := by
  simp only [NetworkData.ClosedBox.Contains, internalBox, Internal, Int.cast_one, Nat.cast_ofNat]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem external_contains (x : ℝ) : externalBox.Contains x ↔ External x := by
  simp only [NetworkData.ClosedBox.Contains, externalBox, External, Int.cast_one, Nat.cast_ofNat, Nat.cast_one]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem forall_species (P : Fin (speciesCount e n m) → Prop) :
    (∀ s, P s) ↔ ∀ s : Species e n m, P (speciesNumbering e n m s) := by
  constructor
  · intro h s
    exact h _
  · intro h s
    obtain ⟨s, rfl⟩ := (speciesNumbering e n m).surjective s
    exact h s

theorem boxes_iff (boxed : Bool) (z : Fin (speciesCount e n m) → ℝ) :
    (∀ s, match (boxes boxed s : Option NetworkData.ClosedBox) with
      | none => True | some box => box.Contains (z s)) ↔ Bounds boxed (z ∘ speciesNumbering e n m) := by
  rw [forall_species]
  cases boxed
  · simp only [boxes, Bounds, Bool.false_eq_true, ↓reduceIte, implies_true]
  · simp only [boxes, Bounds, ↓reduceIte, Equiv.symm_apply_apply]
    apply forall_congr'
    intro s
    rcases s with i | (a | j)
    · exact internal_contains _
    · exact external_contains _
    · exact internal_contains _

theorem right_private (j : Fin m) :
    (@Emitted.rightVertex (Fin e) n m ⟨j.val + 2, by omega⟩) = .inr (.inr j) := by
  let k : Fin (m + 2) := ⟨j.val + 2, by omega⟩
  change @Emitted.rightVertex (Fin e) n m k = _
  have h0 : k.val ≠ 0 := by change j.val + 2 ≠ 0; omega
  have h1 : k.val ≠ 1 := by change j.val + 2 ≠ 1; omega
  unfold Emitted.rightVertex
  rw [dite_eq_right h0, dite_eq_right h1]
  apply congrArg Sum.inr
  apply congrArg Sum.inr
  apply Fin.ext
  change j.val + 2 - 2 = j.val
  omega

theorem bounds_vertices (x : Species e n m → ℝ) :
    Bounds true x ↔
      (∀ i, Internal (x (Emitted.leftVertex i))) ∧
      (∀ i, Internal (x (Emitted.rightVertex i))) ∧
      (∀ a, External (x (Emitted.external a))) := by
  change (∀ s : Species e n m, match s with | .inr (.inl _) => External (x s) | _ => Internal (x s)) ↔ _
  constructor
  · intro h
    refine ⟨(fun i => h (.inl i)), ?_, (fun a => h (.inr (.inl a)))⟩
    intro i
    unfold Emitted.rightVertex
    split_ifs
    · exact h (.inl _)
    · exact h (.inl _)
    · exact h (.inr (.inr _))
  · rintro ⟨hl, hr, he⟩ s
    rcases s with i | (a | j)
    · exact hl i
    · exact he a
    · have h := hr (⟨j.val + 2, by omega⟩ : Fin (m + 2))
      rw [right_private] at h
      exact h

end JointThermoComplexity.Complexity.RationalLiteralBoxes

#print axioms JointThermoComplexity.Complexity.RationalLiteralBoxes.boxes_iff
#print axioms JointThermoComplexity.Complexity.RationalLiteralBoxes.bounds_vertices
