module
public import proofs.JointThermoComplexity.Complexity.RationalLiteralProduction
public import proofs.JointThermoComplexity.Complexity.RationalLiteralBoxes
public import proofs.JointThermoComplexity.FamilyDock

set_option autoImplicit false
@[expose] public section

/-! Full positive shared-state feasibility transport, including both supplied
cores and every prescribed closed box. -/

namespace JointThermoComplexity.Complexity.RationalLiteralFeasibility
open RationalBranchData RationalLiteralNetwork RationalLiteralProduction RationalLiteralBoxes
variable {e n m : ℕ}

def SourceConstraints (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m)
    (x : Species e n m → ℝ) : Prop :=
  (∀ s, 0 < x s) ∧ Bounds boxed x ∧
  (∀ r, 0 < (Emitted.source L.toBranch R.toBranch).current x r) ∧
  (Emitted.leftCycle L.toBranch R.toBranch).motif.Productive ((Emitted.source L.toBranch R.toBranch).current x) ∧
  (Emitted.rightCycle L.toBranch R.toBranch).motif.Productive ((Emitted.source L.toBranch R.toBranch).current x)

theorem constraints_iff (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m)
    (z : Fin (speciesCount e n m) → ℝ) :
    (network boxed L R).Constraints z (fun r => ((network boxed L R).reactions r).current z) ↔
      SourceConstraints boxed L R (z ∘ speciesNumbering e n m) := by
  unfold SourceConstraints
  rw [LiteralBridge.constraints_iff]
  simp only [LiteralBridge.orientation, network_forward, ↓reduceIte, Int.cast_one, one_mul]
  rw [positive_on_motifs_iff boxed L R, currents_positive_iff boxed L R z,
    productive_pair_iff boxed L R, current_pull boxed L R z,
    positive_states_iff (e := e) (n := n) (m := m) z]
  constructor
  · rintro ⟨hz, hb, hj, hl, hr⟩
    exact ⟨hz, (boxes_iff (e := e) (n := n) (m := m) boxed z).mp hb, hj, hl, hr⟩
  · rintro ⟨hz, hb, hj, hl, hr⟩
    exact ⟨hz, (boxes_iff (e := e) (n := n) (m := m) boxed z).mpr hb, hj, hl, hr⟩

theorem feasible_source_iff (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) :
    (network boxed L R).Feasible ↔ ∃ x : Species e n m → ℝ, SourceConstraints boxed L R x := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z ∘ speciesNumbering e n m, (constraints_iff boxed L R z).mp hz⟩
  · rintro ⟨x, hx⟩
    refine ⟨x ∘ (speciesNumbering e n m).symm, (constraints_iff boxed L R _).mpr ?_⟩
    have he : (x ∘ (speciesNumbering e n m).symm) ∘ speciesNumbering e n m = x := by
      funext s
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [he]
    exact hx

theorem unboxed_iff (L : Data (Fin e) n) (R : Data (Fin e) m) :
    (network false L R).Feasible ↔ (Emitted.family L.toBranch R.toBranch).MultiCAC := by
  rw [feasible_source_iff, Emitted.family_multicac_iff]
  constructor
  · rintro ⟨x, hpos, _hb, hcurr, hl, hr⟩
    exact ⟨fun a => x (Emitted.external a), (fun a => hpos _), x, hpos, (fun _ => rfl), hcurr, hl, hr⟩
  · rintro ⟨u, _hu, x, hpos, _he, hcurr, hl, hr⟩
    exact ⟨x, hpos, True.intro, hcurr, hl, hr⟩

theorem boxed_iff (L : Data (Fin e) n) (R : Data (Fin e) m) :
    (network true L R).Feasible ↔ ∃ u : Fin e → ℝ,
      (∀ a, (1 / 2 : ℝ) ≤ u a ∧ u a ≤ 1) ∧ Emitted.BoxCompatible L.toBranch R.toBranch u := by
  rw [feasible_source_iff]
  constructor
  · rintro ⟨x, hpos, hb, hcurr, hl, hr⟩
    obtain ⟨hbl, hbr, hbe⟩ := (bounds_vertices x).mp hb
    exact ⟨fun a => x (Emitted.external a), hbe, x, hpos, (fun _ => rfl), hcurr, hl, hr, hbl, hbr⟩
  · rintro ⟨u, hu, x, hpos, he, hcurr, hl, hr, hbl, hbr⟩
    refine ⟨x, hpos, (bounds_vertices x).mpr ⟨hbl, hbr, ?_⟩, hcurr, hl, hr⟩
    intro a
    change (1 / 2 : ℝ) ≤ x (Emitted.external a) ∧ x (Emitted.external a) ≤ 1
    rw [he a]
    exact hu a

end JointThermoComplexity.Complexity.RationalLiteralFeasibility

#print axioms JointThermoComplexity.Complexity.RationalLiteralFeasibility.constraints_iff
#print axioms JointThermoComplexity.Complexity.RationalLiteralFeasibility.feasible_source_iff
#print axioms JointThermoComplexity.Complexity.RationalLiteralFeasibility.unboxed_iff
#print axioms JointThermoComplexity.Complexity.RationalLiteralFeasibility.boxed_iff
