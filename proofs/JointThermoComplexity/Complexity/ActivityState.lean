module
public import proofs.JointThermoComplexity.Complexity.MonomialRestore

set_option autoImplicit false
@[expose] public section

/-! A source cursor and zero binary scratch suffice for activity-output loops, with all other data in a stable frame. -/

namespace JointThermoComplexity.Complexity.ActivityState
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts

def Ready (m idx : ℕ) (R : (Fin (m + 15) → Tape) → Prop) (work : Fin (m + 15) → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
  IsReg idx (work (species (m + 1))) ∧ R work

theorem replace (m idx : ℕ) (R S : (Fin (m + 15) → Tape) → Prop) (r : Fin (m + 15))
    (hsource : r ≠ species (m + 1)) (hzero : r ≠ scratch (m + 2))
    (work work' : Fin (m + 15) → Tape) (hw : ∀ j, j ≠ r → work' j = work j)
    (ht : Parked (work' r)) (hr : R work → S work') (h : Ready m idx R work) : Ready m idx S work' := by
  rcases h with ⟨hs, hz, hi, hR⟩
  exact ⟨MonomialRestore.safe_replace r work work' hw hs ht,
    by simpa only [hw _ hzero.symm] using hz,
    by simpa only [hw _ hsource.symm] using hi, hr hR⟩

end JointThermoComplexity.Complexity.ActivityState

#print axioms JointThermoComplexity.Complexity.ActivityState.replace
