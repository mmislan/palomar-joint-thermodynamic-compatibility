module
public import proofs.JointThermoComplexity.Complexity.CurrentReady
public import proofs.JointThermoComplexity.Complexity.MonomialRestore

set_option autoImplicit false
@[expose] public section

/-! Transfer only the outer fuel head around an exact current-record step. -/

namespace JointThermoComplexity.Complexity.CurrentRestore
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts CurrentReady

theorem ready_replace (m L count idx n : ℕ) (R S : (Fin (m + 15) → Tape) → Prop)
    (r : Fin (m + 15)) (sep : ReactionFuel.Separate m r) (hraw : r ≠ raw m)
    (work work' : Fin (m + 15) → Tape) (hw : ∀ j, j ≠ r → work' j = work j)
    (ht : Parked (work' r)) (hr : R work → S work') (h : Ready m L count idx n R work) :
    Ready m L count idx n S work' := by
  rcases h with ⟨hs, hz, hc, hi, ⟨old, hold, hp⟩, hf, hR⟩
  exact ⟨MonomialRestore.safe_replace r work work' hw hs ht,
    by simpa only [hw _ sep.scratch.symm] using hz,
    by simpa only [hw _ hraw.symm] using hc,
    by simpa only [hw _ sep.species.symm] using hi,
    ⟨old, hold, by simpa only [hw _ sep.previous.symm] using hp⟩,
    by simpa only [hw _ sep.speciesFuel.symm] using hf, hr hR⟩

end JointThermoComplexity.Complexity.CurrentRestore

#print axioms JointThermoComplexity.Complexity.CurrentRestore.ready_replace
