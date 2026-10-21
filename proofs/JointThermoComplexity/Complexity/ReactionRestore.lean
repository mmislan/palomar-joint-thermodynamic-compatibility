module
public import proofs.JointThermoComplexity.Complexity.NetworkEmitReady
public import proofs.JointThermoComplexity.Complexity.ReactionFuel
public import proofs.JointThermoComplexity.Complexity.MonomialRestore

set_option autoImplicit false
@[expose] public section

/-! Move only the outer fuel head between its physical and logical views. -/

namespace JointThermoComplexity.Complexity.ReactionRestore
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady ReactionPorts NetworkEmitReady ReactionFuel

theorem ready_replace (m L offset size n : ℕ)
    (R S : (Fin (m + 15) → Tape) → Prop) (r : Fin (m + 15)) (sep : Separate m r)
    (work work' : Fin (m + 15) → Tape) (hw : ∀ j, j ≠ r → work' j = work j)
    (ht : Parked (work' r)) (hr : R work → S work') (h : Ready m L offset size n R work) :
    Ready m L offset size n S work' := by
  rcases h with ⟨hs, hz, hn, ⟨a, p, ha, hp, har, hpr⟩,
    ⟨old, hold, ho⟩, ⟨keep, hkeep, hk⟩, ⟨idx, hidx, hi⟩, hf, hR⟩
  refine ⟨MonomialRestore.safe_replace r work work' hw hs ht, ?_, ?_, ⟨a, p, ha, hp, ?_, ?_⟩,
    ⟨old, hold, ?_⟩, ⟨keep, hkeep, ?_⟩, ⟨idx, hidx, ?_⟩, ?_, hr hR⟩
  · simpa only [hw _ sep.scratch.symm] using hz
  · simpa only [hw _ sep.next.symm] using hn
  · simpa only [hw _ sep.accumulator.symm] using har
  · simpa only [hw _ sep.power.symm] using hpr
  · simpa only [hw _ sep.previous.symm] using ho
  · simpa only [hw _ sep.saved.symm] using hk
  · simpa only [hw _ sep.species.symm] using hi
  · simpa only [hw _ sep.speciesFuel.symm] using hf

end JointThermoComplexity.Complexity.ReactionRestore

#print axioms JointThermoComplexity.Complexity.ReactionRestore.ready_replace
