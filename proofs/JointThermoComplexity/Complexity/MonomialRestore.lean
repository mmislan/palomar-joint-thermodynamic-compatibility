module
public import proofs.JointThermoComplexity.Complexity.MonomialReady
public import proofs.JointThermoComplexity.Complexity.MonomialFuel
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! Transfer the monomial invariant between the actual fuel head and its restored cell-one view. -/

namespace JointThermoComplexity.Complexity.MonomialRestore
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady MonomialFuel

variable {m n : ℕ}

theorem safe_replace (r : Fin (m + 14)) (work work' : Fin (m + 14) → Tape)
    (hw : ∀ j, j ≠ r → work' j = work j) (hs : ∀ j, Parked (work j)) (ht : Parked (work' r)) :
    ∀ j, Parked (work' j) := by
  intro j
  by_cases hj : j = r
  · subst j; exact ht
  · rw [hw j hj]; exact hs j

theorem cursor_replace {before input emitted : List Bool} {inp out : Tape}
    (r : Fin (m + 14)) (work work' : Fin (m + 14) → Tape)
    (hw : ∀ j, j ≠ r → work' j = work j) (ht : Parked (work' r))
    (hc : Cursor before input emitted inp work out) : Cursor before input emitted inp work' out := by
  refine ⟨hc.cells, hc.head, ?_, hc.tapePrefix, hc.zero⟩
  intro j
  by_cases hj : j = r
  · subst j; exact ⟨ht.read_ne_start, ht.1⟩
  · rw [hw j hj]; exact hc.works j

theorem ready_replace (L offset idx : ℕ) (s : MonomialCircuit.State n)
    (R S : (Fin (m + 14) → Tape) → Prop) (r : Fin (m + 14)) (sep : Separate m r)
    (work work' : Fin (m + 14) → Tape) (hw : ∀ j, j ≠ r → work' j = work j)
    (ht : Parked (work' r)) (hr : R work → S work') (h : Ready m L offset s idx R work) :
    Ready m L offset s idx S work' := by
  rcases h with ⟨hs, hi, hz, hn, hp, ⟨a, p, ha, hb, har, hpr⟩, hR⟩
  exact ⟨safe_replace r work work' hw hs ht,
    by simpa only [hw _ sep.species.symm] using hi,
    by simpa only [hw _ sep.scratch.symm] using hz,
    by simpa only [hw _ sep.next.symm] using hn,
    by simpa only [hw _ sep.previous.symm] using hp,
    ⟨a, p, ha, hb, by simpa only [hw _ sep.accumulator.symm] using har,
      by simpa only [hw _ sep.power.symm] using hpr⟩, hr hR⟩

theorem current_fuel_parked (r : Fin (m + 14)) (v head : ℕ) (work : Fin (m + 14) → Tape)
    (hh : 1 ≤ head) (hf : work r = ⟨head, regCells v⟩) : Parked (work r) := by
  rw [hf]
  exact ⟨hh, fun j hj => regCells_ne_start hj⟩

end JointThermoComplexity.Complexity.MonomialRestore

#print axioms JointThermoComplexity.Complexity.MonomialRestore.ready_replace
