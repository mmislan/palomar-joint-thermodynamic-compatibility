module
public import proofs.JointThermoComplexity.Complexity.CountAppend

set_option autoImplicit false
@[expose] public section

/-!
# Fixed offsets on a unary gate-count accumulator

The offset is a compile-time constant (three per exponent or six per reaction).
Runtime numeric exponent and coefficient values are not machine parameters.
-/

namespace JointThermoComplexity.Complexity.CountOffset
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountAppend

variable {w : ℕ}

theorem cast_ne_destination (j : Fin w) : j.castSucc ≠ (destination : Fin (w + 1)) := by
  intro h
  have hv := congrArg Fin.val h
  change j.val = w at hv
  omega

theorem oldWork_eq {work work' : Fin (w + 1) → Tape}
    (h : ∀ j, j ≠ destination → work' j = work j) : oldWork work' = oldWork work := by
  funext j
  exact h j.castSucc (cast_ne_destination j)

def machine (offset : ℕ) : TM (w + 1) := (emitBitsTM (n := w) (List.replicate offset true)).retargetOutput

theorem hoareTime (offset count : ℕ) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w) offset).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work destination).HasBinaryPrefix (List.replicate count true) ∧ (work destination).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work destination).HasBinaryPrefix (List.replicate (count + offset) true) ∧
        (work destination).cells 0 = Γ.start ∧ R (oldWork work)) offset := by
  rintro inp work out ⟨hc, hs, hp, hz, hr⟩
  let S : Tape → Prop := fun out => out.HasBinaryPrefix emitted ∧ out.cells 0 = Γ.start
  have hemit := FixedOutput.hoareTime (List.replicate offset true) before input (List.replicate count true) R
  have hroute := OutputRoute.hoareTime (emitBitsTM (List.replicate offset true)) _ _ _ S hemit
  have hvcur : Cursor before input (List.replicate count true) inp (oldWork work) (work destination) :=
    ⟨hc.cells, hc.head, fun j => hc.works j.castSucc, hp, hz⟩
  obtain ⟨e, t, ht, hreach, hhalt, _ho, hout, heCur, heSafe, heR⟩ :=
    hroute inp work out ⟨hc.output_read, ⟨hc.tapePrefix, hc.zero⟩, hvcur, (fun j => hs j.castSucc), hr⟩
  have hePrefix : (e.work destination).HasBinaryPrefix (List.replicate (count + offset) true) := by
    simpa only [destination, ← List.replicate_add] using heCur.tapePrefix
  have heZero : (e.work destination).cells 0 = Γ.start := heCur.zero
  have heAll : ∀ j, Parked (e.work j) := by
    intro j
    by_cases hj : j.val < w
    · let k : Fin w := ⟨j.val, hj⟩
      have he : j = k.castSucc := rfl
      rw [he]
      exact heSafe k
    · have he : j = Fin.last w := by apply Fin.ext; simp only [Fin.val_last]; omega
      rw [he]
      exact ((FixedOutput.outAcc_iff _ _).mpr ⟨hePrefix, heZero⟩).parked
  exact ⟨e, t, by simpa only [List.length_replicate] using ht, hreach, hhalt,
    ⟨heCur.cells, heCur.head, fun j => ⟨(heAll j).read_ne_start, (heAll j).1⟩, hout.1, hout.2⟩,
    heAll, hePrefix, heZero, heR⟩

end JointThermoComplexity.Complexity.CountOffset

#print axioms JointThermoComplexity.Complexity.CountOffset.hoareTime
