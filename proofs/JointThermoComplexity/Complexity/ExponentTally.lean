module
public import proofs.JointThermoComplexity.Complexity.GateTally
public import proofs.JointThermoComplexity.Complexity.CountOffset

set_option autoImplicit false
@[expose] public section

/-! Count all gates contributed by one encoded monomial exponent field. -/

namespace JointThermoComplexity.Complexity.ExponentTally
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountAppend

variable {w : ℕ}

def fieldCost (exponent : ℕ) : ℕ := 3 + ExactGateCount.bitsCost exponent.bits
def machine : TM (w + 1) := seqTM (CountOffset.machine 3) (GateTally.machine destination)

theorem hoareTime (exponent count : ℕ) (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode exponent ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work destination).HasBinaryPrefix (List.replicate count true) ∧
        (work destination).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode exponent) tail emitted inp work out ∧
        (∀ j, Parked (work j)) ∧
        (work destination).HasBinaryPrefix (List.replicate (count + fieldCost exponent) true) ∧
        (work destination).cells 0 = Γ.start ∧ R (oldWork work)) ((BitCodec.naturalCode exponent).length + 4) := by
  rintro inp work out ⟨hc, hs, hp, hz, hr⟩
  obtain ⟨c, tc, htc, hcreach, hchalt, hccur, hcsafe, hcp, hcz, hcR⟩ :=
    CountOffset.hoareTime 3 count before (BitCodec.naturalCode exponent ++ tail) emitted R inp work out ⟨hc, hs, hp, hz, hr⟩
  let RN : (Fin (w + 1) → Tape) → Prop := fun work => R (oldWork work)
  have hRN : ∀ work work', (∀ j, j ≠ destination → work' j = work j) → RN work → RN work' := by
    intro work work' hw h
    change R (oldWork work')
    rw [CountOffset.oldWork_eq hw]
    exact h
  obtain ⟨e, te, hte, hereach, hehalt, hecur, hesafe, hep, hez, heR⟩ :=
    GateTally.natural_hoareTime destination exponent (count + 3) before tail emitted RN hRN
      c.input c.work c.output ⟨hccur, hcsafe, hcp, hcz, hcR⟩
  obtain ⟨hi, hw, ho⟩ := hccur.phase
  have hrr : (GateTally.machine destination).reachesIn te
      ⟨(GateTally.machine destination).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ e := by
    simpa only [hi, hw, ho] using hereach
  have hreach := seqTM_reachesIn_of_reachesIn (CountOffset.machine 3) (GateTally.machine destination) hcreach hchalt hrr
  exact ⟨phase2Wrap (CountOffset.machine 3) (GateTally.machine destination) e, tc + 1 + te, by omega,
    hreach, (phase2Wrap_halted_iff _ _ e).mpr hehalt, hecur, hesafe,
    by simpa only [phase2Wrap, fieldCost, Nat.add_assoc] using hep, hez, heR⟩

end JointThermoComplexity.Complexity.ExponentTally

#print axioms JointThermoComplexity.Complexity.ExponentTally.hoareTime
