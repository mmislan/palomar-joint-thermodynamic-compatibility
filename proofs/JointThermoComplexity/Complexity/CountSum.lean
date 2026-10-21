module
public import proofs.JointThermoComplexity.Complexity.CountAppend
public import proofs.JointThermoComplexity.Complexity.CountRewind

set_option autoImplicit false
@[expose] public section

/-! Add bounded address counts on a fresh work register; both sources are restored. -/

namespace JointThermoComplexity.Complexity.CountSum
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountAppend

variable {w : ℕ}

def accumulate (a b : Fin w) : TM (w + 1) := seqTM (CountAppend.machine a) (CountAppend.machine b)
def machine (a b : Fin w) : TM (w + 1) := seqTM (accumulate a b) (rewindWorkTM destination)

theorem accumulate_hoareTime (a b : Fin w) (va vb d : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (accumulate a b).HoareTime
      (fun inp work out => IsReg va (work a.castSucc) ∧ IsReg vb (work b.castSucc) ∧
        Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work destination).HasBinaryPrefix (List.replicate d true) ∧ (work destination).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => IsReg va (work a.castSucc) ∧ IsReg vb (work b.castSucc) ∧
        Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work destination).HasBinaryPrefix (List.replicate (d + va + vb) true) ∧
        (work destination).cells 0 = Γ.start ∧ R (oldWork work)) (4 * (va + vb) + 5) := by
  rintro inp work out ⟨ha, hb, hc, hs, hp, hz, hr⟩
  let RP : (Fin w → Tape) → Prop := fun work => IsReg va (work a) ∧ IsReg vb (work b) ∧ R work
  obtain ⟨c, tc, htc, hcreach, hchalt, _hca, hccur, hcsafe, hcp, hcz, hcR⟩ :=
    CountAppend.hoareTime a va d before input emitted RP inp work out ⟨ha, hc, hs, hp, hz, ⟨ha, hb, hr⟩⟩
  obtain ⟨e, te, hte, hereach, hehalt, _heb, hecur, hesafe, hep, hez, heR⟩ :=
    CountAppend.hoareTime b vb (d + va) before input emitted RP c.input c.work c.output
      ⟨hcR.2.1, hccur, hcsafe, hcp, hcz, hcR⟩
  obtain ⟨hi, hw, ho⟩ := hccur.phase
  have hrb : (CountAppend.machine b).reachesIn te
      ⟨(CountAppend.machine b).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ e := by
    simpa only [hi, hw, ho] using hereach
  have hreach := seqTM_reachesIn_of_reachesIn (CountAppend.machine a) (CountAppend.machine b) hcreach hchalt hrb
  exact ⟨phase2Wrap (CountAppend.machine a) (CountAppend.machine b) e, tc + 1 + te,
    by omega, hreach, (phase2Wrap_halted_iff _ _ e).mpr hehalt, heR.1, heR.2.1, hecur, hesafe, hep, hez, heR.2.2⟩

theorem hoareTime (a b : Fin w) (va vb : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine a b).HoareTime
      (fun inp work out => IsReg va (work a.castSucc) ∧ IsReg vb (work b.castSucc) ∧ IsReg 0 (work destination) ∧
        Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R (oldWork work))
      (fun inp work out => IsReg va (work a.castSucc) ∧ IsReg vb (work b.castSucc) ∧ IsReg (va + vb) (work destination) ∧
        Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R (oldWork work)) (5 * (va + vb) + 9) := by
  rintro inp work out ⟨ha, hb, hz, hc, hs, hr⟩
  obtain ⟨c, tc, htc, hcreach, hchalt, hca, hcb, hccur, hcsafe, hcp, hcz, hcR⟩ :=
    accumulate_hoareTime a b va vb 0 before input emitted R inp work out
      ⟨ha, hb, hc, hs, CountTape.empty_prefix_of_zero hz, hz.cell0, hr⟩
  let RP : (Fin (w + 1) → Tape) → Prop := fun work =>
    IsReg va (work a.castSucc) ∧ IsReg vb (work b.castSucc) ∧ R (oldWork work)
  have hRP : ∀ work work', (∀ j, j ≠ destination → work' j = work j) → RP work → RP work' := by
    intro work work' hw h
    have hold : oldWork work' = oldWork work := by
      funext j
      apply hw j.castSucc
      intro he
      have hv := congrArg Fin.val he
      change j.val = w at hv
      omega
    change IsReg va (oldWork work' a) ∧ IsReg vb (oldWork work' b) ∧ R (oldWork work')
    rw [hold]
    exact h
  obtain ⟨e, te, hte, hereach, hehalt, heReg, hecur, hesafe, heR⟩ :=
    CountRewind.hoareTime destination (va + vb) before input emitted RP hRP c.input c.work c.output
      ⟨hccur, hcsafe, by simpa only [Nat.zero_add] using hcp, hcz, ⟨hca, hcb, hcR⟩⟩
  obtain ⟨hi, hw, ho⟩ := hccur.phase
  have hrw : (rewindWorkTM destination).reachesIn te
      ⟨(rewindWorkTM destination).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ e := by
    simpa only [hi, hw, ho] using hereach
  have hreach := seqTM_reachesIn_of_reachesIn (accumulate a b) (rewindWorkTM destination) hcreach hchalt hrw
  exact ⟨phase2Wrap (accumulate a b) (rewindWorkTM destination) e, tc + 1 + te, by omega,
    hreach, (phase2Wrap_halted_iff _ _ e).mpr hehalt, heR.1, heR.2.1, heReg, hecur, hesafe, heR.2.2⟩

end JointThermoComplexity.Complexity.CountSum

#print axioms JointThermoComplexity.Complexity.CountSum.hoareTime
