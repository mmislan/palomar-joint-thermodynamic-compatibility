module
public import proofs.JointThermoComplexity.Complexity.CountSum
public import proofs.JointThermoComplexity.Complexity.WorkPermutation

set_option autoImplicit false
@[expose] public section

/-! Place bounded-count addition at any fixed register permutation, with a full physical frame. -/

namespace JointThermoComplexity.Complexity.CountSumAt
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def destination (e : Fin (w + 1) ≃ Fin (w + 1)) : Fin (w + 1) := e (Fin.last w)

def machine (e : Fin (w + 1) ≃ Fin (w + 1)) (a b : Fin w) : TM (w + 1) :=
  WorkPermutation.machine e (CountSum.machine a b)

theorem preimage (e : Fin (w + 1) ≃ Fin (w + 1)) (j : Fin (w + 1)) (hj : j ≠ destination e) :
    ∃ k : Fin w, e k.castSucc = j := by
  have hne : e.symm j ≠ Fin.last w := by
    intro he
    apply hj
    change j = e (Fin.last w)
    rw [← he, e.apply_symm_apply]
  have hv : (e.symm j).val < w := by
    by_contra h
    apply hne
    apply Fin.ext
    simp only [Fin.val_last]
    have hi := (e.symm j).isLt
    omega
  let k : Fin w := ⟨(e.symm j).val, hv⟩
  refine ⟨k, ?_⟩
  have hk : k.castSucc = e.symm j := rfl
  rw [hk, e.apply_symm_apply]

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (a b : Fin w) (va vb : ℕ)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ destination e → work' j = work j) → R work → R work') :
    (machine e a b).HoareTime
      (fun inp work out => IsReg va (work (e a.castSucc)) ∧ IsReg vb (work (e b.castSucc)) ∧
        IsReg 0 (work (destination e)) ∧ Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => IsReg va (work (e a.castSucc)) ∧ IsReg vb (work (e b.castSucc)) ∧
        IsReg (va + vb) (work (destination e)) ∧ Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (5 * (va + vb) + 9) := by
  rintro inp work out ⟨ha, hb, hz, hc, hs, hr⟩
  let original : Fin w → Tape := fun j => work (e j.castSucc)
  have hbase := CountSum.hoareTime a b va vb before input emitted (fun old => old = original)
  have hroute := WorkPermutation.hoareTime e (CountSum.machine a b) _ _ _ hbase
  have hpull : Cursor before input emitted inp (fun j => work (e j)) out :=
    ⟨hc.cells, hc.head, (fun j => hc.works (e j)), hc.tapePrefix, hc.zero⟩
  obtain ⟨d, t, ht, hreach, hhalt, hda, hdb, hdd, hdcur, hdsafe, hdold⟩ :=
    hroute inp work out ⟨ha, hb, hz, hpull, (fun j => hs (e j)), rfl⟩
  have hdCur : Cursor before input emitted d.input d.work d.output :=
    ⟨hdcur.cells, hdcur.head, (fun j => by simpa only [e.apply_symm_apply] using hdcur.works (e.symm j)),
      hdcur.tapePrefix, hdcur.zero⟩
  have hdSafe : ∀ j, Parked (d.work j) := fun j => by
    simpa only [e.apply_symm_apply] using hdsafe (e.symm j)
  have hother : ∀ j, j ≠ destination e → d.work j = work j := by
    intro j hj
    obtain ⟨k, hk⟩ := preimage e j hj
    have h := congrArg (fun f : Fin w → Tape => f k) hdold
    change d.work (e k.castSucc) = work (e k.castSucc) at h
    simpa only [hk] using h
  exact ⟨d, t, ht, hreach, hhalt, hda, hdb, hdd, hdCur, hdSafe, hR work d.work hother hr⟩

end JointThermoComplexity.Complexity.CountSumAt

#print axioms JointThermoComplexity.Complexity.CountSumAt.hoareTime
