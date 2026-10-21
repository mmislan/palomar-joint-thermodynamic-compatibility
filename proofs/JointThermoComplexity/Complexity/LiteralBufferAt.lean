module
public import proofs.JointThermoComplexity.Complexity.LiteralBuffer
public import proofs.JointThermoComplexity.Complexity.CountSumAt

set_option autoImplicit false
@[expose] public section

/-! Place exact binary-field buffering at any fixed work-tape permutation. -/

namespace JointThermoComplexity.Complexity.LiteralBufferAt
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (e : Fin (w + 1) ≃ Fin (w + 1)) (tm : TM w) : TM (w + 1) :=
  WorkPermutation.machine e tm.retargetOutput

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (tm : TM w)
    (word before tail emitted : List Bool) (bound : ℕ)
    (hcopy : ∀ C : (Fin w → Tape) → Prop, tm.HoareTime
      (fun inp work out => Cursor before (word ++ tail) [] inp work out ∧ C work)
      (fun inp work out => Cursor (before ++ word) tail word inp work out ∧ C work) bound)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → R work → R work') :
    (machine e tm).HoareTime
      (fun inp work out => Cursor before (word ++ tail) emitted inp work out ∧
        (work (CountSumAt.destination e)).HasBinaryPrefix [] ∧
        (work (CountSumAt.destination e)).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor (before ++ word) tail emitted inp work out ∧
        (work (CountSumAt.destination e)).HasBinaryPrefix word ∧
        (work (CountSumAt.destination e)).cells 0 = Γ.start ∧ R work) bound := by
  rintro inp work out ⟨hc, hp, hz, hr⟩
  let original : Fin w → Tape := fun j => work (e j.castSucc)
  have hbase := LiteralBuffer.route_hoareTime tm word before tail emitted (fun old => old = original) bound
    (hcopy (fun old => old = original))
  have hroute := WorkPermutation.hoareTime e tm.retargetOutput _ _ bound hbase
  have hpull : Cursor before (word ++ tail) emitted inp (fun j => work (e j)) out :=
    ⟨hc.cells, hc.head, (fun j => hc.works (e j)), hc.tapePrefix, hc.zero⟩
  obtain ⟨d, t, ht, hreach, hhalt, hdcur, hdp, hdz, hdold⟩ :=
    hroute inp work out ⟨hpull, hp, hz, rfl⟩
  have hdCur : Cursor (before ++ word) tail emitted d.input d.work d.output :=
    ⟨hdcur.cells, hdcur.head, (fun j => by simpa only [e.apply_symm_apply] using hdcur.works (e.symm j)),
      hdcur.tapePrefix, hdcur.zero⟩
  have hother : ∀ j, j ≠ CountSumAt.destination e → d.work j = work j := by
    intro j hj
    obtain ⟨k, hk⟩ := CountSumAt.preimage e j hj
    have h := congrArg (fun f : Fin w → Tape => f k) hdold
    change d.work (e k.castSucc) = work (e k.castSucc) at h
    simpa only [hk] using h
  exact ⟨d, t, ht, hreach, hhalt, hdCur, hdp, hdz, hR work d.work hother hr⟩

end JointThermoComplexity.Complexity.LiteralBufferAt

#print axioms JointThermoComplexity.Complexity.LiteralBufferAt.hoareTime
