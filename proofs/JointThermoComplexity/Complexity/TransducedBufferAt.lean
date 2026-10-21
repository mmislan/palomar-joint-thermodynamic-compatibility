module
public import proofs.JointThermoComplexity.Complexity.LiteralBufferAt

set_option autoImplicit false
@[expose] public section

/-! Route a field transducer's distinct consumed word and output payload to one fixed physical work buffer. -/

namespace JointThermoComplexity.Complexity.TransducedBufferAt
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (e : Fin (w + 1) ≃ Fin (w + 1)) (tm : TM w) : TM (w + 1) :=
  WorkPermutation.machine e tm.retargetOutput

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (tm : TM w)
    (word bits before tail emitted : List Bool) (bound : ℕ)
    (hcopy : ∀ C : (Fin w → Tape) → Prop, tm.HoareTime
      (fun inp work out => Cursor before (word ++ tail) [] inp work out ∧ C work)
      (fun inp work out => Cursor (before ++ word) tail bits inp work out ∧ C work) bound)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → R work → R work') :
    (machine e tm).HoareTime
      (fun inp work out => Cursor before (word ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work (CountSumAt.destination e)).HasBinaryPrefix [] ∧ (work (CountSumAt.destination e)).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor (before ++ word) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work (CountSumAt.destination e)).HasBinaryPrefix bits ∧ (work (CountSumAt.destination e)).cells 0 = Γ.start ∧ R work) bound := by
  rintro inp work out ⟨hc, hs, hp, hz, hr⟩
  let original : Fin w → Tape := fun j => work (e j.castSucc)
  have hbase := OutputRoute.hoareTime tm _ _ bound (fun out' => out' = out) (hcopy (fun old => old = original))
  have hroute := WorkPermutation.hoareTime e tm.retargetOutput _ _ bound hbase
  obtain ⟨d, t, ht, hreach, hhalt, _, hdout, hdcur, hdold⟩ := hroute inp work out
    ⟨hc.output_read, rfl, ⟨hc.cells, hc.head, (fun j => hc.works (e j.castSucc)), hp, hz⟩, rfl⟩
  have hother : ∀ j, j ≠ CountSumAt.destination e → d.work j = work j := by
    intro j hj
    obtain ⟨k, hk⟩ := CountSumAt.preimage e j hj
    have h := congrArg (fun f : Fin w → Tape => f k) hdold
    change d.work (e k.castSucc) = work (e k.castSucc) at h
    simpa only [hk] using h
  have hbits : (d.work (CountSumAt.destination e)).HasBinaryPrefix bits := hdcur.tapePrefix
  have hsafe : ∀ j, Parked (d.work j) := by
    intro j
    by_cases hj : j = CountSumAt.destination e
    · subst j
      exact ⟨by rw [hbits.1]; omega, (show (d.work (CountSumAt.destination e)).HasBinaryContent bits from hbits.2).cells_ne_start⟩
    · rw [hother j hj]; exact hs j
  have hcur : Cursor (before ++ word) tail emitted d.input d.work d.output :=
    ⟨hdcur.cells, hdcur.head, fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩,
      by simpa only [hdout] using hc.tapePrefix, by simpa only [hdout] using hc.zero⟩
  exact ⟨d, t, ht, hreach, hhalt, hcur, hsafe, hbits, hdcur.zero, hR work d.work hother hr⟩

end JointThermoComplexity.Complexity.TransducedBufferAt

#print axioms JointThermoComplexity.Complexity.TransducedBufferAt.hoareTime
