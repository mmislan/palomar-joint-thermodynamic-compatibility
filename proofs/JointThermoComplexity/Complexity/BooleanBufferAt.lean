module
public import proofs.JointThermoComplexity.Complexity.BooleanWordCopy
public import proofs.JointThermoComplexity.Complexity.LiteralBufferAt

set_option autoImplicit false
@[expose] public section

/-! Copy an actual fixed-count Boolean vector into a selected work buffer, preserving formula output. -/

namespace JointThermoComplexity.Complexity.BooleanBufferAt
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def fuel (e : Fin (w + 1) ≃ Fin (w + 1)) (r : Fin w) : Fin (w + 1) := e r.castSucc

def machine (e : Fin (w + 1) ≃ Fin (w + 1)) (r : Fin w) : TM (w + 1) :=
  LiteralBufferAt.machine e (BooleanWordCopy.machine r)

theorem fuel_ne_destination (e : Fin (w + 1) ≃ Fin (w + 1)) (r : Fin w) :
    fuel e r ≠ CountSumAt.destination e := by
  intro he
  have hv := congrArg Fin.val (e.injective he)
  change r.val = w at hv
  have hr := r.isLt
  omega

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (r : Fin w)
    (bits before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → R work → R work') :
    (machine e r).HoareTime
      (fun inp work out => Cursor before (bits ++ tail) emitted inp work out ∧
        (work (CountSumAt.destination e)).HasBinaryPrefix [] ∧ (work (CountSumAt.destination e)).cells 0 = Γ.start ∧
        IsReg bits.length (work (fuel e r)) ∧ R work)
      (fun inp work out => Cursor (before ++ bits) tail emitted inp work out ∧
        (work (CountSumAt.destination e)).HasBinaryPrefix bits ∧ (work (CountSumAt.destination e)).cells 0 = Γ.start ∧
        IsReg bits.length (work (fuel e r)) ∧ R work) (4 * bits.length + 2) := by
  rintro inp work out ⟨hc, hp, hz, hf, hr⟩
  let original : Fin w → Tape := fun j => work (e j.castSucc)
  have hcopy := BooleanWordCopy.hoareTime r bits before tail [] (fun old => old = original)
  have hbase := LiteralBuffer.route_hoareTime (BooleanWordCopy.machine r) bits before tail emitted
    (fun old => IsReg bits.length (old r) ∧ old = original) (4 * bits.length + 2)
    (hcopy.consequence (fun _ _ _ h => h) (fun _ _ _ h => by simpa only [List.nil_append] using h) le_rfl)
  have hroute := WorkPermutation.hoareTime e (BooleanWordCopy.machine r).retargetOutput _ _ (4 * bits.length + 2) hbase
  have hpull : Cursor before (bits ++ tail) emitted inp (fun j => work (e j)) out :=
    ⟨hc.cells, hc.head, (fun j => hc.works (e j)), hc.tapePrefix, hc.zero⟩
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdp, hdz, hdf, hdold⟩ :=
    hroute inp work out ⟨hpull, hp, hz, hf, rfl⟩
  have hdCur : Cursor (before ++ bits) tail emitted d.input d.work d.output :=
    ⟨hdc.cells, hdc.head, (fun j => by simpa only [e.apply_symm_apply] using hdc.works (e.symm j)), hdc.tapePrefix, hdc.zero⟩
  have hother : ∀ j, j ≠ CountSumAt.destination e → d.work j = work j := by
    intro j hj
    obtain ⟨k, hk⟩ := CountSumAt.preimage e j hj
    have h := congrArg (fun f : Fin w → Tape => f k) hdold
    change d.work (e k.castSucc) = work (e k.castSucc) at h
    simpa only [hk] using h
  exact ⟨d, t, ht, hreach, hhalt, hdCur, hdp, hdz, hdf, hR work d.work hother hr⟩

end JointThermoComplexity.Complexity.BooleanBufferAt

#print axioms JointThermoComplexity.Complexity.BooleanBufferAt.fuel_ne_destination
#print axioms JointThermoComplexity.Complexity.BooleanBufferAt.hoareTime
