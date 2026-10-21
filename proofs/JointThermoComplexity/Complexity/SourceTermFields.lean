module
public import proofs.JointThermoComplexity.Complexity.SourceTermToken

set_option autoImplicit false
@[expose] public section

/-! Integer and constant verdict branches preserve the common source-token register state. -/

namespace JointThermoComplexity.Complexity.SourceTermFields
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
open BinaryDifferenceCursor SourceIndexField
variable {n : ℕ}

def Kept (L : ℕ) (left right : Fin (n + 1)) (arity : ℕ) (R : (Fin (n + 1) → Tape) → Prop)
    (work : Fin (n + 2) → Tape) : Prop := Reusable L (work left.castSucc) ∧
  (work right.castSucc).HasBinaryString arity.bits ∧ (work right.castSucc).cells 0 = Γ.start ∧
  R (fun j => work j.castSucc)

theorem kept_frame (L : ℕ) (left right : Fin (n + 1)) (sep : Separate left right (NaturalMachine.flagIndex n))
    (arity : ℕ) (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    ∀ work work', (∀ j, j ≠ NaturalScanBuffer.buffer n → j ≠ NaturalScanBuffer.flag n → work' j = work j) →
      Kept L left right arity R work → Kept L left right arity R work' := by
  rintro work work' hw ⟨hl, hr, hz, hframe⟩
  have hinner : ∀ j : Fin (n + 1), j ≠ NaturalMachine.flagIndex n → work' j.castSucc = work j.castSucc := by
    intro j hj
    apply hw
    · intro he
      have hv := congrArg Fin.val he
      simp only [NaturalScanBuffer.buffer, Fin.val_castSucc, Fin.val_last] at hv
      omega
    · intro he
      apply hj
      apply Fin.ext
      have hv := congrArg (fun i : Fin (n + 2) => i.val) he
      simpa only [NaturalScanBuffer.flag, Fin.val_castSucc] using hv
  have hl' := hinner left sep.flagLeft.symm
  have hr' := hinner right sep.flagRight.symm
  exact ⟨by simpa only [hl'] using hl, by simpa only [hr'] using hr, by simpa only [hr'] using hz,
    hR _ _ (fun j _ _ hj => hinner j hj) hframe⟩

theorem integer_hoareTime (L : ℕ) (left right : Fin (n + 1))
    (sep : Separate left right (NaturalMachine.flagIndex n)) (arity : ℕ)
    (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (SourceIntegerField.machine n).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work)
      (fun inp work out => Cursor (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input)
          emitted inp work out ∧ Ready L left right arity R work ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (NaturalMachineParser.integerAccepted input)) (13 * L + 13) := by
  have h := SourceIntegerField.hoareTime L before input emitted hlen (Kept L left right arity R)
    (kept_frame L left right sep arity R hR)
  rintro inp work out ⟨hc, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', _hb', hu', hf', hv', hl', hright', hrz', hframe'⟩ :=
    h inp work out ⟨hc, hr.safe, hr.encoded, hr.flagHead, hr.candidate, hr.arityBits, hr.arityZero, hr.frame⟩
  have hm := VirtualCursor.markers_reaches (SourceIntegerField.machine n) hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  exact ⟨d, t, ht, hd, hh, hc', ⟨hs', fun j => (hm.2.1 j).1, hu', hl', hright', hrz', hf', hframe'⟩, hv'⟩

theorem constant_hoareTime (value : Bool) (L : ℕ) (left right : Fin (n + 1))
    (sep : Separate left right (NaturalMachine.flagIndex n)) (arity : ℕ)
    (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (SourceTermToken.setStatus (NaturalScanBuffer.flag n) value).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool value) 1 := by
  let R0 : (Fin (n + 2) → Tape) → Prop := fun work =>
    Reusable L (work (NaturalScanBuffer.buffer n)) ∧ Kept L left right arity R work
  have hR0 : ∀ work work', (∀ j, j ≠ NaturalScanBuffer.flag n → work' j = work j) → R0 work → R0 work' := by
    rintro work work' hw ⟨hb, hk⟩
    exact ⟨by simpa only [hw _ NaturalScanBuffer.separate.symm] using hb,
      kept_frame L left right sep arity R hR work work' (fun j _ hj => hw j hj) hk⟩
  have h := SourceTermToken.setStatus_hoareTime (NaturalScanBuffer.flag n) value before input emitted R0 hR0
  rintro inp work out ⟨hc, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', hf', hv', hb', hl', hright', hz', hframe'⟩ :=
    h inp work out ⟨hc, hr.safe, hr.flagHead, hr.encoded, hr.candidate, hr.arityBits, hr.arityZero, hr.frame⟩
  have hm := VirtualCursor.markers_reaches (SourceTermToken.setStatus (NaturalScanBuffer.flag n) value) hd
    (VirtualCursor.input_safe hc) (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  exact ⟨d, t, ht, hd, hh, hc', ⟨hs', fun j => (hm.2.1 j).1, hb', hl', hright', hz', hf', hframe'⟩, hv'⟩

end JointThermoComplexity.Complexity.SourceTermFields

#print axioms JointThermoComplexity.Complexity.SourceTermFields.integer_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceTermFields.constant_hoareTime
