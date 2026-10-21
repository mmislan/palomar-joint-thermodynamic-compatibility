module
public import proofs.JointThermoComplexity.Complexity.NaturalField
public import proofs.JointThermoComplexity.Complexity.NaturalRawLoad
public import proofs.JointThermoComplexity.Complexity.VirtualCursor

set_option autoImplicit false
@[expose] public section

/-! Canonical natural validation into a reusable encoded buffer on every input. -/

namespace JointThermoComplexity.Complexity.NaturalScanBuffer
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
variable {n : ℕ}

def buffer (n : ℕ) : Fin (n + 2) := Fin.last (n + 1)
def flag (n : ℕ) : Fin (n + 2) := (NaturalMachine.flagIndex n).castSucc

theorem separate : flag n ≠ buffer n := by
  intro h
  have hv := congrArg Fin.val h
  simp only [flag, buffer, NaturalMachine.flagIndex, Fin.val_castSucc, Fin.val_last] at hv
  omega

def copyMachine (requirePositive : Bool) (n : ℕ) : TM (n + 2) :=
  (NaturalMachine.machine requirePositive n).retargetOutput

theorem copy_hoareTime (requirePositive : Bool) (before input emitted : List Bool)
    (R : (Fin (n + 2) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ buffer n → j ≠ flag n → work' j = work j) → R work → R work') :
    (copyMachine requirePositive n).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work (buffer n)).HasBinaryPrefix [] ∧ (work (buffer n)).cells 0 = Γ.start ∧
        (work (flag n)).head = 1 ∧ R work)
      (fun inp work out => Cursor (before ++ PayloadControl.copied .empty input) (NumericCursor.naturalRest input)
          emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Stored (PayloadControl.copied .empty input) (work (buffer n)) ∧
        (work (flag n)).head = 1 ∧
        (work (flag n)).read = Γ.ofBool (NaturalMachineParser.accepted requirePositive input) ∧ R work)
      (input.length + 2) := by
  rintro inp work out ⟨hc, hs, hb, hz, hf, hr⟩
  let original : Fin (n + 1) → Tape := fun j => work j.castSucc
  let C : (Fin (n + 1) → Tape) → Prop := fun old =>
    ∀ j, j ≠ NaturalMachine.flagIndex n → old j = original j
  have hC : ∀ old old', (∀ j, j ≠ NaturalMachine.flagIndex n → old' j = old j) → C old → C old' := by
    intro old old' hh hp j hj
    exact (hh j hj).trans (hp j hj)
  have hscan := NaturalField.scan_hoareTime requirePositive before input [] C hC
  have hroute := OutputRoute.hoareTime (NaturalMachine.machine requirePositive n) _ _ (input.length + 2)
    (fun out' => out' = out) hscan
  obtain ⟨d, t, ht, hd, hh, _ho, hdout, hdcur, hdfh, hdfr, hdc⟩ :=
    hroute inp work out ⟨hc.output_read, rfl, ⟨hc.cells, hc.head,
      fun j => hc.works j.castSucc, hb, hz⟩, hf, fun _ _ => rfl⟩
  have hother : ∀ j, j ≠ buffer n → j ≠ flag n → d.work j = work j := by
    intro j hjb hjf
    have hj : j.val < n + 1 := by
      by_contra hn
      have he : j = buffer n := by apply Fin.ext; simp only [buffer, Fin.val_last]; omega
      exact hjb he
    let i : Fin (n + 1) := ⟨j.val, hj⟩
    have hij : i.castSucc = j := by apply Fin.ext; rfl
    have hif : i ≠ NaturalMachine.flagIndex n := by
      intro he
      apply hjf
      exact hij.symm.trans (congrArg Fin.castSucc he)
    simpa only [original, hij] using hdc i hif
  have hbits : (d.work (buffer n)).HasBinaryPrefix (PayloadControl.copied .empty input) := by
    simpa only [buffer, List.nil_append] using hdcur.tapePrefix
  have hsafe : ∀ j, Parked (d.work j) := by
    intro j
    by_cases hj : j = buffer n
    · subst j
      exact ⟨by rw [hbits.1]; omega, (show (d.work (buffer n)).HasBinaryContent _ from hbits.2).cells_ne_start⟩
    · by_cases hjf : j = flag n
      · subst j
        exact ⟨by change (d.work ((NaturalMachine.flagIndex n).castSucc)).head ≥ 1; rw [hdfh],
          TapeSafety.work_reaches (flag n) hd (hs _).2⟩
      · rw [hother j hj hjf]
        exact hs j
  have hcur : Cursor (before ++ PayloadControl.copied .empty input) (NumericCursor.naturalRest input)
      emitted d.input d.work d.output :=
    ⟨hdcur.cells, hdcur.head, fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩,
      by simpa only [hdout] using hc.tapePrefix, by simpa only [hdout] using hc.zero⟩
  exact ⟨d, t, ht, hd, hh, hcur, hsafe, ⟨hbits, hdcur.zero⟩, hdfh, hdfr, hR work d.work hother hr⟩

def machine (requirePositive : Bool) (n : ℕ) : TM (n + 2) :=
  seqTM (seqTM (BinaryBufferReset.machine (buffer n)) (copyMachine requirePositive n)) (rewindWorkTM (buffer n))

theorem hoareTime (requirePositive : Bool) (L : ℕ) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 2) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ buffer n → j ≠ flag n → work' j = work j) → R work → R work') :
    (machine requirePositive n).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Reusable L (work (buffer n)) ∧ (work (flag n)).head = 1 ∧ R work)
      (fun inp work out => Cursor (before ++ PayloadControl.copied .empty input) (NumericCursor.naturalRest input)
          emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work (buffer n)).HasBinaryString (PayloadControl.copied .empty input) ∧
        (work (buffer n)).cells 0 = Γ.start ∧ Reusable L (work (buffer n)) ∧
        (work (flag n)).head = 1 ∧
        (work (flag n)).read = Γ.ofBool (NaturalMachineParser.accepted requirePositive input) ∧ R work)
      (14 * L + 18) := by
  rintro inp work out ⟨hc, hs, ⟨old, hold, hcontent, hz, hhead⟩, hf, hr⟩
  let R0 : (Fin (n + 2) → Tape) → Prop := fun work => (work (flag n)).head = 1 ∧ R work
  have hR0 : ∀ work work', (∀ j, j ≠ buffer n → work' j = work j) → R0 work → R0 work' := by
    rintro work work' hw ⟨hf, hr⟩
    exact ⟨by simpa only [hw (flag n) separate] using hf, hR work work' (fun j hj _ => hw j hj) hr⟩
  let R1 : (Fin (n + 2) → Tape) → Prop := fun work =>
    (work (flag n)).head = 1 ∧ (work (flag n)).read = Γ.ofBool (NaturalMachineParser.accepted requirePositive input) ∧ R work
  have hR1 : ∀ work work', (∀ j, j ≠ buffer n → work' j = work j) → R1 work → R1 work' := by
    rintro work work' hw ⟨hf, hv, hr⟩
    exact ⟨by simpa only [hw (flag n) separate] using hf,
      by simpa only [hw (flag n) separate] using hv, hR work work' (fun j hj _ => hw j hj) hr⟩
  have hrst := BinaryBufferReset.hoareTime (buffer n) old before input emitted R0 hR0
  have hcopy := copy_hoareTime requirePositive before input emitted R hR
  have hrew := BinaryPrefixRewind.hoareTime (buffer n) (PayloadControl.copied .empty input)
    (before ++ PayloadControl.copied .empty input) (NumericCursor.naturalRest input) emitted R1 hR1
  have hrc := seqTM_hoareTime (BinaryBufferReset.machine (buffer n)) (copyMachine requirePositive n) hrst (by
    rintro inp work out ⟨hc, hs, hb, hf, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, CountTape.empty_prefix_of_zero hb, hb.cell0, hf, hr⟩) hcopy
  have hfull := seqTM_hoareTime (seqTM (BinaryBufferReset.machine (buffer n)) (copyMachine requirePositive n))
    (rewindWorkTM (buffer n)) hrc (by
      rintro inp work out ⟨hc, hs, ⟨hb, hz⟩, hf, hv, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, hb, hz, hf, hv, hr⟩) hrew
  obtain ⟨d, t, ht, hd, hh, hc', hs', hb', hz', hf', hv', hr'⟩ :=
    hfull inp work out ⟨hc, hs, hcontent, hz, hhead, hf, hr⟩
  have hcplen : (PayloadControl.copied .empty input).length ≤ L := by
    have he := congrArg List.length (NumericCursor.natural_split input)
    rw [List.length_append] at he
    omega
  have hu : Reusable L (d.work (buffer n)) :=
    ⟨PayloadControl.copied .empty input, by omega, hb'.2, hz', by rw [hb'.1]; omega⟩
  exact ⟨d, t, by omega, hd, hh, hc', hs', hb', hz', hu, hf', hv', hr'⟩

end JointThermoComplexity.Complexity.NaturalScanBuffer

#print axioms JointThermoComplexity.Complexity.NaturalScanBuffer.copy_hoareTime
#print axioms JointThermoComplexity.Complexity.NaturalScanBuffer.hoareTime
