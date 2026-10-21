module
public import proofs.JointThermoComplexity.Complexity.NaturalScanBuffer
public import proofs.JointThermoComplexity.Complexity.IntegerField

set_option autoImplicit false
@[expose] public section

/-! Silent canonical signed-integer validation on every input, including negative zero. -/

namespace JointThermoComplexity.Complexity.SourceIntegerField
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
open NaturalScanBuffer (buffer flag separate)
variable {n : ℕ}

def copyMachine (n : ℕ) : TM (n + 2) := (IntegerMachine.machine n).retargetOutput

theorem copy_hoareTime (before input emitted : List Bool)
    (R : (Fin (n + 2) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ buffer n → j ≠ flag n → work' j = work j) → R work → R work') :
    (copyMachine n).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work (buffer n)).HasBinaryPrefix [] ∧ (work (buffer n)).cells 0 = Γ.start ∧
        (work (flag n)).head = 1 ∧ R work)
      (fun inp work out => Cursor (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input)
          emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Stored (IntegerMachineRun.copied input) (work (buffer n)) ∧
        (work (flag n)).head = 1 ∧ (work (flag n)).read = Γ.ofBool (NaturalMachineParser.integerAccepted input) ∧ R work)
      (input.length + 3) := by
  rintro inp work out ⟨hc, hs, hb, hz, hf, hr⟩
  let original : Fin (n + 1) → Tape := fun j => work j.castSucc
  let C : (Fin (n + 1) → Tape) → Prop := fun old => ∀ j, j ≠ NaturalMachine.flagIndex n → old j = original j
  have hC : ∀ old old', (∀ j, j ≠ NaturalMachine.flagIndex n → old' j = old j) → C old → C old' := by
    intro old old' hh hp j hj
    exact (hh j hj).trans (hp j hj)
  have hscan := IntegerField.scan_hoareTime before input [] C hC
  have hroute := OutputRoute.hoareTime (IntegerMachine.machine n) _ _ (input.length + 3) (fun out' => out' = out) hscan
  obtain ⟨d, t, ht, hd, hh, _ho, hdout, hdcur, hdfh, hdfr, hdc⟩ := hroute inp work out
    ⟨hc.output_read, rfl, ⟨hc.cells, hc.head, fun j => hc.works j.castSucc, hb, hz⟩, hf, fun _ _ => rfl⟩
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
      exact hjf (hij.symm.trans (congrArg Fin.castSucc he))
    simpa only [original, hij] using hdc i hif
  have hbits : (d.work (buffer n)).HasBinaryPrefix (IntegerMachineRun.copied input) := by
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
  have hcur : Cursor (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input) emitted d.input d.work d.output :=
    ⟨hdcur.cells, hdcur.head, fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩,
      by simpa only [hdout] using hc.tapePrefix, by simpa only [hdout] using hc.zero⟩
  exact ⟨d, t, ht, hd, hh, hcur, hsafe, ⟨hbits, hdcur.zero⟩, hdfh, hdfr, hR work d.work hother hr⟩

def machine (n : ℕ) : TM (n + 2) := seqTM (BinaryBufferReset.machine (buffer n)) (copyMachine n)

theorem hoareTime (L : ℕ) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 2) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ buffer n → j ≠ flag n → work' j = work j) → R work → R work') :
    (machine n).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Reusable L (work (buffer n)) ∧ (work (flag n)).head = 1 ∧ R work)
      (fun inp work out => Cursor (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input)
          emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Stored (IntegerMachineRun.copied input) (work (buffer n)) ∧
        Reusable L (work (buffer n)) ∧ (work (flag n)).head = 1 ∧
        (work (flag n)).read = Γ.ofBool (NaturalMachineParser.integerAccepted input) ∧ R work) (13 * L + 13) := by
  rintro inp work out ⟨hc, hs, ⟨old, hold, hcontent, hz, hhead⟩, hf, hr⟩
  let R0 : (Fin (n + 2) → Tape) → Prop := fun work => (work (flag n)).head = 1 ∧ R work
  have hR0 : ∀ work work', (∀ j, j ≠ buffer n → work' j = work j) → R0 work → R0 work' := by
    rintro work work' hw ⟨hf, hr⟩
    exact ⟨by simpa only [hw (flag n) separate] using hf, hR work work' (fun j hj _ => hw j hj) hr⟩
  have hreset := BinaryBufferReset.hoareTime (buffer n) old before input emitted R0 hR0
  have hcopy := copy_hoareTime before input emitted R hR
  have hfull := seqTM_hoareTime (BinaryBufferReset.machine (buffer n)) (copyMachine n) hreset (by
    rintro inp work out ⟨hc, hs, hb, hf, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, CountTape.empty_prefix_of_zero hb, hb.cell0, hf, hr⟩) hcopy
  obtain ⟨d, t, ht, hd, hh, hc', hs', hb', hf', hv', hr'⟩ :=
    hfull inp work out ⟨hc, hs, hcontent, hz, hhead, hf, hr⟩
  have hcopied : (IntegerMachineRun.copied input).length ≤ L := by
    have he := congrArg List.length (NumericCursor.integer_split input)
    rw [List.length_append] at he
    omega
  exact ⟨d, t, by omega, hd, hh, hc', hs', hb', hb'.reusable (by omega), hf', hv', hr'⟩

end JointThermoComplexity.Complexity.SourceIntegerField

#print axioms JointThermoComplexity.Complexity.SourceIntegerField.hoareTime
