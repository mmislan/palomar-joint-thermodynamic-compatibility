module
public import proofs.JointThermoComplexity.Complexity.SourceBinderControl
public import proofs.JointThermoComplexity.Complexity.NaturalScanBuffer

set_option autoImplicit false
@[expose] public section

/-! Read a unary source binder into a named counter and a work buffer, preserving real output. -/

namespace JointThermoComplexity.Complexity.SourceBinderBuffer
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
variable {n : ℕ}

def buffer (n : ℕ) : Fin (n + 3) := Fin.last (n + 2)
def counter (e : Fin (n + 2) ≃ Fin (n + 2)) : Fin (n + 3) := (HeaderAt.counter e).castSucc
def flag (e : Fin (n + 2) ≃ Fin (n + 2)) : Fin (n + 3) := (HeaderAt.flag e).castSucc

def machine (e : Fin (n + 2) ≃ Fin (n + 2)) : TM (n + 3) := (HeaderAt.machine e).retargetOutput

theorem hoareTime (e : Fin (n + 2) ≃ Fin (n + 2)) (before input emitted : List Bool)
    (R : (Fin (n + 3) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ buffer n → j ≠ counter e → j ≠ flag e → work' j = work j) → R work → R work') :
    (machine e).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work (buffer n)).HasBinaryPrefix [] ∧ (work (buffer n)).cells 0 = Γ.start ∧
        IsReg 0 (work (counter e)) ∧ (work (flag e)).head = 1 ∧ R work)
      (fun inp work out => Cursor (before ++ HeaderControl.copied input) (HeaderControl.suffix input) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Stored (HeaderControl.copied input) (work (buffer n)) ∧
        IsReg (HeaderControl.count input) (work (counter e)) ∧ (work (flag e)).head = 1 ∧
        (work (flag e)).read = Γ.ofBool (HeaderControl.valid input) ∧ R work)
      (2 * HeaderControl.count input + 5) := by
  rintro inp work out ⟨hc, hs, hb, hz, hcounter, hf, hr⟩
  let original : Fin (n + 2) → Tape := fun j => work j.castSucc
  let C : (Fin (n + 2) → Tape) → Prop := fun old =>
    ∀ j, j ≠ HeaderAt.counter e → j ≠ HeaderAt.flag e → old j = original j
  have hC : ∀ old old', (∀ j, j ≠ HeaderAt.counter e → j ≠ HeaderAt.flag e → old' j = old j) → C old → C old' := by
    intro old old' hh hp j hjc hjf
    exact (hh j hjc hjf).trans (hp j hjc hjf)
  have hscan := HeaderAt.hoareTime e before input [] C hC
  have hroute := OutputRoute.hoareTime (HeaderAt.machine e) _ _ (2 * HeaderControl.count input + 5)
    (fun out' => out' = out) hscan
  obtain ⟨c, t, ht, hd, hh, _ho, hdout, hdcur, hdcount, hdfh, hdfr, hdc⟩ :=
    hroute inp work out ⟨hc.output_read, rfl, ⟨hc.cells, hc.head, fun j => hc.works j.castSucc, hb, hz⟩,
      hcounter, hf, fun _ _ _ => rfl⟩
  change (c.work (flag e)).head = 1 at hdfh
  have hother : ∀ j, j ≠ buffer n → j ≠ counter e → j ≠ flag e → c.work j = work j := by
    intro j hjb hjc hjf
    have hj : j.val < n + 2 := by
      by_contra hn
      have he : j = buffer n := by apply Fin.ext; simp only [buffer, Fin.val_last]; omega
      exact hjb he
    let i : Fin (n + 2) := ⟨j.val, hj⟩
    have hij : i.castSucc = j := by apply Fin.ext; rfl
    have hic : i ≠ HeaderAt.counter e := by
      intro he
      apply hjc
      exact hij.symm.trans (congrArg Fin.castSucc he)
    have hif : i ≠ HeaderAt.flag e := by
      intro he
      apply hjf
      exact hij.symm.trans (congrArg Fin.castSucc he)
    simpa only [original, hij] using hdc i hic hif
  have hbits : (c.work (buffer n)).HasBinaryPrefix (HeaderControl.copied input) := by
    simpa only [buffer, List.nil_append] using hdcur.tapePrefix
  have hsafe : ∀ j, Parked (c.work j) := by
    intro j
    by_cases hj : j = buffer n
    · subst j
      exact ⟨by rw [hbits.1]; omega, (show (c.work (buffer n)).HasBinaryContent _ from hbits.2).cells_ne_start⟩
    · by_cases hjc : j = counter e
      · subst j
        exact hdcount.parked
      · by_cases hjf : j = flag e
        · subst j
          exact ⟨by rw [hdfh], TapeSafety.work_reaches (flag e) hd (hs _).2⟩
        · rw [hother j hj hjc hjf]
          exact hs j
  have hcur : Cursor (before ++ HeaderControl.copied input) (HeaderControl.suffix input) emitted c.input c.work c.output :=
    ⟨hdcur.cells, hdcur.head, fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩,
      by simpa only [hdout] using hc.tapePrefix, by simpa only [hdout] using hc.zero⟩
  exact ⟨c, t, ht, hd, hh, hcur, hsafe, ⟨hbits, hdcur.zero⟩, hdcount, hdfh, hdfr, hR work c.work hother hr⟩

theorem timeBound_le (L : ℕ) (input : List Bool) (hlen : input.length ≤ L) :
    2 * HeaderControl.count input + 5 ≤ 2 * L + 5 := by
  have hc := HeaderControl.count_le_length input
  omega

end JointThermoComplexity.Complexity.SourceBinderBuffer

#print axioms JointThermoComplexity.Complexity.SourceBinderBuffer.hoareTime
