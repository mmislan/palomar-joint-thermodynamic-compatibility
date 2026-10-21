module
public import proofs.JointThermoComplexity.Complexity.NaturalField
public import proofs.JointThermoComplexity.Complexity.WorkPermutation
public import proofs.JointThermoComplexity.Complexity.VirtualCursor

set_option autoImplicit false
@[expose] public section

/-! Copy a binary variable-index field with an arbitrarily selected validity tape. -/

namespace JointThermoComplexity.Complexity.NaturalWordCopy
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {n : ℕ}

def machine (e : Fin (n + 1) ≃ Fin (n + 1)) : TM (n + 1) :=
  WorkPermutation.machine e (NaturalMachine.machine false n)

def flag (e : Fin (n + 1) ≃ Fin (n + 1)) : Fin (n + 1) := e (NaturalMachine.flagIndex n)

def select (idx : Fin (n + 1)) : Fin (n + 1) ≃ Fin (n + 1) := Equiv.swap (NaturalMachine.flagIndex n) idx

theorem flag_select (idx : Fin (n + 1)) : flag (select idx) = idx := by simp [flag, select]

theorem run (e : Fin (n + 1) ≃ Fin (n + 1)) (before input emitted : List Bool)
    (c : Cfg (n + 1) (machine e).Q) (hstart : c.state = .start)
    (hc : Cursor before input emitted c.input c.work c.output) (hf : (c.work (flag e)).head = 1) :
    ∃ d t, t ≤ input.length + 2 ∧ (machine e).reachesIn t c d ∧ (machine e).halted d ∧
      Cursor (before ++ PayloadControl.copied .empty input) (NumericCursor.naturalRest input)
        (emitted ++ PayloadControl.copied .empty input) d.input d.work d.output ∧
      (d.work (flag e)).head = 1 ∧
      (d.work (flag e)).read = Γ.ofBool (NaturalMachineParser.accepted false input) ∧
      (∀ j, j ≠ flag e → d.work j = c.work j) := by
  let v : Cfg (n + 1) (NaturalMachine.machine false n).Q := WorkPermutation.cfg e.symm c
  obtain ⟨d', t, ht, hd, hh, hic, hih, hw, hfh, hfr, hz, hp⟩ :=
    NaturalMachineParser.run_parser_from_cursor false before emitted input v hstart hc.cells hc.head
      (fun j => (hc.works (e j)).1) hf hc.tapePrefix hc.zero
  let d : Cfg (n + 1) (machine e).Q := WorkPermutation.cfg e d'
  have hcfg : WorkPermutation.cfg e v = c := by
    apply Cfg.ext <;> simp [v, WorkPermutation.cfg]
  have hreach : (machine e).reachesIn t c d := by
    rw [← hcfg]
    exact WorkPermutation.reaches e (NaturalMachine.machine false n) hd
  have hfh' : (d.work (flag e)).head = 1 := by simpa [d, WorkPermutation.cfg, flag] using hfh
  have hfr' : (d.work (flag e)).read = Γ.ofBool (NaturalMachineParser.accepted false input) := by
    simpa [d, WorkPermutation.cfg, flag] using hfr
  have hother : ∀ j, j ≠ flag e → d.work j = c.work j := by
    intro j hj
    have hj' : e.symm j ≠ NaturalMachine.flagIndex n := by
      intro he
      apply hj
      simpa [flag] using congrArg e he
    simpa [d, v, WorkPermutation.cfg] using hw (e.symm j) hj'
  have hsafe : ∀ j, (d.work j).read ≠ Γ.start ∧ 1 ≤ (d.work j).head := by
    intro j
    by_cases hj : j = flag e
    · subst j
      refine ⟨?_, by rw [hfh']⟩
      rw [hfr']
      exact Γ.ofBool_ne_start _
    · rw [hother j hj]
      exact hc.works j
  have hcur := NumericCursor.advance hc (NumericCursor.natural_split input) hic hih hsafe hp hz
  exact ⟨d, t, ht, hreach, WorkPermutation.halted e (NaturalMachine.machine false n) hh,
    hcur, hfh', hfr', hother⟩

theorem hoareTime (e : Fin (n + 1) ≃ Fin (n + 1)) (before input emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ flag e → work' j = work j) → R work → R work') :
    (machine e).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (work (flag e)).head = 1 ∧ R work)
      (fun inp work out => Cursor (before ++ PayloadControl.copied .empty input) (NumericCursor.naturalRest input)
        (emitted ++ PayloadControl.copied .empty input) inp work out ∧ (work (flag e)).head = 1 ∧
        (work (flag e)).read = Γ.ofBool (NaturalMachineParser.accepted false input) ∧ R work) (input.length + 2) := by
  rintro inp work out ⟨hc, hf, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hfh, hfr, hw⟩ := run e before input emitted ⟨.start, inp, work, out⟩ rfl hc hf
  exact ⟨d, t, ht, hd, hh, hc', hfh, hfr, hR work d.work hw hr⟩

theorem parked_hoareTime (e : Fin (n + 1) ≃ Fin (n + 1)) (before input emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ flag e → work' j = work j) → R work → R work') :
    (machine e).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ j, (work j).cells 0 = Γ.start) ∧ (work (flag e)).head = 1 ∧ R work)
      (fun inp work out => Cursor (before ++ PayloadControl.copied .empty input) (NumericCursor.naturalRest input)
        (emitted ++ PayloadControl.copied .empty input) inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ j, (work j).cells 0 = Γ.start) ∧ (work (flag e)).head = 1 ∧
        (work (flag e)).read = Γ.ofBool (NaturalMachineParser.accepted false input) ∧ R work) (input.length + 2) := by
  rintro inp work out ⟨hc, hs, hz, hf, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hfh, hfr, hw⟩ := run e before input emitted ⟨.start, inp, work, out⟩ rfl hc hf
  have hm := VirtualCursor.markers_reaches (machine e) hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hz j, (hs j).2⟩) (VirtualCursor.output_safe hc)
  have hs' : ∀ j, Parked (d.work j) := fun j => ⟨(hc'.works j).2, (hm.2.1 j).2⟩
  exact ⟨d, t, ht, hd, hh, hc', hs', fun j => (hm.2.1 j).1, hfh, hfr, hR work d.work hw hr⟩

theorem encoded_hoareTime (e : Fin (n + 1) ≃ Fin (n + 1)) (v : ℕ) (before suffix emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ flag e → work' j = work j) → R work → R work') :
    (machine e).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode v ++ suffix) emitted inp work out ∧
        (work (flag e)).head = 1 ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode v) suffix
        (emitted ++ BitCodec.naturalCode v) inp work out ∧ (work (flag e)).head = 1 ∧
        (work (flag e)).read = Γ.one ∧ R work) ((BitCodec.naturalCode v ++ suffix).length + 2) := by
  have ha : NaturalMachineParser.accepted false (BitCodec.naturalCode v ++ suffix) = true := by
    simp [NaturalMachineParser.accepted, BitCodec.parseNatural_code]
  simpa only [NumericCursor.natural_copied_code, NumericCursor.natural_rest_code, ha, Γ.ofBool] using
    hoareTime e before (BitCodec.naturalCode v ++ suffix) emitted R hR

end JointThermoComplexity.Complexity.NaturalWordCopy

#print axioms JointThermoComplexity.Complexity.NaturalWordCopy.parked_hoareTime
#print axioms JointThermoComplexity.Complexity.NaturalWordCopy.encoded_hoareTime
