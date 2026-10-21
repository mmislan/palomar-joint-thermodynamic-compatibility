module
public import proofs.JointThermoComplexity.Complexity.InputPositionMachine

set_option autoImplicit false
@[expose] public section

/-! Exact reverse-walk position saving, followed by canonical unary-register rewind. -/

namespace JointThermoComplexity.Complexity.InputPositionRun
open _root_.Complexity _root_.Complexity.TM HeaderAt InputPositionMachine
variable {w : ℕ}

theorem scan (idx : Fin w) (k v : ℕ) (c : Cfg w (InputPositionMachine.machine idx).Q)
    (hs : c.state = some true) (hi : Tape.StartInvariant c.input) (hh : c.input.head = k)
    (hw : ∀ j, Parked (c.work j)) (hp : (c.work idx).HasBinaryPrefix (List.replicate v true))
    (hz : (c.work idx).cells 0 = Γ.start) (ho : c.output.read ≠ Γ.start) :
    ∃ d, (InputPositionMachine.machine idx).reachesIn (k + 1) c d ∧
      (InputPositionMachine.machine idx).halted d ∧ d.input.cells = c.input.cells ∧ d.input.head = 1 ∧
      (∀ j, j ≠ idx → d.work j = c.work j) ∧
      (d.work idx).HasBinaryPrefix (List.replicate (v + k) true) ∧ (d.work idx).cells 0 = Γ.start ∧
      (∀ j, Parked (d.work j)) ∧ d.output = c.output := by
  induction k generalizing v c with
  | zero =>
    have hr : c.input.read = Γ.start := by rw [Tape.read, hh]; exact hi.1
    have he := finish_step idx c hs hr (fun j => (hw j).read_ne_start) ho
    refine ⟨⟨none, c.input.move .right, c.work, c.output⟩, .step he .zero, rfl, rfl, ?_,
      (fun _ _ => rfl), by simpa only [Nat.add_zero] using hp, hz, hw, rfl⟩
    change c.input.head + 1 = 1
    omega
  | succ k ih =>
    have hr : c.input.read ≠ Γ.start := hi.2 c.input.head (by omega)
    have he := scan_step idx c hs hr (fun j => (hw j).read_ne_start) ho
    let a : Cfg w (InputPositionMachine.machine idx).Q :=
      ⟨some true, c.input.move .left, appendMark idx c.work, c.output⟩
    have hp' := append_prefix idx c.work v hp
    have hz' := append_zero idx c.work v hp hz
    have hw' : ∀ j, Parked (a.work j) := by
      intro j
      by_cases hj : j = idx
      · subst j
        have hcontent : (appendMark idx c.work idx).HasBinaryContent (List.replicate (v + 1) true) := hp'.2
        exact ⟨by change 1 ≤ (appendMark idx c.work idx).head; rw [hp'.1]; omega, hcontent.cells_ne_start⟩
      · simpa only [a, appendMark, Function.update_of_ne hj] using hw j
    obtain ⟨d, hd, hhalt, hcells, hhead, hother, hprefix, hzero, hsafe, hout⟩ :=
      ih (v + 1) a rfl hi (by change c.input.head - 1 = k; omega) hw' hp' hz' ho
    refine ⟨d, .step he hd, hhalt, hcells, hhead, ?_, ?_, hzero, hsafe, hout⟩
    · intro j hj
      exact (hother j hj).trans (by simp only [a, appendMark, Function.update_of_ne hj])
    · have hn : v + 1 + k = v + (k + 1) := by omega
      simpa only [hn] using hprefix

theorem raw_hoareTime (idx : Fin w) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (InputPositionMachine.machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work idx) ∧ R work)
      (fun inp work out => Cursor [] (before ++ input) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix (List.replicate before.length true) ∧
        (work idx).cells 0 = Γ.start ∧ R work) (before.length + 2) := by
  rintro inp work out ⟨hc, hw, hz, hr⟩
  let c : Cfg w (InputPositionMachine.machine idx).Q := ⟨some false, inp, work, out⟩
  have he := initial_step idx c rfl hc.input_read (fun j => (hc.works j).1) hc.output_read
  let a : Cfg w (InputPositionMachine.machine idx).Q := ⟨some true, inp.move .left, work, out⟩
  obtain ⟨d, hd, hh, hcells, hhead, hother, hp, hzero, hsafe, hout⟩ :=
    scan idx before.length 0 a rfl ⟨(VirtualCursor.input_safe hc).1, (VirtualCursor.input_safe hc).2⟩
      (by change inp.head - 1 = before.length; rw [hc.head]; omega)
      hw (CountTape.empty_prefix_of_zero hz) hz.2.1 hc.output_read
  have hcur : Cursor [] (before ++ input) emitted d.input d.work d.output :=
    ⟨by simpa only [List.nil_append] using hcells.trans hc.cells, hhead,
      fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩,
      by simpa only [a] using hout ▸ hc.tapePrefix, by simpa only [a] using hout ▸ hc.zero⟩
  exact ⟨d, before.length + 2, le_rfl, .step he hd, hh, hcur, hsafe,
    by simpa only [Nat.zero_add] using hp, hzero, hR work d.work hother hr⟩

def machine (idx : Fin w) : TM w := seqTM (InputPositionMachine.machine idx) (rewindWorkTM idx)

theorem hoareTime (idx : Fin w) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work idx) ∧ R work)
      (fun inp work out => Cursor [] (before ++ input) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg before.length (work idx) ∧ R work) (2 * before.length + 6) := by
  have hs := raw_hoareTime idx before input emitted R hR
  have hr := CountRewind.hoareTime idx before.length [] (before ++ input) emitted R hR
  have hseq := seqTM_hoareTime (InputPositionMachine.machine idx) (rewindWorkTM idx) hs (by
    rintro inp work out ⟨hc, hw, hp, hz, hframe⟩
    obtain ⟨hi, hworks, ho⟩ := hc.phase
    rw [hi, hworks, ho]
    exact ⟨hc, hw, hp, hz, hframe⟩) hr
  apply HoareTime.mono_bound (b := (before.length + 2) + 1 + (before.length + 3))
  · apply HoareTime.strengthen_post hseq
    rintro inp work out ⟨hreg, hc, hw, hframe⟩
    exact ⟨hc, hw, hreg, hframe⟩
  · omega

end JointThermoComplexity.Complexity.InputPositionRun

#print axioms JointThermoComplexity.Complexity.InputPositionRun.raw_hoareTime
#print axioms JointThermoComplexity.Complexity.InputPositionRun.hoareTime
