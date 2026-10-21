module
public import proofs.JointThermoComplexity.Complexity.HeaderMachineParser
public import proofs.JointThermoComplexity.Complexity.WorkPermutation

set_option autoImplicit false
@[expose] public section

/-! Dimension parsing at selected registers, with a stable compositional cursor. -/

namespace JointThermoComplexity.Complexity.HeaderAt
open _root_.Complexity
open _root_.Complexity.TM

structure Cursor {m : ℕ} (before remaining emitted : List Bool)
    (inp : Tape) (work : Fin m → Tape) (out : Tape) : Prop where
  cells : inp.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells
  head : inp.head = before.length + 1
  works : ∀ i, (work i).read ≠ Γ.start ∧ 1 ≤ (work i).head
  tapePrefix : out.HasBinaryPrefix emitted
  zero : out.cells 0 = Γ.start

theorem Cursor.input_read {m : ℕ} {before remaining emitted : List Bool}
    {inp : Tape} {work : Fin m → Tape} {out : Tape}
    (h : Cursor before remaining emitted inp work out) : inp.read ≠ Γ.start := by
  rw [Tape.read, h.head, h.cells]
  exact Tape.init_ofBool_cells_ne_start _ _ (by omega)

theorem Cursor.output_read {m : ℕ} {before remaining emitted : List Bool}
    {inp : Tape} {work : Fin m → Tape} {out : Tape}
    (h : Cursor before remaining emitted inp work out) : out.read ≠ Γ.start := by
  have hb : out.read = Γ.blank := by
    simp [Tape.read, h.tapePrefix.1, h.tapePrefix.2.2 emitted.length le_rfl]
  simp [hb]

theorem Cursor.phase {m : ℕ} {before remaining emitted : List Bool}
    {inp : Tape} {work : Fin m → Tape} {out : Tape}
    (h : Cursor before remaining emitted inp work out) :
    transitionInput inp = inp ∧ (fun i => transitionTape (work i)) = work ∧
      transitionTape out = out :=
  ⟨transitionInput_eq_self h.input_read, funext (fun i => transitionTape_eq_self (h.works i).1),
    transitionTape_eq_self h.output_read⟩

variable {n : ℕ}

def machine (e : Fin (n + 2) ≃ Fin (n + 2)) : TM (n + 2) :=
  WorkPermutation.machine e (HeaderMachine.machine n)

def counter (e : Fin (n + 2) ≃ Fin (n + 2)) : Fin (n + 2) := e (HeaderMachine.counterIndex n)
def flag (e : Fin (n + 2) ≃ Fin (n + 2)) : Fin (n + 2) := e (HeaderMachine.flagIndex n)

theorem run (e : Fin (n + 2) ≃ Fin (n + 2)) (before remaining emitted : List Bool)
    (c : Cfg (n + 2) (machine e).Q) (hs : c.state = .start)
    (hc : Cursor before remaining emitted c.input c.work c.output)
    (hr : IsReg 0 (c.work (counter e))) (hf : (c.work (flag e)).head = 1) :
    ∃ d t, t ≤ 2 * HeaderControl.count remaining + 5 ∧
      (machine e).reachesIn t c d ∧ (machine e).halted d ∧
      Cursor (before ++ HeaderControl.copied remaining) (HeaderControl.suffix remaining)
        (emitted ++ HeaderControl.copied remaining) d.input d.work d.output ∧
      IsReg (HeaderControl.count remaining) (d.work (counter e)) ∧
      (d.work (flag e)).head = 1 ∧ (d.work (flag e)).read = Γ.ofBool (HeaderControl.valid remaining) ∧
      (∀ i, i ≠ counter e → i ≠ flag e → d.work i = c.work i) := by
  let v : Cfg (n + 2) (HeaderMachine.machine n).Q := WorkPermutation.cfg e.symm c
  obtain ⟨d', t, ht, hreach, hhalt, hic, hih, hwork, hreg, hfh, hfr, hz, hp⟩ :=
    HeaderMachineRun.run_count_bound before emitted remaining v hs hc.cells hc.head
      (fun i => hc.works (e i)) hr hf hc.tapePrefix hc.zero
  let d : Cfg (n + 2) (machine e).Q := WorkPermutation.cfg e d'
  have hstart : WorkPermutation.cfg e v = c := by
    apply Cfg.ext <;> simp [v, WorkPermutation.cfg]
  have hparent : (machine e).reachesIn t c d := by
    rw [← hstart]
    exact WorkPermutation.reaches e (HeaderMachine.machine n) hreach
  have hreg' : IsReg (HeaderControl.count remaining) (d.work (counter e)) := by
    simpa [d, WorkPermutation.cfg, counter] using hreg
  have hfh' : (d.work (flag e)).head = 1 := by
    simpa [d, WorkPermutation.cfg, flag] using hfh
  have hfr' : (d.work (flag e)).read = Γ.ofBool (HeaderControl.valid remaining) := by
    simpa [d, WorkPermutation.cfg, flag] using hfr
  have hother : ∀ i, i ≠ counter e → i ≠ flag e → d.work i = c.work i := by
    intro i hci hfi
    have hci' : e.symm i ≠ HeaderMachine.counterIndex n := by
      intro heq
      apply hci
      simpa [counter] using congrArg e heq
    have hfi' : e.symm i ≠ HeaderMachine.flagIndex n := by
      intro heq
      apply hfi
      simpa [flag] using congrArg e heq
    simpa [d, v, WorkPermutation.cfg] using hwork (e.symm i) hci' hfi'
  have hcursor : Cursor (before ++ HeaderControl.copied remaining) (HeaderControl.suffix remaining)
      (emitted ++ HeaderControl.copied remaining) d.input d.work d.output := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [d, WorkPermutation.cfg, List.append_assoc, HeaderControl.consumed_and_suffix] using hic.trans hc.cells
    · simpa only [d, WorkPermutation.cfg, List.length_append] using hih
    · intro i
      by_cases hci : i = counter e
      · subst i
        exact ⟨hreg'.parked.read_ne_start, hreg'.parked.1⟩
      · by_cases hfi : i = flag e
        · subst i
          refine ⟨?_, by rw [hfh']⟩
          rw [hfr']
          exact Γ.ofBool_ne_start _
        · rw [hother i hci hfi]
          exact hc.works i
    · exact hp
    · exact hz
  exact ⟨d, t, ht, hparent, WorkPermutation.halted e (HeaderMachine.machine n) hhalt,
    hcursor, hreg', hfh', hfr', hother⟩

theorem hoareTime (e : Fin (n + 2) ≃ Fin (n + 2)) (before remaining emitted : List Bool)
    (P : (Fin (n + 2) → Tape) → Prop)
    (hP : ∀ work work', (∀ i, i ≠ counter e → i ≠ flag e → work' i = work i) → P work → P work') :
    (machine e).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧
        IsReg 0 (work (counter e)) ∧ (work (flag e)).head = 1 ∧ P work)
      (fun inp work out =>
        Cursor (before ++ HeaderControl.copied remaining) (HeaderControl.suffix remaining)
          (emitted ++ HeaderControl.copied remaining) inp work out ∧
        IsReg (HeaderControl.count remaining) (work (counter e)) ∧
        (work (flag e)).head = 1 ∧ (work (flag e)).read = Γ.ofBool (HeaderControl.valid remaining) ∧ P work)
      (2 * HeaderControl.count remaining + 5) := by
  rintro inp work out ⟨hc, hr, hf, hp⟩
  obtain ⟨d, t, ht, hreach, hhalt, hcursor, hreg, hfh, hfr, hother⟩ :=
    run e before remaining emitted ⟨.start, inp, work, out⟩ rfl hc hr hf
  exact ⟨d, t, ht, hreach, hhalt, hcursor, hreg, hfh, hfr, hP work d.work hother hp⟩

end JointThermoComplexity.Complexity.HeaderAt

#print axioms JointThermoComplexity.Complexity.HeaderAt.run
#print axioms JointThermoComplexity.Complexity.HeaderAt.hoareTime
