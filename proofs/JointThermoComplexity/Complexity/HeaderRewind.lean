module
public import proofs.JointThermoComplexity.Complexity.HeaderMachine
public import proofs.Complexitylib.Models.TuringMachine.Subroutines.Internal

set_option autoImplicit false
@[expose] public section

/-! Reuse the checked work-tape rewind with the header counter's complete frame. -/

namespace JointThermoComplexity.Complexity.HeaderRewind
open _root_.Complexity
open _root_.Complexity.TM
open HeaderMachine

variable {n : ℕ}

theorem run (k : ℕ) (c : Cfg (n + 2) (machine n).Q) (hs : c.state = .rewind .moveLeft)
    (hcounter : c.work (counterIndex n) = growing k)
    (hi : c.input.read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) (hohead : 1 ≤ c.output.head)
    (hw : ∀ i, i ≠ counterIndex n → (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head) :
    ∃ c' t, t ≤ k + 3 ∧ (machine n).reachesIn t c c' ∧ (machine n).halted c' ∧
      c'.input = c.input ∧ c'.output = c.output ∧
      (∀ i, i ≠ counterIndex n → c'.work i = c.work i) ∧ IsReg k (c'.work (counterIndex n)) := by
  let P : Tape → (Fin (n + 2) → Tape) → Tape → Prop := fun inp work out =>
    inp = c.input ∧ out = c.output ∧ (work (counterIndex n)).cells = regCells k ∧
      ∀ i, i ≠ counterIndex n → work i = c.work i
  have hP : ∀ (inp : Tape) (work : Fin (n + 2) → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin (n + 2) → Tape) (out' : Tape),
      P inp work out → (work' (counterIndex n)).cells = (work (counterIndex n)).cells →
      (work' (counterIndex n)).head = 1 →
      (∀ i, i ≠ counterIndex n → work' i = work i) → inp' = inp →
      out'.cells = out.cells → out'.head = out.head → P inp' work' out' := by
    rintro inp work out inp' work' out' ⟨hinp, hout, hcells, hothers⟩ hc _ hw' hi' hoc hoh
    refine ⟨hi'.trans hinp, (Tape.ext hoh hoc).trans hout, hc.trans hcells, ?_⟩
    intro i hne
    exact (hw' i hne).trans (hothers i hne)
  have hrewind := rewindWorkTM_hoareTime_frame (counterIndex n) (k + 1) (P := P) hP
  have hpre : (c.work (counterIndex n)).cells 0 = Γ.start ∧
      (∀ j, 1 ≤ j → (c.work (counterIndex n)).cells j ≠ Γ.start) ∧
      (c.work (counterIndex n)).head ≤ k + 1 ∧ c.input.read ≠ Γ.start ∧
      c.output.read ≠ Γ.start ∧ 1 ≤ c.output.head ∧
      (∀ i, i ≠ counterIndex n → (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head) ∧
      P c.input c.work c.output := by
    refine ⟨?_, ?_, ?_, hi, ho, hohead, hw, rfl, rfl, ?_, fun _ _ => rfl⟩
    · simp [hcounter, growing]
    · intro j hj
      simpa only [hcounter, growing] using regCells_ne_start (v := k) hj
    · simp [hcounter, growing]
    · simp only [hcounter, growing]
  obtain ⟨d', t, ht, hreach, hhalt, hh, hp⟩ := hrewind c.input c.work c.output hpre
  let d₀ : Cfg (n + 2) RewindPhase := ⟨.moveLeft, c.input, c.work, c.output⟩
  have hwrap : wrap d₀ = c := by
    apply Cfg.ext
    · exact hs.symm
    · rfl
    · rfl
    · rfl
  have hparent : (machine n).reachesIn t c (wrap d') := by
    rw [← hwrap]
    exact rewind_reaches hreach
  have hc : d'.work (counterIndex n) = regTape k := Tape.ext hh hp.2.2.1
  refine ⟨wrap d', t, by omega, hparent, rewind_halted d' hhalt, hp.1, hp.2.1, hp.2.2.2, ?_⟩
  change IsReg k (d'.work (counterIndex n))
  rw [hc]
  exact reg_regT k

end JointThermoComplexity.Complexity.HeaderRewind

#print axioms JointThermoComplexity.Complexity.HeaderRewind.run
