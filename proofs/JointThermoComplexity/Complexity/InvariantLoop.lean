module
public import proofs.JointThermoComplexity.Complexity.CursorLoopSteps

set_option autoImplicit false
@[expose] public section

/-!
# A predicate-based loop rule for advancing parsers

The invariant may describe the current input cursor, output accumulator and work
tapes without prescribing one exact work-tape family. It sees the read-only fuel
register parked at cell one; the machine physically advances its head to count
iterations and restores it when the loop exits.
-/

namespace JointThermoComplexity.Complexity.InvariantLoop
open _root_.Complexity
open _root_.Complexity.TM
open CursorLoopSteps

variable {n : ℕ} {body : TM n} {r : Fin n}

def restore (work : Fin n → Tape) (r : Fin n) (v : ℕ) : Fin n → Tape :=
  Function.update work r (regTape v)

theorem restore_update (work : Fin n → Tape) (r : Fin n) (v : ℕ) (t : Tape) :
    restore (Function.update work r t) r v = restore work r v := by
  simp only [restore, Function.update_idem]

theorem restore_idem (work : Fin n → Tape) (r : Fin n) (v : ℕ) :
    restore (restore work r v) r v = restore work r v := by
  simp only [restore, Function.update_idem]

theorem restore_self (work : Fin n → Tape) (r : Fin n) (v : ℕ)
    (h : work r = regTape v) : restore work r v = work := by
  rw [restore, ← h, Function.update_eq_self]

structure Frame (r : Fin n) (v head : ℕ) (P : _root_.Complexity.TM.TapePred n)
    (inp : Tape) (work : Fin n → Tape) (out : Tape) : Prop where
  fuel : work r = ⟨head, regCells v⟩
  readInput : inp.read ≠ Γ.start
  readOthers : ∀ j, j ≠ r → (work j).read ≠ Γ.start
  readOutput : out.read ≠ Γ.start
  invariant : P inp (restore work r v) out

theorem Frame.register {v : ℕ} {P : _root_.Complexity.TM.TapePred n}
    {inp : Tape} {work : Fin n → Tape} {out : Tape} (h : Frame r v 1 P inp work out) :
    IsReg v (work r) := by rw [h.fuel]; exact reg_regT v

theorem Frame.on_work {v : ℕ} {P : _root_.Complexity.TM.TapePred n}
    {inp : Tape} {work : Fin n → Tape} {out : Tape} (h : Frame r v 1 P inp work out) :
    P inp work out := by
  have hs := restore_self work r v h.fuel
  simpa only [hs] using h.invariant

theorem run (P : ℕ → _root_.Complexity.TM.TapePred n) (B v : ℕ)
    (hbody : ∀ i, i < v → body.HoareTime (Frame r v (i + 2) (P i))
      (Frame r v (i + 2) (P (i + 1))) B) :
    ∀ m i, v = i + m → ∀ c : Cfg n (forRegTM body r).Q,
      c.state = .inl .test → Frame r v (i + 1) (P i) c.input c.work c.output →
      ∃ d t, t ≤ m * (B + 2) + (v + 2) ∧ (forRegTM body r).reachesIn t c d ∧
        (forRegTM body r).halted d ∧ Frame r v 1 (P v) d.input d.work d.output := by
  intro m
  induction m with
  | zero =>
    intro i hi c hs hf
    obtain rfl : v = i := by omega
    have hblank : (c.work r).read = Γ.blank := by
      rw [hf.fuel]
      exact regCells_blank le_rfl
    have hstep := forRegTM_step_test_blank c hs hblank hf.readInput hf.readOthers hf.readOutput
    obtain ⟨d, hreach, hhalt, hinp, hwork, hcells, hhead, hout⟩ :=
      forRegTM_rewind_run (body := body) v
        { state := .inl .rewind, input := c.input,
          work := Function.update c.work r ((c.work r).move .left), output := c.output }
        rfl hf.readInput
        (fun j hj => by
          change (Function.update c.work r ((c.work r).move .left) j).read ≠ Γ.start
          rw [Function.update_of_ne hj]
          exact hf.readOthers j hj)
        hf.readOutput
        (by simp only [Function.update_self, Tape.move_cells, hf.fuel]; rfl)
        (fun j hj => by
          simp only [Function.update_self, Tape.move_cells, hf.fuel]
          exact regCells_ne_start hj)
        (by simp [hf.fuel, Tape.move])
    have hdreg : d.work r = regTape v := by
      apply Tape.ext hhead
      simpa only [Function.update_self, Tape.move_cells, hf.fuel, regT_cells] using hcells
    have hdwork : d.work = restore c.work r v := by
      funext j
      by_cases hj : j = r
      · subst j
        simpa only [restore, Function.update_self] using hdreg
      · simpa only [restore, Function.update_of_ne hj] using hwork j hj
    have hfinal : Frame r v 1 (P v) d.input d.work d.output := by
      refine ⟨hdreg, ?_, ?_, ?_, ?_⟩
      · simpa only [hinp] using hf.readInput
      · intro j hj
        simpa only [hdwork, restore, Function.update_of_ne hj] using hf.readOthers j hj
      · simpa only [hout] using hf.readOutput
      · simpa only [hinp, hout, hdwork, restore_idem] using hf.invariant
    exact ⟨d, (v + 1) + 1, by omega, .step hstep hreach, hhalt, hfinal⟩
  | succ m ih =>
    intro i hi c hs hf
    have hone : (c.work r).read = Γ.one := by
      rw [hf.fuel]
      change regCells v (i + 1) = Γ.one
      exact regCells_one (by omega) (by omega)
    have hstep₁ := forRegTM_step_test_one c hs hone hf.readInput hf.readOthers hf.readOutput
    let work₁ := Function.update c.work r ((c.work r).move .right)
    have hpre : Frame r v (i + 2) (P i) c.input work₁ c.output := by
      refine ⟨?_, hf.readInput, ?_, hf.readOutput, ?_⟩
      · simp only [work₁, Function.update_self, hf.fuel, Tape.move]
      · intro j hj
        change (Function.update c.work r ((c.work r).move .right) j).read ≠ Γ.start
        rw [Function.update_of_ne hj]
        exact hf.readOthers j hj
      · simpa only [work₁, restore_update] using hf.invariant
    obtain ⟨cb, tb, htb, hbreach, hbhalt, hb⟩ := hbody i (by omega) c.input work₁ c.output hpre
    have hlift := reachesIn_map (wrapCfg body r) (fun a b h => forRegTM_lift_step a b h) hbreach
    have hbreads : ∀ j, (cb.work j).read ≠ Γ.start := by
      intro j
      by_cases hj : j = r
      · subst j
        rw [hb.fuel]
        change regCells v (i + 2) ≠ Γ.start
        exact regCells_ne_start (by omega)
      · exact hb.readOthers j hj
    have hstep₂ := forRegTM_step_loopback (wrapCfg body r cb)
      (by show Sum.inr cb.state = Sum.inr body.qhalt; rw [hbhalt]) hb.readInput hbreads hb.readOutput
    obtain ⟨d, t, ht, hreach, hhalt, hfinal⟩ := ih (i + 1) (by omega)
      ⟨.inl .test, cb.input, cb.work, cb.output⟩ rfl hb
    refine ⟨d, tb + (t + 1) + 1, ?_, .step hstep₁ ?_, hhalt, hfinal⟩
    · have hmul : (m + 1) * (B + 2) = m * (B + 2) + (B + 2) := Nat.succ_mul ..
      omega
    · exact reachesIn_trans _ hlift (.step hstep₂ hreach)

theorem hoareTime (body : TM n) (r : Fin n) (P : ℕ → _root_.Complexity.TM.TapePred n) (B v : ℕ)
    (hbody : ∀ i, i < v → body.HoareTime (Frame r v (i + 2) (P i))
      (Frame r v (i + 2) (P (i + 1))) B) :
    (forRegTM body r).HoareTime (Frame r v 1 (P 0)) (Frame r v 1 (P v))
      (v * (B + 2) + (v + 2)) := by
  intro inp work out hf
  obtain ⟨d, t, ht, hreach, hhalt, hfinal⟩ :=
    run P B v hbody v 0 (by omega) ⟨.inl .test, inp, work, out⟩ rfl hf
  exact ⟨d, t, ht, hreach, hhalt, hfinal⟩

end JointThermoComplexity.Complexity.InvariantLoop

#print axioms JointThermoComplexity.Complexity.InvariantLoop.run
#print axioms JointThermoComplexity.Complexity.InvariantLoop.hoareTime
