module
public import proofs.Complexitylib.Models.TuringMachine.Registers.ForReg

/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in third_party/complexitylib/LICENSE.
Authors: Samuel Schlesinger

Adapted from the private ForReg simulation lemmas at upstream
43d4bb1a30bd93846eab5480bec8a37113586109. The owned extension exposes
step/rewind interfaces and weakens the surrounding tape hypotheses to current
reads different from the left marker. The adopted library source is unchanged.
-/

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity.Complexity.CursorLoopSteps
open _root_.Complexity
open _root_.Complexity.TM

variable {n : ℕ} {body : TM n} {r : Fin n}

def wrapCfg (body : TM n) (r : Fin n) (c : Cfg n body.Q) :
    Cfg n (forRegTM body r).Q :=
  { state := .inr c.state, input := c.input, work := c.work, output := c.output }

/-- Body steps lift to composite steps. -/
theorem forRegTM_lift_step (c c' : Cfg n body.Q)
    (hstep : body.step c = some c') :
    (forRegTM body r).step (wrapCfg body r c) = some (wrapCfg body r c') := by
  have hne : ¬ c.state = body.qhalt := by
    intro h
    rw [TM.step, ite_eq_left h] at hstep
    simp at hstep
  rw [TM.step, ite_eq_right hne] at hstep
  rw [TM.step, ite_eq_right (show ¬ (wrapCfg body r c).state = (forRegTM body r).qhalt from
    by simp [wrapCfg, forRegTM])]
  simp only [wrapCfg, forRegTM, hne, ↓reduceIte]
  revert hstep
  generalize body.δ c.state c.input.read (fun i => (c.work i).read) c.output.read = bd
  obtain ⟨q', ww, ow, iD, wD, oD⟩ := bd
  intro hstep
  cases Option.some.inj hstep
  rfl

theorem forRegTM_ne_halt {s : ForPhase ⊕ body.Q} (h : s ≠ .inl .done)
    {c : Cfg n (forRegTM body r).Q} (hst : c.state = s) :
    ¬ c.state = (forRegTM body r).qhalt := by
  rw [hst]
  show ¬ s = Sum.inl ForPhase.done
  exact h

/-- `test` over a mark: consume it (register head right) and enter the body. -/
theorem forRegTM_step_test_one (c : Cfg n (forRegTM body r).Q)
    (hst : c.state = .inl .test) (hone : (c.work r).read = Γ.one)
    (hinp : c.input.read ≠ Γ.start) (hwork : ∀ i, i ≠ r → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    (forRegTM body r).step c = some
      { state := .inr body.qstart, input := c.input,
        work := Function.update c.work r ((c.work r).move .right),
        output := c.output } := by
  rw [TM.step, ite_eq_right (forRegTM_ne_halt (by simp) hst)]
  simp only [forRegTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [ite_eq_left rfl, Function.update_self,
        writeAndMove_readBack _ (by rw [hone]; decide)]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact transitionTape_eq_self (hwork i hir)
  · exact transitionTape_eq_self hout

/-- `test` at the first blank: exit toward the rewind. -/
theorem forRegTM_step_test_blank (c : Cfg n (forRegTM body r).Q)
    (hst : c.state = .inl .test) (hblank : (c.work r).read = Γ.blank)
    (hinp : c.input.read ≠ Γ.start) (hwork : ∀ i, i ≠ r → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    (forRegTM body r).step c = some
      { state := .inl .rewind, input := c.input,
        work := Function.update c.work r ((c.work r).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (forRegTM_ne_halt (by simp) hst)]
  simp only [forRegTM, hst, hblank, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = r
    · subst hir
      simp only [↓reduceIte, Function.update_self]
      rw [writeAndMove_readBack _ (by rw [hblank]; decide)]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact transitionTape_eq_self (hwork i hir)
  · exact transitionTape_eq_self hout

/-- `rewind` off the sentinel: keep rewinding. -/
theorem forRegTM_step_rewind_left (c : Cfg n (forRegTM body r).Q)
    (hst : c.state = .inl .rewind) (hns : (c.work r).read ≠ Γ.start)
    (hinp : c.input.read ≠ Γ.start) (hwork : ∀ i, i ≠ r → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    (forRegTM body r).step c = some
      { state := .inl .rewind, input := c.input,
        work := Function.update c.work r ((c.work r).move .left),
        output := c.output } := by
  rw [TM.step, ite_eq_right (forRegTM_ne_halt (by simp) hst)]
  simp only [forRegTM, hst, hns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [ite_eq_left rfl, Function.update_self, writeAndMove_readBack _ hns]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact transitionTape_eq_self (hwork i hir)
  · exact transitionTape_eq_self hout

/-- `rewind` on the sentinel: step right to cell 1 and halt. -/
theorem forRegTM_step_rewind_start (c : Cfg n (forRegTM body r).Q)
    (hst : c.state = .inl .rewind) (hs : (c.work r).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work r).cells j ≠ Γ.start)
    (hinp : c.input.read ≠ Γ.start) (hwork : ∀ i, i ≠ r → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    (forRegTM body r).step c = some
      { state := .inl .done, input := c.input,
        work := Function.update c.work r ((c.work r).move .right),
        output := c.output } := by
  have h0 : (c.work r).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, ite_eq_right (forRegTM_ne_halt (by simp) hst)]
  simp only [forRegTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    by_cases hir : i = r
    · subst hir
      rw [ite_eq_left rfl, Function.update_self]
      show ((c.work i).write _).move Dir3.right = (c.work i).move .right
      congr 1
      rw [Tape.write, ite_eq_left h0]
    · rw [ite_eq_right hir, Function.update_of_ne hir]
      exact transitionTape_eq_self (hwork i hir)
  · exact transitionTape_eq_self hout

/-- The body has halted: one idle step loops back to the test. -/
theorem forRegTM_step_loopback (c : Cfg n (forRegTM body r).Q)
    (hst : c.state = .inr body.qhalt)
    (hinp : c.input.read ≠ Γ.start) (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    (forRegTM body r).step c = some
      { state := .inl .test, input := c.input, work := c.work,
        output := c.output } := by
  rw [TM.step, ite_eq_right (forRegTM_ne_halt (by simp) hst)]
  simp only [forRegTM, hst, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinp
  · funext i
    exact transitionTape_eq_self (hwork i)
  · exact transitionTape_eq_self hout

/-- The rewind loop: from `rewind` at head `h`, halt parked at cell 1 in
    `h + 1` steps. -/
theorem forRegTM_rewind_run (h : ℕ) :
    ∀ (c : Cfg n (forRegTM body r).Q),
      c.state = .inl .rewind → c.input.read ≠ Γ.start → (∀ i, i ≠ r → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work r).cells 0 = Γ.start →
      (∀ j, 1 ≤ j → (c.work r).cells j ≠ Γ.start) →
      (c.work r).head = h →
      ∃ c', (forRegTM body r).reachesIn (h + 1) c c' ∧
        c'.state = .inl .done ∧ c'.input = c.input ∧
        (∀ i, i ≠ r → c'.work i = c.work i) ∧
        (c'.work r).cells = (c.work r).cells ∧ (c'.work r).head = 1 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hs : (c.work r).read = Γ.start := by rw [Tape.read, hhead]; exact hc0
    have hstep := forRegTM_step_rewind_start c hst hs hcr hinp hwork hout
    refine ⟨_, .step hstep .zero, rfl, rfl, ?_, ?_, ?_, rfl⟩
    · intro i hi
      show Function.update c.work r ((c.work r).move .right) i = c.work i
      rw [Function.update_of_ne hi]
    · show (Function.update c.work r ((c.work r).move .right) r).cells = _
      rw [Function.update_self]
      rfl
    · show (Function.update c.work r ((c.work r).move .right) r).head = 1
      rw [Function.update_self]
      show (c.work r).head + 1 = 1
      rw [hhead]
  | succ h ih =>
    intro c hst hinp hwork hout hc0 hcr hhead
    have hns : (c.work r).read ≠ Γ.start := by
      rw [Tape.read, hhead]; exact hcr (h + 1) (by omega)
    have hstep := forRegTM_step_rewind_left c hst hns hinp hwork hout
    have hupd : (Function.update c.work r ((c.work r).move .left) r).cells
        = (c.work r).cells := by
      rw [Function.update_self]
      rfl
    obtain ⟨c', hreach, hst', hinp', hwork', hcells', hhead', hout'⟩ :=
      ih { state := .inl .rewind, input := c.input,
           work := Function.update c.work r ((c.work r).move .left),
           output := c.output } rfl hinp
        (fun i hi => by
          show (Function.update c.work r ((c.work r).move .left) i).read ≠ Γ.start
          rw [Function.update_of_ne hi]
          exact hwork i hi)
        hout
        (by rw [hupd]; exact hc0)
        (fun j hj => by rw [hupd]; exact hcr j hj)
        (by
          show (Function.update c.work r ((c.work r).move .left) r).head = h
          rw [Function.update_self]
          show (c.work r).head - 1 = h
          rw [hhead]
          omega)
    refine ⟨c', .step hstep hreach, hst', hinp', ?_, ?_, hhead', hout'⟩
    · intro i hi
      rw [hwork' i hi]
      show Function.update c.work r ((c.work r).move .left) i = c.work i
      rw [Function.update_of_ne hi]
    · rw [hcells', hupd]

end JointThermoComplexity.Complexity.CursorLoopSteps

#print axioms JointThermoComplexity.Complexity.CursorLoopSteps.forRegTM_rewind_run
