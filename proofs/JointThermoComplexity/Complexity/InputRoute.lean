module
public import proofs.JointThermoComplexity.Complexity.OutputRoute
public import proofs.Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget

set_option autoImplicit false
@[expose] public section

/-! Virtual-input simulation with exact preservation of a parked real input. -/

namespace JointThermoComplexity.Complexity.InputRoute
open _root_.Complexity
open _root_.Complexity.TM

variable {w : ℕ}

theorem step (tm : TM w) (inp : Tape) (hi : inp.read ≠ Γ.start)
    {c d : Cfg w tm.Q} (h : tm.step c = some d) (hs : Tape.StartInvariant c.input) :
    tm.retargetInput.step (retargetWrap tm inp c) = some (retargetWrap tm inp d) := by
  have he : inp.move (idleDir inp.read) = inp := by simp [idleDir, hi, Tape.move]
  simpa only [he] using retargetInput_step_commute tm h inp hs

theorem reaches (tm : TM w) (inp : Tape) (hi : inp.read ≠ Γ.start)
    {t : ℕ} {c d : Cfg w tm.Q} (h : tm.reachesIn t c d)
    (hinput : Tape.StartInvariant c.input) (hwork : ∀ j, Tape.StartInvariant (c.work j))
    (hout : Tape.StartInvariant c.output) :
    tm.retargetInput.reachesIn t (retargetWrap tm inp c) (retargetWrap tm inp d) := by
  induction h with
  | zero => exact .zero
  | step hs _ ih =>
    obtain ⟨hin', hw', ho'⟩ := Tape.StartInvariant.step tm hs hinput hwork hout
    exact .step (step tm inp hi hs hinput) (ih hin' hw' ho')

theorem hoareTime (tm : TM w) (pre post : _root_.Complexity.TM.TapePred w) (bound : ℕ) (S : Tape → Prop)
    (h : tm.HoareTime pre post bound)
    (hinput : ∀ inp work out, pre inp work out → Tape.StartInvariant inp)
    (hwork : ∀ inp work out, pre inp work out → ∀ j, Tape.StartInvariant (work j))
    (hout : ∀ inp work out, pre inp work out → Tape.StartInvariant out) :
    tm.retargetInput.HoareTime
      (fun inp work out => inp.read ≠ Γ.start ∧ S inp ∧
        pre (work (Fin.last w)) (fun j => work j.castSucc) out)
      (fun inp work out => inp.read ≠ Γ.start ∧ S inp ∧
        post (work (Fin.last w)) (fun j => work j.castSucc) out) bound := by
  rintro inp work out ⟨hi, hs, hp⟩
  obtain ⟨d, t, ht, hr, hh, hpost⟩ := h (work (Fin.last w)) (fun j => work j.castSucc) out hp
  have hstart : retargetWrap tm inp ⟨tm.qstart, work (Fin.last w), (fun j => work j.castSucc), out⟩ =
      ⟨tm.retargetInput.qstart, inp, work, out⟩ := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      by_cases hj : j.val < w
      · simp only [retargetWrap, hj, ↓reduceDIte]
        rfl
      · have he : j = Fin.last w := by apply Fin.ext; simp only [Fin.val_last]; omega
        subst j
        simp only [retargetWrap, Fin.val_last, Nat.lt_irrefl, ↓reduceDIte]
    · rfl
  refine ⟨retargetWrap tm inp d, t, ht, ?_, hh, hi, hs, ?_⟩
  · rw [← hstart]
    exact reaches tm inp hi hr (hinput _ _ _ hp) (hwork _ _ _ hp) (hout _ _ _ hp)
  · change post ((retargetWrap tm inp d).work (Fin.last w))
      (fun j => (retargetWrap tm inp d).work j.castSucc) d.output
    have hlast : (retargetWrap tm inp d).work (Fin.last w) = d.input :=
      retargetWrap_work_last tm inp d
    have hsub : (fun j : Fin w => (retargetWrap tm inp d).work j.castSucc) = d.work := by
      funext j
      exact retargetWrap_work_lt tm inp d j.castSucc j.isLt
    rw [hlast, hsub]
    exact hpost

end JointThermoComplexity.Complexity.InputRoute

#print axioms JointThermoComplexity.Complexity.InputRoute.reaches
#print axioms JointThermoComplexity.Complexity.InputRoute.hoareTime
