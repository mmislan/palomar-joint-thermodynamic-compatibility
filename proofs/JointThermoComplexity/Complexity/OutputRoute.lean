module
public import proofs.JointThermoComplexity.Complexity.WorkPermutation
public import proofs.Complexitylib.Models.TuringMachine.Lift

set_option autoImplicit false
@[expose] public section

/-!
# Output routing with an arbitrary surrounding output accumulator

The adopted `retargetOutput` machine routes its virtual output to the last work
tape. This frame exposes exact runs while preserving a real output tape whose
current head is past the left marker. No extra machine steps are introduced.
-/

namespace JointThermoComplexity.Complexity.OutputRoute
open _root_.Complexity
open _root_.Complexity.TM

variable {w : ℕ}

def cfg (tm : TM w) (out : Tape) (c : Cfg w tm.Q) : Cfg (w + 1) tm.retargetOutput.Q :=
  {tm.retargetCfg c with output := out}

@[simp] theorem cfg_work (tm : TM w) (out : Tape) (c : Cfg w tm.Q) (j : Fin w) :
    (cfg tm out c).work j.castSucc = c.work j := by
  exact tm.retargetCfg_work_lt c j.castSucc j.isLt

@[simp] theorem cfg_last (tm : TM w) (out : Tape) (c : Cfg w tm.Q) :
    (cfg tm out c).work (Fin.last w) = c.output := tm.retargetCfg_work_last c

theorem step (tm : TM w) (out : Tape) (ho : out.read ≠ Γ.start)
    {c d : Cfg w tm.Q} (h : tm.step c = some d) :
    tm.retargetOutput.step (cfg tm out c) = some (cfg tm out d) := by
  have hne := state_ne_qhalt_of_step h
  simp only [TM.step, hne, ↓reduceIte] at h
  have hd := Option.some.inj h
  subst d
  have hw : (fun j : Fin w => ((cfg tm out c).work j.castSucc).read) = fun j => (c.work j).read := by
    funext j
    rw [cfg_work]
  have hl := cfg_last tm out c
  simp only [TM.step, retargetOutput, cfg, retargetCfg, hne, ↓reduceIte] at hw hl ⊢
  rw [hw, hl]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    by_cases hj : j.val < w
    · simp only [hj, ↓reduceDIte]
    · simp only [hj, ↓reduceDIte]
  · exact transitionTape_eq_self ho

theorem reaches (tm : TM w) (out : Tape) (ho : out.read ≠ Γ.start)
    {t : ℕ} {c d : Cfg w tm.Q} (h : tm.reachesIn t c d) :
    tm.retargetOutput.reachesIn t (cfg tm out c) (cfg tm out d) := by
  induction h with
  | zero => exact .zero
  | step hs _ ih => exact .step (step tm out ho hs) ih

theorem hoareTime (tm : TM w) (pre post : _root_.Complexity.TM.TapePred w) (bound : ℕ) (S : Tape → Prop)
    (h : tm.HoareTime pre post bound) :
    tm.retargetOutput.HoareTime
      (fun inp work out => out.read ≠ Γ.start ∧ S out ∧ pre inp (fun j => work j.castSucc) (work (Fin.last w)))
      (fun inp work out => out.read ≠ Γ.start ∧ S out ∧ post inp (fun j => work j.castSucc) (work (Fin.last w))) bound := by
  rintro inp work out ⟨ho, hs, hp⟩
  obtain ⟨d, t, ht, hr, hh, hpost⟩ := h inp (fun j => work j.castSucc) (work (Fin.last w)) hp
  have hstart : cfg tm out ⟨tm.qstart, inp, (fun j => work j.castSucc), work (Fin.last w)⟩ =
      ⟨tm.retargetOutput.qstart, inp, work, out⟩ := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      by_cases hj : j.val < w
      · simp only [cfg, retargetCfg, hj, ↓reduceDIte]
        rfl
      · have he : j = Fin.last w := by apply Fin.ext; simp only [Fin.val_last]; omega
        subst j
        simp only [cfg, retargetCfg, Fin.val_last, Nat.lt_irrefl, ↓reduceDIte]
    · rfl
  refine ⟨cfg tm out d, t, ht, ?_, hh, ho, hs, ?_⟩
  · rw [← hstart]
    exact reaches tm out ho hr
  · change post d.input (fun j => (cfg tm out d).work j.castSucc) ((cfg tm out d).work (Fin.last w))
    simpa only [cfg_work, cfg_last] using hpost

end JointThermoComplexity.Complexity.OutputRoute

#print axioms JointThermoComplexity.Complexity.OutputRoute.hoareTime
