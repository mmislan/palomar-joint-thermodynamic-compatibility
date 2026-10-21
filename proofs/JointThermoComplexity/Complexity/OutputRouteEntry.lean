module
public import proofs.JointThermoComplexity.Complexity.OutputRoute

set_option autoImplicit false
@[expose] public section

/-! Fresh-input output routing, exposing all retained work tapes and input cells. -/

namespace JointThermoComplexity.Complexity.OutputRouteEntry
open _root_.Complexity
open _root_.Complexity.TM
open OutputRoute

variable {w : ℕ}

theorem step (tm : TM w) (out : Tape) {c d : Cfg w tm.Q} (h : tm.step c = some d) :
    tm.retargetOutput.step (cfg tm out c) = some (cfg tm (transitionTape out) d) := by
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
  · rfl

theorem cfg_init (tm : TM w) (input : List Bool) :
    cfg tm (Tape.init []) (tm.initCfg input) = tm.retargetOutput.initCfg input := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    simp only [cfg, retargetCfg]
    split <;> rfl
  · rfl

theorem init_reaches (tm : TM w) (input : List Bool) {d : Cfg w tm.Q} {t : ℕ}
    (h : tm.reachesIn t (tm.initCfg input) d) (ht : 0 < t) :
    tm.retargetOutput.reachesIn t (tm.retargetOutput.initCfg input)
      (cfg tm ((Tape.init []).move Dir3.right) d) := by
  cases h with
  | zero => omega
  | step hs hr =>
    have hh := step tm (Tape.init []) hs
    have hz : transitionTape (Tape.init []) = (Tape.init []).move Dir3.right := rfl
    rw [cfg_init, hz] at hh
    refine .step hh ?_
    apply OutputRoute.reaches tm ((Tape.init []).move Dir3.right) ?_ hr
    simp [Tape.move, Tape.init, Tape.read]

end JointThermoComplexity.Complexity.OutputRouteEntry

#print axioms JointThermoComplexity.Complexity.OutputRouteEntry.init_reaches
