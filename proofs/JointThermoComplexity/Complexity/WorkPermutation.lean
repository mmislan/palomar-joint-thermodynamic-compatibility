module
public import proofs.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
public import proofs.Complexitylib.Models.TuringMachine.Hoare.Defs

set_option autoImplicit false
@[expose] public section

/-!
# Reassigning named work tapes

A finite permutation changes which physical tape a machine uses, with no extra
steps and no change to input or output. This lets the checked header counter
fill separate dimension registers without copying their unary contents.
-/

namespace JointThermoComplexity.Complexity.WorkPermutation
open _root_.Complexity
open _root_.Complexity.TM

variable {n : ℕ}

def cfg {Q : Type} (e : Fin n ≃ Fin n) (c : Cfg n Q) : Cfg n Q :=
  ⟨c.state, c.input, fun i => c.work (e.symm i), c.output⟩

@[simp] theorem cfg_inverse {Q : Type} (e : Fin n ≃ Fin n) (c : Cfg n Q) :
    cfg e.symm (cfg e c) = c := by
  apply Cfg.ext <;> simp [cfg]

def machine (e : Fin n ≃ Fin n) (tm : TM n) : TM n where
  Q := tm.Q
  qstart := tm.qstart
  qhalt := tm.qhalt
  δ q si sw so :=
    let (q', ww, ow, di, dw, dout) := tm.δ q si (fun i => sw (e i)) so
    (q', fun i => ww (e.symm i), ow, di, fun i => dw (e.symm i), dout)
  δ_right_of_start q si sw so := by
    have h := tm.δ_right_of_start q si (fun i => sw (e i)) so
    refine ⟨h.1, ?_, h.2.2⟩
    intro i hi
    exact h.2.1 (e.symm i) (by simpa using hi)

theorem step (e : Fin n ≃ Fin n) (tm : TM n) {c c' : Cfg n tm.Q}
    (hstep : tm.step c = some c') :
    (machine e tm).step (cfg e c) = some (cfg e c') := by
  have hne := state_ne_qhalt_of_step hstep
  simp only [TM.step, hne, ↓reduceIte] at hstep
  have hc := Option.some.inj hstep
  subst c'
  simp [TM.step, machine, cfg, hne]

theorem reaches (e : Fin n ≃ Fin n) (tm : TM n) {t : ℕ} {c c' : Cfg n tm.Q}
    (h : tm.reachesIn t c c') :
    (machine e tm).reachesIn t (cfg e c) (cfg e c') :=
  reachesIn_map (tm := tm) (tm' := machine e tm) (cfg e) (fun _ _ => step e tm) h

theorem halted (e : Fin n ≃ Fin n) (tm : TM n) {c : Cfg n tm.Q}
    (h : tm.halted c) : (machine e tm).halted (cfg e c) := h

theorem hoareTime (e : Fin n ≃ Fin n) (tm : TM n)
    (pre post : Tape → (Fin n → Tape) → Tape → Prop) (bound : ℕ)
    (h : tm.HoareTime pre post bound) :
    (machine e tm).HoareTime
      (fun inp work out => pre inp (fun i => work (e i)) out)
      (fun inp work out => post inp (fun i => work (e i)) out) bound := by
  intro inp work out hp
  obtain ⟨c', t, ht, hr, hh, hs⟩ := h inp (fun i => work (e i)) out hp
  refine ⟨cfg e c', t, ht, ?_, halted e tm hh, ?_⟩
  · simpa [cfg, machine] using reaches e tm hr
  · simpa [cfg] using hs

end JointThermoComplexity.Complexity.WorkPermutation

#print axioms JointThermoComplexity.Complexity.WorkPermutation.reaches
#print axioms JointThermoComplexity.Complexity.WorkPermutation.hoareTime
