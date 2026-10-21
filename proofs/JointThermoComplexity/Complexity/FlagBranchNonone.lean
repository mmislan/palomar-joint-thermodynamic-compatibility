module
public import proofs.JointThermoComplexity.Complexity.FlagBranchRun

set_option autoImplicit false
@[expose] public section

/-! The retained-flag branch selects its no arm for every symbol other than one. -/

namespace JointThermoComplexity.Complexity.FlagBranchNonone
open _root_.Complexity _root_.Complexity.TM HeaderAt FlagBranch
variable {w : ℕ}

theorem start_no (flag : Fin w) (yes no : TM w) (before input emitted : List Bool)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before input emitted inp work out)
    (hf : (work flag).read ≠ Γ.one) :
    (machine flag yes no).step ⟨(machine flag yes no).qstart, inp, work, out⟩ =
      some (wrapNo flag yes no ⟨no.qstart, inp, work, out⟩) := by
  simp only [TM.step, FlagBranch.machine, reduceCtorEq, ↓reduceIte, ite_eq_right hf, allReadBack]
  change some (⟨some (.inr no.qstart), transitionInput inp, (fun j => transitionTape (work j)), transitionTape out⟩ :
    Cfg w (Option (yes.Q ⊕ no.Q))) = _
  obtain ⟨hi, hw, ho⟩ := hc.phase
  rw [hi, hw, ho]
  rfl

theorem hoareTime (flag : Fin w) (yes no : TM w)
    (before input emitted before' input' emitted' : List Bool)
    (P Q : (Fin w → Tape) → Prop) (bound : ℕ)
    (h : no.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) bound) :
    (machine flag yes no).HoareTime
      (fun inp work out => (Cursor before input emitted inp work out ∧ P work) ∧ (work flag).read ≠ Γ.one)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) (bound + 2) := by
  rintro inp work out ⟨⟨hc, hp⟩, hf⟩
  obtain ⟨d, t, ht, hr, hh, hpost⟩ := h inp work out ⟨hc, hp⟩
  have hs := start_no flag yes no before input emitted inp work out hc hf
  have he := finish_no flag yes no before' input' emitted' d hh hpost.1
  have hend : (machine flag yes no).reachesIn 1 (wrapNo flag yes no d)
      ⟨(machine flag yes no).qhalt, d.input, d.work, d.output⟩ := .step he .zero
  have hbody := reachesIn_trans (machine flag yes no) (no_reaches flag yes no hr) hend
  exact ⟨⟨(machine flag yes no).qhalt, d.input, d.work, d.output⟩, (t + 1) + 1,
    by omega, .step hs hbody, rfl, hpost⟩

end JointThermoComplexity.Complexity.FlagBranchNonone

#print axioms JointThermoComplexity.Complexity.FlagBranchNonone.hoareTime
