module
public import proofs.JointThermoComplexity.Complexity.FlagBranch

set_option autoImplicit false
@[expose] public section

/-! Runtime rules for a retained-flag branch; dispatch never emits a test bit. -/

namespace JointThermoComplexity.Complexity.FlagBranchRun
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt FlagBranch

variable {w : ℕ}

theorem yes_hoareTime (flag : Fin w) (yes no : TM w)
    (before input emitted before' input' emitted' : List Bool)
    (P Q : (Fin w → Tape) → Prop) (bound : ℕ)
    (h : yes.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) bound) :
    (machine flag yes no).HoareTime
      (fun inp work out => (Cursor before input emitted inp work out ∧ P work) ∧ (work flag).read = Γ.one)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) (bound + 1) := by
  rintro inp work out ⟨⟨hc, hp⟩, hf⟩
  obtain ⟨d, t, ht, hr, hh, hpost⟩ := h inp work out ⟨hc, hp⟩
  have hs := start_yes flag yes no before input emitted inp work out hc hf
  have hreach := (TM.reachesIn.step hs (yes_reaches flag yes no hr))
  refine ⟨wrapYes flag yes no d, t + 1, by omega, hreach, ?_, hpost⟩
  change some (Sum.inl d.state) = some (Sum.inl yes.qhalt)
  rw [hh]

theorem no_hoareTime (flag : Fin w) (yes no : TM w)
    (before input emitted before' input' emitted' : List Bool)
    (P Q : (Fin w → Tape) → Prop) (bound : ℕ)
    (h : no.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) bound) :
    (machine flag yes no).HoareTime
      (fun inp work out => (Cursor before input emitted inp work out ∧ P work) ∧ (work flag).read = Γ.zero)
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

end JointThermoComplexity.Complexity.FlagBranchRun

#print axioms JointThermoComplexity.Complexity.FlagBranchRun.no_hoareTime
