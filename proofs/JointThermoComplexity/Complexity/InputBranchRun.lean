module
public import proofs.JointThermoComplexity.Complexity.InputBranch

set_option autoImplicit false
@[expose] public section

/-! Prepared-cursor execution rules for non-emitting actual-input dispatch. -/

namespace JointThermoComplexity.Complexity.InputBranchRun
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InputBranch

variable {w : ℕ}

theorem yes_hoareTime (yes no : TM w) (before input emitted before' input' emitted' : List Bool)
    (P Q : (Fin w → Tape) → Prop) (bound : ℕ)
    (h : yes.HoareTime
      (fun inp work out => Cursor (before ++ [true]) input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) bound) :
    (machine yes no).HoareTime
      (fun inp work out => Cursor before (true :: input) emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) (bound + 1) := by
  rintro inp work out ⟨hc, hp⟩
  obtain ⟨d, t, ht, hr, hh, hpost⟩ := h (inp.move .right) work out ⟨InputCursor.consume true hc, hp⟩
  have hs := start_yes yes no before input emitted inp work out hc
  have hreach := TM.reachesIn.step hs (yes_reaches yes no hr)
  refine ⟨wrapYes yes no d, t + 1, by omega, hreach, ?_, hpost⟩
  change some (Sum.inl d.state) = some (Sum.inl yes.qhalt)
  rw [hh]

theorem no_hoareTime (yes no : TM w) (before input emitted before' input' emitted' : List Bool)
    (P Q : (Fin w → Tape) → Prop) (bound : ℕ)
    (h : no.HoareTime
      (fun inp work out => Cursor (before ++ [false]) input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) bound) :
    (machine yes no).HoareTime
      (fun inp work out => Cursor before (false :: input) emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) (bound + 2) := by
  rintro inp work out ⟨hc, hp⟩
  obtain ⟨d, t, ht, hr, hh, hpost⟩ := h (inp.move .right) work out ⟨InputCursor.consume false hc, hp⟩
  have hs := start_no yes no before input emitted inp work out hc
  have he := finish_no yes no before' input' emitted' d hh hpost.1
  have hend : (machine yes no).reachesIn 1 (wrapNo yes no d)
      ⟨(machine yes no).qhalt, d.input, d.work, d.output⟩ := .step he .zero
  have hbody := reachesIn_trans (machine yes no) (no_reaches yes no hr) hend
  exact ⟨⟨(machine yes no).qhalt, d.input, d.work, d.output⟩, (t + 1) + 1,
    by omega, .step hs hbody, rfl, hpost⟩

end JointThermoComplexity.Complexity.InputBranchRun

#print axioms JointThermoComplexity.Complexity.InputBranchRun.yes_hoareTime
#print axioms JointThermoComplexity.Complexity.InputBranchRun.no_hoareTime
