module
public import proofs.JointThermoComplexity.Complexity.FlagBranchRun

set_option autoImplicit false
@[expose] public section

/-! Branch on an arbitrary retained work symbol without writing a test bit.
The existing branch-body simulation is reused; only dispatch is generalized.
-/

namespace JointThermoComplexity.Complexity.WorkSymbolBranch
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def machine (symbol : Γ) (flag : Fin w) (yes no : TM w) : TM w where
  Q := Option (yes.Q ⊕ no.Q)
  qstart := none
  qhalt := some (.inl yes.qhalt)
  δ q si sw so := match q with
    | none => allReadBack (if sw flag = symbol then some (.inl yes.qstart) else some (.inr no.qstart)) si sw so
    | some (.inl q) =>
      let a := yes.δ q si sw so
      (some (.inl a.1), a.2)
    | some (.inr q) =>
      if q = no.qhalt then allReadBack (some (.inl yes.qhalt)) si sw so
      else
        let a := no.δ q si sw so
        (some (.inr a.1), a.2)
  δ_right_of_start q si sw so := by
    cases q with
    | none => exact rightOfStart_allReadBack si sw so
    | some q =>
      cases q with
      | inl q => exact yes.δ_right_of_start q si sw so
      | inr q =>
        dsimp only
        split
        · exact rightOfStart_allReadBack si sw so
        · exact no.δ_right_of_start q si sw so

def wrapYes (symbol : Γ) (flag : Fin w) (yes no : TM w) (c : Cfg w yes.Q) : Cfg w (machine symbol flag yes no).Q :=
  ⟨some (.inl c.state), c.input, c.work, c.output⟩

def wrapNo (symbol : Γ) (flag : Fin w) (yes no : TM w) (c : Cfg w no.Q) : Cfg w (machine symbol flag yes no).Q :=
  ⟨some (.inr c.state), c.input, c.work, c.output⟩

theorem yes_step (symbol : Γ) (flag : Fin w) (yes no : TM w) {c d : Cfg w yes.Q}
    (h : yes.step c = some d) :
    (machine symbol flag yes no).step (wrapYes symbol flag yes no c) = some (wrapYes symbol flag yes no d) := by
  change (FlagBranch.machine flag yes no).step (FlagBranch.wrapYes flag yes no c) =
    some (FlagBranch.wrapYes flag yes no d)
  exact FlagBranch.yes_step flag yes no h

theorem no_step (symbol : Γ) (flag : Fin w) (yes no : TM w) {c d : Cfg w no.Q}
    (h : no.step c = some d) :
    (machine symbol flag yes no).step (wrapNo symbol flag yes no c) = some (wrapNo symbol flag yes no d) := by
  change (FlagBranch.machine flag yes no).step (FlagBranch.wrapNo flag yes no c) =
    some (FlagBranch.wrapNo flag yes no d)
  exact FlagBranch.no_step flag yes no h

theorem yes_reaches (symbol : Γ) (flag : Fin w) (yes no : TM w) {c d : Cfg w yes.Q} {t : ℕ}
    (h : yes.reachesIn t c d) :
    (machine symbol flag yes no).reachesIn t (wrapYes symbol flag yes no c) (wrapYes symbol flag yes no d) :=
  reachesIn_map (tm := yes) (tm' := machine symbol flag yes no) (wrapYes symbol flag yes no)
    (fun _ _ => yes_step symbol flag yes no) h

theorem no_reaches (symbol : Γ) (flag : Fin w) (yes no : TM w) {c d : Cfg w no.Q} {t : ℕ}
    (h : no.reachesIn t c d) :
    (machine symbol flag yes no).reachesIn t (wrapNo symbol flag yes no c) (wrapNo symbol flag yes no d) :=
  reachesIn_map (tm := no) (tm' := machine symbol flag yes no) (wrapNo symbol flag yes no)
    (fun _ _ => no_step symbol flag yes no) h

theorem start_yes (symbol : Γ) (flag : Fin w) (yes no : TM w) (before input emitted : List Bool)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before input emitted inp work out)
    (hf : (work flag).read = symbol) :
    (machine symbol flag yes no).step ⟨(machine symbol flag yes no).qstart, inp, work, out⟩ =
      some (wrapYes symbol flag yes no ⟨yes.qstart, inp, work, out⟩) := by
  simp only [TM.step, machine, reduceCtorEq, ↓reduceIte, hf, allReadBack]
  change some (⟨some (.inl yes.qstart), transitionInput inp, (fun j => transitionTape (work j)), transitionTape out⟩ :
    Cfg w (Option (yes.Q ⊕ no.Q))) = _
  obtain ⟨hi, hw, ho⟩ := hc.phase
  rw [hi, hw, ho]
  rfl

theorem start_no (symbol : Γ) (flag : Fin w) (yes no : TM w) (before input emitted : List Bool)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before input emitted inp work out)
    (hf : (work flag).read ≠ symbol) :
    (machine symbol flag yes no).step ⟨(machine symbol flag yes no).qstart, inp, work, out⟩ =
      some (wrapNo symbol flag yes no ⟨no.qstart, inp, work, out⟩) := by
  simp only [TM.step, machine, reduceCtorEq, ↓reduceIte, ite_eq_right hf, allReadBack]
  change some (⟨some (.inr no.qstart), transitionInput inp, (fun j => transitionTape (work j)), transitionTape out⟩ :
    Cfg w (Option (yes.Q ⊕ no.Q))) = _
  obtain ⟨hi, hw, ho⟩ := hc.phase
  rw [hi, hw, ho]
  rfl

theorem finish_no (symbol : Γ) (flag : Fin w) (yes no : TM w) (before input emitted : List Bool)
    (c : Cfg w no.Q) (hh : no.halted c) (hc : Cursor before input emitted c.input c.work c.output) :
    (machine symbol flag yes no).step (wrapNo symbol flag yes no c) =
      some ⟨(machine symbol flag yes no).qhalt, c.input, c.work, c.output⟩ := by
  change (FlagBranch.machine flag yes no).step (FlagBranch.wrapNo flag yes no c) =
    some ⟨(FlagBranch.machine flag yes no).qhalt, c.input, c.work, c.output⟩
  exact FlagBranch.finish_no flag yes no before input emitted c hh hc

theorem yes_hoareTime (symbol : Γ) (flag : Fin w) (yes no : TM w)
    (before input emitted before' input' emitted' : List Bool)
    (P Q : (Fin w → Tape) → Prop) (bound : ℕ)
    (h : yes.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) bound) :
    (machine symbol flag yes no).HoareTime
      (fun inp work out => (Cursor before input emitted inp work out ∧ P work) ∧ (work flag).read = symbol)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) (bound + 1) := by
  rintro inp work out ⟨⟨hc, hp⟩, hf⟩
  obtain ⟨d, t, ht, hr, hh, hpost⟩ := h inp work out ⟨hc, hp⟩
  have hs := start_yes symbol flag yes no before input emitted inp work out hc hf
  have hreach := TM.reachesIn.step hs (yes_reaches symbol flag yes no hr)
  refine ⟨wrapYes symbol flag yes no d, t + 1, by omega, hreach, ?_, hpost⟩
  change some (Sum.inl d.state) = some (Sum.inl yes.qhalt)
  rw [hh]

theorem no_hoareTime (symbol : Γ) (flag : Fin w) (yes no : TM w)
    (before input emitted before' input' emitted' : List Bool)
    (P Q : (Fin w → Tape) → Prop) (bound : ℕ)
    (h : no.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) bound) :
    (machine symbol flag yes no).HoareTime
      (fun inp work out => (Cursor before input emitted inp work out ∧ P work) ∧ (work flag).read ≠ symbol)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) (bound + 2) := by
  rintro inp work out ⟨⟨hc, hp⟩, hf⟩
  obtain ⟨d, t, ht, hr, hh, hpost⟩ := h inp work out ⟨hc, hp⟩
  have hs := start_no symbol flag yes no before input emitted inp work out hc hf
  have he := finish_no symbol flag yes no before' input' emitted' d hh hpost.1
  have hend : (machine symbol flag yes no).reachesIn 1 (wrapNo symbol flag yes no d)
      ⟨(machine symbol flag yes no).qhalt, d.input, d.work, d.output⟩ := .step he .zero
  have hbody := reachesIn_trans (machine symbol flag yes no) (no_reaches symbol flag yes no hr) hend
  exact ⟨⟨(machine symbol flag yes no).qhalt, d.input, d.work, d.output⟩, (t + 1) + 1,
    by omega, .step hs hbody, rfl, hpost⟩

end JointThermoComplexity.Complexity.WorkSymbolBranch

#print axioms JointThermoComplexity.Complexity.WorkSymbolBranch.yes_hoareTime
#print axioms JointThermoComplexity.Complexity.WorkSymbolBranch.no_hoareTime
