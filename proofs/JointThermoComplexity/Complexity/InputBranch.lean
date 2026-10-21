module
public import proofs.JointThermoComplexity.Complexity.InputCursor

set_option autoImplicit false
@[expose] public section

/-! Consume an actual input tag and dispatch without copying that data tag into formula output. -/

namespace JointThermoComplexity.Complexity.InputBranch
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (yes no : TM w) : TM w where
  Q := Option (yes.Q ⊕ no.Q)
  qstart := none
  qhalt := some (.inl yes.qhalt)
  δ q si sw so := match q with
    | none => ((if si = Γ.one then some (.inl yes.qstart) else some (.inr no.qstart)),
      (fun j => readBackWrite (sw j)), readBackWrite so, .right,
      (fun j => idleDir (sw j)), idleDir so)
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
    | none => exact ⟨fun _ => rfl, fun _ hj => idleDir_right_of_start hj, idleDir_right_of_start⟩
    | some q =>
      cases q with
      | inl q => exact yes.δ_right_of_start q si sw so
      | inr q =>
        dsimp only
        split
        · exact rightOfStart_allReadBack si sw so
        · exact no.δ_right_of_start q si sw so

def wrapYes (yes no : TM w) (c : Cfg w yes.Q) : Cfg w (machine yes no).Q :=
  ⟨some (.inl c.state), c.input, c.work, c.output⟩

def wrapNo (yes no : TM w) (c : Cfg w no.Q) : Cfg w (machine yes no).Q :=
  ⟨some (.inr c.state), c.input, c.work, c.output⟩

theorem yes_step (yes no : TM w) {c d : Cfg w yes.Q} (h : yes.step c = some d) :
    (machine yes no).step (wrapYes yes no c) = some (wrapYes yes no d) := by
  have hne := state_ne_qhalt_of_step h
  simp only [TM.step, hne, ↓reduceIte] at h
  have hd := Option.some.inj h
  subst d
  simp [TM.step, machine, wrapYes, hne]

theorem no_step (yes no : TM w) {c d : Cfg w no.Q} (h : no.step c = some d) :
    (machine yes no).step (wrapNo yes no c) = some (wrapNo yes no d) := by
  have hne := state_ne_qhalt_of_step h
  simp only [TM.step, hne, ↓reduceIte] at h
  have hd := Option.some.inj h
  subst d
  simp [TM.step, machine, wrapNo, hne]

theorem yes_reaches (yes no : TM w) {c d : Cfg w yes.Q} {t : ℕ} (h : yes.reachesIn t c d) :
    (machine yes no).reachesIn t (wrapYes yes no c) (wrapYes yes no d) :=
  reachesIn_map (tm := yes) (tm' := machine yes no) (wrapYes yes no) (fun _ _ => yes_step yes no) h

theorem no_reaches (yes no : TM w) {c d : Cfg w no.Q} {t : ℕ} (h : no.reachesIn t c d) :
    (machine yes no).reachesIn t (wrapNo yes no c) (wrapNo yes no d) :=
  reachesIn_map (tm := no) (tm' := machine yes no) (wrapNo yes no) (fun _ _ => no_step yes no) h

theorem start_yes (yes no : TM w) (before input emitted : List Bool)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before (true :: input) emitted inp work out) :
    (machine yes no).step ⟨(machine yes no).qstart, inp, work, out⟩ =
      some (wrapYes yes no ⟨yes.qstart, inp.move .right, work, out⟩) := by
  have hf := InputCursor.read_bit true hc
  simp only [TM.step, machine, reduceCtorEq, ↓reduceIte, hf, Γ.ofBool]
  change some (⟨some (.inl yes.qstart), inp.move .right, (fun j => transitionTape (work j)), transitionTape out⟩ :
    Cfg w (Option (yes.Q ⊕ no.Q))) = _
  obtain ⟨_, hw, ho⟩ := hc.phase
  rw [hw, ho]
  rfl

theorem start_no (yes no : TM w) (before input emitted : List Bool)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before (false :: input) emitted inp work out) :
    (machine yes no).step ⟨(machine yes no).qstart, inp, work, out⟩ =
      some (wrapNo yes no ⟨no.qstart, inp.move .right, work, out⟩) := by
  have hf := InputCursor.read_bit false hc
  simp only [TM.step, machine, reduceCtorEq, ↓reduceIte, hf, Γ.ofBool]
  change some (⟨some (.inr no.qstart), inp.move .right, (fun j => transitionTape (work j)), transitionTape out⟩ :
    Cfg w (Option (yes.Q ⊕ no.Q))) = _
  obtain ⟨_, hw, ho⟩ := hc.phase
  rw [hw, ho]
  rfl

theorem finish_no (yes no : TM w) (before input emitted : List Bool)
    (c : Cfg w no.Q) (hh : no.halted c) (hc : Cursor before input emitted c.input c.work c.output) :
    (machine yes no).step (wrapNo yes no c) = some ⟨(machine yes no).qhalt, c.input, c.work, c.output⟩ := by
  change c.state = no.qhalt at hh
  simp only [TM.step, ↓reduceIte, machine, wrapNo, hh, allReadBack]
  change some (⟨some (.inl yes.qhalt), transitionInput c.input,
    (fun j => transitionTape (c.work j)), transitionTape c.output⟩ : Cfg w (Option (yes.Q ⊕ no.Q))) = _
  obtain ⟨hi, hw, ho⟩ := hc.phase
  rw [hi, hw, ho]

end JointThermoComplexity.Complexity.InputBranch

#print axioms JointThermoComplexity.Complexity.InputBranch.no_reaches
