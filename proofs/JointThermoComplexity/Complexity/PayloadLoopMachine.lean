module
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Uniform flag/bit-pair control: run a supplied bit-consuming body after each true flag. -/

namespace JointThermoComplexity.Complexity.PayloadLoopMachine
open _root_.Complexity
open _root_.Complexity.TM

variable {w : ℕ}

def advance (body : TM w) (next : Bool ⊕ body.Q) (_si : Γ) (sw : Fin w → Γ) (so : Γ) :
    (Bool ⊕ body.Q) × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (next, (fun j => readBackWrite (sw j)), readBackWrite so, .right, (fun j => idleDir (sw j)), idleDir so)

theorem advance_right (body : TM w) (next : Bool ⊕ body.Q) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    let (_, _, _, di, dw, dout) := advance body next si sw so
    (si = Γ.start → di = .right) ∧ (∀ j, sw j = Γ.start → dw j = .right) ∧ (so = Γ.start → dout = .right) :=
  ⟨fun _ => rfl, fun _ hj => idleDir_right_of_start hj, idleDir_right_of_start⟩

def machine (body : TM w) : TM w where
  Q := Bool ⊕ body.Q
  qstart := .inl false
  qhalt := .inl true
  δ q si sw so := match q with
    | .inl false => match si with
      | .one => advance body (.inr body.qstart) si sw so
      | .zero => advance body (.inl true) si sw so
      | _ => allReadBack (.inl true) si sw so
    | .inl true => allReadBack (.inl true) si sw so
    | .inr q =>
      if q = body.qhalt then allReadBack (.inl false) si sw so
      else
        let a := body.δ q si sw so
        (.inr a.1, a.2)
  δ_right_of_start q si sw so := by
    cases q with
    | inl bit =>
      cases bit <;> cases si <;> first
        | exact advance_right body (.inl true) .zero sw so
        | exact advance_right body (.inr body.qstart) .one sw so
        | exact rightOfStart_allReadBack _ sw so
    | inr q =>
      dsimp only
      split
      · exact rightOfStart_allReadBack si sw so
      · exact body.δ_right_of_start q si sw so

def wrap (body : TM w) (c : Cfg w body.Q) : Cfg w (machine body).Q :=
  ⟨.inr c.state, c.input, c.work, c.output⟩

theorem body_step (body : TM w) {c d : Cfg w body.Q} (h : body.step c = some d) :
    (machine body).step (wrap body c) = some (wrap body d) := by
  have hne := state_ne_qhalt_of_step h
  simp only [TM.step, hne, ↓reduceIte] at h
  have hd := Option.some.inj h
  subst d
  simp [TM.step, machine, wrap, hne]

theorem body_reaches (body : TM w) {c d : Cfg w body.Q} {t : ℕ} (h : body.reachesIn t c d) :
    (machine body).reachesIn t (wrap body c) (wrap body d) :=
  reachesIn_map (tm := body) (tm' := machine body) (wrap body) (fun _ _ => body_step body) h

end JointThermoComplexity.Complexity.PayloadLoopMachine

#print axioms JointThermoComplexity.Complexity.PayloadLoopMachine.body_reaches
