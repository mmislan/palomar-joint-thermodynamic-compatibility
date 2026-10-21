module
public import proofs.Complexitylib.Models.TuringMachine.Lift
public import proofs.Complexitylib.Models.TuringMachine.Hoare.Defs
public import proofs.Complexitylib.Models.TuringMachine.Registers

set_option autoImplicit false
@[expose] public section

/-! Lift a genuine blank-tape entry with its complete postcondition and fresh tapes. -/

namespace JointThermoComplexity.Complexity.InitialTapeLift
open _root_.Complexity _root_.Complexity.TM
variable {n : ℕ}

def Initial (w : ℕ) (input : List Bool) : _root_.Complexity.TM.TapePred w := fun inp work out =>
  inp = Tape.init (input.map Γ.ofBool) ∧ (∀ j, work j = Tape.init []) ∧ out = Tape.init []

def oldWork (m : ℕ) (work : Fin (n + m) → Tape) : Fin n → Tape := fun j => work (Fin.castAdd m j)

def Fresh (n m : ℕ) (work : Fin (n + m) → Tape) : Prop :=
  ∀ j, n ≤ j.val → work j = regTape 0

theorem hoareTime (tm : TM n) (m : ℕ) (input : List Bool) (Q : _root_.Complexity.TM.TapePred n)
    (B : ℕ) (h : tm.HoareTime (Initial n input) Q B) (hne : tm.qstart ≠ tm.qhalt) :
    (tm.liftTM m).HoareTime (Initial (n + m) input)
      (fun inp work out => Q inp (oldWork m work) out ∧ Fresh n m work) B := by
  rintro inp work out ⟨rfl, hw, rfl⟩
  have he : work = fun _ => Tape.init [] := funext hw
  subst work
  obtain ⟨c, t, ht, hr, hh, hq⟩ := h (Tape.init (input.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
    ⟨rfl, fun _ => rfl, rfl⟩
  change tm.reachesIn t (tm.initCfg input) c at hr
  have hpos : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := by omega
    subst t
    cases hr
    exact hne hh
  have hl := liftTM_reachesIn_initCfg_of_pos tm m input hpos hr
  have hold : oldWork m (tm.liftCfg m c).work = c.work := by
    funext j
    exact liftCfg_work_lt tm m c (Fin.castAdd m j) j.isLt
  refine ⟨tm.liftCfg m c, t, ht, hl, hh, ?_, ?_⟩
  · simpa only [liftCfg_input, liftCfg_output, hold] using hq
  · intro j hj
    rw [liftCfg_work_ge tm m c j hj]
    exact reg_zero_init_bumped.eq_regT

end JointThermoComplexity.Complexity.InitialTapeLift

#print axioms JointThermoComplexity.Complexity.InitialTapeLift.hoareTime
