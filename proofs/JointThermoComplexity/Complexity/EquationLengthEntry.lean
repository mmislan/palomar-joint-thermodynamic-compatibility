module
public import proofs.JointThermoComplexity.Complexity.EquationLoopPolynomial
public import proofs.JointThermoComplexity.Complexity.CounterInputEntry

set_option autoImplicit false
@[expose] public section

/-! Measure the real input length into the three independent fixed registers from blank tapes. -/

namespace JointThermoComplexity.Complexity.EquationLengthEntry
open _root_.Complexity _root_.Complexity.TM
open HeaderAt (Cursor)

def values (L : ℕ) (j : Fin 32) : ℕ := if j = 4 ∨ j = 12 ∨ j = 16 then L else 0
def work (L : ℕ) (j : Fin 32) : Tape := regTape (values L j)

def Initial (input : List Bool) : _root_.Complexity.TM.TapePred 32 := fun inp tapes out =>
  inp = Tape.init (input.map Γ.ofBool) ∧ (∀ j, tapes j = Tape.init []) ∧ out = Tape.init []

def machine : TM 32 := seqTM (BoundedCounters.entry 4) (seqTM (inputLenRegTM 12) (inputLenRegTM 16))

theorem work_register (L : ℕ) (j : Fin 32) : IsReg (values L j) (work L j) := reg_regT _
theorem work_safe (L : ℕ) (j : Fin 32) : Parked (work L j) := (work_register L j).parked
theorem work_markers (L : ℕ) (j : Fin 32) : (work L j).cells 0 = Γ.start := (work_register L j).cell0

theorem hoareTime (input : List Bool) :
    machine.HoareTime (Initial input)
      (EmitPred ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩ (work input.length) []) (6 * input.length + 16) := by
  let first := BoundedCounters.inputWork (4 : Fin 32) input
  let second := Function.update first 12 (regTape input.length)
  have hsafe : ∀ j, Parked (first j) := by
    intro j
    simp only [first, BoundedCounters.inputWork, Function.update_apply]
    split <;> exact parked_regTape _
  have hsafe' : ∀ j, Parked (second j) := by
    intro j
    by_cases hj : j = 12
    · subst j
      simpa only [second, Function.update_self] using parked_regTape input.length
    · simpa only [second, Function.update_of_ne hj] using hsafe j
  have hfirst := BoundedCounters.entry_hoareTime (4 : Fin 32) input
  rw [BoundedCounters.inputWork_eq] at hfirst
  have hsecond := inputLenRegTM_hoareTime (12 : Fin 32) input first [] (fun j _ => hsafe j)
    (by simp [first, BoundedCounters.inputWork])
  have hthird := inputLenRegTM_hoareTime (16 : Fin 32) input second [] (fun j _ => hsafe' j)
    (by simp [second, first, BoundedCounters.inputWork])
  have hrest := seqTM_hoareTime (inputLenRegTM (12 : Fin 32)) (inputLenRegTM 16) hsecond
    (emitPred_transition (parked_init_input input) hsafe' []) hthird
  have hseq := seqTM_hoareTime (BoundedCounters.entry (4 : Fin 32))
    (seqTM (inputLenRegTM 12) (inputLenRegTM 16)) hfirst
    (emitPred_transition (parked_init_input input) hsafe []) hrest
  have heq : Function.update second 16 (regTape input.length) = work input.length := by
    funext j
    by_cases h16 : j = 16
    · subst j
      simp [work, values]
    · by_cases h12 : j = 12
      · subst j
        simp [second, work, values]
      · by_cases h4 : j = 4
        · subst j
          simp [second, first, BoundedCounters.inputWork, work, values]
        · simp [second, first, BoundedCounters.inputWork, work, values, h16, h12, h4]
  apply hseq.consequence (fun _ _ _ h => h)
  · rintro inp tapes out ⟨hi, hw, ho⟩
    exact ⟨hi, hw.trans heq, ho⟩
  · omega

end JointThermoComplexity.Complexity.EquationLengthEntry

#print axioms JointThermoComplexity.Complexity.EquationLengthEntry.hoareTime
