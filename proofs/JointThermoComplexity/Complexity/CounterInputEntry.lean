module
public import proofs.DInstabilityComplexity.CounterProgramSyntax
public import proofs.Complexitylib.Models.TuringMachine.Registers.InputLen

set_option autoImplicit false
@[expose] public section

/-! Initial-tape entry for the reviewed generic counter compiler. The input
length is measured by an actual machine while preserving the original word. -/

namespace JointThermoComplexity.Complexity.BoundedCounters
open _root_.Complexity _root_.Complexity.TM
open DInstabilityComplexity.MachineConstruction
variable {n : ℕ}

def initialValues (q : Fin n) (L : ℕ) : Fin n → ℕ := Function.update (fun _ => 0) q L

theorem initialValues_le (q : Fin n) (L : ℕ) : ∀ j, initialValues q L j ≤ L := by
  intro j
  by_cases hj : j = q
  · subst j; simpa only [initialValues, Function.update_self] using Nat.le_refl L
  · simp only [initialValues, Function.update_of_ne hj]; exact Nat.zero_le _

def inputWork (q : Fin n) (input : List Bool) : Fin n → Tape :=
  Function.update (fun _ => regTape 0) q (regTape input.length)

theorem inputWork_eq (q : Fin n) (input : List Bool) :
    counterValues (initialValues q input.length) = inputWork q input := by
  rw [initialValues, counterValues_update]
  rfl

def entry (q : Fin n) : TM n := seqTM bumpTM (inputLenRegTM q)

theorem entry_hoareTime (q : Fin n) (input : List Bool) :
    (entry q).HoareTime
      (fun inp work out => inp = Tape.init (input.map Γ.ofBool) ∧
        (∀ j, work j = Tape.init []) ∧ out = Tape.init [])
      (EmitPred ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩ (counterValues (initialValues q input.length)) [])
      (2 * input.length + 6) := by
  let inp : Tape := ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩
  let work : Fin n → Tape := fun _ => regTape 0
  have hi := parked_init_input input
  have hw : ∀ j, Parked (work j) := fun _ => parked_regTape 0
  have hb := bumpTM_hoareTime (n := n) input
  have hb' : (bumpTM (n := n)).HoareTime
      (fun inp work out => inp = Tape.init (input.map Γ.ofBool) ∧
        (∀ j, work j = Tape.init []) ∧ out = Tape.init []) (EmitPred inp work []) 1 := by
    apply hb.strengthen_post
    rintro inp work out ⟨hinp, hwork, hout⟩
    exact ⟨hinp, funext (fun j => (hwork j).eq_regT), hout⟩
  have hl := inputLenRegTM_hoareTime q input work [] (fun j _ => hw j) rfl
  have hall := seqTM_hoareTime (bumpTM (n := n)) (inputLenRegTM q) hb'
    (emitPred_transition hi hw []) hl
  rw [inputWork_eq]
  exact hall.mono_bound (by omega)

end JointThermoComplexity.Complexity.BoundedCounters

#print axioms JointThermoComplexity.Complexity.BoundedCounters.entry_hoareTime
