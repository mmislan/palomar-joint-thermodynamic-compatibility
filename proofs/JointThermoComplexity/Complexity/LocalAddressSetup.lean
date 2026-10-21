module
public import proofs.JointThermoComplexity.Complexity.AddressCounterPlacement
public import proofs.JointThermoComplexity.Complexity.LocalEquationTemplates

set_option autoImplicit false
@[expose] public section

/-! Ten fixed counter instructions prepare exact child and witness addresses in ports19..24. -/

namespace JointThermoComplexity.Complexity.LocalAddressSetup
open _root_.Complexity _root_.Complexity.TM HeaderAt AddressCounterPlacement
open DInstabilityComplexity.MachineConstruction

def program : CounterProgram 9 :=
  [.copy 0 1 (by decide), .increment 1, .copy 1 2 (by decide), .add 6 2 (by decide),
    .copy 2 3 (by decide), .add 7 3 (by decide), .copy 3 4 (by decide), .increment 4,
    .copy 4 5 (by decide), .increment 5]

def prepared (v : Fin 9 → ℕ) : Fin 9 → ℕ :=
  ![v 0, v 0 + 1, v 0 + 1 + v 6, v 0 + 1 + v 6 + v 7,
    v 0 + 1 + v 6 + v 7 + 1, v 0 + 1 + v 6 + v 7 + 2, v 6, v 7, v 8]

theorem program_eval (v : Fin 9 → ℕ) : counterProgramEval program v = prepared v := by
  funext i
  fin_cases i <;> simp [program, counterProgramEval, CounterInstruction.eval, prepared, Nat.add_assoc]

theorem program_length : program.length = 10 := rfl

def addressValues (v : Fin 9 → ℕ) (i : Fin 6) : ℕ := prepared v ⟨i.val, by omega⟩
def addressPorts (i : Fin 6) : Fin 32 := slot ⟨i.val, by omega⟩

theorem addressValues_eq (v : Fin 9 → ℕ) :
    addressValues v = LocalEquationTemplates.formulaValues (v 0) (v 6) (v 7) := by
  funext i
  fin_cases i <;> rfl

theorem prepared_bound (v : Fin 9 → ℕ) (B : ℕ) (hv : ∀ i, v i ≤ B) : ∀ i, prepared v i ≤ 3 * B + 3 := by
  intro i
  have h0 := hv 0
  have h6 := hv 6
  have h7 := hv 7
  have h8 := hv 8
  fin_cases i <;> (dsimp [prepared]; omega)

def machine : TM 32 := AddressCounterPlacement.machine program

theorem hoareTime (v : Fin 9 → ℕ) (B : ℕ) (hv : ∀ i, v i ≤ B) (before input emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) (hR : Stable R) :
    machine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Registers v work ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Registers (prepared v) work ∧ R work)
      (counterIterTime 10 B) := by
  simpa only [machine, program_eval, program_length] using AddressCounterPlacement.bounded_hoareTime program v B hv before input emitted R hR

end JointThermoComplexity.Complexity.LocalAddressSetup

#print axioms JointThermoComplexity.Complexity.LocalAddressSetup.program_eval
#print axioms JointThermoComplexity.Complexity.LocalAddressSetup.hoareTime
