module
public import proofs.JointThermoComplexity.Complexity.ScannerSpec
public import proofs.JointThermoComplexity.Complexity.NaturalArray
public import proofs.JointThermoComplexity.Complexity.IntegerField

set_option autoImplicit false
@[expose] public section

/-! Concrete scalar-machine instances of the compositional record specification. -/

namespace JointThermoComplexity.Complexity.ScalarScanner
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ScannerSpec

variable {n : ℕ}

theorem natural_runs (requirePositive : Bool) (master : Fin (n + 1))
    (hm : master ≠ NaturalMachine.flagIndex n) (Env : (Fin (n + 1) → Tape) → Prop)
    (hEnv : ∀ work work',
      (∀ j, j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) → Env work → Env work') :
    Runs (NaturalArray.control requirePositive) (NaturalField.machine requirePositive master)
      master (NaturalMachine.flagIndex n) Env (fun L => L + 4) := by
  intro initial before input emitted R hR
  let RE : (Fin (n + 1) → Tape) → Prop := fun work => Env work ∧ R work
  have hRE : ∀ work work',
      (∀ j, j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) → RE work → RE work' := by
    rintro work work' h ⟨he, hr⟩
    exact ⟨hEnv work work' h he, hR work work' h hr⟩
  have hscan := NaturalField.hoareTime requirePositive initial master hm before input emitted RE hRE
  apply HoareTime.strengthen_post hscan
  rintro inp work out ⟨hc, hf, _, hmh, hmr, he, hr⟩
  refine ⟨?_, hf, hmh, ?_, he, hr⟩
  · simpa only [NaturalArray.taken_eq, NaturalArray.rest_eq] using hc
  · simpa only [NaturalArray.valid_eq] using hmr

theorem integer_runs (master : Fin (n + 1)) (hm : master ≠ NaturalMachine.flagIndex n)
    (Env : (Fin (n + 1) → Tape) → Prop)
    (hEnv : ∀ work work',
      (∀ j, j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) → Env work → Env work') :
    Runs FieldControl.integer (IntegerField.machine master) master (NaturalMachine.flagIndex n) Env (fun L => L + 5) := by
  intro initial before input emitted R hR
  let RE : (Fin (n + 1) → Tape) → Prop := fun work => Env work ∧ R work
  have hRE : ∀ work work',
      (∀ j, j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) → RE work → RE work' := by
    rintro work work' h ⟨he, hr⟩
    exact ⟨hEnv work work' h he, hR work work' h hr⟩
  have hscan := IntegerField.hoareTime initial master hm before input emitted RE hRE
  apply HoareTime.strengthen_post hscan
  rintro inp work out ⟨hc, hf, _, hmh, hmr, he, hr⟩
  exact ⟨hc, hf, hmh, hmr, he, hr⟩

end JointThermoComplexity.Complexity.ScalarScanner

#print axioms JointThermoComplexity.Complexity.ScalarScanner.natural_runs
#print axioms JointThermoComplexity.Complexity.ScalarScanner.integer_runs
