module
public import proofs.JointThermoComplexity.Complexity.ScalarScanner

set_option autoImplicit false
@[expose] public section

/-! Fixed rational endpoints and closed boxes, retaining exact encoded factors. -/

namespace JointThermoComplexity.Complexity.BoxScanner
open _root_.Complexity
open _root_.Complexity.TM
open ScannerSpec

variable {n : ℕ}

def rationalMachine (master : Fin (n + 1)) : TM (n + 1) :=
  seqTM (IntegerField.machine master) (NaturalField.machine true master)

def machine (master : Fin (n + 1)) : TM (n + 1) := seqTM (rationalMachine master) (rationalMachine master)

def rationalTime (L : ℕ) : ℕ := (L + 5) + 1 + (L + 4)
def timeBound (L : ℕ) : ℕ := rationalTime L + 1 + rationalTime L

theorem rationalTime_mono : Monotone rationalTime := by
  intro a b h
  change (a + 5) + 1 + (a + 4) ≤ (b + 5) + 1 + (b + 4)
  omega

theorem timeBound_mono : Monotone timeBound := by
  intro a b h
  have hb := rationalTime_mono h
  dsimp [timeBound]
  omega

theorem rational_runs (master : Fin (n + 1)) (hm : master ≠ NaturalMachine.flagIndex n)
    (Env : (Fin (n + 1) → Tape) → Prop)
    (hEnv : ∀ work work',
      (∀ j, j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) → Env work → Env work') :
    Runs RecordControl.rational (rationalMachine master) master (NaturalMachine.flagIndex n) Env rationalTime := by
  have hi := ScalarScanner.integer_runs master hm Env hEnv
  have hp := ScalarScanner.natural_runs true master hm Env hEnv
  have hraw := product_runs hi hp (by
    intro a b h
    change a + 4 ≤ b + 4
    omega)
  exact transport_runs DataCodec.rationalEquiv hraw

theorem runs (master : Fin (n + 1)) (hm : master ≠ NaturalMachine.flagIndex n)
    (Env : (Fin (n + 1) → Tape) → Prop)
    (hEnv : ∀ work work',
      (∀ j, j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) → Env work → Env work') :
    Runs RecordControl.box (machine master) master (NaturalMachine.flagIndex n) Env timeBound := by
  have hr := rational_runs master hm Env hEnv
  exact transport_runs DataCodec.boxEquiv (product_runs hr hr rationalTime_mono)

theorem timeBound_eq (L : ℕ) : timeBound L = 4 * L + 21 := by
  dsimp [timeBound, rationalTime]
  omega

end JointThermoComplexity.Complexity.BoxScanner

#print axioms JointThermoComplexity.Complexity.BoxScanner.rational_runs
#print axioms JointThermoComplexity.Complexity.BoxScanner.runs
