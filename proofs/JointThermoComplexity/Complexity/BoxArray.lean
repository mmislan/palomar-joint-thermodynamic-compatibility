module
public import proofs.JointThermoComplexity.Complexity.OptionalScanner
public import proofs.JointThermoComplexity.Complexity.BoxScanner
public import proofs.JointThermoComplexity.Complexity.ScannerArray

set_option autoImplicit false
@[expose] public section

/-! Optional closed boxes for every species, on the actual binary machine. -/

namespace JointThermoComplexity.Complexity.BoxArray
open _root_.Complexity
open _root_.Complexity.TM
open ScannerSpec

variable {n : ℕ}

def optionalMachine (master : Fin (n + 1)) : TM (n + 1) :=
  OptionalMachine.machine (BoxScanner.machine master) master (NaturalMachine.flagIndex n)

def machine (species master : Fin (n + 1)) : TM (n + 1) := forRegTM (optionalMachine master) species

def optionalTime (L : ℕ) : ℕ := BoxScanner.timeBound L + 1
def timeBound (ns L : ℕ) : ℕ := ns * (optionalTime L + 2) + (ns + 2)

theorem optionalTime_mono : Monotone optionalTime := by
  intro a b h
  exact Nat.add_le_add_right (BoxScanner.timeBound_mono h) 1

theorem optional_runs (master : Fin (n + 1)) (hm : master ≠ NaturalMachine.flagIndex n) :
    Runs (RecordControl.optional RecordControl.box) (optionalMachine master) master (NaturalMachine.flagIndex n)
      (fun _ => True) optionalTime := by
  have hbox := BoxScanner.runs master hm (fun _ => True) (by intros; trivial)
  have hne : (BoxScanner.machine master).qstart ≠ (BoxScanner.machine master).qhalt := by
    simp [BoxScanner.machine, seqTM]
  exact OptionalScanner.runs hbox BoxScanner.timeBound_mono hne hm (by intros; trivial)

theorem runs (species master : Fin (n + 1)) (hs : species ≠ NaturalMachine.flagIndex n)
    (hsm : species ≠ master) (hm : master ≠ NaturalMachine.flagIndex n) (ns : ℕ) :
    Runs (RecordControl.array (RecordControl.optional RecordControl.box) ns) (machine species master)
      master (NaturalMachine.flagIndex n) (fun work => True ∧ IsReg ns (work species)) (timeBound ns) :=
  ScannerArray.runs_array (optional_runs master hm) optionalTime_mono species hs hsm (by intros; trivial) ns

theorem time_bound_in_total_length {ns L : ℕ} {input : List Bool} (hs : ns ≤ L) (hi : input.length ≤ L) :
    timeBound ns input.length ≤ L * (4 * L + 24) + (L + 2) := by
  have hb : optionalTime input.length + 2 ≤ 4 * L + 24 := by
    simp only [optionalTime, BoxScanner.timeBound_eq]
    omega
  exact Nat.add_le_add (Nat.mul_le_mul hs hb) (Nat.add_le_add_right hs 2)

end JointThermoComplexity.Complexity.BoxArray

#print axioms JointThermoComplexity.Complexity.BoxArray.optional_runs
#print axioms JointThermoComplexity.Complexity.BoxArray.runs
