module
public import proofs.JointThermoComplexity.Complexity.ScannerArray
public import proofs.JointThermoComplexity.Complexity.MotifScanner

set_option autoImplicit false
@[expose] public section

/-! Uniform supplied-motif arrays with all three count registers preserved. -/

namespace JointThermoComplexity.Complexity.MotifArray
open _root_.Complexity
open _root_.Complexity.TM
open ScannerSpec

variable {n : ℕ}

def machine (species reactions cores master : Fin (n + 1)) : TM (n + 1) :=
  forRegTM (MotifScanner.machine species reactions master) cores

def timeBound (ns nr nc : ℕ) : ℕ := nc * (MotifScanner.timeBound ns nr + 2) + (nc + 2)

theorem runs (species reactions cores master : Fin (n + 1))
    (hs : species ≠ NaturalMachine.flagIndex n) (hm : master ≠ NaturalMachine.flagIndex n) (hsm : species ≠ master)
    (hr : reactions ≠ NaturalMachine.flagIndex n) (hrm : reactions ≠ master)
    (hc : cores ≠ NaturalMachine.flagIndex n) (hcm : cores ≠ master)
    (hsc : species ≠ cores) (hrc : reactions ≠ cores) (ns nr nc : ℕ) :
    Runs (RecordControl.array (RecordControl.motif ns nr) nc) (machine species reactions cores master)
      master (NaturalMachine.flagIndex n)
      (fun work => (IsReg ns (work species) ∧ IsReg nr (work reactions)) ∧ IsReg nc (work cores))
      (fun _ => timeBound ns nr nc) := by
  have hbody := MotifScanner.runs species reactions master hs hm hsm hr hrm ns nr
  have hEnv : ∀ (work work' : Fin (n + 1) → Tape), (∀ j, j ≠ cores → work' j = work j) →
      (IsReg ns (work species) ∧ IsReg nr (work reactions)) →
      (IsReg ns (work' species) ∧ IsReg nr (work' reactions)) := by
    rintro work work' h ⟨hss, hrr⟩
    exact ⟨by simpa only [h species hsc] using hss, by simpa only [h reactions hrc] using hrr⟩
  exact ScannerArray.runs_array hbody (by intro a b h; rfl) cores hc hcm hEnv nc

theorem time_bound_in_total_length {ns nr nc L : ℕ} (hs : ns ≤ L) (hr : nr ≤ L) (hc : nc ≤ L) :
    timeBound ns nr nc ≤ L * (8 * L + 15) + (L + 2) := by
  have hb : MotifScanner.timeBound ns nr + 2 ≤ 8 * L + 15 := by
    have h := MotifScanner.time_bound_in_total_length hs hr
    omega
  exact Nat.add_le_add (Nat.mul_le_mul hc hb) (Nat.add_le_add_right hc 2)

end JointThermoComplexity.Complexity.MotifArray

#print axioms JointThermoComplexity.Complexity.MotifArray.runs
