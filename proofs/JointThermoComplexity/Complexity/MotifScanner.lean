module
public import proofs.JointThermoComplexity.Complexity.MaskScanner
public import proofs.JointThermoComplexity.Complexity.ScannerEnv

set_option autoImplicit false
@[expose] public section

/-! A supplied motif's two finite masks, without PAC recognition. -/

namespace JointThermoComplexity.Complexity.MotifScanner
open _root_.Complexity
open _root_.Complexity.TM
open ScannerSpec

variable {n : ℕ}

def machine (species reactions master : Fin (n + 1)) : TM (n + 1) :=
  seqTM (MaskScanner.machine species master) (MaskScanner.machine reactions master)

def timeBound (ns nr : ℕ) : ℕ := (4 * ns + 6) + 1 + (4 * nr + 6)

theorem runs (species reactions master : Fin (n + 1))
    (hs : species ≠ NaturalMachine.flagIndex n) (hm : master ≠ NaturalMachine.flagIndex n) (hsm : species ≠ master)
    (hr : reactions ≠ NaturalMachine.flagIndex n) (hrm : reactions ≠ master) (ns nr : ℕ) :
    Runs (RecordControl.motif ns nr) (machine species reactions master) master (NaturalMachine.flagIndex n)
      (fun work => IsReg ns (work species) ∧ IsReg nr (work reactions)) (fun _ => timeBound ns nr) := by
  let Env : (Fin (n + 1) → Tape) → Prop := fun work => IsReg ns (work species) ∧ IsReg nr (work reactions)
  have hEnv : ∀ work work',
      (∀ j, j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) → Env work → Env work' := by
    rintro work work' h ⟨hss, hrr⟩
    exact ⟨by simpa only [h species hsm hs] using hss, by simpa only [h reactions hrm hr] using hrr⟩
  have hspecies := ScannerEnv.strengthen (MaskScanner.runs_finset species master hs hm hsm ns)
    (fun _ h => h.1 : ∀ work, Env work → IsReg ns (work species)) hEnv
  have hreactions := ScannerEnv.strengthen (MaskScanner.runs_finset reactions master hr hm hrm nr)
    (fun _ h => h.2 : ∀ work, Env work → IsReg nr (work reactions)) hEnv
  have hraw := product_runs hspecies hreactions (by intro a b h; rfl)
  exact transport_runs (DataCodec.motifEquiv ns nr) hraw

theorem time_bound_in_total_length {ns nr L : ℕ} (hs : ns ≤ L) (hr : nr ≤ L) : timeBound ns nr ≤ 8 * L + 13 := by
  dsimp [timeBound]
  omega

end JointThermoComplexity.Complexity.MotifScanner

#print axioms JointThermoComplexity.Complexity.MotifScanner.runs
