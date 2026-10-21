module
public import proofs.JointThermoComplexity.Complexity.ScannerArray
public import proofs.JointThermoComplexity.Complexity.ReactionScanner

set_option autoImplicit false
@[expose] public section

/-! A uniform array of literal reactions, with both dimension registers restored. -/

namespace JointThermoComplexity.Complexity.ReactionArray
open _root_.Complexity
open _root_.Complexity.TM
open ScannerSpec

variable {n : ℕ}

def machine (species reactions master : Fin (n + 1)) : TM (n + 1) :=
  forRegTM (ReactionScanner.machine species master) reactions

def timeBound (ns nr L : ℕ) : ℕ := nr * (ReactionScanner.timeBound ns L + 2) + (nr + 2)

theorem runs (species reactions master : Fin (n + 1))
    (hs : species ≠ NaturalMachine.flagIndex n) (hm : master ≠ NaturalMachine.flagIndex n)
    (hsm : species ≠ master) (hr : reactions ≠ NaturalMachine.flagIndex n) (hrm : reactions ≠ master)
    (hsr : species ≠ reactions) (ns nr : ℕ) :
    Runs (RecordControl.array (RecordControl.reaction ns) nr) (machine species reactions master)
      master (NaturalMachine.flagIndex n)
      (fun work => IsReg ns (work species) ∧ IsReg nr (work reactions)) (timeBound ns nr) := by
  have hbody := ReactionScanner.runs species master hs hm hsm ns
  have hEnv : ∀ (work work' : Fin (n + 1) → Tape),
      (∀ j, j ≠ reactions → work' j = work j) → IsReg ns (work species) → IsReg ns (work' species) := by
    intro work work' h hreg
    simpa only [h species hsr] using hreg
  exact ScannerArray.runs_array hbody (ReactionScanner.timeBound_mono ns) reactions hr hrm hEnv nr

theorem codec_status_iff (ns nr : ℕ) (input : List Bool) (initial : Bool) {value : Γ}
    (h : value = Γ.ofBool (initial && (RecordControl.array (RecordControl.reaction ns) nr).valid input)) :
    value = Γ.one ↔ initial = true ∧
      ∃ Q tail, (FiniteCodec.finiteFunction (DataCodec.reaction ns) nr).parse input = some (Q, tail) := by
  have hv : Γ.ofBool (initial && (RecordControl.array (RecordControl.reaction ns) nr).valid input) = Γ.one ↔
      initial = true ∧ (RecordControl.array (RecordControl.reaction ns) nr).valid input = true := by
    cases initial <;> cases (RecordControl.array (RecordControl.reaction ns) nr).valid input <;> simp [Γ.ofBool]
  rw [h, hv, (RecordControl.array (RecordControl.reaction ns) nr).accepts input]

theorem time_bound_in_total_length {ns nr L : ℕ} {input : List Bool}
    (hs : ns ≤ L) (hr : nr ≤ L) (hi : input.length ≤ L) :
    timeBound ns nr input.length ≤ L * (2 * (L * L) + 16 * L + 17) + (L + 2) := by
  have hreaction := ReactionScanner.time_bound_in_total_length hs hi
  have hb : ReactionScanner.timeBound ns input.length + 2 ≤ 2 * (L * L) + 16 * L + 17 := by omega
  exact Nat.add_le_add (Nat.mul_le_mul hr hb) (Nat.add_le_add_right hr 2)

end JointThermoComplexity.Complexity.ReactionArray

#print axioms JointThermoComplexity.Complexity.ReactionArray.runs
#print axioms JointThermoComplexity.Complexity.ReactionArray.codec_status_iff
