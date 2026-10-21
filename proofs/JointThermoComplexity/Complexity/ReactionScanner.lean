module
public import proofs.JointThermoComplexity.Complexity.ArrayScanner
public import proofs.JointThermoComplexity.Complexity.ScalarScanner

set_option autoImplicit false
@[expose] public section

/-!
# Literal reaction records on a uniform binary TM

The machine reads two exponent tables and two fixed positive factor fields.
Its finite control depends on tape addresses, not on the declared species count
or the represented exponent and factor values.
-/

namespace JointThermoComplexity.Complexity.ReactionScanner
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ScannerSpec

variable {n : ℕ}

def machine (species master : Fin (n + 1)) : TM (n + 1) :=
  seqTM
    (seqTM (NaturalArray.machine false species master) (NaturalArray.machine false species master))
    (seqTM (NaturalField.machine true master) (NaturalField.machine true master))

def timeBound (v L : ℕ) : ℕ :=
  (v * (L + 6) + (v + 2) + 1 + (v * (L + 6) + (v + 2))) + 1 + ((L + 4) + 1 + (L + 4))

theorem timeBound_mono (v : ℕ) : Monotone (timeBound v) := by
  intro a b h
  have ha := ArrayScanner.bound_mono v h
  dsimp at ha
  dsimp [timeBound]
  omega

theorem runs (species master : Fin (n + 1))
    (hs : species ≠ NaturalMachine.flagIndex n) (hm : master ≠ NaturalMachine.flagIndex n) (hsm : species ≠ master)
    (v : ℕ) :
    Runs (RecordControl.reaction v) (machine species master) master (NaturalMachine.flagIndex n)
      (fun work => IsReg v (work species)) (timeBound v) := by
  have harray := ArrayScanner.natural_runs false species master hs hm hsm v
  have hEnv : ∀ (work work' : Fin (n + 1) → Tape),
      (∀ j, j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) →
      IsReg v (work species) → IsReg v (work' species) := by
    intro work work' h hreg
    simpa only [h species hsm hs] using hreg
  have hpos := ScalarScanner.natural_runs true master hm (fun work => IsReg v (work species)) hEnv
  have hcomplexes := product_runs harray harray (ArrayScanner.bound_mono v)
  have hpositive := product_runs hpos hpos (by
    intro a b h
    change a + 4 ≤ b + 4
    omega)
  have hmonop : Monotone (fun L : ℕ => (L + 4) + 1 + (L + 4)) := by
    intro a b h
    change (a + 4) + 1 + (a + 4) ≤ (b + 4) + 1 + (b + 4)
    omega
  have hraw := product_runs hcomplexes hpositive hmonop
  exact transport_runs (DataCodec.reactionEquiv v) hraw

theorem codec_status_iff (v : ℕ) (input : List Bool) (initial : Bool) {value : Γ}
    (h : value = Γ.ofBool (initial && (RecordControl.reaction v).valid input)) :
    value = Γ.one ↔ initial = true ∧ ∃ Q tail, (DataCodec.reaction v).parse input = some (Q, tail) := by
  have hv : Γ.ofBool (initial && (RecordControl.reaction v).valid input) = Γ.one ↔
      initial = true ∧ (RecordControl.reaction v).valid input = true := by
    cases initial <;> cases (RecordControl.reaction v).valid input <;> simp [Γ.ofBool]
  rw [h, hv, (RecordControl.reaction v).accepts input]

theorem time_bound_in_total_length {v L : ℕ} {input : List Bool} (hv : v ≤ L) (hi : input.length ≤ L) :
    timeBound v input.length ≤ 2 * (L * L) + 16 * L + 15 := by
  have ha := NaturalArray.time_bound_in_total_length hv hi
  dsimp [timeBound]
  omega

end JointThermoComplexity.Complexity.ReactionScanner

#print axioms JointThermoComplexity.Complexity.ReactionScanner.runs
#print axioms JointThermoComplexity.Complexity.ReactionScanner.codec_status_iff
