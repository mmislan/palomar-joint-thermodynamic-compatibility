module
public import proofs.JointThermoComplexity.Complexity.RowPairSelect

set_option autoImplicit false
@[expose] public section

/-! Actual literal Cartesian-order output of all nine possible row pairs.
The saved source cursor, row data and scale word survive every enabled entry.
-/

namespace JointThermoComplexity.Complexity.RowSquareMachine
open _root_.Complexity _root_.Complexity.TM EquationRowControl RowSquareFrame
open HeaderAt (Cursor)
variable {w : ℕ}

def runMachine (p : Ports w) : List (Fin 3 × Fin 3) → TM (w + 1)
  | [] => emitBitsTM []
  | ij :: rest => seqTM (RowPairSelect.machine p ij.1 ij.2) (runMachine p rest)

def stream (s : State) (scaleBits : List Bool) (entries : List (Fin 3 × Fin 3)) : List Bool :=
  entries.flatMap (fun ij => RowSquareControl.pair s scaleBits ij.1 ij.2)

theorem run_hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (entries : List (Fin 3 × Fin 3)) (B W : ℕ)
    (hB : 2 ≤ B) (emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (runMachine p entries).HoareTime (Logical p s scaleBits B W emitted R)
      (Logical p s scaleBits B W (emitted ++ stream s scaleBits entries) R)
      (entries.length * (RowPairSelect.timeBound B W + 1)) := by
  induction entries generalizing emitted with
  | nil => simpa only [runMachine, stream, List.flatMap_nil, List.length_nil, Nat.zero_mul] using
      literal_hoareTime p s scaleBits [] B W emitted R
  | cons ij rest ih =>
    have hp := RowPairSelect.hoareTime p s scaleBits ij.1 ij.2 B W hB emitted R hR
    have hr := ih (emitted ++ RowSquareControl.pair s scaleBits ij.1 ij.2)
    have h := seqTM_hoareTime _ _ hp (by
      rintro inp work out ⟨hc, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hr⟩) hr
    apply h.consequence (fun _ _ _ hh => hh)
    · intro inp work out hh
      simpa only [Logical, stream, List.flatMap_cons, List.append_assoc] using hh
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

def machine (p : Ports w) : TM (w + 1) := runMachine p RowSquareControl.pairs
def timeBound (B W : ℕ) : ℕ := 9 * (RowPairSelect.timeBound B W + 1)

theorem hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ) (hB : 2 ≤ B)
    (emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p).HoareTime (Logical p s scaleBits B W emitted R)
      (Logical p s scaleBits B W (emitted ++ RowSquareControl.output s scaleBits) R) (timeBound B W) := by
  simpa only [machine, stream, RowSquareControl.output, timeBound, RowSquareControl.pairs_length] using
    run_hoareTime p s scaleBits RowSquareControl.pairs B W hB emitted R hR

end JointThermoComplexity.Complexity.RowSquareMachine

#print axioms JointThermoComplexity.Complexity.RowSquareMachine.run_hoareTime
#print axioms JointThermoComplexity.Complexity.RowSquareMachine.hoareTime
