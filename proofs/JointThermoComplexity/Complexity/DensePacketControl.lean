module
public import proofs.JointThermoComplexity.Complexity.DenseRowStep

set_option autoImplicit false
@[expose] public section

/-! Total word control for a precompiled finite list of row programs. -/

namespace JointThermoComplexity.Complexity.DensePacketControl
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {A : Type}

def index (N current : ℕ) : Fin (N + 2) := ⟨current % (N + 2), Nat.mod_lt _ (by omega)⟩
theorem index_val (N current : ℕ) (h : current ≤ N + 1) : (index N current).val = current := by
  exact Nat.mod_eq_of_lt (by omega)

def machine (right : Bool) (external : A → TM 64) (coefficient : A → ℤ) : List A → TM 64
  | [] => emitBitsTM []
  | row :: rows => seqTM (DenseRowStep.machine right (external row) (coefficient row)) (machine right external coefficient rows)

def words (right : Bool) (N e : ℕ) (gamma : A → Fin e → ℕ) (coefficient : A → ℤ) (v : ℕ) (negative : Bool) : ℕ → List A → List Bool
  | _, [] => []
  | current, row :: rows => DenseRawRecord.word right N (index N current) e (gamma row) (coefficient row) v negative ++
      words right N e gamma coefficient v negative (current + 1) rows

def Ready (current m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N v : ℕ) (negative : Bool)
    (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  ∃ u, u ≤ N + 1 ∧ DenseRowFrame.Work current u m hm values n N v negative R work
def Pre (current m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N v : ℕ) (negative : Bool)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Ready current m hm values n N v negative R work

def timeBound (right : Bool) (N B E count : ℕ) : ℕ := count * (DenseRowStep.timeBound right N B E + 1)

end JointThermoComplexity.Complexity.DensePacketControl

#print axioms JointThermoComplexity.Complexity.DensePacketControl.index_val
