module
public import proofs.JointThermoComplexity.Complexity.PowerAddressCode

set_option autoImplicit false
@[expose] public section

/-! Contiguous natural addresses serialize the same circuit as repeated squaring. -/

namespace JointThermoComplexity.Complexity.PowerAddressCircuit
open RealCircuit CircuitSerialization PowerAddressState

variable {n : ℕ}

def ofState (offset : ℕ) (s : BinaryPower.State n) : State :=
  ⟨offset + s.size, offset + s.accumulator.val, offset + s.power.val⟩

def index (offset size arity : ℕ) (h : offset + size ≤ arity) (i : Fin size) : Fin arity :=
  ⟨offset + i.val, by have hi := i.isLt; omega⟩

theorem ofState_advance (offset : ℕ) (s : BinaryPower.State n) (bit : Bool) :
    ofState offset (s.advance bit) = (ofState offset s).advance bit := by
  cases bit <;> simp [ofState, BinaryPower.State.advance, State.advance, Nat.add_assoc]

theorem ofState_run (offset : ℕ) (s : BinaryPower.State n) (bits : List Bool) :
    ofState offset (s.runBits bits) = (ofState offset s).run bits := by
  induction bits generalizing s with
  | nil => rfl
  | cons bit bits ih =>
    simp only [BinaryPower.State.runBits, State.run, ih, ofState_advance]

theorem fits (offset arity : ℕ) (s : BinaryPower.State n) (bits : List Bool)
    (h : offset + (s.runBits bits).size ≤ arity) : Fits arity bits (ofState offset s) := by
  have ha := s.accumulator.isLt
  have hp := s.power.isLt
  have hs := s.size_le_runBits bits
  rw [ExactGateCount.power_run_size] at h
  change offset + s.accumulator.val < arity ∧ offset + s.power.val < arity ∧
    (offset + s.size) + ExactGateCount.bitsCost bits ≤ arity
  omega

theorem advance_stream (offset arity : ℕ) (s : BinaryPower.State n) (bit : Bool)
    (inputs : Fin n → Fin arity) (h : offset + (s.advance bit).size ≤ arity) :
    equationStream (s.advance bit).circuit inputs (index offset _ arity h) =
      equationStream s.circuit inputs (index offset _ arity (by have hs := s.size_le_advance bit; omega)) ++
        PowerAddressCode.word (ofState offset s) bit := by
  cases bit with
  | false =>
    have h0 : offset + s.size ≤ arity := by change offset + (s.size + 1) ≤ arity at h; omega
    have hi : (fun i : Fin s.size => index offset (s.size + 1) arity h i.castSucc) =
        index offset s.size arity h0 := by funext i; apply Fin.ext; rfl
    apply (BinaryPowerCode.advance_false s inputs (index offset _ arity h)).trans
    rw [hi]
    congr 1
  | true =>
    have h0 : offset + s.size ≤ arity := by change offset + (s.size + 2) ≤ arity at h; omega
    have hi : (fun i : Fin s.size => index offset (s.size + 2) arity h i.castSucc.castSucc) =
        index offset s.size arity h0 := by funext i; apply Fin.ext; rfl
    apply (BinaryPowerCode.advance_true s inputs (index offset _ arity h)).trans
    rw [hi, List.append_assoc]
    simp only [PowerAddressCode.typed_multiply, index, Fin.val_last, Fin.val_castSucc,
      PowerAddressCode.word, ofState, Nat.add_assoc]

theorem run_stream (offset arity : ℕ) (s : BinaryPower.State n) (bits : List Bool)
    (inputs : Fin n → Fin arity) (h : offset + (s.runBits bits).size ≤ arity) :
    equationStream (s.runBits bits).circuit inputs (index offset _ arity h) =
      equationStream s.circuit inputs (index offset _ arity (by have hs := s.size_le_runBits bits; omega)) ++
        PowerAddressCode.stream (ofState offset s) bits := by
  induction bits generalizing s with
  | nil => simp only [BinaryPower.State.runBits, PowerAddressCode.stream, List.append_nil]
  | cons bit bits ih =>
    have h' : offset + ((s.advance bit).runBits bits).size ≤ arity := h
    have hm : offset + (s.advance bit).size ≤ arity := by
      have hs := (s.advance bit).size_le_runBits bits
      omega
    apply (ih (s.advance bit) h').trans
    simpa only [PowerAddressCode.stream, ofState_advance, List.append_assoc] using
      congrArg (fun code => code ++ PowerAddressCode.stream (ofState offset (s.advance bit)) bits)
        (advance_stream offset arity s bit inputs hm)

end JointThermoComplexity.Complexity.PowerAddressCircuit

#print axioms JointThermoComplexity.Complexity.PowerAddressCircuit.run_stream
