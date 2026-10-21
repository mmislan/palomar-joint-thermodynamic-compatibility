module
public import proofs.JointThermoComplexity.Complexity.PowerStartCircuit

set_option autoImplicit false
@[expose] public section

/-! Exact final product-gate serialization of one semantic monomial advance. -/

namespace JointThermoComplexity.Complexity.MonomialAdvanceCode
open RealCircuit CircuitSerialization PowerAddressCircuit

variable {n : ℕ}

def power (s : MonomialCircuit.State n) (item : Fin n × ℕ) : BinaryPower.State n :=
  BinaryPower.build (s.circuit.snoc (.input item.1)) (Fin.last s.size) item.2

theorem advance_size (s : MonomialCircuit.State n) (item : Fin n × ℕ) :
    (s.advance item).size = (power s item).size + 1 := rfl

theorem advance_accumulator (s : MonomialCircuit.State n) (item : Fin n × ℕ) :
    (s.advance item).accumulator.val = (power s item).size := rfl

def afterState (offset : ℕ) (s : MonomialCircuit.State n) (item : Fin n × ℕ) : PowerAddressState.State :=
  ⟨offset + (s.advance item).size, offset + (power s item).accumulator.val, offset + (power s item).power.val⟩

theorem after_eq (offset : ℕ) (s : MonomialCircuit.State n) (item : Fin n × ℕ) :
    (⟨(ofState offset (power s item)).nextAddress + 1,
      (ofState offset (power s item)).accumulatorAddress,
      (ofState offset (power s item)).powerAddress⟩ : PowerAddressState.State) = afterState offset s item := by
  simp only [ofState, afterState, advance_size, Nat.add_assoc]

theorem advance_stream (offset arity : ℕ) (s : MonomialCircuit.State n) (item : Fin n × ℕ)
    (inputs : Fin n → Fin arity) (h : offset + (s.advance item).size ≤ arity) :
    equationStream (s.advance item).circuit inputs (index offset _ arity h) =
      equationStream (power s item).circuit inputs
        (index offset _ arity (by rw [advance_size] at h; omega)) ++
      BinaryPowerCode.multiply
        (⟨offset + (power s item).size, by rw [advance_size] at h; omega⟩ : Fin arity)
        ⟨offset + s.accumulator.val, by have ha := s.accumulator.isLt; have hs := s.advance_size_ge item; omega⟩
        ⟨offset + (power s item).accumulator.val, by
          have ha := (power s item).accumulator.isLt; rw [advance_size] at h; omega⟩ := by
  have hi : (fun j : Fin (power s item).size => index offset ((power s item).size + 1) arity h j.castSucc) =
      index offset (power s item).size arity (by rw [advance_size] at h; omega) := by
    funext j; apply Fin.ext; rfl
  let previous := Fin.castLE (BinaryPower.build_size_ge (s.circuit.snoc (.input item.1))
    (Fin.last s.size) item.2) s.accumulator.castSucc
  change equationStream (power s item).circuit inputs
      (fun j => index offset ((power s item).size + 1) arity h j.castSucc) ++
    BinaryPowerCode.multiply (index offset ((power s item).size + 1) arity h (Fin.last (power s item).size))
      (index offset ((power s item).size + 1) arity h previous.castSucc)
      (index offset ((power s item).size + 1) arity h (power s item).accumulator.castSucc) = _
  rw [hi]
  rfl

end JointThermoComplexity.Complexity.MonomialAdvanceCode

#print axioms JointThermoComplexity.Complexity.MonomialAdvanceCode.advance_stream
