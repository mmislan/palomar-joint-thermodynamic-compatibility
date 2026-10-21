module
public import proofs.JointThermoComplexity.Complexity.PowerPayloadRun
public import proofs.JointThermoComplexity.Complexity.PowerAddressCircuit

set_option autoImplicit false
@[expose] public section

/-! A polynomial-time exponent payload loop appends the exact semantic circuit equations. -/

namespace JointThermoComplexity.Complexity.PowerPayloadCircuit
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts PowerAddressCircuit CircuitSerialization

theorem runtime_bound (L count : ℕ) (h : count ≤ L) :
    PowerPayloadRun.timeBound L count ≤ 192 * L ^ 3 + 360 * L ^ 2 + 182 * L + 1 := by
  unfold PowerPayloadRun.timeBound
  calc
    count * (PowerBitStep.timeBound L + 2) + 1 ≤ L * (PowerBitStep.timeBound L + 2) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _
    _ = _ := by rw [PowerBitStep.timeBound_eq]; ring1

theorem hoareTime {n : ℕ} (m offset arity L : ℕ) (ha : arity ≤ 4 * L)
    (s : BinaryPower.State n) (bits : List Bool) (inputs : Fin n → Fin arity)
    (h : offset + (s.runBits bits).size ≤ arity) (hlen : bits.length ≤ L)
    (before tail initial : List Bool) (R : (Fin (m + 13) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next m → j ≠ accumulator m → j ≠ power m →
      j ≠ PowerBitState.flag m → work' j = work j) → R work → R work') :
    (PowerPayloadRun.machine m).HoareTime
      (fun inp work out => Cursor before (BitCodec.encodeBits bits ++ tail)
        (initial ++ equationStream s.circuit inputs
          (index offset _ arity (by have hs := s.size_le_runBits bits; omega))) inp work out ∧
        PowerAddressFrame.Ready m (ofState offset s) R work)
      (fun inp work out => Cursor (before ++ BitCodec.encodeBits bits) tail
        (initial ++ equationStream (s.runBits bits).circuit inputs (index offset _ arity h)) inp work out ∧
        PowerAddressFrame.Ready m (ofState offset (s.runBits bits)) R work)
      (192 * L ^ 3 + 360 * L ^ 2 + 182 * L + 1) := by
  have hp := PowerPayloadRun.hoareTime m arity L ha R hR bits (ofState offset s) before tail
    (initial ++ equationStream s.circuit inputs
      (index offset _ arity (by have hs := s.size_le_runBits bits; omega))) (fits offset arity s bits h)
  exact hp.consequence (fun _ _ _ hp => hp) (by
    rintro inp work out ⟨hc, hr⟩
    refine ⟨?_, ?_⟩
    · rw [run_stream offset arity s bits inputs h]
      simpa only [List.append_assoc] using hc
    · simpa only [ofState_run] using hr) (runtime_bound L bits.length hlen)

end JointThermoComplexity.Complexity.PowerPayloadCircuit

#print axioms JointThermoComplexity.Complexity.PowerPayloadCircuit.hoareTime
