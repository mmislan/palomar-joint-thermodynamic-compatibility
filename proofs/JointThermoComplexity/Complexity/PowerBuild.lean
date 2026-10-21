module
public import proofs.JointThermoComplexity.Complexity.PowerPayloadCircuit
public import proofs.JointThermoComplexity.Complexity.PowerStartCircuit

set_option autoImplicit false
@[expose] public section

/-! An actual exponent routine initializes the unit and consumes its canonical binary exponent. -/

namespace JointThermoComplexity.Complexity.PowerBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts RealCircuit CircuitSerialization PowerAddressCircuit PowerStartCircuit

def machine (m : ℕ) : TM (m + 13) := seqTM (PowerUnit.machine m) (PowerPayloadRun.machine m)

def timeBound (L : ℕ) : ℕ := 192 * L ^ 3 + 392 * L ^ 2 + 266 * L + 56

theorem hoareTime {n k : ℕ} (m offset arity L old : ℕ) (ha : arity ≤ 4 * L)
    (c : Circuit n k) (base : Fin k) (exponent : ℕ) (inputs : Fin n → Fin arity)
    (h : offset + (BinaryPower.build c base exponent).size ≤ arity)
    (hlen : exponent.bits.length ≤ L) (hold : old ≤ 4 * L)
    (before tail initial : List Bool) (R : (Fin (m + 13) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next m → j ≠ accumulator m → j ≠ power m →
      j ≠ PowerBitState.flag m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode exponent ++ tail)
        (initial ++ equationStream c inputs
          (index offset k arity (by have hs := BinaryPower.build_size_ge c base exponent; omega))) inp work out ∧
        PowerAddressFrame.Ready m (beforeState offset old c base) R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode exponent) tail
        (initial ++ equationStream (BinaryPower.build c base exponent).circuit inputs (index offset _ arity h)) inp work out ∧
        PowerAddressFrame.Ready m (ofState offset (BinaryPower.build c base exponent)) R work)
      (timeBound L) := by
  have hs : k + 1 ≤ (BinaryPower.build c base exponent).size :=
    (BinaryPower.start c base).size_le_runBits exponent.bits
  have hstart : offset + (k + 1) ≤ arity := by omega
  have hn : (beforeState offset old c base).nextAddress < arity := by
    change offset + k < arity
    omega
  have hunit := PowerUnit.hoareTime m arity (beforeState offset old c base) hn before
    (BitCodec.naturalCode exponent ++ tail)
    (initial ++ equationStream c inputs (index offset k arity (by omega))) R
    (fun work work' hw hr => hR work work' (fun j hn ha _ _ => hw j hn ha) hr)
  have hpayload := PowerPayloadCircuit.hoareTime m offset arity L ha (BinaryPower.start c base)
    exponent.bits inputs h hlen before tail initial R hR
  have hseq := seqTM_hoareTime (PowerUnit.machine m) (PowerPayloadRun.machine m) hunit (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    refine ⟨?_, ?_⟩
    · rw [start_stream offset arity c base inputs hstart]
      simpa only [beforeState, BitCodec.naturalCode, List.append_assoc] using hc
    · simpa only [unit_eq] using hr) hpayload
  have hunitBound := PowerUnit.runtime_bound (beforeState offset old c base) L
    (by change offset + k ≤ 4 * L; omega) hold
  exact hseq.consequence (fun _ _ _ hp => hp) (fun _ _ _ hp => hp) (by unfold timeBound; omega)

end JointThermoComplexity.Complexity.PowerBuild

#print axioms JointThermoComplexity.Complexity.PowerBuild.hoareTime
