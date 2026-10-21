module
public import proofs.JointThermoComplexity.Complexity.MonomialInputCircuit
public import proofs.JointThermoComplexity.Complexity.PowerBuild

set_option autoImplicit false
@[expose] public section

/-! Read the current species address, emit its input gate, and compute its encoded power. -/

namespace JointThermoComplexity.Complexity.MonomialPower
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts RealCircuit CircuitSerialization PowerAddressCircuit MonomialInputCircuit

def machine (m : ℕ) : TM (m + 14) := seqTM (MonomialInput.machine m) (PowerBuild.machine (m + 1))

def timeBound (L : ℕ) : ℕ := 192 * L ^ 3 + 456 * L ^ 2 + 398 * L + 126

theorem hoareTime {n k : ℕ} (m offset arity L oldAcc oldPower : ℕ) (ha : arity ≤ 4 * L)
    (c : Circuit n k) (i : Fin n) (exponent : ℕ) (inputs : Fin n → Fin arity)
    (h : offset + (BinaryPower.build (c.snoc (.input i)) (Fin.last k) exponent).size ≤ arity)
    (hlen : exponent.bits.length ≤ L) (hacc : oldAcc ≤ 4 * L) (hpower : oldPower ≤ 4 * L)
    (before tail initial : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ accumulator (m + 1) →
      j ≠ power (m + 1) → j ≠ PowerBitState.flag (m + 1) → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode exponent ++ tail)
        (initial ++ equationStream c inputs (index offset k arity
          (by have hs := BinaryPower.build_size_ge (c.snoc (.input i)) (Fin.last k) exponent; omega))) inp work out ∧
        PowerAddressFrame.Ready (m + 1) (temporary offset oldAcc oldPower c) R work ∧
        IsReg (inputs i).val (work (species m)))
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode exponent) tail
        (initial ++ equationStream (BinaryPower.build (c.snoc (.input i)) (Fin.last k) exponent).circuit
          inputs (index offset _ arity h)) inp work out ∧
        PowerAddressFrame.Ready (m + 1)
          (ofState offset (BinaryPower.build (c.snoc (.input i)) (Fin.last k) exponent)) R work ∧
        IsReg (inputs i).val (work (species m))) (timeBound L) := by
  have hstart : offset + (k + 1) ≤ arity := by
    have hs := BinaryPower.build_size_ge (c.snoc (.input i)) (Fin.last k) exponent
    omega
  have hin := MonomialInputCircuit.hoareTime m offset arity L oldAcc oldPower ha c i inputs hstart hpower
    before (BitCodec.naturalCode exponent ++ tail) initial R
    (fun work work' hw hr => hR work work' (fun j hn _ hp _ => hw j hn hp) hr)
  let P : (Fin (m + 14) → Tape) → Prop := fun work => IsReg (inputs i).val (work (species m)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ accumulator (m + 1) →
      j ≠ power (m + 1) → j ≠ PowerBitState.flag (m + 1) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hi, hr⟩
    have hs := hw (species m) (species_ne_next m) (species_ne_accumulator m) (species_ne_power m) (species_ne_flag m)
    exact ⟨by simpa only [hs] using hi, hR work work' hw hr⟩
  have hbuild := PowerBuild.hoareTime (m + 1) offset arity L oldAcc ha (c.snoc (.input i)) (Fin.last k)
    exponent inputs h hlen hacc before tail initial P hP
  have hseq := seqTM_hoareTime (MonomialInput.machine m) (PowerBuild.machine (m + 1)) hin (by
    rintro inp work out ⟨hc, ⟨hs, hz, hn, ha, hp, hr⟩, hi⟩
    obtain ⟨hip, hw, ho⟩ := hc.phase
    rw [hip, hw, ho]
    exact ⟨hc, hs, hz, hn, ha, hp, hi, hr⟩) hbuild
  exact hseq.consequence (fun _ _ _ hp => hp) (by
    rintro inp work out ⟨hc, hs, hz, hn, ha, hp, hi, hr⟩
    exact ⟨hc, ⟨hs, hz, hn, ha, hp, hr⟩, hi⟩) (by unfold timeBound PowerBuild.timeBound; omega)

end JointThermoComplexity.Complexity.MonomialPower

#print axioms JointThermoComplexity.Complexity.MonomialPower.hoareTime
