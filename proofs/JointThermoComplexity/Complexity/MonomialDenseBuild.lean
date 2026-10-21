module
public import proofs.JointThermoComplexity.Complexity.MonomialBuild
public import proofs.JointThermoComplexity.Complexity.MonomialDenseCode

set_option autoImplicit false
@[expose] public section

/-! The concrete species-count routine consumes the actual network exponent-array codec. -/

namespace JointThermoComplexity.Complexity.MonomialDenseBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady MonomialFuel
open RealCircuit CircuitSerialization PowerAddressCircuit FiniteCodec

theorem hoareTime {n k : ℕ} (m L offset arity old idx : ℕ) (ha : arity ≤ 4 * L)
    (hold : old ≤ 4 * L) (hidx : idx ≤ L) (c : Circuit n k) (γ : Fin n → ℕ)
    (inputs : Fin n → Fin arity) (hinputs : ∀ i, (inputs i).val = i.val)
    (h : offset + (MonomialCircuit.build c (MonomialCircuit.denseTerms γ)).size ≤ arity)
    (hcount : n ≤ L) (hbits : ∀ i, (γ i).bits.length ≤ L)
    (before tail initial : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ accumulator (m + 1) →
      j ≠ power (m + 1) → j ≠ PowerBitState.flag (m + 1) → j ≠ previous m → j ≠ species m →
      work' j = work j) → R work → R work') :
    (MonomialBuild.machine m (slot m)).HoareTime
      (fun inp work out => Cursor before (functionCode natural γ ++ tail)
        (initial ++ equationStream c inputs (index offset k arity
          (by have hs := MonomialCircuit.build_size_ge c (MonomialCircuit.denseTerms γ); omega))) inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 1))) ∧
        IsReg (offset + k) (work (next (m + 1))) ∧ IsReg old (work (previous m)) ∧
        Temps m L work ∧ IsReg idx (work (species m)) ∧ IsReg n (work (slot m)) ∧ R work)
      (fun inp work out => Cursor (before ++ functionCode natural γ) tail
        (initial ++ equationStream (MonomialCircuit.build c (MonomialCircuit.denseTerms γ)).circuit
          inputs (index offset _ arity h)) inp work out ∧
        Ready m L offset (MonomialCircuit.build c (MonomialCircuit.denseTerms γ)) n R work ∧ IsReg n (work (slot m)))
      (MonomialBuild.timeBound L) := by
  have ht := MonomialBuild.hoareTime m L offset arity old idx ha hold hidx (slot m) (slot_separate m) c
    (MonomialCircuit.denseTerms γ) inputs h (by simpa only [MonomialDenseCode.count_eq] using hcount)
    (MonomialDenseCode.bits_bound γ hbits) (MonomialDenseCode.index_eq γ inputs hinputs) before tail initial R hR
  simpa only [MonomialDenseCode.code_eq, MonomialDenseCode.count_eq] using ht

end JointThermoComplexity.Complexity.MonomialDenseBuild

#print axioms JointThermoComplexity.Complexity.MonomialDenseBuild.hoareTime
