module
public import proofs.JointThermoComplexity.Complexity.GateCountRuntime
public import proofs.JointThermoComplexity.Complexity.ParserRegisters

set_option autoImplicit false
@[expose] public section

/-! Apply the canonical tally at the parser's actual retained register addresses. -/

namespace JointThermoComplexity.Complexity.ValidGateCount
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def machine (n : ℕ) : TM (n + 6) :=
  NetworkGateCount.machine (NetworkParser.count n 0) (NetworkParser.count n 1)

def timeBound (L : ℕ) : ℕ := 2 * L ^ 3 + 16 * L ^ 2 + 22 * L + 13

theorem hoareTime (n : ℕ) (input emitted : List Bool) (Q : NetworkCodec.Input)
    (hQ : NetworkCodec.decode input = some Q) (R : (Fin (n + 5) → Tape) → Prop) :
    (machine n).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work (RoutedNetworkParser.raw n)) ∧ ParserRegisters.Kept n input (CountAppend.oldWork work) ∧ R (CountAppend.oldWork work))
      (fun inp work out => Cursor [] input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg (NetworkMembership.gates Q.network) (work (RoutedNetworkParser.raw n)) ∧
        ParserRegisters.Kept n input (CountAppend.oldWork work) ∧ R (CountAppend.oldWork work)) (timeBound input.length) := by
  have hinput := NetworkCodec.decode_sound hQ
  have hcount := NetworkGateCount.hoareTime (NetworkParser.count n 0) (NetworkParser.count n 1)
    (NetworkParser.count_ne_count n 0 1 (by decide)) Q [] emitted
    (fun old => ParserRegisters.Kept n input old ∧ R old)
  have hbound : NetworkGateCount.timeBound Q ≤ timeBound input.length := by
    simpa only [timeBound, hinput] using GateCountRuntime.timeBound_le_input Q
  refine hcount.consequence ?_ ?_ hbound
  · rintro inp work out ⟨hc, hs, hz, hkept, hr⟩
    obtain ⟨hsp, hre, _⟩ := ParserRegisters.decoded_counts n input (CountAppend.oldWork work) hkept hQ
    exact ⟨hre, hsp, by simpa only [hinput, List.append_nil] using hc, hs, hz, hkept, hr⟩
  · rintro inp work out ⟨hg, _, _, hc, hs, hkept, hr⟩
    exact ⟨by simpa only [hinput, List.append_nil] using hc, hs, hg, hkept, hr⟩

end JointThermoComplexity.Complexity.ValidGateCount

#print axioms JointThermoComplexity.Complexity.ValidGateCount.hoareTime
