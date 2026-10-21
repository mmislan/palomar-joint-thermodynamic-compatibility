module
public import proofs.JointThermoComplexity.Complexity.ValidGateCount
public import proofs.JointThermoComplexity.Complexity.GateCountValue
public import proofs.JointThermoComplexity.Complexity.FlagBranchRun

set_option autoImplicit false
@[expose] public section

/-! The retained parser verdict guards the actual count pass on every binary input. -/

namespace JointThermoComplexity.Complexity.CountDispatch
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def machine (n : ℕ) : TM (n + 6) :=
  FlagBranch.machine (RoutedNetworkParser.master n) (ValidGateCount.machine n) (emitBitsTM [])

def timeBound (L : ℕ) : ℕ := ValidGateCount.timeBound L + 2

theorem hoareTime (n : ℕ) (input emitted : List Bool) (R : (Fin (n + 5) → Tape) → Prop) :
    (machine n).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work (RoutedNetworkParser.raw n)) ∧ ParserRegisters.Kept n input (CountAppend.oldWork work) ∧ R (CountAppend.oldWork work))
      (fun inp work out => Cursor [] input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg (GateCountValue.count input) (work (RoutedNetworkParser.raw n)) ∧
        ParserRegisters.Kept n input (CountAppend.oldWork work) ∧ R (CountAppend.oldWork work)) (timeBound input.length) := by
  let P : (Fin (n + 6) → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧
    IsReg 0 (work (RoutedNetworkParser.raw n)) ∧ ParserRegisters.Kept n input (CountAppend.oldWork work) ∧ R (CountAppend.oldWork work)
  cases ha : NetworkInputControl.accepted input with
  | false =>
    have hn := FixedOutput.hoareTime ([] : List Bool) [] input emitted
      (fun work => IsReg 0 (work (RoutedNetworkParser.raw n)) ∧ ParserRegisters.Kept n input (CountAppend.oldWork work) ∧ R (CountAppend.oldWork work))
    have hn' : (emitBitsTM (n := n + 6) []).HoareTime
        (fun inp work out => Cursor [] input emitted inp work out ∧ P work)
        (fun inp work out => Cursor [] input emitted inp work out ∧ P work) 0 := by
      exact hn.consequence (fun _ _ _ h => h)
        (fun _ _ _ ⟨hc, hs, hg, hk, hr⟩ => ⟨by simpa only [List.append_nil] using hc, hs, hg, hk, hr⟩) le_rfl
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master n) (ValidGateCount.machine n) (emitBitsTM [])
      [] input emitted [] input emitted P P 0 hn'
    rintro inp work out ⟨hc, hs, hg, hk, hr⟩
    have hf : (work (RoutedNetworkParser.master n)).read = Γ.zero := by
      simpa only [CountAppend.oldWork, RoutedNetworkParser.master, ha, Γ.ofBool] using hk.2.1
    obtain ⟨d, t, ht, hreach, hhalt, hdcur, hdsafe, hdreg, hdkept, hdR⟩ :=
      hb inp work out ⟨⟨hc, hs, hg, hk, hr⟩, hf⟩
    exact ⟨d, t, by unfold timeBound; omega, hreach, hhalt, hdcur, hdsafe,
      by simpa only [GateCountValue.rejected ha] using hdreg, hdkept, hdR⟩
  | true =>
    obtain ⟨Q, hQ⟩ := (NetworkInputControl.status_iff_decode input).mp ha
    let S : (Fin (n + 6) → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧
      IsReg (NetworkMembership.gates Q.network) (work (RoutedNetworkParser.raw n)) ∧
      ParserRegisters.Kept n input (CountAppend.oldWork work) ∧ R (CountAppend.oldWork work)
    have hv := ValidGateCount.hoareTime n input emitted Q hQ R
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master n) (ValidGateCount.machine n) (emitBitsTM [])
      [] input emitted [] input emitted P S (ValidGateCount.timeBound input.length) hv
    rintro inp work out ⟨hc, hs, hg, hk, hr⟩
    have hf : (work (RoutedNetworkParser.master n)).read = Γ.one := by
      simpa only [CountAppend.oldWork, RoutedNetworkParser.master, ha, Γ.ofBool] using hk.2.1
    obtain ⟨d, t, ht, hreach, hhalt, hdcur, hdsafe, hdreg, hdkept, hdR⟩ :=
      hb inp work out ⟨⟨hc, hs, hg, hk, hr⟩, hf⟩
    exact ⟨d, t, by unfold timeBound; omega, hreach, hhalt, hdcur, hdsafe,
      by simpa only [GateCountValue.on_decode hQ] using hdreg, hdkept, hdR⟩

end JointThermoComplexity.Complexity.CountDispatch

#print axioms JointThermoComplexity.Complexity.CountDispatch.hoareTime
