module
public import proofs.JointThermoComplexity.Complexity.ParserCountReady
public import proofs.JointThermoComplexity.Complexity.CountDispatch

set_option autoImplicit false
@[expose] public section

/-! Actual total binary-input parsing and gate-count preparation with a retained verdict. -/

namespace JointThermoComplexity.Complexity.FreshGateCount
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def machine (n : ℕ) : TM (n + 6) := seqTM (ParserCountReady.machine n) (CountDispatch.machine n)

def timeBound (L : ℕ) : ℕ := ParserCountReady.timeBound L + 1 + CountDispatch.timeBound L

theorem timeBound_eq (L : ℕ) : timeBound L = 4 * L ^ 3 + 44 * L ^ 2 + 91 * L + 70 := by
  rw [timeBound, ParserCountReady.timeBound_eq]
  unfold CountDispatch.timeBound ValidGateCount.timeBound
  ring1

theorem run (n : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine n).reachesIn t ((machine n).initCfg input) d ∧
      (machine n).halted d ∧ Cursor [] input [] d.input d.work d.output ∧ (∀ j, Parked (d.work j)) ∧
      IsReg (GateCountValue.count input) (d.work (RoutedNetworkParser.raw n)) ∧
      ParserRegisters.Kept n input (CountAppend.oldWork d.work) := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hs, hz, hk⟩ := ParserCountReady.run n input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdsafe, hdreg, hdkept, _⟩ :=
    CountDispatch.hoareTime n input [] (fun _ => True) c.input c.work c.output ⟨hc, hs, hz, hk, trivial⟩
  obtain ⟨hi, hw, ho⟩ := hc.phase
  have hr : (CountDispatch.machine n).reachesIn td
      ⟨(CountDispatch.machine n).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, ho] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (ParserCountReady.machine n) (CountDispatch.machine n) hcreach hchalt hr
  have hstart : phase1Wrap (ParserCountReady.machine n) (CountDispatch.machine n)
      ((ParserCountReady.machine n).initCfg input) = (machine n).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (ParserCountReady.machine n) (CountDispatch.machine n) d, tc + 1 + td,
    by unfold timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdsafe, hdreg, hdkept⟩

end JointThermoComplexity.Complexity.FreshGateCount

#print axioms JointThermoComplexity.Complexity.FreshGateCount.run
