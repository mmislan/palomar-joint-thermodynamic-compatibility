module
public import proofs.JointThermoComplexity.Complexity.PendingEquationDispatch

set_option autoImplicit false
@[expose] public section

/-! One actual machine step emits local rows, then advances the main counted traversal. -/

namespace JointThermoComplexity.Complexity.EquationEmissionStep
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryCounterInit MainEquationWork MainNodeEquation
open HeaderAt (Cursor)

def machine : TM 32 := seqTM PendingEquationDispatch.machine (FormulaSpanStep.machine 24)
noncomputable def timeBound (N : ℕ) : ℕ := PendingEquationDispatch.timeBound N + 13 * N + 101
noncomputable def timePolynomial : Polynomial ℕ := MainNodeEquation.timePolynomial + 13 * Polynomial.X + 105

theorem timePolynomial_eval (N : ℕ) : timePolynomial.eval N = timeBound N := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
    MainNodeEquation.timePolynomial_eval, timeBound, PendingEquationDispatch.timeBound]
  omega

theorem scan_hoareTime (s : FormulaSpanControl.State) (arity L N : ℕ) (emitted : List Bool)
    (hL : L ≤ N) (ht : s.terms ≤ N) (hf : s.formulas ≤ N) (hc : s.coordinates ≤ N) (hlen : s.input.length ≤ L)
    (R : Work → Prop) (hR : Stable R) :
    (FormulaSpanStep.machine 24).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Bounded s arity L N R work)
      (fun inp work out => Cursor (FormulaSpanControl.step s).before (FormulaSpanControl.step s).input emitted inp work out ∧
        Bounded (FormulaSpanControl.step s) arity L N R work) (13 * N + 100) := by
  rintro inp work out ⟨hcur, adjusted, counts, values, hr, hadj, hq, hv, hz⟩
  have h := FormulaSpanStep.bounded_hoareTime L N N N emitted (High arity L adjusted counts values R)
    (high_stable arity L adjusted counts values R hR) s hlen ht hf hc
  obtain ⟨d, t, htime, hd, hh, hcur', hr'⟩ := h inp work out
    ⟨hcur, to_scan s arity L adjusted counts values R work hr⟩
  exact ⟨d, t, by omega, hd, hh, hcur', adjusted, counts, values,
    from_scan (FormulaSpanControl.step s) arity L adjusted counts values R d.work hr', hadj, hq, hv, hz⟩

theorem hoareTime (s : PreorderEmissionControl.State) (arity L N : ℕ)
    (ha : arity ≤ N) (hL : L ≤ N) (ht : s.scan.terms ≤ N) (hf : s.scan.formulas ≤ N)
    (hc : s.scan.coordinates ≤ N) (hp : s.scan.before.length ≤ N) (hlen : s.scan.input.length ≤ L)
    (R : Work → Prop) (hR : Stable R) :
    machine.HoareTime
      (fun inp work out => Cursor s.scan.before s.scan.input (RowEntriesCodec.entries s.emitted) inp work out ∧
        Bounded s.scan arity L N R work)
      (fun inp work out =>
        let next := PreorderEmissionControl.step L arity s
        Cursor next.scan.before next.scan.input (RowEntriesCodec.entries next.emitted) inp work out ∧
          Bounded next.scan arity L N R work) (timeBound N) := by
  let emitted := RowEntriesCodec.entries s.emitted ++ RowEntriesCodec.entries (PreorderEmissionControl.localRows L arity s.scan)
  have he := PendingEquationDispatch.hoareTime s.scan arity L N (RowEntriesCodec.entries s.emitted)
    ha hL hc hp hlen R hR
  have hs := scan_hoareTime s.scan arity L N emitted hL ht hf hc hlen R hR
  have hseq := seqTM_hoareTime PendingEquationDispatch.machine (FormulaSpanStep.machine 24) he (by
    rintro inp work out ⟨hcur, hr⟩
    obtain ⟨hin, hwork, hout⟩ := hcur.phase
    rw [hin, hwork, hout]
    exact ⟨hcur, hr⟩) hs
  apply hseq.consequence (fun _ _ _ hr => hr)
  · intro inp work out hr
    simpa only [emitted, ← RowEntriesCodec.entries_append, PreorderEmissionControl.step] using hr
  · dsimp [timeBound]
    omega

end JointThermoComplexity.Complexity.EquationEmissionStep

#print axioms JointThermoComplexity.Complexity.EquationEmissionStep.timePolynomial_eval
#print axioms JointThermoComplexity.Complexity.EquationEmissionStep.scan_hoareTime
#print axioms JointThermoComplexity.Complexity.EquationEmissionStep.hoareTime
