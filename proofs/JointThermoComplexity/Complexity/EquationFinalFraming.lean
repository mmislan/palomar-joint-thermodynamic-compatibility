module
public import proofs.JointThermoComplexity.Complexity.EquationRootActivation

set_option autoImplicit false
@[expose] public section

/-! Append the root activation rows and exactly one outer row-list terminator. -/

namespace JointThermoComplexity.Complexity.EquationFinalFraming
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery MainNodeEquation
open HeaderAt (Cursor)

def machine : TM 32 := seqTM EquationRootActivation.machine (emitBitsTM [false])
def timeBound (N : ℕ) : ℕ := EquationRootActivation.timeBound N + 2
noncomputable def timePolynomial : Polynomial ℕ := EquationRootActivation.timePolynomial + 2

theorem timePolynomial_eval (N : ℕ) : timePolynomial.eval N = timeBound N := by
  simp [timePolynomial, timeBound, EquationRootActivation.timePolynomial_eval]

theorem time_mono : Monotone timeBound := by
  intro a b hab
  have hc := EquationBranchPolynomial.counter_time_mono 9 (by omega : 30 * a + 3 ≤ 30 * b + 3)
  have hp := EquationBranchPolynomial.prepared_time_mono hab
  dsimp [timeBound, EquationRootActivation.timeBound]
  omega

theorem combine (prefixBits : List Bool) (ps : PreorderLocalRows.Rows) (arity : ℕ) :
    (prefixBits ++ RowEntriesCodec.entries ps) ++ RowWordCodec.rows (EquationRootActivation.rows arity) =
      prefixBits ++ RowWordCodec.rows (ps ++ EquationRootActivation.rows arity) := by
  simp only [← RowEntriesCodec.complete, RowEntriesCodec.entries_append, List.append_assoc]

theorem hoareTime (s : FormulaSpanControl.State) (arity L N : ℕ) (ha : arity ≤ N) (emitted : List Bool) :
    machine.HoareTime
      (fun inp tapes out => Cursor s.before s.input emitted inp tapes out ∧ Bounded s arity L N (fun _ => True) tapes)
      (fun inp tapes out => Cursor s.before s.input (emitted ++ RowWordCodec.rows (EquationRootActivation.rows arity)) inp tapes out ∧
        (∀ j, Parked (tapes j))) (timeBound N) := by
  have ha := EquationRootActivation.hoareTime s arity L N ha emitted
  have hf := FixedOutput.hoareTime (w := 32) [false] s.before s.input
    (emitted ++ RowEntriesCodec.entries (EquationRootActivation.rows arity)) (fun _ => True)
  have hseq := seqTM_hoareTime EquationRootActivation.machine (emitBitsTM (n := 32) [false]) ha (by
    rintro inp tapes out ⟨hc, hs⟩
    obtain ⟨hin, hwork, hout⟩ := hc.phase
    rw [hin, hwork, hout]
    exact ⟨hc, hs, trivial⟩) hf
  apply hseq.consequence (fun _ _ _ h => h)
  · rintro inp tapes out ⟨hc, hs, _⟩
    exact ⟨by simpa only [List.append_assoc, RowEntriesCodec.complete] using hc, hs⟩
  · simp only [List.length_cons, List.length_nil]
    dsimp [timeBound]
    omega

end JointThermoComplexity.Complexity.EquationFinalFraming

#print axioms JointThermoComplexity.Complexity.EquationFinalFraming.hoareTime
