module
public import proofs.JointThermoComplexity.Complexity.EquationTagDispatch

set_option autoImplicit false
@[expose] public section

/-! A single natural-coefficient polynomial bounds the complete fresh-tag local emission machine. -/

namespace JointThermoComplexity.Complexity.EquationBranchPolynomial
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryCounterInit LocalBranchState
open HeaderAt (Cursor)
open DInstabilityComplexity.MachineConstruction

theorem counter_time_mono (k : ℕ) : Monotone (counterIterTime k) := by
  induction k with
  | zero => intro a b _; exact le_rfl
  | succ k ih =>
    intro a b hab
    have hn : counterNextBound a ≤ counterNextBound b := by dsimp [counterNextBound]; gcongr
    have ht := ih hn
    change 100 * (a + 1) ^ 4 + 1 + counterIterTime k (counterNextBound a) ≤
      100 * (b + 1) ^ 4 + 1 + counterIterTime k (counterNextBound b)
    exact add_le_add (by gcongr) ht

theorem prepared_time_mono : Monotone PreparedLocalEquation.timeBound := by
  intro a b hab
  exact add_le_add (Nat.add_le_add_right (counter_time_mono 10 hab) 1) (by gcongr)

theorem scan_bound_mono {L B C L' B' C' : ℕ} (hL : L ≤ L') (hB : B ≤ B') (hC : C ≤ C') :
    NonleafEquationBranch.scanBound L B C ≤ NonleafEquationBranch.scanBound L' B' C' := by
  dsimp [NonleafEquationBranch.scanBound]
  gcongr

theorem forward_time_mono {L B C L' B' C' : ℕ} (hL : L ≤ L') (hB : B ≤ B') (hC : C ≤ C') :
    NonleafEquationBranch.forwardTime L B C ≤ NonleafEquationBranch.forwardTime L' B' C' := by
  have h1 := scan_bound_mono hL hB hC
  have h2 := scan_bound_mono hL (by omega : B + 4 * L ≤ B' + 4 * L')
    (by omega : C + 7 * L + 1 ≤ C' + 7 * L' + 1)
  have h3 := prepared_time_mono (by omega : B + 8 * L ≤ B' + 8 * L')
  dsimp [NonleafEquationBranch.forwardTime]
  omega

theorem time_bound_mono {L B C p L' B' C' p' : ℕ} (hL : L ≤ L') (hB : B ≤ B') (hC : C ≤ C') (hp : p ≤ p') :
    EquationTagDispatch.timeBound L B C p ≤ EquationTagDispatch.timeBound L' B' C' p' := by
  have hi : ReusableIndexEmitter.timeBound B ≤ ReusableIndexEmitter.timeBound B' := by
    dsimp [ReusableIndexEmitter.timeBound]
    gcongr
  have hf := forward_time_mono hL hB hC
  dsimp [EquationTagDispatch.timeBound, EquationTagDispatch.branchTime, EquationTagDispatch.leafTime, EquationTagDispatch.nodeTime]
  omega

noncomputable def timePolynomial : Polynomial ℕ :=
  80 * Polynomial.X ^ 2 + 335 * Polynomial.X + 244 +
    PreparedLocalEquation.timePolynomial.comp (9 * Polynomial.X)

theorem timePolynomial_eval (N : ℕ) : timePolynomial.eval N = EquationTagDispatch.timeBound N N N N := by
  have he : timePolynomial.eval N = 80 * N ^ 2 + 335 * N + 244 + PreparedLocalEquation.timeBound (9 * N) := by
    simp [timePolynomial, PreparedLocalEquation.timePolynomial_eval]
  rw [he]
  dsimp [EquationTagDispatch.timeBound, EquationTagDispatch.branchTime, EquationTagDispatch.leafTime, EquationTagDispatch.nodeTime,
    NonleafEquationBranch.forwardTime, NonleafEquationBranch.scanBound]
  rw [ReusableIndexEmitter.timeBound_eq, show N + 8 * N = 9 * N by omega]
  ring

theorem hoareTime (termMode : Bool) (counts : Counts) (values : Fin 9 → ℕ) (L B C N : ℕ)
    (before input emitted : List Bool) (hz : values 8 = 0) (hv : ∀ i, values i ≤ B) (hc : counts.total ≤ C)
    (hlen : input.length ≤ L) (hL : L ≤ N) (hB : B ≤ N) (hC : C ≤ N) (hp : before.length ≤ N)
    (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (EquationTagDispatch.machine termMode).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ EquationTagDispatch.Before counts values L R work)
      (fun inp work out => Cursor before input
        (emitted ++ RowEntriesCodec.entries (EquationTagDispatch.rows termMode L (values 0) input)) inp work out ∧
          EquationTagDispatch.After (values 0) L B C R work) (timePolynomial.eval N) := by
  apply (EquationTagDispatch.hoareTime termMode counts values L B C before input emitted hz hv hc hlen R hR).mono_bound
  rw [timePolynomial_eval]
  exact time_bound_mono hL hB hC hp

end JointThermoComplexity.Complexity.EquationBranchPolynomial

#print axioms JointThermoComplexity.Complexity.EquationBranchPolynomial.timePolynomial_eval
#print axioms JointThermoComplexity.Complexity.EquationBranchPolynomial.hoareTime
