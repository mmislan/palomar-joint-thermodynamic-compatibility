module
public import proofs.JointThermoComplexity.Complexity.EquationLoopInitialization

set_option autoImplicit false
@[expose] public section

/-! Emit root activation at the original arity after the main traversal has finished. -/

namespace JointThermoComplexity.Complexity.EquationRootActivation
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryCounterInit MainEquationWork MainNodeEquation
open HeaderAt (Cursor)
open DInstabilityComplexity.MachineConstruction

def rootPort : Fin 32 := 19
def zeroPort : Fin 32 := 27
def copyRoot : TM 32 := SelectedAddressArithmetic.machine rootPort arityPort zeroPort (by decide) (by decide)
def rows (arity : ℕ) : PreorderLocalRows.Rows :=
  PreorderLocalRows.words [SparseInteger.sub (SparseInteger.atom arity) (SparseInteger.constant 1)]

theorem copy_hoareTime (s : FormulaSpanControl.State) (arity L adjusted : ℕ) (counts : Counts) (values : Fin 9 → ℕ)
    (hz : values 8 = 0) (emitted : List Bool) (R : Work → Prop) (hR : MainEquationWork.Stable R) :
    copyRoot.HoareTime
      (fun inp tapes out => Cursor s.before s.input emitted inp tapes out ∧ Before s arity L adjusted counts values R tapes)
      (fun inp tapes out => Cursor s.before s.input emitted inp tapes out ∧
        Before s arity L adjusted counts (Function.update values 0 arity) R tapes) (2 * values 0 + 5 * arity + 15) := by
  rintro inp tapes out ⟨hc, hs, hp, hr⟩
  let C : Work → Prop := fun tapes' => ∀ j, j ≠ rootPort → tapes' j = tapes j
  have hC : ∀ tapes' tapes'', (∀ j, j ≠ rootPort → tapes'' j = tapes' j) → C tapes' → C tapes'' := by
    intro tapes' tapes'' he hh j hj
    exact (he j hj).trans (hh j hj)
  have hzero : IsReg 0 (tapes zeroPort) := by
    change IsReg 0 (tapes (AddressCounterPlacement.slot 8))
    simpa only [hz] using hr.addresses 8
  obtain ⟨d, t, ht, hd, hh, hc', hs', hroot, _, _, he⟩ :=
    SelectedAddressArithmetic.copy_hoareTime rootPort arityPort zeroPort (by decide) (by decide)
      (values 0) arity s.before s.input emitted C hC inp tapes out
      ⟨hc, hs, hr.addresses 0, hr.basic.frame.arityReg, hzero, fun _ _ => rfl⟩
  have hbasic : ∀ j, LocalBranchState.BasicPorts j → j ≠ rootPort := by unfold LocalBranchState.BasicPorts; decide
  have hprotected : ∀ j, LocalBranchState.Protected j → j ≠ rootPort := by unfold LocalBranchState.Protected; decide
  have hf := frame_stable s arity L adjusted R hR tapes d.work (fun j hj => he j (hprotected j hj)) hr.basic.frame
  have hb := LocalBranchState.basic_transfer counts L (Frame s arity L adjusted R) tapes d.work hr.basic
    (fun j hj => he j (hbasic j hj)) hf
  have hm : ∀ j, j ≠ LocalBranchState.anchor → (d.work j).cells 0 = Γ.start := by
    intro j hj
    by_cases hj' : j = rootPort
    · subst j
      exact hroot.cell0
    · rw [he j hj']
      exact hr.markers j hj
  have ha : AddressCounterPlacement.Registers (Function.update values 0 arity) d.work := by
    intro i
    by_cases hi : i = 0
    · subst i
      rw [Function.update_self]
      change IsReg arity (d.work rootPort)
      exact hroot
    · have hn : AddressCounterPlacement.slot i ≠ rootPort := by
        intro h
        apply hi
        exact placeWorkIdx_injective 19 4 h
      rw [Function.update_of_ne hi, he _ hn]
      exact hr.addresses i
  exact ⟨d, t, ht, hd, hh, hc', hs', by simpa only [he LocalBranchState.anchor (by decide)] using hp, hb, hm, ha⟩

theorem template_rows (arity : ℕ) :
    LocalEquationTemplates.wordRows .activate (LocalAddressSetup.addressValues (Function.update EquationWorkReset.zeroValues 0 arity)) = rows arity := by
  rw [LocalAddressSetup.addressValues_eq, LocalEquationTemplates.wordRows_eq]
  simp [rows, LocalEquationTemplates.realize, LocalEquationTemplates.rows, LocalEquationTemplates.formulaValues,
    NumberedFormulaEquations.signPorts, PreorderLocalRows.words, NumberedTermEquations.relabel_sub,
    NumberedTermEquations.relabel_atom, NumberedTermEquations.relabel_constant]

def machine : TM 32 := seqTM EquationWorkReset.machine (seqTM copyRoot (PreparedLocalEquation.machine .activate))
def timeBound (N : ℕ) : ℕ := counterIterTime 9 (30 * N + 3) + PreparedLocalEquation.timeBound N + 33 * N + 50

noncomputable def timePolynomial : Polynomial ℕ :=
  (counterTimePolynomial 9).comp (30 * Polynomial.X + 3) + PreparedLocalEquation.timePolynomial + 33 * Polynomial.X + 50

theorem timePolynomial_eval (N : ℕ) : timePolynomial.eval N = timeBound N := by
  simp [timePolynomial, timeBound, counterTimePolynomial_eval, PreparedLocalEquation.timePolynomial_eval]

theorem hoareTime (s : FormulaSpanControl.State) (arity L N : ℕ) (ha : arity ≤ N) (emitted : List Bool) :
    machine.HoareTime
      (fun inp tapes out => Cursor s.before s.input emitted inp tapes out ∧ Bounded s arity L N (fun _ => True) tapes)
      (fun inp tapes out => Cursor s.before s.input (emitted ++ RowEntriesCodec.entries (rows arity)) inp tapes out ∧
        (∀ j, Parked (tapes j))) (timeBound N) := by
  rintro inp tapes out ⟨hc, adjusted, counts, values, hr, _, hq, hv, _⟩
  let R := Frame s arity L adjusted (fun _ => True)
  have htrue : MainEquationWork.Stable (fun _ : Work => True) := by
    intro _ _ _ _
    trivial
  have hR := frame_stable s arity L adjusted (fun _ => True) htrue
  let vals := Function.update EquationWorkReset.zeroValues 0 arity
  have hvals : ∀ i, vals i ≤ N := by
    intro i
    by_cases hi : i = 0
    · subst i
      simpa only [vals, Function.update_self] using ha
    · simp only [vals, Function.update_of_ne hi, EquationWorkReset.zeroValues, Nat.zero_le]
  have hreset := EquationWorkReset.hoareTime counts values L 0 (30 * N + 3) hv s.before s.input emitted R hR
  have hcopy := copy_hoareTime s arity L adjusted EquationWorkReset.zeroCounts EquationWorkReset.zeroValues rfl emitted (fun _ => True) htrue
  have hprepare := LocalBranchPrepare.hoareTime .activate EquationWorkReset.zeroCounts vals L 0 N hvals s.before s.input emitted R hR
  have hrest := seqTM_hoareTime copyRoot (PreparedLocalEquation.machine .activate) hcopy (by
    rintro inp tapes out ⟨hcur, hs, hp, hr⟩
    obtain ⟨hin, hwork, hout⟩ := hcur.phase
    rw [hin, hwork, hout]
    exact ⟨hcur, hs, hp, hr⟩) hprepare
  have hseq := seqTM_hoareTime EquationWorkReset.machine (seqTM copyRoot (PreparedLocalEquation.machine .activate)) hreset (by
    rintro inp tapes out ⟨hcur, hs, hp, hr⟩
    obtain ⟨hin, hwork, hout⟩ := hcur.phase
    rw [hin, hwork, hout]
    exact ⟨hcur, hs, hp, hr⟩) hrest
  obtain ⟨d, t, ht, hd, hh, hcur, hs, _, _⟩ := hseq inp tapes out ⟨hc, hr⟩
  refine ⟨d, t, ?_, hd, hh, ?_, hs⟩
  · dsimp [timeBound, EquationWorkReset.timeBound, EquationWorkReset.zeroValues] at ht ⊢
    omega
  · simpa only [vals, template_rows] using hcur

end JointThermoComplexity.Complexity.EquationRootActivation

#print axioms JointThermoComplexity.Complexity.EquationRootActivation.hoareTime
