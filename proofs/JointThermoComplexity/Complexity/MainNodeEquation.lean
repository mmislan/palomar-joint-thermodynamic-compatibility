module
public import proofs.JointThermoComplexity.Complexity.EquationWorkReset

set_option autoImplicit false
@[expose] public section

/-! Reset local scratch, compute the current root, and emit the exact selected local rows. -/

namespace JointThermoComplexity.Complexity.MainNodeEquation
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryCounterInit MainEquationWork
open HeaderAt (Cursor)
open DInstabilityComplexity.MachineConstruction

def root (mode : Bool) (arity : ℕ) (s : FormulaSpanControl.State) : ℕ :=
  arity + GeneratedNodeAddress.corrected mode s.coordinates

def Bounded (s : FormulaSpanControl.State) (arity L N : ℕ) (R : Work → Prop) (work : Work) : Prop :=
  ∃ adjusted counts values, Before s arity L adjusted counts values R work ∧ adjusted ≤ N ∧
    counts.total ≤ 14 * N + 2 ∧ (∀ i, values i ≤ 30 * N + 3) ∧ values 8 = 0

theorem corrected_le (mode : Bool) (coords : ℕ) : GeneratedNodeAddress.corrected mode coords ≤ coords := by
  cases mode <;> simp [GeneratedNodeAddress.corrected]

theorem basic_other : ∀ j, LocalBranchState.BasicPorts j → j ≠ GeneratedNodeAddress.adjusted ∧ j ≠ GeneratedNodeAddress.root := by
  unfold LocalBranchState.BasicPorts
  decide

theorem extra_other : ∀ j, ExtraPort j → j ≠ GeneratedNodeAddress.adjusted ∧ j ≠ GeneratedNodeAddress.root := by
  unfold ExtraPort
  decide

theorem frame_address (s : FormulaSpanControl.State) (arity L old new : ℕ) (R : Work → Prop) (hR : Stable R)
    (work work' : Work) (hr : Frame s arity L old R work)
    (he : ∀ j, j ≠ GeneratedNodeAddress.adjusted → j ≠ GeneratedNodeAddress.root → work' j = work j)
    (hadj : IsReg new (work' adjustedPort)) : Frame s arity L new R work' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hadj, hR work work' (fun j hj => he j (extra_other j hj).1 (extra_other j hj).2) hr.extra⟩
  · simpa only [he mainTerm (by decide) (by decide)] using hr.termReg
  · simpa only [he mainFormula (by decide) (by decide)] using hr.formulaReg
  · simpa only [he mainCoordinates (by decide) (by decide)] using hr.coordinatesReg
  · intro i
    have ha : mainTags i ≠ GeneratedNodeAddress.adjusted := by
      intro hh
      have hv := congrArg Fin.val hh
      change i.val = 28 at hv
      omega
    have hb : mainTags i ≠ GeneratedNodeAddress.root := by
      intro hh
      have hv := congrArg Fin.val hh
      change i.val = 19 at hv
      omega
    simpa only [he _ ha hb] using hr.tagHeads i
  · simpa only [he mainFlag (by decide) (by decide)] using hr.flagHead
  · simpa only [he lengthPort (by decide) (by decide)] using hr.lengthReg
  · simpa only [he arityPort (by decide) (by decide)] using hr.arityReg

theorem address_hoareTime (mode : Bool) (s : FormulaSpanControl.State) (arity L adjusted : ℕ)
    (counts : Counts) (values : Fin 9 → ℕ) (hz : values 8 = 0) (emitted : List Bool)
    (R : Work → Prop) (hR : Stable R) :
    (GeneratedNodeAddress.machine mode).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Before s arity L adjusted counts values R work)
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧
        Before s arity L (GeneratedNodeAddress.corrected mode s.coordinates) counts (Function.update values 0 (root mode arity s)) R work)
      (2 * adjusted + 2 * values 0 + 16 * s.coordinates + 5 * arity + 77) := by
  rintro inp work out ⟨hc, hs, hp, hr⟩
  let C : Work → Prop := fun work' => ∀ j, j ≠ GeneratedNodeAddress.adjusted → j ≠ GeneratedNodeAddress.root → work' j = work j
  have hC : GeneratedNodeAddress.Stable C := by
    intro work' work'' he hh j ha hb
    exact (he j ha hb).trans (hh j ha hb)
  have hzero : IsReg 0 (work GeneratedNodeAddress.zero) := by
    change IsReg 0 (work (AddressCounterPlacement.slot 8))
    simpa only [hz] using hr.addresses 8
  obtain ⟨d, t, ht, hd, hh, hc', hs', hadj, hroot, _, _, _, he⟩ :=
    GeneratedNodeAddress.hoareTime mode adjusted (values 0) s.coordinates arity s.before s.input emitted C hC
      inp work out ⟨hc, hs, hr.basic.frame.adjustedReg, hr.addresses 0, hr.basic.frame.coordinatesReg,
        hr.basic.frame.arityReg, hzero, fun _ _ _ => rfl⟩
  have hframe := frame_address s arity L adjusted (GeneratedNodeAddress.corrected mode s.coordinates) R hR work d.work
    hr.basic.frame he hadj
  have hb0 : LocalBranchState.Basic counts L (fun _ => True) work :=
    ⟨hr.basic.tagHeads, hr.basic.flagHead, hr.basic.termReg, hr.basic.formulaReg, hr.basic.nodeReg,
      hr.basic.fuelReg, hr.basic.positionReg, hr.basic.scratchReg, trivial⟩
  have hb := LocalBranchState.basic_transfer counts L (fun _ => True) work d.work hb0
    (fun j hj => he j (basic_other j hj).1 (basic_other j hj).2) trivial
  have hb' : LocalBranchState.Basic counts L (Frame s arity L (GeneratedNodeAddress.corrected mode s.coordinates) R) d.work :=
    ⟨hb.tagHeads, hb.flagHead, hb.termReg, hb.formulaReg, hb.nodeReg, hb.fuelReg, hb.positionReg, hb.scratchReg, hframe⟩
  have hm : ∀ j, j ≠ LocalBranchState.anchor → (d.work j).cells 0 = Γ.start := by
    intro j hj
    by_cases ha : j = GeneratedNodeAddress.adjusted
    · subst j
      exact hadj.cell0
    · by_cases hb : j = GeneratedNodeAddress.root
      · subst j
        exact hroot.cell0
      · rw [he j ha hb]
        exact hr.markers j hj
  have hvalues : AddressCounterPlacement.Registers (Function.update values 0 (root mode arity s)) d.work := by
    intro i
    by_cases hi : i = 0
    · subst i
      rw [Function.update_self]
      change IsReg (root mode arity s) (d.work GeneratedNodeAddress.root)
      exact hroot
    · have ha : AddressCounterPlacement.slot i ≠ GeneratedNodeAddress.adjusted := by
        intro heq
        have hv := congrArg Fin.val heq
        change 19 + i.val = 28 at hv
        omega
      have hb : AddressCounterPlacement.slot i ≠ GeneratedNodeAddress.root := by
        intro heq
        apply hi
        exact placeWorkIdx_injective 19 4 heq
      rw [Function.update_of_ne hi, he _ ha hb]
      exact hr.addresses i
  exact ⟨d, t, ht, hd, hh, hc', hs', by simpa only [he LocalBranchState.anchor (by decide) (by decide)] using hp,
    hb', hm, hvalues⟩

def machine (mode : Bool) : TM 32 :=
  seqTM EquationWorkReset.machine (seqTM (GeneratedNodeAddress.machine mode) (EquationTagDispatch.machine mode))

noncomputable def timeBound (N : ℕ) : ℕ := counterIterTime 9 (30 * N + 3) + EquationBranchPolynomial.timePolynomial.eval (2 * N) + 51 * N + 110

noncomputable def timePolynomial : Polynomial ℕ :=
  (counterTimePolynomial 9).comp (30 * Polynomial.X + 3) +
    EquationBranchPolynomial.timePolynomial.comp (2 * Polynomial.X) + 51 * Polynomial.X + 110

theorem timePolynomial_eval (N : ℕ) : timePolynomial.eval N = timeBound N := by
  simp [timePolynomial, timeBound, counterTimePolynomial_eval]

theorem hoareTime (mode : Bool) (s : FormulaSpanControl.State) (arity L N adjusted : ℕ)
    (counts : Counts) (values : Fin 9 → ℕ) (emitted : List Bool)
    (ha : arity ≤ N) (hL : L ≤ N) (hc : s.coordinates ≤ N) (hp : s.before.length ≤ N) (hlen : s.input.length ≤ L)
    (hadj : adjusted ≤ N) (hq : counts.total ≤ 14 * N + 2) (hv : ∀ i, values i ≤ 30 * N + 3)
    (R : Work → Prop) (hR : Stable R) :
    (machine mode).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Before s arity L adjusted counts values R work)
      (fun inp work out => Cursor s.before s.input
        (emitted ++ RowEntriesCodec.entries (EquationTagDispatch.rows mode L (root mode arity s) s.input)) inp work out ∧
          Bounded s arity L N R work) (timeBound N) := by
  let adjusted' := GeneratedNodeAddress.corrected mode s.coordinates
  let values' := Function.update EquationWorkReset.zeroValues 0 (root mode arity s)
  have hcorr := corrected_le mode s.coordinates
  have hb : ∀ i, values' i ≤ arity + s.coordinates := by
    intro i
    by_cases hi : i = 0
    · subst i
      simp only [values', Function.update_self, root]
      omega
    · simp only [values', Function.update_of_ne hi, EquationWorkReset.zeroValues, Nat.zero_le]
  have hz : values' 8 = 0 := by simp [values', EquationWorkReset.zeroValues]
  have hreset := EquationWorkReset.hoareTime counts values L 0 (30 * N + 3) hv s.before s.input emitted
    (Frame s arity L adjusted R) (frame_stable s arity L adjusted R hR)
  have haddress := address_hoareTime mode s arity L adjusted EquationWorkReset.zeroCounts EquationWorkReset.zeroValues rfl emitted R hR
  have hemit := EquationBranchPolynomial.hoareTime mode EquationWorkReset.zeroCounts values' L (arity + s.coordinates) 0 (2 * N)
    s.before s.input emitted hz hb (by rfl) hlen (by omega) (by omega) (by omega) (by omega)
    (Frame s arity L adjusted' R) (frame_stable s arity L adjusted' R hR)
  have hbody := seqTM_hoareTime (GeneratedNodeAddress.machine mode) (EquationTagDispatch.machine mode) haddress (by
    rintro inp work out ⟨hcur, hs, ha, hr⟩
    obtain ⟨hin, hwork, hout⟩ := hcur.phase
    rw [hin, hwork, hout]
    exact ⟨hcur, hs, ha, hr⟩) hemit
  have hseq := seqTM_hoareTime EquationWorkReset.machine
    (seqTM (GeneratedNodeAddress.machine mode) (EquationTagDispatch.machine mode)) hreset (by
      rintro inp work out ⟨hcur, hs, ha, hr⟩
      obtain ⟨hin, hwork, hout⟩ := hcur.phase
      rw [hin, hwork, hout]
      exact ⟨hcur, hs, ha, hr⟩) hbody
  apply hseq.consequence (fun _ _ _ ht => ht)
  · rintro inp work out ⟨hcur, hs, ha', counts', values'', hr, _, hz', hv', hq'⟩
    refine ⟨?_, adjusted', counts', values'', ⟨hs, ha', hr⟩, hcorr.trans hc, ?_, ?_, hz'⟩
    · simpa only [values', Function.update_self] using hcur
    · omega
    · intro i
      have hi := hv' i
      omega
  · dsimp [EquationWorkReset.timeBound, EquationWorkReset.zeroValues, timeBound]
    omega

end JointThermoComplexity.Complexity.MainNodeEquation

#print axioms JointThermoComplexity.Complexity.MainNodeEquation.address_hoareTime
#print axioms JointThermoComplexity.Complexity.MainNodeEquation.timePolynomial_eval
#print axioms JointThermoComplexity.Complexity.MainNodeEquation.hoareTime
