module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaRegisters

set_option autoImplicit false
@[expose] public section

/-! The nested two-term parser preserves the outer formula count and surrounding frame. -/

namespace JointThermoComplexity.Complexity.SourceFormulaPairCall
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters
variable {n : ℕ}

def afterPair (arity L count : ℕ) (before input : List Bool) : SourceTermLoopState.State :=
  ⟨before ++ (SourceTermPair.state arity L input).before, (SourceTermPair.state arity L input).input,
    count, (SourceTermPair.state arity L input).valid⟩

def machine (d : Layout n) : TM (n + 2) := SourceTermPair.machine d.tags d.termFuel d.termPending d.left d.right

def timeBound (L : ℕ) : ℕ := 34 * L ^ 2 + 93 * L + 31

theorem hoareTime (d : Layout n) (L arity count : ℕ) (ha : arity.bits.length ≤ L)
    (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R) :
    (machine d).HoareTime
      (Inv d L arity emitted R ⟨before, input, count, true⟩)
      (Inv d L arity emitted R (afterPair arity L count before input)) (timeBound L) := by
  let RF : (Fin (n + 1) → Tape) → Prop := fun work => IsReg count (work d.formulaPending) ∧ R work
  have hRF : ∀ work work', (∀ j, j ≠ d.left → j ≠ d.right → j ≠ NaturalMachine.flagIndex n →
      (∀ i, j ≠ d.tags i) → j ≠ d.termPending → j ≠ d.termFuel → work' j = work j) → RF work → RF work' := by
    rintro work work' hw ⟨hf, hr⟩
    have heq := hw d.formulaPending d.formulaSep.left d.formulaSep.right d.formulaSep.flag d.formulaSep.tags d.pendingDistinct.symm d.fuelFormula.symm
    exact ⟨by simpa only [heq] using hf,
      hR _ _ (fun j hj => hw j hj.left hj.right hj.flag hj.tags hj.termPending hj.termFuel) hr⟩
  rintro inp work out ⟨hc, hr, hf, hv⟩
  obtain ⟨q, hq, hqp⟩ := hr.termPending
  have hpair := SourceTermPair.hoareTime d.tags d.termFuel d.termPending d.left d.right d.tagSep d.operandSep d.termSep
    d.fuelSep d.fuelTerm L arity q ha before input emitted hlen RF hRF
  obtain ⟨c, t, ht, hd, hh, ⟨hc', hr', hq', hheads', hv'⟩, hFuel'⟩ := hpair inp work out
    ⟨⟨hc, ⟨hr.base.safe, hr.base.markers, hr.base.encoded, hr.base.candidate, hr.base.arityBits, hr.base.arityZero,
      hr.base.flagHead, hf, hr.base.frame⟩, hqp, hr.tagHeads, hv⟩, hr.termFuel⟩
  have hbounds := SourceTermPair.state_bounds arity L input
  have hready : Ready d L arity R c.work :=
    ⟨⟨hr'.safe, hr'.markers, hr'.encoded, hr'.candidate, hr'.arityBits, hr'.arityZero, hr'.flagHead, hr'.frame.2⟩,
      hFuel', ⟨(SourceTermPair.state arity L input).pending, by omega, hq'⟩, hheads'⟩
  exact ⟨c, t, ht.trans (SourceTermPair.bounded_timeBound L q hq), hd, hh, hc', hready, hr'.frame.1, hv'⟩

end JointThermoComplexity.Complexity.SourceFormulaPairCall

#print axioms JointThermoComplexity.Complexity.SourceFormulaPairCall.hoareTime
