module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaBranches

set_option autoImplicit false
@[expose] public section

/-! Load formula tag flags while preserving both pending counts and the inner fuel. -/

namespace JointThermoComplexity.Complexity.SourceFormulaTagRead
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters
variable {n : ℕ}

def afterTag (count : ℕ) (before input : List Bool) : SourceTermLoopState.State :=
  ⟨before ++ input.take 3, input.drop 3, count, SourceTags.accepted input⟩

def machine (d : Layout n) : TM (n + 2) :=
  SourceTagFlags.machine (fun i => (d.tags i).castSucc) (NaturalScanBuffer.flag n)

theorem hoareTime (d : Layout n) (L arity count : ℕ) (initial : Bool) (before input emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R) :
    (machine d).HoareTime (Inv d L arity emitted R ⟨before, input, count, initial⟩)
      (fun inp work out => Inv d L arity emitted R (afterTag count before input) inp work out ∧
        SourceTagDispatch.Reads (List.ofFn (fun i => (d.tags i).castSucc)) (SourceTermToken.tagBits input) work) 6 := by
  let RT : (Fin (n + 1) → Tape) → Prop := fun work => IsReg L (work d.termFuel) ∧
    (∃ q, q ≤ L + 2 ∧ IsReg q (work d.termPending)) ∧ IsReg count (work d.formulaPending) ∧ R work
  have hRT : ∀ work work', (∀ j, j ≠ d.left → j ≠ d.right → j ≠ NaturalMachine.flagIndex n →
      (∀ i, j ≠ d.tags i) → work' j = work j) → RT work → RT work' := by
    rintro work work' hw ⟨hf, ht, hp, hr⟩
    have hFuel := hw d.termFuel d.fuelSep.left d.fuelSep.right d.fuelSep.flag d.fuelSep.tags
    have hTerm := hw d.termPending d.termSep.left d.termSep.right d.termSep.flag d.termSep.tags
    have hFormula := hw d.formulaPending d.formulaSep.left d.formulaSep.right d.formulaSep.flag d.formulaSep.tags
    exact ⟨by simpa only [hFuel] using hf, by simpa only [hTerm] using ht, by simpa only [hFormula] using hp,
      hR _ _ (fun j hj => hw j hj.left hj.right hj.flag hj.tags) hr⟩
  have htag := SourceTermTagRead.hoareTime d.tags d.left d.right d.tagSep d.operandSep L arity initial before input emitted RT hRT
  rintro inp work out ⟨hc, hr, hp, hf⟩
  obtain ⟨c, t, ht, hd, hh, hc', hr', hheads', hv', hreads'⟩ := htag inp work out
    ⟨hc, ⟨hr.base.safe, hr.base.markers, hr.base.encoded, hr.base.candidate, hr.base.arityBits, hr.base.arityZero,
      hr.base.flagHead, hr.termFuel, hr.termPending, hp, hr.base.frame⟩, hr.tagHeads, hf⟩
  rcases hr'.frame with ⟨hFuel, hTerm, hFormula, hFrame⟩
  have hready : Ready d L arity R c.work :=
    ⟨⟨hr'.safe, hr'.markers, hr'.encoded, hr'.candidate, hr'.arityBits, hr'.arityZero, hr'.flagHead, hFrame⟩,
      hFuel, hTerm, hheads'⟩
  exact ⟨c, t, ht, hd, hh, ⟨hc', hready, hFormula, hv'⟩, hreads'⟩

end JointThermoComplexity.Complexity.SourceFormulaTagRead

#print axioms JointThermoComplexity.Complexity.SourceFormulaTagRead.hoareTime
