module
public import proofs.JointThermoComplexity.Complexity.EquationBranchPolynomial
public import proofs.JointThermoComplexity.Complexity.FormulaSpanStep
public import proofs.JointThermoComplexity.Complexity.GeneratedNodeAddress

set_option autoImplicit false
@[expose] public section

/-! A common work frame joins main traversal, query state and local equation emission. -/

namespace JointThermoComplexity.Complexity.MainEquationWork
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryCounterInit
open HeaderAt (Cursor)

def lengthPort : Fin 32 := 16
def arityPort : Fin 32 := 18
def adjustedPort : Fin 32 := 28
def mainTags : Fin 3 → Fin 32 := TermSpanRegisters.tags 25
def mainTerm : Fin 32 := TermSpanRegisters.pending 25
def mainCoordinates : Fin 32 := TermSpanRegisters.nodeCounter 25
def mainFlag : Fin 32 := TermSpanRegisters.flag 25
def mainFormula : Fin 32 := FormulaSpanRegisters.formulaPending 24

def ExtraPort (j : Fin 32) : Prop := j.val = 4 ∨ j.val = 31
def Stable (R : Work → Prop) : Prop :=
  ∀ work work', (∀ j, ExtraPort j → work' j = work j) → R work → R work'

structure Frame (s : FormulaSpanControl.State) (arity L adjusted : ℕ) (R : Work → Prop) (work : Work) : Prop where
  termReg : IsReg s.terms (work mainTerm)
  formulaReg : IsReg s.formulas (work mainFormula)
  coordinatesReg : IsReg s.coordinates (work mainCoordinates)
  tagHeads : ∀ i, (work (mainTags i)).head = 1
  flagHead : (work mainFlag).head = 1
  lengthReg : IsReg L (work lengthPort)
  arityReg : IsReg arity (work arityPort)
  adjustedReg : IsReg adjusted (work adjustedPort)
  extra : R work

def Ready (s : FormulaSpanControl.State) (arity L adjusted : ℕ) (counts : Counts) (values : Fin 9 → ℕ)
    (R : Work → Prop) : Work → Prop := LocalBranchState.Ready counts values L (Frame s arity L adjusted R)

def Before (s : FormulaSpanControl.State) (arity L adjusted : ℕ) (counts : Counts) (values : Fin 9 → ℕ)
    (R : Work → Prop) : Work → Prop := EquationTagDispatch.Before counts values L (Frame s arity L adjusted R)

theorem extra_protected : ∀ j, ExtraPort j → LocalBranchState.Protected j := by
  unfold ExtraPort LocalBranchState.Protected
  decide

theorem frame_stable (s : FormulaSpanControl.State) (arity L adjusted : ℕ) (R : Work → Prop) (hR : Stable R) :
    LocalBranchState.Stable (Frame s arity L adjusted R) := by
  rintro work work' he hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hR work work' (fun j hj => he j (extra_protected j hj)) hr.extra⟩
  · simpa only [he mainTerm (by unfold LocalBranchState.Protected; decide)] using hr.termReg
  · simpa only [he mainFormula (by unfold LocalBranchState.Protected; decide)] using hr.formulaReg
  · simpa only [he mainCoordinates (by unfold LocalBranchState.Protected; decide)] using hr.coordinatesReg
  · intro i
    have hi : LocalBranchState.Protected (mainTags i) := Or.inl (by change i.val < 8; omega)
    simpa only [he _ hi] using hr.tagHeads i
  · simpa only [he mainFlag (by unfold LocalBranchState.Protected; decide)] using hr.flagHead
  · simpa only [he lengthPort (by unfold LocalBranchState.Protected; decide)] using hr.lengthReg
  · simpa only [he arityPort (by unfold LocalBranchState.Protected; decide)] using hr.arityReg
  · simpa only [he adjustedPort (by unfold LocalBranchState.Protected; decide)] using hr.adjustedReg

structure High (arity L adjusted : ℕ) (counts : Counts) (values : Fin 9 → ℕ) (R : Work → Prop) (work : Work) : Prop where
  basic : LocalBranchState.Basic counts L R work
  addresses : AddressCounterPlacement.Registers values work
  lengthReg : IsReg L (work lengthPort)
  arityReg : IsReg arity (work arityPort)
  adjustedReg : IsReg adjusted (work adjustedPort)
  anchorReg : IsReg 0 (work LocalBranchState.anchor)

theorem high_outside : ∀ j : Fin 32, 8 ≤ j.val → FormulaSpanRegisters.Outside 24 j := by
  unfold FormulaSpanRegisters.Outside TermSpanRegisters.Outside
  decide

theorem extra_outside : ∀ j, ExtraPort j → FormulaSpanRegisters.Outside 24 j := by
  unfold ExtraPort FormulaSpanRegisters.Outside TermSpanRegisters.Outside
  decide

theorem high_stable (arity L adjusted : ℕ) (counts : Counts) (values : Fin 9 → ℕ) (R : Work → Prop) (hR : Stable R) :
    FormulaSpanRegisters.Stable (High arity L adjusted counts values R) := by
  rintro work work' he hr
  have htag (i : Fin 3) : FormulaSpanRegisters.Outside 24 (QueryWorkFrame.tags i) :=
    high_outside _ (by change 8 ≤ i.val + 8; omega)
  have hslot (i : Fin 9) : FormulaSpanRegisters.Outside 24 (AddressCounterPlacement.slot i) :=
    high_outside _ (by change 8 ≤ 19 + i.val; omega)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [he _ (htag i)] using hr.basic.tagHeads i
  · simpa only [he QueryWorkFrame.flag (high_outside _ (by decide))] using hr.basic.flagHead
  · simpa only [he QueryWorkFrame.pending (high_outside _ (by decide))] using hr.basic.termReg
  · simpa only [he QueryWorkFrame.formulas (high_outside _ (by decide))] using hr.basic.formulaReg
  · simpa only [he QueryWorkFrame.result (high_outside _ (by decide))] using hr.basic.nodeReg
  · simpa only [he QueryWorkFrame.fuel (high_outside _ (by decide))] using hr.basic.fuelReg
  · simpa only [he QueryWorkFrame.position (high_outside _ (by decide))] using hr.basic.positionReg
  · simpa only [he LocalBranchState.scratch (high_outside _ (by decide))] using hr.basic.scratchReg
  · exact hR work work' (fun j hj => he j (extra_outside j hj)) hr.basic.frame
  · intro i
    simpa only [he _ (hslot i)] using hr.addresses i
  · simpa only [he lengthPort (high_outside _ (by decide))] using hr.lengthReg
  · simpa only [he arityPort (high_outside _ (by decide))] using hr.arityReg
  · simpa only [he adjustedPort (high_outside _ (by decide))] using hr.adjustedReg
  · simpa only [he LocalBranchState.anchor (high_outside _ (by decide))] using hr.anchorReg

theorem to_scan (s : FormulaSpanControl.State) (arity L adjusted : ℕ) (counts : Counts) (values : Fin 9 → ℕ)
    (R : Work → Prop) (work : Work) (hr : Before s arity L adjusted counts values R work) :
    TermSpanRegisters.Ready s.terms s.coordinates (FormulaSpanRegisters.Frame s.formulas (High arity L adjusted counts values R)) work := by
  have hf := hr.2.2.basic.frame
  refine ⟨hr.1, BranchWorkTransfer.full_markers counts values L 0 (Frame s arity L adjusted R) work hr.2.2 hr.2.1,
    hf.termReg, hf.coordinatesReg, hf.tagHeads, hf.flagHead, hf.formulaReg,
    ⟨hr.2.2.basic.tagHeads, hr.2.2.basic.flagHead, hr.2.2.basic.termReg, hr.2.2.basic.formulaReg, hr.2.2.basic.nodeReg,
      hr.2.2.basic.fuelReg, hr.2.2.basic.positionReg, hr.2.2.basic.scratchReg, hf.extra⟩,
    hr.2.2.addresses, hf.lengthReg, hf.arityReg, hf.adjustedReg, hr.2.1⟩

theorem from_scan (s : FormulaSpanControl.State) (arity L adjusted : ℕ) (counts : Counts) (values : Fin 9 → ℕ)
    (R : Work → Prop) (work : Work)
    (hr : TermSpanRegisters.Ready s.terms s.coordinates
      (FormulaSpanRegisters.Frame s.formulas (High arity L adjusted counts values R)) work) :
    Before s arity L adjusted counts values R work := by
  have hh := hr.frame.2
  refine ⟨hr.safe, hh.anchorReg, ⟨?_, fun j _ => hr.markers j, hh.addresses⟩⟩
  exact ⟨hh.basic.tagHeads, hh.basic.flagHead, hh.basic.termReg, hh.basic.formulaReg, hh.basic.nodeReg,
    hh.basic.fuelReg, hh.basic.positionReg, hh.basic.scratchReg,
    hr.counter, hr.frame.1, hr.nodeReg, hr.tagHeads, hr.flagHead, hh.lengthReg, hh.arityReg, hh.adjustedReg, hh.basic.frame⟩

end JointThermoComplexity.Complexity.MainEquationWork

#print axioms JointThermoComplexity.Complexity.MainEquationWork.frame_stable
#print axioms JointThermoComplexity.Complexity.MainEquationWork.high_stable
#print axioms JointThermoComplexity.Complexity.MainEquationWork.to_scan
#print axioms JointThermoComplexity.Complexity.MainEquationWork.from_scan
