module
public import proofs.JointThermoComplexity.Complexity.EquationEmissionStep
public import proofs.JointThermoComplexity.Complexity.FormulaSpanLoop

set_option autoImplicit false
@[expose] public section

/-! Reuse the checked traversal fuel conversion for the equation output/work invariant. -/

namespace JointThermoComplexity.Complexity.EquationFuelFrame
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryCounterInit MainEquationWork MainNodeEquation
open HeaderAt (Cursor)

def fuel : Fin 32 := FormulaSpanLoop.fuel 24

def Logical (s : PreorderEmissionControl.State) (arity L N : ℕ) : _root_.Complexity.TM.TapePred 32 := fun inp work out =>
  Cursor s.scan.before s.scan.input (RowEntriesCodec.entries s.emitted) inp work out ∧
    Bounded s.scan arity L N (fun _ => True) work

def ExactFuel (v head : ℕ) (work : Work) : Prop := work fuel = ⟨head, regCells v⟩

theorem exact_stable (v head : ℕ) : MainEquationWork.Stable (ExactFuel v head) := by
  rintro work work' he hf
  exact (he fuel (by unfold ExtraPort; decide)).trans hf

theorem map_bounded (s : FormulaSpanControl.State) (arity L N : ℕ) (R S : Work → Prop) (work : Work)
    (h : R work → S work) (hr : Bounded s arity L N R work) : Bounded s arity L N S work := by
  obtain ⟨adjusted, counts, values, hs, hadj, hq, hv, hz⟩ := hr
  have hb := hs.2.2.basic
  have hf := hb.frame
  exact ⟨adjusted, counts, values, ⟨hs.1, hs.2.1,
    ⟨⟨hb.tagHeads, hb.flagHead, hb.termReg, hb.formulaReg, hb.nodeReg, hb.fuelReg, hb.positionReg, hb.scratchReg,
      hf.termReg, hf.formulaReg, hf.coordinatesReg, hf.tagHeads, hf.flagHead, hf.lengthReg, hf.arityReg, hf.adjustedReg, h hf.extra⟩,
      hs.2.2.markers, hs.2.2.addresses⟩⟩, hadj, hq, hv, hz⟩

theorem high_fuel_stable (arity L adjusted : ℕ) (counts : Counts) (values : Fin 9 → ℕ) :
    ∀ work work', (∀ j, j ≠ fuel → work' j = work j) →
      High arity L adjusted counts values (fun _ => True) work → High arity L adjusted counts values (fun _ => True) work' := by
  rintro work work' he hr
  have htag (i : Fin 3) : QueryWorkFrame.tags i ≠ fuel := by
    intro hh
    have hv := congrArg Fin.val hh
    change i.val + 8 = 4 at hv
    omega
  have hslot (i : Fin 9) : AddressCounterPlacement.slot i ≠ fuel := by
    intro hh
    have hv := congrArg Fin.val hh
    change 19 + i.val = 4 at hv
    omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [he _ (htag i)] using hr.basic.tagHeads i
  · simpa only [he QueryWorkFrame.flag (by decide)] using hr.basic.flagHead
  · simpa only [he QueryWorkFrame.pending (by decide)] using hr.basic.termReg
  · simpa only [he QueryWorkFrame.formulas (by decide)] using hr.basic.formulaReg
  · simpa only [he QueryWorkFrame.result (by decide)] using hr.basic.nodeReg
  · simpa only [he QueryWorkFrame.fuel (by decide)] using hr.basic.fuelReg
  · simpa only [he QueryWorkFrame.position (by decide)] using hr.basic.positionReg
  · simpa only [he LocalBranchState.scratch (by decide)] using hr.basic.scratchReg
  · intro i
    simpa only [he _ (hslot i)] using hr.addresses i
  · simpa only [he lengthPort (by decide)] using hr.lengthReg
  · simpa only [he arityPort (by decide)] using hr.arityReg
  · simpa only [he adjustedPort (by decide)] using hr.adjustedReg
  · simpa only [he LocalBranchState.anchor (by decide)] using hr.anchorReg

theorem reframe (s : PreorderEmissionControl.State) (arity L N : ℕ) (work work' : Work)
    (he : ∀ j, j ≠ fuel → work' j = work j) (hs : Parked (work' fuel)) (hz : (work' fuel).cells 0 = Γ.start) :
    ∀ inp out, Logical s arity L N inp work out → Logical s arity L N inp work' out := by
  rintro inp out ⟨hcur, adjusted, counts, values, hr, hadj, hq, hv, hzero⟩
  have hi : FormulaSpanRegisters.Inv (RowEntriesCodec.entries s.emitted)
      (High arity L adjusted counts values (fun _ => True)) s.scan inp work out :=
    ⟨hcur, to_scan s.scan arity L adjusted counts values (fun _ => True) work hr⟩
  have ho := FormulaSpanLoop.reframe (RowEntriesCodec.entries s.emitted)
    (High arity L adjusted counts values (fun _ => True)) (high_fuel_stable arity L adjusted counts values)
    s.scan work work' he hs hz inp out hi
  exact ⟨ho.1, adjusted, counts, values,
    from_scan s.scan arity L adjusted counts values (fun _ => True) work' ho.2, hadj, hq, hv, hzero⟩

theorem to_actual (s : PreorderEmissionControl.State) (arity L N v head : ℕ) (hhead : 1 ≤ head)
    (inp : Tape) (work : Work) (out : Tape)
    (hf : InvariantLoop.Frame fuel v head (Logical s arity L N) inp work out) :
    Cursor s.scan.before s.scan.input (RowEntriesCodec.entries s.emitted) inp work out ∧
      Bounded s.scan arity L N (ExactFuel v head) work := by
  have ha := reframe s arity L N (InvariantLoop.restore work fuel v) work
    (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
    (by rw [hf.fuel]; exact ⟨hhead, fun j hj => regCells_ne_start hj⟩)
    (by rw [hf.fuel]; rfl) inp out hf.invariant
  exact ⟨ha.1, map_bounded s.scan arity L N (fun _ => True) (ExactFuel v head) work (fun _ => hf.fuel) ha.2⟩

theorem from_actual (s : PreorderEmissionControl.State) (arity L N v head : ℕ)
    (inp : Tape) (work : Work) (out : Tape)
    (hc : Cursor s.scan.before s.scan.input (RowEntriesCodec.entries s.emitted) inp work out)
    (hr : Bounded s.scan arity L N (ExactFuel v head) work) :
    InvariantLoop.Frame fuel v head (Logical s arity L N) inp work out := by
  have hbase : Logical s arity L N inp work out :=
    ⟨hc, map_bounded s.scan arity L N (ExactFuel v head) (fun _ => True) work (fun _ => trivial) hr⟩
  obtain ⟨_, _, _, hb, _, _, _, _⟩ := hr
  have hrest := reframe s arity L N work (InvariantLoop.restore work fuel v)
    (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
    (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape v)
    (by simp only [InvariantLoop.restore, Function.update_self, regT_cells, regCells_zero]) inp out hbase
  exact ⟨hb.2.2.basic.frame.extra, hc.input_read, fun j _ => (hb.1 j).read_ne_start, hc.output_read, hrest⟩

end JointThermoComplexity.Complexity.EquationFuelFrame

#print axioms JointThermoComplexity.Complexity.EquationFuelFrame.reframe
#print axioms JointThermoComplexity.Complexity.EquationFuelFrame.to_actual
#print axioms JointThermoComplexity.Complexity.EquationFuelFrame.from_actual
