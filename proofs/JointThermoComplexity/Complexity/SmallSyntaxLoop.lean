module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxStep
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! Fixed-fuel execution of the total syntax token machine, including the displaced fuel head. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxLoop
open _root_.Complexity _root_.Complexity.TM SmallSyntaxRegisters
open HeaderAt (Cursor)

theorem reframe (s : SmallSyntaxControl.State) (work work' : Fin 6 → Tape)
    (hw : ∀ j, j ≠ fuel → work' j = work j)
    (hs : Parked (work' fuel)) (hz : (work' fuel).cells 0 = Γ.start) :
    ∀ inp out, Inv (fun _ => True) s inp work out → Inv (fun _ => True) s inp work' out := by
  rintro inp out ⟨hc, hr⟩
  have hs' : ∀ j, Parked (work' j) := by
    intro j
    by_cases hj : j = fuel
    · subst j; exact hs
    · rw [hw j hj]; exact hr.safe j
  have hz' : ∀ j, (work' j).cells 0 = Γ.start := by
    intro j
    by_cases hj : j = fuel
    · subst j; exact hz
    · rw [hw j hj]; exact hr.markers j
  refine ⟨⟨hc.cells, hc.head, fun j => ⟨(hs' j).read_ne_start, (hs' j).1⟩,
    hc.tapePrefix, hc.zero⟩, hs', hz', ?_, ?_, ?_, trivial⟩
  · simpa only [hw pending (by decide)] using hr.counter
  · intro i
    simpa only [hw (tags i) (fuel_tags i).symm] using hr.tagHeads i
  · simpa only [hw flag (by decide)] using hr.flagHead

def machine : TM 6 := forRegTM SmallSyntaxStep.machine fuel
def bodyBound (L pending count : ℕ) : ℕ := 12 * L + 2 * (pending + 2 * count) + 50
def timeBound (L pending count : ℕ) : ℕ := count * (bodyBound L pending count + 2) + (count + 2)

theorem frame_body_hoareTime (L count i : ℕ) (hi : i < count)
    (s : SmallSyntaxControl.State) (hlen : s.input.length ≤ L) :
    SmallSyntaxStep.machine.HoareTime
      (InvariantLoop.Frame fuel count (i + 2) (Inv (fun _ => True) (SmallSyntaxControl.run i s)))
      (InvariantLoop.Frame fuel count (i + 2) (Inv (fun _ => True) (SmallSyntaxControl.run (i + 1) s)))
      (bodyBound L s.pending count) := by
  let ft : Tape := ⟨i + 2, regCells count⟩
  let RB : (Fin 6 → Tape) → Prop := fun work => work fuel = ft
  have hRB : Stable RB := by
    intro work work' he hr
    exact he.trans hr
  have hbounds := SmallSyntaxControl.run_bounds i s
  have hb := SmallSyntaxStep.bounded_hoareTime L (s.pending + 2 * count) RB hRB
    (SmallSyntaxControl.run i s) (hbounds.2.1.trans hlen) (by have := hbounds.1; omega)
  intro inp work out hf
  have hactual : Inv (fun _ => True) (SmallSyntaxControl.run i s) inp work out := by
    apply reframe (SmallSyntaxControl.run i s) (InvariantLoop.restore work fuel count) work
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by rw [hf.fuel]; exact ⟨by change 1 ≤ i + 2; omega, fun j hj => regCells_ne_start hj⟩)
      (by rw [hf.fuel]; rfl) inp out hf.invariant
  have hpre : Inv RB (SmallSyntaxControl.run i s) inp work out := by
    rcases hactual with ⟨hc, hr⟩
    exact ⟨hc, hr.safe, hr.markers, hr.counter, hr.tagHeads, hr.flagHead, hf.fuel⟩
  obtain ⟨d, t, ht, hd, hh, hc', hr'⟩ := hb inp work out hpre
  have hbase : Inv (fun _ => True) (SmallSyntaxControl.step (SmallSyntaxControl.run i s))
      d.input d.work d.output :=
    ⟨hc', hr'.safe, hr'.markers, hr'.counter, hr'.tagHeads, hr'.flagHead, trivial⟩
  have hrestored : Inv (fun _ => True) (SmallSyntaxControl.step (SmallSyntaxControl.run i s))
      d.input (InvariantLoop.restore d.work fuel count) d.output := by
    apply reframe _ d.work (InvariantLoop.restore d.work fuel count)
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape count)
      (by simp only [InvariantLoop.restore, Function.update_self, regT_cells, regCells_zero])
      d.input d.output hbase
  refine ⟨d, t, ht, hd, hh, hr'.frame, hc'.input_read, ?_, hc'.output_read, ?_⟩
  · intro j _
    exact (hr'.safe j).read_ne_start
  · simpa only [SmallSyntaxControl.run_succ_last] using hrestored

theorem framed_hoareTime (L count : ℕ) (s : SmallSyntaxControl.State) (hlen : s.input.length ≤ L) :
    machine.HoareTime
      (InvariantLoop.Frame fuel count 1 (Inv (fun _ => True) s))
      (InvariantLoop.Frame fuel count 1 (Inv (fun _ => True) (SmallSyntaxControl.run count s)))
      (timeBound L s.pending count) := by
  exact InvariantLoop.hoareTime SmallSyntaxStep.machine fuel
    (fun i => Inv (fun _ => True) (SmallSyntaxControl.run i s)) (bodyBound L s.pending count) count
    (fun i hi => frame_body_hoareTime L count i hi s hlen)

theorem hoareTime (L count : ℕ) (s : SmallSyntaxControl.State) (hlen : s.input.length ≤ L) :
    machine.HoareTime
      (fun inp work out => Inv (fun _ => True) s inp work out ∧ IsReg count (work fuel))
      (fun inp work out => Inv (fun _ => True) (SmallSyntaxControl.run count s) inp work out ∧
        IsReg count (work fuel)) (timeBound L s.pending count) := by
  have h := framed_hoareTime L count s hlen
  exact h.consequence (by
    rintro inp work out ⟨hi, hf⟩
    refine ⟨hf.eq_regT, hi.1.input_read, fun j _ => (hi.1.works j).1, hi.1.output_read, ?_⟩
    simpa only [InvariantLoop.restore_self work fuel count hf.eq_regT] using hi)
    (fun _ _ _ hf => ⟨hf.on_work, hf.register⟩) le_rfl

theorem quadratic_timeBound (L : ℕ) : timeBound L 0 L = 16 * L ^ 2 + 53 * L + 2 := by
  unfold timeBound bodyBound
  ring1

end JointThermoComplexity.Complexity.SmallSyntaxLoop

#print axioms JointThermoComplexity.Complexity.SmallSyntaxLoop.frame_body_hoareTime
#print axioms JointThermoComplexity.Complexity.SmallSyntaxLoop.hoareTime
#print axioms JointThermoComplexity.Complexity.SmallSyntaxLoop.quadratic_timeBound
