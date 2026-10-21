module
public import proofs.JointThermoComplexity.Complexity.DenseMarkedStep
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! A fixed-fuel actual source pass emits exactly the counted raw record words.
Each body preserves the advanced physical fuel tape, then the loop restores it. -/

namespace JointThermoComplexity.Complexity.DenseSourceLoop
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open CountedSparseControl

def Stable (R : (Fin 64 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, DenseMarkedFrame.Outside j → j ≠ 18 → next j = work j) → R work → R next
def machine (boxed right : Bool) : TM 64 := forRegTM (DenseMarkedStep.machine boxed right) 18
def timeBound (boxed right : Bool) (L n N B count : ℕ) : ℕ :=
  count * (DenseMarkedStep.bound boxed right L n N B + 2) + (count + 2)

theorem inv_frame (L n N : ℕ) (emitted : List Bool) (R S : (Fin 64 → Tape) → Prop) (s : State)
    (inp out : Tape) (work : Fin 64 → Tape) (hp : DenseMarkedFrame.Inv L n N emitted R s inp work out) (hs : S work) :
    DenseMarkedFrame.Inv L n N emitted S s inp work out := by
  rcases hp with ⟨hc, hpark, ⟨hparser, hcore⟩, hstatus⟩
  exact ⟨hc, hpark, ⟨hparser, DenseMarkedStep.core_frame n N (2 + s.rows) R S work hcore hs⟩, hstatus⟩

theorem frame_body_hoareTime (boxed right : Bool) (L n N B count i : ℕ) (hi : i < count)
    (emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (s : State)
    (hlen : s.base.input.length ≤ L) (hLB : L ≤ B) (hbase : N + 2 ≤ B) (hN : (CountedSparseControl.run boxed count s).rows ≤ N) :
    (DenseMarkedStep.machine boxed right).HoareTime
      (InvariantLoop.Frame 18 count (i + 2)
        (DenseMarkedFrame.Inv L n N (emitted ++ DenseMarkedControl.runWords boxed right n N i s) R (CountedSparseControl.run boxed i s)))
      (InvariantLoop.Frame 18 count (i + 2)
        (DenseMarkedFrame.Inv L n N (emitted ++ DenseMarkedControl.runWords boxed right n N (i + 1) s) R (CountedSparseControl.run boxed (i + 1) s)))
      (DenseMarkedStep.bound boxed right L n N B) := by
  let ft : Tape := ⟨i + 2, regCells count⟩
  let RB : (Fin 64 → Tape) → Prop := fun work => R work ∧ work 18 = ft
  have h18 : DenseMarkedFrame.Outside (18 : Fin 64) := by
    unfold DenseMarkedFrame.Outside DenseSourceFrame.Outside DenseRowFrame.Outside
    decide
  have hRB : DenseMarkedFrame.Stable RB := by
    rintro work next he ⟨hr, hf⟩
    exact ⟨hR work next (fun j hj _ => he j hj) hr, (he 18 h18).trans hf⟩
  have hRf : ∀ work next, (∀ j, j ≠ (18 : Fin 64) → next j = work j) → R work → R next :=
    fun work next he => hR work next (fun j _ hj => he j hj)
  have hbds := run_bounds boxed i s L hlen
  have hfit := (DenseMarkedControl.next_rows_le_final boxed count i s hi).trans hN
  have hb := DenseMarkedStep.hoareTime boxed right L n N B
    (emitted ++ DenseMarkedControl.runWords boxed right n N i s) RB hRB (CountedSparseControl.run boxed i s)
    (hbds.1.trans hlen) hLB hbase hfit
  intro inp work out hf
  have hactual : DenseMarkedFrame.Inv L n N (emitted ++ DenseMarkedControl.runWords boxed right n N i s) R (CountedSparseControl.run boxed i s) inp work out := by
    apply DenseMarkedFrame.reframe L n N _ R (CountedSparseControl.run boxed i s) (InvariantLoop.restore work 18 count) work
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by rw [hf.fuel]; exact ⟨by change 1 ≤ i + 2; omega, fun j hj => regCells_ne_start hj⟩)
      hRf inp out hf.invariant
  have hpre : DenseMarkedFrame.Inv L n N (emitted ++ DenseMarkedControl.runWords boxed right n N i s) RB (CountedSparseControl.run boxed i s) inp work out :=
    inv_frame L n N _ R RB _ inp out work hactual ⟨hactual.2.2.1.2.frame, hf.fuel⟩
  obtain ⟨d, t, ht, hd, hh, hpost⟩ := hb inp work out hpre
  rcases hpost with ⟨hc', hs', ⟨hparser, hcore⟩, hstatus⟩
  have hbase' : DenseMarkedFrame.Inv L n N
      ((emitted ++ DenseMarkedControl.runWords boxed right n N i s) ++ DenseMarkedControl.word boxed right n N (CountedSparseControl.run boxed i s))
      R (step boxed (CountedSparseControl.run boxed i s)) d.input d.work d.output :=
    ⟨hc', hs', ⟨hparser, DenseMarkedStep.core_frame n N _ RB R d.work hcore hcore.frame.1⟩, hstatus⟩
  have hrestored : DenseMarkedFrame.Inv L n N
      ((emitted ++ DenseMarkedControl.runWords boxed right n N i s) ++ DenseMarkedControl.word boxed right n N (CountedSparseControl.run boxed i s))
      R (step boxed (CountedSparseControl.run boxed i s)) d.input (InvariantLoop.restore d.work 18 count) d.output := by
    apply DenseMarkedFrame.reframe L n N _ R (step boxed (CountedSparseControl.run boxed i s)) d.work (InvariantLoop.restore d.work 18 count)
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape count)
      hRf d.input d.output hbase'
  refine ⟨d, t, ht, hd, hh, hcore.frame.2, hc'.input_read, fun j _ => (hs' j).read_ne_start, hc'.output_read, ?_⟩
  simpa only [run_succ_last, DenseMarkedControl.runWords_succ_last, List.append_assoc] using hrestored

theorem framed_hoareTime (boxed right : Bool) (L n N B count : ℕ) (emitted : List Bool)
    (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (s : State)
    (hlen : s.base.input.length ≤ L) (hLB : L ≤ B) (hbase : N + 2 ≤ B) (hN : (CountedSparseControl.run boxed count s).rows ≤ N) :
    (machine boxed right).HoareTime
      (InvariantLoop.Frame 18 count 1 (DenseMarkedFrame.Inv L n N emitted R s))
      (InvariantLoop.Frame 18 count 1
        (DenseMarkedFrame.Inv L n N (emitted ++ DenseMarkedControl.runWords boxed right n N count s) R (CountedSparseControl.run boxed count s)))
      (timeBound boxed right L n N B count) := by
  have hb := InvariantLoop.hoareTime (DenseMarkedStep.machine boxed right) (18 : Fin 64)
    (fun i => DenseMarkedFrame.Inv L n N (emitted ++ DenseMarkedControl.runWords boxed right n N i s) R (CountedSparseControl.run boxed i s))
    (DenseMarkedStep.bound boxed right L n N B) count
    (fun i hi => frame_body_hoareTime boxed right L n N B count i hi emitted R hR s hlen hLB hbase hN)
  simpa only [DenseMarkedControl.runWords, CountedSparseControl.run, List.append_nil, machine, timeBound] using hb

theorem hoareTime (boxed right : Bool) (L n N B count : ℕ) (emitted : List Bool)
    (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (s : State)
    (hlen : s.base.input.length ≤ L) (hLB : L ≤ B) (hbase : N + 2 ≤ B) (hN : (CountedSparseControl.run boxed count s).rows ≤ N) :
    (machine boxed right).HoareTime
      (fun inp work out => DenseMarkedFrame.Inv L n N emitted R s inp work out ∧ IsReg count (work 18))
      (fun inp work out => DenseMarkedFrame.Inv L n N (emitted ++ DenseMarkedControl.runWords boxed right n N count s)
        R (CountedSparseControl.run boxed count s) inp work out ∧ IsReg count (work 18))
      (timeBound boxed right L n N B count) := by
  have hb := framed_hoareTime boxed right L n N B count emitted R hR s hlen hLB hbase hN
  apply hb.consequence
  · rintro inp work out ⟨hs, hf⟩
    refine ⟨hf.eq_regT, hs.1.input_read, fun j _ => (hs.1.works j).1, hs.1.output_read, ?_⟩
    simpa only [InvariantLoop.restore_self work (18 : Fin 64) count hf.eq_regT] using hs
  · exact fun _ _ _ hf => ⟨hf.on_work, hf.register⟩
  · exact le_rfl

end JointThermoComplexity.Complexity.DenseSourceLoop

#print axioms JointThermoComplexity.Complexity.DenseSourceLoop.hoareTime
