module
public import proofs.JointThermoComplexity.Complexity.CountedMarkedStep
public import proofs.JointThermoComplexity.Complexity.SparseOffsetLoop

set_option autoImplicit false
@[expose] public section

/-! An actual fixed-fuel pass accumulates offset and normalized-row count. -/

namespace JointThermoComplexity.Complexity.CountedSparseLoop
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open SparseOffsetPorts CountedSparseControl
open CountedMarkedStep (Inv)

def Stable (R : (Fin 32 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, 16 ≤ j.val → j ≠ rows → j ≠ fuel → next j = work j) → R work → R next

theorem inv_iff (L : ℕ) (emitted : List Bool) (R : (Fin 32 → Tape) → Prop) (s : State)
    (inp out : Tape) (work : Fin 33 → Tape) :
    Inv L emitted R s inp work out ↔ SparseOffsetMarkedStep.Inv L emitted
      (fun old => R old ∧ Register s.rows (old rows)) s.base inp work out := by
  constructor
  · rintro ⟨hc, hs, ⟨hf, hn⟩, hh, hr⟩
    rcases hf with ⟨hready, hadj, hacc, haux, hlast, hx⟩
    exact ⟨hc, hs, ⟨hready, hadj, hacc, haux, hlast, hx, hn⟩, hh, hr⟩
  · rintro ⟨hc, hs, hf, hh, hr⟩
    rcases hf with ⟨hready, hadj, hacc, haux, hlast, hx, hn⟩
    exact ⟨hc, hs, ⟨⟨hready, hadj, hacc, haux, hlast, hx⟩, hn⟩, hh, hr⟩

theorem reframe (L : ℕ) (emitted : List Bool) (R : (Fin 32 → Tape) → Prop) (s : State)
    (work next : Fin 33 → Tape) (he : ∀ j, j ≠ fuel.castSucc → next j = work j)
    (hs : Parked (next fuel.castSucc))
    (hR : ∀ old new, (∀ j, j ≠ fuel → new j = old j) → R old → R new) :
    ∀ inp out, Inv L emitted R s inp work out → Inv L emitted R s inp next out := by
  intro inp out hp
  apply (inv_iff L emitted R s inp out next).mpr
  apply SparseOffsetLoop.reframe L emitted (fun old => R old ∧ Register s.rows (old rows)) s.base work next he hs
  · rintro old new hh ⟨hr, hn⟩
    exact ⟨hR old new hh hr, by rw [hh rows (by decide)]; exact hn⟩
  · exact (inv_iff L emitted R s inp out work).mp hp

def machine (boxed : Bool) : TM 33 := forRegTM (CountedMarkedStep.machine boxed) fuel.castSucc

def bodyBound (L C B count : ℕ) : ℕ :=
  CountedMarkedStep.bound L (C + count * (16 * (L + 2609))) (B + 16 * count)

def timeBound (L C B count : ℕ) : ℕ := count * (bodyBound L C B count + 2) + (count + 2)

theorem frame_body_hoareTime (boxed : Bool) (L C B count i : ℕ) (hi : i < count)
    (emitted : List Bool) (R : (Fin 32 → Tape) → Prop) (hR : Stable R) (s : State)
    (hlen : s.base.input.length ≤ L) (hA : s.base.offset.bits.length ≤ C) (hN : s.rows.bits.length ≤ B) :
    (CountedMarkedStep.machine boxed).HoareTime
      (InvariantLoop.Frame fuel.castSucc count (i + 2) (Inv L emitted R (run boxed i s)))
      (InvariantLoop.Frame fuel.castSucc count (i + 2) (Inv L emitted R (run boxed (i + 1) s)))
      (bodyBound L C B count) := by
  let ft : Tape := ⟨i + 2, regCells count⟩
  let RB : (Fin 32 → Tape) → Prop := fun work => R work ∧ work fuel = ft
  have hRB : CountedMarkedStep.Stable RB := by
    rintro work next he ⟨hr, hf⟩
    exact ⟨hR _ _ (fun j hj hrow _ => he j hj hrow) hr, (he fuel (by decide) (by decide)).trans hf⟩
  have hRf : ∀ work next, (∀ j, j ≠ fuel → next j = work j) → R work → R next :=
    fun work next he => hR work next (fun j _ _ hj => he j hj)
  have hbds := run_bounds boxed i s L hlen
  have hbits : (run boxed i s).base.offset.bits.length ≤ C + count * (16 * (L + 2609)) :=
    hbds.2.1.trans (Nat.add_le_add hA (Nat.mul_le_mul_right _ (Nat.le_of_lt hi)))
  have hrow : (run boxed i s).rows.bits.length ≤ B + 16 * count :=
    hbds.2.2.trans (Nat.add_le_add hN (Nat.mul_le_mul_left _ (Nat.le_of_lt hi)))
  have hb := CountedMarkedStep.hoareTime boxed L (C + count * (16 * (L + 2609))) (B + 16 * count)
    emitted RB hRB (run boxed i s) (hbds.1.trans hlen) hbits hrow
  intro inp work out hf
  have hactual : Inv L emitted R (run boxed i s) inp work out := by
    apply reframe L emitted R (run boxed i s) (InvariantLoop.restore work fuel.castSucc count) work
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by rw [hf.fuel]; exact ⟨by change 1 ≤ i + 2; omega, fun j hj => regCells_ne_start hj⟩)
      hRf inp out hf.invariant
  have hpre : Inv L emitted RB (run boxed i s) inp work out := by
    rcases hactual with ⟨hc, hs, ⟨hfields, hn⟩, hmh, hmr⟩
    rcases hfields with ⟨hr, hh, ha, hu, hl, hx⟩
    exact ⟨hc, hs, ⟨⟨hr, hh, ha, hu, hl, hx, hf.fuel⟩, hn⟩, hmh, hmr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', ⟨hfields', hn⟩, hmh, hmr⟩ := hb inp work out hpre
  rcases hfields' with ⟨hr', hadj, hacc, haux, hlast, hx⟩
  have hbase : Inv L emitted R (step boxed (run boxed i s)) d.input d.work d.output :=
    ⟨hc', hs', ⟨⟨hr', hadj, hacc, haux, hlast, hx.1⟩, hn⟩, hmh, hmr⟩
  have hrestored : Inv L emitted R (step boxed (run boxed i s)) d.input
      (InvariantLoop.restore d.work fuel.castSucc count) d.output := by
    apply reframe L emitted R (step boxed (run boxed i s)) d.work (InvariantLoop.restore d.work fuel.castSucc count)
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape count)
      hRf d.input d.output hbase
  refine ⟨d, t, ht, hd, hh, hx.2, hc'.input_read, fun j _ => (hs' j).read_ne_start, hc'.output_read, ?_⟩
  simpa only [run_succ_last] using hrestored

theorem framed_hoareTime (boxed : Bool) (L C B count : ℕ) (emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) (hR : Stable R) (s : State)
    (hlen : s.base.input.length ≤ L) (hA : s.base.offset.bits.length ≤ C) (hN : s.rows.bits.length ≤ B) :
    (machine boxed).HoareTime
      (InvariantLoop.Frame fuel.castSucc count 1 (Inv L emitted R s))
      (InvariantLoop.Frame fuel.castSucc count 1 (Inv L emitted R (run boxed count s))) (timeBound L C B count) := by
  exact InvariantLoop.hoareTime _ fuel.castSucc (fun i => Inv L emitted R (run boxed i s))
    (bodyBound L C B count) count
    (fun i hi => frame_body_hoareTime boxed L C B count i hi emitted R hR s hlen hA hN)

theorem hoareTime (boxed : Bool) (L C B count : ℕ) (emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) (hR : Stable R) (s : State)
    (hlen : s.base.input.length ≤ L) (hA : s.base.offset.bits.length ≤ C) (hN : s.rows.bits.length ≤ B) :
    (machine boxed).HoareTime
      (fun inp work out => Inv L emitted R s inp work out ∧ IsReg count (work fuel.castSucc))
      (fun inp work out => Inv L emitted R (run boxed count s) inp work out ∧ IsReg count (work fuel.castSucc))
      (timeBound L C B count) := by
  have hb := framed_hoareTime boxed L C B count emitted R hR s hlen hA hN
  apply hb.consequence
  · rintro inp work out ⟨hs, hf⟩
    refine ⟨hf.eq_regT, hs.1.input_read, fun j _ => (hs.1.works j).1, hs.1.output_read, ?_⟩
    simpa only [InvariantLoop.restore_self work fuel.castSucc count hf.eq_regT] using hs
  · exact fun _ _ _ hf => ⟨hf.on_work, hf.register⟩
  · exact le_rfl

theorem cubic_timeBound (L C B : ℕ) :
    timeBound L C B L = 3328 * L ^ 3 + 8687531 * L ^ 2 + (10897584 + 208 * C + 32 * B) * L + 2 := by
  unfold timeBound bodyBound CountedMarkedStep.bound OffsetTemplateProgram.bound
  ring1

end JointThermoComplexity.Complexity.CountedSparseLoop

#print axioms JointThermoComplexity.Complexity.CountedSparseLoop.hoareTime
#print axioms JointThermoComplexity.Complexity.CountedSparseLoop.cubic_timeBound
