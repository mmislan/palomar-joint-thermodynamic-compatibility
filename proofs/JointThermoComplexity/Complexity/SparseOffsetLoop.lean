module
public import proofs.JointThermoComplexity.Complexity.SparseOffsetMarkedStep
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! A fixed-fuel sparse offset pass with a uniform polynomial runtime. -/

namespace JointThermoComplexity.Complexity.SparseOffsetLoop
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
open BinaryScaleBuffer (oldWork)
open SparseOffsetPorts SparseOffsetLoopControl
open SparseOffsetMarkedStep (Inv)

def Stable (R : (Fin 32 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, 16 ≤ j.val → j ≠ fuel → next j = work j) → R work → R next

theorem low_ne_fuel (j : Fin 32) (hj : j.val < 16) : j.castSucc ≠ fuel.castSucc := by
  intro he
  have hv := congrArg (fun x : Fin 33 => x.val) he
  change j.val = 18 at hv
  omega

theorem reframe (L : ℕ) (emitted : List Bool) (R : (Fin 32 → Tape) → Prop) (s : State)
    (work next : Fin 33 → Tape)
    (he : ∀ j, j ≠ fuel.castSucc → next j = work j) (hs : Parked (next fuel.castSucc))
    (hR : ∀ old new, (∀ j, j ≠ fuel → new j = old j) → R old → R new) :
    ∀ inp out, Inv L emitted R s inp work out → Inv L emitted R s inp next out := by
  rintro inp out ⟨hc, hsafe, hfields, hmh, hmr⟩
  rcases hfields with ⟨⟨hi, hsign, hp, hend, hflag⟩, hh, ha, hu, hl, hr⟩
  have hsafe' : ∀ j, Parked (next j) := by
    intro j
    by_cases hj : j = fuel.castSucc
    · subst j; exact hs
    · rw [he j hj]; exact hsafe j
  have hc' : Cursor s.before s.input emitted inp next out :=
    ⟨hc.cells, hc.head, fun j => ⟨(hsafe' j).read_ne_start, (hsafe' j).1⟩, hc.tapePrefix, hc.zero⟩
  refine ⟨hc', hsafe', ?_, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [oldWork]
      rw [he layout.idx.castSucc (low_ne_fuel _ (by decide))]; exact hi
    · simp only [oldWork]
      rw [he layout.sign.castSucc (low_ne_fuel _ (by decide))]; exact hsign
    · intro p hmem
      have hm : p ∈ [(2, 6), (3, 7), (4, 8), (5, 9)] := hmem
      simp at hm
      have hd : p.1.castSucc ≠ fuel.castSucc := by
        rcases hm with rfl | rfl | rfl | rfl <;> exact low_ne_fuel _ (by decide)
      have hmark : p.2.castSucc ≠ fuel.castSucc := by
        rcases hm with rfl | rfl | rfl | rfl <;> exact low_ne_fuel _ (by decide)
      simp only [oldWork]
      rw [he p.1.castSucc hd, he p.2.castSucc hmark]
      exact hp p hmem
    · simp only [oldWork]
      rw [he layout.ending.castSucc (low_ne_fuel _ (by decide))]; exact hend
    · simp only [oldWork]
      rw [he layout.flag.castSucc (low_ne_fuel _ (by decide))]; exact hflag
    · rw [he layout.adjusted.castSucc (low_ne_fuel _ (by decide))]; exact hh
    · rw [he layout.acc.castSucc (low_ne_fuel _ (by decide))]; exact ha
    · rw [he layout.aux.castSucc (low_ne_fuel _ (by decide))]; exact hu
    · rw [he (Fin.last 32) (by decide)]; exact hl
    · exact hR _ _ (fun j hj => he j.castSucc (TemplateFactorPipeline.cast_ne _ _ hj)) hr
  · rw [he marker.castSucc (low_ne_fuel _ (by decide))]; exact hmh
  · rw [he marker.castSucc (low_ne_fuel _ (by decide))]; exact hmr

def machine (boxed : Bool) : TM 33 := forRegTM (SparseOffsetMarkedStep.machine boxed) fuel.castSucc

def bodyBound (L C count : ℕ) : ℕ := SparseOffsetMarkedStep.bound L (C + count * (16 * (L + 2609)))

def timeBound (L C count : ℕ) : ℕ := count * (bodyBound L C count + 2) + (count + 2)

theorem frame_body_hoareTime (boxed : Bool) (L C count i : ℕ) (hi : i < count)
    (emitted : List Bool) (R : (Fin 32 → Tape) → Prop) (hR : Stable R)
    (s : State) (hlen : s.input.length ≤ L) (hA : s.offset.bits.length ≤ C) :
    (SparseOffsetMarkedStep.machine boxed).HoareTime
      (InvariantLoop.Frame fuel.castSucc count (i + 2) (Inv L emitted R (run boxed i s)))
      (InvariantLoop.Frame fuel.castSucc count (i + 2) (Inv L emitted R (run boxed (i + 1) s)))
      (bodyBound L C count) := by
  let ft : Tape := ⟨i + 2, regCells count⟩
  let RB : (Fin 32 → Tape) → Prop := fun work => R work ∧ work fuel = ft
  have hRB : SparseOffsetMarkedStep.Stable RB := by
    rintro work next he ⟨hr, hf⟩
    exact ⟨hR _ _ (fun j hj _ => he j hj) hr, (he fuel (by decide)).trans hf⟩
  have hRf : ∀ work next, (∀ j, j ≠ fuel → next j = work j) → R work → R next :=
    fun work next he => hR work next (fun j _ hj => he j hj)
  have hbds := run_bounds boxed i s L hlen
  have hbits : (run boxed i s).offset.bits.length ≤ C + count * (16 * (L + 2609)) := by
    exact hbds.2.trans (Nat.add_le_add hA (Nat.mul_le_mul_right _ (Nat.le_of_lt hi)))
  have hb := SparseOffsetMarkedStep.hoareTime boxed L (C + count * (16 * (L + 2609))) emitted RB hRB
    (run boxed i s) (hbds.1.trans hlen) hbits
  intro inp work out hf
  have hactual : Inv L emitted R (run boxed i s) inp work out := by
    apply reframe L emitted R (run boxed i s) (InvariantLoop.restore work fuel.castSucc count) work
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by rw [hf.fuel]; exact ⟨by change 1 ≤ i + 2; omega, fun j hj => regCells_ne_start hj⟩)
      hRf inp out hf.invariant
  have hpre : Inv L emitted RB (run boxed i s) inp work out := by
    rcases hactual with ⟨hc, hs, hfields, hmh, hmr⟩
    rcases hfields with ⟨hr, hh, ha, hu, hl, hx⟩
    exact ⟨hc, hs, ⟨hr, hh, ha, hu, hl, hx, hf.fuel⟩, hmh, hmr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', hfields', hmh, hmr⟩ := hb inp work out hpre
  rcases hfields' with ⟨hr', hadj, hacc, haux, hlast, hx⟩
  have hbase : Inv L emitted R (step boxed (run boxed i s)) d.input d.work d.output :=
    ⟨hc', hs', ⟨hr', hadj, hacc, haux, hlast, hx.1⟩, hmh, hmr⟩
  have hrestored : Inv L emitted R (step boxed (run boxed i s)) d.input
      (InvariantLoop.restore d.work fuel.castSucc count) d.output := by
    apply reframe L emitted R (step boxed (run boxed i s)) d.work
      (InvariantLoop.restore d.work fuel.castSucc count)
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape count)
      hRf d.input d.output hbase
  refine ⟨d, t, ht, hd, hh, hx.2, hc'.input_read, fun j _ => (hs' j).read_ne_start,
    hc'.output_read, ?_⟩
  simpa only [run_succ_last] using hrestored

theorem framed_hoareTime (boxed : Bool) (L C count : ℕ) (emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) (hR : Stable R) (s : State)
    (hlen : s.input.length ≤ L) (hA : s.offset.bits.length ≤ C) :
    (machine boxed).HoareTime
      (InvariantLoop.Frame fuel.castSucc count 1 (Inv L emitted R s))
      (InvariantLoop.Frame fuel.castSucc count 1 (Inv L emitted R (run boxed count s)))
      (timeBound L C count) := by
  exact InvariantLoop.hoareTime _ fuel.castSucc (fun i => Inv L emitted R (run boxed i s))
    (bodyBound L C count) count
    (fun i hi => frame_body_hoareTime boxed L C count i hi emitted R hR s hlen hA)

theorem hoareTime (boxed : Bool) (L C count : ℕ) (emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) (hR : Stable R) (s : State)
    (hlen : s.input.length ≤ L) (hA : s.offset.bits.length ≤ C) :
    (machine boxed).HoareTime
      (fun inp work out => Inv L emitted R s inp work out ∧ IsReg count (work fuel.castSucc))
      (fun inp work out => Inv L emitted R (run boxed count s) inp work out ∧ IsReg count (work fuel.castSucc))
      (timeBound L C count) := by
  have hb := framed_hoareTime boxed L C count emitted R hR s hlen hA
  apply hb.consequence
  · rintro inp work out ⟨hs, hf⟩
    refine ⟨hf.eq_regT, hs.1.input_read, fun j _ => (hs.1.works j).1, hs.1.output_read, ?_⟩
    simpa only [InvariantLoop.restore_self work fuel.castSucc count hf.eq_regT] using hs
  · exact fun _ _ _ hf => ⟨hf.on_work, hf.register⟩
  · exact le_rfl

theorem cubic_timeBound (L C : ℕ) :
    timeBound L C L = 3328 * L ^ 3 + 8687019 * L ^ 2 + (10896984 + 208 * C) * L + 2 := by
  unfold timeBound bodyBound SparseOffsetMarkedStep.bound OffsetTemplateProgram.bound
  ring1

end JointThermoComplexity.Complexity.SparseOffsetLoop

#print axioms JointThermoComplexity.Complexity.SparseOffsetLoop.hoareTime
#print axioms JointThermoComplexity.Complexity.SparseOffsetLoop.cubic_timeBound
