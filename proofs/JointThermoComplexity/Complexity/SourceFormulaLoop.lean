module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaLoopBody
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! Actual outer formula iteration, with a separate restored fuel register and cubic cost. -/

namespace JointThermoComplexity.Complexity.SourceFormulaLoop
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters
open SourceTermLoopState (State outcome)
open SourceFormulaLoopState
variable {n : ℕ}

theorem run_succ_last (arity L count : ℕ) (s : State) :
    run arity L (count + 1) s = step arity L (run arity L count s) := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih => exact ih (step arity L s)

theorem reframe (d : Layout n) (fuel : Fin (n + 1)) (hfu : Outside d fuel)
    (L arity : ℕ) (emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop) (s : State)
    (work work' : Fin (n + 2) → Tape)
    (hw : ∀ j, j ≠ fuel.castSucc → work' j = work j)
    (hs : Parked (work' fuel.castSucc)) (hz : (work' fuel.castSucc).cells 0 = Γ.start)
    (hR : ∀ old new, (∀ j, j ≠ fuel → new j = old j) → R old → R new) :
    ∀ inp out, Inv d L arity emitted R s inp work out → Inv d L arity emitted R s inp work' out := by
  rintro inp out ⟨hc, hr, hp, hf⟩
  have hs' : ∀ j, Parked (work' j) := by
    intro j
    by_cases hj : j = fuel.castSucc
    · subst j; exact hs
    · rw [hw j hj]; exact hr.base.safe j
  have hz' : ∀ j, (work' j).cells 0 = Γ.start := by
    intro j
    by_cases hj : j = fuel.castSucc
    · subst j; exact hz
    · rw [hw j hj]; exact hr.base.markers j
  have hl := hw d.left.castSucc (SourcePendingFrame.cast_ne hfu.left.symm)
  have hright := hw d.right.castSucc (SourcePendingFrame.cast_ne hfu.right.symm)
  have hflag := hw (NaturalScanBuffer.flag n) (SourcePendingFrame.cast_ne hfu.flag.symm)
  have hbuf := hw (NaturalScanBuffer.buffer n) (SourcePendingFrame.buffer_ne fuel)
  have hpend := hw d.formulaPending.castSucc (SourcePendingFrame.cast_ne hfu.formulaPending.symm)
  have hinnerFuel := hw d.termFuel.castSucc (SourcePendingFrame.cast_ne hfu.termFuel.symm)
  have hinnerPending := hw d.termPending.castSucc (SourcePendingFrame.cast_ne hfu.termPending.symm)
  have hbase : SourceIndexField.Ready L d.left d.right arity R work' :=
    ⟨hs', hz', by simpa only [hbuf] using hr.base.encoded, by simpa only [hl] using hr.base.candidate,
      by simpa only [hright] using hr.base.arityBits, by simpa only [hright] using hr.base.arityZero,
      by simpa only [hflag] using hr.base.flagHead,
      hR _ _ (fun j hj => hw j.castSucc (SourcePendingFrame.cast_ne hj)) hr.base.frame⟩
  have hready : Ready d L arity R work' :=
    ⟨hbase, by simpa only [hinnerFuel] using hr.termFuel, by simpa only [hinnerPending] using hr.termPending,
      fun i => by simpa only [hw (d.tags i).castSucc (SourcePendingFrame.cast_ne (hfu.tags i).symm)] using hr.tagHeads i⟩
  exact ⟨⟨hc.cells, hc.head, fun j => ⟨(hs' j).read_ne_start, (hs' j).1⟩, hc.tapePrefix, hc.zero⟩,
    hready, by simpa only [hpend] using hp, by simpa only [hflag] using hf⟩

def machine (d : Layout n) (fuel : Fin (n + 1)) : TM (n + 2) :=
  forRegTM (SourceFormulaLoopBody.machine d) fuel.castSucc

def bodyBound (L pending fuel : ℕ) : ℕ := 34 * L ^ 2 + 93 * L + 2 * (pending + fuel) + 62
def timeBound (L pending fuel : ℕ) : ℕ := fuel * (bodyBound L pending fuel + 2) + (fuel + 2)

theorem frame_body_hoareTime (d : Layout n) (fuel : Fin (n + 1)) (hfu : Outside d fuel)
    (L arity count i : ℕ) (hi : i < count) (ha : arity.bits.length ≤ L)
    (emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop) (s : State) (hlen : s.input.length ≤ L)
    (hR : ∀ work work', (∀ j, Outside d j → j ≠ fuel → work' j = work j) → R work → R work') :
    (SourceFormulaLoopBody.machine d).HoareTime
      (InvariantLoop.Frame fuel.castSucc count (i + 2) (Inv d L arity emitted R (run arity L i s)))
      (InvariantLoop.Frame fuel.castSucc count (i + 2) (Inv d L arity emitted R (run arity L (i + 1) s)))
      (bodyBound L s.pending count) := by
  let ft : Tape := ⟨i + 2, regCells count⟩
  let RB : (Fin (n + 1) → Tape) → Prop := fun work => R work ∧ work fuel = ft
  have hRB : Stable d RB := by
    rintro work work' hw ⟨hr, hf⟩
    exact ⟨hR _ _ (fun j hj _ => hw j hj) hr, (hw fuel hfu).trans hf⟩
  have hRf : ∀ work work', (∀ j, j ≠ fuel → work' j = work j) → R work → R work' :=
    fun work work' hw => hR work work' (fun j _ hj => hw j hj)
  have hbounds := run_bounds arity L i s
  have hb := SourceFormulaLoopBody.hoareTime d L arity (s.pending + count) ha emitted RB
    (run arity L i s) (hbounds.2.1.trans hlen) (by have := hbounds.1; omega) hRB
  intro inp work out hf
  have hactual : Inv d L arity emitted R (run arity L i s) inp work out := by
    apply reframe d fuel hfu L arity emitted R (run arity L i s)
      (InvariantLoop.restore work fuel.castSucc count) work
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by rw [hf.fuel]; exact ⟨by change 1 ≤ i + 2; omega, fun j hj => regCells_ne_start hj⟩)
      (by rw [hf.fuel]; rfl) hRf inp out hf.invariant
  have hpre : Inv d L arity emitted RB (run arity L i s) inp work out := by
    rcases hactual with ⟨hc, hr, hv, hf'⟩
    exact ⟨hc, ⟨⟨hr.base.safe, hr.base.markers, hr.base.encoded, hr.base.candidate, hr.base.arityBits,
      hr.base.arityZero, hr.base.flagHead, hr.base.frame, hf.fuel⟩, hr.termFuel, hr.termPending, hr.tagHeads⟩, hv, hf'⟩
  obtain ⟨c, t, ht, hd, hh, hc', hr', hv', hflag'⟩ := hb inp work out hpre
  have hbase : Inv d L arity emitted R (step arity L (run arity L i s)) c.input c.work c.output :=
    ⟨hc', ⟨⟨hr'.base.safe, hr'.base.markers, hr'.base.encoded, hr'.base.candidate, hr'.base.arityBits,
      hr'.base.arityZero, hr'.base.flagHead, hr'.base.frame.1⟩, hr'.termFuel, hr'.termPending, hr'.tagHeads⟩, hv', hflag'⟩
  have hrestored : Inv d L arity emitted R (step arity L (run arity L i s))
      c.input (InvariantLoop.restore c.work fuel.castSucc count) c.output := by
    apply reframe d fuel hfu L arity emitted R (step arity L (run arity L i s))
      c.work (InvariantLoop.restore c.work fuel.castSucc count)
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape count)
      (by simp only [InvariantLoop.restore, Function.update_self, regT_cells, regCells_zero]) hRf c.input c.output hbase
  refine ⟨c, t, ht, hd, hh, hr'.base.frame.2, hc'.input_read, ?_, hc'.output_read, ?_⟩
  · intro j _
    exact (hr'.base.safe j).read_ne_start
  · simpa only [run_succ_last] using hrestored

theorem framed_hoareTime (d : Layout n) (fuel : Fin (n + 1)) (hfu : Outside d fuel)
    (L arity count : ℕ) (ha : arity.bits.length ≤ L) (emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (s : State) (hlen : s.input.length ≤ L)
    (hR : ∀ work work', (∀ j, Outside d j → j ≠ fuel → work' j = work j) → R work → R work') :
    (machine d fuel).HoareTime
      (InvariantLoop.Frame fuel.castSucc count 1 (Inv d L arity emitted R s))
      (InvariantLoop.Frame fuel.castSucc count 1 (Inv d L arity emitted R (run arity L count s)))
      (timeBound L s.pending count) := by
  exact InvariantLoop.hoareTime _ fuel.castSucc
    (fun i => Inv d L arity emitted R (run arity L i s)) (bodyBound L s.pending count) count
    (fun i hi => frame_body_hoareTime d fuel hfu L arity count i hi ha emitted R s hlen hR)

theorem hoareTime (d : Layout n) (fuel : Fin (n + 1)) (hfu : Outside d fuel)
    (L arity count : ℕ) (ha : arity.bits.length ≤ L) (emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (s : State) (hlen : s.input.length ≤ L)
    (hR : ∀ work work', (∀ j, Outside d j → j ≠ fuel → work' j = work j) → R work → R work') :
    (machine d fuel).HoareTime
      (fun inp work out => Inv d L arity emitted R s inp work out ∧ IsReg count (work fuel.castSucc))
      (fun inp work out => Inv d L arity emitted R (run arity L count s) inp work out ∧
        IsReg count (work fuel.castSucc)) (timeBound L s.pending count) := by
  have h := framed_hoareTime d fuel hfu L arity count ha emitted R s hlen hR
  exact h.consequence (by
    rintro inp work out ⟨hi, hf⟩
    refine ⟨hf.eq_regT, hi.1.input_read, fun j _ => (hi.1.works j).1, hi.1.output_read, ?_⟩
    simpa only [InvariantLoop.restore_self work fuel.castSucc count hf.eq_regT] using hi)
    (fun _ _ _ hf => ⟨hf.on_work, hf.register⟩) le_rfl

theorem cubic_timeBound (L : ℕ) : timeBound L 1 L = 34 * L ^ 3 + 95 * L ^ 2 + 67 * L + 2 := by
  unfold timeBound bodyBound
  ring1

theorem source_forest_criterion (arity L count pending : ℕ) (before input suffix : List Bool) (hlen : input.length ≤ L) :
    outcome (run arity L count ⟨before, input, pending, true⟩) = some suffix ↔
      ∃ ps : List (RealSyntax.Formula arity), ps.length = pending ∧ SourceFormulaScan.forestNodes ps ≤ count ∧
        input = SourceFormulaScan.forestCode ps ++ suffix := by
  rw [outcome_run]
  exact SourceFormulaScan.scan_some_iff L count pending input suffix hlen

theorem source_formula_criterion (arity L : ℕ) (before input suffix : List Bool) (hlen : input.length ≤ L) :
    outcome (run arity L L ⟨before, input, 1, true⟩) = some suffix ↔
      ∃ p : RealSyntax.Formula arity, input = p.code ++ suffix := by
  rw [outcome_run]
  exact SourceFormulaScan.scan_one_iff L input suffix hlen

end JointThermoComplexity.Complexity.SourceFormulaLoop

#print axioms JointThermoComplexity.Complexity.SourceFormulaLoop.frame_body_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceFormulaLoop.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceFormulaLoop.cubic_timeBound
#print axioms JointThermoComplexity.Complexity.SourceFormulaLoop.source_formula_criterion
