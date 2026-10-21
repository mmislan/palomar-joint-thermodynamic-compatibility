module
public import proofs.JointThermoComplexity.Complexity.SourceTermLoopBody
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! Actual fixed-fuel term-forest scanning, with the displaced fuel head tracked exactly. -/

namespace JointThermoComplexity.Complexity.SourceTermLoop
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceIndexField SourceTermLoopState
open SourceTermLoopBody (Inv)
variable {n : ℕ}

theorem run_succ_last (arity count : ℕ) (s : State) : run arity (count + 1) s = step arity (run arity count s) := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih => exact ih (step arity s)

theorem reframe (ports : Fin 3 → Fin (n + 1)) (fuel pending left right : Fin (n + 1))
    (hfu : SourcePendingFrame.Separate ports fuel left right) (hfp : fuel ≠ pending)
    (L arity : ℕ) (emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop) (s : State)
    (work work' : Fin (n + 2) → Tape)
    (hw : ∀ j, j ≠ fuel.castSucc → work' j = work j)
    (hs : Parked (work' fuel.castSucc)) (hz : (work' fuel.castSucc).cells 0 = Γ.start)
    (hR : ∀ old new, (∀ j, j ≠ fuel → new j = old j) → R old → R new) :
    ∀ inp out, Inv ports pending left right L arity emitted R s inp work out →
      Inv ports pending left right L arity emitted R s inp work' out := by
  rintro inp out ⟨hc, hr, hp, hh, hf⟩
  have hs' : ∀ j, Parked (work' j) := by
    intro j
    by_cases hj : j = fuel.castSucc
    · subst j; exact hs
    · rw [hw j hj]; exact hr.safe j
  have hz' : ∀ j, (work' j).cells 0 = Γ.start := by
    intro j
    by_cases hj : j = fuel.castSucc
    · subst j; exact hz
    · rw [hw j hj]; exact hr.markers j
  have hl := hw left.castSucc (SourcePendingFrame.cast_ne hfu.left.symm)
  have hright := hw right.castSucc (SourcePendingFrame.cast_ne hfu.right.symm)
  have hflag := hw (NaturalScanBuffer.flag n) (SourcePendingFrame.cast_ne hfu.flag.symm)
  have hbuf := hw (NaturalScanBuffer.buffer n) (SourcePendingFrame.buffer_ne fuel)
  have hpend := hw pending.castSucc (SourcePendingFrame.cast_ne hfp.symm)
  have hready : Ready L left right arity R work' :=
    ⟨hs', hz', by simpa only [hbuf] using hr.encoded, by simpa only [hl] using hr.candidate,
      by simpa only [hright] using hr.arityBits, by simpa only [hright] using hr.arityZero,
      by simpa only [hflag] using hr.flagHead,
      hR _ _ (fun j hj => hw j.castSucc (SourcePendingFrame.cast_ne hj)) hr.frame⟩
  exact ⟨⟨hc.cells, hc.head, fun j => ⟨(hs' j).read_ne_start, (hs' j).1⟩, hc.tapePrefix, hc.zero⟩,
    hready, by simpa only [hpend] using hp,
    fun i => by simpa only [hw (ports i).castSucc (SourcePendingFrame.cast_ne (hfu.tags i).symm)] using hh i,
    by simpa only [hflag] using hf⟩

def machine (ports : Fin 3 → Fin (n + 1)) (fuel pending left right : Fin (n + 1)) : TM (n + 2) :=
  forRegTM (SourceTermLoopBody.machine ports pending left right) fuel.castSucc

def bodyBound (L pending fuel : ℕ) : ℕ := 32 * L + 2 * (pending + fuel) + 84
def timeBound (L pending fuel : ℕ) : ℕ := fuel * (bodyBound L pending fuel + 2) + (fuel + 2)

theorem frame_body_hoareTime (ports : Fin 3 → Fin (n + 1)) (fuel pending left right : Fin (n + 1))
    (hs : SourceTermTagRead.Separate ports left right)
    (sep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n))
    (hp : SourcePendingFrame.Separate ports pending left right)
    (hfu : SourcePendingFrame.Separate ports fuel left right) (hfp : fuel ≠ pending)
    (L arity count i : ℕ) (hi : i < count) (ha : arity.bits.length ≤ L)
    (emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop) (s : State) (hlen : s.input.length ≤ L)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ k, j ≠ ports k) → j ≠ pending → j ≠ fuel → work' j = work j) → R work → R work') :
    (SourceTermLoopBody.machine ports pending left right).HoareTime
      (InvariantLoop.Frame fuel.castSucc count (i + 2) (Inv ports pending left right L arity emitted R (run arity i s)))
      (InvariantLoop.Frame fuel.castSucc count (i + 2) (Inv ports pending left right L arity emitted R (run arity (i + 1) s)))
      (bodyBound L s.pending count) := by
  let ft : Tape := ⟨i + 2, regCells count⟩
  let RB : (Fin (n + 1) → Tape) → Prop := fun work => R work ∧ work fuel = ft
  have hRB : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ k, j ≠ ports k) → j ≠ pending → work' j = work j) → RB work → RB work' := by
    rintro work work' hw ⟨hr, hf⟩
    exact ⟨hR _ _ (fun j hl hr hf ht hp _ => hw j hl hr hf ht hp) hr,
      (hw fuel hfu.left hfu.right hfu.flag hfu.tags hfp).trans hf⟩
  have hRf : ∀ work work', (∀ j, j ≠ fuel → work' j = work j) → R work → R work' :=
    fun work work' hw => hR work work' (fun j _ _ _ _ _ hj => hw j hj)
  have hbounds := run_bounds arity i s
  have hb := SourceTermLoopBody.hoareTime ports pending left right hs sep hp L arity (s.pending + count) ha emitted RB
    (run arity i s) (hbounds.2.1.trans hlen) (by have := hbounds.1; omega) hRB
  intro inp work out hf
  have hactual : Inv ports pending left right L arity emitted R (run arity i s) inp work out := by
    apply reframe ports fuel pending left right hfu hfp L arity emitted R (run arity i s)
      (InvariantLoop.restore work fuel.castSucc count) work
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by rw [hf.fuel]; exact ⟨by change 1 ≤ i + 2; omega, fun j hj => regCells_ne_start hj⟩)
      (by rw [hf.fuel]; rfl) hRf inp out hf.invariant
  have hpre : Inv ports pending left right L arity emitted RB (run arity i s) inp work out := by
    rcases hactual with ⟨hc, hr, hv, hh, hf'⟩
    exact ⟨hc, ⟨hr.safe, hr.markers, hr.encoded, hr.candidate, hr.arityBits, hr.arityZero, hr.flagHead, hr.frame, hf.fuel⟩, hv, hh, hf'⟩
  obtain ⟨d, t, ht, hd, hh, hc', hr', hv', hheads', hflag'⟩ := hb inp work out hpre
  have hbase : Inv ports pending left right L arity emitted R (step arity (run arity i s)) d.input d.work d.output :=
    ⟨hc', ⟨hr'.safe, hr'.markers, hr'.encoded, hr'.candidate, hr'.arityBits, hr'.arityZero, hr'.flagHead, hr'.frame.1⟩,
      hv', hheads', hflag'⟩
  have hrestored : Inv ports pending left right L arity emitted R (step arity (run arity i s))
      d.input (InvariantLoop.restore d.work fuel.castSucc count) d.output := by
    apply reframe ports fuel pending left right hfu hfp L arity emitted R (step arity (run arity i s))
      d.work (InvariantLoop.restore d.work fuel.castSucc count)
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape count)
      (by simp only [InvariantLoop.restore, Function.update_self, regT_cells, regCells_zero]) hRf
      d.input d.output hbase
  refine ⟨d, t, ht, hd, hh, hr'.frame.2, hc'.input_read, ?_, hc'.output_read, ?_⟩
  · intro j _
    exact (hr'.safe j).read_ne_start
  · simpa only [run_succ_last] using hrestored

theorem framed_hoareTime (ports : Fin 3 → Fin (n + 1)) (fuel pending left right : Fin (n + 1))
    (hs : SourceTermTagRead.Separate ports left right)
    (sep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n))
    (hp : SourcePendingFrame.Separate ports pending left right)
    (hfu : SourcePendingFrame.Separate ports fuel left right) (hfp : fuel ≠ pending)
    (L arity count : ℕ) (ha : arity.bits.length ≤ L) (emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (s : State) (hlen : s.input.length ≤ L)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ k, j ≠ ports k) → j ≠ pending → j ≠ fuel → work' j = work j) → R work → R work') :
    (machine ports fuel pending left right).HoareTime
      (InvariantLoop.Frame fuel.castSucc count 1 (Inv ports pending left right L arity emitted R s))
      (InvariantLoop.Frame fuel.castSucc count 1 (Inv ports pending left right L arity emitted R (run arity count s)))
      (timeBound L s.pending count) := by
  exact InvariantLoop.hoareTime _ fuel.castSucc
    (fun i => Inv ports pending left right L arity emitted R (run arity i s))
    (bodyBound L s.pending count) count
    (fun i hi => frame_body_hoareTime ports fuel pending left right hs sep hp hfu hfp L arity count i hi ha emitted R s hlen hR)

theorem hoareTime (ports : Fin 3 → Fin (n + 1)) (fuel pending left right : Fin (n + 1))
    (hs : SourceTermTagRead.Separate ports left right)
    (sep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n))
    (hp : SourcePendingFrame.Separate ports pending left right)
    (hfu : SourcePendingFrame.Separate ports fuel left right) (hfp : fuel ≠ pending)
    (L arity count : ℕ) (ha : arity.bits.length ≤ L) (emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (s : State) (hlen : s.input.length ≤ L)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ k, j ≠ ports k) → j ≠ pending → j ≠ fuel → work' j = work j) → R work → R work') :
    (machine ports fuel pending left right).HoareTime
      (fun inp work out => Inv ports pending left right L arity emitted R s inp work out ∧ IsReg count (work fuel.castSucc))
      (fun inp work out => Inv ports pending left right L arity emitted R (run arity count s) inp work out ∧
        IsReg count (work fuel.castSucc)) (timeBound L s.pending count) := by
  have h := framed_hoareTime ports fuel pending left right hs sep hp hfu hfp L arity count ha emitted R s hlen hR
  exact h.consequence (by
    rintro inp work out ⟨hi, hf⟩
    refine ⟨hf.eq_regT, hi.1.input_read, fun j _ => (hi.1.works j).1, hi.1.output_read, ?_⟩
    simpa only [InvariantLoop.restore_self work fuel.castSucc count hf.eq_regT] using hi)
    (fun _ _ _ hf => ⟨hf.on_work, hf.register⟩) le_rfl

theorem quadratic_timeBound (L pending : ℕ) (hp : pending ≤ L) :
    timeBound L pending L ≤ 36 * L ^ 2 + 87 * L + 2 := by
  have hb : bodyBound L pending L + 2 ≤ 36 * L + 86 := by unfold bodyBound; omega
  calc timeBound L pending L = L * (bodyBound L pending L + 2) + (L + 2) := rfl
       _ ≤ L * (36 * L + 86) + (L + 2) := Nat.add_le_add_right (Nat.mul_le_mul_left L hb) _
       _ = 36 * L ^ 2 + 87 * L + 2 := by ring1

theorem source_forest_criterion (arity count pending : ℕ) (before input suffix : List Bool) :
    outcome (run arity count ⟨before, input, pending, true⟩) = some suffix ↔
      ∃ ts : List (RealSyntax.Term arity), ts.length = pending ∧ SourceTermScan.forestNodes ts ≤ count ∧
        input = SourceTermScan.forestCode ts ++ suffix := by
  rw [outcome_run]
  exact SourceTermControl.scan_some_iff arity count pending input suffix

end JointThermoComplexity.Complexity.SourceTermLoop

#print axioms JointThermoComplexity.Complexity.SourceTermLoop.frame_body_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceTermLoop.framed_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceTermLoop.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceTermLoop.quadratic_timeBound
#print axioms JointThermoComplexity.Complexity.SourceTermLoop.source_forest_criterion
