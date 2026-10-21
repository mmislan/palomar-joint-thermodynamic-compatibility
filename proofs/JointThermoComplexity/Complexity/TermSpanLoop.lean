module
public import proofs.JointThermoComplexity.Complexity.TermSpanStep
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! Actual bounded read-only subtree traversal and measurement, including displaced fuel and outside frames. -/

namespace JointThermoComplexity.Complexity.TermSpanLoop
open _root_.Complexity _root_.Complexity.TM TermSpanRegisters
open HeaderAt (Cursor)
variable {n : ℕ}

def Stable (R : (Fin (n + 7) → Tape) → Prop) : Prop :=
  ∀ work work', (∀ j, Outside n j → j ≠ fuel n → work' j = work j) → R work → R work'

theorem reframe (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ fuel n → work' j = work j) → R work → R work')
    (s : TermSpanControl.State) (work work' : Fin (n + 7) → Tape)
    (hw : ∀ j, j ≠ fuel n → work' j = work j)
    (hs : Parked (work' (fuel n))) (hz : (work' (fuel n)).cells 0 = Γ.start) :
    ∀ inp out, Inv emitted R s inp work out → Inv emitted R s inp work' out := by
  rintro inp out ⟨hc, hr⟩
  have hs' : ∀ j, Parked (work' j) := by
    intro j
    by_cases hj : j = fuel n
    · subst j; exact hs
    · rw [hw j hj]; exact hr.safe j
  have hz' : ∀ j, (work' j).cells 0 = Γ.start := by
    intro j
    by_cases hj : j = fuel n
    · subst j; exact hz
    · rw [hw j hj]; exact hr.markers j
  refine ⟨⟨hc.cells, hc.head, fun j => ⟨(hs' j).read_ne_start, (hs' j).1⟩,
    hc.tapePrefix, hc.zero⟩, hs', hz', ?_, ?_, ?_, ?_, hR work work' hw hr.frame⟩
  · simpa only [hw (pending n) (fuel_outside n).1.symm] using hr.counter
  · simpa only [hw (nodeCounter n) (fuel_outside n).2.1.symm] using hr.nodeReg
  · intro i
    simpa only [hw (tags n i) (fuel_tags n i).symm] using hr.tagHeads i
  · simpa only [hw (flag n) (fuel_outside n).2.2.1.symm] using hr.flagHead

def machine (n : ℕ) : TM (n + 7) := forRegTM (TermSpanStep.machine n) (fuel n)
def bodyBound (L pending nodes count : ℕ) : ℕ := L + 2 * (pending + count) + 2 * (nodes + count) + 42
def timeBound (L pending nodes count : ℕ) : ℕ := count * (bodyBound L pending nodes count + 2) + (count + 2)

theorem frame_body_hoareTime (L count i : ℕ) (hi : i < count) (emitted : List Bool)
    (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R) (s : TermSpanControl.State) (hlen : s.input.length ≤ L) :
    (TermSpanStep.machine n).HoareTime
      (InvariantLoop.Frame (fuel n) count (i + 2) (Inv emitted R (TermSpanControl.run i s)))
      (InvariantLoop.Frame (fuel n) count (i + 2) (Inv emitted R (TermSpanControl.run (i + 1) s)))
      (bodyBound L s.pending s.nodes count) := by
  let ft : Tape := ⟨i + 2, regCells count⟩
  let RB : (Fin (n + 7) → Tape) → Prop := fun work => R work ∧ work (fuel n) = ft
  have hRB : TermSpanRegisters.Stable RB := by
    rintro work work' he ⟨hr, hf⟩
    exact ⟨hR work work' (fun j hj _ => he j hj) hr, (he (fuel n) (fuel_outside n)).trans hf⟩
  have hRf : ∀ work work', (∀ j, j ≠ fuel n → work' j = work j) → R work → R work' :=
    fun work work' he => hR work work' (fun j _ hj => he j hj)
  have hbounds := TermSpanControl.run_bounds i s
  have hb := TermSpanStep.bounded_hoareTime L (s.pending + count) (s.nodes + count) emitted RB hRB
    (TermSpanControl.run i s) (hbounds.2.2.1.trans hlen) (by have := hbounds.1; omega) (by have := hbounds.2.1; omega)
  intro inp work out hf
  have hactual : Inv emitted R (TermSpanControl.run i s) inp work out := by
    apply reframe emitted R hRf (TermSpanControl.run i s) (InvariantLoop.restore work (fuel n) count) work
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by rw [hf.fuel]; exact ⟨by change 1 ≤ i + 2; omega, fun j hj => regCells_ne_start hj⟩)
      (by rw [hf.fuel]; rfl) inp out hf.invariant
  have hpre : Inv emitted RB (TermSpanControl.run i s) inp work out := by
    rcases hactual with ⟨hc, hr⟩
    exact ⟨hc, hr.safe, hr.markers, hr.counter, hr.nodeReg, hr.tagHeads, hr.flagHead, hr.frame, hf.fuel⟩
  obtain ⟨d, t, ht, hd, hh, hc', hr'⟩ := hb inp work out hpre
  have hbase : Inv emitted R (TermSpanControl.step (TermSpanControl.run i s)) d.input d.work d.output :=
    ⟨hc', hr'.safe, hr'.markers, hr'.counter, hr'.nodeReg, hr'.tagHeads, hr'.flagHead, hr'.frame.1⟩
  have hrestored : Inv emitted R (TermSpanControl.step (TermSpanControl.run i s))
      d.input (InvariantLoop.restore d.work (fuel n) count) d.output := by
    apply reframe emitted R hRf _ d.work (InvariantLoop.restore d.work (fuel n) count)
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape count)
      (by simp only [InvariantLoop.restore, Function.update_self, regT_cells, regCells_zero])
      d.input d.output hbase
  refine ⟨d, t, ht, hd, hh, hr'.frame.2, hc'.input_read, ?_, hc'.output_read, ?_⟩
  · intro j _
    exact (hr'.safe j).read_ne_start
  · simpa only [TermSpanControl.run_succ_last] using hrestored

theorem framed_hoareTime (L count : ℕ) (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop)
    (hR : Stable R) (s : TermSpanControl.State) (hlen : s.input.length ≤ L) :
    (machine n).HoareTime
      (InvariantLoop.Frame (fuel n) count 1 (Inv emitted R s))
      (InvariantLoop.Frame (fuel n) count 1 (Inv emitted R (TermSpanControl.run count s)))
      (timeBound L s.pending s.nodes count) :=
  InvariantLoop.hoareTime (TermSpanStep.machine n) (fuel n)
    (fun i => Inv emitted R (TermSpanControl.run i s)) (bodyBound L s.pending s.nodes count) count
    (fun i hi => frame_body_hoareTime L count i hi emitted R hR s hlen)

theorem hoareTime (L count : ℕ) (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop)
    (hR : Stable R) (s : TermSpanControl.State) (hlen : s.input.length ≤ L) :
    (machine n).HoareTime
      (fun inp work out => Inv emitted R s inp work out ∧ IsReg count (work (fuel n)))
      (fun inp work out => Inv emitted R (TermSpanControl.run count s) inp work out ∧ IsReg count (work (fuel n)))
      (timeBound L s.pending s.nodes count) := by
  have h := framed_hoareTime L count emitted R hR s hlen
  exact h.consequence (by
    rintro inp work out ⟨hi, hf⟩
    refine ⟨hf.eq_regT, hi.1.input_read, fun j _ => (hi.1.works j).1, hi.1.output_read, ?_⟩
    simpa only [InvariantLoop.restore_self work (fuel n) count hf.eq_regT] using hi)
    (fun _ _ _ hf => ⟨hf.on_work, hf.register⟩) le_rfl

theorem quadratic_timeBound (L : ℕ) : timeBound L 1 0 L = 5 * L ^ 2 + 47 * L + 2 := by
  unfold timeBound bodyBound
  ring1

theorem output_unique {emitted : List Bool} {out out' : Tape}
    (h : out.HasBinaryPrefix emitted) (hz : out.cells 0 = Γ.start)
    (h' : out'.HasBinaryPrefix emitted) (hz' : out'.cells 0 = Γ.start) : out' = out := by
  apply Tape.ext
  · exact h'.1.trans h.1.symm
  · funext k
    cases k with
    | zero => exact hz'.trans hz.symm
    | succ j =>
      by_cases hj : j < emitted.length
      · exact (h'.2.1 j hj).trans (h.2.1 j hj).symm
      · exact (h'.2.2 j (by omega)).trans (h.2.2 j (by omega)).symm

theorem run_from_cursor (L count : ℕ) (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop)
    (hR : Stable R) (s : TermSpanControl.State) (hlen : s.input.length ≤ L)
    (inp : Tape) (work : Fin (n + 7) → Tape) (out : Tape) (hp : Inv emitted R s inp work out)
    (hf : IsReg count (work (fuel n))) :
    ∃ d t, t ≤ timeBound L s.pending s.nodes count ∧
      (machine n).reachesIn t ⟨(machine n).qstart, inp, work, out⟩ d ∧ (machine n).halted d ∧
      Inv emitted R (TermSpanControl.run count s) d.input d.work d.output ∧
      IsReg count (d.work (fuel n)) ∧ d.input.cells = inp.cells ∧ d.output = out := by
  obtain ⟨d, t, ht, hd, hh, hpost, hreg⟩ := hoareTime L count emitted R hR s hlen inp work out ⟨hp, hf⟩
  have hw := (TermSpanControl.run_bounds count s).2.2.2
  have hi : d.input.cells = inp.cells := by rw [hpost.1.cells, hp.1.cells, hw]
  exact ⟨d, t, ht, hd, hh, hpost, hreg, hi, output_unique hp.1.tapePrefix hp.1.zero hpost.1.tapePrefix hpost.1.zero⟩

theorem term_hoareTime {arity : ℕ} (L count nodes : ℕ) (t : RealSyntax.Term arity) (hn : t.size ≤ count)
    (before suffix emitted : List Bool) (hlen : (t.code ++ suffix).length ≤ L)
    (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R) :
    (machine n).HoareTime
      (fun inp work out => Inv emitted R ⟨before, t.code ++ suffix, 1, nodes⟩ inp work out ∧ IsReg count (work (fuel n)))
      (fun inp work out => Inv emitted R ⟨before ++ t.code, suffix, 0, nodes + t.size⟩ inp work out ∧ IsReg count (work (fuel n)))
      (timeBound L 1 nodes count) := by
  have h := hoareTime L count emitted R hR ⟨before, t.code ++ suffix, 1, nodes⟩ hlen
  rw [TermSpanCorrect.run_term count t hn before suffix nodes] at h
  exact h

end JointThermoComplexity.Complexity.TermSpanLoop

#print axioms JointThermoComplexity.Complexity.TermSpanLoop.hoareTime
#print axioms JointThermoComplexity.Complexity.TermSpanLoop.quadratic_timeBound
#print axioms JointThermoComplexity.Complexity.TermSpanLoop.run_from_cursor
#print axioms JointThermoComplexity.Complexity.TermSpanLoop.term_hoareTime
