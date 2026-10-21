module
public import proofs.JointThermoComplexity.Complexity.FormulaSpanStep

set_option autoImplicit false
@[expose] public section

/-! Actual bounded mixed subtree traversal returns the exact allocated formula coordinates with read-only IO. -/

namespace JointThermoComplexity.Complexity.FormulaSpanLoop
open _root_.Complexity _root_.Complexity.TM FormulaSpanRegisters
open HeaderAt (Cursor)
variable {n : ℕ}

def fuel (n : ℕ) : Fin (n + 8) := TermSpanRegisters.fuel (n + 1)
theorem fuel_outside (n : ℕ) : Outside n (fuel n) :=
  ⟨TermSpanRegisters.fuel_outside (n + 1), (formulaPending_fuel n).symm⟩

def Stable (R : (Fin (n + 8) → Tape) → Prop) : Prop :=
  ∀ work work', (∀ j, Outside n j → j ≠ fuel n → work' j = work j) → R work → R work'

theorem reframe (emitted : List Bool) (R : (Fin (n + 8) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ fuel n → work' j = work j) → R work → R work')
    (s : FormulaSpanControl.State) (work work' : Fin (n + 8) → Tape)
    (hw : ∀ j, j ≠ fuel n → work' j = work j)
    (hs : Parked (work' (fuel n))) (hz : (work' (fuel n)).cells 0 = Γ.start) :
    ∀ inp out, Inv emitted R s inp work out → Inv emitted R s inp work' out := by
  have hF : ∀ old new, (∀ j, j ≠ TermSpanRegisters.fuel (n + 1) → new j = old j) →
      Frame s.formulas R old → Frame s.formulas R new := by
    rintro old new he ⟨hf, hr⟩
    exact ⟨by simpa only [he (formulaPending n) (formulaPending_fuel n)] using hf, hR old new he hr⟩
  exact TermSpanLoop.reframe emitted (Frame s.formulas R) hF (FormulaSpanControl.termState s) work work' hw hs hz

def machine (n : ℕ) : TM (n + 8) := forRegTM (FormulaSpanStep.machine n) (fuel n)
def bodyBound (L terms formulas coordinates count : ℕ) : ℕ :=
  L + 2 * (terms + 2 * count) + 2 * (formulas + count) + 8 * (coordinates + 4 * count) + 100
def timeBound (L terms formulas coordinates count : ℕ) : ℕ :=
  count * (bodyBound L terms formulas coordinates count + 2) + (count + 2)

theorem frame_body_hoareTime (L count i : ℕ) (hi : i < count) (emitted : List Bool)
    (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R) (s : FormulaSpanControl.State) (hlen : s.input.length ≤ L) :
    (FormulaSpanStep.machine n).HoareTime
      (InvariantLoop.Frame (fuel n) count (i + 2) (Inv emitted R (FormulaSpanControl.run i s)))
      (InvariantLoop.Frame (fuel n) count (i + 2) (Inv emitted R (FormulaSpanControl.run (i + 1) s)))
      (bodyBound L s.terms s.formulas s.coordinates count) := by
  let ft : Tape := ⟨i + 2, regCells count⟩
  let RB : (Fin (n + 8) → Tape) → Prop := fun work => R work ∧ work (fuel n) = ft
  have hRB : FormulaSpanRegisters.Stable RB := by
    rintro work work' he ⟨hr, hf⟩
    exact ⟨hR work work' (fun j hj _ => he j hj) hr, (he (fuel n) (fuel_outside n)).trans hf⟩
  have hRf : ∀ work work', (∀ j, j ≠ fuel n → work' j = work j) → R work → R work' :=
    fun work work' he => hR work work' (fun j _ hj => he j hj)
  have hbounds := FormulaSpanControl.run_bounds i s
  have hb := FormulaSpanStep.bounded_hoareTime L (s.terms + 2 * count) (s.formulas + count) (s.coordinates + 4 * count)
    emitted RB hRB (FormulaSpanControl.run i s) (hbounds.2.2.2.1.trans hlen)
    (by have := hbounds.1; omega) (by have := hbounds.2.1; omega) (by have := hbounds.2.2.1; omega)
  intro inp work out hf
  have hactual : Inv emitted R (FormulaSpanControl.run i s) inp work out := by
    apply reframe emitted R hRf (FormulaSpanControl.run i s) (InvariantLoop.restore work (fuel n) count) work
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by rw [hf.fuel]; exact ⟨by change 1 ≤ i + 2; omega, fun j hj => regCells_ne_start hj⟩)
      (by rw [hf.fuel]; rfl) inp out hf.invariant
  have hpre : Inv emitted RB (FormulaSpanControl.run i s) inp work out := by
    rcases hactual with ⟨hc, hr⟩
    exact ⟨hc, hr.safe, hr.markers, hr.counter, hr.nodeReg, hr.tagHeads, hr.flagHead, hr.frame.1, hr.frame.2, hf.fuel⟩
  obtain ⟨d, t, ht, hd, hh, hc', hr'⟩ := hb inp work out hpre
  have hbase : Inv emitted R (FormulaSpanControl.step (FormulaSpanControl.run i s)) d.input d.work d.output :=
    ⟨hc', hr'.safe, hr'.markers, hr'.counter, hr'.nodeReg, hr'.tagHeads, hr'.flagHead, hr'.frame.1, hr'.frame.2.1⟩
  have hrestored : Inv emitted R (FormulaSpanControl.step (FormulaSpanControl.run i s))
      d.input (InvariantLoop.restore d.work (fuel n) count) d.output := by
    apply reframe emitted R hRf _ d.work (InvariantLoop.restore d.work (fuel n) count)
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
      (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape count)
      (by simp only [InvariantLoop.restore, Function.update_self, regT_cells, regCells_zero])
      d.input d.output hbase
  refine ⟨d, t, ht, hd, hh, hr'.frame.2.2, hc'.input_read, ?_, hc'.output_read, ?_⟩
  · intro j _
    exact (hr'.safe j).read_ne_start
  · simpa only [FormulaSpanControl.run_succ_last] using hrestored

theorem framed_hoareTime (L count : ℕ) (emitted : List Bool) (R : (Fin (n + 8) → Tape) → Prop)
    (hR : Stable R) (s : FormulaSpanControl.State) (hlen : s.input.length ≤ L) :
    (machine n).HoareTime
      (InvariantLoop.Frame (fuel n) count 1 (Inv emitted R s))
      (InvariantLoop.Frame (fuel n) count 1 (Inv emitted R (FormulaSpanControl.run count s)))
      (timeBound L s.terms s.formulas s.coordinates count) :=
  InvariantLoop.hoareTime (FormulaSpanStep.machine n) (fuel n)
    (fun i => Inv emitted R (FormulaSpanControl.run i s)) (bodyBound L s.terms s.formulas s.coordinates count) count
    (fun i hi => frame_body_hoareTime L count i hi emitted R hR s hlen)

theorem hoareTime (L count : ℕ) (emitted : List Bool) (R : (Fin (n + 8) → Tape) → Prop)
    (hR : Stable R) (s : FormulaSpanControl.State) (hlen : s.input.length ≤ L) :
    (machine n).HoareTime
      (fun inp work out => Inv emitted R s inp work out ∧ IsReg count (work (fuel n)))
      (fun inp work out => Inv emitted R (FormulaSpanControl.run count s) inp work out ∧ IsReg count (work (fuel n)))
      (timeBound L s.terms s.formulas s.coordinates count) := by
  have h := framed_hoareTime L count emitted R hR s hlen
  exact h.consequence (by
    rintro inp work out ⟨hi, hf⟩
    refine ⟨hf.eq_regT, hi.1.input_read, fun j _ => (hi.1.works j).1, hi.1.output_read, ?_⟩
    simpa only [InvariantLoop.restore_self work (fuel n) count hf.eq_regT] using hi)
    (fun _ _ _ hf => ⟨hf.on_work, hf.register⟩) le_rfl

theorem quadratic_timeBound (L : ℕ) : timeBound L 0 1 0 L = 39 * L ^ 2 + 105 * L + 2 := by
  unfold timeBound bodyBound
  ring1

theorem run_from_cursor (L count : ℕ) (emitted : List Bool) (R : (Fin (n + 8) → Tape) → Prop)
    (hR : Stable R) (s : FormulaSpanControl.State) (hlen : s.input.length ≤ L)
    (inp : Tape) (work : Fin (n + 8) → Tape) (out : Tape) (hp : Inv emitted R s inp work out)
    (hf : IsReg count (work (fuel n))) :
    ∃ d t, t ≤ timeBound L s.terms s.formulas s.coordinates count ∧
      (machine n).reachesIn t ⟨(machine n).qstart, inp, work, out⟩ d ∧ (machine n).halted d ∧
      Inv emitted R (FormulaSpanControl.run count s) d.input d.work d.output ∧
      IsReg count (d.work (fuel n)) ∧ d.input.cells = inp.cells ∧ d.output = out := by
  obtain ⟨d, t, ht, hd, hh, hpost, hreg⟩ := hoareTime L count emitted R hR s hlen inp work out ⟨hp, hf⟩
  have hw := (FormulaSpanControl.run_bounds count s).2.2.2.2
  have hi : d.input.cells = inp.cells := by
    rw [hpost.1.cells, hp.1.cells]
    simp only [FormulaSpanControl.termState, hw]
  exact ⟨d, t, ht, hd, hh, hpost, hreg, hi,
    TermSpanLoop.output_unique hp.1.tapePrefix hp.1.zero hpost.1.tapePrefix hpost.1.zero⟩

theorem formula_hoareTime {arity : ℕ} (L count coordinates : ℕ) (p : RealSyntax.Formula arity)
    (hn : SmallSyntaxForests.formulaTokens p ≤ count) (before suffix emitted : List Bool) (hlen : (p.code ++ suffix).length ≤ L)
    (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R) :
    (machine n).HoareTime
      (fun inp work out => Inv emitted R ⟨before, p.code ++ suffix, 0, 1, coordinates⟩ inp work out ∧ IsReg count (work (fuel n)))
      (fun inp work out => Inv emitted R ⟨before ++ p.code, suffix, 0, 0, coordinates + SourceCoordinateEnumeration.formulaCount p⟩ inp work out ∧
        IsReg count (work (fuel n))) (timeBound L 0 1 coordinates count) := by
  have h := hoareTime L count emitted R hR ⟨before, p.code ++ suffix, 0, 1, coordinates⟩ hlen
  rw [FormulaSpanCorrect.run_formula count p hn before suffix coordinates] at h
  exact h

end JointThermoComplexity.Complexity.FormulaSpanLoop

#print axioms JointThermoComplexity.Complexity.FormulaSpanLoop.hoareTime
#print axioms JointThermoComplexity.Complexity.FormulaSpanLoop.quadratic_timeBound
#print axioms JointThermoComplexity.Complexity.FormulaSpanLoop.run_from_cursor
#print axioms JointThermoComplexity.Complexity.FormulaSpanLoop.formula_hoareTime
