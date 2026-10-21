module
public import proofs.JointThermoComplexity.Complexity.EquationEmissionLoop

set_option autoImplicit false
@[expose] public section

/-! A univariate polynomial bounds the actual full loop in its initial serialized-state size. -/

namespace JointThermoComplexity.Complexity.EquationLoopPolynomial
open _root_.Complexity _root_.Complexity.TM EquationFuelFrame EquationLoopBounds
open DInstabilityComplexity.MachineConstruction

theorem step_time_mono : Monotone EquationEmissionStep.timeBound := by
  intro a b hab
  have hc := EquationBranchPolynomial.counter_time_mono 9 (by omega : 30 * a + 3 ≤ 30 * b + 3)
  have hlocal : EquationBranchPolynomial.timePolynomial.eval (2 * a) ≤ EquationBranchPolynomial.timePolynomial.eval (2 * b) := by
    rw [EquationBranchPolynomial.timePolynomial_eval, EquationBranchPolynomial.timePolynomial_eval]
    exact EquationBranchPolynomial.time_bound_mono (by omega) (by omega) (by omega) (by omega)
  dsimp only [EquationEmissionStep.timeBound, PendingEquationDispatch.timeBound, MainNodeEquation.timeBound]
  omega

theorem time_mono {L N L' N' : ℕ} (hL : L ≤ L') (hN : N ≤ N') :
    EquationEmissionLoop.timeBound L N ≤ EquationEmissionLoop.timeBound L' N' := by
  exact add_le_add (Nat.mul_le_mul hL (Nat.add_le_add_right (step_time_mono hN) 2)) (Nat.add_le_add_right hL 2)

noncomputable def timePolynomial : Polynomial ℕ :=
  Polynomial.X * (EquationEmissionStep.timePolynomial.comp (5 * Polynomial.X) + 2) + (Polynomial.X + 2)

theorem timePolynomial_eval (M : ℕ) : timePolynomial.eval M = EquationEmissionLoop.timeBound M (5 * M) := by
  simp [timePolynomial, EquationEmissionLoop.timeBound, EquationEmissionStep.timePolynomial_eval]

theorem hoareTime (arity L : ℕ) (s : PreorderEmissionControl.State) (hlen : s.scan.input.length ≤ L) :
    EquationEmissionLoop.machine.HoareTime
      (fun inp work out => Logical s arity L (bound arity L s) inp work out ∧ IsReg L (work fuel))
      (fun inp work out => Logical (PreorderEmissionControl.run L arity L s) arity L (bound arity L s) inp work out ∧ IsReg L (work fuel))
      (timePolynomial.eval (size arity L s)) := by
  apply (EquationEmissionLoop.hoareTime arity L s hlen).mono_bound
  rw [timePolynomial_eval]
  exact time_mono (length_le_size arity L s) (bound_le_size arity L s)

namespace WithPrefix
open RelocatedSpanQuery MainEquationWork MainNodeEquation
open HeaderAt (Cursor)

def Logical (prefixBits : List Bool) (s : PreorderEmissionControl.State) (arity L N : ℕ) : _root_.Complexity.TM.TapePred 32 :=
  fun inp work out => Cursor s.scan.before s.scan.input (prefixBits ++ RowEntriesCodec.entries s.emitted) inp work out ∧
    Bounded s.scan arity L N (fun _ => True) work

theorem reframe (prefixBits : List Bool) (s : PreorderEmissionControl.State) (arity L N : ℕ) (work work' : Work)
    (he : ∀ j, j ≠ fuel → work' j = work j) (hs : Parked (work' fuel)) (hz : (work' fuel).cells 0 = Γ.start) :
    ∀ inp out, Logical prefixBits s arity L N inp work out → Logical prefixBits s arity L N inp work' out := by
  rintro inp out ⟨hcur, adjusted, counts, values, hr, hadj, hq, hv, hzero⟩
  have hi : FormulaSpanRegisters.Inv (prefixBits ++ RowEntriesCodec.entries s.emitted)
      (High arity L adjusted counts values (fun _ => True)) s.scan inp work out :=
    ⟨hcur, to_scan s.scan arity L adjusted counts values (fun _ => True) work hr⟩
  have ho := FormulaSpanLoop.reframe (prefixBits ++ RowEntriesCodec.entries s.emitted)
    (High arity L adjusted counts values (fun _ => True)) (high_fuel_stable arity L adjusted counts values)
    s.scan work work' he hs hz inp out hi
  exact ⟨ho.1, adjusted, counts, values,
    from_scan s.scan arity L adjusted counts values (fun _ => True) work' ho.2, hadj, hq, hv, hzero⟩

theorem to_actual (prefixBits : List Bool) (s : PreorderEmissionControl.State) (arity L N v head : ℕ) (hhead : 1 ≤ head)
    (inp : Tape) (work : Work) (out : Tape)
    (hf : InvariantLoop.Frame fuel v head (Logical prefixBits s arity L N) inp work out) :
    Cursor s.scan.before s.scan.input (prefixBits ++ RowEntriesCodec.entries s.emitted) inp work out ∧
      Bounded s.scan arity L N (ExactFuel v head) work := by
  have ha := reframe prefixBits s arity L N (InvariantLoop.restore work fuel v) work
    (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
    (by rw [hf.fuel]; exact ⟨hhead, fun j hj => regCells_ne_start hj⟩)
    (by rw [hf.fuel]; rfl) inp out hf.invariant
  exact ⟨ha.1, map_bounded s.scan arity L N (fun _ => True) (ExactFuel v head) work (fun _ => hf.fuel) ha.2⟩

theorem from_actual (prefixBits : List Bool) (s : PreorderEmissionControl.State) (arity L N v head : ℕ)
    (inp : Tape) (work : Work) (out : Tape)
    (hc : Cursor s.scan.before s.scan.input (prefixBits ++ RowEntriesCodec.entries s.emitted) inp work out)
    (hr : Bounded s.scan arity L N (ExactFuel v head) work) :
    InvariantLoop.Frame fuel v head (Logical prefixBits s arity L N) inp work out := by
  have hbase : Logical prefixBits s arity L N inp work out :=
    ⟨hc, map_bounded s.scan arity L N (ExactFuel v head) (fun _ => True) work (fun _ => trivial) hr⟩
  obtain ⟨_, _, _, hb, _, _, _, _⟩ := hr
  have hrest := reframe prefixBits s arity L N work (InvariantLoop.restore work fuel v)
    (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
    (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape v)
    (by simp only [InvariantLoop.restore, Function.update_self, regT_cells, regCells_zero]) inp out hbase
  exact ⟨hb.2.2.basic.frame.extra, hc.input_read, fun j _ => (hb.1 j).read_ne_start, hc.output_read, hrest⟩

theorem step_hoareTime (prefixBits : List Bool) (s : PreorderEmissionControl.State) (arity L N : ℕ)
    (ha : arity ≤ N) (hL : L ≤ N) (ht : s.scan.terms ≤ N) (hf : s.scan.formulas ≤ N)
    (hc : s.scan.coordinates ≤ N) (hp : s.scan.before.length ≤ N) (hlen : s.scan.input.length ≤ L)
    (R : Work → Prop) (hR : Stable R) :
    EquationEmissionStep.machine.HoareTime
      (fun inp work out => Cursor s.scan.before s.scan.input (prefixBits ++ RowEntriesCodec.entries s.emitted) inp work out ∧
        Bounded s.scan arity L N R work)
      (fun inp work out =>
        let next := PreorderEmissionControl.step L arity s
        Cursor next.scan.before next.scan.input (prefixBits ++ RowEntriesCodec.entries next.emitted) inp work out ∧
          Bounded next.scan arity L N R work) (EquationEmissionStep.timeBound N) := by
  let emitted := (prefixBits ++ RowEntriesCodec.entries s.emitted) ++ RowEntriesCodec.entries (PreorderEmissionControl.localRows L arity s.scan)
  have he := PendingEquationDispatch.hoareTime s.scan arity L N (prefixBits ++ RowEntriesCodec.entries s.emitted)
    ha hL hc hp hlen R hR
  have hs := EquationEmissionStep.scan_hoareTime s.scan arity L N emitted hL ht hf hc hlen R hR
  have hseq := seqTM_hoareTime PendingEquationDispatch.machine (FormulaSpanStep.machine 24) he (by
    rintro inp work out ⟨hcur, hr⟩
    obtain ⟨hin, hwork, hout⟩ := hcur.phase
    rw [hin, hwork, hout]
    exact ⟨hcur, hr⟩) hs
  apply hseq.consequence (fun _ _ _ hr => hr)
  · intro inp work out hr
    simpa only [emitted, List.append_assoc, ← RowEntriesCodec.entries_append, PreorderEmissionControl.step] using hr
  · dsimp [EquationEmissionStep.timeBound]
    omega

theorem body_hoareTime (prefixBits : List Bool) (arity L i : ℕ) (s : PreorderEmissionControl.State)
    (hi : i < L) (hlen : s.scan.input.length ≤ L) :
    EquationEmissionStep.machine.HoareTime
      (InvariantLoop.Frame fuel L (i + 2) (Logical prefixBits (PreorderEmissionControl.run L arity i s) arity L (bound arity L s)))
      (InvariantLoop.Frame fuel L (i + 2) (Logical prefixBits (PreorderEmissionControl.run L arity (i + 1) s) arity L (bound arity L s)))
      (EquationEmissionStep.timeBound (bound arity L s)) := by
  let q := PreorderEmissionControl.run L arity i s
  let N := bound arity L s
  obtain ⟨ha, hL, ht, hf, hc, hp, hinput⟩ := current_bounds arity L i s (by omega) hlen
  have hb := step_hoareTime prefixBits q arity L N ha hL ht hf hc hp hinput (ExactFuel L (i + 2)) (exact_stable L (i + 2))
  intro inp work out hframe
  have hpre := to_actual prefixBits q arity L N L (i + 2) (by omega) inp work out hframe
  obtain ⟨d, t, htime, hd, hh, hcur, hr⟩ := hb inp work out hpre
  have hpost := from_actual prefixBits (PreorderEmissionControl.step L arity q) arity L N L (i + 2) d.input d.work d.output hcur hr
  refine ⟨d, t, htime, hd, hh, ?_⟩
  simpa only [run_succ_last] using hpost

theorem hoareTime (prefixBits : List Bool) (arity L : ℕ) (s : PreorderEmissionControl.State) (hlen : s.scan.input.length ≤ L) :
    EquationEmissionLoop.machine.HoareTime
      (fun inp work out => Logical prefixBits s arity L (bound arity L s) inp work out ∧ IsReg L (work fuel))
      (fun inp work out => Logical prefixBits (PreorderEmissionControl.run L arity L s) arity L (bound arity L s) inp work out ∧ IsReg L (work fuel))
      (timePolynomial.eval (size arity L s)) := by
  have h := InvariantLoop.hoareTime EquationEmissionStep.machine fuel
    (fun i => Logical prefixBits (PreorderEmissionControl.run L arity i s) arity L (bound arity L s))
    (EquationEmissionStep.timeBound (bound arity L s)) L (fun i hi => body_hoareTime prefixBits arity L i s hi hlen)
  apply h.consequence
  · rintro inp work out ⟨hi, hf⟩
    refine ⟨hf.eq_regT, hi.1.input_read, fun j _ => (hi.1.works j).1, hi.1.output_read, ?_⟩
    simpa only [InvariantLoop.restore_self work fuel L hf.eq_regT, PreorderEmissionControl.run] using hi
  · exact fun _ _ _ hf => ⟨hf.on_work, hf.register⟩
  · rw [timePolynomial_eval]
    exact time_mono (length_le_size arity L s) (bound_le_size arity L s)

end WithPrefix

end JointThermoComplexity.Complexity.EquationLoopPolynomial

#print axioms JointThermoComplexity.Complexity.EquationLoopPolynomial.timePolynomial_eval
#print axioms JointThermoComplexity.Complexity.EquationLoopPolynomial.hoareTime
#print axioms JointThermoComplexity.Complexity.EquationLoopPolynomial.WithPrefix.hoareTime
