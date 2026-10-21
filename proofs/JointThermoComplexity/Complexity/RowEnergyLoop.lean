module
public import proofs.JointThermoComplexity.Complexity.RowEnergyStep
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! Bounded actual traversal of the outer marked row list. The outer fuel is
separate from every row-reader/emitter port, including its nested prefix fuel.
The exact displaced fuel tape is retained by each body execution.
-/

namespace JointThermoComplexity.Complexity.RowEnergyLoop
open _root_.Complexity _root_.Complexity.TM BoxBufferState RowEnergyControl RowEnergyStep
open HeaderAt (Cursor)
variable {w : ℕ}

def FuelStable (r : Fin (w + 1)) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work next, (∀ k, k ≠ r → next k = work k) → R work → R next

def ExactFuel (r : Fin (w + 1)) (v head : ℕ) (work : Fin (w + 1) → Tape) : Prop :=
  work r = ⟨head, regCells v⟩

theorem exact_stable (p : Ports w) (r : Fin (w + 1)) (ha : r ≠ p.active)
    (hp : ∀ a, r ≠ p.square.index a) (v head : ℕ) : Stable p (ExactFuel r v head) := by
  intro work next he hf
  exact (he r ha hp).trans hf

theorem reframe (p : Ports w) (r : Fin (w + 1)) (ha : r ≠ p.active)
    (hp : ∀ a, r ≠ p.square.index a) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (hRF : FuelStable r R)
    (work next : Fin (w + 1) → Tape) (he : ∀ k, k ≠ r → next k = work k) (hs : Parked (next r)) :
    ∀ inp out, Logical p s scaleBits B W R inp work out → Logical p s scaleBits B W R inp next out := by
  rintro inp out ⟨hc, hr⟩
  have hs' : ∀ k, Parked (next k) := by
    intro k
    by_cases hk : k = r
    · subst k
      exact hs
    · rw [he k hk]
      exact hr.square.saved.safe k
  have hc' : Cursor s.row.before s.row.input s.emitted inp next out :=
    ⟨hc.cells, hc.head, fun k => ⟨(hs' k).read_ne_start, (hs' k).1⟩, hc.tapePrefix, hc.zero⟩
  have hrow (a : Fin 25) : next (p.square.row.index a) = work (p.square.row.index a) := he _ (hp _).symm
  have hsaved : EquationRowFrame.Ready p.square.row s.row B R next := by
    refine ⟨hs', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hRF work next he hr.square.saved.extra⟩
    · intro i
      simpa only [EquationRowFrame.Ports.presence, hrow] using hr.square.saved.presence i
    · intro i j
      simpa only [EquationRowFrame.Ports.flag, EquationRowFrame.Ports.slot, hrow] using hr.square.saved.flags i j
    · intro i j
      simpa only [EquationRowFrame.Ports.word, EquationRowFrame.Ports.slot, hrow] using hr.square.saved.words i j
    · intro i
      simpa only [EquationRowFrame.Ports.coefficient, EquationRowFrame.Ports.slot, hrow] using hr.square.saved.coefficients i
    · simpa only [EquationRowFrame.Ports.available, hrow] using hr.square.saved.available_head
    · simpa only [EquationRowFrame.Ports.available, hrow] using hr.square.saved.available_read
    · simpa only [EquationRowFrame.Ports.loopAvailable, hrow] using hr.square.saved.loop_head
    · simpa only [EquationRowFrame.Ports.scratch, hrow] using hr.square.saved.scratch
    · simpa only [EquationRowFrame.Ports.fuel, hrow] using hr.square.saved.fuel
  exact ⟨hc', ⟨⟨hsaved,
    by simpa only [he p.square.scale (hp _).symm] using hr.square.scale,
    by simpa only [he p.square.scale (hp _).symm] using hr.square.scale_zero,
    hr.square.scale_length, hr.square.word_bound,
    by simpa only [he p.square.constant (hp _).symm] using hr.square.constant,
    by simpa only [he p.square.compare (hp _).symm] using hr.square.compare_head⟩,
    by simpa only [he p.active ha.symm] using hr.active_head,
    by simpa only [he p.active ha.symm] using hr.active_read⟩⟩

theorem to_actual (p : Ports w) (r : Fin (w + 1)) (ha : r ≠ p.active)
    (hp : ∀ a, r ≠ p.square.index a) (s : State) (scaleBits : List Bool) (B W v head : ℕ)
    (hhead : 1 ≤ head) (R : (Fin (w + 1) → Tape) → Prop) (hRF : FuelStable r R)
    (inp : Tape) (work : Fin (w + 1) → Tape) (out : Tape)
    (hf : InvariantLoop.Frame r v head (Logical p s scaleBits B W R) inp work out) :
    Logical p s scaleBits B W (fun work => R work ∧ ExactFuel r v head work) inp work out := by
  obtain ⟨hc, hr⟩ := reframe p r ha hp s scaleBits B W R hRF (InvariantLoop.restore work r v) work
    (fun k hk => by simp only [InvariantLoop.restore, Function.update_of_ne hk])
    (by rw [hf.fuel]; exact ⟨hhead, fun k hk => regCells_ne_start hk⟩) inp out hf.invariant
  exact ⟨hc, { hr with square := { hr.square with saved := { hr.square.saved with extra := ⟨hr.square.saved.extra, hf.fuel⟩ } } }⟩

theorem from_actual (p : Ports w) (r : Fin (w + 1)) (ha : r ≠ p.active)
    (hp : ∀ a, r ≠ p.square.index a) (s : State) (scaleBits : List Bool) (B W v head : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (hRF : FuelStable r R)
    (inp : Tape) (work : Fin (w + 1) → Tape) (out : Tape)
    (h : Logical p s scaleBits B W (fun work => R work ∧ ExactFuel r v head work) inp work out) :
    InvariantLoop.Frame r v head (Logical p s scaleBits B W R) inp work out := by
  rcases h with ⟨hc, hr⟩
  rcases hr.square.saved.extra with ⟨hx, hf⟩
  have hbase : Logical p s scaleBits B W R inp work out :=
    ⟨hc, { hr with square := { hr.square with saved := { hr.square.saved with extra := hx } } }⟩
  have hrest := reframe p r ha hp s scaleBits B W R hRF work (InvariantLoop.restore work r v)
    (fun k hk => by simp only [InvariantLoop.restore, Function.update_of_ne hk])
    (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape v) inp out hbase
  exact ⟨hf, hc.input_read, fun k _ => (hr.square.saved.safe k).read_ne_start, hc.output_read, hrest⟩

def machine (p : Ports w) (r : Fin (w + 1)) : TM (w + 1) := forRegTM (RowEnergyStep.machine p) r

def timeBound (B W fuel : ℕ) : ℕ := fuel * (RowEnergyStep.timeBound B W + 2) + (fuel + 2)

def expected (scale : ℕ) : List (List (ℤ × List ℕ)) → EquationRowControl.State → List Bool → List Bool → State
  | [], s, suffix, emitted =>
      ⟨{ s with before := s.before ++ code [], input := suffix, available := true }, false, emitted⟩
  | row :: rows, s, suffix, emitted => expected scale rows
      (EquationRowControl.expected { s with before := s.before ++ [true] } row (code rows ++ suffix)) suffix
      (emitted ++ RowSquareCanonical.entries (SparseInteger.scale (-256)
        (SparseInteger.square (RowSquareCanonical.homogeneous scale row))))

def entries (scale : ℕ) (rows : List (List (ℤ × List ℕ))) : List Bool :=
  rows.flatMap (fun row => RowSquareCanonical.entries (SparseInteger.scale (-256)
    (SparseInteger.square (RowSquareCanonical.homogeneous scale row))))

theorem expected_active (scale : ℕ) (rows : List (List (ℤ × List ℕ)))
    (s : EquationRowControl.State) (suffix emitted : List Bool) : (expected scale rows s suffix emitted).active = false := by
  induction rows generalizing s emitted with
  | nil => rfl
  | cons row rows ih => exact ih _ _

theorem expected_input (scale : ℕ) (rows : List (List (ℤ × List ℕ)))
    (s : EquationRowControl.State) (suffix emitted : List Bool) : (expected scale rows s suffix emitted).row.input = suffix := by
  induction rows generalizing s emitted with
  | nil => rfl
  | cons row rows ih => exact ih _ _

theorem expected_output (scale : ℕ) (rows : List (List (ℤ × List ℕ)))
    (s : EquationRowControl.State) (suffix emitted : List Bool) :
    (expected scale rows s suffix emitted).emitted = emitted ++ entries scale rows := by
  induction rows generalizing s emitted with
  | nil => exact (List.append_nil emitted).symm
  | cons row rows ih =>
    simpa only [expected, entries, List.flatMap_cons, List.append_assoc] using
      ih (EquationRowControl.expected { s with before := s.before ++ [true] } row (code rows ++ suffix))
        (emitted ++ RowSquareCanonical.entries (SparseInteger.scale (-256)
          (SparseInteger.square (RowSquareCanonical.homogeneous scale row))))

theorem run_minimal (B scale : ℕ) (rows : List (List (ℤ × List ℕ)))
    (hr : ∀ row ∈ rows, row.length ≤ 3) (hc : ∀ row ∈ rows, ∀ a ∈ row, a.1.natAbs ≤ 5)
    (hf : ∀ row ∈ rows, ∀ a ∈ row, a.2.length + 1 ≤ B)
    (s : EquationRowControl.State) (suffix emitted : List Bool) :
    run B scale.bits (rows.length + 1) ⟨{ s with input := code rows ++ suffix }, true, emitted⟩ =
      expected scale rows s suffix emitted := by
  induction rows generalizing s emitted with
  | nil => simpa only [List.length_nil, Nat.zero_add, run, expected] using step_nil B scale.bits s suffix emitted
  | cons row rows ih =>
    rw [List.length_cons, run_succ_start,
      step_cons B scale s row rows suffix emitted (hr row (by simp)) (hc row (by simp)) (hf row (by simp))]
    exact ih (fun q hq => hr q (List.mem_cons_of_mem row hq))
      (fun q hq => hc q (List.mem_cons_of_mem row hq))
      (fun q hq => hf q (List.mem_cons_of_mem row hq))
      (EquationRowControl.expected { s with before := s.before ++ [true] } row (code rows ++ suffix))
      (emitted ++ RowSquareCanonical.entries (SparseInteger.scale (-256)
        (SparseInteger.square (RowSquareCanonical.homogeneous scale row))))

theorem run_code (B scale fuel : ℕ) (rows : List (List (ℤ × List ℕ)))
    (hr : ∀ row ∈ rows, row.length ≤ 3) (hc : ∀ row ∈ rows, ∀ a ∈ row, a.1.natAbs ≤ 5)
    (hf : ∀ row ∈ rows, ∀ a ∈ row, a.2.length + 1 ≤ B) (hFuel : rows.length + 1 ≤ fuel)
    (s : EquationRowControl.State) (suffix emitted : List Bool) :
    run B scale.bits fuel ⟨{ s with input := code rows ++ suffix }, true, emitted⟩ =
      expected scale rows s suffix emitted := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hFuel
  rw [run_add, run_minimal B scale rows hr hc hf]
  exact run_inactive B scale.bits extra _ (expected_active scale rows s suffix emitted)

theorem hoareTime (p : Ports w) (r : Fin (w + 1)) (ha : r ≠ p.active)
    (hp : ∀ a, r ≠ p.square.index a) (s : State) (scaleBits : List Bool) (B W fuel : ℕ)
    (hB : 2 ≤ B) (hlen : s.row.input.length ≤ B)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) (hRF : FuelStable r R) :
    (machine p r).HoareTime
      (fun inp work out => Logical p s scaleBits B W R inp work out ∧ IsReg fuel (work r))
      (fun inp work out => Logical p (run B scaleBits fuel s) scaleBits B W R inp work out ∧ IsReg fuel (work r))
      (timeBound B W fuel) := by
  let P : ℕ → _root_.Complexity.TM.TapePred (w + 1) := fun i => Logical p (run B scaleBits i s) scaleBits B W R
  have hbody : ∀ i, i < fuel → (RowEnergyStep.machine p).HoareTime
      (InvariantLoop.Frame r fuel (i + 2) (P i)) (InvariantLoop.Frame r fuel (i + 2) (P (i + 1)))
      (RowEnergyStep.timeBound B W) := by
    intro i _
    have hframe : Stable p (fun work => R work ∧ ExactFuel r fuel (i + 2) work) := by
      rintro work next he ⟨hr, hf⟩
      exact ⟨hR work next he hr, exact_stable p r ha hp fuel (i + 2) work next he hf⟩
    have h := RowEnergyStep.hoareTime p (run B scaleBits i s) scaleBits B W hB
      ((run_length B scaleBits i s).trans hlen) (fun work => R work ∧ ExactFuel r fuel (i + 2) work) hframe
    exact h.consequence
      (fun inp work out hf => to_actual p r ha hp (run B scaleBits i s) scaleBits B W fuel (i + 2) (by omega) R hRF inp work out hf)
      (fun inp work out hh => from_actual p r ha hp (step B scaleBits (run B scaleBits i s)) scaleBits B W fuel (i + 2) R hRF inp work out hh)
      le_rfl
  have h := InvariantLoop.hoareTime (RowEnergyStep.machine p) r P (RowEnergyStep.timeBound B W) fuel hbody
  apply h.consequence
  · rintro inp work out ⟨⟨hc, hr⟩, hf⟩
    refine ⟨hf.eq_regT, hc.input_read, fun k _ => (hr.square.saved.safe k).read_ne_start, hc.output_read, ?_⟩
    rw [InvariantLoop.restore_self work r fuel hf.eq_regT]
    exact ⟨hc, hr⟩
  · intro inp work out hf
    exact ⟨hf.on_work, hf.register⟩
  · exact le_rfl

theorem row_code_length (row : List (ℤ × List ℕ)) (rows : List (List (ℤ × List ℕ))) (hrow : row ∈ rows) :
    (EquationRowControl.code row).length ≤ (code rows).length := by
  induction rows with
  | nil => simp at hrow
  | cons q rest ih =>
    rcases List.mem_cons.mp hrow with he | hm
    · subst q
      simp only [code, RowWordCodec.marked, List.length_cons, List.length_append]
      omega
    · have h := ih hm
      simp only [code, RowWordCodec.marked, List.length_cons, List.length_append] at h ⊢
      omega

theorem encoded_hoareTime (p : Ports w) (r : Fin (w + 1)) (ha : r ≠ p.active)
    (hp : ∀ a, r ≠ p.square.index a) (B W scale : ℕ) (hB : 2 ≤ B)
    (rows : List (List (ℤ × List ℕ))) (hr : ∀ row ∈ rows, row.length ≤ 3)
    (hc : ∀ row ∈ rows, ∀ a ∈ row, a.1.natAbs ≤ 5)
    (s : EquationRowControl.State) (suffix emitted : List Bool) (hlen : (code rows ++ suffix).length ≤ B)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) (hRF : FuelStable r R) :
    (machine p r).HoareTime
      (fun inp work out => Logical p ⟨{ s with input := code rows ++ suffix }, true, emitted⟩ scale.bits B W R inp work out ∧ IsReg B (work r))
      (fun inp work out => Logical p (expected scale rows s suffix emitted) scale.bits B W R inp work out ∧ IsReg B (work r))
      (timeBound B W B) := by
  have hFuel : rows.length + 1 ≤ B := by
    have h := code_length rows
    rw [List.length_append] at hlen
    omega
  have hf : ∀ row ∈ rows, ∀ a ∈ row, a.2.length + 1 ≤ B := by
    intro row hrow a ha
    have hterm := EquationRowMachine.code_monomial_length row a ha
    have hrowlen := row_code_length row rows hrow
    rw [List.length_append] at hlen
    omega
  simpa only [run_code B scale B rows hr hc hf hFuel s suffix emitted] using
    hoareTime p r ha hp ⟨{ s with input := code rows ++ suffix }, true, emitted⟩ scale.bits B W B hB hlen R hR hRF

end JointThermoComplexity.Complexity.RowEnergyLoop

#print axioms JointThermoComplexity.Complexity.RowEnergyLoop.reframe
#print axioms JointThermoComplexity.Complexity.RowEnergyLoop.to_actual
#print axioms JointThermoComplexity.Complexity.RowEnergyLoop.hoareTime
#print axioms JointThermoComplexity.Complexity.RowEnergyLoop.expected_output
#print axioms JointThermoComplexity.Complexity.RowEnergyLoop.encoded_hoareTime
