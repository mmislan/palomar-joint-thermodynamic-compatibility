module
public import proofs.JointThermoComplexity.Complexity.GeneratedEnergyStep
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! Actual bounded generated-section traversal. The two raw binary address
buffers advance once per emitted fixed template; a separate unary fuel tape
is retained exactly at its displaced head and restored on loop completion.
-/

namespace JointThermoComplexity.Complexity.GeneratedEnergyLoop
open _root_.Complexity _root_.Complexity.TM BinaryIncrementRun StrictGeneratedTemplates GeneratedEnergyStep
open HeaderAt (Cursor)
variable {w : ℕ}

def valuesAt (values : Fin 2 → ℕ) (i : ℕ) : Fin 2 → ℕ := fun j => values j + i

def entries (values : Fin 2 → ℕ) (kind : Kind) (count : ℕ) : List Bool :=
  (List.ofFn (fun i : Fin count => RowSquareCanonical.entries (data (valuesAt values i.val) kind))).flatten

theorem values_zero (values : Fin 2 → ℕ) : valuesAt values 0 = values := by
  funext i
  exact Nat.add_zero _

theorem values_succ (values : Fin 2 → ℕ) (i : ℕ) : advance (valuesAt values i) = valuesAt values (i + 1) := by
  funext j
  simp only [advance, valuesAt, Nat.add_assoc]

theorem entries_zero (values : Fin 2 → ℕ) (kind : Kind) : entries values kind 0 = [] := rfl

theorem entries_succ (values : Fin 2 → ℕ) (kind : Kind) (i : ℕ) :
    entries values kind (i + 1) = entries values kind i ++ RowSquareCanonical.entries (data (valuesAt values i) kind) := by
  unfold entries
  rw [List.ofFn_succ_last, List.flatten_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, Fin.val_castSucc, Fin.val_last]

def FuelStable (r : Fin w) (R : (Fin w → Tape) → Prop) : Prop :=
  ∀ work next, (∀ k, k ≠ r → next k = work k) → R work → R next

def ExactFuel (r : Fin w) (v head : ℕ) (work : Fin w → Tape) : Prop := work r = ⟨head, regCells v⟩

theorem exact_stable (p : Ports w) (r : Fin w) (hp : ∀ i, r ≠ p.index i) (v head : ℕ) : Stable p (ExactFuel r v head) := by
  intro work next he hf
  exact (he r hp).trans hf

theorem reframe (p : Ports w) (r : Fin w) (hp : ∀ i, r ≠ p.index i)
    (values : Fin 2 → ℕ) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hRF : FuelStable r R)
    (work next : Fin w → Tape) (he : ∀ k, k ≠ r → next k = work k) (hs : Parked (next r)) :
    ∀ inp out, Logical p values before input emitted R inp work out → Logical p values before input emitted R inp next out := by
  rintro inp out ⟨hc, hr⟩
  have hs' : ∀ k, Parked (next k) := by
    intro k
    by_cases hk : k = r
    · subst k
      exact hs
    · rw [he k hk]
      exact hr.safe k
  have hc' : Cursor before input emitted inp next out :=
    ⟨hc.cells, hc.head, fun k => ⟨(hs' k).read_ne_start, (hs' k).1⟩, hc.tapePrefix, hc.zero⟩
  exact ⟨hc', ⟨hs', fun i => by simpa only [he _ (hp i).symm] using hr.registers i,
    hRF work next he hr.extra⟩⟩

theorem to_actual (p : Ports w) (r : Fin w) (hp : ∀ i, r ≠ p.index i)
    (values : Fin 2 → ℕ) (before input emitted : List Bool) (v head : ℕ) (hhead : 1 ≤ head)
    (R : (Fin w → Tape) → Prop) (hRF : FuelStable r R)
    (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hf : InvariantLoop.Frame r v head (Logical p values before input emitted R) inp work out) :
    Logical p values before input emitted (fun work => R work ∧ ExactFuel r v head work) inp work out := by
  obtain ⟨hc, hr⟩ := reframe p r hp values before input emitted R hRF (InvariantLoop.restore work r v) work
    (fun k hk => by simp only [InvariantLoop.restore, Function.update_of_ne hk])
    (by rw [hf.fuel]; exact ⟨hhead, fun k hk => regCells_ne_start hk⟩) inp out hf.invariant
  exact ⟨hc, { hr with extra := ⟨hr.extra, hf.fuel⟩ }⟩

theorem from_actual (p : Ports w) (r : Fin w) (hp : ∀ i, r ≠ p.index i)
    (values : Fin 2 → ℕ) (before input emitted : List Bool) (v head : ℕ)
    (R : (Fin w → Tape) → Prop) (hRF : FuelStable r R)
    (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (h : Logical p values before input emitted (fun work => R work ∧ ExactFuel r v head work) inp work out) :
    InvariantLoop.Frame r v head (Logical p values before input emitted R) inp work out := by
  rcases h with ⟨hc, hr⟩
  rcases hr.extra with ⟨hx, hf⟩
  have hbase : Logical p values before input emitted R inp work out := ⟨hc, { hr with extra := hx }⟩
  have hrest := reframe p r hp values before input emitted R hRF work (InvariantLoop.restore work r v)
    (fun k hk => by simp only [InvariantLoop.restore, Function.update_of_ne hk])
    (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape v) inp out hbase
  exact ⟨hf, hc.input_read, fun k _ => (hr.safe k).read_ne_start, hc.output_read, hrest⟩

def machine (p : Ports w) (r : Fin w) (kind : Kind) : TM w := forRegTM (GeneratedEnergyStep.machine p kind) r
def timeBound (W count : ℕ) (kind : Kind) : ℕ := count * (GeneratedEnergyStep.timeBound W kind + 2) + (count + 2)

theorem hoareTime (p : Ports w) (r : Fin w) (hp : ∀ i, r ≠ p.index i) (values : Fin 2 → ℕ)
    (W count : ℕ) (hW : ∀ i < count, ∀ j, (values j + i).bits.length ≤ W)
    (kind : Kind) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : Stable p R) (hRF : FuelStable r R) :
    (machine p r kind).HoareTime
      (fun inp work out => Logical p values before input emitted R inp work out ∧ IsReg count (work r))
      (fun inp work out => Logical p (valuesAt values count) before input (emitted ++ entries values kind count) R inp work out ∧
        IsReg count (work r)) (timeBound W count kind) := by
  let P : ℕ → _root_.Complexity.TM.TapePred w := fun i =>
    Logical p (valuesAt values i) before input (emitted ++ entries values kind i) R
  have hbody : ∀ i, i < count → (GeneratedEnergyStep.machine p kind).HoareTime
      (InvariantLoop.Frame r count (i + 2) (P i)) (InvariantLoop.Frame r count (i + 2) (P (i + 1)))
      (GeneratedEnergyStep.timeBound W kind) := by
    intro i hi
    have hframe : Stable p (fun work => R work ∧ ExactFuel r count (i + 2) work) := by
      rintro work next he ⟨hr, hf⟩
      exact ⟨hR work next he hr, exact_stable p r hp count (i + 2) work next he hf⟩
    have h := GeneratedEnergyStep.hoareTime p (valuesAt values i) W (hW i hi) kind before input
      (emitted ++ entries values kind i) (fun work => R work ∧ ExactFuel r count (i + 2) work) hframe
    apply h.consequence
    · exact fun inp work out hf => to_actual p r hp (valuesAt values i) before input
        (emitted ++ entries values kind i) count (i + 2) (by omega) R hRF inp work out hf
    · intro inp work out hh
      apply from_actual p r hp (valuesAt values (i + 1)) before input
        (emitted ++ entries values kind (i + 1)) count (i + 2) R hRF inp work out
      simpa only [values_succ, entries_succ, List.append_assoc] using hh
    · exact le_rfl
  have h := InvariantLoop.hoareTime (GeneratedEnergyStep.machine p kind) r P (GeneratedEnergyStep.timeBound W kind) count hbody
  apply h.consequence
  · rintro inp work out ⟨⟨hc, hr⟩, hf⟩
    refine ⟨hf.eq_regT, hc.input_read, fun k _ => (hr.safe k).read_ne_start, hc.output_read, ?_⟩
    rw [InvariantLoop.restore_self work r count hf.eq_regT]
    simpa only [P, values_zero, entries_zero, List.append_nil, Logical] using And.intro hc hr
  · intro inp work out hf
    exact ⟨hf.on_work, hf.register⟩
  · exact le_rfl

theorem bounded_hoareTime (p : Ports w) (r : Fin w) (hp : ∀ i, r ≠ p.index i) (values : Fin 2 → ℕ)
    (W count : ℕ) (hW : ∀ j, values j + count ≤ W) (kind : Kind) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable p R) (hRF : FuelStable r R) :
    (machine p r kind).HoareTime
      (fun inp work out => Logical p values before input emitted R inp work out ∧ IsReg count (work r))
      (fun inp work out => Logical p (valuesAt values count) before input (emitted ++ entries values kind count) R inp work out ∧
        IsReg count (work r)) (timeBound W count kind) := by
  apply hoareTime p r hp values W count _ kind before input emitted R hR hRF
  intro i hi j
  exact (BinaryIncrementControl.bits_length_le (values j + i)).trans (by have := hW j; omega)

end JointThermoComplexity.Complexity.GeneratedEnergyLoop

#print axioms JointThermoComplexity.Complexity.GeneratedEnergyLoop.entries_succ
#print axioms JointThermoComplexity.Complexity.GeneratedEnergyLoop.hoareTime
#print axioms JointThermoComplexity.Complexity.GeneratedEnergyLoop.bounded_hoareTime
