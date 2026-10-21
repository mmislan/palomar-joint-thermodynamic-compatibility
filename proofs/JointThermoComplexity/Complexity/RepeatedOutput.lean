module
public import proofs.JointThermoComplexity.Complexity.FixedOutput
public import proofs.JointThermoComplexity.Complexity.LoopCursor

set_option autoImplicit false
@[expose] public section

/-! Bounded repetition of a syntax word with exact output and restored work state. -/

namespace JointThermoComplexity.Complexity.RepeatedOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def copies (word : List Bool) : ℕ → List Bool
  | 0 => []
  | v + 1 => copies word v ++ word

theorem copies_length (word : List Bool) (v : ℕ) : (copies word v).length = v * word.length := by
  induction v with
  | zero => simp [copies]
  | succ v ih => simp only [copies, List.length_append, ih, Nat.succ_mul]

theorem copies_singleton (bit : Bool) (v : ℕ) : copies [bit] v = List.replicate v bit := by
  induction v with
  | zero => rfl
  | succ v ih =>
    rw [copies, ih]
    simpa only [List.replicate_one] using (List.replicate_add v 1 bit).symm

theorem restored_safe (work : Fin w → Tape) (fuel : Fin w) (v : ℕ)
    (h : ∀ j, Parked (work j)) : ∀ j, Parked (InvariantLoop.restore work fuel v j) := by
  intro j
  by_cases hj : j = fuel
  · subst j
    rw [InvariantLoop.restore, Function.update_self]
    exact (reg_regT v).parked
  · rw [InvariantLoop.restore, Function.update_of_ne hj]
    exact h j

def StateInv (before input emitted word : List Bool) (R : (Fin w → Tape) → Prop) (i : ℕ) :
    _root_.Complexity.TM.TapePred w := fun inp work out =>
  Cursor before input (emitted ++ copies word i) inp work out ∧ (∀ j, Parked (work j)) ∧ R work

theorem body_hoareTime (fuel : Fin w) (v i : ℕ) (before input emitted word : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (emitBitsTM (n := w) word).HoareTime
      (InvariantLoop.Frame fuel v (i + 2) (StateInv before input emitted word R i))
      (InvariantLoop.Frame fuel v (i + 2) (StateInv before input emitted word R (i + 1))) word.length := by
  intro inp work out hf
  rcases hf.invariant with ⟨hc, hs, hr⟩
  have hfuel : Parked (work fuel) := by
    rw [hf.fuel]
    exact parked_regCells (by omega : 1 ≤ i + 2)
  have hphysical := LoopCursor.physical fuel v hc ⟨hfuel.read_ne_start, hfuel.1⟩
  have hsafe : ∀ j, Parked (work j) := by
    intro j
    by_cases hj : j = fuel
    · subst j
      exact hfuel
    · have h := hs j
      rw [InvariantLoop.restore, Function.update_of_ne hj] at h
      exact h
  obtain ⟨d, t, ht, hreach, hhalt, hdcur, hdsafe, hdwork⟩ :=
    FixedOutput.hoareTime word before input (emitted ++ copies word i) (fun work' => work' = work)
      inp work out ⟨hphysical, hsafe, rfl⟩
  have hdfuel : d.work fuel = ⟨i + 2, regCells v⟩ := by rw [hdwork]; exact hf.fuel
  refine ⟨d, t, ht, hreach, hhalt, hdfuel, hdcur.input_read,
    (fun j _ => (hdcur.works j).1), hdcur.output_read, ?_, restored_safe d.work fuel v hdsafe, ?_⟩
  · simpa only [copies, List.append_assoc] using LoopCursor.restore hdcur fuel v
  · simpa only [hdwork] using hr

def machine (fuel : Fin w) (word : List Bool) : TM w := forRegTM (emitBitsTM word) fuel

theorem hoareTime (fuel : Fin w) (v : ℕ) (before input emitted word : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine fuel word).HoareTime
      (fun inp work out => IsReg v (work fuel) ∧ Cursor before input emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => IsReg v (work fuel) ∧ Cursor before input (emitted ++ copies word v) inp work out ∧
        (∀ j, Parked (work j)) ∧ R work)
      (v * (word.length + 2) + (v + 2)) := by
  rintro inp work out ⟨hf, hc, hs, hr⟩
  have hpre : InvariantLoop.Frame fuel v 1 (StateInv before input emitted word R 0) inp work out := by
    refine ⟨hf.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [InvariantLoop.restore_self work fuel v hf.eq_regT]
    simpa only [StateInv, copies, List.append_nil] using (show Cursor before input emitted inp work out ∧
      (∀ j, Parked (work j)) ∧ R work from ⟨hc, hs, hr⟩)
  obtain ⟨d, t, ht, hreach, hhalt, hpost⟩ :=
    InvariantLoop.hoareTime (emitBitsTM word) fuel (StateInv before input emitted word R) word.length v
      (fun i _ => body_hoareTime fuel v i before input emitted word R) inp work out hpre
  exact ⟨d, t, ht, hreach, hhalt, hpost.register, hpost.on_work⟩

end JointThermoComplexity.Complexity.RepeatedOutput

#print axioms JointThermoComplexity.Complexity.RepeatedOutput.hoareTime
