module
public import proofs.JointThermoComplexity.Complexity.FieldControl
public import proofs.JointThermoComplexity.Complexity.NaturalField
public import proofs.JointThermoComplexity.Complexity.LoopCursor

set_option autoImplicit false
@[expose] public section

/-!
# Binary natural and positive arrays on the actual TM

The dimension register counts fields, never numeric values. Each binary payload
is scanned by the checked canonical field machine and combined with retained
validity. The array invariant handles malformed input and preserves arbitrary
state outside its fuel and two status tapes.
-/

namespace JointThermoComplexity.Complexity.NaturalArray
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def Value : Bool → Type
  | false => ℕ
  | true => {k : ℕ // 0 < k}

def codec : (requirePositive : Bool) → FiniteCodec.Codec (Value requirePositive)
  | false => FiniteCodec.natural
  | true => FiniteCodec.positive

def control : (requirePositive : Bool) → FieldControl.Control (codec requirePositive)
  | false => FieldControl.natural
  | true => FieldControl.positive

theorem taken_eq (requirePositive : Bool) (input : List Bool) :
    (control requirePositive).taken input = PayloadControl.copied .empty input := by cases requirePositive <;> rfl

theorem rest_eq (requirePositive : Bool) (input : List Bool) :
    (control requirePositive).rest input = NumericCursor.naturalRest input := by cases requirePositive <;> rfl

theorem valid_eq (requirePositive : Bool) (input : List Bool) :
    (control requirePositive).valid input = NaturalMachineParser.accepted requirePositive input := by cases requirePositive <;> rfl

variable {n : ℕ}

def StateInv (requirePositive initial : Bool) (master : Fin (n + 1))
    (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (i : ℕ) : _root_.Complexity.TM.TapePred (n + 1) := fun inp work out =>
  Cursor (before ++ (control requirePositive).copied i input) ((control requirePositive).tail i input)
    (emitted ++ (control requirePositive).copied i input) inp work out ∧
    (work (NaturalMachine.flagIndex n)).head = 1 ∧ (work master).head = 1 ∧
    (work master).read = Γ.ofBool (initial && (control requirePositive).accepted i input) ∧ R work

theorem body_hoareTime (requirePositive initial : Bool) (r master : Fin (n + 1))
    (hr : r ≠ NaturalMachine.flagIndex n) (hm : master ≠ NaturalMachine.flagIndex n) (hrm : r ≠ master)
    (v i : ℕ) (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work',
      (∀ j, j ≠ r → j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (NaturalField.machine requirePositive master).HoareTime
      (InvariantLoop.Frame r v (i + 2) (StateInv requirePositive initial master before input emitted R i))
      (InvariantLoop.Frame r v (i + 2) (StateInv requirePositive initial master before input emitted R (i + 1)))
      (input.length + 4) := by
  intro inp work out hf
  rcases hf.invariant with ⟨hc, hfh, hmh, hmr, hstate⟩
  have hphysical : Cursor (before ++ (control requirePositive).copied i input)
      ((control requirePositive).tail i input) (emitted ++ (control requirePositive).copied i input) inp work out := by
    apply LoopCursor.physical r v hc
    rw [hf.fuel]
    refine ⟨?_, ?_⟩
    · change regCells v (i + 2) ≠ Γ.start
      exact regCells_ne_start (by omega)
    · change 1 ≤ i + 2
      omega
  have hflag : InvariantLoop.restore work r v (NaturalMachine.flagIndex n) = work (NaturalMachine.flagIndex n) := by
    rw [InvariantLoop.restore, Function.update_of_ne hr.symm]
  have hmaster : InvariantLoop.restore work r v master = work master := by
    rw [InvariantLoop.restore, Function.update_of_ne hrm.symm]
  let RN : (Fin (n + 1) → Tape) → Prop := fun w =>
    w r = ⟨i + 2, regCells v⟩ ∧ R (InvariantLoop.restore w r v)
  have hRN : ∀ w w',
      (∀ j, j ≠ master → j ≠ NaturalMachine.flagIndex n → w' j = w j) → RN w → RN w' := by
    rintro w w' h ⟨hreg, hstate'⟩
    refine ⟨(h r hrm hr).trans hreg, ?_⟩
    apply hR (InvariantLoop.restore w r v) (InvariantLoop.restore w' r v) ?_ hstate'
    intro j hj hjm hjf
    rw [InvariantLoop.restore, Function.update_of_ne hj, InvariantLoop.restore, Function.update_of_ne hj]
    exact h j hjm hjf
  have hpre : Cursor (before ++ (control requirePositive).copied i input)
      ((control requirePositive).tail i input) (emitted ++ (control requirePositive).copied i input) inp work out ∧
      (work (NaturalMachine.flagIndex n)).head = 1 ∧ (work master).head = 1 ∧
      (work master).read = Γ.ofBool (initial && (control requirePositive).accepted i input) ∧ RN work := by
    exact ⟨hphysical, by simpa only [hflag] using hfh, by simpa only [hmaster] using hmh,
      by simpa only [hmaster] using hmr, hf.fuel, hstate⟩
  obtain ⟨d, t, ht, hreach, hhalt, hdcur, hfh', _, hmh', hmr', hfuel, hstate'⟩ :=
    NaturalField.hoareTime requirePositive (initial && (control requirePositive).accepted i input) master hm
      (before ++ (control requirePositive).copied i input) ((control requirePositive).tail i input)
      (emitted ++ (control requirePositive).copied i input) RN hRN inp work out hpre
  have hcur' : Cursor (before ++ (control requirePositive).copied (i + 1) input)
      ((control requirePositive).tail (i + 1) input) (emitted ++ (control requirePositive).copied (i + 1) input)
      d.input d.work d.output := by
    simpa only [FieldControl.Control.copied_succ, FieldControl.Control.tail_succ, taken_eq, rest_eq,
      List.append_assoc] using hdcur
  have hmaster' : (d.work master).read = Γ.ofBool (initial && (control requirePositive).accepted (i + 1) input) := by
    simpa only [FieldControl.Control.accepted_succ, valid_eq, Bool.and_assoc] using hmr'
  have hdf : InvariantLoop.restore d.work r v (NaturalMachine.flagIndex n) = d.work (NaturalMachine.flagIndex n) := by
    rw [InvariantLoop.restore, Function.update_of_ne hr.symm]
  have hdm : InvariantLoop.restore d.work r v master = d.work master := by
    rw [InvariantLoop.restore, Function.update_of_ne hrm.symm]
  have hlen := (control requirePositive).tail_length_le i input
  refine ⟨d, t, by omega, hreach, hhalt, hfuel, hcur'.input_read, fun j _ => (hcur'.works j).1,
    hcur'.output_read, ?_⟩
  exact ⟨LoopCursor.restore hcur' r v, by simpa only [hdf] using hfh',
    by simpa only [hdm] using hmh', by simpa only [hdm] using hmaster', hstate'⟩

def machine (requirePositive : Bool) (r master : Fin (n + 1)) : TM (n + 1) :=
  forRegTM (NaturalField.machine requirePositive master) r

theorem hoareTime (requirePositive initial : Bool) (r master : Fin (n + 1))
    (hr : r ≠ NaturalMachine.flagIndex n) (hm : master ≠ NaturalMachine.flagIndex n) (hrm : r ≠ master)
    (v : ℕ) (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work',
      (∀ j, j ≠ r → j ≠ master → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (machine requirePositive r master).HoareTime
      (fun inp work out => IsReg v (work r) ∧ StateInv requirePositive initial master before input emitted R 0 inp work out)
      (fun inp work out => IsReg v (work r) ∧ StateInv requirePositive initial master before input emitted R v inp work out)
      (v * (input.length + 6) + (v + 2)) := by
  rintro inp work out ⟨hreg, hstate⟩
  have hpre : InvariantLoop.Frame r v 1 (StateInv requirePositive initial master before input emitted R 0) inp work out := by
    refine ⟨hreg.eq_regT, hstate.1.input_read, fun j _ => (hstate.1.works j).1, hstate.1.output_read, ?_⟩
    rw [InvariantLoop.restore_self work r v hreg.eq_regT]
    exact hstate
  have hbody : ∀ i, i < v → (NaturalField.machine requirePositive master).HoareTime
      (InvariantLoop.Frame r v (i + 2) (StateInv requirePositive initial master before input emitted R i))
      (InvariantLoop.Frame r v (i + 2) (StateInv requirePositive initial master before input emitted R (i + 1)))
      (input.length + 4) :=
    fun i _ => body_hoareTime requirePositive initial r master hr hm hrm v i before input emitted R hR
  obtain ⟨d, t, ht, hreach, hhalt, hf⟩ :=
    InvariantLoop.hoareTime (NaturalField.machine requirePositive master) r
      (StateInv requirePositive initial master before input emitted R) (input.length + 4) v hbody inp work out hpre
  exact ⟨d, t, ht, hreach, hhalt, hf.register, hf.on_work⟩

theorem start_iff (requirePositive initial : Bool) (master : Fin (n + 1))
    (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (inp : Tape) (work : Fin (n + 1) → Tape) (out : Tape) :
    StateInv requirePositive initial master before input emitted R 0 inp work out ↔
      Cursor before input emitted inp work out ∧ (work (NaturalMachine.flagIndex n)).head = 1 ∧
      (work master).head = 1 ∧ (work master).read = Γ.ofBool initial ∧ R work := by
  simp [StateInv, FieldControl.Control.copied, FieldControl.Control.tail, FieldControl.Control.accepted]

theorem codec_status_iff (requirePositive initial : Bool) (v : ℕ) (input : List Bool) {value : Γ}
    (h : value = Γ.ofBool (initial && (control requirePositive).accepted v input)) :
    value = Γ.one ↔ initial = true ∧ ∃ f tail, (FiniteCodec.finiteFunction (codec requirePositive) v).parse input = some (f, tail) := by
  have hv : Γ.ofBool (initial && (control requirePositive).accepted v input) = Γ.one ↔
      initial = true ∧ (control requirePositive).accepted v input = true := by
    cases initial <;> cases (control requirePositive).accepted v input <;> simp [Γ.ofBool]
  rw [h, hv, FieldControl.Control.accepted_iff]

theorem time_bound_in_total_length {v L : ℕ} {input : List Bool} (hv : v ≤ L) (hi : input.length ≤ L) :
    v * (input.length + 6) + (v + 2) ≤ L * L + 7 * L + 2 := by
  calc
    v * (input.length + 6) + (v + 2) ≤ L * (L + 6) + (L + 2) :=
      Nat.add_le_add (Nat.mul_le_mul hv (Nat.add_le_add_right hi 6)) (Nat.add_le_add_right hv 2)
    _ = L * L + 7 * L + 2 := by rw [Nat.mul_add]; omega

end JointThermoComplexity.Complexity.NaturalArray

#print axioms JointThermoComplexity.Complexity.NaturalArray.hoareTime
#print axioms JointThermoComplexity.Complexity.NaturalArray.codec_status_iff
