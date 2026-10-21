module
public import proofs.JointThermoComplexity.Complexity.BooleanVector
public import proofs.JointThermoComplexity.Complexity.InvariantLoop
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-!
# Uniform finite-mask parser

The loop uses the declared dimension's unary register as fuel. The Boolean
scanner copies at most that many bits and returns exact finite-function codec
status, including zero-length masks and truncated input. Other retained state
is threaded through an arbitrary frame predicate.
-/

namespace JointThermoComplexity.Complexity.BooleanMask
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {n : ℕ}

def StateInv (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (i : ℕ) : _root_.Complexity.TM.TapePred (n + 1) := fun inp work out =>
  Cursor (before ++ input.take i) (input.drop i) (emitted ++ input.take i) inp work out ∧
    (work (NaturalMachine.flagIndex n)).head = 1 ∧
    (work (NaturalMachine.flagIndex n)).read = Γ.ofBool (BooleanVector.accepted i input) ∧ R work

theorem body_hoareTime (r : Fin (n + 1)) (hr : r ≠ NaturalMachine.flagIndex n)
    (v i : ℕ) (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ r → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (BooleanMachine.machine n).HoareTime
      (InvariantLoop.Frame r v (i + 2) (StateInv before input emitted R i))
      (InvariantLoop.Frame r v (i + 2) (StateInv before input emitted R (i + 1))) 1 := by
  intro inp work out hf
  rcases hf.invariant with ⟨hc, hh, _, hstate⟩
  have hflag₀ : InvariantLoop.restore work r v (NaturalMachine.flagIndex n) = work (NaturalMachine.flagIndex n) := by
    rw [InvariantLoop.restore, Function.update_of_ne hr.symm]
  have hh' : (work (NaturalMachine.flagIndex n)).head = 1 := by simpa only [hflag₀] using hh
  have hw : ∀ j, (work j).read ≠ Γ.start := by
    intro j
    by_cases hj : j = r
    · subst j
      rw [hf.fuel]
      change regCells v (i + 2) ≠ Γ.start
      exact regCells_ne_start (by omega)
    · exact hf.readOthers j hj
  obtain ⟨d, hreach, hhalt, hcells, hhead, hother, hfh, hfr, hz, hp⟩ :=
    BooleanMachine.run_from_cursor (before ++ input.take i) (emitted ++ input.take i) (input.drop i)
      ⟨false, inp, work, out⟩ rfl hc.cells hc.head hw hh' hc.tapePrefix hc.zero
  have hfuel : d.work r = ⟨i + 2, regCells v⟩ := (hother r hr).trans hf.fuel
  have hflag : InvariantLoop.restore d.work r v (NaturalMachine.flagIndex n) = d.work (NaturalMachine.flagIndex n) := by
    rw [InvariantLoop.restore, Function.update_of_ne hr.symm]
  have hothers : ∀ j, j ≠ r → (d.work j).read ≠ Γ.start := by
    intro j hj
    by_cases hstatus : j = NaturalMachine.flagIndex n
    · subst j
      rw [hfr]
      exact Γ.ofBool_ne_start _
    · rw [hother j hstatus]
      exact hf.readOthers j hj
  have hcursor : Cursor (before ++ input.take (i + 1)) (input.drop (i + 1))
      (emitted ++ input.take (i + 1)) d.input (InvariantLoop.restore d.work r v) d.output := by
    refine ⟨?_, ?_, ?_, ?_, hz⟩
    · simpa only [List.append_assoc, List.take_append_drop] using hcells.trans hc.cells
    · simpa only [← BooleanVector.copied_step input i, List.length_append, Nat.add_assoc] using hhead
    · intro j
      by_cases hj : j = r
      · subst j
        rw [InvariantLoop.restore, Function.update_self]
        exact ⟨(reg_regT v).parked.read_ne_start, (reg_regT v).parked.1⟩
      · rw [InvariantLoop.restore, Function.update_of_ne hj]
        refine ⟨hothers j hj, ?_⟩
        by_cases hstatus : j = NaturalMachine.flagIndex n
        · subst j
          rw [hfh]
        · rw [hother j hstatus]
          have hprev := (hc.works j).2
          rw [InvariantLoop.restore, Function.update_of_ne hj] at hprev
          exact hprev
    · simpa only [List.append_assoc, BooleanVector.copied_step] using hp
  have hframe : ∀ j, j ≠ r → j ≠ NaturalMachine.flagIndex n →
      InvariantLoop.restore d.work r v j = InvariantLoop.restore work r v j := by
    intro j hj hstatus
    rw [InvariantLoop.restore, Function.update_of_ne hj, InvariantLoop.restore, Function.update_of_ne hj]
    exact hother j hstatus
  have hstate' := hR (InvariantLoop.restore work r v) (InvariantLoop.restore d.work r v) hframe hstate
  refine ⟨d, 1, le_rfl, hreach, hhalt, hfuel, hcursor.input_read, hothers, hcursor.output_read, ?_⟩
  exact ⟨hcursor, by simpa only [hflag] using hfh,
    by simpa only [hflag, BooleanVector.accepted_step] using hfr, hstate'⟩

def machine (r : Fin (n + 1)) : TM (n + 1) := forRegTM (BooleanMachine.machine n) r

theorem hoareTime (r : Fin (n + 1)) (hr : r ≠ NaturalMachine.flagIndex n)
    (v : ℕ) (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ r → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (machine r).HoareTime
      (fun inp work out => IsReg v (work r) ∧ StateInv before input emitted R 0 inp work out)
      (fun inp work out => IsReg v (work r) ∧ StateInv before input emitted R v inp work out)
      (4 * v + 2) := by
  rintro inp work out ⟨hreg, hstate⟩
  have hpre : InvariantLoop.Frame r v 1 (StateInv before input emitted R 0) inp work out := by
    refine ⟨hreg.eq_regT, hstate.1.input_read, fun j _ => (hstate.1.works j).1, hstate.1.output_read, ?_⟩
    rw [InvariantLoop.restore_self work r v hreg.eq_regT]
    exact hstate
  have hbody : ∀ i, i < v → (BooleanMachine.machine n).HoareTime
      (InvariantLoop.Frame r v (i + 2) (StateInv before input emitted R i))
      (InvariantLoop.Frame r v (i + 2) (StateInv before input emitted R (i + 1))) 1 :=
    fun i _ => body_hoareTime r hr v i before input emitted R hR
  obtain ⟨d, t, ht, hreach, hhalt, hf⟩ :=
    InvariantLoop.hoareTime (BooleanMachine.machine n) r (StateInv before input emitted R) 1 v hbody inp work out hpre
  exact ⟨d, t, by omega, hreach, hhalt, hf.register, hf.on_work⟩

theorem codec_status_iff (v : ℕ) (input : List Bool) {value : Γ}
    (h : value = Γ.ofBool (BooleanVector.accepted v input)) :
    value = Γ.one ↔ ∃ f tail, (FiniteCodec.finiteFunction FiniteCodec.boolean v).parse input = some (f, tail) := by
  rw [h, ← BooleanVector.status_iff]
  cases BooleanVector.accepted v input <;> simp [Γ.ofBool]

end JointThermoComplexity.Complexity.BooleanMask

#print axioms JointThermoComplexity.Complexity.BooleanMask.body_hoareTime
#print axioms JointThermoComplexity.Complexity.BooleanMask.hoareTime
#print axioms JointThermoComplexity.Complexity.BooleanMask.codec_status_iff
