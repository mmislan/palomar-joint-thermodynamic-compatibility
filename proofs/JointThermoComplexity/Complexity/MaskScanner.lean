module
public import proofs.JointThermoComplexity.Complexity.MaskReady
public import proofs.JointThermoComplexity.Complexity.ScannerSpec
public import proofs.JointThermoComplexity.Complexity.LoopCursor

set_option autoImplicit false
@[expose] public section

/-! Finite masks with initialized local status and accumulated global validity. -/

namespace JointThermoComplexity.Complexity.MaskScanner
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ScannerSpec

variable {n : ℕ}

def machine (r master : Fin (n + 1)) : TM (n + 1) :=
  seqTM (MaskReady.machine r) (ValidityAnd.machine master (NaturalMachine.flagIndex n))

theorem runs_booleans (r master : Fin (n + 1))
    (hr : r ≠ NaturalMachine.flagIndex n) (hm : master ≠ NaturalMachine.flagIndex n) (hrm : r ≠ master) (v : ℕ) :
    Runs (RecordControl.booleans v) (machine r master) master (NaturalMachine.flagIndex n)
      (fun work => IsReg v (work r)) (fun _ => 4 * v + 6) := by
  intro initial before input emitted R hR
  let RP : (Fin (n + 1) → Tape) → Prop := fun work =>
    (work master).head = 1 ∧ (work master).read = Γ.ofBool initial ∧ R (InvariantLoop.restore work r v)
  have hRP : ∀ work work',
      (∀ j, j ≠ r → j ≠ NaturalMachine.flagIndex n → work' j = work j) → RP work → RP work' := by
    rintro work work' h ⟨hh, hv, hr'⟩
    have hm' := h master hrm.symm hm
    refine ⟨by simpa only [hm'] using hh, by simpa only [hm'] using hv, ?_⟩
    apply hR (InvariantLoop.restore work r v) (InvariantLoop.restore work' r v) ?_ hr'
    intro j hjm hjf
    by_cases hj : j = r
    · subst j
      simp only [InvariantLoop.restore, Function.update_self]
    · rw [InvariantLoop.restore, Function.update_of_ne hj, InvariantLoop.restore, Function.update_of_ne hj]
      exact h j hj hjf
  have hmask : (MaskReady.machine r).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work (NaturalMachine.flagIndex n)).head = 1 ∧ (work master).head = 1 ∧
        (work master).read = Γ.ofBool initial ∧ IsReg v (work r) ∧ R work)
      (fun inp work out => Cursor (before ++ input.take v) (input.drop v) (emitted ++ input.take v) inp work out ∧
        (work (NaturalMachine.flagIndex n)).head = 1 ∧
        (work (NaturalMachine.flagIndex n)).read = Γ.ofBool (BooleanVector.accepted v input) ∧
        (work master).head = 1 ∧ (work master).read = Γ.ofBool initial ∧ IsReg v (work r) ∧ R work)
      (4 * v + 4) := by
    rintro inp work out ⟨hc, hf, hmh, hmr, hreg, hstate⟩
    have hp : RP work := by
      refine ⟨hmh, hmr, ?_⟩
      simpa only [InvariantLoop.restore_self work r v hreg.eq_regT] using hstate
    obtain ⟨d, t, ht, hreach, hhalt, hreg', hcur, hf', hv', hmh', hmr', hstate'⟩ :=
      MaskReady.hoareTime r hr v before input emitted RP hRP inp work out ⟨hc, hf, hreg, hp⟩
    have hfinal : R d.work := by
      simpa only [InvariantLoop.restore_self d.work r v hreg'.eq_regT] using hstate'
    exact ⟨d, t, ht, hreach, hhalt, hcur, hf', hv', hmh', hmr', hreg', hfinal⟩
  let RA : (Fin (n + 1) → Tape) → Prop := fun work =>
    (work (NaturalMachine.flagIndex n)).head = 1 ∧ IsReg v (work r) ∧ R work
  have hRA : ∀ work work', (∀ j, j ≠ master → work' j = work j) → RA work → RA work' := by
    rintro work work' h ⟨hf, hreg, hstate⟩
    refine ⟨?_, ?_, hR work work' (fun j hj _ => h j hj) hstate⟩
    · simpa only [h (NaturalMachine.flagIndex n) hm.symm] using hf
    · simpa only [h r hrm] using hreg
  have hand := AndCursor.hoareTime master (NaturalMachine.flagIndex n) initial (BooleanVector.accepted v input)
    (before ++ input.take v) (input.drop v) (emitted ++ input.take v) RA hRA
  have hseq := seqTM_hoareTime (MaskReady.machine r) (ValidityAnd.machine master (NaturalMachine.flagIndex n))
    hmask (by
      rintro inp work out ⟨hc, hf, hv, hmh, hmr, hreg, hstate⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hmh, hmr, hv, hf, hreg, hstate⟩) hand
  apply HoareTime.strengthen_post hseq
  rintro inp work out ⟨hc, hmh, hmr, hf, hreg, hstate⟩
  exact ⟨hc, hf, hmh, hmr, hreg, hstate⟩

theorem runs_finset (r master : Fin (n + 1))
    (hr : r ≠ NaturalMachine.flagIndex n) (hm : master ≠ NaturalMachine.flagIndex n) (hrm : r ≠ master) (v : ℕ) :
    Runs (RecordControl.finset v) (machine r master) master (NaturalMachine.flagIndex n)
      (fun work => IsReg v (work r)) (fun _ => 4 * v + 6) :=
  transport_runs (DataCodec.finsetEquiv v) (runs_booleans r master hr hm hrm v)

end JointThermoComplexity.Complexity.MaskScanner

#print axioms JointThermoComplexity.Complexity.MaskScanner.runs_booleans
#print axioms JointThermoComplexity.Complexity.MaskScanner.runs_finset
