module
public import proofs.JointThermoComplexity.Complexity.ScannerSpec
public import proofs.JointThermoComplexity.Complexity.LoopCursor

set_option autoImplicit false
@[expose] public section

/-! Finite arrays of supplied, proved concrete scanners, with a restored fuel tape. -/

namespace JointThermoComplexity.Complexity.ScannerArray
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ScannerSpec FiniteCodec FieldControl

variable {w : ℕ} {α : Type} {A : Codec α}

def StateInv (S : Control A) (initial : Bool) (master flag : Fin w)
    (Env R : (Fin w → Tape) → Prop) (before input emitted : List Bool)
    (i : ℕ) : _root_.Complexity.TM.TapePred w := fun inp work out =>
  Cursor (before ++ S.copied i input) (S.tail i input) (emitted ++ S.copied i input) inp work out ∧
    (work flag).head = 1 ∧ (work master).head = 1 ∧
    (work master).read = Γ.ofBool (initial && S.accepted i input) ∧ Env work ∧ R work

theorem body_hoareTime {S : Control A} {tm : TM w} {master flag : Fin w}
    {Env : (Fin w → Tape) → Prop} {T : ℕ → ℕ}
    (hscan : Runs S tm master flag Env T) (hmono : Monotone T)
    (r : Fin w) (hr : r ≠ flag) (hrm : r ≠ master)
    (hEnv : ∀ (work work' : Fin w → Tape), (∀ j, j ≠ r → work' j = work j) → Env work → Env work')
    (initial : Bool) (v i : ℕ) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ r → j ≠ master → j ≠ flag → work' j = work j) → R work → R work') :
    tm.HoareTime (InvariantLoop.Frame r v (i + 2) (StateInv S initial master flag Env R before input emitted i))
      (InvariantLoop.Frame r v (i + 2) (StateInv S initial master flag Env R before input emitted (i + 1)))
      (T input.length) := by
  intro inp work out hf
  rcases hf.invariant with ⟨hc, hfh, hmh, hmr, he, hstate⟩
  have hphysical : Cursor (before ++ S.copied i input) (S.tail i input)
      (emitted ++ S.copied i input) inp work out := by
    apply LoopCursor.physical r v hc
    rw [hf.fuel]
    refine ⟨?_, ?_⟩
    · change regCells v (i + 2) ≠ Γ.start
      exact regCells_ne_start (by omega)
    · change 1 ≤ i + 2
      omega
  have hflag : InvariantLoop.restore work r v flag = work flag := by
    rw [InvariantLoop.restore, Function.update_of_ne hr.symm]
  have hmaster : InvariantLoop.restore work r v master = work master := by
    rw [InvariantLoop.restore, Function.update_of_ne hrm.symm]
  have hephysical : Env work := hEnv (InvariantLoop.restore work r v) work (by
    intro j hj
    rw [InvariantLoop.restore, Function.update_of_ne hj]) he
  let RN : (Fin w → Tape) → Prop := fun work => work r = ⟨i + 2, regCells v⟩ ∧ R (InvariantLoop.restore work r v)
  have hRN : ∀ work work', (∀ j, j ≠ master → j ≠ flag → work' j = work j) → RN work → RN work' := by
    rintro work work' h ⟨hreg, hstate'⟩
    refine ⟨(h r hrm hr).trans hreg, ?_⟩
    apply hR (InvariantLoop.restore work r v) (InvariantLoop.restore work' r v) ?_ hstate'
    intro j hj hjm hjf
    rw [InvariantLoop.restore, Function.update_of_ne hj, InvariantLoop.restore, Function.update_of_ne hj]
    exact h j hjm hjf
  have hpre : Cursor (before ++ S.copied i input) (S.tail i input) (emitted ++ S.copied i input) inp work out ∧
      (work flag).head = 1 ∧ (work master).head = 1 ∧
      (work master).read = Γ.ofBool (initial && S.accepted i input) ∧ Env work ∧ RN work := by
    exact ⟨hphysical, by simpa only [hflag] using hfh, by simpa only [hmaster] using hmh,
      by simpa only [hmaster] using hmr, hephysical, hf.fuel, hstate⟩
  obtain ⟨d, t, ht, hreach, hhalt, hdcur, hfh', hmh', hmr', he', hfuel, hstate'⟩ :=
    hscan (initial && S.accepted i input) (before ++ S.copied i input) (S.tail i input)
      (emitted ++ S.copied i input) RN hRN inp work out hpre
  have hcur' : Cursor (before ++ S.copied (i + 1) input) (S.tail (i + 1) input)
      (emitted ++ S.copied (i + 1) input) d.input d.work d.output := by
    simpa only [Control.copied_succ, Control.tail_succ, List.append_assoc] using hdcur
  have hmaster' : (d.work master).read = Γ.ofBool (initial && S.accepted (i + 1) input) := by
    simpa only [Control.accepted_succ, Bool.and_assoc] using hmr'
  have hdf : InvariantLoop.restore d.work r v flag = d.work flag := by
    rw [InvariantLoop.restore, Function.update_of_ne hr.symm]
  have hdm : InvariantLoop.restore d.work r v master = d.work master := by
    rw [InvariantLoop.restore, Function.update_of_ne hrm.symm]
  have henorm : Env (InvariantLoop.restore d.work r v) := hEnv d.work (InvariantLoop.restore d.work r v) (by
    intro j hj
    rw [InvariantLoop.restore, Function.update_of_ne hj]) he'
  have htime : t ≤ T input.length := ht.trans (hmono (S.tail_length_le i input))
  refine ⟨d, t, htime, hreach, hhalt, hfuel, hcur'.input_read, fun j _ => (hcur'.works j).1,
    hcur'.output_read, ?_⟩
  exact ⟨LoopCursor.restore hcur' r v, by simpa only [hdf] using hfh',
    by simpa only [hdm] using hmh', by simpa only [hdm] using hmaster', henorm, hstate'⟩

theorem hoareTime {S : Control A} {tm : TM w} {master flag : Fin w}
    {Env : (Fin w → Tape) → Prop} {T : ℕ → ℕ}
    (hscan : Runs S tm master flag Env T) (hmono : Monotone T)
    (r : Fin w) (hr : r ≠ flag) (hrm : r ≠ master)
    (hEnv : ∀ (work work' : Fin w → Tape), (∀ j, j ≠ r → work' j = work j) → Env work → Env work')
    (initial : Bool) (v : ℕ) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ r → j ≠ master → j ≠ flag → work' j = work j) → R work → R work') :
    (forRegTM tm r).HoareTime
      (fun inp work out => IsReg v (work r) ∧ StateInv S initial master flag Env R before input emitted 0 inp work out)
      (fun inp work out => IsReg v (work r) ∧ StateInv S initial master flag Env R before input emitted v inp work out)
      (v * (T input.length + 2) + (v + 2)) := by
  rintro inp work out ⟨hreg, hstate⟩
  have hpre : InvariantLoop.Frame r v 1 (StateInv S initial master flag Env R before input emitted 0) inp work out := by
    refine ⟨hreg.eq_regT, hstate.1.input_read, fun j _ => (hstate.1.works j).1, hstate.1.output_read, ?_⟩
    rw [InvariantLoop.restore_self work r v hreg.eq_regT]
    exact hstate
  have hbody : ∀ i, i < v → tm.HoareTime
      (InvariantLoop.Frame r v (i + 2) (StateInv S initial master flag Env R before input emitted i))
      (InvariantLoop.Frame r v (i + 2) (StateInv S initial master flag Env R before input emitted (i + 1))) (T input.length) :=
    fun i _ => body_hoareTime hscan hmono r hr hrm hEnv initial v i before input emitted R hR
  obtain ⟨d, t, ht, hreach, hhalt, hf⟩ := InvariantLoop.hoareTime tm r
    (StateInv S initial master flag Env R before input emitted) (T input.length) v hbody inp work out hpre
  exact ⟨d, t, ht, hreach, hhalt, hf.register, hf.on_work⟩

theorem runs_array {S : Control A} {tm : TM w} {master flag : Fin w}
    {Env : (Fin w → Tape) → Prop} {T : ℕ → ℕ}
    (hscan : Runs S tm master flag Env T) (hmono : Monotone T)
    (r : Fin w) (hr : r ≠ flag) (hrm : r ≠ master)
    (hEnv : ∀ (work work' : Fin w → Tape), (∀ j, j ≠ r → work' j = work j) → Env work → Env work')
    (v : ℕ) :
    Runs (RecordControl.array S v) (forRegTM tm r) master flag
      (fun work => Env work ∧ IsReg v (work r)) (fun L => v * (T L + 2) + (v + 2)) := by
  intro initial before input emitted R hR inp work out hpre
  rcases hpre with ⟨hc, hf, hmh, hmr, ⟨he, hreg⟩, hstate⟩
  let RN : (Fin w → Tape) → Prop := fun work => R (InvariantLoop.restore work r v)
  have hRN : ∀ work work', (∀ j, j ≠ r → j ≠ master → j ≠ flag → work' j = work j) → RN work → RN work' := by
    intro work work' h hr'
    apply hR (InvariantLoop.restore work r v) (InvariantLoop.restore work' r v) ?_ hr'
    intro j hjm hjf
    by_cases hj : j = r
    · subst j
      simp only [InvariantLoop.restore, Function.update_self]
    · rw [InvariantLoop.restore, Function.update_of_ne hj, InvariantLoop.restore, Function.update_of_ne hj]
      exact h j hj hjm hjf
  have hstate₀ : StateInv S initial master flag Env RN before input emitted 0 inp work out := by
    have hrn : RN work := by simpa only [RN, InvariantLoop.restore_self work r v hreg.eq_regT] using hstate
    simpa [StateInv, Control.copied, Control.tail, Control.accepted] using
      (show Cursor before input emitted inp work out ∧ (work flag).head = 1 ∧ (work master).head = 1 ∧
        (work master).read = Γ.ofBool initial ∧ Env work ∧ RN work from ⟨hc, hf, hmh, hmr, he, hrn⟩)
  obtain ⟨d, t, ht, hreach, hhalt, hreg', hcur, hf', hmh', hmr', he', hstate'⟩ :=
    hoareTime hscan hmono r hr hrm hEnv initial v before input emitted RN hRN inp work out ⟨hreg, hstate₀⟩
  have hfinal : R d.work := by
    simpa only [RN, InvariantLoop.restore_self d.work r v hreg'.eq_regT] using hstate'
  exact ⟨d, t, ht, hreach, hhalt, hcur, hf', hmh', hmr', ⟨he', hreg'⟩, hfinal⟩

end JointThermoComplexity.Complexity.ScannerArray

#print axioms JointThermoComplexity.Complexity.ScannerArray.runs_array
