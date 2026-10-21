module
public import proofs.JointThermoComplexity.Complexity.InputBitSkip
public import proofs.JointThermoComplexity.Complexity.LoopCursor

set_option autoImplicit false
@[expose] public section

/-! Counted input seeking restores the physical fuel register and preserves work frames. -/

namespace JointThermoComplexity.Complexity.InputSeek
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def machine (idx : Fin w) : TM w := forRegTM (InputBitSkip.machine (w := w)) idx

def invariant (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (i : ℕ) : _root_.Complexity.TM.TapePred w := fun inp work out =>
  Cursor (before ++ input.take i) (input.drop i) emitted inp work out ∧ R work

theorem body_hoareTime (idx : Fin w) (v i : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (InputBitSkip.machine (w := w)).HoareTime
      (InvariantLoop.Frame idx v (i + 2) (invariant before input emitted R i))
      (InvariantLoop.Frame idx v (i + 2) (invariant before input emitted R (i + 1))) 1 := by
  intro inp work out hf
  have hcur : Cursor (before ++ input.take i) (input.drop i) emitted inp work out :=
    LoopCursor.physical idx v hf.invariant.1 ⟨by rw [hf.fuel]; change regCells v (i + 2) ≠ Γ.start; exact regCells_ne_start (by omega),
      by rw [hf.fuel]; change 1 ≤ i + 2; omega⟩
  obtain ⟨d, t, ht, hd, hh, hc', heq⟩ :=
    InputBitSkip.hoareTime (before ++ input.take i) (input.drop i) emitted (fun work' _ => work' = work)
      inp work out ⟨hcur, rfl⟩
  have hprefix : (before ++ input.take i) ++ (input.drop i).take 1 = before ++ input.take (i + 1) := by
    rw [List.take_add]
    exact List.append_assoc _ _ _
  have hrest : (input.drop i).drop 1 = input.drop (i + 1) := by rw [List.drop_drop]
  rw [hprefix, hrest] at hc'
  refine ⟨d, t, ht, hd, hh, ?_, hc'.input_read, fun j _ => (hc'.works j).1, hc'.output_read, ?_⟩
  · rw [heq]
    exact hf.fuel
  · exact ⟨LoopCursor.restore hc' idx v, by simpa only [heq] using hf.invariant.2⟩

theorem hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ IsReg v (work idx) ∧ R work)
      (fun inp work out => Cursor (before ++ input.take v) (input.drop v) emitted inp work out ∧
        IsReg v (work idx) ∧ R work) (4 * v + 2) := by
  have hloop := InvariantLoop.hoareTime (InputBitSkip.machine (w := w)) idx
    (invariant before input emitted R) 1 v
    (fun i _ => body_hoareTime idx v i before input emitted R)
  apply hloop.consequence
  · rintro inp work out ⟨hc, hv, hr⟩
    refine ⟨hv.eq_regT, hc.input_read, fun j _ => (hc.works j).1, hc.output_read, ?_⟩
    have hc' := LoopCursor.restore hc idx v
    have hr' := hR work (InvariantLoop.restore work idx v)
      (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj]) hr
    exact ⟨by simpa only [List.take_zero, List.drop_zero, List.append_nil] using hc', hr'⟩
  · intro inp work out hf
    exact ⟨hf.on_work.1, hf.register, hf.on_work.2⟩
  · omega

theorem exact_hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ IsReg v (work idx) ∧ R work)
      (fun inp work out => Cursor (before ++ input.take v) (input.drop v) emitted inp work out ∧
        IsReg v (work idx) ∧ R work) (4 * v + 2) := by
  rintro inp work out ⟨hc, hv, hr⟩
  let S : (Fin w → Tape) → Prop := fun work' => ∀ j, j ≠ idx → work' j = work j
  have hS : ∀ work' work'', (∀ j, j ≠ idx → work'' j = work' j) → S work' → S work'' := by
    intro work' work'' h h' j hj
    exact (h j hj).trans (h' j hj)
  obtain ⟨d, t, ht, hd, hh, hc', hv', hs⟩ := hoareTime idx v before input emitted S hS
    inp work out ⟨hc, hv, fun _ _ => rfl⟩
  have heq : d.work = work := by
    funext j
    by_cases hj : j = idx
    · subst j
      exact hv'.eq_regT.trans hv.eq_regT.symm
    · exact hs j hj
  exact ⟨d, t, ht, hd, hh, hc', hv', by simpa only [heq] using hr⟩

theorem restore_hoareTime (idx : Fin w) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor [] (before ++ input) emitted inp work out ∧
        IsReg before.length (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧
        IsReg before.length (work idx) ∧ R work) (4 * before.length + 2) := by
  simpa only [List.nil_append, List.take_left, List.drop_left] using
    hoareTime idx before.length [] (before ++ input) emitted R hR

theorem restore_exact_hoareTime (idx : Fin w) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine idx).HoareTime
      (fun inp work out => Cursor [] (before ++ input) emitted inp work out ∧
        IsReg before.length (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧
        IsReg before.length (work idx) ∧ R work) (4 * before.length + 2) := by
  simpa only [List.nil_append, List.take_left, List.drop_left] using
    exact_hoareTime idx before.length [] (before ++ input) emitted R

end JointThermoComplexity.Complexity.InputSeek

#print axioms JointThermoComplexity.Complexity.InputSeek.hoareTime
#print axioms JointThermoComplexity.Complexity.InputSeek.restore_hoareTime
#print axioms JointThermoComplexity.Complexity.InputSeek.restore_exact_hoareTime
