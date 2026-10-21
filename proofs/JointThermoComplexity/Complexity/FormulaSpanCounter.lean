module
public import proofs.JointThermoComplexity.Complexity.FormulaSpanRegisters
public import proofs.JointThermoComplexity.Complexity.SourceTermCountReset

set_option autoImplicit false
@[expose] public section

/-! Formula-pending and coordinate-allocation operations preserve the combined traversal frame. -/

namespace JointThermoComplexity.Complexity.FormulaSpanCounter
open _root_.Complexity _root_.Complexity.TM FormulaSpanRegisters
open HeaderAt (Cursor)
variable {n : ℕ}

theorem formula_frame (tm : TM (n + 8)) (old count terms coordinates bound : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R)
    (h : ∀ C : (Fin (n + 8) → Tape) → Prop,
      (∀ work work', (∀ j, j ≠ formulaPending n → work' j = work j) → C work → C work') →
      tm.HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg old (work (formulaPending n)) ∧ C work)
        (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg count (work (formulaPending n)) ∧ C work) bound) :
    tm.HoareTime (Inv emitted R ⟨before, input, terms, old, coordinates⟩)
      (Inv emitted R ⟨before, input, terms, count, coordinates⟩) bound := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin (n + 8) → Tape) → Prop := fun work' => ∀ j, j ≠ formulaPending n → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ formulaPending n → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj
    exact (he j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hd, hh, hc', hs', hfp, hother⟩ := h C hC inp work out ⟨hc, hr.safe, hr.frame.1, fun _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  have htp : IsReg terms (d.work (TermSpanRegisters.pending (n + 1))) := by
    rw [hother _ (formulaPending_outside n).1.symm]
    exact hr.counter
  have hnode : IsReg coordinates (d.work (TermSpanRegisters.nodeCounter (n + 1))) := by
    rw [hother _ (formulaPending_outside n).2.1.symm]
    exact hr.nodeReg
  have htags : ∀ i, (d.work (TermSpanRegisters.tags (n + 1) i)).head = 1 := fun i => by
    rw [hother _ ((formulaPending_outside n).2.2.2 i).symm]
    exact hr.tagHeads i
  have hflag : (d.work (TermSpanRegisters.flag (n + 1))).head = 1 := by
    rw [hother _ (formulaPending_outside n).2.2.1.symm]
    exact hr.flagHead
  have hr' : R d.work := hR work d.work (fun j hj => hother j hj.2) hr.frame.2
  exact ⟨d, t, ht, hd, hh, hc', hs', (fun j => (hm.2.1 j).1), htp, hnode, htags, hflag, hfp, hr'⟩

def formulaMachine (n : ℕ) (up : Bool) : TM (n + 8) :=
  if up then UnarySuccessor.machine (formulaPending n) else UnaryPredecessor.machine (formulaPending n)
def nextFormula (up : Bool) (v : ℕ) : ℕ := if up then v + 2 else v

theorem formula_hoareTime (up : Bool) (v terms coordinates : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R) :
    (formulaMachine n up).HoareTime (Inv emitted R ⟨before, input, terms, v + 1, coordinates⟩)
      (Inv emitted R ⟨before, input, terms, nextFormula up v, coordinates⟩) (2 * v + 12) := by
  apply formula_frame _ (v + 1) (nextFormula up v) terms coordinates _ before input emitted R hR
  intro C hC
  cases up with
  | false => simpa only [formulaMachine, nextFormula, Bool.false_eq_true, ↓reduceIte] using
      UnaryPredecessor.hoareTime (formulaPending n) v before input emitted C hC
  | true =>
    have h := UnarySuccessor.hoareTime (formulaPending n) (v + 1) before input emitted C hC
    simpa only [formulaMachine, nextFormula, ↓reduceIte, Nat.add_assoc] using
      h.mono_bound (by omega : 2 * (v + 1) + 6 ≤ 2 * v + 12)

theorem pending_two_hoareTime (formulas coordinates : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R) :
    (SourceTermCountReset.machine (TermSpanRegisters.pending (n + 1))).HoareTime
      (Inv emitted R ⟨before, input, 0, formulas, coordinates⟩)
      (Inv emitted R ⟨before, input, 2, formulas, coordinates⟩) 21 :=
  TermSpanCounter.pending_frame _ 0 2 coordinates 21 before input emitted (Frame formulas R) (frame_stable formulas R hR)
    (fun C hC => SourceTermCountReset.hoareTime (TermSpanRegisters.pending (n + 1)) 0 before input emitted C hC)

def incrementMachine (n : ℕ) : TM (n + 8) := UnarySuccessor.machine (TermSpanRegisters.nodeCounter (n + 1))

theorem increment_hoareTime (emitted : List Bool) (R : (Fin (n + 8) → Tape) → Prop)
    (hR : Stable R) (s : FormulaSpanControl.State) :
    (incrementMachine n).HoareTime (Inv emitted R s)
      (Inv emitted R {s with coordinates := s.coordinates + 1}) (2 * s.coordinates + 6) :=
  TermSpanCounter.increment_hoareTime emitted (Frame s.formulas R) (frame_stable s.formulas R hR) (FormulaSpanControl.termState s)

def fourMachine (n : ℕ) : TM (n + 8) :=
  seqTM (incrementMachine n) (seqTM (incrementMachine n) (seqTM (incrementMachine n) (incrementMachine n)))

theorem four_hoareTime (emitted : List Bool) (R : (Fin (n + 8) → Tape) → Prop)
    (hR : Stable R) (s : FormulaSpanControl.State) :
    (fourMachine n).HoareTime (Inv emitted R s)
      (Inv emitted R {s with coordinates := s.coordinates + 4}) (8 * s.coordinates + 39) := by
  have h1 := increment_hoareTime emitted R hR s
  have h2 := increment_hoareTime emitted R hR ⟨s.before, s.input, s.terms, s.formulas, s.coordinates + 1⟩
  have h3 := increment_hoareTime emitted R hR ⟨s.before, s.input, s.terms, s.formulas, s.coordinates + 2⟩
  have h4 := increment_hoareTime emitted R hR ⟨s.before, s.input, s.terms, s.formulas, s.coordinates + 3⟩
  have h34 := seq_inv_hoareTime _ _ emitted R _ _ _ _ _ h3 h4
  have h234 := seq_inv_hoareTime _ _ emitted R _ _ _ _ _ h2 h34
  have h := seq_inv_hoareTime _ _ emitted R _ _ _ _ _ h1 h234
  exact h.mono_bound (by
    change 2 * s.coordinates + 6 + 1 + (2 * (s.coordinates + 1) + 6 + 1 +
      (2 * (s.coordinates + 2) + 6 + 1 + (2 * (s.coordinates + 3) + 6))) ≤ 8 * s.coordinates + 39
    omega)

end JointThermoComplexity.Complexity.FormulaSpanCounter

#print axioms JointThermoComplexity.Complexity.FormulaSpanCounter.formula_hoareTime
#print axioms JointThermoComplexity.Complexity.FormulaSpanCounter.pending_two_hoareTime
#print axioms JointThermoComplexity.Complexity.FormulaSpanCounter.four_hoareTime
