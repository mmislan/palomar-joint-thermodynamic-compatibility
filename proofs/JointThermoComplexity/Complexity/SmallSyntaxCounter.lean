module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxRegisters

set_option autoImplicit false
@[expose] public section

/-! Pending-term counter operations preserve the six-tape streaming frame, including displaced outer fuel. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxCounter
open _root_.Complexity _root_.Complexity.TM HeaderAt SmallSyntaxRegisters

theorem frame_hoareTime (tm : TM 6) (old count bound : ℕ) (before input emitted : List Bool)
    (R : (Fin 6 → Tape) → Prop) (hR : Stable R)
    (h : ∀ C : (Fin 6 → Tape) → Prop,
      (∀ work work', (∀ j, j ≠ pending → work' j = work j) → C work → C work') →
      tm.HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg old (work pending) ∧ C work)
        (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg count (work pending) ∧ C work) bound) :
    tm.HoareTime (Inv R ⟨before, input, emitted, old⟩) (Inv R ⟨before, input, emitted, count⟩) bound := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin 6 → Tape) → Prop := fun work' => ∀ j, j ≠ pending → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ pending → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj
    exact (he j hj).trans (hp j hj)
  obtain ⟨c, t, ht, hd, hh, hc', hs', hp, hother⟩ := h C hC inp work out ⟨hc, hr.safe, hr.counter, fun _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  have htags : ∀ i, (c.work (tags i)).head = 1 :=
    fun i => by simpa only [hother (tags i) (tags_pending i)] using hr.tagHeads i
  have hflag : (c.work flag).head = 1 := by simpa only [hother flag (by decide)] using hr.flagHead
  have hr' := reframe old count R hR work c.work hr (hother fuel (by decide)) hs'
    (fun j => (hm.2.1 j).1) hp htags hflag
  exact ⟨c, t, ht, hd, hh, hc', hr'⟩

def move (up : Bool) : TM 6 := if up then UnarySuccessor.machine pending else UnaryPredecessor.machine pending
def nextCount (up : Bool) (v : ℕ) : ℕ := if up then v + 2 else v

theorem move_hoareTime (up : Bool) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    (move up).HoareTime (Inv R ⟨before, input, emitted, v + 1⟩)
      (Inv R ⟨before, input, emitted, nextCount up v⟩) (2 * v + 12) := by
  apply frame_hoareTime _ (v + 1) (nextCount up v) (2 * v + 12) before input emitted R hR
  intro C hC
  cases up with
  | false => simpa only [move, nextCount, Bool.false_eq_true, ↓reduceIte] using
      UnaryPredecessor.hoareTime pending v before input emitted C hC
  | true =>
    have h := UnarySuccessor.hoareTime pending (v + 1) before input emitted C hC
    simpa only [move, nextCount, ↓reduceIte, Nat.add_assoc] using h.mono_bound (by omega : 2 * (v + 1) + 6 ≤ 2 * v + 12)

theorem reset_two_hoareTime (old : ℕ) (before input emitted : List Bool)
    (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    (SourceTermCountReset.machine pending).HoareTime (Inv R ⟨before, input, emitted, old⟩)
      (Inv R ⟨before, input, emitted, 2⟩) (2 * old + 21) := by
  exact frame_hoareTime _ old 2 (2 * old + 21) before input emitted R hR
    (fun C hC => SourceTermCountReset.hoareTime pending old before input emitted C hC)

theorem clear_hoareTime (old : ℕ) (before input emitted : List Bool)
    (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    (clearWorkTM pending).HoareTime (Inv R ⟨before, input, emitted, old⟩)
      (Inv R ⟨before, input, emitted, 0⟩) (2 * old + 5) := by
  exact frame_hoareTime _ old 0 (2 * old + 5) before input emitted R hR
    (fun C hC => UnaryReset.hoareTime pending old before input emitted C hC)

end JointThermoComplexity.Complexity.SmallSyntaxCounter

#print axioms JointThermoComplexity.Complexity.SmallSyntaxCounter.move_hoareTime
#print axioms JointThermoComplexity.Complexity.SmallSyntaxCounter.reset_two_hoareTime
