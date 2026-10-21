module
public import proofs.JointThermoComplexity.Complexity.TermSpanRegisters

set_option autoImplicit false
@[expose] public section

/-! Pending and measured node counters are actual unary machines, with the outer frame preserved. -/

namespace JointThermoComplexity.Complexity.TermSpanCounter
open _root_.Complexity _root_.Complexity.TM TermSpanRegisters
open HeaderAt (Cursor)
variable {n : ℕ}

theorem pending_frame (tm : TM (n + 7)) (old count nodes bound : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R)
    (h : ∀ C : (Fin (n + 7) → Tape) → Prop,
      (∀ work work', (∀ j, j ≠ pending n → work' j = work j) → C work → C work') →
      tm.HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg old (work (pending n)) ∧ C work)
        (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg count (work (pending n)) ∧ C work) bound) :
    tm.HoareTime (Inv emitted R ⟨before, input, old, nodes⟩) (Inv emitted R ⟨before, input, count, nodes⟩) bound := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin (n + 7) → Tape) → Prop := fun work' => ∀ j, j ≠ pending n → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ pending n → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj
    exact (he j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hd, hh, hc', hs', hp, hother⟩ := h C hC inp work out ⟨hc, hr.safe, hr.counter, fun _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hn : IsReg nodes (d.work (nodeCounter n)) := by rw [hother _ (pending_nodeCounter n).symm]; exact hr.nodeReg
  have htags : ∀ i, (d.work (tags n i)).head = 1 := fun i => by rw [hother _ (tags_pending n i)]; exact hr.tagHeads i
  have hflag : (d.work (flag n)).head = 1 := by rw [hother _ (pending_flag n).symm]; exact hr.flagHead
  have hr' := reframe old count nodes nodes R hR work d.work hr (fun j hj => hother j hj.1)
    hs' (fun j => (hm.2.1 j).1) hp hn htags hflag
  exact ⟨d, t, ht, hd, hh, hc', hr'⟩

theorem node_frame (tm : TM (n + 7)) (old count pendingValue bound : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R)
    (h : ∀ C : (Fin (n + 7) → Tape) → Prop,
      (∀ work work', (∀ j, j ≠ nodeCounter n → work' j = work j) → C work → C work') →
      tm.HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg old (work (nodeCounter n)) ∧ C work)
        (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg count (work (nodeCounter n)) ∧ C work) bound) :
    tm.HoareTime (Inv emitted R ⟨before, input, pendingValue, old⟩) (Inv emitted R ⟨before, input, pendingValue, count⟩) bound := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin (n + 7) → Tape) → Prop := fun work' => ∀ j, j ≠ nodeCounter n → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ nodeCounter n → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj
    exact (he j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hd, hh, hc', hs', hn, hother⟩ := h C hC inp work out ⟨hc, hr.safe, hr.nodeReg, fun _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hp : IsReg pendingValue (d.work (pending n)) := by rw [hother _ (pending_nodeCounter n)]; exact hr.counter
  have htags : ∀ i, (d.work (tags n i)).head = 1 := fun i => by rw [hother _ (tags_nodeCounter n i)]; exact hr.tagHeads i
  have hflag : (d.work (flag n)).head = 1 := by rw [hother _ (nodeCounter_flag n).symm]; exact hr.flagHead
  have hr' := reframe pendingValue pendingValue count old R hR work d.work hr (fun j hj => hother j hj.2.1)
    hs' (fun j => (hm.2.1 j).1) hp hn htags hflag
  exact ⟨d, t, ht, hd, hh, hc', hr'⟩

theorem branch_hoareTime (bits : List Bool) (v nodes : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R) :
    (SourcePendingUpdate.branchMachine (pending n) bits).HoareTime
      (Inv emitted R ⟨before, input, v + 1, nodes⟩)
      (Inv emitted R ⟨before, input, v + SourceTermToken.children (SourceTermToken.classify bits), nodes⟩) (2 * v + 12) :=
  pending_frame _ (v + 1) _ nodes _ before input emitted R hR
    (fun C hC => SourcePendingUpdate.branch_hoareTime (pending n) bits v before input emitted C hC)

theorem decrement_hoareTime (v nodes : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R) :
    (UnaryPredecessor.machine (pending n)).HoareTime (Inv emitted R ⟨before, input, v + 1, nodes⟩)
      (Inv emitted R ⟨before, input, v, nodes⟩) (2 * v + 12) :=
  pending_frame _ (v + 1) v nodes _ before input emitted R hR
    (fun C hC => UnaryPredecessor.hoareTime (pending n) v before input emitted C hC)

theorem increment_hoareTime (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop)
    (hR : Stable R) (s : TermSpanControl.State) :
    (UnarySuccessor.machine (nodeCounter n)).HoareTime (Inv emitted R s)
      (Inv emitted R {s with nodes := s.nodes + 1}) (2 * s.nodes + 6) :=
  node_frame _ s.nodes (s.nodes + 1) s.pending _ s.before s.input emitted R hR
    (fun C hC => UnarySuccessor.hoareTime (nodeCounter n) s.nodes s.before s.input emitted C hC)

end JointThermoComplexity.Complexity.TermSpanCounter

#print axioms JointThermoComplexity.Complexity.TermSpanCounter.branch_hoareTime
#print axioms JointThermoComplexity.Complexity.TermSpanCounter.increment_hoareTime
