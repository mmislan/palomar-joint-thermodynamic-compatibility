module
public import proofs.JointThermoComplexity.Complexity.SourceTermForest
public import proofs.JointThermoComplexity.Complexity.UnaryReset

set_option autoImplicit false
@[expose] public section

/-! Reuse a bounded pending register for a two-term formula leaf. -/

namespace JointThermoComplexity.Complexity.SourceTermCountReset
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceIndexField
open SourceTermLoopBody (Inv)
variable {w n : ℕ}

def machine (pending : Fin w) : TM w :=
  seqTM (seqTM (clearWorkTM pending) (UnarySuccessor.machine pending)) (UnarySuccessor.machine pending)

theorem hoareTime (pending : Fin w) (old : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ pending → work' j = work j) → R work → R work') :
    (machine pending).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg old (work pending) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg 2 (work pending) ∧ R work)
      (2 * old + 21) := by
  have hr := UnaryReset.hoareTime pending old before input emitted R hR
  have h0 := UnarySuccessor.hoareTime pending 0 before input emitted R hR
  have h1 := UnarySuccessor.hoareTime pending 1 before input emitted R hR
  have hr0 := seqTM_hoareTime (clearWorkTM pending) (UnarySuccessor.machine pending) hr (by
    rintro inp work out ⟨hc, hs, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hp, hr⟩) h0
  have hfull := seqTM_hoareTime (seqTM (clearWorkTM pending) (UnarySuccessor.machine pending)) (UnarySuccessor.machine pending) hr0 (by
    rintro inp work out ⟨hc, hs, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hp, hr⟩) h1
  exact hfull.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega)

theorem ready_hoareTime (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1))
    (hp : SourcePendingFrame.Separate ports pending left right) (L arity old : ℕ) (initial : Bool)
    (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ pending → work' j = work j) → R work → R work') :
    (machine pending.castSucc).HoareTime
      (Inv ports pending left right L arity emitted R ⟨before, input, old, initial⟩)
      (Inv ports pending left right L arity emitted R ⟨before, input, 2, initial⟩) (2 * old + 21) := by
  rintro inp work out ⟨hc, hr, hv, hh, hf⟩
  let C : (Fin (n + 2) → Tape) → Prop := fun work' => ∀ j, j ≠ pending.castSucc → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ pending.castSucc → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj
    exact (he j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hd, hdhalt, hc', hs', hp', hother⟩ := hoareTime pending.castSucc old before input emitted C hC
    inp work out ⟨hc, hr.safe, hv, fun _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hl := hother left.castSucc (SourcePendingFrame.cast_ne hp.left.symm)
  have hright := hother right.castSucc (SourcePendingFrame.cast_ne hp.right.symm)
  have hflag := hother (NaturalScanBuffer.flag n) (SourcePendingFrame.cast_ne hp.flag.symm)
  have hbuf := hother (NaturalScanBuffer.buffer n) (SourcePendingFrame.buffer_ne pending)
  have hr' : Ready L left right arity R d.work :=
    ⟨hs', fun j => (hm.2.1 j).1, by simpa only [hbuf] using hr.encoded, by simpa only [hl] using hr.candidate,
      by simpa only [hright] using hr.arityBits, by simpa only [hright] using hr.arityZero,
      by simpa only [hflag] using hr.flagHead, hR _ _ (fun j hj => hother j.castSucc (SourcePendingFrame.cast_ne hj)) hr.frame⟩
  exact ⟨d, t, ht, hd, hdhalt, hc', hr', hp',
    fun i => by simpa only [hother (ports i).castSucc (SourcePendingFrame.cast_ne (hp.tags i).symm)] using hh i,
    by simpa only [hflag] using hf⟩

end JointThermoComplexity.Complexity.SourceTermCountReset

#print axioms JointThermoComplexity.Complexity.SourceTermCountReset.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceTermCountReset.ready_hoareTime
