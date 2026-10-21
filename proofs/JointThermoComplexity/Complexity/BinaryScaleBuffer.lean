module
public import proofs.JointThermoComplexity.Complexity.BinaryScaleRun
public import proofs.JointThermoComplexity.Complexity.OutputRoute

set_option autoImplicit false
@[expose] public section

/-! Route the scaled canonical magnitude into a fresh final work tape, then
rewind it for arithmetic. Original work data and real output are retained. -/

namespace JointThermoComplexity.Complexity.BinaryScaleBuffer
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
variable {w : ℕ}

def oldWork (work : Fin (w + 1) → Tape) : Fin w → Tape := fun j => work j.castSucc

theorem cast_ne_last (i : Fin w) : i.castSucc ≠ Fin.last w := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = w at hv
  omega

def bufferedMachine (k : ℕ) (idx : Fin w) : TM (w + 1) := (BinaryScaleRun.machine k idx).retargetOutput

def machine (k : ℕ) (idx : Fin w) : TM (w + 1) := seqTM (bufferedMachine k idx) (rewindWorkTM (Fin.last w))

theorem buffered_hoareTime (k : ℕ) (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (bufferedMachine k idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ (work (Fin.last w)).HasBinaryPrefix [] ∧
        (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ (work (Fin.last w)).HasBinaryPrefix (k * v).bits ∧
        (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (2 * v.bits.length + k + 6) := by
  have hb := BinaryScaleRun.natural_hoareTime k idx v before input [] R
  have hr := OutputRoute.hoareTime (BinaryScaleRun.machine k idx) _ _ _
    (fun out => out.HasBinaryPrefix emitted ∧ out.cells 0 = Γ.start) hb
  apply hr.consequence
  · rintro inp work out ⟨hc, hs, hv, he, hz, hx⟩
    exact ⟨hc.output_read, ⟨hc.tapePrefix, hc.zero⟩,
      ⟨hc.cells, hc.head, fun j => hc.works j.castSucc, he, hz⟩,
      (fun j => hs j.castSucc), hv, hx⟩
  · rintro inp work out ⟨_, ⟨ho, hoz⟩, hc, hs, hv, hx⟩
    have hp : (work (Fin.last w)).HasBinaryPrefix (k * v).bits := by simpa only [List.nil_append] using hc.tapePrefix
    have hcontent : (work (Fin.last w)).HasBinaryContent (k * v).bits := hp.2
    have hsafe : ∀ j, Parked (work j) := by
      intro j
      refine Fin.lastCases ?_ (fun i => hs i) j
      exact ⟨by rw [hp.1]; omega, hcontent.cells_ne_start⟩
    exact ⟨⟨hc.cells, hc.head, fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩, ho, hoz⟩,
      hsafe, hv, hp, hc.zero, hx⟩
  · exact le_rfl

theorem rewind_hoareTime (idx : Fin w) (v y : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (rewindWorkTM (Fin.last w)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ (work (Fin.last w)).HasBinaryPrefix y.bits ∧
        (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ Register y (work (Fin.last w)) ∧ R (oldWork work))
      (y.bits.length + 3) := by
  rintro inp work out ⟨hc, hs, hv, hb, hz, hx⟩
  have hcontent : (work (Fin.last w)).HasBinaryContent y.bits := hb.2
  let P : Tape → (Fin (w + 1) → Tape) → Tape → Prop := fun inp' work' out' =>
    inp' = inp ∧ out' = out ∧ (work' (Fin.last w)).cells = (work (Fin.last w)).cells ∧
      ∀ j, j ≠ Fin.last w → work' j = work j
  have hP : ∀ (inp' : Tape) (work' : Fin (w + 1) → Tape) (out' : Tape)
      (inp'' : Tape) (work'' : Fin (w + 1) → Tape) (out'' : Tape),
      P inp' work' out' → (work'' (Fin.last w)).cells = (work' (Fin.last w)).cells →
      (work'' (Fin.last w)).head = 1 → (∀ j, j ≠ Fin.last w → work'' j = work' j) →
      inp'' = inp' → out''.cells = out'.cells → out''.head = out'.head → P inp'' work'' out'' := by
    rintro inp' work' out' inp'' work'' out'' ⟨hi, ho, hc', hw⟩ hc'' _ hw' hi' hoc hoh
    exact ⟨hi'.trans hi, (Tape.ext hoh hoc).trans ho, hc''.trans hc', fun j hj => (hw' j hj).trans (hw j hj)⟩
  obtain ⟨d, t, ht, hd, hh, hhead, hp⟩ :=
    rewindWorkTM_hoareTime_frame (Fin.last w) (y.bits.length + 1) hP inp work out
      ⟨hz, hcontent.cells_ne_start, hb.1.le, hc.input_read, hc.output_read,
        by rw [hc.tapePrefix.1]; omega, (fun j _ => hc.works j), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hreg : Register y (d.work (Fin.last w)) := by
    refine ⟨⟨hhead, ?_⟩, ?_⟩
    · simpa only [Tape.HasBinaryContent, hp.2.2.1] using hb.2
    · rw [hp.2.2.1]
      exact hz
  have hold : oldWork d.work = oldWork work := by
    funext j
    exact hp.2.2.2 j.castSucc (cast_ne_last j)
  have hsafe : ∀ j, Parked (d.work j) := by
    intro j
    by_cases hj : j = Fin.last w
    · subst j
      exact ⟨by rw [hreg.1.1], hreg.1.hasBinaryContent.cells_ne_start⟩
    · rw [hp.2.2.2 j hj]
      exact hs j
  refine ⟨d, t, by omega, hd, hh, ?_, hsafe, ?_, hreg, ?_⟩
  · exact ⟨by simpa only [hp.1] using hc.cells, by simpa only [hp.1] using hc.head,
      fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩,
      by simpa only [hp.2.1] using hc.tapePrefix, by simpa only [hp.2.1] using hc.zero⟩
  · simpa only [hp.2.2.2 idx.castSucc (cast_ne_last idx)] using hv
  · simpa only [hold] using hx

theorem natural_hoareTime (k : ℕ) (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine k idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ (work (Fin.last w)).HasBinaryPrefix [] ∧
        (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ Register (k * v) (work (Fin.last w)) ∧ R (oldWork work))
      (3 * v.bits.length + 2 * k + 10) := by
  have hb := buffered_hoareTime k idx v before input emitted R
  have hr := rewind_hoareTime idx v (k * v) before input emitted R
  have h := seqTM_hoareTime _ _ hb (by
    rintro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.phase
    rw [hi, hw, ho]
    exact hp) hr
  apply h.mono_bound
  have hl : (k * v).bits.length ≤ v.bits.length + k := by
    simpa only [BinaryScaleCanonical.multiply_bits] using BinaryScaleCanonical.length_multiply k v.bits
  omega

end JointThermoComplexity.Complexity.BinaryScaleBuffer

#print axioms JointThermoComplexity.Complexity.BinaryScaleBuffer.machine
#print axioms JointThermoComplexity.Complexity.BinaryScaleBuffer.buffered_hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryScaleBuffer.rewind_hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryScaleBuffer.natural_hoareTime
