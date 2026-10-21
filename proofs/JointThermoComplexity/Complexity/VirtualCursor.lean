module
public import proofs.JointThermoComplexity.Complexity.InputRoute
public import proofs.JointThermoComplexity.Complexity.InputCursor

set_option autoImplicit false
@[expose] public section

/-! Run a cursor subroutine on the last work tape, retaining the real source cursor. -/

namespace JointThermoComplexity.Complexity.VirtualCursor
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

theorem input_safe {m : ℕ} {before input emitted : List Bool}
    {inp out : Tape} {work : Fin m → Tape} (hc : Cursor before input emitted inp work out) :
    Tape.StartInvariant inp := by
  constructor
  · rw [hc.cells]
    rfl
  · intro j hj
    rw [hc.cells]
    exact Tape.init_ofBool_cells_ne_start _ j hj

theorem output_safe {m : ℕ} {before input emitted : List Bool}
    {inp out : Tape} {work : Fin m → Tape} (hc : Cursor before input emitted inp work out) :
    Tape.StartInvariant out := ⟨hc.zero, (show out.HasBinaryContent emitted from hc.tapePrefix.2).cells_ne_start⟩

theorem markers_reaches (tm : TM w) {c d : Cfg w tm.Q} {t : ℕ} (h : tm.reachesIn t c d)
    (hi : Tape.StartInvariant c.input) (hw : ∀ j, Tape.StartInvariant (c.work j))
    (ho : Tape.StartInvariant c.output) :
    Tape.StartInvariant d.input ∧ (∀ j, Tape.StartInvariant (d.work j)) ∧ Tape.StartInvariant d.output := by
  induction h with
  | zero => exact ⟨hi, hw, ho⟩
  | step hs _ ih =>
    obtain ⟨hi', hw', ho'⟩ := Tape.StartInvariant.step tm hs hi hw ho
    exact ih hi' hw' ho'

theorem hoareTime (tm : TM w) (word taken tail emitted emitted' before input : List Bool)
    (hsplit : taken ++ tail = word) (P Q : (Fin w → Tape) → Prop) (bound : ℕ)
    (h : tm.HoareTime
      (fun inp work out => Cursor [] word emitted inp work out ∧ (∀ j, Parked (work j)) ∧ P work)
      (fun inp work out => Cursor taken tail emitted' inp work out ∧ (∀ j, Parked (work j)) ∧ Q work) bound) :
    tm.retargetInput.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ j, (work j).cells 0 = Γ.start) ∧ (work (Fin.last w)).HasBinaryString word ∧
        P (fun j => work j.castSucc))
      (fun inp work out => Cursor before input emitted' inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ j, (work j).cells 0 = Γ.start) ∧ (work (Fin.last w)).HasBinaryContent word ∧
        (work (Fin.last w)).head = taken.length + 1 ∧ Q (fun j => work j.castSucc)) bound := by
  rintro inp work out ⟨hc, hs, hz, hb, hp⟩
  let inner : Fin w → Tape := fun j => work j.castSucc
  have hv : Cursor [] word emitted (work (Fin.last w)) inner out :=
    ⟨by simpa only [List.nil_append] using BinaryTape.cells_of_content hb.2 (hz _),
      hb.1, fun j => hc.works j.castSucc, hc.tapePrefix, hc.zero⟩
  let S : Tape → Prop := fun t => t.cells = inp.cells ∧ t.head = inp.head
  have hcore : tm.HoareTime
      (fun inp work out => (Cursor [] word emitted inp work out ∧ (∀ j, Parked (work j)) ∧ P work) ∧
        (∀ j, Tape.StartInvariant (work j)))
      (fun inp work out => Cursor taken tail emitted' inp work out ∧ (∀ j, Parked (work j)) ∧ Q work) bound :=
    h.weaken_pre (fun _ _ _ hpre => hpre.1)
  have hroute := InputRoute.hoareTime tm _ _ bound S hcore
    (fun _ _ _ hpre => input_safe hpre.1.1)
    (fun _ _ _ hpre => hpre.2)
    (fun _ _ _ hpre => output_safe hpre.1.1)
  obtain ⟨d, t, ht, hr, hh, _hread, hdinput, hdcur, hdsafe, hdq⟩ :=
    hroute inp work out ⟨hc.input_read, ⟨rfl, rfl⟩, ⟨hv, fun j => hs j.castSucc, hp⟩,
      fun j => ⟨hz j.castSucc, (hs j.castSucc).2⟩⟩
  have hm := markers_reaches tm.retargetInput hr (input_safe hc) (fun j => ⟨hz j, (hs j).2⟩) (output_safe hc)
  have hcontent : (d.work (Fin.last w)).HasBinaryContent word := by
    apply BinaryTape.content_of_cells
    simpa only [hsplit] using hdcur.cells
  have hsafe : ∀ j, Parked (d.work j) := by
    intro j
    by_cases hj : j.val < w
    · have he : j = (⟨j.val, hj⟩ : Fin w).castSucc := by apply Fin.ext; rfl
      rw [he]
      exact hdsafe _
    · have he : j = Fin.last w := by apply Fin.ext; simp only [Fin.val_last]; omega
      subst j
      exact ⟨by rw [hdcur.head]; omega, hcontent.cells_ne_start⟩
  have hmain : Cursor before input emitted' d.input d.work d.output :=
    ⟨hdinput.1.trans hc.cells, hdinput.2.trans hc.head,
      fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩, hdcur.tapePrefix, hdcur.zero⟩
  exact ⟨d, t, ht, hr, hh, hmain, hsafe, fun j => (hm.2.1 j).1, hcontent, hdcur.head, hdq⟩

end JointThermoComplexity.Complexity.VirtualCursor

#print axioms JointThermoComplexity.Complexity.VirtualCursor.markers_reaches
#print axioms JointThermoComplexity.Complexity.VirtualCursor.hoareTime
