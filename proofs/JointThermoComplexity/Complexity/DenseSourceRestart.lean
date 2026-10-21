module
public import proofs.JointThermoComplexity.Complexity.DenseBranchPass

set_option autoImplicit false
@[expose] public section

/-! Reuse the completed branch workspace: clear current/reference buffers,
rewind and skip the input header, and reactivate the source marker. -/

namespace JointThermoComplexity.Complexity.DenseSourceRestart
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun

def Full (boxed : Bool) (count n N U : ℕ) (running : Bool) : (Fin 64 → Tape) → Prop :=
  DenseLiveInitialize.Retained N U (DenseRescanEntry.Outer boxed count n N running)
def Plain (boxed : Bool) (count n N U : ℕ) (work : Fin 64 → Tape) : Prop :=
  IsReg count (work 18) ∧ DenseBranchPass.Retained boxed n N U work
def view (work : Fin 64 → Tape) : Fin 64 → Tape := Function.update work 38 (regTape 0)
def ResetFrame (L n N : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  DenseSourceFrame.Parser L work ∧ DenseSourceFrame.Core n N 0 R (view work)

theorem full_stable (boxed : Bool) (count n N U : ℕ) (running : Bool) : DenseSourceFrame.Stable (Full boxed count n N U running) :=
  DenseLiveInitialize.retained_stable N U _ (DenseRescanEntry.outer_source boxed count n N running)

theorem core_view (n N current : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : DenseSourceFrame.Stable R)
    (work : Fin 64 → Tape) (hp : DenseSourceFrame.Core n N current R work) : DenseSourceFrame.Core n N 0 R (view work) := by
  have he (j : Fin 64) (hj : j ≠ 38) : view work j = work j := Function.update_of_ne hj _ _
  have safe : ∀ j : Fin 64, DenseSourceFrame.Outside j → j ≠ 38 := by
    unfold DenseSourceFrame.Outside DenseRowFrame.Outside
    decide
  obtain ⟨u, hu, hn⟩ := hp.next
  refine ⟨by rw [he 12 (by decide)]; exact hp.adjusted, by rw [he 16 (by decide)]; exact hp.arity,
    by rw [he 33 (by decide)]; exact hp.total, by rw [he 34 (by decide)]; exact hp.branch, ?_,
    ⟨u, hu, by rw [he 41 (by decide)]; exact hn⟩,
    by rw [he 39 (by decide)]; exact hp.cell, by rw [he 42 (by decide)]; exact hp.comparison,
    by rw [he 40 (by decide)]; exact hp.ending, by rw [he 43 (by decide)]; exact hp.lastHead, ?_,
    by rw [he 63 (by decide)]; exact hp.scratch, hR work (view work) (fun j hj => he j (safe j hj)) hp.frame⟩
  · simpa only [view, Function.update_self] using AddressCodeProgram.binary_zero (reg_regT 0)
  · intro i
    rw [he _ (by intro h; have hv := congrArg Fin.val h; change 44 + i.val = 38 at hv; omega)]
    exact hp.powers i

theorem reset_frame_stable (L n N : ℕ) (R : (Fin 64 → Tape) → Prop) :
    BinaryIncrementFramed.Stable (38 : Fin 64) (ResetFrame L n N R) := by
  rintro work next he ⟨hp, hc⟩
  have hv : view next = view work := by
    funext j
    by_cases hj : j = (38 : Fin 64)
    · subst j; simp only [view, Function.update_self]
    · simp only [view, Function.update_of_ne hj, he j hj]
  refine ⟨DenseSourceFrame.parser_transfer L work next (by
    intro j hj
    apply he j
    intro h; have hh := congrArg Fin.val h; change j.val = 38 at hh; omega) hp, ?_⟩
  rw [hv]
  exact hc

def reset : TM 64 := seqTM (BinaryBufferReset.machine (38 : Fin 64)) (DenseReferenceBank.machine 0)
def resetBound (L current : ℕ) : ℕ := (3 * current.bits.length + 9) + 1 + 4 * (12 * L + 10)

theorem reset_hoareTime (boxed : Bool) (L count n N U current : ℕ) (running : Bool) (before input emitted : List Bool) :
    reset.HoareTime (DenseSourceFrame.Pre L n N current before input emitted (Full boxed count n N U running))
      (DenseFixedSourceBank.Pre L n N U 0 (DenseRawReady.values []) before input emitted (Full boxed count n N U running))
      (resetBound L current) := by
  let R := Full boxed count n N U running
  have hR := full_stable boxed count n N U running
  have hr := BinaryBufferReset.hoareTime (38 : Fin 64) current.bits before input emitted (ResetFrame L n N R)
    (reset_frame_stable L n N R)
  have h1 : (BinaryBufferReset.machine (38 : Fin 64)).HoareTime
      (DenseSourceFrame.Pre L n N current before input emitted R)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        DenseReferenceClear.Ready L DenseReferenceBank.slots work ∧ DenseReferenceBank.Present [] (by decide) work ∧
          DenseLiveInitialize.ClearFrame L n N U (DenseRescanEntry.Outer boxed count n N running) work)
      (3 * current.bits.length + 9) := by
    apply hr.consequence
    · rintro inp work out ⟨hc, hs, hp, hcore⟩
      exact ⟨hc, hs, hcore.position.1.2, hcore.position.2, by rw [hcore.position.1.1]; omega,
        hp, core_view n N current R hR work hcore⟩
    · rintro inp work out ⟨hc, hs, hz, hp, hcore⟩
      have hv : view work = work := by unfold view; rw [← hz.eq_regT, Function.update_eq_self]
      rw [hv] at hcore
      exact ⟨hc, hs, DenseSourceFrame.ref_ready L work hp, (by intro i; exact Fin.elim0 i),
        DenseLiveInitialize.marks_of_parser L work hp, hcore⟩
    · exact le_rfl
  have hclear := DenseReferenceBank.hoareTime L [] (by decide) before input emitted
    (DenseLiveInitialize.ClearFrame L n N U (DenseRescanEntry.Outer boxed count n N running))
    (DenseLiveInitialize.clear_stable L n N U _ (DenseRescanEntry.outer_source boxed count n N running))
  have hh := seqTM_hoareTime _ _ h1 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) hclear
  apply hh.consequence (fun _ _ _ h => h)
  · rintro inp work out ⟨hc, hs, hbank, hm, hcore⟩
    have href : PowerVectorUnit.Refs (DensePowerPorts.cellLayout 4 (by decide)) (DenseRawReady.values []) work := by
      apply DensePowerPorts.refs
      · intro i; exact (hbank i).1
      · exact hcore.powers
    exact ⟨⟨hc, hs, DenseLiveInitialize.parser_of_bank L work hbank hm, hcore⟩, hcore.frame.2.1, href⟩
  · exact le_rfl

def cursor : TM 64 := seqTM rewindInputTM HeaderSkip.machine
def cursorBound (before input : List Bool) : ℕ := before.length + 3 + 1 + (HeaderControl.count (before ++ input) + 1)

theorem cursor_hoareTime (L n N U : ℕ) (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) :
    cursor.HoareTime (DenseFixedSourceBank.Pre L n N U 0 (DenseRawReady.values []) before input emitted R)
      (DenseFixedSourceBank.Pre L n N U 0 (DenseRawReady.values []) (HeaderControl.copied (before ++ input))
        (HeaderControl.suffix (before ++ input)) emitted R) (cursorBound before input) := by
  let P : (Fin 64 → Tape) → Prop := fun work => DenseSourceFrame.Work L n N 0 R work ∧ Register U (work 13) ∧
    PowerVectorUnit.Refs (DensePowerPorts.cellLayout 4 (by decide)) (DenseRawReady.values []) work
  have h1 := InputRewind.hoareTime before input emitted (fun work => (∀ j, Parked (work j)) ∧ P work)
  have h2 := HeaderSkipRaw.hoareTime (w := 64) [] (before ++ input) emitted P
  have hh := seqTM_hoareTime _ _ h1 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) h2
  apply hh.consequence
  · rintro inp work out ⟨⟨hc, hs, hp⟩, hu, href⟩
    exact ⟨hc, hs, hp, hu, href⟩
  · rintro inp work out ⟨hc, hs, hp, hu, href⟩
    exact ⟨⟨by simpa only [List.nil_append] using hc, hs, hp⟩, hu, href⟩
  · exact le_rfl

theorem plain_stable (boxed : Bool) (count n N U : ℕ) :
    ∀ work next, (∀ j, j ≠ (15 : Fin 64) → next j = work j) → Plain boxed count n N U work → Plain boxed count n N U next := by
  rintro work next he ⟨hf, hn, hu, h3, h4, h5⟩
  exact ⟨by rw [he 18 (by decide)]; exact hf, by rw [he 17 (by decide)]; exact hn,
    by rw [he 13 (by decide)]; exact hu, by rw [he 35 (by decide)]; exact h3,
    by rw [he 36 (by decide)]; exact h4, by rw [he 37 (by decide)]; exact h5⟩

theorem activate_hoareTime (boxed : Bool) (L count n N U : ℕ) (running : Bool) (before input emitted : List Bool) :
    (SourceTermToken.setStatus (15 : Fin 64) true).HoareTime
      (DenseFixedSourceBank.Pre L n N U 0 (DenseRawReady.values []) before input emitted (Full boxed count n N U running))
      (DenseFixedSourceBank.Pre L n N U 0 (DenseRawReady.values []) before input emitted (Full boxed count n N U true)) 1 := by
  let R := Plain boxed count n N U
  let P : (Fin 64 → Tape) → Prop := fun work => DenseSourceFrame.Work L n N 0 R work ∧ DenseReferenceBank.Bank L [] work
  have hP : ∀ work next, (∀ j, j ≠ (15 : Fin 64) → next j = work j) → P work → P next := by
    rintro work next he ⟨⟨hp, hcore⟩, hbank⟩
    have hparser := DenseSourceFrame.parser_transfer L work next (by
      intro j hj
      apply he j
      intro h; have hv := congrArg Fin.val h; change j.val = 15 at hv; omega) hp
    have hcore' := DenseMarkedFrame.core_transfer n N 0 R work next
      (fun j hj => he j (DenseMarkedFrame.keys_safe j hj).1) (plain_stable boxed count n N U work next he) hcore
    refine ⟨⟨hparser, hcore'⟩, ?_⟩
    intro i
    rw [he (DenseReferenceBank.port i) (by intro h; have hv := congrArg Fin.val h; change 2 + i.val = 15 at hv; omega)]
    exact hbank i
  have hh := SourceTermToken.setStatus_hoareTime (15 : Fin 64) true before input emitted P hP
  apply hh.consequence
  · rintro inp work out ⟨⟨hc, hs, hp, hcore⟩, _hu, href⟩
    have hr := hcore.frame
    have hp' : R work := ⟨hr.2.2.2.1, hr.1, hr.2.1, hr.2.2.2.2⟩
    have hbank : DenseReferenceBank.Bank L [] work := by
      intro i
      fin_cases i
      · exact ⟨(href (DensePowerPorts.comparison 4 (by decide) 0) (List.mem_ofFn.mpr ⟨0, rfl⟩)).1, (hp.2.2.1 (2, 6) (by decide)).1⟩
      · exact ⟨(href (DensePowerPorts.comparison 4 (by decide) 1) (List.mem_ofFn.mpr ⟨1, rfl⟩)).1, (hp.2.2.1 (3, 7) (by decide)).1⟩
      · exact ⟨(href (DensePowerPorts.comparison 4 (by decide) 2) (List.mem_ofFn.mpr ⟨2, rfl⟩)).1, (hp.2.2.1 (4, 8) (by decide)).1⟩
      · exact ⟨(href (DensePowerPorts.comparison 4 (by decide) 3) (List.mem_ofFn.mpr ⟨3, rfl⟩)).1, (hp.2.2.1 (5, 9) (by decide)).1⟩
    exact ⟨hc, hs, hr.2.2.1.1, ⟨hp, DenseMarkedStep.core_frame _ _ _ _ R work hcore hp'⟩, hbank⟩
  · rintro inp work out ⟨hc, hs, hh, hv, ⟨hp, hcore⟩, hbank⟩
    have hr := hcore.frame
    have hf : Full boxed count n N U true work := ⟨hr.2.1, hr.2.2.1, ⟨hh, hv⟩, hr.1, hr.2.2.2⟩
    have href : PowerVectorUnit.Refs (DensePowerPorts.cellLayout 4 (by decide)) (DenseRawReady.values []) work := by
      apply DensePowerPorts.refs
      · intro i; exact (hbank i).1
      · exact hcore.powers
    exact ⟨⟨hc, hs, hp, DenseMarkedStep.core_frame _ _ _ R _ work hcore hf⟩, hr.2.2.1, href⟩
  · exact le_rfl

def machine : TM 64 := seqTM reset (seqTM cursor (SourceTermToken.setStatus 15 true))
def timeBound (L current : ℕ) (before input : List Bool) : ℕ := resetBound L current + 1 + (cursorBound before input + 1 + 1)

theorem hoareTime (boxed : Bool) (L count n N U current : ℕ) (running : Bool) (before input emitted : List Bool) :
    machine.HoareTime (DenseSourceFrame.Pre L n N current before input emitted (Full boxed count n N U running))
      (DenseFixedSourceBank.Pre L n N U 0 (DenseRawReady.values []) (HeaderControl.copied (before ++ input))
        (HeaderControl.suffix (before ++ input)) emitted (Full boxed count n N U true)) (timeBound L current before input) := by
  have h1 := reset_hoareTime boxed L count n N U current running before input emitted
  have h2 := cursor_hoareTime L n N U before input emitted (Full boxed count n N U running)
  have h3 := activate_hoareTime boxed L count n N U running (HeaderControl.copied (before ++ input)) (HeaderControl.suffix (before ++ input)) emitted
  have h23 := seqTM_hoareTime _ _ h2 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.1.phase
    rw [hi, hw, ho]
    exact h) h3
  exact seqTM_hoareTime _ _ h1 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.1.phase
    rw [hi, hw, ho]
    exact h) h23

end JointThermoComplexity.Complexity.DenseSourceRestart

#print axioms JointThermoComplexity.Complexity.DenseSourceRestart.hoareTime
