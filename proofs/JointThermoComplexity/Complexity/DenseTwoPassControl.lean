module
public import proofs.JointThermoComplexity.Complexity.DenseSourceRestart

set_option autoImplicit false
@[expose] public section

/-! Exact all-raw cursor/count handoff between the two reaction-list passes. -/

namespace JointThermoComplexity.Complexity.DenseTwoPassControl
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun

def arity (input : List Bool) : ℕ := HeaderControl.count input
def total (boxed : Bool) (input : List Bool) : ℕ := (DenseReplayControl.rescan boxed input).rows
def offset (boxed : Bool) (input : List Bool) : ℕ := (DenseReplayControl.rescan boxed input).base.offset
def initial (boxed : Bool) (input : List Bool) : CountedSparseControl.State := DenseReplayControl.state boxed input
def finalState (boxed : Bool) (input : List Bool) : CountedSparseControl.State := CountedSparseControl.run boxed input.length (initial boxed input)
def Retained (boxed : Bool) (input : List Bool) : (Fin 64 → Tape) → Prop := DenseBranchPass.Retained boxed (arity input) (total boxed input) (offset boxed input)
def Full (boxed : Bool) (input : List Bool) (running : Bool) : (Fin 64 → Tape) → Prop :=
  DenseSourceRestart.Full boxed input.length (arity input) (total boxed input) (offset boxed input) running
def Payload (boxed : Bool) (input emitted : List Bool) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => DenseMarkedFrame.Inv input.length (arity input) (total boxed input) emitted (Retained boxed input)
    (finalState boxed input) inp work out ∧ IsReg input.length (work 18)
def Ready (boxed : Bool) (input emitted : List Bool) : _root_.Complexity.TM.TapePred 64 :=
  DenseFixedSourceBank.Pre input.length (arity input) (total boxed input) (offset boxed input) 0 (DenseRawReady.values [])
    (initial boxed input).base.before (initial boxed input).base.input emitted
    (DenseBranchPass.Frame input.length (initial boxed input).base.running (Retained boxed input))

theorem final_rows (boxed : Bool) (input : List Bool) : (finalState boxed input).rows = total boxed input :=
  (DenseReplayControl.run_rows boxed input).trans (DenseReplayControl.rescan_rows boxed input).symm

theorem word_conservation (boxed : Bool) (input : List Bool) :
    (finalState boxed input).base.before ++ (finalState boxed input).base.input = input := by
  have h := DenseReplayControl.run_same boxed input.length _ _ (DenseReplayControl.state_same boxed input)
  have hb := h.2.1
  change (finalState boxed input).base.before = (SparseDimensionEntry.outcome boxed input).base.before at hb
  have hi := h.2.2.1
  change (finalState boxed input).base.input = (SparseDimensionEntry.outcome boxed input).base.input at hi
  rw [hb, hi]
  exact SparseSourceWord.outcome_word boxed input

theorem before_length (boxed : Bool) (input : List Bool) : (finalState boxed input).base.before.length ≤ input.length := by
  have h := congrArg List.length (word_conservation boxed input)
  rw [List.length_append] at h
  omega

theorem restart_pre (boxed : Bool) (input emitted : List Bool) :
    ∀ inp work out, Payload boxed input emitted inp work out →
      DenseSourceFrame.Pre input.length (arity input) (total boxed input) (2 + total boxed input)
        (finalState boxed input).base.before (finalState boxed input).base.input emitted
        (Full boxed input (finalState boxed input).base.running) inp work out := by
  rintro inp work out ⟨⟨hc, hs, ⟨hp, hcore⟩, hstatus⟩, hf⟩
  have hr := hcore.frame
  have hfull : Full boxed input (finalState boxed input).base.running work := ⟨hr.1, hr.2.1, hstatus, hf, hr.2.2⟩
  have hcore' := DenseMarkedStep.core_frame _ _ _ _ _ work hcore hfull
  rw [final_rows] at hcore'
  exact ⟨hc, hs, hp, hcore'⟩

theorem restart_post (boxed : Bool) (input emitted : List Bool) :
    ∀ inp work out, DenseFixedSourceBank.Pre input.length (arity input) (total boxed input) (offset boxed input) 0 (DenseRawReady.values [])
      (HeaderControl.copied ((finalState boxed input).base.before ++ (finalState boxed input).base.input))
      (HeaderControl.suffix ((finalState boxed input).base.before ++ (finalState boxed input).base.input)) emitted
      (Full boxed input true) inp work out → Ready boxed input emitted inp work out := by
  rintro inp work out hp
  rw [word_conservation] at hp
  rcases hp with ⟨⟨hc, hs, hparser, hcore⟩, hu, href⟩
  have hr := hcore.frame
  have hframe : DenseBranchPass.Frame input.length (initial boxed input).base.running (Retained boxed input) work :=
    ⟨hr.2.2.1, hr.2.2.2.1, hr.1, hr.2.1, hr.2.2.2.2⟩
  exact ⟨⟨hc, hs, hparser, DenseMarkedStep.core_frame _ _ _ _ _ work hcore hframe⟩, hu, href⟩

def restartBound (L : ℕ) : ℕ := (3 * DenseReplayControl.budget L + 9) + 1 + 4 * (12 * L + 10) + 1 + (L + 3 + 1 + (L + 1) + 1 + 1)

theorem restart_bound (boxed : Bool) (input : List Bool) :
    DenseSourceRestart.timeBound input.length (2 + total boxed input) (finalState boxed input).base.before (finalState boxed input).base.input ≤
      restartBound input.length := by
  have hb : (2 + total boxed input).bits.length ≤ DenseReplayControl.budget input.length :=
    (BoundedUnaryControl.bits_le _).trans (by have h := DenseReplayControl.rows_le_budget boxed input; change total boxed input + 2 ≤ _ at h; omega)
  have hbefore := before_length boxed input
  have hheader := HeaderControl.count_le_length input
  unfold DenseSourceRestart.timeBound DenseSourceRestart.resetBound DenseSourceRestart.cursorBound restartBound
  rw [word_conservation]
  omega

theorem restart_hoareTime (boxed : Bool) (input emitted : List Bool) :
    DenseSourceRestart.machine.HoareTime (Payload boxed input emitted) (Ready boxed input emitted) (restartBound input.length) :=
  (DenseSourceRestart.hoareTime boxed input.length input.length (arity input) (total boxed input) (offset boxed input)
    (2 + total boxed input) (finalState boxed input).base.running (finalState boxed input).base.before (finalState boxed input).base.input emitted).consequence
      (restart_pre boxed input emitted) (restart_post boxed input emitted) (restart_bound boxed input)

theorem branch_hoareTime (boxed right : Bool) (input emitted : List Bool) :
    (DenseBranchPass.machine boxed right).HoareTime (Ready boxed input emitted)
      (Payload boxed input (emitted ++ DenseBranchPass.word boxed right (arity input) (total boxed input) (offset boxed input) input.length (initial boxed input)))
      (DenseBranchPass.timeBound boxed right input.length (arity input) (total boxed input) (DenseReplayControl.budget input.length) input.length) :=
  DenseBranchPass.hoareTime boxed right input.length (arity input) (total boxed input) (offset boxed input)
    (DenseReplayControl.budget input.length) input.length (initial boxed input) rfl (DenseRawReady.values []) emitted (Retained boxed input)
    (DenseBranchPass.retained_stable _ _ _ _) (DenseReplayControl.input_length boxed input) (DenseReplayControl.offset_bits_le_budget boxed input)
    (DenseReplayControl.length_le_budget input.length) (DenseReplayControl.rows_le_budget boxed input) (final_rows boxed input).le

end JointThermoComplexity.Complexity.DenseTwoPassControl

#print axioms JointThermoComplexity.Complexity.DenseTwoPassControl.restart_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseTwoPassControl.branch_hoareTime
