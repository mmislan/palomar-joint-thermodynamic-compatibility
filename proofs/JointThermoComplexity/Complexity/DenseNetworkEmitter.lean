module
public import proofs.JointThermoComplexity.Complexity.DenseNetworkSuffix
public import proofs.JointThermoComplexity.Complexity.DenseTwoPass

set_option autoImplicit false
@[expose] public section

/-! Whole actual all-raw output: dimensions, both reaction lists and the fixed
motif/direction/box suffix. Canonical semantic identity is a separate bridge. -/

namespace JointThermoComplexity.Complexity.DenseNetworkEmitter
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseTwoPassControl

def Tail (boxed : Bool) (input : List Bool) (work : Fin 64 → Tape) : Prop :=
  DenseSourceFrame.Work input.length (arity input) (total boxed input) (2 + (finalState boxed input).rows) (Retained boxed input) work ∧
    DenseMarkedFrame.Status (finalState boxed input).base.running work ∧ IsReg input.length (work 18)
def word (boxed : Bool) (input : List Bool) : List Bool :=
  DenseTwoPass.word boxed input ++ DenseNetworkSuffix.word boxed (arity input) (total boxed input)
def machine (boxed : Bool) : TM 64 := seqTM (DenseTwoPass.machine boxed) (DenseNetworkSuffix.machine boxed)
def timeBound (boxed : Bool) (input : List Bool) : ℕ :=
  DenseTwoPass.timeBound boxed input + 1 + DenseNetworkSuffix.timeBound boxed (arity input) (total boxed input)

theorem suffix_hoareTime (boxed : Bool) (input emitted : List Bool) :
    (DenseNetworkSuffix.machine boxed).HoareTime (Payload boxed input emitted)
      (Payload boxed input (emitted ++ DenseNetworkSuffix.word boxed (arity input) (total boxed input)))
      (DenseNetworkSuffix.timeBound boxed (arity input) (total boxed input)) := by
  have hh := DenseNetworkSuffix.hoareTime boxed (arity input) (total boxed input)
    (finalState boxed input).base.before (finalState boxed input).base.input emitted (Tail boxed input)
  apply hh.consequence
  · rintro inp work out ⟨⟨hc, hs, hwork, hstatus⟩, hf⟩
    exact ⟨hc, hs, ⟨hwork.2.total, hwork.2.branch, hwork.2.frame.2.2⟩, hwork, hstatus, hf⟩
  · rintro inp work out ⟨hc, hs, _hd, hwork, hstatus, hf⟩
    exact ⟨⟨hc, hs, hwork, hstatus⟩, hf⟩
  · exact le_rfl

theorem hoareTime (boxed : Bool) (input : List Bool) :
    (machine boxed).HoareTime (InitialTapeLift.Initial 64 input) (Payload boxed input (word boxed input)) (timeBound boxed input) := by
  exact seqTM_hoareTime _ _ (DenseTwoPass.hoareTime boxed input) (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.1.phase
    rw [hi, hw, ho]
    exact h) (suffix_hoareTime boxed input (DenseTwoPass.word boxed input))

end JointThermoComplexity.Complexity.DenseNetworkEmitter

#print axioms JointThermoComplexity.Complexity.DenseNetworkEmitter.hoareTime
