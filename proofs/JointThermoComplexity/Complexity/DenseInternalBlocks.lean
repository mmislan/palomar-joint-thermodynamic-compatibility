module
public import proofs.JointThermoComplexity.Complexity.IndicatorFixedPair
public import proofs.JointThermoComplexity.Complexity.DenseBlockWords
public import proofs.JointThermoComplexity.Complexity.ReusableIndicatorVector
public import proofs.JointThermoComplexity.Complexity.BinaryConstantAdd

set_option autoImplicit false
@[expose] public section

/-! Actual shared/private internal blocks retain both structural loop registers. -/

namespace JointThermoComplexity.Complexity.DenseInternalBlocks
open _root_.Complexity _root_.Complexity.TM BinaryIncrementRun
open HeaderAt (Cursor)
variable {w : ℕ}

structure Ports (w : ℕ) where
  comparison : SmallCoefficientMatch.Ports w
  count : Fin (w + 1)
  branch : Fin (w + 1)
  count_idx : count ≠ comparison.operand
  count_target : count ≠ comparison.constant
  count_flag : count ≠ comparison.flag
  branch_idx : branch ≠ comparison.operand
  branch_target : branch ≠ comparison.constant
  branch_flag : branch ≠ comparison.flag
  count_branch : count ≠ branch

def countPorts (d : Ports w) : IndicatorVectorLoop.Ports w :=
  ⟨d.comparison, d.count, d.count_idx, d.count_target, d.count_flag⟩
def branchPorts (d : Ports w) : IndicatorVectorLoop.Ports w :=
  ⟨d.comparison, d.branch, d.branch_idx, d.branch_target, d.branch_flag⟩

def Stable (d : Ports w) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ d.comparison.operand → j ≠ d.comparison.constant → j ≠ d.comparison.flag →
    j ≠ d.count → j ≠ d.branch → next j = work j) → R work → R next

def Frame (d : Ports w) (N : ℕ) (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape) : Prop :=
  IsReg N (work d.count) ∧ IsReg (N + 2) (work d.branch) ∧ R work

def Pre (d : Ports w) (N M i : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) :=
  IndicatorVectorUnit.Pre d.comparison i M before input emitted (Frame d N R)

theorem phase (d : Ports w) (N M i : ℕ) (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) :
    ∀ inp work out, Pre d N M i before input emitted R inp work out →
      Pre d N M i before input emitted R (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out hp
  obtain ⟨hi, hw, ho⟩ := hp.1.phase
  rw [hi, hw, ho]
  exact hp

theorem frame_stable (d : Ports w) (N : ℕ) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    IndicatorVectorUnit.Stable d.comparison (Frame d N R) := by
  rintro work next he ⟨hn, hb, hr⟩
  exact ⟨by rw [he d.count d.count_idx d.count_target d.count_flag]; exact hn,
    by rw [he d.branch d.branch_idx d.branch_target d.branch_flag]; exact hb,
    hR work next (fun j hi hm hf _ _ => he j hi hm hf) hr⟩

theorem branch_stable (d : Ports w) (N : ℕ) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    IndicatorVectorLoop.Stable (branchPorts d) (fun work => IsReg N (work d.count) ∧ R work) := by
  rintro work next he ⟨hn, hr⟩
  exact ⟨by rw [he d.count d.count_idx d.count_target d.count_flag d.count_branch]; exact hn,
    hR work next (fun j hi hm hf _ hb => he j hi hm hf hb) hr⟩

theorem count_stable (d : Ports w) (N : ℕ) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    IndicatorVectorLoop.Stable (countPorts d) (fun work => IsReg (N + 2) (work d.branch) ∧ R work) := by
  rintro work next he ⟨hb, hr⟩
  exact ⟨by rw [he d.branch d.branch_idx d.branch_target d.branch_flag d.count_branch.symm]; exact hb,
    hR work next (fun j hi hm hf hn _ => he j hi hm hf hn) hr⟩

def leftBefore (d : Ports w) (k : ℕ) : TM (w + 1) := ReusableIndicatorVector.machine (branchPorts d) k
def zeros (d : Ports w) : TM (w + 1) := RepeatedOutput.machine d.count (BitCodec.naturalCode 0)
def rightBefore (d : Ports w) (k : ℕ) : TM (w + 1) := seqTM (IndicatorFixedPair.machine d.comparison k) (zeros d)
def preparePrivate (d : Ports w) : TM (w + 1) := BinaryConstantAdd.machine 2 d.comparison.operand
def privateVector (d : Ports w) (k : ℕ) : TM (w + 1) := ReusableIndicatorVector.machine (countPorts d) k
def rightAfter (d : Ports w) (k : ℕ) : TM (w + 1) := seqTM (preparePrivate d) (privateVector d k)

def zeroBound (N : ℕ) : ℕ := N * ((BitCodec.naturalCode 0).length + 2) + (N + 2)
def leftBound (N B k : ℕ) : ℕ := ReusableIndicatorVector.bound (N + 2) (N + 2) B k
def rightBeforeBound (N B k : ℕ) : ℕ := IndicatorFixedPair.bound B k + 1 + zeroBound N
def rightAfterBound (N B k : ℕ) : ℕ := ReusableIndicatorVector.bound N (N + 2) B k + 19

theorem left_before_hoareTime (d : Ports w) (k N M B : ℕ) (hM : M.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    (leftBefore d k).HoareTime (Pre d N M 0 before input emitted R)
      (Pre d N M 0 before input (emitted ++ DenseBlockWords.leftBefore k M N) R) (leftBound N B k) := by
  have hh := ReusableIndicatorVector.hoareTime (branchPorts d) k M 0 (N + 2) (N + 2) B (by omega) hM before input emitted
    (fun work => IsReg N (work d.count) ∧ R work) (branch_stable d N R hR)
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hi, hm, hf, hn, hb, hr⟩
    exact ⟨⟨hc, hs, hi, hm, hf, hn, hr⟩, hb⟩
  · rintro inp work out ⟨⟨hc, hs, hi, hm, hf, hn, hr⟩, hb⟩
    exact ⟨hc, hs, hi, hm, hf, hn, hb, hr⟩
  · exact le_rfl

theorem zeros_hoareTime (d : Ports w) (N M i : ℕ) (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) :
    (zeros d).HoareTime (Pre d N M i before input emitted R)
      (Pre d N M i before input (emitted ++ DenseBlockWords.zeros N) R) (zeroBound N) := by
  let S : (Fin (w + 1) → Tape) → Prop := fun work => Register i (work d.comparison.operand) ∧
    Register M (work d.comparison.constant) ∧ (work d.comparison.flag).head = 1 ∧ IsReg (N + 2) (work d.branch) ∧ R work
  have hh := RepeatedOutput.hoareTime d.count N before input emitted (BitCodec.naturalCode 0) S
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hi, hm, hf, hn, hb, hr⟩
    exact ⟨hn, hc, hs, hi, hm, hf, hb, hr⟩
  · rintro inp work out ⟨hn, hc, hs, hi, hm, hf, hb, hr⟩
    exact ⟨hc, hs, hi, hm, hf, hn, hb, hr⟩
  · exact le_rfl

theorem right_before_hoareTime (d : Ports w) (k N M B : ℕ) (hM : M.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    (rightBefore d k).HoareTime (Pre d N M 0 before input emitted R)
      (Pre d N M 0 before input (emitted ++ DenseBlockWords.rightBefore k M N) R) (rightBeforeBound N B k) := by
  have hp := IndicatorFixedPair.hoareTime d.comparison k M B hM before input emitted (Frame d N R) (frame_stable d N R hR)
  have hz := zeros_hoareTime d N M 0 before input (emitted ++ IndicatorVectorControl.words k M 0 2) R
  have hh := seqTM_hoareTime _ _ hp (phase d N M 0 before input _ R) hz
  apply hh.consequence
  · exact fun _ _ _ hp => hp
  · intro inp work out hp
    simpa only [Pre, DenseBlockWords.rightBefore, List.append_assoc] using hp
  · exact le_rfl

theorem prepare_hoareTime (d : Ports w) (N M : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    (preparePrivate d).HoareTime (Pre d N M 0 before input emitted R) (Pre d N M 2 before input emitted R) 18 := by
  let S : (Fin (w + 1) → Tape) → Prop := fun work => Register M (work d.comparison.constant) ∧
    (work d.comparison.flag).head = 1 ∧ Frame d N R work
  have hS : BinaryIncrementFramed.Stable d.comparison.operand S := by
    rintro work next he ⟨hm, hf, hr⟩
    exact ⟨by rw [he d.comparison.constant d.comparison.separate.operands.symm]; exact hm,
      by rw [he d.comparison.flag d.comparison.separate.flagLeft]; exact hf,
      frame_stable d N R hR work next (fun j hj _ _ => he j hj) hr⟩
  exact BinaryConstantAdd.hoareTime 2 d.comparison.operand 0 before input emitted S hS

theorem private_hoareTime (d : Ports w) (k N M B : ℕ) (hM : M.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    (privateVector d k).HoareTime (Pre d N M 2 before input emitted R)
      (Pre d N M 0 before input (emitted ++ DenseBlockWords.rightAfter k M N) R)
      (ReusableIndicatorVector.bound N (N + 2) B k) := by
  have hh := ReusableIndicatorVector.hoareTime (countPorts d) k M 2 N (N + 2) B (by omega) hM before input emitted
    (fun work => IsReg (N + 2) (work d.branch) ∧ R work) (count_stable d N R hR)
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hi, hm, hf, hn, hb, hr⟩
    exact ⟨⟨hc, hs, hi, hm, hf, hb, hr⟩, hn⟩
  · rintro inp work out ⟨⟨hc, hs, hi, hm, hf, hb, hr⟩, hn⟩
    exact ⟨hc, hs, hi, hm, hf, hn, hb, hr⟩
  · exact le_rfl

theorem right_after_hoareTime (d : Ports w) (k N M B : ℕ) (hM : M.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    (rightAfter d k).HoareTime (Pre d N M 0 before input emitted R)
      (Pre d N M 0 before input (emitted ++ DenseBlockWords.rightAfter k M N) R) (rightAfterBound N B k) := by
  have hh := seqTM_hoareTime _ _ (prepare_hoareTime d N M before input emitted R hR)
    (phase d N M 2 before input emitted R) (private_hoareTime d k N M B hM before input emitted R hR)
  exact hh.mono_bound (by unfold rightAfterBound; omega)

end JointThermoComplexity.Complexity.DenseInternalBlocks

#print axioms JointThermoComplexity.Complexity.DenseInternalBlocks.left_before_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseInternalBlocks.right_before_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseInternalBlocks.right_after_hoareTime
