module
public import proofs.JointThermoComplexity.Complexity.PowerVectorControl
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementFramed
public import proofs.JointThermoComplexity.Complexity.BoundedUnaryControl

set_option autoImplicit false
@[expose] public section

/-! An actual binary-reference power cell followed by a retained binary index increment. -/

namespace JointThermoComplexity.Complexity.PowerVectorUnit
open _root_.Complexity _root_.Complexity.TM BinaryIncrementRun
open HeaderAt (Cursor)
open SmallCoefficientMatch (Ports)
open PowerVectorControl (Layout)
variable {w : ℕ}

def Stable (d : Layout w) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ d.idx → (∀ p ∈ d.comparisons, j ≠ p.flag) → next j = work j) → R work → R next

def Refs (d : Layout w) (values : Fin (w + 1) → ℕ) (work : Fin (w + 1) → Tape) : Prop :=
  ∀ p ∈ d.comparisons, Register (values p.constant) (work p.constant) ∧ (work p.flag).head = 1

def Pre (d : Layout w) (values : Fin (w + 1) → ℕ) (i : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register i (work d.idx) ∧ Refs d values work ∧ R work

def machine (d : Layout w) (weights : Ports w → ℕ) : TM (w + 1) :=
  seqTM (PowerCellEmit.machine d.comparisons weights) (BinaryIncrementMachine.machine d.idx)

def bound (T B : ℕ) : ℕ := 98 * T + 96 * B + 111

theorem hoareTime (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ) (i T B : ℕ)
    (hi : i ≤ T) (hbits : ∀ p ∈ d.comparisons, (values p.constant).bits.length ≤ B)
    (hcount : d.comparisons.length ≤ 4) (hweight : PowerCellWord.weight (PowerCellEmit.items d.comparisons weights) ≤ 4)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable d R) :
    (machine d weights).HoareTime (Pre d values i before input emitted R)
      (Pre d values (i + 1) before input (emitted ++ BitCodec.naturalCode (PowerVectorControl.cell d weights values i)) R)
      (bound T B) := by
  let v := Function.update values d.idx i
  let C : (Fin (w + 1) → Tape) → Prop := fun work => Register i (work d.idx) ∧ R work
  have hC : PowerCellCompare.Stable d.comparisons C := by
    rintro work next he ⟨hr, hx⟩
    exact ⟨by rw [he d.idx (fun p hp => (PowerVectorControl.flag_ne_idx d p hp).symm)]; exact hr,
      hR work next (fun j _ hj => he j hj) hx⟩
  have hB : ∀ p ∈ d.comparisons, (v p.operand).bits.length ≤ T + B ∧ (v p.constant).bits.length ≤ T + B := by
    intro p hp
    dsimp only [v]
    rw [d.operand_eq p hp, Function.update_self, Function.update_of_ne (PowerVectorControl.constant_ne_idx d p hp)]
    have hh := (BoundedUnaryControl.bits_le i).trans hi
    have hm := hbits p hp
    constructor <;> omega
  have he := PowerReferenceEmit.degree_four_hoareTime d.comparisons weights v (T + B)
    d.separated d.unique hB hcount hweight before input emitted C hC
  let S : (Fin (w + 1) → Tape) → Prop := fun work => Refs d values work ∧ R work
  have hS : BinaryIncrementFramed.Stable d.idx S := by
    rintro work next hsame ⟨hr, hx⟩
    refine ⟨?_, hR work next (fun j hj _ => hsame j hj) hx⟩
    intro p hp
    rw [hsame p.constant (PowerVectorControl.constant_ne_idx d p hp), hsame p.flag (PowerVectorControl.flag_ne_idx d p hp)]
    exact hr p hp
  have ht := BinaryIncrementFramed.bounded_hoareTime d.idx i T ((BoundedUnaryControl.bits_le i).trans hi)
    before input (emitted ++ BitCodec.naturalCode (PowerVectorControl.cell d weights values i)) S hS
  have hh := seqTM_hoareTime _ _ he (by
    rintro inp work out ⟨hc, hs, hr, _, hi, hx⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    refine ⟨?_, hs, hi, ?_, hx⟩
    · simpa only [v, ← PowerVectorControl.cell_eq_power] using hc
    · intro p hp
      have hpready := hr p hp
      simpa only [v, Function.update_of_ne (PowerVectorControl.constant_ne_idx d p hp)] using hpready.2) ht
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hi, hr, hx⟩
    refine ⟨hc, hs, ?_, hi, hx⟩
    intro p hp
    have hpref := hr p hp
    dsimp only [v]
    rw [d.operand_eq p hp, Function.update_self, Function.update_of_ne (PowerVectorControl.constant_ne_idx d p hp)]
    exact ⟨hi, hpref⟩
  · exact fun _ _ _ hp => hp
  · unfold bound
    omega

end JointThermoComplexity.Complexity.PowerVectorUnit

#print axioms JointThermoComplexity.Complexity.PowerVectorUnit.hoareTime
