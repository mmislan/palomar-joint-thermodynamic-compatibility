module
public import proofs.JointThermoComplexity.Complexity.BoundedUnaryControl
public import proofs.JointThermoComplexity.Complexity.BinaryCompareRewind
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementFramed
public import proofs.JointThermoComplexity.Complexity.WorkSymbolBranch

set_option autoImplicit false
@[expose] public section

/-! Compare a real binary index/count, append a static word, increment index. -/

namespace JointThermoComplexity.Complexity.BoundedUnaryUnit
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
variable {w : ℕ}

structure Ports (w : ℕ) where
  idx : Fin w
  value : Fin w
  flag : Fin w
  fuel : Fin w
  idx_value : idx ≠ value
  flag_idx : flag ≠ idx
  flag_value : flag ≠ value
  fuel_idx : fuel ≠ idx
  fuel_value : fuel ≠ value
  fuel_flag : fuel ≠ flag

def Stable (d : Ports w) (R : (Fin w → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ d.idx → j ≠ d.value → j ≠ d.flag → next j = work j) → R work → R next

def Fields (d : Ports w) (i N : ℕ) (R : (Fin w → Tape) → Prop) (work : Fin w → Tape) : Prop :=
  Register i (work d.idx) ∧ Register N (work d.value) ∧ (work d.flag).head = 1 ∧ R work

def Inv (d : Ports w) (N : ℕ) (before input emitted word : List Bool)
    (R : (Fin w → Tape) → Prop) (i : ℕ) : _root_.Complexity.TM.TapePred w := fun inp work out =>
  Cursor before input (emitted ++ RepeatedOutput.copies word (min i N)) inp work out ∧
    (∀ j, Parked (work j)) ∧ Fields d i N R work

def branch (d : Ports w) (word : List Bool) : TM w :=
  WorkSymbolBranch.machine Γ.one d.flag (emitBitsTM word) (emitBitsTM [])

def machine (d : Ports w) (word : List Bool) : TM w :=
  seqTM (seqTM (BinaryCompareRewind.machine d.idx d.value d.flag) (branch d word))
    (BinaryIncrementMachine.machine d.idx)

def bound (C : ℕ) (word : List Bool) : ℕ := 5 * C + word.length + 18

theorem branch_hoareTime (d : Ports w) (word : List Bool) (i N : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (branch d word).HoareTime
      (fun inp work out => (Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work) ∧
        (work d.flag).read = Γ.ofBool (decide (i < N)))
      (fun inp work out => Cursor before input (emitted ++ BoundedUnaryControl.selected i N word) inp work out ∧
        (∀ j, Parked (work j)) ∧ R work) (word.length + 2) := by
  by_cases hi : i < N
  · have hf := FixedOutput.hoareTime word before input emitted R
    have hb := WorkSymbolBranch.yes_hoareTime Γ.one d.flag (emitBitsTM word) (emitBitsTM [])
      before input emitted before input (emitted ++ word) (fun work => (∀ j, Parked (work j)) ∧ R work)
      (fun work => (∀ j, Parked (work j)) ∧ R work) word.length hf
    apply hb.consequence
    · rintro inp work out ⟨hp, hh⟩
      exact ⟨hp, by simpa only [hi, decide_true, Γ.ofBool] using hh⟩
    · intro inp work out hp
      simpa only [BoundedUnaryControl.selected, ite_eq_left hi] using hp
    · omega
  · have hf := FixedOutput.hoareTime [] before input emitted R
    have hb := WorkSymbolBranch.no_hoareTime Γ.one d.flag (emitBitsTM word) (emitBitsTM [])
      before input emitted before input (emitted ++ []) (fun work => (∀ j, Parked (work j)) ∧ R work)
      (fun work => (∀ j, Parked (work j)) ∧ R work) 0 hf
    apply hb.consequence
    · rintro inp work out ⟨hp, hh⟩
      exact ⟨hp, by rw [hh]; simp [hi, Γ.ofBool]⟩
    · intro inp work out hp
      simpa only [BoundedUnaryControl.selected, ite_eq_right hi] using hp
    · omega

theorem hoareTime (d : Ports w) (word : List Bool) (i N C : ℕ)
    (hi : i.bits.length ≤ C) (hN : N.bits.length ≤ C)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : Stable d R) :
    (machine d word).HoareTime (Inv d N before input emitted word R i)
      (Inv d N before input emitted word R (i + 1)) (bound C word) := by
  let ys := emitted ++ RepeatedOutput.copies word (min i N)
  have hc := BinaryCompareRewind.hoareTime d.idx d.value d.flag ⟨d.idx_value, d.flag_idx, d.flag_value⟩
    i.bits N.bits before input ys R hR
  have hb := branch_hoareTime d word i N before input ys (Fields d i N R)
  have hcb := seqTM_hoareTime _ _ hc (by
    rintro inp work out ⟨hc, ⟨hs, hh, hn, hz, hnz, hfh⟩, hv, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨⟨hc, hs, ⟨hh, hz⟩, ⟨hn, hnz⟩, hfh, hr⟩,
      by simpa only [BoundedUnaryControl.borrow_bits] using hv⟩) hb
  let T : (Fin w → Tape) → Prop := fun work => Register N (work d.value) ∧ (work d.flag).head = 1 ∧ R work
  have hT : BinaryIncrementFramed.Stable d.idx T := by
    rintro work next he ⟨hn, hh, hr⟩
    exact ⟨by rw [he d.value d.idx_value.symm]; exact hn,
      by rw [he d.flag d.flag_idx]; exact hh, hR work next (fun j hj _ _ => he j hj) hr⟩
  have hin := BinaryIncrementFramed.hoareTime d.idx i before input (ys ++ BoundedUnaryControl.selected i N word) T hT
  have hall := seqTM_hoareTime _ _ hcb (by
    rintro inp work out ⟨hc, hs, hi, hn, hh, hr⟩
    obtain ⟨hinput, hwork, hout⟩ := hc.phase
    rw [hinput, hwork, hout]
    exact ⟨hc, hs, hi, hn, hh, hr⟩) hin
  apply hall.consequence
  · rintro inp work out ⟨hc, hs, hi, hn, hh, hr⟩
    exact ⟨hc, ⟨hs, hi.1, hn.1, hi.2, hn.2, hh⟩, hr⟩
  · rintro inp work out ⟨hc, hs, hi, hn, hh, hr⟩
    rw [BoundedUnaryControl.copies_concat] at hc
    exact ⟨hc, hs, hi, hn, hh, hr⟩
  · have hm : max i.bits.length N.bits.length ≤ C := max_le hi hN
    unfold bound BinaryCompareRewind.timeBound
    omega

end JointThermoComplexity.Complexity.BoundedUnaryUnit

#print axioms JointThermoComplexity.Complexity.BoundedUnaryUnit.machine
#print axioms JointThermoComplexity.Complexity.BoundedUnaryUnit.hoareTime
