module
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceRuntime
public import proofs.JointThermoComplexity.Complexity.BinaryPrefixRewind

set_option autoImplicit false
@[expose] public section

/-! Compare two binary operands, store the real borrow bit, and restore both operand heads. -/

namespace JointThermoComplexity.Complexity.BinaryCompareRewind
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryDifferenceCursor BinaryDifferenceRuntime

variable {w : ℕ}

def machine (left right flag : Fin w) : TM w :=
  seqTM (seqTM (BinaryDifferenceMachine.machine left right flag false) (rewindWorkTM left)) (rewindWorkTM right)

def timeBound (xs ys : List Bool) : ℕ := max xs.length ys.length + xs.length + ys.length + 9

theorem hoareTime (left right flag : Fin w) (sep : Separate left right flag)
    (xs ys before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ flag → work' j = work j) → R work → R work') :
    (machine left right flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Start left right flag xs ys work ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ Start left right flag xs ys work ∧
        (work flag).read = Γ.ofBool (BinaryDifference.subtract xs ys false).2 ∧ R work) (timeBound xs ys) := by
  let R₁ : (Fin w → Tape) → Prop := fun work => (work right).HasBinaryPrefix ys ∧
    (work right).cells 0 = Γ.start ∧ (work flag).head = 1 ∧
    (work flag).read = Γ.ofBool (BinaryDifference.subtract xs ys false).2 ∧ R work
  have hR₁ : ∀ work work', (∀ j, j ≠ left → work' j = work j) → R₁ work → R₁ work' := by
    rintro work work' hw ⟨hr, hz, hh, hv, hrest⟩
    refine ⟨?_, ?_, ?_, ?_, hR work work' (fun j hj _ _ => hw j hj) hrest⟩
    · simpa only [hw right sep.operands.symm] using hr
    · simpa only [hw right sep.operands.symm] using hz
    · simpa only [hw flag sep.flagLeft] using hh
    · simpa only [hw flag sep.flagLeft] using hv
  let R₂ : (Fin w → Tape) → Prop := fun work => (work left).HasBinaryString xs ∧
    (work left).cells 0 = Γ.start ∧ (work flag).head = 1 ∧
    (work flag).read = Γ.ofBool (BinaryDifference.subtract xs ys false).2 ∧ R work
  have hR₂ : ∀ work work', (∀ j, j ≠ right → work' j = work j) → R₂ work → R₂ work' := by
    rintro work work' hw ⟨hl, hz, hh, hv, hrest⟩
    refine ⟨?_, ?_, ?_, ?_, hR work work' (fun j _ hj _ => hw j hj) hrest⟩
    · simpa only [hw left sep.operands] using hl
    · simpa only [hw left sep.operands] using hz
    · simpa only [hw flag sep.flagRight] using hh
    · simpa only [hw flag sep.flagRight] using hv
  have hc := BinaryDifferenceRuntime.hoareTime left right flag sep false xs ys before input emitted R hR
  have hl := BinaryPrefixRewind.hoareTime left xs before input emitted R₁ hR₁
  have hr := BinaryPrefixRewind.hoareTime right ys before input emitted R₂ hR₂
  have hcl := seqTM_hoareTime (BinaryDifferenceMachine.machine left right flag false) (rewindWorkTM left) hc (by
    rintro inp work out ⟨hc, hp, hrest⟩
    have hc' : Cursor before input emitted inp work out := by
      simpa only [Bool.false_eq_true, ↓reduceIte, List.append_nil] using hc
    obtain ⟨hi, hw, ho⟩ := hc'.phase
    rw [hi, hw, ho]
    exact ⟨hc', hp.safe, hp.lhs, hp.lhsZero, hp.rhs, hp.rhsZero, hp.flagHead, hp.flagValue rfl, hrest⟩) hl
  have hfull := seqTM_hoareTime
    (seqTM (BinaryDifferenceMachine.machine left right flag false) (rewindWorkTM left)) (rewindWorkTM right) hcl (by
      rintro inp work out ⟨hc, hs, hl, hz, hr, hrz, hh, hv, hrest⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, hr, hrz, hl, hz, hh, hv, hrest⟩) hr
  exact hfull.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hs, hr, hrz, hl, hlz, hh, hv, hrest⟩
    exact ⟨hc, ⟨hs, hl, hr, hlz, hrz, hh⟩, hv, hrest⟩) (by unfold timeBound; omega)

end JointThermoComplexity.Complexity.BinaryCompareRewind

#print axioms JointThermoComplexity.Complexity.BinaryCompareRewind.hoareTime
