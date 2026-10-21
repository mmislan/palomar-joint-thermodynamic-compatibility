module
public import proofs.JointThermoComplexity.Complexity.ReactionGateFrame
public import proofs.JointThermoComplexity.Complexity.NatConstantStore

set_option autoImplicit false
@[expose] public section

/-! Copy the actual binary numerator into its constant gate and retain the difference reference. -/

namespace JointThermoComplexity.Complexity.ReactionCoefficient
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts ReactionGateFrame RealSyntax

def machine (m : ℕ) : TM (m + 15) :=
  NatConstantStore.machine (savedPermutation m) (nextOld (m + 2)) (scratchOld (m + 2))

theorem hoareTime (m arity L : ℕ) (ha : arity ≤ 4 * L) (target prev keep : Fin arity) (value : ℕ)
    (hv : (BitCodec.naturalCode value).length ≤ L) (before tail emitted : List Bool)
    (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ saved m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧
        Ready m target.val prev.val keep.val R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail
        (emitted ++ (Formula.eq (.var target) (.int (value : ℤ))).code) inp work out ∧
        Ready m (target.val + 1) prev.val target.val R work) (32 * L ^ 2 + 85 * L + 54) := by
  have ht : GateStore.next (savedPermutation m) (nextOld (m + 2)) ≠
      GateStore.scratch (savedPermutation m) (scratchOld (m + 2)) := by
    simpa only [saved_next, saved_scratch] using next_ne_scratch (m + 2)
  let P : (Fin (m + 15) → Tape) → Prop := fun work => IsReg prev.val (work (previous (m + 1))) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ GateStore.next (savedPermutation m) (nextOld (m + 2)) →
      j ≠ CountSumAt.destination (savedPermutation m) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hp, hr⟩
    have hw' : ∀ j, j ≠ next (m + 2) → j ≠ saved m → work' j = work j := by
      simpa only [saved_next, saved_destination] using hw
    exact ⟨by simpa only [hw' _ (previous_ne_next (m + 1)) (saved_ne_previous m).symm] using hp,
      hR work work' hw' hr⟩
  have h := NatConstantStore.hoareTime (savedPermutation m) (nextOld (m + 2)) (scratchOld (m + 2)) ht
    target keep.val value before tail emitted P hP
  simp only [saved_next, saved_scratch, saved_destination, P] at h
  exact h.consequence (by
    rintro inp work out ⟨hc, hs, hz, hn, hp, hk, hr⟩
    exact ⟨hc, hs, hz, hn, hk, hp, hr⟩) (by
    rintro inp work out ⟨hc, hs, hz, hn, hk, hp, hr⟩
    exact ⟨hc, hs, hz, hn, hp, hk, hr⟩)
    (NatConstantStore.runtime_bound keep.val target.val value L (keep.isLt.le.trans ha) (target.isLt.le.trans ha) hv)

end JointThermoComplexity.Complexity.ReactionCoefficient

#print axioms JointThermoComplexity.Complexity.ReactionCoefficient.hoareTime
