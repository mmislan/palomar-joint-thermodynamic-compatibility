module
public import proofs.JointThermoComplexity.Complexity.ReactionGateFrame
public import proofs.JointThermoComplexity.Complexity.UnaryGateStore
public import proofs.JointThermoComplexity.Complexity.TemplateRuntime

set_option autoImplicit false
@[expose] public section

/-! Negate the product monomial at the next gate and retain the saved reactant reference. -/

namespace JointThermoComplexity.Complexity.ReactionNegate
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts ReactionGateFrame

def machine (m : ℕ) : TM (m + 15) :=
  UnaryGateStore.machine true (resultPermutation (m + 1)) (nextOld (m + 2)) (scratchOld (m + 2)) (previous (m + 1))

theorem hoareTime (m arity L : ℕ) (ha : arity ≤ 4 * L) (target prev keep : Fin arity)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ previous (m + 1) → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready m target.val prev.val keep.val R work)
      (fun inp work out => Cursor before input
        (emitted ++ (RealSyntax.Formula.eq (.var target) (.neg (.var prev))).code) inp work out ∧
        Ready m (target.val + 1) target.val keep.val R work) (64 * L ^ 2 + 132 * L + 69) := by
  have ht : GateStore.next (resultPermutation (m + 1)) (nextOld (m + 2)) ≠
      GateStore.scratch (resultPermutation (m + 1)) (scratchOld (m + 2)) := by
    simpa only [result_next, result_scratch] using next_ne_scratch (m + 2)
  have hp : previous (m + 1) ≠ GateStore.scratch (resultPermutation (m + 1)) (scratchOld (m + 2)) := by
    simpa only [result_scratch] using previous_ne_scratch (m + 1)
  let P : (Fin (m + 15) → Tape) → Prop := fun work => IsReg keep.val (work (saved m)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ GateStore.next (resultPermutation (m + 1)) (nextOld (m + 2)) →
      j ≠ CountSumAt.destination (resultPermutation (m + 1)) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hs, hr⟩
    have hw' : ∀ j, j ≠ next (m + 2) → j ≠ previous (m + 1) → work' j = work j := by
      simpa only [result_next, result_destination] using hw
    exact ⟨by simpa only [hw' _ (saved_ne_next m) (saved_ne_previous m)] using hs, hR work work' hw' hr⟩
  have h := UnaryGateStore.hoareTime true (resultPermutation (m + 1)) (nextOld (m + 2)) (scratchOld (m + 2))
    (previous (m + 1)) ht hp (values m target prev keep) prev.val before input emitted P hP
  simp only [result_next, result_scratch, result_destination, values_next, values_previous, P,
    UnaryGateOutput.formula, ↓reduceIte] at h
  have hb := TemplateRuntime.unary_bound (fun j => (values m target prev keep j).val)
    (next (m + 2)) (previous (m + 1)) L
    (by simp only [values_next]; exact target.isLt.le.trans ha)
    (by simp only [values_previous]; exact prev.isLt.le.trans ha)
  apply h.consequence
  · rintro inp work out ⟨hc, hs, hz, hn, hp, hk, hr⟩
    exact ⟨hc, hs, hz, hn, hp, hp, hk, hr⟩
  · exact fun _ _ _ hp => hp
  · change UnaryGateOutput.timeBound (fun j : Fin (m + 15) => (values m target prev keep j).val)
      (next (m + 2)) (previous (m + 1)) + 2 * prev.val + 7 * target.val + 23 ≤ _
    have hprev := prev.isLt
    have htarget := target.isLt
    omega

end JointThermoComplexity.Complexity.ReactionNegate

#print axioms JointThermoComplexity.Complexity.ReactionNegate.hoareTime
