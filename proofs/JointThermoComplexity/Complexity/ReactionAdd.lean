module
public import proofs.JointThermoComplexity.Complexity.ReactionGateFrame
public import proofs.JointThermoComplexity.Complexity.AddGateStore

set_option autoImplicit false
@[expose] public section

/-! Add the saved reactant monomial to the negative product at a fresh gate. -/

namespace JointThermoComplexity.Complexity.ReactionAdd
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts ReactionGateFrame

def machine (m : ℕ) : TM (m + 15) :=
  AddGateStore.machine (resultPermutation (m + 1)) (nextOld (m + 2)) (scratchOld (m + 2)) (saved m) (previous (m + 1))

theorem hoareTime (m arity L : ℕ) (ha : arity ≤ 4 * L) (target prev keep : Fin arity)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ previous (m + 1) → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready m target.val prev.val keep.val R work)
      (fun inp work out => Cursor before input
        (emitted ++ (RealSyntax.Formula.eq (.var target) (.add (.var keep) (.var prev))).code) inp work out ∧
        Ready m (target.val + 1) target.val keep.val R work) (96 * L ^ 2 + 180 * L + 88) := by
  have ht : GateStore.next (resultPermutation (m + 1)) (nextOld (m + 2)) ≠
      GateStore.scratch (resultPermutation (m + 1)) (scratchOld (m + 2)) := by
    simpa only [result_next, result_scratch] using next_ne_scratch (m + 2)
  have hl : saved m ≠ GateStore.scratch (resultPermutation (m + 1)) (scratchOld (m + 2)) := by
    simpa only [result_scratch] using saved_ne_scratch m
  have hr : previous (m + 1) ≠ GateStore.scratch (resultPermutation (m + 1)) (scratchOld (m + 2)) := by
    simpa only [result_scratch] using previous_ne_scratch (m + 1)
  let P : (Fin (m + 15) → Tape) → Prop := fun work => IsReg keep.val (work (saved m)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ GateStore.next (resultPermutation (m + 1)) (nextOld (m + 2)) →
      j ≠ CountSumAt.destination (resultPermutation (m + 1)) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hs, hr⟩
    have hw' : ∀ j, j ≠ next (m + 2) → j ≠ previous (m + 1) → work' j = work j := by
      simpa only [result_next, result_destination] using hw
    exact ⟨by simpa only [hw' _ (saved_ne_next m) (saved_ne_previous m)] using hs, hR work work' hw' hr⟩
  have h := AddGateStore.hoareTime (resultPermutation (m + 1)) (nextOld (m + 2)) (scratchOld (m + 2))
    (saved m) (previous (m + 1)) ht hl hr (values m target prev keep) prev.val before input emitted P hP
  simp only [result_next, result_scratch, result_destination, values_next, values_previous, values_saved, P,
    BinaryGateOutput.formula, Bool.false_eq_true, ↓reduceIte] at h
  have hv : ∀ j, (values m target prev keep j).val ≤ 4 * L := fun j => (values m target prev keep j).isLt.le.trans ha
  have hb := GateStoreRuntime.bound (fun j => (values m target prev keep j).val) prev.val
    (next (m + 2)) (saved m) (previous (m + 1)) L (hv _) (hv _) (hv _) (prev.isLt.le.trans ha)
  exact h.consequence (by
    rintro inp work out ⟨hc, hs, hz, hn, hp, hk, hr⟩
    exact ⟨hc, hs, hz, hn, hk, hp, hp, hk, hr⟩) (fun _ _ _ hp => hp) hb

end JointThermoComplexity.Complexity.ReactionAdd

#print axioms JointThermoComplexity.Complexity.ReactionAdd.hoareTime
