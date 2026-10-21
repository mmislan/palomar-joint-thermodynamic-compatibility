module
public import proofs.JointThermoComplexity.Complexity.ReactionGateFrame
public import proofs.JointThermoComplexity.Complexity.PowerGateStore
public import proofs.JointThermoComplexity.Complexity.GateStoreRuntime

set_option autoImplicit false
@[expose] public section

/-! Multiply the literal difference by the runtime numerator and retain its output address. -/

namespace JointThermoComplexity.Complexity.ReactionMultiply
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts ReactionGateFrame

def machine (m : ℕ) : TM (m + 15) :=
  GateStore.machine (resultPermutation (m + 1)) (nextOld (m + 2)) (scratchOld (m + 2)) (previous (m + 1)) (saved m)

theorem hoareTime (m arity L : ℕ) (ha : arity ≤ 4 * L) (target prev keep : Fin arity)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ previous (m + 1) → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready m target.val prev.val keep.val R work)
      (fun inp work out => Cursor before input (emitted ++ BinaryPowerCode.multiply target prev keep) inp work out ∧
        Ready m (target.val + 1) target.val keep.val R work) (96 * L ^ 2 + 180 * L + 88) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work => IsReg keep.val (work (saved m)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ previous (m + 1) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hk, hr⟩
    exact ⟨by simpa only [hw _ (saved_ne_next m) (saved_ne_previous m)] using hk, hR work work' hw hr⟩
  have h := PowerGateStore.hoareTime (m + 2) (resultPermutation (m + 1)) (nextOld (m + 2)) (scratchOld (m + 2))
    (previous (m + 1)) (previous (m + 1)) (saved m) (result_next (m + 1)) (result_scratch (m + 1))
    (result_destination (m + 1)) (previous_ne_scratch (m + 1)) (saved_ne_scratch m)
    (values m target prev keep) prev.val before input emitted P hP
  simp only [values_next, values_previous, values_saved, P, GateStoreCircuit.code_eq] at h
  have hv : ∀ j, (values m target prev keep j).val ≤ 4 * L := fun j => (values m target prev keep j).isLt.le.trans ha
  have hb := GateStoreRuntime.bound (fun j => (values m target prev keep j).val) prev.val
    (next (m + 2)) (previous (m + 1)) (saved m) L (hv _) (hv _) (hv _) (prev.isLt.le.trans ha)
  exact h.consequence (by
    rintro inp work out ⟨hc, hs, hz, hn, hp, hk, hr⟩
    exact ⟨hc, hs, hz, hn, hp, hk, hp, hk, hr⟩) (fun _ _ _ hp => hp) hb

end JointThermoComplexity.Complexity.ReactionMultiply

#print axioms JointThermoComplexity.Complexity.ReactionMultiply.hoareTime
