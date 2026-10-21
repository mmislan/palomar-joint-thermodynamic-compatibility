module
public import proofs.JointThermoComplexity.Complexity.ReactionSelectionCode
public import proofs.JointThermoComplexity.Complexity.ReactionTableSkip

set_option autoImplicit false
@[expose] public section

/-! Reach one actual reaction record using a retained bounded position, preserving all work and output. -/

namespace JointThermoComplexity.Complexity.ReactionIndexedAccess
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ReactionCircuit ReactionSelectionCode

variable {w n r : ℕ}

abbrev machine (count position : Fin w) : TM w := ReactionListSkip.machine count position

theorem hoareTime (count position : Fin w) (hne : count ≠ position) (L : ℕ) (hr : r ≤ L)
    (values : Fin r → Reaction n) (i : Fin r) (hsize : ∀ j, ReactionSkip.Bounded L (values j))
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (machine count position).HoareTime
      (fun inp work out => Cursor before (code values ++ tail) emitted inp work out ∧
        IsReg i.val (work position) ∧ IsReg n (work count) ∧ R work out)
      (fun inp work out => Cursor (before ++ leading values i) ((DataCodec.reaction n).code (values i) ++ trailing values i ++ tail) emitted inp work out ∧
        IsReg i.val (work position) ∧ IsReg n (work count) ∧ R work out) (ReactionTableSkip.timeBound L) := by
  have hs : ∀ q ∈ (List.ofFn values).take i.val, ReactionSkip.Bounded L q := by
    intro q hq
    have hm : q ∈ List.ofFn values := List.mem_of_mem_take hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hm
    exact hsize j
  have h := ReactionListSkip.hoareTime count position hne L ((List.ofFn values).take i.val) hs before
    ((DataCodec.reaction n).code (values i) ++ trailing values i ++ tail) emitted R
  exact h.consequence (by
    intro inp work out h
    simpa only [ReactionSelectionCode.split values i, leading, List.append_assoc, leading_count] using h)
    (by intro inp work out h; simpa only [leading, leading_count] using h)
    (by rw [leading_count]; exact ReactionTableSkip.runtime_bound L i.val (by omega))

end JointThermoComplexity.Complexity.ReactionIndexedAccess

#print axioms JointThermoComplexity.Complexity.ReactionIndexedAccess.hoareTime
