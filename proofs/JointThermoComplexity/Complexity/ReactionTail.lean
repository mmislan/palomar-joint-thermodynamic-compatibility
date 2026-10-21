module
public import proofs.JointThermoComplexity.Complexity.ReactionArithmetic
public import proofs.JointThermoComplexity.Complexity.NaturalSkip

set_option autoImplicit false
@[expose] public section

/-! Emit the reaction's four arithmetic gates and consume its positive-denominator field read only. -/

namespace JointThermoComplexity.Complexity.ReactionTail
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts ReactionGateFrame

def machine (m : ℕ) : TM (m + 15) := seqTM (ReactionArithmetic.machine m) NaturalSkip.machine

theorem hoareTime (m arity L : ℕ) (ha : arity ≤ 4 * L) (target prev keep : Fin arity)
    (num den : ℕ) (room : target.val + 3 < arity)
    (hn : (BitCodec.naturalCode num).length ≤ L) (hd : (BitCodec.naturalCode den).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ previous (m + 1) → j ≠ saved m →
      work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before ((BitCodec.naturalCode num ++ BitCodec.naturalCode den) ++ tail) emitted inp work out ∧
        Ready m target.val prev.val keep.val R work)
      (fun inp work out => Cursor (before ++ (BitCodec.naturalCode num ++ BitCodec.naturalCode den)) tail
        (emitted ++ ReactionArithmetic.word target prev keep num room) inp work out ∧
        Ready m (target.val + 4) (target.val + 3) (target.val + 2) R work)
      (288 * L ^ 2 + 578 * L + 303) := by
  have ha := ReactionArithmetic.hoareTime m arity L ha target prev keep num room hn
    before (BitCodec.naturalCode den ++ tail) emitted R hR
  have hs := NaturalSkip.hoareTime den (before ++ BitCodec.naturalCode num) tail
    (emitted ++ ReactionArithmetic.word target prev keep num room)
    (Ready m (target.val + 4) (target.val + 3) (target.val + 2) R)
  have hseq := seqTM_hoareTime (ReactionArithmetic.machine m) NaturalSkip.machine ha (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr.1, hr⟩) hs
  exact hseq.consequence (by
    intro inp work out hp
    rw [List.append_assoc] at hp
    exact hp) (by
    rintro inp work out ⟨hc, _, hr⟩
    rw [List.append_assoc] at hc
    exact ⟨hc, hr⟩) (by omega)

end JointThermoComplexity.Complexity.ReactionTail

#print axioms JointThermoComplexity.Complexity.ReactionTail.hoareTime
