module
public import proofs.JointThermoComplexity.Complexity.ProductionFrame

set_option autoImplicit false
@[expose] public section

/-! Actual original-input operand loading in the fixed production layout, retaining arithmetic and loop resources. -/

namespace JointThermoComplexity.Complexity.ProductionOperandLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts BoxBufferState ReactionCircuit

variable {n : ℕ}

structure State (m L n ri si : ℕ) (work : Fin (m + 20) → Tape) : Prop where
  safe : ∀ j, Parked (work j)
  productReusable : Reusable L (work (left m))
  reactantReusable : Reusable L (work (right m))
  magnitudeReusable : Reusable L (work (magnitude m))
  signHead : (work (sign m)).head = 1
  speciesPosition : IsReg si (work (species m))
  speciesCount : IsReg n (work (count m))
  reactionPosition : IsReg ri (work (reaction m))

structure Prepared (m L ri : ℕ) (q : Reaction n) (s : Fin n) (work : Fin (m + 20) → Tape) : Prop where
  operands : ReactionOperandsLoad.Loaded (left m) (right m) (count m) (reaction m) (species m) L ri q s work
  magnitudeReusable : Reusable L (work (magnitude m))
  signHead : (work (sign m)).head = 1

def machine (m : ℕ) : TM (m + 20) := ReactionOperandsLoad.machine (left m) (right m) (count m) (reaction m) (species m)

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', ProductionFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m input.length Q.speciesCount i.val s.val work ∧ R work)
      (fun inp work out => Cursor (DecodedReactionFieldLoad.atPrefix Q i s true) (DecodedReactionFieldLoad.atSuffix Q i s true) emitted inp work out ∧
        Prepared m input.length i.val (Q.network.reactions i) s work ∧ R work) (ReactionOperandsLoad.timeBound input.length) := by
  let R' : (Fin (m + 20) → Tape) → Prop := fun work => Reusable input.length (work (magnitude m)) ∧ (work (sign m)).head = 1 ∧ R work
  have hR' : ∀ work work', (∀ j, j ≠ left m → j ≠ right m → work' j = work j) → R' work → R' work' := by
    rintro work work' hw ⟨hm, hs, hr⟩
    have hml : magnitude m ≠ left m := by intro h; have hv := congrArg Fin.val h; change (8 : ℕ) = 9 at hv; omega
    have hmr : magnitude m ≠ right m := by intro h; have hv := congrArg Fin.val h; change (8 : ℕ) = 10 at hv; omega
    have hsl : sign m ≠ left m := by intro h; have hv := congrArg Fin.val h; change (11 : ℕ) = 9 at hv; omega
    have hsr : sign m ≠ right m := by intro h; have hv := congrArg Fin.val h; change (11 : ℕ) = 10 at hv; omega
    exact ⟨by simpa only [hw (magnitude m) hml hmr] using hm,
      by simpa only [hw (sign m) hsl hsr] using hs,
      hR work work' (fun j hl hr _ _ => hw j hl hr) hr⟩
  have h := ReactionOperandsLoad.hoareTime (left m) (right m) (count m) (reaction m) (species m) (operand_separate m)
    input Q hd i s before remaining emitted hsplit R' hR'
  exact h.consequence (by
    rintro inp work out ⟨hc, hp, hr⟩
    exact ⟨hc, hp.safe, hp.productReusable, hp.reactantReusable, hp.reactionPosition, hp.speciesPosition, hp.speciesCount,
      hp.magnitudeReusable, hp.signHead, hr⟩) (by
        rintro inp work out ⟨hc, hp, hm, hs, hr⟩
        exact ⟨hc, ⟨hp, hm, hs⟩, hr⟩) le_rfl

end JointThermoComplexity.Complexity.ProductionOperandLoad

#print axioms JointThermoComplexity.Complexity.ProductionOperandLoad.hoareTime
