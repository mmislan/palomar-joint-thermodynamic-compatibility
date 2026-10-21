module
public import proofs.JointThermoComplexity.Complexity.ProductionOperandLoad
public import proofs.JointThermoComplexity.Complexity.ProductionArithmetic

set_option autoImplicit false
@[expose] public section

/-! Original-input operand loading, bounded magnitude reset and exact signed coefficient output form one reusable machine. -/

namespace JointThermoComplexity.Complexity.ProductionCoefficient
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts BoxBufferState ReactionCircuit

variable {n : ℕ}

def Indices (m n ri si : ℕ) (work : Fin (m + 20) → Tape) : Prop :=
  IsReg si (work (species m)) ∧ IsReg n (work (count m)) ∧ IsReg ri (work (reaction m))

theorem clear_hoareTime (m L ri : ℕ) (q : Reaction n) (s : Fin n) (before remaining emitted : List Bool)
    (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', ProductionFrame.Unchanged m work work' → R work → R work') :
    (BinaryBufferReset.machine (magnitude m)).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionOperandLoad.Prepared m L ri q s work ∧ R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionArithmetic.Ready m q s work ∧
        Indices m n ri s.val work ∧ R work) (12 * L + 9) := by
  rintro inp work out ⟨hc, hp, hr⟩
  obtain ⟨old, hold, hcontent, hz, hhead⟩ := hp.magnitudeReusable
  let P : (Fin (m + 20) → Tape) → Prop := fun work' => ∀ j, j ≠ magnitude m → work' j = work j
  have hP : ∀ work' work'', (∀ j, j ≠ magnitude m → work'' j = work' j) → P work' → P work'' := by
    intro work' work'' hw hp j hj
    exact (hw j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hd, hh, hc', hs, he, hw⟩ := BinaryBufferReset.hoareTime (magnitude m) old before remaining emitted P hP
    inp work out ⟨hc, hp.operands.safe, hcontent, hz, hhead, fun _ _ => rfl⟩
  have hl : left m ≠ magnitude m := by intro h; have hv := congrArg Fin.val h; change (9 : ℕ) = 8 at hv; omega
  have hright : right m ≠ magnitude m := by intro h; have hv := congrArg Fin.val h; change (10 : ℕ) = 8 at hv; omega
  have hsign : sign m ≠ magnitude m := by intro h; have hv := congrArg Fin.val h; change (11 : ℕ) = 8 at hv; omega
  have hspecies : species m ≠ magnitude m := by intro h; have hv := congrArg Fin.val h; change (12 : ℕ) = 8 at hv; omega
  have hcount : count m ≠ magnitude m := by intro h; have hv := congrArg Fin.val h; change m + 15 = 8 at hv; omega
  have hreaction : reaction m ≠ magnitude m := by intro h; have hv := congrArg Fin.val h; change (6 : ℕ) = 8 at hv; omega
  have hready : ProductionArithmetic.Ready m q s d.work :=
    ⟨hs, by simpa only [hw (left m) hl] using hp.operands.productString,
      by simpa only [hw (right m) hright] using hp.operands.reactantString,
      by simpa only [hw (left m) hl] using hp.operands.productZero,
      by simpa only [hw (right m) hright] using hp.operands.reactantZero,
      by simpa only [hw (sign m) hsign] using hp.signHead, CountTape.empty_prefix_of_zero he, he.cell0⟩
  have hindices : Indices m n ri s.val d.work :=
    ⟨by simpa only [hw (species m) hspecies] using hp.operands.speciesPosition,
      by simpa only [hw (count m) hcount] using hp.operands.speciesCount,
      by simpa only [hw (reaction m) hreaction] using hp.operands.reactionPosition⟩
  exact ⟨d, t, by omega, hd, hh, hc', hready, hindices, hR work d.work (fun j _ _ _ hj => hw j hj) hr⟩

def machine (m : ℕ) : TM (m + 20) := seqTM
  (seqTM (ProductionOperandLoad.machine m) (BinaryBufferReset.machine (magnitude m))) (ProductionArithmetic.machine m)

def timeBound (L : ℕ) : ℕ := 4 * L ^ 3 + 20 * L ^ 2 + 91 * L + 110

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', ProductionFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionOperandLoad.State m input.length Q.speciesCount i.val s.val work ∧ R work)
      (fun inp work out => Cursor (DecodedReactionFieldLoad.atPrefix Q i s true) (DecodedReactionFieldLoad.atSuffix Q i s true)
        (emitted ++ BitCodec.integerCode (NetworkData.stoich (Q.network.reactions i) s)) inp work out ∧
        ProductionOperandLoad.State m input.length Q.speciesCount i.val s.val work ∧ R work) (timeBound input.length) := by
  let R' : (Fin (m + 20) → Tape) → Prop := fun work => Indices m Q.speciesCount i.val s.val work ∧ R work
  have hR' : ∀ work work', ProductionFrame.Unchanged m work work' → R' work → R' work' := by
    rintro work work' hw ⟨⟨hsp, hn, hi⟩, hr⟩
    obtain ⟨hreaction, _, hspecies, _⟩ := ProductionFrame.indices_eq m work work' hw
    have hcount := ProductionFrame.outside m work work' hw (count m) (by right; change 12 ≤ m + 15; omega)
    exact ⟨⟨by simpa only [hspecies] using hsp, by simpa only [hcount] using hn,
      by simpa only [hreaction] using hi⟩, hR work work' hw hr⟩
  have hl := ProductionOperandLoad.hoareTime m input Q hd i s before remaining emitted hsplit R hR
  have hc := clear_hoareTime m input.length i.val (Q.network.reactions i) s
    (DecodedReactionFieldLoad.atPrefix Q i s true) (DecodedReactionFieldLoad.atSuffix Q i s true) emitted R hR
  have ha := ProductionArithmetic.hoareTime m input Q hd i s
    (DecodedReactionFieldLoad.atPrefix Q i s true) (DecodedReactionFieldLoad.atSuffix Q i s true) emitted R' hR'
  have hlc := seqTM_hoareTime (ProductionOperandLoad.machine m) (BinaryBufferReset.machine (magnitude m)) hl (by
    rintro inp work out ⟨hc, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp, hr⟩) hc
  have hfull := seqTM_hoareTime (seqTM (ProductionOperandLoad.machine m) (BinaryBufferReset.machine (magnitude m)))
    (ProductionArithmetic.machine m) hlc (by
      rintro inp work out ⟨hc, hp, hi, hr⟩
      obtain ⟨hinp, hw, ho⟩ := hc.phase
      rw [hinp, hw, ho]
      exact ⟨hc, hp, hi, hr⟩) ha
  exact hfull.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hp, ⟨hsp, hn, hi⟩, hr⟩
    exact ⟨hc, ⟨hp.safe, hp.productReusable, hp.reactantReusable, hp.magnitudeReusable, hp.signHead, hsp, hn, hi⟩, hr⟩) (by
      unfold ReactionOperandsLoad.timeBound timeBound
      omega)

end JointThermoComplexity.Complexity.ProductionCoefficient

#print axioms JointThermoComplexity.Complexity.ProductionCoefficient.clear_hoareTime
#print axioms JointThermoComplexity.Complexity.ProductionCoefficient.hoareTime
