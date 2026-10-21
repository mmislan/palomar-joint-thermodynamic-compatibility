module
public import proofs.JointThermoComplexity.Complexity.DecodedReactionFieldLoad

set_option autoImplicit false
@[expose] public section

/-! Load both actual stoichiometric operands from the original input while retaining independent iteration metadata. -/

namespace JointThermoComplexity.Complexity.ReactionOperandsLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState ReactionCircuit

variable {w n : ℕ}

structure Separate (left right count reaction species : Fin (w + 1)) : Prop where
  operands : left ≠ right
  countLeft : count ≠ left
  countRight : count ≠ right
  reactionLeft : reaction ≠ left
  reactionRight : reaction ≠ right
  speciesLeft : species ≠ left
  speciesRight : species ≠ right
  countReaction : count ≠ reaction

structure Loaded (left right count reaction species : Fin (w + 1)) (L ri : ℕ) (q : Reaction n) (s : Fin n)
    (work : Fin (w + 1) → Tape) : Prop where
  safe : ∀ j, Parked (work j)
  productString : (work left).HasBinaryString (q.product s).bits
  reactantString : (work right).HasBinaryString (q.reactant s).bits
  productZero : (work left).cells 0 = Γ.start
  reactantZero : (work right).cells 0 = Γ.start
  productReusable : Reusable L (work left)
  reactantReusable : Reusable L (work right)
  speciesPosition : IsReg s.val (work species)
  speciesCount : IsReg n (work count)
  reactionPosition : IsReg ri (work reaction)

def machine (left right count reaction species : Fin (w + 1)) : TM (w + 1) :=
  seqTM (DecodedReactionFieldLoad.machine right count reaction species false)
    (DecodedReactionFieldLoad.machine left count reaction species true)

def timeBound (L : ℕ) : ℕ := 4 * L ^ 3 + 20 * L ^ 2 + 70 * L + 69

theorem hoareTime (left right count reaction species : Fin (w + 1)) (sep : Separate left right count reaction species)
    (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → work' j = work j) → R work → R work') :
    (machine left right count reaction species).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Reusable input.length (work left) ∧ Reusable input.length (work right) ∧ IsReg i.val (work reaction) ∧
        IsReg s.val (work species) ∧ IsReg Q.speciesCount (work count) ∧ R work)
      (fun inp work out => Cursor (DecodedReactionFieldLoad.atPrefix Q i s true) (DecodedReactionFieldLoad.atSuffix Q i s true) emitted inp work out ∧
        Loaded left right count reaction species input.length i.val (Q.network.reactions i) s work ∧ R work) (timeBound input.length) := by
  let R₁ : (Fin (w + 1) → Tape) → Prop := fun work => Reusable input.length (work left) ∧ R work
  have hR₁ : ∀ work work', (∀ j, j ≠ right → work' j = work j) → R₁ work → R₁ work' := by
    rintro work work' hw ⟨hl, hr⟩
    exact ⟨by simpa only [hw left sep.operands] using hl, hR work work' (fun j _ hj => hw j hj) hr⟩
  let R₂ : (Fin (w + 1) → Tape) → Prop := fun work => (work right).HasBinaryString ((Q.network.reactions i).reactant s).bits ∧
    (work right).cells 0 = Γ.start ∧ Reusable input.length (work right) ∧ R work
  have hR₂ : ∀ work work', (∀ j, j ≠ left → work' j = work j) → R₂ work → R₂ work' := by
    rintro work work' hw ⟨hb, hz, hrb, hr⟩
    exact ⟨by simpa only [hw right sep.operands.symm] using hb, by simpa only [hw right sep.operands.symm] using hz,
      by simpa only [hw right sep.operands.symm] using hrb, hR work work' (fun j hj _ => hw j hj) hr⟩
  have hr := DecodedReactionFieldLoad.hoareTime right count reaction species sep.countReaction sep.countRight sep.reactionRight
    sep.speciesRight false input Q hd i s before remaining emitted hsplit R₁ hR₁
  have hl := DecodedReactionFieldLoad.hoareTime left count reaction species sep.countReaction sep.countLeft sep.reactionLeft
    sep.speciesLeft true input Q hd i s (DecodedReactionFieldLoad.atPrefix Q i s false) (DecodedReactionFieldLoad.atSuffix Q i s false) emitted
    (DecodedReactionFieldLoad.input_split input Q hd i s false) R₂ hR₂
  have hfull := seqTM_hoareTime (DecodedReactionFieldLoad.machine right count reaction species false)
    (DecodedReactionFieldLoad.machine left count reaction species true) hr (by
      rintro inp work out ⟨hc, hs, hb, hz, hreuse, hsp, hn, hi, hleft, hr⟩
      obtain ⟨hinp, hw, ho⟩ := hc.phase
      rw [hinp, hw, ho]
      exact ⟨hc, hs, hleft, hi, hsp, hn,
        by simpa only [ReactionFieldSelect.value, Bool.false_eq_true, ↓reduceIte] using hb, hz, hreuse, hr⟩) hl
  exact hfull.consequence (by
    rintro inp work out ⟨hc, hs, hl, hr, hi, hsp, hn, hrest⟩
    exact ⟨hc, hs, hr, hi, hsp, hn, hl, hrest⟩) (by
      rintro inp work out ⟨hc, hs, hl, hlz, hlr, hsp, hn, hi, hr, hrz, hrr, hrest⟩
      exact ⟨hc, ⟨hs, by simpa only [ReactionFieldSelect.value, ↓reduceIte] using hl,
        hr, hlz, hrz, hlr, hrr, hsp, hn, hi⟩, hrest⟩) (by
          unfold timeBound DecodedReactionFieldLoad.timeBound
          omega)

end JointThermoComplexity.Complexity.ReactionOperandsLoad

#print axioms JointThermoComplexity.Complexity.ReactionOperandsLoad.hoareTime
