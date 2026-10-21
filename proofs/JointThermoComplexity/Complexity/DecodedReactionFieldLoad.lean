module
public import proofs.JointThermoComplexity.Complexity.ReactionFieldIndexedLoad
public import proofs.JointThermoComplexity.Complexity.ReactionTableAccess

set_option autoImplicit false
@[expose] public section

/-! Load an actual indexed binary reaction field after a bounded restart of the original decoded input. -/

namespace JointThermoComplexity.Complexity.DecodedReactionFieldLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState ReactionCircuit

variable {w n : ℕ}

theorem field_split (q : Reaction n) (s : Fin n) (product : Bool) (before tail : List Bool) :
    ReactionFieldSelect.taken q s product before ++ ReactionFieldSelect.remaining q s product tail =
      before ++ ((DataCodec.reaction n).code q ++ tail) := by
  cases product <;> simp only [ReactionFieldSelect.taken, ReactionFieldSelect.remaining, Bool.false_eq_true,
    ↓reduceIte, ReactionSkip.code_eq, ReactionNaturalSelect.factors,
    NaturalSelectionCode.split q.reactant s, NaturalSelectionCode.split q.product s, List.append_assoc]

def atPrefix (Q : NetworkCodec.Input) (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (product : Bool) : List Bool :=
  ReactionFieldSelect.taken (Q.network.reactions i) s product
    (NetworkTallyData.headers Q ++ ReactionSelectionCode.leading Q.network.reactions i)

def atSuffix (Q : NetworkCodec.Input) (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (product : Bool) : List Bool :=
  ReactionFieldSelect.remaining (Q.network.reactions i) s product
    (ReactionSelectionCode.trailing Q.network.reactions i ++ NetworkTallyData.tail Q)

theorem input_split (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (product : Bool) : atPrefix Q i s product ++ atSuffix Q i s product = input := by
  have h := ReactionTableAccess.input_split input Q hd
  rw [ReactionSelectionCode.split Q.network.reactions i] at h
  simpa only [atPrefix, atSuffix, field_split, List.append_assoc] using h.symm

def machine (idx count reaction species : Fin (w + 1)) (product : Bool) : TM (w + 1) :=
  seqTM ReactionTableAccess.machine (ReactionFieldIndexedLoad.machine idx count reaction species product)

def timeBound (L : ℕ) : ℕ := 2 * L ^ 3 + 10 * L ^ 2 + 35 * L + 34

theorem hoareTime (idx count reaction species : Fin (w + 1)) (hcr : count ≠ reaction)
    (hcount : count ≠ idx) (hreaction : reaction ≠ idx) (hspecies : species ≠ idx) (product : Bool)
    (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx count reaction species product).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Reusable input.length (work idx) ∧ IsReg i.val (work reaction) ∧ IsReg s.val (work species) ∧ IsReg Q.speciesCount (work count) ∧ R work)
      (fun inp work out => Cursor (atPrefix Q i s product) (atSuffix Q i s product) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString (ReactionFieldSelect.value (Q.network.reactions i) s product).bits ∧
        (work idx).cells 0 = Γ.start ∧ Reusable input.length (work idx) ∧ IsReg s.val (work species) ∧ IsReg Q.speciesCount (work count) ∧
        IsReg i.val (work reaction) ∧ R work) (timeBound input.length) := by
  have ha := ReactionTableAccess.hoareTime input Q hd before remaining emitted hsplit
    (fun work => Reusable input.length (work idx) ∧ IsReg i.val (work reaction) ∧ IsReg s.val (work species) ∧ IsReg Q.speciesCount (work count) ∧ R work)
  have hr : Q.reactionCount ≤ input.length := by have h := NetworkCodec.decoded_dimensions_le_length hd; omega
  have hl := ReactionFieldIndexedLoad.hoareTime idx count reaction species hcr hcount hreaction hspecies product input.length hr
    Q.network.reactions i s (fun j => ReactionTableSkip.fields_bounded input Q hd j)
    (NetworkTallyData.headers Q) (NetworkTallyData.tail Q) emitted R hR
  have hfull := seqTM_hoareTime ReactionTableAccess.machine (ReactionFieldIndexedLoad.machine idx count reaction species product) ha (by
    rintro inp work out ⟨hc, hs, hb, hi, hsp, hn, hr⟩
    obtain ⟨hinp, hw, ho⟩ := hc.phase
    rw [hinp, hw, ho]
    exact ⟨hc, hs, hb, hi, hsp, hn, hr⟩) hl
  exact hfull.consequence (fun _ _ _ h => h) (by
    intro inp work out h
    simpa only [atPrefix, atSuffix] using h) (by
      unfold ReactionTableAccess.timeBound ReactionFieldIndexedLoad.timeBound timeBound
      omega)

end JointThermoComplexity.Complexity.DecodedReactionFieldLoad

#print axioms JointThermoComplexity.Complexity.DecodedReactionFieldLoad.input_split
#print axioms JointThermoComplexity.Complexity.DecodedReactionFieldLoad.hoareTime
