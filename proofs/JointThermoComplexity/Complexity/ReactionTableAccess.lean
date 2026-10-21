module
public import proofs.JointThermoComplexity.Complexity.ReactionSelectionCode
public import proofs.JointThermoComplexity.Complexity.NetworkTallyData
public import proofs.JointThermoComplexity.Complexity.InputRewind

set_option autoImplicit false
@[expose] public section

/-! Restart at the original reaction table from any valid cursor without changing work or formula output. -/

namespace JointThermoComplexity.Complexity.ReactionTableAccess
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine : TM w := seqTM rewindInputTM DimensionSkip.machine

def timeBound (L : ℕ) : ℕ := 4 * L + 9

theorem input_split (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q) :
    input = NetworkTallyData.headers Q ++ (ReactionSelectionCode.code Q.network.reactions ++ NetworkTallyData.tail Q) := by
  rw [NetworkCodec.decode_sound hd, NetworkTallyData.code_split]
  rfl

theorem hoareTime (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before remaining emitted : List Bool) (hsplit : before ++ remaining = input) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => Cursor (NetworkTallyData.headers Q) (ReactionSelectionCode.code Q.network.reactions ++ NetworkTallyData.tail Q)
        emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work) (timeBound input.length) := by
  have hr := InputRewind.hoareTime before remaining emitted (fun work => (∀ j, Parked (work j)) ∧ R work)
  have hs := DimensionSkip.hoareTime Q.speciesCount Q.reactionCount Q.coreCount []
    (ReactionSelectionCode.code Q.network.reactions ++ NetworkTallyData.tail Q) emitted R
  have hfull := seqTM_hoareTime rewindInputTM DimensionSkip.machine hr (by
    rintro inp work out ⟨hc, hs, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨by simpa only [hsplit, input_split input Q hd, NetworkTallyData.headers] using hc, hs, hr⟩) hs
  exact hfull.consequence (fun _ _ _ h => h) (by
    intro inp work out h
    simpa only [List.nil_append, NetworkTallyData.headers] using h) (by
      have hdims := NetworkCodec.decoded_dimensions_le_length hd
      have hlen := congrArg List.length hsplit
      simp only [List.length_append] at hlen
      unfold timeBound
      omega)

end JointThermoComplexity.Complexity.ReactionTableAccess

#print axioms JointThermoComplexity.Complexity.ReactionTableAccess.hoareTime
