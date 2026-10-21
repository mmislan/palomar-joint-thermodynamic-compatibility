module
public import proofs.JointThermoComplexity.Complexity.MotifAccess

set_option autoImplicit false
@[expose] public section

/-! Return to the first motif from any canonical cursor position in the original decoded input. -/

namespace JointThermoComplexity.Complexity.MotifRescan
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def body (m : ℕ) : TM (m + 15) := seqTM DimensionSkip.machine (ReactionTableSkip.machine m)

abbrev machine (m : ℕ) : TM (m + 15) := MotifAccess.machine m

theorem from_start (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (emitted : List Bool) (R : (Fin (m + 15) → Tape) → Tape → Prop) :
    (body m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ CurrentPins.Kept m input work ∧ R work out)
      (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ CurrentPins.Kept m input work ∧ R work out)
      (ReactionTableSkip.timeBound input.length + Q.speciesCount + Q.reactionCount + Q.coreCount + 6) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work => (∀ j, Parked (work j))
  let S : (Fin (m + 15) → Tape) → Tape → Prop := fun work out => CurrentPins.Kept m input work ∧ R work out
  have hs := CursorReadOnly.hoareTime DimensionSkip.machine []
    (DimensionSkip.code Q.speciesCount Q.reactionCount Q.coreCount ++ (ReactionTableSkip.code Q ++ NetworkTallyData.tail Q))
    ([] ++ DimensionSkip.code Q.speciesCount Q.reactionCount Q.coreCount)
    (ReactionTableSkip.code Q ++ NetworkTallyData.tail Q) emitted P (Q.speciesCount + Q.reactionCount + Q.coreCount + 5)
    (fun V => DimensionSkip.hoareTime Q.speciesCount Q.reactionCount Q.coreCount []
      (ReactionTableSkip.code Q ++ NetworkTallyData.tail Q) emitted V) S
  have ht := ReactionTableSkip.hoareTime m input Q hd (NetworkTallyData.headers Q) (NetworkTallyData.tail Q) emitted
    (fun work out => P work ∧ R work out)
  have hfull := seqTM_hoareTime DimensionSkip.machine (ReactionTableSkip.machine m) hs (by
    rintro inp work out ⟨hc, hp, hk, hR⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨by simpa only [NetworkTallyData.headers, List.nil_append] using hc, hk, hp, hR⟩) ht
  exact hfull.consequence (by
    rintro inp work out ⟨hc, hp, hk, hR⟩
    exact ⟨by simpa only [MotifAccess.input_split input Q hd, NetworkTallyData.headers] using hc, hp, hk, hR⟩) (by
      rintro inp work out ⟨hc, hk, hp, hR⟩
      exact ⟨hc, hp, hk, hR⟩) (by omega)

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (m + 15) → Tape) → Tape → Prop) :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ (∀ j, Parked (work j)) ∧ CurrentPins.Kept m input work ∧ R work out)
      (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ CurrentPins.Kept m input work ∧ R work out) (MotifAccess.timeBound input.length) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work => (∀ j, Parked (work j))
  let S : (Fin (m + 15) → Tape) → Tape → Prop := fun work out => CurrentPins.Kept m input work ∧ R work out
  have hr := CursorReadOnly.hoareTime rewindInputTM before remaining [] (before ++ remaining) emitted P (before.length + 3)
    (fun V => (InputRewind.hoareTime before remaining emitted (fun work => P work ∧ V work)).consequence
      (fun _ _ _ h => h) (fun _ _ _ h => h) le_rfl) S
  have hb := from_start m input Q hd emitted R
  have hfull := seqTM_hoareTime rewindInputTM (body m) hr (by
    rintro inp work out ⟨hc, hp, hk, hR⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨by simpa only [hsplit] using hc, hp, hk, hR⟩) hb
  exact hfull.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by
    have hdim := NetworkCodec.decoded_dimensions_le_length hd
    have hlength := congrArg List.length hsplit
    simp only [List.length_append] at hlength
    unfold MotifAccess.timeBound ReactionTableSkip.timeBound
    omega)

end JointThermoComplexity.Complexity.MotifRescan

#print axioms JointThermoComplexity.Complexity.MotifRescan.from_start
#print axioms JointThermoComplexity.Complexity.MotifRescan.hoareTime
