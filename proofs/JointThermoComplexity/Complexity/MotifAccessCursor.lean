module
public import proofs.JointThermoComplexity.Complexity.MotifAccess

set_option autoImplicit false
@[expose] public section

/-! The existing actual motif-access machine accepts any original-input cursor, including the rewound start. -/

namespace JointThermoComplexity.Complexity.MotifAccessCursor
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (m + 15) → Tape) → Tape → Prop) :
    (MotifAccess.machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        CurrentPins.Kept m input work ∧ R work out)
      (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ CurrentPins.Kept m input work ∧ R work out) (MotifAccess.timeBound input.length) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work => ∀ j, Parked (work j)
  let S : (Fin (m + 15) → Tape) → Tape → Prop := fun work out => CurrentPins.Kept m input work ∧ R work out
  have hr := CursorReadOnly.hoareTime rewindInputTM before remaining [] (before ++ remaining) emitted P (before.length + 3)
    (fun V => (InputRewind.hoareTime before remaining emitted (fun work => P work ∧ V work)).consequence
      (fun _ _ _ h => h) (fun _ _ _ h => h) le_rfl) S
  have hs := CursorReadOnly.hoareTime DimensionSkip.machine []
    (DimensionSkip.code Q.speciesCount Q.reactionCount Q.coreCount ++ (ReactionTableSkip.code Q ++ NetworkTallyData.tail Q))
    ([] ++ DimensionSkip.code Q.speciesCount Q.reactionCount Q.coreCount)
    (ReactionTableSkip.code Q ++ NetworkTallyData.tail Q) emitted P (Q.speciesCount + Q.reactionCount + Q.coreCount + 5)
    (fun V => DimensionSkip.hoareTime Q.speciesCount Q.reactionCount Q.coreCount []
      (ReactionTableSkip.code Q ++ NetworkTallyData.tail Q) emitted V) S
  have ht := ReactionTableSkip.hoareTime m input Q hd (NetworkTallyData.headers Q) (NetworkTallyData.tail Q) emitted
    (fun work out => P work ∧ R work out)
  have hst := seqTM_hoareTime DimensionSkip.machine (ReactionTableSkip.machine m) hs (by
    rintro inp work out ⟨hc, hp, hk, hR⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨by simpa only [NetworkTallyData.headers, List.nil_append] using hc, hk, hp, hR⟩) ht
  have hfull := seqTM_hoareTime rewindInputTM (seqTM DimensionSkip.machine (ReactionTableSkip.machine m)) hr (by
    rintro inp work out ⟨hc, hp, hk, hR⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨by simpa only [hsplit, MotifAccess.input_split input Q hd, NetworkTallyData.headers] using hc, hp, hk, hR⟩) hst
  have hlength := congrArg List.length hsplit
  simp only [List.length_append] at hlength
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  exact hfull.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hk, hp, hR⟩
    exact ⟨hc, hp, hk, hR⟩) (by unfold MotifAccess.timeBound ReactionTableSkip.timeBound; omega)

end JointThermoComplexity.Complexity.MotifAccessCursor

#print axioms JointThermoComplexity.Complexity.MotifAccessCursor.hoareTime
