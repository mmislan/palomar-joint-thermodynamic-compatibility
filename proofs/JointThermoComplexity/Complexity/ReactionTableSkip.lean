module
public import proofs.JointThermoComplexity.Complexity.ReactionListSkip
public import proofs.JointThermoComplexity.Complexity.CurrentPins
public import proofs.JointThermoComplexity.Complexity.InputSize

set_option autoImplicit false
@[expose] public section

/-! Read the complete decoded reaction table with a cubic binary input-length bound. -/

namespace JointThermoComplexity.Complexity.ReactionTableSkip
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def code (Q : NetworkCodec.Input) : List Bool := ReactionArrayData.code (NetworkTallyData.reactions Q)

def machine (m : ℕ) : TM (m + 15) :=
  ReactionListSkip.machine (MonomialFuel.slot (m + 1)) (ReactionFuel.slot m)

def timeBound (L : ℕ) : ℕ := 2 * L ^ 3 + 8 * L ^ 2 + 10 * L + 2

theorem runtime_bound (L r : ℕ) (hr : r ≤ L) : ReactionListSkip.timeBound L r ≤ timeBound L := by
  unfold ReactionListSkip.timeBound ReactionSkip.timeBound timeBound
  calc r * (2 * L ^ 2 + 8 * L + 7 + 2) + (r + 2) ≤
        L * (2 * L ^ 2 + 8 * L + 7 + 2) + (L + 2) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ hr) (Nat.add_le_add_right hr 2)
       _ = _ := by ring1

theorem fields_bounded (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) : ReactionSkip.Bounded input.length (Q.network.reactions i) := by
  have hdim := NetworkCodec.decoded_dimensions_le_length hd
  have hr := InputSize.reaction_length_le_input Q i
  have hlen : Q.code.length = input.length := by rw [NetworkCodec.decode_sound hd]
  rw [InputSize.reaction_code_length] at hr
  refine ⟨by omega, ?_, ?_, by omega, by omega⟩
  · intro s
    have hs := (InputSize.complex_entries_le_input Q i s).1
    omega
  · intro s
    have hs := (InputSize.complex_entries_le_input Q i s).2
    omega

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Tape → Prop) :
    (machine m).HoareTime
      (fun inp work out => Cursor before (code Q ++ tail) emitted inp work out ∧ CurrentPins.Kept m input work ∧ R work out)
      (fun inp work out => Cursor (before ++ code Q) tail emitted inp work out ∧ CurrentPins.Kept m input work ∧ R work out)
      (timeBound input.length) := by
  have hne : MonomialFuel.slot (m + 1) ≠ ReactionFuel.slot m := by
    intro he
    have hv := congrArg Fin.val he
    change m + 1 + 9 = m + 11 at hv
    omega
  have hs := ReactionListSkip.hoareTime (MonomialFuel.slot (m + 1)) (ReactionFuel.slot m) hne input.length
    (NetworkTallyData.reactions Q) (by
      intro q hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact fields_bounded input Q hd i) before tail emitted
    (fun work out => CurrentPins.Kept m input work ∧ R work out)
  exact hs.consequence (by
    rintro inp work out ⟨hc, hk, hr⟩
    obtain ⟨hn, hreact⟩ := CurrentPins.counts m input Q hd work hk
    exact ⟨hc, by simpa only [NetworkTallyData.reaction_count] using hreact, hn, hk, hr⟩) (by
      rintro inp work out ⟨hc, _, _, hk, hr⟩
      exact ⟨hc, hk, hr⟩) (by
        rw [NetworkTallyData.reaction_count]
        exact runtime_bound _ _ (by have h := NetworkCodec.decoded_dimensions_le_length hd; omega))

end JointThermoComplexity.Complexity.ReactionTableSkip

#print axioms JointThermoComplexity.Complexity.ReactionTableSkip.runtime_bound
#print axioms JointThermoComplexity.Complexity.ReactionTableSkip.fields_bounded
#print axioms JointThermoComplexity.Complexity.ReactionTableSkip.hoareTime
