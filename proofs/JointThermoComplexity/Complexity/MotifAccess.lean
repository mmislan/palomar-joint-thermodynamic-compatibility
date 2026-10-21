module
public import proofs.JointThermoComplexity.Complexity.ReactionTableSkip
public import proofs.JointThermoComplexity.Complexity.CursorReadOnly
public import proofs.JointThermoComplexity.Complexity.InputRewind

set_option autoImplicit false
@[expose] public section

/-! From the consumed validated input, revisit its first motif without changing any output or work tape. -/

namespace JointThermoComplexity.Complexity.MotifAccess
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def before (Q : NetworkCodec.Input) : List Bool := NetworkTallyData.headers Q ++ ReactionTableSkip.code Q

def machine (m : ℕ) : TM (m + 15) :=
  seqTM rewindInputTM (seqTM DimensionSkip.machine (ReactionTableSkip.machine m))

def timeBound (L : ℕ) : ℕ := 2 * L ^ 3 + 8 * L ^ 2 + 12 * L + 12

theorem input_split (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q) :
    input = NetworkTallyData.headers Q ++ (ReactionTableSkip.code Q ++ NetworkTallyData.tail Q) := by
  rw [NetworkCodec.decode_sound hd, NetworkTallyData.code_split]
  rfl

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (emitted : List Bool) (R : (Fin (m + 15) → Tape) → Tape → Prop) :
    (machine m).HoareTime
      (fun inp work out => Cursor input [] emitted inp work out ∧ (∀ j, Parked (work j)) ∧ CurrentPins.Kept m input work ∧ R work out)
      (fun inp work out => Cursor (before Q) (NetworkTallyData.tail Q) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ CurrentPins.Kept m input work ∧ R work out) (timeBound input.length) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work => (∀ j, Parked (work j))
  let S : (Fin (m + 15) → Tape) → Tape → Prop := fun work out => CurrentPins.Kept m input work ∧ R work out
  have hr := CursorReadOnly.hoareTime rewindInputTM input [] [] (input ++ []) emitted P (input.length + 3)
    (fun V => (InputRewind.hoareTime input [] emitted (fun work => P work ∧ V work)).consequence
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
    exact ⟨by simpa only [List.append_nil, input_split input Q hd, NetworkTallyData.headers] using hc, hp, hk, hR⟩) hst
  exact hfull.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hk, hp, hR⟩
    exact ⟨hc, hp, hk, hR⟩) (by
      have hdim := NetworkCodec.decoded_dimensions_le_length hd
      unfold timeBound ReactionTableSkip.timeBound
      omega)

theorem run (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (emitted : List Bool) (inp : Tape) (work : Fin (m + 15) → Tape) (out : Tape)
    (hc : Cursor input [] emitted inp work out) (hp : ∀ j, Parked (work j)) (hk : CurrentPins.Kept m input work) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine m).reachesIn t ⟨(machine m).qstart, inp, work, out⟩ d ∧
      (machine m).halted d ∧ Cursor (before Q) (NetworkTallyData.tail Q) emitted d.input d.work d.output ∧
      d.work = work ∧ d.output = out := by
  obtain ⟨d, t, ht, hr, hh, hdc, _, _, hdw, hdo⟩ :=
    hoareTime m input Q hd emitted (fun work' out' => work' = work ∧ out' = out) inp work out ⟨hc, hp, hk, rfl, rfl⟩
  exact ⟨d, t, ht, hr, hh, hdc, hdw, hdo⟩

end JointThermoComplexity.Complexity.MotifAccess

#print axioms JointThermoComplexity.Complexity.MotifAccess.input_split
#print axioms JointThermoComplexity.Complexity.MotifAccess.hoareTime
#print axioms JointThermoComplexity.Complexity.MotifAccess.run
