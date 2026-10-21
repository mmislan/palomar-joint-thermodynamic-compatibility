module
public import proofs.JointThermoComplexity.Complexity.DataCodec
public import proofs.JointThermoComplexity.Complexity.NetworkMembership

set_option autoImplicit false
@[expose] public section

/-!
# Complete binary inputs and a total formula map

Three unary dimension headers bound all declared finite dimensions, including
empty-data cases. Exponents, signed box numerators and positive factor data
retain their binary codecs. Decoding rejects malformed and trailing data.
The total language is supplied-motif feasibility, without PAC recognition.
The formula map sends malformed strings to a false sentence. Its semantic
correctness is unconditional; its binary-machine runtime remains to be proved.
-/

namespace JointThermoComplexity.Complexity.NetworkCodec
open FiniteCodec NetworkData RealSyntax

theorem parseBinders_sound {input suffix : List Bool} {n : ℕ}
    (h : parseBinders input = some (n, suffix)) : input = binderCode n ++ suffix := by
  induction input generalizing n suffix with
  | nil => simp [parseBinders] at h
  | cons bit rest ih =>
    cases bit with
    | false =>
      simp only [parseBinders, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | true =>
      cases hp : parseBinders rest with
      | none => simp [parseBinders, hp] at h
      | some pair =>
        obtain ⟨k, tail⟩ := pair
        simp [parseBinders, hp] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa [binderCode, List.replicate_succ] using congrArg (List.cons true) (ih hp)

def dimension : Codec ℕ := ⟨binderCode, parseBinders, parseBinders_code, parseBinders_sound⟩

structure Input where
  speciesCount : ℕ
  reactionCount : ℕ
  coreCount : ℕ
  network : Network speciesCount reactionCount coreCount

def Input.code (Q : Input) : List Bool :=
  binderCode Q.speciesCount ++ binderCode Q.reactionCount ++ binderCode Q.coreCount ++
    (DataCodec.network Q.speciesCount Q.reactionCount Q.coreCount).code Q.network

def parseInput (input : List Bool) : Option (Input × List Bool) := do
  let (n, tail₁) ← dimension.parse input
  let (r, tail₂) ← dimension.parse tail₁
  let (c, tail₃) ← dimension.parse tail₂
  let (Q, suffix) ← (DataCodec.network n r c).parse tail₃
  pure (⟨n, r, c, Q⟩, suffix)

theorem parseInput_code (Q : Input) (suffix : List Bool) :
    parseInput (Q.code ++ suffix) = some (Q, suffix) := by
  obtain ⟨n, r, c, Q⟩ := Q
  simp [Input.code, parseInput, dimension, List.append_assoc, DataCodec.network_roundtrip]

theorem parseInput_sound {input suffix : List Bool} {Q : Input}
    (h : parseInput input = some (Q, suffix)) : input = Q.code ++ suffix := by
  cases hn : dimension.parse input with
  | none => simp [parseInput, hn] at h
  | some pair =>
    obtain ⟨n, tail₁⟩ := pair
    cases hr : dimension.parse tail₁ with
    | none => simp [parseInput, hn, hr] at h
    | some pair =>
      obtain ⟨r, tail₂⟩ := pair
      cases hc : dimension.parse tail₂ with
      | none => simp [parseInput, hn, hr, hc] at h
      | some pair =>
        obtain ⟨c, tail₃⟩ := pair
        cases hQ : (DataCodec.network n r c).parse tail₃ with
        | none => simp [parseInput, hn, hr, hc, hQ] at h
        | some pair =>
          obtain ⟨N, tail₄⟩ := pair
          simp [parseInput, hn, hr, hc, hQ] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [dimension.sound hn, dimension.sound hr, dimension.sound hc,
            (DataCodec.network n r c).sound hQ]
          simp only [Input.code, dimension, List.append_assoc]

def codec : Codec Input := ⟨Input.code, parseInput, parseInput_code, parseInput_sound⟩

def decode (input : List Bool) : Option Input := do
  let (Q, suffix) ← parseInput input
  if suffix = [] then pure Q else none

theorem decode_code_append (Q : Input) (suffix : List Bool) :
    decode (Q.code ++ suffix) = if suffix = [] then some Q else none := by
  simp [decode, parseInput_code]

@[simp] theorem decode_code (Q : Input) : decode Q.code = some Q := by
  simpa using decode_code_append Q []

theorem decode_trailing_data (Q : Input) {suffix : List Bool} (h : suffix ≠ []) :
    decode (Q.code ++ suffix) = none := by simp [decode_code_append, h]

theorem decode_sound {input : List Bool} {Q : Input} (h : decode input = some Q) :
    input = Q.code := by
  cases hp : parseInput input with
  | none => simp [decode, hp] at h
  | some pair =>
    obtain ⟨N, suffix⟩ := pair
    by_cases hs : suffix = []
    · subst suffix
      simp [decode, hp] at h
      subst Q
      simpa using parseInput_sound hp
    · simp [decode, hp, hs] at h

theorem Input.code_injective : Function.Injective Input.code := codec.code_injective

theorem dimensions_le_code_length (Q : Input) :
    Q.speciesCount + Q.reactionCount + Q.coreCount + 3 ≤ Q.code.length := by
  simp only [Input.code, binderCode, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

theorem decoded_dimensions_le_length {input : List Bool} {Q : Input}
    (h : decode input = some Q) :
    Q.speciesCount + Q.reactionCount + Q.coreCount + 3 ≤ input.length := by
  rw [decode_sound h]
  exact dimensions_le_code_length Q

def TotalFeasibility : Set (List Bool) :=
  {input | ∃ Q, decode input = some Q ∧ Q.network.Feasible}

theorem code_mem_total_iff (Q : Input) : Q.code ∈ TotalFeasibility ↔ Q.network.Feasible := by
  simp [TotalFeasibility]

theorem malformed_not_mem_total {input : List Bool} (h : decode input = none) :
    input ∉ TotalFeasibility := by simp [TotalFeasibility, h]

def toSentence (input : List Bool) : Sentence :=
  match decode input with
  | none => ⟨0, .falsity⟩
  | some Q => NetworkMembership.sentence Q.network

theorem toSentence_correct (input : List Bool) :
    input ∈ TotalFeasibility ↔ (toSentence input).code ∈ ETR := by
  rw [RealSyntax.code_mem_ETR_iff]
  cases hd : decode input with
  | none =>
    have hs : toSentence input = (⟨0, .falsity⟩ : Sentence) := by simp [toSentence, hd]
    rw [hs]
    simp [TotalFeasibility, hd, Sentence.Satisfiable, Formula.eval]
  | some Q =>
    simpa [TotalFeasibility, toSentence, hd] using
      (NetworkMembership.sentence_satisfiable_iff Q.network).symm

end JointThermoComplexity.Complexity.NetworkCodec

#print axioms JointThermoComplexity.Complexity.NetworkCodec.parseInput_code
#print axioms JointThermoComplexity.Complexity.NetworkCodec.decode_sound
#print axioms JointThermoComplexity.Complexity.NetworkCodec.decoded_dimensions_le_length
#print axioms JointThermoComplexity.Complexity.NetworkCodec.toSentence_correct
