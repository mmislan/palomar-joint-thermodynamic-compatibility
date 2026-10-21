module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaHead

set_option autoImplicit false
@[expose] public section

/-! Total formula head scanning: eq/lt payloads use the actual two-term control specification. -/

namespace JointThermoComplexity.Complexity.SourceFormulaToken
open SourceFormulaScan

def bodyTaken (arity L : ℕ) (bits input : List Bool) : List Bool := match classify bits with
  | .eq | .lt => (SourceTermPair.state arity L input).before
  | _ => []

def bodyRest (arity L : ℕ) (bits input : List Bool) : List Bool := match classify bits with
  | .eq | .lt => (SourceTermPair.state arity L input).input
  | _ => input

def bodyAccepted (arity L : ℕ) (bits input : List Bool) : Bool := match classify bits with
  | .eq | .lt => (SourceTermPair.state arity L input).valid
  | .invalid => false
  | _ => true

def taken (arity L : ℕ) (input : List Bool) : List Bool := input.take 3 ++
  if SourceTags.accepted input then bodyTaken arity L (SourceTermToken.tagBits input) (input.drop 3) else []

def rest (arity L : ℕ) (input : List Bool) : List Bool :=
  if SourceTags.accepted input then bodyRest arity L (SourceTermToken.tagBits input) (input.drop 3) else input.drop 3

def accepted (arity L : ℕ) (input : List Bool) : Bool :=
  SourceTags.accepted input && bodyAccepted arity L (SourceTermToken.tagBits input) (input.drop 3)

theorem body_split (arity L : ℕ) (bits input : List Bool) : bodyTaken arity L bits input ++ bodyRest arity L bits input = input := by
  unfold bodyTaken bodyRest
  cases classify bits <;> simp only [List.nil_append]
  · exact (SourceTermPair.state_bounds arity L input).2.2
  · exact (SourceTermPair.state_bounds arity L input).2.2

theorem split (arity L : ℕ) (input : List Bool) : taken arity L input ++ rest arity L input = input := by
  unfold taken rest
  cases hp : SourceTags.accepted input with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]; exact List.take_append_drop 3 input
  | true => rw [ite_eq_left rfl, ite_eq_left rfl, List.append_assoc, body_split]; exact List.take_append_drop 3 input

theorem body_sound (arity L : ℕ) (a b c : Bool) (input : List Bool) (hlen : input.length ≤ L)
    (h : bodyAccepted arity L [a, b, c] input = true) :
    ∃ head : Head arity, [a, b, c] ++ input = head.code ++ bodyRest arity L [a, b, c] input ∧
      [a, b, c] ++ bodyTaken arity L [a, b, c] input = head.code ∧ (classify [a, b, c]).children = head.children := by
  cases a <;> cases b <;> cases c
  · exact ⟨.truth, rfl, rfl, rfl⟩
  · exact ⟨.falsity, rfl, rfl, rfl⟩
  · obtain ⟨s, t, hp, hc⟩ := SourceTermPair.status_sound arity L input hlen h
    refine ⟨.eq s t, ?_, ?_, rfl⟩
    · simpa only [Head.code, bodyRest, classify, List.append_assoc] using congrArg (fun xs => [false, true, false] ++ xs) hc
    · simp only [Head.code, bodyTaken, classify, hp, List.append_assoc]
  · obtain ⟨s, t, hp, hc⟩ := SourceTermPair.status_sound arity L input hlen h
    refine ⟨.lt s t, ?_, ?_, rfl⟩
    · simpa only [Head.code, bodyRest, classify, List.append_assoc] using congrArg (fun xs => [false, true, true] ++ xs) hc
    · simp only [Head.code, bodyTaken, classify, hp, List.append_assoc]
  · exact ⟨.conj, rfl, rfl, rfl⟩
  · exact ⟨.disj, rfl, rfl, rfl⟩
  all_goals simp [bodyAccepted, classify] at h

theorem sound (arity L : ℕ) (input : List Bool) (hlen : input.length ≤ L) (h : accepted arity L input = true) :
    ∃ head : Head arity, input = head.code ++ rest arity L input ∧ taken arity L input = head.code ∧
      (classify (SourceTermToken.tagBits input)).children = head.children := by
  cases input with
  | nil => simp [accepted, SourceTags.accepted] at h
  | cons a input =>
    cases input with
    | nil => simp [accepted, SourceTags.accepted] at h
    | cons b input =>
      cases input with
      | nil => simp [accepted, SourceTags.accepted] at h
      | cons c input =>
        have hlen' : input.length ≤ L := by simp only [List.length_cons] at hlen; omega
        have htag : SourceTags.accepted (a :: b :: c :: input) = true := by simp [SourceTags.accepted]
        have hb : bodyAccepted arity L [a, b, c] input = true := by
          simpa [accepted, htag, SourceTermToken.tagBits, SourceBitRead.value] using h
        simpa [taken, rest, htag, SourceTermToken.tagBits, SourceBitRead.value] using body_sound arity L a b c input hlen' hb

theorem pair_code (arity L : ℕ) (a b : RealSyntax.Term arity) (suffix : List Bool)
    (hlen : (a.code ++ b.code ++ suffix).length ≤ L) :
    (SourceTermPair.state arity L (a.code ++ b.code ++ suffix)).before = a.code ++ b.code ∧
      (SourceTermPair.state arity L (a.code ++ b.code ++ suffix)).input = suffix ∧
      (SourceTermPair.state arity L (a.code ++ b.code ++ suffix)).valid = true := by
  obtain ⟨hr, hv⟩ := SourceTermPair.code_result arity L a b suffix hlen
  have hw := (SourceTermPair.state_bounds arity L (a.code ++ b.code ++ suffix)).2.2
  rw [hr] at hw
  exact ⟨List.append_cancel_right (by simpa only [List.append_assoc] using hw), hr, hv⟩

theorem code_result {arity L : ℕ} (head : Head arity) (suffix : List Bool) (hlen : (head.code ++ suffix).length ≤ L) :
    taken arity L (head.code ++ suffix) = head.code ∧ rest arity L (head.code ++ suffix) = suffix ∧
      accepted arity L (head.code ++ suffix) = true := by
  cases head with
  | eq a b | lt a b =>
    have hfield : (a.code ++ b.code ++ suffix).length ≤ L := by
      simp only [Head.code, List.length_append, List.length_cons, List.length_nil] at hlen ⊢
      omega
    obtain ⟨hp, hr, hv⟩ := pair_code arity L a b suffix hfield
    simp only [List.append_assoc] at hp hr hv
    simp [taken, rest, accepted, Head.code, SourceTags.accepted, SourceTermToken.tagBits,
      SourceBitRead.value, bodyTaken, bodyRest, bodyAccepted, classify, List.append_assoc, hp, hr, hv]
  | truth | falsity | conj | disj =>
    simp [taken, rest, accepted, Head.code, SourceTags.accepted, SourceTermToken.tagBits,
      SourceBitRead.value, bodyTaken, bodyRest, bodyAccepted, classify]

theorem success_consumes (arity L : ℕ) (input : List Bool) (hlen : input.length ≤ L) (h : accepted arity L input = true) :
    (rest arity L input).length + 3 ≤ input.length := by
  obtain ⟨head, hc, _ht, _hn⟩ := sound arity L input hlen h
  have hmin := head_min_length head
  have he := congrArg List.length hc
  rw [List.length_append] at he
  omega

end JointThermoComplexity.Complexity.SourceFormulaToken

#print axioms JointThermoComplexity.Complexity.SourceFormulaToken.sound
#print axioms JointThermoComplexity.Complexity.SourceFormulaToken.code_result
#print axioms JointThermoComplexity.Complexity.SourceFormulaToken.success_consumes
