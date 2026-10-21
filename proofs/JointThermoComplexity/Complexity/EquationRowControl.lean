module
public import proofs.JointThermoComplexity.Complexity.MonomialPrefixControl
public import proofs.JointThermoComplexity.Complexity.EquationCoefficientLoad

set_option autoImplicit false
@[expose] public section

/-! Total three-term row storage. Presence and degree flags are decoded in
order; unused slots keep their old contents. Coefficients are encoded words,
whereas variable buffers store raw natural bits.
-/

namespace JointThermoComplexity.Complexity.EquationRowControl

structure Term where
  present : Bool
  coefficient : List Bool
  flags : Fin 3 → Bool
  words : Fin 2 → List Bool

structure State where
  before : List Bool
  input : List Bool
  terms : Fin 3 → Term
  available : Bool

def read (s : State) (i : Fin 3) : State :=
  { s with
    before := s.before ++ BooleanMachine.copied s.input
    input := BooleanMachine.suffix s.input
    terms := Function.update s.terms i { s.terms i with present := SourceBitRead.value s.input }
    available := BooleanMachine.accepted s.input }

def coefficient (s : State) (i : Fin 3) : State :=
  { s with
    before := s.before ++ (EquationCoefficientControl.signed s.input).2.taken
    input := (EquationCoefficientControl.signed s.input).2.rest
    terms := Function.update s.terms i { s.terms i with coefficient := EquationCoefficientLoad.output s.input } }

def prefixState (s : State) (i : Fin 3) : MonomialPrefixControl.State :=
  ⟨s.before, s.input, (s.terms i).flags, (s.terms i).words, s.available⟩

def monomial (fuel : ℕ) (s : State) (i : Fin 3) : State :=
  let t := MonomialPrefixControl.parse fuel (prefixState s i)
  { s with
    before := t.before
    input := t.input
    terms := Function.update s.terms i { s.terms i with flags := t.flags, words := t.words }
    available := t.available }

def body (fuel : ℕ) (s : State) (i : Fin 3) : State := monomial fuel (coefficient s i) i

def term (fuel : ℕ) (s : State) (i : Fin 3) : State :=
  let t := read s i
  if (t.terms i).present then body fuel t i else t

def second (fuel : ℕ) (s : State) : State := if (s.terms 0).present then term fuel s 1 else s

def third (fuel : ℕ) (s : State) : State :=
  if (s.terms 0).present then if (s.terms 1).present then term fuel s 2 else s else s

def close (s : State) : State :=
  if (s.terms 0).present then if (s.terms 1).present then if (s.terms 2).present then
    { s with
      before := s.before ++ BooleanMachine.copied s.input
      input := BooleanMachine.suffix s.input
      available := BooleanMachine.accepted s.input }
  else s else s else s

def parse (fuel : ℕ) (s : State) : State := close (third fuel (second fuel (term fuel s 0)))

def count (s : State) : ℕ := if (s.terms 0).present then if (s.terms 1).present then if (s.terms 2).present then 3 else 2 else 1 else 0

theorem read_split (s : State) (i : Fin 3) : (read s i).before ++ (read s i).input = s.before ++ s.input := by
  simp only [read, List.append_assoc, BooleanMachine.consumed_and_suffix]

theorem coefficient_split (s : State) (i : Fin 3) :
    (coefficient s i).before ++ (coefficient s i).input = s.before ++ s.input := by
  simp only [coefficient, List.append_assoc, EquationCoefficientControl.signed_split]

theorem monomial_split (fuel : ℕ) (s : State) (i : Fin 3) :
    (monomial fuel s i).before ++ (monomial fuel s i).input = s.before ++ s.input :=
  MonomialPrefixControl.parse_split fuel (prefixState s i)

theorem body_split (fuel : ℕ) (s : State) (i : Fin 3) :
    (body fuel s i).before ++ (body fuel s i).input = s.before ++ s.input :=
  (monomial_split _ _ _).trans (coefficient_split s i)

theorem term_split (fuel : ℕ) (s : State) (i : Fin 3) : (term fuel s i).before ++ (term fuel s i).input = s.before ++ s.input := by
  unfold term
  dsimp only
  split
  · exact (body_split _ _ _).trans (read_split s i)
  · exact read_split s i

theorem second_split (fuel : ℕ) (s : State) : (second fuel s).before ++ (second fuel s).input = s.before ++ s.input := by
  unfold second
  split
  · exact term_split _ _ _
  · rfl

theorem third_split (fuel : ℕ) (s : State) : (third fuel s).before ++ (third fuel s).input = s.before ++ s.input := by
  unfold third
  split
  · split
    · exact term_split _ _ _
    · rfl
  · rfl

theorem close_split (s : State) : (close s).before ++ (close s).input = s.before ++ s.input := by
  unfold close
  split
  · split
    · split
      · simp only [List.append_assoc, BooleanMachine.consumed_and_suffix]
      · rfl
    · rfl
  · rfl

theorem parse_split (fuel : ℕ) (s : State) : (parse fuel s).before ++ (parse fuel s).input = s.before ++ s.input :=
  (close_split _).trans ((third_split _ _).trans ((second_split _ _).trans (term_split _ _ _)))

theorem read_length (s : State) (i : Fin 3) : (read s i).input.length ≤ s.input.length := by
  change (BooleanMachine.suffix s.input).length ≤ s.input.length
  cases s.input <;> simp [BooleanMachine.suffix]

theorem coefficient_length (s : State) (i : Fin 3) : (coefficient s i).input.length ≤ s.input.length := by
  have h := congrArg List.length (EquationCoefficientControl.signed_split s.input)
  simp only [List.length_append] at h
  change (EquationCoefficientControl.signed s.input).2.rest.length ≤ s.input.length
  omega

theorem monomial_length (fuel : ℕ) (s : State) (i : Fin 3) : (monomial fuel s i).input.length ≤ s.input.length :=
  MonomialPrefixControl.parse_length fuel (prefixState s i)

theorem body_length (fuel : ℕ) (s : State) (i : Fin 3) : (body fuel s i).input.length ≤ s.input.length :=
  (monomial_length _ _ _).trans (coefficient_length s i)

theorem term_length (fuel : ℕ) (s : State) (i : Fin 3) : (term fuel s i).input.length ≤ s.input.length := by
  unfold term
  dsimp only
  split
  · exact (body_length _ _ _).trans (read_length s i)
  · exact read_length s i

theorem second_length (fuel : ℕ) (s : State) : (second fuel s).input.length ≤ s.input.length := by
  unfold second
  split
  · exact term_length _ _ _
  · exact le_rfl

theorem third_length (fuel : ℕ) (s : State) : (third fuel s).input.length ≤ s.input.length := by
  unfold third
  split
  · split
    · exact term_length _ _ _
    · exact le_rfl
  · exact le_rfl

theorem close_length (s : State) : (close s).input.length ≤ s.input.length := by
  unfold close
  split
  · split
    · split
      · change (BooleanMachine.suffix s.input).length ≤ s.input.length
        cases s.input <;> simp [BooleanMachine.suffix]
      · exact le_rfl
    · exact le_rfl
  · exact le_rfl

theorem parse_length (fuel : ℕ) (s : State) : (parse fuel s).input.length ≤ s.input.length :=
  (close_length _).trans ((third_length _ _).trans ((second_length _ _).trans (term_length _ _ _)))

def code (row : List (ℤ × List ℕ)) : List Bool :=
  RowWordCodec.marked (fun a => BitCodec.integerCode a.1 ++ MarkedNaturalControl.code a.2) row

def stored (old : Term) (a : ℤ × List ℕ) : Term :=
  let t := MonomialPrefixControl.expected ⟨[], [], old.flags, old.words, true⟩ a.2 []
  ⟨true, BitCodec.integerCode a.1, t.flags, t.words⟩

def slots (old : Fin 3 → Term) (row : List (ℤ × List ℕ)) : Fin 3 → Term :=
  match row with
  | [] => Function.update old 0 { old 0 with present := false }
  | [a] => Function.update (Function.update old 0 (stored (old 0) a)) 1 { old 1 with present := false }
  | [a, b] => Function.update (Function.update (Function.update old 0 (stored (old 0) a)) 1 (stored (old 1) b)) 2
      { old 2 with present := false }
  | a :: b :: c :: _ => Function.update (Function.update (Function.update old 0 (stored (old 0) a)) 1 (stored (old 1) b)) 2 (stored (old 2) c)

def expected (s : State) (row : List (ℤ × List ℕ)) (suffix : List Bool) : State :=
  ⟨s.before ++ code row, suffix, slots s.terms row, true⟩

theorem term_nil (fuel : ℕ) (before : List Bool) (terms : Fin 3 → Term) (available : Bool)
    (i : Fin 3) (suffix : List Bool) :
    term fuel ⟨before, false :: suffix, terms, available⟩ i =
      ⟨before ++ [false], suffix, Function.update terms i { terms i with present := false }, true⟩ := by
  simp [term, read, SourceBitRead.value, BooleanMachine.copied, BooleanMachine.suffix, BooleanMachine.accepted]

theorem term_cons (fuel : ℕ) (before : List Bool) (terms : Fin 3 → Term) (available : Bool)
    (i : Fin 3) (a : ℤ × List ℕ) (suffix : List Bool)
    (ha : a.1.natAbs ≤ 5) (hf : a.2.length + 1 ≤ fuel) :
    term fuel ⟨before, true :: (BitCodec.integerCode a.1 ++ (MarkedNaturalControl.code a.2 ++ suffix)), terms, available⟩ i =
      ⟨before ++ [true] ++ BitCodec.integerCode a.1 ++ MarkedNaturalControl.code a.2,
        suffix, Function.update terms i (stored (terms i) a),
        (MonomialPrefixControl.expected ⟨[], [], (terms i).flags, (terms i).words, true⟩ a.2 []).available⟩ := by
  have hc := EquationCoefficientControl.encoded false a.1 ha (MarkedNaturalControl.code a.2 ++ suffix)
  have hv := EquationCoefficientControl.signed_value_code a.1 ha (MarkedNaturalControl.code a.2 ++ suffix)
  have hm (b : List Bool) (f : Fin 3 → Bool) (v : Fin 2 → List Bool) (av : Bool) :=
    MonomialPrefixControl.parse_code fuel ⟨b, [], f, v, av⟩ a.2 suffix hf
  simp only [term, read, SourceBitRead.value, BooleanMachine.copied, BooleanMachine.suffix,
    BooleanMachine.accepted, Function.update_self, ↓reduceIte]
  unfold body coefficient monomial
  simp only [List.append_assoc, EquationCoefficientLoad.output, hv, hc.1, hc.2.1, prefixState,
    Function.update_self, hm]
  rcases a with ⟨z, _ | ⟨u, _ | ⟨v, _ | ⟨q, rest⟩⟩⟩⟩ <;>
    simp [stored, MonomialPrefixControl.expected, List.append_assoc]

theorem parse_code (fuel : ℕ) (s : State) (row : List (ℤ × List ℕ)) (suffix : List Bool)
    (hr : row.length ≤ 3) (ha : ∀ a ∈ row, a.1.natAbs ≤ 5) (hf : ∀ a ∈ row, a.2.length + 1 ≤ fuel) :
    parse fuel { s with input := code row ++ suffix } = expected s row suffix := by
  rcases row with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [parse, second, third, close, code, RowWordCodec.marked, term_nil, expected, slots]
  · simp [parse, second, third, close, code, RowWordCodec.marked, term_cons, term_nil,
      expected, slots, stored, ha a (by simp), hf a (by simp), List.append_assoc]
  · simp [parse, second, third, close, code, RowWordCodec.marked, term_cons, term_nil,
      expected, slots, stored, ha a (by simp), hf a (by simp), ha b (by simp), hf b (by simp), List.append_assoc]
  · have he : rest = [] := by simp only [List.length_cons] at hr; exact List.length_eq_zero_iff.mp (by omega)
    subst rest
    simp [parse, second, third, close, code, RowWordCodec.marked, term_cons,
      expected, slots, stored, ha a (by simp), hf a (by simp), ha b (by simp), hf b (by simp),
      ha c (by simp), hf c (by simp), BooleanMachine.copied,
      BooleanMachine.suffix, BooleanMachine.accepted, List.append_assoc]

theorem expected_count (s : State) (row : List (ℤ × List ℕ)) (suffix : List Bool) (hr : row.length ≤ 3) :
    count (expected s row suffix) = row.length := by
  rcases row with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [count, expected, slots]
  · simp [count, expected, slots, stored]
  · simp [count, expected, slots, stored]
  · have he : rest = [] := by simp only [List.length_cons] at hr; exact List.length_eq_zero_iff.mp (by omega)
    subst rest
    simp [count, expected, slots, stored]

end JointThermoComplexity.Complexity.EquationRowControl

#print axioms JointThermoComplexity.Complexity.EquationRowControl.parse_split
#print axioms JointThermoComplexity.Complexity.EquationRowControl.parse_length
#print axioms JointThermoComplexity.Complexity.EquationRowControl.term_cons
#print axioms JointThermoComplexity.Complexity.EquationRowControl.parse_code
