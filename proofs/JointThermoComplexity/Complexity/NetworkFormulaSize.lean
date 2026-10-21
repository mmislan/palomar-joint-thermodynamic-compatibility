module
public import proofs.JointThermoComplexity.Complexity.NetworkMembership
public import proofs.JointThermoComplexity.Complexity.CircuitSize

set_option autoImplicit false
@[expose] public section

/-!
# Size of the complete generated sentence

The bound is polynomial in finite dimensions, auxiliary gate count, a bound on
encoded integer literals, and the total encoded constants of the circuit. It
uses the actual binary sentence code, including all existential binders. Bounds
on those parameters in a decoded network's serialized input remain separate.
-/

namespace JointThermoComplexity.Complexity.NetworkFormulaSize
open RealSyntax RealCircuit NetworkData NetworkFormula NetworkMembership CircuitSize BitCodec

variable {n r c m : ℕ}

def conjunctionBound (A B : ℕ) : ℕ := 3 + A + B
def allBound (count B : ℕ) : ℕ := 3 + count * (B + 3)
def directionBound (m : ℕ) : ℕ := 2 * m + 15
def productionBound (m r B : ℕ) : ℕ := 13 + r * (B + 2 * m + 13)
def boxBound (m B : ℕ) : ℕ := 8 * B + 8 * m + 73
def coreBound (m n r B : ℕ) : ℕ :=
  conjunctionBound (allBound r (directionBound m)) (allBound n (productionBound m r B))
def constraintsBound (m n r c B : ℕ) : ℕ :=
  conjunctionBound (allBound n (2 * m + 12))
    (conjunctionBound (allBound n (boxBound m B)) (allBound c (coreBound m n r B)))

def BoxLiteralsBound (box : Option ClosedBox) (B : ℕ) : Prop :=
  match box with
  | none => True
  | some b => (integerCode b.lower.numerator).length ≤ B ∧
      (integerCode (b.lower.denominator : ℤ)).length ≤ B ∧
      (integerCode b.upper.numerator).length ≤ B ∧
      (integerCode (b.upper.denominator : ℤ)).length ≤ B

def LiteralsBound (Q : Network n r c) (B : ℕ) : Prop :=
  (∀ i, (integerCode ((Q.reactions i).denominator : ℤ)).length ≤ B) ∧
  (∀ i s, (integerCode (stoich (Q.reactions i) s)).length ≤ B) ∧
  ∀ s, BoxLiteralsBound (Q.boxes s) B

theorem conjunction_code_le (p q : Formula m) (A B : ℕ)
    (hp : p.code.length ≤ A) (hq : q.code.length ≤ B) :
    (Formula.conj p q).code.length ≤ conjunctionBound A B := by
  simp only [Formula.code, List.length_append, List.length_cons, List.length_nil,
    conjunctionBound]
  omega

theorem integer_term_code (z : ℤ) : (Term.int z : Term m).code.length =
    3 + (integerCode z).length := by
  simp only [Term.code, List.length_append, List.length_cons, List.length_nil]

theorem zero_term_code : (Term.int 0 : Term m).code.length = 5 := by
  simp [Term.code, integerCode, naturalCode, encodeBits]

theorem lessEqual_code_le (s t : Term m) (A B : ℕ)
    (hs : s.code.length ≤ A) (ht : t.code.length ≤ B) :
    (lessEqual s t).code.length ≤ 9 + 2 * A + 2 * B := by
  simp only [lessEqual, Formula.code, List.length_append, List.length_cons, List.length_nil]
  omega

theorem box_code_le (box : Option ClosedBox) (z : Fin m) (B : ℕ)
    (h : BoxLiteralsBound box B) :
    (boxFormula box z).code.length ≤ boxBound m B := by
  cases box with
  | none => simp [boxFormula, Formula.code, boxBound]
  | some b =>
    obtain ⟨hln, hld, hun, hud⟩ := h
    have hv := variable_code_length_le z
    have hlow := lessEqual_code_le (.int b.lower.numerator)
      (.mul (.int b.lower.denominator) (.var z)) (B + 3) (B + 2 * m + 10)
      (by rw [integer_term_code]; omega) (by
        simp only [Term.code, List.length_append, List.length_cons, List.length_nil]
        simp only [Term.code, List.length_append, List.length_cons, List.length_nil] at hv
        omega)
    have hupp := lessEqual_code_le
      (.mul (.int b.upper.denominator) (.var z)) (.int b.upper.numerator)
      (B + 2 * m + 10) (B + 3) (by
        simp only [Term.code, List.length_append, List.length_cons, List.length_nil]
        simp only [Term.code, List.length_append, List.length_cons, List.length_nil] at hv
        omega) (by rw [integer_term_code]; omega)
    have hc := conjunction_code_le _ _ _ _ hlow hupp
    simp only [conjunctionBound] at hc
    change _ ≤ 8 * B + 8 * m + 73
    simp only [boxFormula]
    omega

theorem direction_code_le (forward : Bool) (j : Fin m) :
    (directionFormula forward j).code.length ≤ directionBound m := by
  have hv := variable_code_length_le j
  cases forward <;>
    simp only [directionFormula, Bool.false_eq_true, ↓reduceIte,
      Formula.code, Term.code, List.length_append, List.length_cons, List.length_nil,
      directionBound] at hv ⊢ <;>
    have hzero := (zero_term_code (m := m)) <;>
    simp only [Term.code, List.length_append, List.length_cons, List.length_nil] at hzero <;>
    omega

theorem production_code_le (Q : Network n r c) (a : Fin c) (s : Fin n)
    (j : Fin r → Fin m) (B : ℕ)
    (h : ∀ i, (integerCode (stoich (Q.reactions i) s)).length ≤ B) :
    (productionTerm Q a s j).code.length ≤ 5 + r * (B + 2 * m + 13) := by
  apply sumFin_code_length_le _ (B + 2 * m + 10)
  intro i
  split
  · have hv := variable_code_length_le (j i)
    have hc := h i
    simp only [Term.code, List.length_append, List.length_cons, List.length_nil] at hv ⊢
    omega
  · rw [zero_term_code]
    omega

theorem constraints_code_le (Q : Network n r c) (z : Fin n → Fin m)
    (j : Fin r → Fin m) (B : ℕ) (h : LiteralsBound Q B) :
    (constraintsFormula Q z j).code.length ≤ constraintsBound m n r c B := by
  apply conjunction_code_le
  · apply allFin_code_length_le _ (2 * m + 12)
    intro s
    have hv := variable_code_length_le (z s)
    have hzero := (zero_term_code (m := m))
    simp only [Formula.code, List.length_append, List.length_cons, List.length_nil]
    omega
  · apply conjunction_code_le
    · apply allFin_code_length_le
      intro s
      exact box_code_le _ _ B (h.2.2 s)
    · apply allFin_code_length_le
      intro a
      apply conjunction_code_le
      · apply allFin_code_length_le
        intro i
        split
        · exact direction_code_le _ _
        · simp [Formula.code, directionBound]
      · apply allFin_code_length_le
        intro s
        split
        · have hp := production_code_le Q a s j B (fun i => h.2.1 i s)
          have hzero := (zero_term_code (m := m))
          simp only [Formula.code, List.length_append, List.length_cons, List.length_nil,
            productionBound]
          omega
        · simp only [Formula.code, List.length_cons, List.length_nil, productionBound]
          omega

def formulaBound (Q : Network n r c) (B : ℕ) : ℕ :=
  conjunctionBound (3 + gates Q * (6 * arity Q + 22) +
    weight (NetworkCircuit.dense Q.reactions).circuit)
    (conjunctionBound (allBound r (B + 4 * arity Q + 17))
      (constraintsBound (arity Q) n r c B))

theorem formula_code_le (Q : Network n r c) (B : ℕ) (h : LiteralsBound Q B) :
    (formula Q).code.length ≤ formulaBound Q B := by
  apply conjunction_code_le
  · exact formula_code_length_le _ _ _
  · apply conjunction_code_le
    · apply allFin_code_length_le _ (B + 4 * arity Q + 17)
      intro i
      have hv := variable_code_length_le (currentIndex Q i)
      have hg := variable_code_length_le (auxiliaryIndex Q (NetworkCircuit.output Q.reactions i))
      have hd := h.1 i
      simp only [Formula.code, Term.code, List.length_append, List.length_cons,
        List.length_nil] at hv hg ⊢
      omega
    · exact constraints_code_le _ _ _ B h

theorem sentence_code_le (Q : Network n r c) (B : ℕ) (h : LiteralsBound Q B) :
    (sentence Q).code.length ≤ arity Q + 1 + formulaBound Q B := by
  have hf := formula_code_le Q B h
  simp only [Sentence.code, sentence, binderCode, List.length_append,
    List.length_cons, List.length_nil, List.length_replicate]
  omega

end JointThermoComplexity.Complexity.NetworkFormulaSize

#print axioms JointThermoComplexity.Complexity.NetworkFormulaSize.sentence_code_le
