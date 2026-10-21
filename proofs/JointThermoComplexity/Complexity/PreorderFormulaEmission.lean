module
public import proofs.JointThermoComplexity.Complexity.PreorderTermEmission
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxFP

set_option autoImplicit false
@[expose] public section

/-! Exact forward formula rows from total bounded control, with literal height bounded before emission. -/

namespace JointThermoComplexity.Complexity.PreorderFormulaEmission
open RealSyntax SourceCoordinateEnumeration PreorderLocalRows PreorderEmissionControl
open SmallSyntaxForests (formulaTokens)
variable {n : ℕ}

def Correct (L : ℕ) (p : Formula n) : Prop := ∀ (before suffix : List Bool) (offset forms : ℕ) (rows : Rows),
  (p.code ++ suffix).length ≤ L → p.literalHeight ≤ 2 →
  run L n (formulaTokens p) ⟨⟨before, p.code ++ suffix, 0, forms + 1, offset⟩, rows⟩ =
    ⟨⟨before ++ p.code, suffix, 0, forms, offset + formulaCount p⟩,
      rows ++ words (PreorderFormulaEquations.equations p Fin.val (n + offset))⟩

def atomic (strict : Bool) (a b : Term n) : Formula n := if strict then .lt a b else .eq a b
def atomicTag (strict : Bool) : List Bool := if strict then [false, true, true] else [false, true, false]
def binary (disj : Bool) (p q : Formula n) : Formula n := if disj then .disj p q else .conj p q
def binaryTag (disj : Bool) : List Bool := if disj then [true, false, true] else [true, false, false]

theorem atomic_one (strict : Bool) (L forms offset : ℕ) (a b : Term n) (before suffix : List Bool) (rows : Rows)
    (hlen : ((atomic strict a b).code ++ suffix).length ≤ L) :
    run L n 1 ⟨⟨before, (atomic strict a b).code ++ suffix, 0, forms + 1, offset⟩, rows⟩ =
      ⟨⟨before ++ atomicTag strict, a.code ++ b.code ++ suffix, 2, forms, offset + 4⟩,
        rows ++ words (formulaLocal (atomic strict a b) (n + offset))⟩ := by
  have h := formula_step L forms offset (atomic strict a b) before suffix rows hlen
  have hs : FormulaSpanControl.formulaStep forms ⟨before, (atomic strict a b).code ++ suffix, 0, forms + 1, offset⟩ =
      ⟨before ++ atomicTag strict, a.code ++ b.code ++ suffix, 2, forms, offset + 4⟩ := by
    cases strict <;> simp [atomic, atomicTag, FormulaSpanControl.formulaStep, Formula.code, SourceTags.accepted,
      SourceTermToken.tagBits, SourceBitRead.value, FormulaSpanControl.termCount, FormulaSpanControl.allocation,
      SourceFormulaScan.classify, SourceFormulaScan.Kind.children, List.append_assoc]
  simpa only [run, hs] using h

theorem atomic_correct (strict : Bool) (L : ℕ) (a b : Term n) : Correct L (atomic strict a b) := by
  intro before suffix offset forms rows hlen hh
  have hab : max a.literalHeight b.literalHeight ≤ 2 := by
    cases strict <;> simpa only [atomic, Bool.false_eq_true, ↓reduceIte, Formula.literalHeight] using hh
  have hbody : (a.code ++ b.code ++ suffix).length ≤ L := by
    cases strict <;> simp only [atomic, Bool.false_eq_true, ↓reduceIte, Formula.code, List.length_append,
      List.length_cons, List.length_nil] at hlen <;> simp only [List.length_append] <;> omega
  have hfuel : formulaTokens (atomic strict a b) = 1 + SourceTermScan.forestNodes [a, b] := by
    cases strict <;> simp [atomic, formulaTokens, SourceTermScan.forestNodes, Nat.add_assoc]
  change run L n (formulaTokens (atomic strict a b)) _ = _
  rw [hfuel, run_add L n 1 (SourceTermScan.forestNodes [a, b]), atomic_one strict L forms offset a b before suffix rows hlen]
  have hrec := PreorderTermEmission.run_terms (SourceTermScan.forestNodes [a, b]) [a, b] rfl L
    (before ++ atomicTag strict) suffix (offset + 1) forms (rows ++ words (formulaLocal (atomic strict a b) (n + offset)))
    (by simpa [SourceTermScan.forestCode, List.append_assoc] using hbody)
    (by
      intro t ht
      have he : t = a ∨ t = b := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using ht
      rcases he with rfl | rfl
      · exact ((Nat.le_max_left _ _).trans hab)
      · exact ((Nat.le_max_right _ _).trans hab))
  have hc : offset + 1 + 3 + SourceTermScan.forestNodes [a, b] = offset + formulaCount (atomic strict a b) := by
    cases strict <;> simp only [atomic, Bool.false_eq_true, ↓reduceIte, formulaCount,
      SourceTermScan.forestNodes_cons, SourceTermScan.forestNodes_nil] <;> omega
  rw [hc] at hrec
  cases strict <;> simpa [atomic, atomicTag, Formula.code, PreorderFormulaEquations.equations, formulaLocal,
    PreorderTermEmission.termForest, words, SourceTermScan.forestCode, List.map_append, List.append_assoc, Nat.add_assoc] using hrec

theorem binary_one (disj : Bool) (L forms offset : ℕ) (p q : Formula n) (before suffix : List Bool) (rows : Rows)
    (hlen : ((binary disj p q).code ++ suffix).length ≤ L) :
    run L n 1 ⟨⟨before, (binary disj p q).code ++ suffix, 0, forms + 1, offset⟩, rows⟩ =
      ⟨⟨before ++ binaryTag disj, p.code ++ q.code ++ suffix, 0, forms + 2, offset + 1⟩,
        rows ++ words (formulaLocal (binary disj p q) (n + offset))⟩ := by
  have h := formula_step L forms offset (binary disj p q) before suffix rows hlen
  have hs : FormulaSpanControl.formulaStep forms ⟨before, (binary disj p q).code ++ suffix, 0, forms + 1, offset⟩ =
      ⟨before ++ binaryTag disj, p.code ++ q.code ++ suffix, 0, forms + 2, offset + 1⟩ := by
    cases disj <;> simp [binary, binaryTag, FormulaSpanControl.formulaStep, Formula.code, SourceTags.accepted,
      SourceTermToken.tagBits, SourceBitRead.value, FormulaSpanControl.termCount, FormulaSpanControl.allocation,
      SourceFormulaScan.classify, SourceFormulaScan.Kind.children, List.append_assoc]
  simpa only [run, hs] using h

theorem binary_correct (disj : Bool) (L : ℕ) (p q : Formula n) (hp : Correct L p) (hq : Correct L q) : Correct L (binary disj p q) := by
  intro before suffix offset forms rows hlen hh
  have hab : max p.literalHeight q.literalHeight ≤ 2 := by
    cases disj <;> simpa only [binary, Bool.false_eq_true, ↓reduceIte, Formula.literalHeight] using hh
  have hbody : (p.code ++ q.code ++ suffix).length ≤ L := by
    cases disj <;> simp only [binary, Bool.false_eq_true, ↓reduceIte, Formula.code, List.length_append,
      List.length_cons, List.length_nil] at hlen <;> simp only [List.length_append] <;> omega
  have hfuel : formulaTokens (binary disj p q) = 1 + formulaTokens p + formulaTokens q := by cases disj <;> rfl
  change run L n (formulaTokens (binary disj p q)) _ = _
  rw [hfuel, run_add L n (1 + formulaTokens p) (formulaTokens q), run_add L n 1 (formulaTokens p),
    binary_one disj L forms offset p q before suffix rows hlen]
  have hleft := hp (before ++ binaryTag disj) (q.code ++ suffix) (offset + 1) (forms + 1)
    (rows ++ words (formulaLocal (binary disj p q) (n + offset)))
    (by simpa only [List.append_assoc] using hbody) ((Nat.le_max_left _ _).trans hab)
  simp only [List.append_assoc]
  rw [hleft]
  have hright := hq ((before ++ binaryTag disj) ++ p.code) suffix (offset + 1 + formulaCount p) forms
    ((rows ++ words (formulaLocal (binary disj p q) (n + offset))) ++ words (PreorderFormulaEquations.equations p Fin.val (n + (offset + 1))))
    (by simp only [List.length_append] at hbody ⊢; omega) ((Nat.le_max_right _ _).trans hab)
  rw [hright]
  cases disj <;> simp [binary, binaryTag, Formula.code, formulaCount, PreorderFormulaEquations.equations,
    formulaLocal, words, List.map_append, List.append_assoc, Nat.add_assoc]

theorem correct (L : ℕ) (p : Formula n) : Correct L p := by
  induction p with
  | truth =>
    intro before suffix offset forms rows hlen _hh
    have h := formula_step L forms offset (Formula.truth : Formula n) before suffix rows hlen
    simpa [run, formulaTokens, FormulaSpanControl.formulaStep, Formula.code, SourceTags.accepted, SourceTermToken.tagBits,
      SourceBitRead.value, FormulaSpanControl.termCount, FormulaSpanControl.allocation, SourceFormulaScan.classify,
      SourceFormulaScan.Kind.children, formulaCount, PreorderFormulaEquations.equations, formulaLocal] using h
  | falsity =>
    intro before suffix offset forms rows hlen _hh
    have h := formula_step L forms offset (Formula.falsity : Formula n) before suffix rows hlen
    simpa [run, formulaTokens, FormulaSpanControl.formulaStep, Formula.code, SourceTags.accepted, SourceTermToken.tagBits,
      SourceBitRead.value, FormulaSpanControl.termCount, FormulaSpanControl.allocation, SourceFormulaScan.classify,
      SourceFormulaScan.Kind.children, formulaCount, PreorderFormulaEquations.equations, formulaLocal] using h
  | eq a b => exact atomic_correct false L a b
  | lt a b => exact atomic_correct true L a b
  | conj p q hp hq => exact binary_correct false L p q hp hq
  | disj p q hp hq => exact binary_correct true L p q hp hq

theorem input_length_fuel (L : ℕ) (p : Formula n) (before suffix : List Bool) (rows : Rows)
    (hlen : (p.code ++ suffix).length ≤ L) (hh : p.literalHeight ≤ 2) :
    run L n L ⟨⟨before, p.code ++ suffix, 0, 1, 0⟩, rows⟩ =
      ⟨⟨before ++ p.code, suffix, 0, 0, formulaCount p⟩,
        rows ++ words (PreorderFormulaEquations.equations p Fin.val n)⟩ := by
  have hn : formulaTokens p ≤ L := by have := SmallSyntaxForests.formulaTokens_le_code_length p; rw [List.length_append] at hlen; omega
  have he := correct L p before suffix 0 0 rows hlen hh
  have hf : formulaTokens p + (L - formulaTokens p) = L := by omega
  conv_lhs =>
    arg 3
    rw [← hf]
  rw [run_add L n, he, run_finished]
  simp only [Nat.zero_add, Nat.add_zero]

def result (input : List Bool) : State := run input.length (HeaderControl.count input) input.length
  ⟨⟨HeaderControl.copied input, HeaderControl.suffix input, 0, 1, 0⟩, []⟩

def rows (input : List Bool) : Rows := (result input).emitted ++
  words [SparseInteger.sub (SparseInteger.atom (HeaderControl.count input)) (SparseInteger.constant 1)]

theorem result_sentence (s : Sentence) (hh : s.formula.literalHeight ≤ 2) :
    (result s.code).emitted = words (PreorderFormulaEquations.equations s.formula Fin.val s.arity) := by
  have hlen : (s.formula.code ++ []).length ≤ s.code.length := by
    simp only [List.append_nil, Sentence.code, List.length_append]
    omega
  have h := input_length_fuel s.code.length s.formula (HeaderControl.copied s.code) [] [] hlen hh
  have he := congrArg State.emitted h
  simpa only [result, Sentence.code, HeaderControl.count_code, HeaderControl.copied_code,
    HeaderControl.suffix_code, List.append_nil, List.nil_append] using he

theorem rows_sentence (s : Sentence) (hh : s.formula.literalHeight ≤ 2) :
    rows s.code = words (PreorderSourceEquations.equations s) := by
  have hc : HeaderControl.count s.code = s.arity := by simp only [Sentence.code, HeaderControl.count_code]
  unfold rows
  rw [result_sentence s hh, hc]
  simp only [PreorderSourceEquations.equations, PreorderFormulaEquations.closed, words, List.map_append]

def normalized (input : List Bool) : Rows := rows (SmallSyntaxFP.code input)

theorem normalized_eq (input : List Bool) : normalized input = words (PreorderSourceEquations.normalized input) :=
  rows_sentence (SourceSmallLiterals.normalizeSmall input) (SourceSmallLiterals.normalizeSmall_height input)

end JointThermoComplexity.Complexity.PreorderFormulaEmission

#print axioms JointThermoComplexity.Complexity.PreorderFormulaEmission.correct
#print axioms JointThermoComplexity.Complexity.PreorderFormulaEmission.input_length_fuel
#print axioms JointThermoComplexity.Complexity.PreorderFormulaEmission.normalized_eq
