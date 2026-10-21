module
public import proofs.JointThermoComplexity.Complexity.SparseListCodec
public import proofs.JointThermoComplexity.Complexity.RawSourceMagnitude
public import Mathlib.Algebra.Polynomial.Eval.Degree

set_option autoImplicit false
@[expose] public section

/-! # Faithful binary format and polynomial size of the emitted integer lists

The declared arity is unary; signed coefficients and variable IDs are binary.
Monomials list variable occurrences, including repeats. Stored zero terms and
repeated monomials are preserved. These are serialization and size theorems,
not a binary construction-runtime theorem.
-/

namespace JointThermoComplexity.Complexity.SparsePolynomialCodec
open FiniteCodec BitCodec SparseInteger
open RealSyntax NumericStrictData NumericStrictRawBounds RawSourceMagnitude

structure PolynomialData where
  arity : ℕ
  payload : Poly (Fin arity)

def term (n : ℕ) : Codec (ℤ × List (Fin n)) :=
  FiniteCodec.product FiniteCodec.integer (SparseListCodec.list (SparseListCodec.finite n))

def polynomial (n : ℕ) : Codec (Poly (Fin n)) := SparseListCodec.list (term n)

def code (p : PolynomialData) : List Bool := SparseListCodec.unaryCode p.arity ++ (polynomial p.arity).code p.payload

def parse (input : List Bool) : Option (PolynomialData × List Bool) := do
  let (n, rest) ← SparseListCodec.parseUnary input
  let (ps, suffix) ← (polynomial n).parse rest
  pure (⟨n, ps⟩, suffix)

theorem parse_code (p : PolynomialData) (suffix : List Bool) : parse (code p ++ suffix) = some (p, suffix) := by
  cases p with
  | mk n ps => simp [code, parse, List.append_assoc, SparseListCodec.parseUnary_code, (polynomial n).roundtrip]

theorem parse_sound {input suffix : List Bool} {p : PolynomialData}
    (h : parse input = some (p, suffix)) : input = code p ++ suffix := by
  cases hn : SparseListCodec.parseUnary input with
  | none => simp [parse, hn] at h
  | some pair =>
    obtain ⟨n, rest⟩ := pair
    cases hp : (polynomial n).parse rest with
    | none => simp [parse, hn, hp] at h
    | some pair =>
      obtain ⟨ps, tail⟩ := pair
      simp [parse, hn, hp] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [SparseListCodec.parseUnary_sound hn, (polynomial n).sound hp]
      simp only [code, List.append_assoc]

def codec : Codec PolynomialData := ⟨code, parse, parse_code, parse_sound⟩

def decode (input : List Bool) : Option PolynomialData :=
  match parse input with
  | some (p, []) => some p
  | _ => none

theorem decode_code (p : PolynomialData) : decode (code p) = some p := by
  have h := parse_code p []
  simp only [List.append_nil] at h
  simp only [decode, h]

theorem decode_sound {input : List Bool} {p : PolynomialData} (h : decode input = some p) : input = code p := by
  cases hp : parse input with
  | none => simp [decode, hp] at h
  | some pair =>
    obtain ⟨q, tail⟩ := pair
    cases tail with
    | nil =>
      simp only [decode, hp, Option.some.injEq] at h
      subst q
      simpa only [List.append_nil] using parse_sound hp
    | cons b tail => simp [decode, hp] at h

theorem code_injective : Function.Injective code := codec.code_injective

theorem term_code_length (n : ℕ) (a : ℤ × List (Fin n)) (D C : ℕ)
    (hD : a.2.length ≤ D) (hC : (integerCode a.1).length ≤ C) :
    ((term n).code a).length ≤ C + D * (2 * n + 2) + 1 := by
  have hv := SparseListCodec.listCode_length_le (SparseListCodec.finite n) a.2 (2 * n + 1)
    (fun i _ => SparseListCodec.finite_code_length n i)
  have hm := Nat.mul_le_mul_right (2 * n + 2) hD
  change (integerCode a.1 ++ SparseListCodec.listCode (SparseListCodec.finite n) a.2).length ≤ _
  rw [List.length_append]
  change (SparseListCodec.listCode (SparseListCodec.finite n) a.2).length ≤ a.2.length * (2 * n + 2) + 1 at hv
  omega

theorem polynomial_code_length (n : ℕ) (p : Poly (Fin n)) (D C : ℕ) (hD : DegreeLE D p)
    (hC : ∀ a ∈ p, (integerCode a.1).length ≤ C) :
    ((polynomial n).code p).length ≤ p.length * (C + D * (2 * n + 2) + 2) + 1 :=
  SparseListCodec.listCode_length_le (term n) p _ (fun a ha => term_code_length n a D C (hD a ha) (hC a ha))

theorem code_length (p : PolynomialData) (D C : ℕ) (hD : DegreeLE D p.payload)
    (hC : ∀ a ∈ p.payload, (integerCode a.1).length ≤ C) :
    (code p).length ≤ p.arity + 2 + p.payload.length * (C + D * (2 * p.arity + 2) + 2) := by
  have h := polynomial_code_length p.arity p.payload D C hD hC
  rw [code, List.length_append, SparseListCodec.unaryCode_length]
  omega

def boundedData (s : Sentence) : PolynomialData := ⟨variableCount s, NumericStrictData.bounded s⟩
def allRealData (s : Sentence) : PolynomialData := ⟨variableCount s, NumericStrictData.allReal s⟩
def boundedCode (s : Sentence) : List Bool := code (boundedData s)
def allRealCode (s : Sentence) : List Bool := code (allRealData s)

def sizeBound (L : ℕ) : ℕ :=
  coordinateBound L + 2 + termCountBound L * (2 * coefficientBitsBound L + 8 * coordinateBound L + 12)

theorem source_code_length (s : Sentence) (p : Poly (Fin (variableCount s))) (hD : DegreeLE 4 p)
    (hC : ∀ a ∈ p, (integerCode a.1).length ≤ 2 * coefficientBitsBound s.code.length + 2)
    (hM : p.length ≤ termCountBound s.code.length) :
    (code ⟨variableCount s, p⟩).length ≤ sizeBound s.code.length := by
  have h := code_length (⟨variableCount s, p⟩ : PolynomialData) 4 (2 * coefficientBitsBound s.code.length + 2) hD hC
  have hn := RawSourceMagnitude.coordinate_count s
  have hf : 2 * coefficientBitsBound s.code.length + 2 + 4 * (2 * variableCount s + 2) + 2 ≤
      2 * coefficientBitsBound s.code.length + 8 * coordinateBound s.code.length + 12 := by omega
  have hm := Nat.mul_le_mul hM hf
  exact h.trans (Nat.add_le_add (Nat.add_le_add_right hn 2) hm)

theorem boundedCode_length (s : Sentence) : (boundedCode s).length ≤ sizeBound s.code.length :=
  source_code_length s _ (NumericStrictData.bounded_raw_degree s)
    (RawSourceMagnitude.bounded_coefficient_code s) (NumericStrictRawBounds.bounded_term_count s)

theorem allRealCode_length (s : Sentence) : (allRealCode s).length ≤ sizeBound s.code.length :=
  source_code_length s _ (NumericStrictData.allReal_raw_degree s)
    (RawSourceMagnitude.allReal_coefficient_code s) (NumericStrictRawBounds.allReal_term_count s)

noncomputable def coordinatePolynomial : Polynomial ℕ :=
  57600 * Polynomial.X ^ 4 + 518880 * Polynomial.X ^ 3 + 1291440 * Polynomial.X ^ 2 + 553437 * Polynomial.X + 65225

noncomputable def coefficientPolynomial : Polynomial ℕ :=
  57600 * Polynomial.X ^ 4 + 518880 * Polynomial.X ^ 3 + 1291440 * Polynomial.X ^ 2 + 553438 * Polynomial.X + 65251

noncomputable def termPolynomial : Polynomial ℕ :=
  230400 * Polynomial.X ^ 4 + 2075520 * Polynomial.X ^ 3 + 5166360 * Polynomial.X ^ 2 + 2216439 * Polynomial.X + 261501

noncomputable def sizePolynomial : Polynomial ℕ :=
  coordinatePolynomial + 2 + termPolynomial * (2 * coefficientPolynomial + 8 * coordinatePolynomial + 12)

theorem sizePolynomial_eval (L : ℕ) : sizePolynomial.eval L = sizeBound L := by
  simp [sizePolynomial, coordinatePolynomial, coefficientPolynomial, termPolynomial, sizeBound,
    coordinateBound, coefficientBitsBound_formula, termCountBound_formula]

end JointThermoComplexity.Complexity.SparsePolynomialCodec

#print axioms JointThermoComplexity.Complexity.SparsePolynomialCodec.parse_code
#print axioms JointThermoComplexity.Complexity.SparsePolynomialCodec.parse_sound
#print axioms JointThermoComplexity.Complexity.SparsePolynomialCodec.decode_sound
#print axioms JointThermoComplexity.Complexity.SparsePolynomialCodec.code_injective
#print axioms JointThermoComplexity.Complexity.SparsePolynomialCodec.boundedCode_length
#print axioms JointThermoComplexity.Complexity.SparsePolynomialCodec.allRealCode_length
#print axioms JointThermoComplexity.Complexity.SparsePolynomialCodec.sizePolynomial_eval
