module
public import proofs.JointThermoComplexity.Complexity.BitCodec
public import Mathlib.Basic.Real.Basic

set_option autoImplicit false
@[expose] public section

/-!
# Finite existential-real sentences and their binary representation

The language is defined before, and independently of, reaction networks.
Integer literals use the canonical binary codec. A sentence explicitly lists
its existential binders through a unary variable-count header; hence its number
of declared variables is bounded by its encoded length. All variable references
are range checked. Parsers use fuel bounded by input length and reject trailing
data. No machine-runtime or source-hardness theorem is asserted by this module.
-/

namespace JointThermoComplexity.Complexity.RealSyntax
open BitCodec

inductive Term (n : ℕ) where
  | int : ℤ → Term n
  | var : Fin n → Term n
  | add : Term n → Term n → Term n
  | mul : Term n → Term n → Term n
  | neg : Term n → Term n
  deriving DecidableEq

inductive Formula (n : ℕ) where
  | truth : Formula n
  | falsity : Formula n
  | eq : Term n → Term n → Formula n
  | lt : Term n → Term n → Formula n
  | conj : Formula n → Formula n → Formula n
  | disj : Formula n → Formula n → Formula n
  deriving DecidableEq

variable {n : ℕ}

def Term.eval (ρ : Fin n → ℝ) : Term n → ℝ
  | .int z => z
  | .var i => ρ i
  | .add s t => s.eval ρ + t.eval ρ
  | .mul s t => s.eval ρ * t.eval ρ
  | .neg t => -t.eval ρ

def Formula.eval (ρ : Fin n → ℝ) : Formula n → Prop
  | .truth => True
  | .falsity => False
  | .eq s t => s.eval ρ = t.eval ρ
  | .lt s t => s.eval ρ < t.eval ρ
  | .conj p q => p.eval ρ ∧ q.eval ρ
  | .disj p q => p.eval ρ ∨ q.eval ρ

def Term.depth : Term n → ℕ
  | .int _ | .var _ => 1
  | .add s t | .mul s t => 1 + max s.depth t.depth
  | .neg t => 1 + t.depth

def Formula.depth : Formula n → ℕ
  | .truth | .falsity => 1
  | .eq s t | .lt s t => 1 + max s.depth t.depth
  | .conj p q | .disj p q => 1 + max p.depth q.depth

def Term.code : Term n → List Bool
  | .int z => [false, false, false] ++ integerCode z
  | .var i => [false, false, true] ++ naturalCode i.val
  | .add s t => [false, true, false] ++ s.code ++ t.code
  | .mul s t => [false, true, true] ++ s.code ++ t.code
  | .neg t => [true, false, false] ++ t.code

def Formula.code : Formula n → List Bool
  | .truth => [false, false, false]
  | .falsity => [false, false, true]
  | .eq s t => [false, true, false] ++ s.code ++ t.code
  | .lt s t => [false, true, true] ++ s.code ++ t.code
  | .conj p q => [true, false, false] ++ p.code ++ q.code
  | .disj p q => [true, false, true] ++ p.code ++ q.code

def parseTerm (n : ℕ) : ℕ → List Bool → Option (Term n × List Bool)
  | 0, _ => none
  | k + 1, input =>
    match input with
    | false :: false :: false :: rest => do
        let (z, tail) ← parseInteger rest
        pure (.int z, tail)
    | false :: false :: true :: rest => do
        let (i, tail) ← parseNatural rest
        if h : i < n then pure (.var ⟨i, h⟩, tail) else none
    | false :: true :: false :: rest => do
        let (s, rest) ← parseTerm n k rest
        let (t, tail) ← parseTerm n k rest
        pure (.add s t, tail)
    | false :: true :: true :: rest => do
        let (s, rest) ← parseTerm n k rest
        let (t, tail) ← parseTerm n k rest
        pure (.mul s t, tail)
    | true :: false :: false :: rest => do
        let (t, tail) ← parseTerm n k rest
        pure (.neg t, tail)
    | _ => none

def parseFormula (n : ℕ) : ℕ → List Bool → Option (Formula n × List Bool)
  | 0, _ => none
  | k + 1, input =>
    match input with
    | false :: false :: false :: rest => some (.truth, rest)
    | false :: false :: true :: rest => some (.falsity, rest)
    | false :: true :: false :: rest => do
        let (s, rest) ← parseTerm n k rest
        let (t, tail) ← parseTerm n k rest
        pure (.eq s t, tail)
    | false :: true :: true :: rest => do
        let (s, rest) ← parseTerm n k rest
        let (t, tail) ← parseTerm n k rest
        pure (.lt s t, tail)
    | true :: false :: false :: rest => do
        let (p, rest) ← parseFormula n k rest
        let (q, tail) ← parseFormula n k rest
        pure (.conj p q, tail)
    | true :: false :: true :: rest => do
        let (p, rest) ← parseFormula n k rest
        let (q, tail) ← parseFormula n k rest
        pure (.disj p q, tail)
    | _ => none

theorem parseTerm_code (t : Term n) (fuel : ℕ) (suffix : List Bool)
    (hf : t.depth ≤ fuel) :
    parseTerm n fuel (t.code ++ suffix) = some (t, suffix) := by
  induction t generalizing fuel suffix with
  | int z =>
    cases fuel with
    | zero => simp [Term.depth] at hf
    | succ k => simp [Term.code, parseTerm]
  | var i =>
    cases fuel with
    | zero => simp [Term.depth] at hf
    | succ k => simp [Term.code, parseTerm, i.isLt]
  | add s t ihs iht =>
    cases fuel with
    | zero => simp [Term.depth] at hf
    | succ k =>
      have hs : s.depth ≤ k := by simp only [Term.depth] at hf; omega
      have ht : t.depth ≤ k := by simp only [Term.depth] at hf; omega
      simp [Term.code, parseTerm, List.append_assoc,
        ihs k (t.code ++ suffix) hs, iht k suffix ht]
  | mul s t ihs iht =>
    cases fuel with
    | zero => simp [Term.depth] at hf
    | succ k =>
      have hs : s.depth ≤ k := by simp only [Term.depth] at hf; omega
      have ht : t.depth ≤ k := by simp only [Term.depth] at hf; omega
      simp [Term.code, parseTerm, List.append_assoc,
        ihs k (t.code ++ suffix) hs, iht k suffix ht]
  | neg t ih =>
    cases fuel with
    | zero => simp [Term.depth] at hf
    | succ k =>
      have ht : t.depth ≤ k := by simp only [Term.depth] at hf; omega
      simp [Term.code, parseTerm, ih k suffix ht]

theorem parseFormula_code (p : Formula n) (fuel : ℕ) (suffix : List Bool)
    (hf : p.depth ≤ fuel) :
    parseFormula n fuel (p.code ++ suffix) = some (p, suffix) := by
  induction p generalizing fuel suffix with
  | truth =>
    cases fuel with
    | zero => simp [Formula.depth] at hf
    | succ k => rfl
  | falsity =>
    cases fuel with
    | zero => simp [Formula.depth] at hf
    | succ k => rfl
  | eq s t =>
    cases fuel with
    | zero => simp [Formula.depth] at hf
    | succ k =>
      have hs : s.depth ≤ k := by simp only [Formula.depth] at hf; omega
      have ht : t.depth ≤ k := by simp only [Formula.depth] at hf; omega
      simp [Formula.code, parseFormula, List.append_assoc,
        parseTerm_code s k (t.code ++ suffix) hs, parseTerm_code t k suffix ht]
  | lt s t =>
    cases fuel with
    | zero => simp [Formula.depth] at hf
    | succ k =>
      have hs : s.depth ≤ k := by simp only [Formula.depth] at hf; omega
      have ht : t.depth ≤ k := by simp only [Formula.depth] at hf; omega
      simp [Formula.code, parseFormula, List.append_assoc,
        parseTerm_code s k (t.code ++ suffix) hs, parseTerm_code t k suffix ht]
  | conj p q ihp ihq =>
    cases fuel with
    | zero => simp [Formula.depth] at hf
    | succ k =>
      have hp : p.depth ≤ k := by simp only [Formula.depth] at hf; omega
      have hq : q.depth ≤ k := by simp only [Formula.depth] at hf; omega
      simp [Formula.code, parseFormula, List.append_assoc,
        ihp k (q.code ++ suffix) hp, ihq k suffix hq]
  | disj p q ihp ihq =>
    cases fuel with
    | zero => simp [Formula.depth] at hf
    | succ k =>
      have hp : p.depth ≤ k := by simp only [Formula.depth] at hf; omega
      have hq : q.depth ≤ k := by simp only [Formula.depth] at hf; omega
      simp [Formula.code, parseFormula, List.append_assoc,
        ihp k (q.code ++ suffix) hp, ihq k suffix hq]

theorem Term.depth_le_code_length (t : Term n) : t.depth ≤ t.code.length := by
  induction t with
  | int z =>
    simp only [Term.depth, Term.code, List.length_append, List.length_cons, List.length_nil]
    omega
  | var i =>
    simp only [Term.depth, Term.code, List.length_append, List.length_cons, List.length_nil]
    omega
  | add s t ihs iht =>
    simp only [Term.depth, Term.code, List.length_append, List.length_cons, List.length_nil]
    omega
  | mul s t ihs iht =>
    simp only [Term.depth, Term.code, List.length_append, List.length_cons, List.length_nil]
    omega
  | neg t ih =>
    simp only [Term.depth, Term.code, List.length_append, List.length_cons, List.length_nil]
    omega

theorem Formula.depth_le_code_length (p : Formula n) : p.depth ≤ p.code.length := by
  induction p with
  | truth =>
    simp only [Formula.depth, Formula.code, List.length_cons, List.length_nil]
    omega
  | falsity =>
    simp only [Formula.depth, Formula.code, List.length_cons, List.length_nil]
    omega
  | eq s t =>
    have hs := s.depth_le_code_length
    have ht := t.depth_le_code_length
    simp only [Formula.depth, Formula.code, List.length_append, List.length_cons, List.length_nil]
    omega
  | lt s t =>
    have hs := s.depth_le_code_length
    have ht := t.depth_le_code_length
    simp only [Formula.depth, Formula.code, List.length_append, List.length_cons, List.length_nil]
    omega
  | conj p q ihp ihq =>
    simp only [Formula.depth, Formula.code, List.length_append, List.length_cons, List.length_nil]
    omega
  | disj p q ihp ihq =>
    simp only [Formula.depth, Formula.code, List.length_append, List.length_cons, List.length_nil]
    omega

def binderCode (n : ℕ) : List Bool := List.replicate n true ++ [false]

def parseBinders : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, suffix) ← parseBinders rest
      pure (n + 1, suffix)

@[simp] theorem parseBinders_code (n : ℕ) (suffix : List Bool) :
    parseBinders (binderCode n ++ suffix) = some (n, suffix) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := congrArg (fun r : Option (ℕ × List Bool) =>
      r.bind (fun x => some (x.1 + 1, x.2))) ih
    simpa [binderCode, List.replicate_succ, parseBinders] using h

structure Sentence where
  arity : ℕ
  formula : Formula arity
  deriving DecidableEq

def Sentence.Satisfiable (s : Sentence) : Prop :=
  ∃ ρ : Fin s.arity → ℝ, s.formula.eval ρ

def Sentence.code (s : Sentence) : List Bool :=
  binderCode s.arity ++ s.formula.code

def decodeSentence (input : List Bool) : Option Sentence := do
  let (n, rest) ← parseBinders input
  let (p, suffix) ← parseFormula n rest.length rest
  if suffix = [] then pure ⟨n, p⟩ else none

theorem decodeSentence_code_append (s : Sentence) (suffix : List Bool) :
    decodeSentence (s.code ++ suffix) = if suffix = [] then some s else none := by
  rcases s with ⟨n, p⟩
  have hf : p.depth ≤ (p.code ++ suffix).length := by
    have h := p.depth_le_code_length
    simp only [List.length_append]
    omega
  have hp := parseFormula_code p (p.code ++ suffix).length suffix hf
  simp only [List.length_append] at hp
  simp [Sentence.code, decodeSentence, List.append_assoc, hp]

@[simp] theorem decodeSentence_code (s : Sentence) :
    decodeSentence s.code = some s := by
  simpa using decodeSentence_code_append s []

theorem decodeSentence_trailing_data (s : Sentence) {suffix : List Bool}
    (h : suffix ≠ []) : decodeSentence (s.code ++ suffix) = none := by
  simp [decodeSentence_code_append, h]

def ETR : Set (List Bool) :=
  {input | ∃ s, decodeSentence input = some s ∧ s.Satisfiable}

theorem code_mem_ETR_iff (s : Sentence) : s.code ∈ ETR ↔ s.Satisfiable := by
  simp [ETR]

theorem Sentence.code_injective : Function.Injective Sentence.code := by
  intro s t h
  have hd := congrArg decodeSentence h
  simpa only [decodeSentence_code, Option.some.injEq] using hd

theorem variables_le_code_length (s : Sentence) : s.arity ≤ s.code.length := by
  simp only [Sentence.code, binderCode, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

theorem malformed_not_mem_ETR {input : List Bool} (h : decodeSentence input = none) :
    input ∉ ETR := by
  simp [ETR, h]

end JointThermoComplexity.Complexity.RealSyntax

#print axioms JointThermoComplexity.Complexity.RealSyntax.parseTerm_code
#print axioms JointThermoComplexity.Complexity.RealSyntax.parseFormula_code
#print axioms JointThermoComplexity.Complexity.RealSyntax.decodeSentence_code
#print axioms JointThermoComplexity.Complexity.RealSyntax.decodeSentence_trailing_data
#print axioms JointThermoComplexity.Complexity.RealSyntax.code_mem_ETR_iff
