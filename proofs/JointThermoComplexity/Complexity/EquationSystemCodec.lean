module
public import proofs.JointThermoComplexity.Complexity.SparsePolynomialCodec

set_option autoImplicit false
@[expose] public section

/-! A faithful finite equation-list format: unary arity, binary signed coefficients and finite IDs. -/

namespace JointThermoComplexity.Complexity.EquationSystemCodec
open SparseInteger FiniteCodec

structure Data where
  arity : ℕ
  rows : List (Poly (Fin arity))

def rowsCodec (n : ℕ) : Codec (List (Poly (Fin n))) :=
  SparseListCodec.list (SparsePolynomialCodec.polynomial n)

def code (p : Data) : List Bool :=
  SparseListCodec.unaryCode p.arity ++ (rowsCodec p.arity).code p.rows

def parse (input : List Bool) : Option (Data × List Bool) := do
  let (n, rest) ← SparseListCodec.parseUnary input
  let (ps, suffix) ← (rowsCodec n).parse rest
  pure (⟨n, ps⟩, suffix)

theorem parse_code (p : Data) (suffix : List Bool) : parse (code p ++ suffix) = some (p, suffix) := by
  cases p with
  | mk n ps => simp [code, parse, List.append_assoc, SparseListCodec.parseUnary_code, (rowsCodec n).roundtrip]

theorem parse_sound {input suffix : List Bool} {p : Data}
    (h : parse input = some (p, suffix)) : input = code p ++ suffix := by
  cases hn : SparseListCodec.parseUnary input with
  | none => simp [parse, hn] at h
  | some pair =>
    obtain ⟨n, rest⟩ := pair
    cases hp : (rowsCodec n).parse rest with
    | none => simp [parse, hn, hp] at h
    | some pair =>
      obtain ⟨ps, tail⟩ := pair
      simp [parse, hn, hp] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [SparseListCodec.parseUnary_sound hn, (rowsCodec n).sound hp]
      simp only [code, List.append_assoc]

def codec : Codec Data := ⟨code, parse, parse_code, parse_sound⟩

def decode (input : List Bool) : Option Data :=
  match parse input with
  | some (p, []) => some p
  | _ => none

theorem decode_code (p : Data) : decode (code p) = some p := by
  have h := parse_code p []
  simp only [List.append_nil] at h
  simp only [decode, h]

theorem decode_sound {input : List Bool} {p : Data} (h : decode input = some p) : input = code p := by
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

end JointThermoComplexity.Complexity.EquationSystemCodec

#print axioms JointThermoComplexity.Complexity.EquationSystemCodec.parse_sound
#print axioms JointThermoComplexity.Complexity.EquationSystemCodec.decode_code
#print axioms JointThermoComplexity.Complexity.EquationSystemCodec.decode_sound
#print axioms JointThermoComplexity.Complexity.EquationSystemCodec.code_injective
