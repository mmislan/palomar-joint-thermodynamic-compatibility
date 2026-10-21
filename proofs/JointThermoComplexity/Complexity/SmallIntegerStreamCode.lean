module
public import proofs.JointThermoComplexity.Complexity.SmallLiteralStreamRun

set_option autoImplicit false
@[expose] public section

/-! A total raw signed-literal extension agrees exactly with the typed small-integer construction. -/

namespace JointThermoComplexity.Complexity.SmallIntegerStream
open RealSyntax BitCodec

def signPrefix (negative : Bool) : List Bool := if negative then [true, false, false] else []
def taken (input : List Bool) : List Bool := BooleanMachine.copied input ++ (SmallLiteralStream.scan (BooleanMachine.suffix input)).taken
def rest (input : List Bool) : List Bool := (SmallLiteralStream.scan (BooleanMachine.suffix input)).rest
def output (input : List Bool) : List Bool := signPrefix (SourceBitRead.value input) ++
  SmallLiteralStream.output (SmallLiteralStream.scan (BooleanMachine.suffix input)).bits

theorem split (input : List Bool) : taken input ++ rest input = input := by
  rw [taken, rest, List.append_assoc, SmallLiteralStream.scan_split]
  cases input <;> rfl

theorem suffix_bound (input : List Bool) : (BooleanMachine.suffix input).length ≤ input.length := by
  cases input <;> simp [BooleanMachine.suffix]

theorem code_result (n : ℕ) (z : ℤ) (suffix : List Bool) :
    taken (integerCode z ++ suffix) = integerCode z ∧ rest (integerCode z ++ suffix) = suffix ∧
      output (integerCode z ++ suffix) = (SourceSmallLiterals.integerTerm z : Term n).code := by
  cases z with
  | ofNat k =>
    have hn : ¬Int.ofNat k < 0 := by
      change ¬(k : ℤ) < 0
      omega
    simp only [taken, rest, output, integerCode, naturalCode, List.cons_append, BooleanMachine.copied,
      BooleanMachine.suffix, SourceBitRead.value, SmallLiteralStream.scan_encoded, signPrefix,
      Bool.false_eq_true, ↓reduceIte, List.nil_append, SourceSmallLiterals.integerTerm, hn, Int.natAbs_ofNat',
      SmallLiteralStream.fromBits_code]
    exact ⟨trivial, trivial, trivial⟩
  | negSucc k =>
    have hn : Int.negSucc k < 0 := by omega
    simp only [taken, rest, output, integerCode, naturalCode, List.cons_append, BooleanMachine.copied,
      BooleanMachine.suffix, SourceBitRead.value, SmallLiteralStream.scan_encoded, signPrefix,
      ↓reduceIte, List.nil_append, SourceSmallLiterals.integerTerm, hn, Int.natAbs_negSucc, Term.code, SmallLiteralStream.fromBits_code]
    exact ⟨trivial, trivial, trivial⟩

end JointThermoComplexity.Complexity.SmallIntegerStream

#print axioms JointThermoComplexity.Complexity.SmallIntegerStream.code_result
