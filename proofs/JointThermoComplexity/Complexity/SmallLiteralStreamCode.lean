module
public import proofs.JointThermoComplexity.Complexity.SourceSmallLiteralTerm
public import proofs.JointThermoComplexity.Complexity.SourceNormalizationFP

set_option autoImplicit false
@[expose] public section

/-! Exact constant-code fragments for streaming binary literals, with a total raw payload extension. -/

namespace JointThermoComplexity.Complexity.SmallLiteralStream
open RealSyntax BitCodec

def chunk (b : Bool) : List Bool :=
  [false, true, false] ++ (Term.int (if b then 1 else 0) : Term 0).code ++
    [false, true, true] ++ (Term.int 2 : Term 0).code

def base : List Bool := (Term.int 0 : Term 0).code
def output (bits : List Bool) : List Bool := bits.flatMap chunk ++ base

theorem chunk_length (b : Bool) : (chunk b).length = if b then 22 else 20 := by cases b <;> rfl
theorem chunk_bound (b : Bool) : 0 < (chunk b).length ∧ (chunk b).length ≤ 22 := by cases b <;> decide
theorem base_length : base.length = 5 := rfl

@[simp] theorem output_nil : output [] = base := rfl
@[simp] theorem output_cons (b : Bool) (bits : List Bool) : output (b :: bits) = chunk b ++ output bits := by
  simp only [output, List.flatMap_cons, List.append_assoc]

theorem fromBits_code (n : ℕ) (bits : List Bool) : (SourceSmallLiterals.fromBits bits : Term n).code = output bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [SourceSmallLiterals.fromBits, Term.code, ih, output_cons, chunk, List.append_assoc]

theorem output_length (bits : List Bool) : (output bits).length ≤ 22 * bits.length + 5 := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    have hb := (chunk_bound b).2
    rw [output_cons, List.length_append, List.length_cons]
    omega

structure Scan where
  bits : List Bool
  taken : List Bool
  rest : List Bool
  deriving DecidableEq

def scan : List Bool → Scan
  | [] => ⟨[], [], []⟩
  | false :: rest => ⟨[], [false], rest⟩
  | [true] => ⟨[], [true], []⟩
  | true :: b :: rest =>
      let next := scan rest
      ⟨b :: next.bits, true :: b :: next.taken, next.rest⟩

theorem scan_split (input : List Bool) : (scan input).taken ++ (scan input).rest = input := by
  induction input using parseBits.induct with
  | case1 => rfl
  | case2 rest => rfl
  | case3 => rfl
  | case4 b rest ih => simpa only [scan, List.cons_append] using congrArg (fun xs => true :: b :: xs) ih

theorem scan_payload_bound (input : List Bool) : (scan input).bits.length * 2 ≤ (scan input).taken.length := by
  induction input using parseBits.induct with
  | case1 => rfl
  | case2 rest => simp [scan]
  | case3 => simp [scan]
  | case4 b rest ih => simp only [scan, List.length_cons]; omega

theorem scan_bounds (input : List Bool) : (scan input).bits.length * 2 ≤ (scan input).taken.length ∧
    (scan input).taken.length ≤ input.length := by
  have hlen := congrArg List.length (scan_split input)
  rw [List.length_append] at hlen
  exact ⟨scan_payload_bound input, by omega⟩

theorem scan_encoded (bits suffix : List Bool) : scan (encodeBits bits ++ suffix) = ⟨bits, encodeBits bits, suffix⟩ := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp only [encodeBits, List.cons_append, scan, ih]

end JointThermoComplexity.Complexity.SmallLiteralStream

#print axioms JointThermoComplexity.Complexity.SmallLiteralStream.fromBits_code
#print axioms JointThermoComplexity.Complexity.SmallLiteralStream.scan_encoded
