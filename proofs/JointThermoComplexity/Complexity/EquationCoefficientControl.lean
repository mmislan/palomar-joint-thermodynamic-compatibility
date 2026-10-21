module
public import proofs.JointThermoComplexity.Complexity.SmallCoefficientCursor
public import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
@[expose] public section

/-! Finite signed coefficient control for all eleven integers from minus five
through five. Oversized/noncanonical payloads default to zero while the full
structural field is consumed. No numeric-value counter is constructed.
-/

namespace JointThermoComplexity.Complexity.EquationCoefficientControl

inductive Magnitude where
  | empty | one | zero | zeroZero | oneZero | two | three | four | five | bad
  deriving DecidableEq

instance : Fintype Magnitude where
  elems := {.empty, .one, .zero, .zeroZero, .oneZero, .two, .three, .four, .five, .bad}
  complete m := by cases m <;> simp

def push : Magnitude → Bool → Magnitude
  | .empty, false => .zero
  | .empty, true => .one
  | .zero, false => .zeroZero
  | .zero, true => .two
  | .one, false => .oneZero
  | .one, true => .three
  | .zeroZero, true => .four
  | .oneZero, true => .five
  | _, _ => .bad

def value (negative : Bool) : Magnitude → ℤ
  | .one => if negative then -1 else 1
  | .two => if negative then -2 else 2
  | .three => if negative then -3 else 3
  | .four => if negative then -4 else 4
  | .five => if negative then -5 else 5
  | _ => 0

structure Scan where
  taken : List Bool
  rest : List Bool
  magnitude : Magnitude

def scan : Magnitude → List Bool → Scan
  | _, [] => ⟨[], [], .bad⟩
  | m, false :: rest => ⟨[false], rest, m⟩
  | _, [true] => ⟨[true], [], .bad⟩
  | m, true :: bit :: rest =>
    let next := scan (push m bit) rest
    ⟨true :: bit :: next.taken, next.rest, next.magnitude⟩

def signed (input : List Bool) : Bool × Scan := match input with
  | [] => (false, ⟨[], [], .bad⟩)
  | negative :: rest =>
    let next := scan .empty rest
    (negative, ⟨negative :: next.taken, next.rest, next.magnitude⟩)

def signedValue (input : List Bool) : ℤ := value (signed input).1 (signed input).2.magnitude
def coefficient (negate negative : Bool) (m : Magnitude) : ℤ := if negate then -(value negative m) else value negative m
def word (negate negative : Bool) (m : Magnitude) : List Bool := BitCodec.integerCode (coefficient negate negative m)

theorem value_bound (negative : Bool) (m : Magnitude) : (value negative m).natAbs ≤ 5 := by
  cases negative <;> cases m <;> decide

theorem signedValue_bound (input : List Bool) : (signedValue input).natAbs ≤ 5 :=
  value_bound _ _

theorem signed_value_code (z : ℤ) (hz : z.natAbs ≤ 5) (suffix : List Bool) :
    signedValue (BitCodec.integerCode z ++ suffix) = z := by
  cases z with
  | ofNat k =>
    have hk : k ≤ 5 := by simpa only [Int.natAbs_ofNat'] using hz
    interval_cases k <;> rfl
  | negSucc k =>
    have hk : k ≤ 4 := by change k + 1 ≤ 5 at hz; omega
    interval_cases k <;> rfl

theorem word_bound (negate negative : Bool) (m : Magnitude) : (word negate negative m).length ≤ 8 := by
  cases negate <;> cases negative <;> cases m <;> decide

theorem scan_taken (input : List Bool) (m : Magnitude) :
    (scan m input).taken = PayloadControl.copied .empty input := by
  induction input using BitCodec.parseBits.induct generalizing m with
  | case1 => rfl
  | case2 rest => rfl
  | case3 => rfl
  | case4 b rest ih =>
    change true :: b :: (scan (push m b) rest).taken =
      true :: b :: PayloadControl.copied (PayloadControl.flag [b]) rest
    rw [ih, SmallCoefficientCursor.copied_marker (PayloadControl.flag [b]) (by cases b <;> decide)]

theorem scan_rest (input : List Bool) (m : Magnitude) :
    (scan m input).rest = NumericCursor.naturalRest input := by
  induction input using BitCodec.parseBits.induct generalizing m with
  | case1 => rfl
  | case2 rest => rfl
  | case3 => rfl
  | case4 b rest ih =>
    change (scan (push m b) rest).rest = NumericCursor.payloadRest (PayloadControl.flag [b]) rest
    rw [ih, SmallCoefficientCursor.rest_marker (PayloadControl.flag [b]) (by cases b <;> decide)]

theorem signed_taken (input : List Bool) : (signed input).2.taken = IntegerMachineRun.copied input := by
  cases input with
  | nil => rfl
  | cons b rest => simpa only [signed, IntegerMachineRun.copied] using congrArg (List.cons b) (scan_taken rest .empty)

theorem signed_rest (input : List Bool) : (signed input).2.rest = NumericCursor.integerRest input := by
  cases input with
  | nil => rfl
  | cons b rest => exact scan_rest rest .empty

theorem signed_split (input : List Bool) : (signed input).2.taken ++ (signed input).2.rest = input := by
  rw [signed_taken, signed_rest]
  exact NumericCursor.integer_split input

theorem signed_word (negate : Bool) (input : List Bool) :
    word negate (signed input).1 (signed input).2.magnitude =
      BitCodec.integerCode (if negate then -(signedValue input) else signedValue input) := by
  simp only [word, coefficient, signedValue]

theorem encoded (negate : Bool) (z : ℤ) (hz : z.natAbs ≤ 5) (suffix : List Bool) :
    (signed (BitCodec.integerCode z ++ suffix)).2.taken = BitCodec.integerCode z ∧
    (signed (BitCodec.integerCode z ++ suffix)).2.rest = suffix ∧
    word negate (signed (BitCodec.integerCode z ++ suffix)).1
      (signed (BitCodec.integerCode z ++ suffix)).2.magnitude = BitCodec.integerCode (if negate then -z else z) := by
  rw [signed_taken, signed_rest, NumericCursor.integer_copied_code, NumericCursor.integer_rest_code,
    signed_word, signed_value_code z hz]
  exact ⟨rfl, rfl, rfl⟩

end JointThermoComplexity.Complexity.EquationCoefficientControl

#print axioms JointThermoComplexity.Complexity.EquationCoefficientControl.signed_value_code
#print axioms JointThermoComplexity.Complexity.EquationCoefficientControl.word_bound
#print axioms JointThermoComplexity.Complexity.EquationCoefficientControl.signed_split
#print axioms JointThermoComplexity.Complexity.EquationCoefficientControl.encoded
