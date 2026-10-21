module
public import proofs.JointThermoComplexity.Complexity.SmallIntegerLookup
public import proofs.JointThermoComplexity.Complexity.NumericCursor

set_option autoImplicit false
@[expose] public section

/-! Finite magnitude control classifies five literals while consuming the complete raw numeric field. -/

namespace JointThermoComplexity.Complexity.SmallCoefficientControl

inductive Magnitude where
  | empty | one | zero | two | bad
  deriving DecidableEq

instance : Fintype Magnitude where
  elems := {.empty, .one, .zero, .two, .bad}
  complete m := by cases m <;> simp

def push : Magnitude → Bool → Magnitude
  | .empty, true => .one
  | .empty, false => .zero
  | .zero, true => .two
  | _, _ => .bad

def value (negative : Bool) : Magnitude → ℤ
  | .one => if negative then -1 else 1
  | .two => if negative then -2 else 2
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

def lookup (negative : Bool) : Magnitude → List Bool → ℤ
  | .one, false :: _ => if negative then -1 else 1
  | .two, false :: _ => if negative then -2 else 2
  | .zero, true :: true :: false :: _ => if negative then -2 else 2
  | .empty, true :: true :: false :: _ => if negative then -1 else 1
  | .empty, true :: false :: true :: true :: false :: _ => if negative then -2 else 2
  | _, _ => 0

theorem scan_value (negative : Bool) (input : List Bool) (m : Magnitude) :
    value negative (scan m input).magnitude = lookup negative m input := by
  induction input using BitCodec.parseBits.induct generalizing m with
  | case1 => cases m <;> rfl
  | case2 rest => cases m <;> rfl
  | case3 => cases m <;> rfl
  | case4 bit rest ih =>
    change value negative (scan (push m bit) rest).magnitude = _
    rw [ih]
    cases m <;> cases bit <;> first
      | rfl
      | cases rest with
        | nil => rfl
        | cons a rest =>
          cases rest with
          | nil => cases a <;> rfl
          | cons b rest =>
            cases rest with
            | nil => cases a <;> cases b <;> rfl
            | cons c rest => cases a <;> cases b <;> cases c <;> rfl

theorem lookup_signed (negative : Bool) (input : List Bool) : lookup negative .empty input = SmallIntegerLookup.value (negative :: input) := by
  cases input with
  | nil => cases negative <;> rfl
  | cons a input =>
    cases input with
    | nil => cases negative <;> cases a <;> rfl
    | cons b input =>
      cases input with
      | nil => cases negative <;> cases a <;> cases b <;> rfl
      | cons c input =>
        cases input with
        | nil => cases negative <;> cases a <;> cases b <;> cases c <;> rfl
        | cons d input =>
          cases input with
          | nil => cases negative <;> cases a <;> cases b <;> cases c <;> cases d <;> rfl
          | cons e input => cases negative <;> cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

def signed (input : List Bool) : Bool × Scan := match input with
  | [] => (false, ⟨[], [], .bad⟩)
  | negative :: rest =>
    let next := scan .empty rest
    (negative, ⟨negative :: next.taken, next.rest, next.magnitude⟩)

def signedValue (input : List Bool) : ℤ := value (signed input).1 (signed input).2.magnitude
def coefficient (negate : Bool) (negative : Bool) (m : Magnitude) : ℤ :=
  if negate then -(value negative m) else value negative m
def word (negate negative : Bool) (m : Magnitude) : List Bool := BitCodec.integerCode (coefficient negate negative m)

theorem signed_value_eq (input : List Bool) : signedValue input = SmallIntegerLookup.value input := by
  cases input with
  | nil => rfl
  | cons negative rest => exact (scan_value negative rest .empty).trans (lookup_signed negative rest)

theorem word_bound (negate negative : Bool) (m : Magnitude) : (word negate negative m).length ≤ 6 := by
  cases negate <;> cases negative <;> cases m <;> decide

end JointThermoComplexity.Complexity.SmallCoefficientControl

#print axioms JointThermoComplexity.Complexity.SmallCoefficientControl.scan_value
#print axioms JointThermoComplexity.Complexity.SmallCoefficientControl.signed_value_eq
#print axioms JointThermoComplexity.Complexity.SmallCoefficientControl.word_bound
