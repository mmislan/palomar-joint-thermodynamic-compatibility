module
public import proofs.JointThermoComplexity.Complexity.BinaryTrim
public import proofs.JointThermoComplexity.Complexity.BinaryScaleControl

set_option autoImplicit false
@[expose] public section

/-! Total ripple-carry addition on two finite little-endian words. Numeric
values affect bits, never the number of loop iterations. -/

namespace JointThermoComplexity.Complexity.BinaryAddControl
open BitCodec

def val (b : Bool) : ℕ := if b then 1 else 0
def digit (carry a b : Bool) : Bool := Bool.xor (Bool.xor carry a) b
def next (carry a b : Bool) : Bool := (a && b) || (carry && (a || b))

def add : Bool → List Bool → List Bool → List Bool
  | false, [], [] => []
  | true, [], [] => [true]
  | carry, [], b :: right => digit carry false b :: add (next carry false b) [] right
  | carry, a :: left, [] => digit carry a false :: add (next carry a false) left []
  | carry, a :: left, b :: right => digit carry a b :: add (next carry a b) left right
termination_by _ left right => left.length + right.length
decreasing_by
  all_goals simp_wf
  omega

theorem step_value (carry a b : Bool) (x y : ℕ) :
    Nat.bit (digit carry a b) (val (next carry a b) + x + y) =
      val carry + Nat.bit a x + Nat.bit b y := by
  cases carry <;> cases a <;> cases b <;> simp [digit, next, val, Nat.bit] <;> omega

theorem read_add (carry : Bool) (left right : List Bool) :
    readBits (add carry left right) = val carry + readBits left + readBits right := by
  induction carry, left, right using add.induct with
  | case1 => simp [add, readBits, val]
  | case2 => simp [add, readBits, val]
  | case3 carry b right ih =>
    rw [add]
    change Nat.bit (digit carry false b) (readBits (add (next carry false b) [] right)) =
      val carry + 0 + Nat.bit b (readBits right)
    rw [ih]
    exact step_value carry false b 0 (readBits right)
  | case4 carry a left ih =>
    rw [add]
    change Nat.bit (digit carry a false) (readBits (add (next carry a false) left [])) =
      val carry + Nat.bit a (readBits left) + 0
    rw [ih]
    exact step_value carry a false (readBits left) 0
  | case5 carry a left b right ih =>
    rw [add]
    change Nat.bit (digit carry a b) (readBits (add (next carry a b) left right)) =
      val carry + Nat.bit a (readBits left) + Nat.bit b (readBits right)
    rw [ih]
    exact step_value carry a b (readBits left) (readBits right)

theorem length_add (carry : Bool) (left right : List Bool) :
    (add carry left right).length ≤ left.length + right.length + 1 := by
  induction carry, left, right using add.induct with
  | case1 => simp [add]
  | case2 => simp [add]
  | case3 carry b right ih =>
    simp only [add, List.length_cons, List.length_nil] at ih ⊢
    omega
  | case4 carry a left ih =>
    simp only [add, List.length_cons, List.length_nil] at ih ⊢
    omega
  | case5 carry a left b right ih =>
    simp only [add, List.length_cons]
    omega

theorem canonical_sum (m n : ℕ) : BinaryTrim.trim (add false m.bits n.bits) = (m + n).bits := by
  rw [BinaryTrim.canonical, read_add, readBits_bits, readBits_bits]
  simp [val]

end JointThermoComplexity.Complexity.BinaryAddControl

#print axioms JointThermoComplexity.Complexity.BinaryAddControl.read_add
#print axioms JointThermoComplexity.Complexity.BinaryAddControl.length_add
#print axioms JointThermoComplexity.Complexity.BinaryAddControl.canonical_sum
