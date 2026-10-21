module
public import proofs.JointThermoComplexity.Complexity.SourceTermPair

set_option autoImplicit false
@[expose] public section

/-! Formula head tokens use the independently defined source terms and formula tags. -/

namespace JointThermoComplexity.Complexity.SourceFormulaScan
open RealSyntax
variable {n : ℕ}

inductive Kind where
  | truth | falsity | eq | lt | conj | disj | invalid
  deriving DecidableEq

def classify : List Bool → Kind
  | [false, false, false] => .truth
  | [false, false, true] => .falsity
  | [false, true, false] => .eq
  | [false, true, true] => .lt
  | [true, false, false] => .conj
  | [true, false, true] => .disj
  | _ => .invalid

def Kind.children : Kind → ℕ
  | .conj | .disj => 2
  | _ => 0

inductive Head (n : ℕ) where
  | truth | falsity : Head n
  | eq : Term n → Term n → Head n
  | lt : Term n → Term n → Head n
  | conj | disj : Head n
  deriving DecidableEq

def Head.kind : Head n → Kind
  | .truth => .truth
  | .falsity => .falsity
  | .eq _ _ => .eq
  | .lt _ _ => .lt
  | .conj => .conj
  | .disj => .disj

def Head.children (h : Head n) : ℕ := h.kind.children

def Head.code : Head n → List Bool
  | .truth => [false, false, false]
  | .falsity => [false, false, true]
  | .eq a b => [false, true, false] ++ a.code ++ b.code
  | .lt a b => [false, true, true] ++ a.code ++ b.code
  | .conj => [true, false, false]
  | .disj => [true, false, true]

theorem head_min_length (h : Head n) : 3 ≤ h.code.length := by
  cases h <;> simp only [Head.code, List.length_append, List.length_cons, List.length_nil] <;> omega

theorem children_bound (bits : List Bool) : (classify bits).children ≤ 2 := by
  cases classify bits <;> simp [Kind.children]

theorem classify_head (h : Head n) (suffix : List Bool) :
    classify (SourceTermToken.tagBits (h.code ++ suffix)) = h.kind := by
  cases h <;> simp [Head.code, Head.kind, classify, SourceTermToken.tagBits, SourceBitRead.value]

end JointThermoComplexity.Complexity.SourceFormulaScan

#print axioms JointThermoComplexity.Complexity.SourceFormulaScan.head_min_length
#print axioms JointThermoComplexity.Complexity.SourceFormulaScan.classify_head
