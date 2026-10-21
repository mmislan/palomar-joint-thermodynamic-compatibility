module
public import proofs.JointThermoComplexity.Complexity.SparseIntegerPolynomial

set_option autoImplicit false
@[expose] public section

/-! Executable ordered expansion of raw integer polynomial lists. Empty
monomials, zero terms and repeated monomials retain their list semantics. -/

namespace JointThermoComplexity.Complexity.SparseSubstitution
open SparseInteger
variable {V W : Type}

def expand (f : V → Poly W) : List V → Poly W
  | [] => constant 1
  | v :: vs => product (f v) (expand f vs)

def substitute (f : V → Poly W) : Poly V → Poly W
  | [] => []
  | a :: p => scale a.1 (expand f a.2) ++ substitute f p

def cubeVariable (v : V) : Poly V := [(2, [v]), (-3, [])]
def orthantVariable (v : V) : Poly (V ⊕ V) := [(1, [Sum.inl v]), (-1, [Sum.inr v])]

def cubeTerm (d : ℕ) (a : ℤ × List V) : Poly V :=
  scale (a.1 * (2 : ℤ) ^ (d - a.2.length)) (expand cubeVariable a.2)

def cube (d : ℕ) : Poly V → Poly V
  | [] => []
  | a :: p => cubeTerm d a ++ cube d p

def orthant (p : Poly V) : Poly (V ⊕ V) := substitute orthantVariable p

@[simp] theorem expand_nil (f : V → Poly W) : expand f [] = constant 1 := rfl
@[simp] theorem expand_cons (f : V → Poly W) (v : V) (vs : List V) :
    expand f (v :: vs) = product (f v) (expand f vs) := rfl
@[simp] theorem substitute_nil (f : V → Poly W) : substitute f [] = [] := rfl
@[simp] theorem substitute_cons (f : V → Poly W) (a : ℤ × List V) (p : Poly V) :
    substitute f (a :: p) = scale a.1 (expand f a.2) ++ substitute f p := rfl
@[simp] theorem cube_nil (d : ℕ) : cube d ([] : Poly V) = [] := rfl
@[simp] theorem cube_cons (d : ℕ) (a : ℤ × List V) (p : Poly V) :
    cube d (a :: p) = cubeTerm d a ++ cube d p := rfl

end JointThermoComplexity.Complexity.SparseSubstitution

#print axioms JointThermoComplexity.Complexity.SparseSubstitution.expand
#print axioms JointThermoComplexity.Complexity.SparseSubstitution.substitute
#print axioms JointThermoComplexity.Complexity.SparseSubstitution.cube
