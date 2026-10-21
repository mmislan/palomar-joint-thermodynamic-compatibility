module
public import proofs.JointThermoComplexity.Complexity.BitCodec
public import Mathlib.Algebra.Ring.Nat

set_option autoImplicit false
@[expose] public section

/-! # Executable integer polynomial lists

A monomial lists its variable occurrences, so repeated variables represent
powers. Lists may contain repeated monomials and zero coefficients. All data
operations here are executable and require no finite-support enumeration or
choice. Their algebraic interpretation is proved in SparseIntegerSemantics.
-/

namespace JointThermoComplexity.Complexity.SparseInteger
variable {V W : Type}

abbrev Poly (V : Type) := List (ℤ × List V)

def constant (c : ℤ) : Poly V := [(c, [])]
def atom (v : V) : Poly V := [(1, [v])]
def add (p q : Poly V) : Poly V := p ++ q
def scale (c : ℤ) (p : Poly V) : Poly V := p.map (fun t => (c * t.1, t.2))
def neg (p : Poly V) : Poly V := scale (-1) p
def sub (p q : Poly V) : Poly V := add p (neg q)
def product (p q : Poly V) : Poly V :=
  p.flatMap (fun a => q.map (fun b => (a.1 * b.1, a.2 ++ b.2)))
def square (p : Poly V) : Poly V := product p p
def relabel (f : V → W) (p : Poly V) : Poly W := p.map (fun t => (t.1, t.2.map f))

def DegreeLE (d : ℕ) (p : Poly V) : Prop := ∀ t ∈ p, t.2.length ≤ d

@[simp] theorem length_constant (c : ℤ) : (constant (V := V) c).length = 1 := rfl
@[simp] theorem length_atom (v : V) : (atom v).length = 1 := rfl
@[simp] theorem length_add (p q : Poly V) : (add p q).length = p.length + q.length := List.length_append
@[simp] theorem length_scale (c : ℤ) (p : Poly V) : (scale c p).length = p.length := List.length_map _
@[simp] theorem length_neg (p : Poly V) : (neg p).length = p.length := length_scale _ _
@[simp] theorem length_sub (p q : Poly V) : (sub p q).length = p.length + q.length := by
  simp only [sub, length_add, length_neg]
@[simp] theorem length_relabel (f : V → W) (p : Poly V) : (relabel f p).length = p.length := List.length_map _

theorem length_product (p q : Poly V) : (product p q).length = p.length * q.length := by
  induction p with
  | nil => simp [product]
  | cons a p ih =>
    change (q.map (fun b => (a.1 * b.1, a.2 ++ b.2)) ++ product p q).length = (p.length + 1) * q.length
    rw [List.length_append, List.length_map, ih, Nat.add_mul, one_mul]
    omega

theorem length_square (p : Poly V) : (square p).length = p.length ^ 2 := by
  simpa only [square, pow_two] using length_product p p

theorem degree_constant (c : ℤ) : DegreeLE 0 (constant (V := V) c) := by
  simp [DegreeLE, constant]

theorem degree_atom (v : V) : DegreeLE 1 (atom v) := by
  simp [DegreeLE, atom]

theorem degree_add {d : ℕ} {p q : Poly V} (hp : DegreeLE d p) (hq : DegreeLE d q) : DegreeLE d (add p q) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hp t ht
  · exact hq t ht

theorem degree_scale {d : ℕ} (c : ℤ) {p : Poly V} (hp : DegreeLE d p) : DegreeLE d (scale c p) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact hp u hu

theorem degree_neg {d : ℕ} {p : Poly V} (hp : DegreeLE d p) : DegreeLE d (neg p) := degree_scale _ hp

theorem degree_sub {d : ℕ} {p q : Poly V} (hp : DegreeLE d p) (hq : DegreeLE d q) : DegreeLE d (sub p q) :=
  degree_add hp (degree_neg hq)

theorem degree_relabel {d : ℕ} (f : V → W) {p : Poly V} (hp : DegreeLE d p) : DegreeLE d (relabel f p) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  simpa only [List.length_map] using hp u hu

theorem degree_product {a b : ℕ} {p q : Poly V} (hp : DegreeLE a p) (hq : DegreeLE b q) :
    DegreeLE (a + b) (product p q) := by
  intro t ht
  obtain ⟨u, hu, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
  change (u.2 ++ v.2).length ≤ a + b
  rw [List.length_append]
  exact Nat.add_le_add (hp u hu) (hq v hv)

theorem degree_square {d : ℕ} {p : Poly V} (hp : DegreeLE d p) : DegreeLE (d + d) (square p) :=
  degree_product hp hp

end JointThermoComplexity.Complexity.SparseInteger

#print axioms JointThermoComplexity.Complexity.SparseInteger.length_product
#print axioms JointThermoComplexity.Complexity.SparseInteger.degree_product
