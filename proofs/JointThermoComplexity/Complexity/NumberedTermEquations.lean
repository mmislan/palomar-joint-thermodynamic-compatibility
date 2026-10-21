module
public import proofs.JointThermoComplexity.Complexity.NumericSparseSource

set_option autoImplicit false
@[expose] public section

/-! Explicit preorder coordinate addresses, with the original postorder equation lists preserved exactly. -/

namespace JointThermoComplexity.Complexity.NumberedTermEquations
open RealSyntax QuadraticCircuit SparseInteger SourceCoordinateEnumeration
variable {n : ℕ} {V W U : Type}

theorem relabel_comp (f : V → W) (g : W → U) (p : Poly V) :
    relabel g (relabel f p) = relabel (g ∘ f) p := by
  simp [relabel, List.map_map, Function.comp_def]

theorem map_relabel_comp (f : V → W) (g : W → U) (ps : List (Poly V)) :
    (ps.map (relabel f)).map (relabel g) = ps.map (relabel (g ∘ f)) := by
  simp only [List.map_map, Function.comp_def, relabel_comp]

theorem relabel_constant (f : V → W) (z : ℤ) : relabel f (constant z) = constant z := rfl
theorem relabel_atom (f : V → W) (v : V) : relabel f (atom v) = atom (f v) := rfl
theorem relabel_add (f : V → W) (p q : Poly V) : relabel f (add p q) = add (relabel f p) (relabel f q) :=
  List.map_append
theorem relabel_scale (f : V → W) (z : ℤ) (p : Poly V) : relabel f (scale z p) = scale z (relabel f p) := by
  simp [relabel, scale, List.map_map, Function.comp_def]
theorem relabel_sub (f : V → W) (p q : Poly V) : relabel f (sub p q) = sub (relabel f p) (relabel f q) := by
  simp only [sub, neg, relabel_add, relabel_scale]
theorem relabel_product (f : V → W) (p q : Poly V) :
    relabel f (product p q) = product (relabel f p) (relabel f q) := by
  simp [relabel, product, List.map_flatMap, List.flatMap_map, List.map_map, List.map_append, Function.comp_def]
theorem relabel_square (f : V → W) (p : Poly V) : relabel f (square p) = square (relabel f p) :=
  relabel_product f p p

def slot : (t : Term n) → TermSlot t → ℕ
  | .int _, _ | .var _, _ => 0
  | .add _ _, .inl _ | .mul _ _, .inl _ => 0
  | .add s _, .inr (.inl a) | .mul s _, .inr (.inl a) => 1 + slot s a
  | .add s t, .inr (.inr a) | .mul s t, .inr (.inr a) => 1 + s.size + slot t a
  | .neg _, .inl _ => 0
  | .neg s, .inr a => 1 + slot s a

theorem slot_eq_enumeration (t : Term n) (a : TermSlot t) : slot t a = (termEnumeration t a).val := by
  induction t with
  | int z | var z => rfl
  | add s t hs ht | mul s t hs ht =>
    rcases a with u | a | a
    · cases u; rfl
    · simpa [slot, termEnumeration, sumEnumeration] using hs a
    · simpa [slot, termEnumeration, sumEnumeration, Nat.add_assoc] using congrArg (fun k => 1 + s.size + k) (ht a)
  | neg s hs =>
    rcases a with u | a
    · cases u; rfl
    · change 1 + slot s a = 1 + (termEnumeration s a).val
      exact congrArg (fun k => 1 + k) (hs a)

@[simp] theorem root_slot (t : Term n) : slot t (termRoot t) = 0 := by cases t <;> rfl

def address (t : Term n) (inputs : Fin n → ℕ) (offset : ℕ) : Fin n ⊕ TermSlot t → ℕ :=
  Sum.elim inputs (fun a => offset + slot t a)

theorem binary_left_address (s t : Term n) (inputs : Fin n → ℕ) (offset : ℕ) :
    address (.add s t) inputs offset ∘ binaryLeft s t = address s inputs (offset + 1) := by
  funext a
  cases a <;> simp [address, binaryLeft, slot, Nat.add_assoc]

theorem binary_right_address (s t : Term n) (inputs : Fin n → ℕ) (offset : ℕ) :
    address (.add s t) inputs offset ∘ binaryRight s t = address t inputs (offset + 1 + s.size) := by
  funext a
  cases a <;> simp [address, binaryRight, slot, Nat.add_assoc]

theorem unary_address (s : Term n) (inputs : Fin n → ℕ) (offset : ℕ) :
    address (.neg s) inputs offset ∘ unaryChild s = address s inputs (offset + 1) := by
  funext a
  cases a <;> simp [address, unaryChild, slot, Nat.add_assoc]

def equations : (t : Term n) → (Fin n → ℕ) → ℕ → List (Poly ℕ)
  | .int z, _, offset => [sub (atom offset) (constant z)]
  | .var v, inputs, offset => [sub (atom offset) (atom (inputs v))]
  | .add s t, inputs, offset => equations s inputs (offset + 1) ++ equations t inputs (offset + 1 + s.size) ++
      [sub (atom offset) (add (atom (offset + 1)) (atom (offset + 1 + s.size)))]
  | .mul s t, inputs, offset => equations s inputs (offset + 1) ++ equations t inputs (offset + 1 + s.size) ++
      [sub (atom offset) (product (atom (offset + 1)) (atom (offset + 1 + s.size)))]
  | .neg s, inputs, offset => equations s inputs (offset + 1) ++ [add (atom offset) (atom (offset + 1))]

theorem equations_agree (t : Term n) (inputs : Fin n → ℕ) (offset : ℕ) :
    (SparseCircuit.termEquations t).map (relabel (address t inputs offset)) = equations t inputs offset := by
  induction t generalizing offset with
  | int z | var z => simp [SparseCircuit.termEquations, equations, relabel_sub, relabel_atom, relabel_constant, address, slot]
  | add s t hs ht =>
    have hl := binary_left_address s t inputs offset
    have hr := binary_right_address s t inputs offset
    simp only [SparseCircuit.termEquations, equations, List.map_append, map_relabel_comp]
    rw [hl, hr, hs, ht]
    simp only [List.map_cons, List.map_nil, relabel_sub, relabel_add,
      relabel_atom, address, Sum.elim_inr, slot, root_slot, Nat.add_zero, Nat.add_assoc]
  | mul s t hs ht =>
    have hl : address (.mul s t) inputs offset ∘ binaryLeft s t = address s inputs (offset + 1) :=
      by funext a; cases a <;> simp [address, binaryLeft, slot, Nat.add_assoc]
    have hr : address (.mul s t) inputs offset ∘ binaryRight s t = address t inputs (offset + 1 + s.size) :=
      by funext a; cases a <;> simp [address, binaryRight, slot, Nat.add_assoc]
    simp only [SparseCircuit.termEquations, equations, List.map_append, map_relabel_comp]
    rw [hl, hr, hs, ht]
    simp only [List.map_cons, List.map_nil, relabel_sub, relabel_product,
      relabel_atom, address, Sum.elim_inr, slot, root_slot, Nat.add_zero, Nat.add_assoc]
  | neg s hs =>
    simp only [SparseCircuit.termEquations, equations, List.map_append, map_relabel_comp]
    rw [unary_address, hs]
    simp only [List.map_cons, List.map_nil, relabel_add,
      relabel_atom, address, Sum.elim_inr, slot, root_slot, Nat.add_zero]

theorem equation_count (t : Term n) (inputs : Fin n → ℕ) (offset : ℕ) :
    (equations t inputs offset).length = t.size := by
  rw [← equations_agree, List.length_map]
  exact SparseCircuit.term_equation_count t

end JointThermoComplexity.Complexity.NumberedTermEquations

#print axioms JointThermoComplexity.Complexity.NumberedTermEquations.slot_eq_enumeration
#print axioms JointThermoComplexity.Complexity.NumberedTermEquations.equations_agree
