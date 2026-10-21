module
public import proofs.JointThermoComplexity.Complexity.NumberedTermEquations
public import Mathlib.Tactic.FinCases

set_option autoImplicit false
@[expose] public section

/-! Explicit arithmetic addresses for activated formula equations, retaining all witness slots and list order. -/

namespace JointThermoComplexity.Complexity.NumberedFormulaEquations
open RealSyntax QuadraticCircuit SparseInteger SourceCoordinateEnumeration NumberedTermEquations
variable {n : ℕ}

def slot : (p : Formula n) → FormulaSlot p → ℕ
  | .truth, _ | .falsity, _ => 0
  | .eq _ _, .inl _ | .lt _ _, .inl _ => 0
  | .eq s _, .inr (.inl (.inl a)) | .lt s _, .inr (.inl (.inl a)) => 1 + NumberedTermEquations.slot s a
  | .eq s t, .inr (.inl (.inr a)) | .lt s t, .inr (.inl (.inr a)) => 1 + s.size + NumberedTermEquations.slot t a
  | .eq s t, .inr (.inr i) | .lt s t, .inr (.inr i) => 1 + s.size + t.size + i.val
  | .conj _ _, .inl _ | .disj _ _, .inl _ => 0
  | .conj p _, .inr (.inl a) | .disj p _, .inr (.inl a) => 1 + slot p a
  | .conj p q, .inr (.inr a) | .disj p q, .inr (.inr a) => 1 + formulaCount p + slot q a

theorem slot_eq_enumeration (p : Formula n) (a : FormulaSlot p) : slot p a = (formulaEnumeration p a).val := by
  induction p with
  | truth | falsity => rfl
  | eq s t | lt s t =>
    rcases a with u | (a | a) | i
    · cases u; rfl
    · change 1 + NumberedTermEquations.slot s a = 1 + (termEnumeration s a).val
      rw [NumberedTermEquations.slot_eq_enumeration]
    · change 1 + s.size + NumberedTermEquations.slot t a = 1 + (s.size + (termEnumeration t a).val)
      rw [NumberedTermEquations.slot_eq_enumeration, Nat.add_assoc]
    · change 1 + s.size + t.size + i.val = 1 + (s.size + t.size + i.val)
      omega
  | conj p q hp hq | disj p q hp hq =>
    rcases a with u | a | a
    · cases u; rfl
    · change 1 + slot p a = 1 + (formulaEnumeration p a).val
      rw [hp]
    · change 1 + formulaCount p + slot q a = 1 + (formulaCount p + (formulaEnumeration q a).val)
      rw [hq, Nat.add_assoc]

@[simp] theorem root_slot (p : Formula n) : slot p (formulaRoot p) = 0 := by cases p <;> rfl

def address (p : Formula n) (inputs : Fin n → ℕ) (offset : ℕ) : Fin n ⊕ FormulaSlot p → ℕ :=
  Sum.elim inputs (fun a => offset + slot p a)

def equalityPorts (offset left right : ℕ) : Fin 3 → ℕ := ![offset, left, right]
def signPorts (offset left right extra : ℕ) : Fin 6 → ℕ := ![offset, left, right, extra, extra + 1, extra + 2]

theorem eq_left_address (s t : Term n) (inputs : Fin n → ℕ) (offset : ℕ) :
    address (.eq s t) inputs offset ∘ atomLeft s t = NumberedTermEquations.address s inputs (offset + 1) := by
  funext a
  cases a <;> simp [address, NumberedTermEquations.address, atomLeft, slot, Nat.add_assoc]

theorem eq_right_address (s t : Term n) (inputs : Fin n → ℕ) (offset : ℕ) :
    address (.eq s t) inputs offset ∘ atomRight s t = NumberedTermEquations.address t inputs (offset + 1 + s.size) := by
  funext a
  cases a <;> simp [address, NumberedTermEquations.address, atomRight, slot, Nat.add_assoc]

theorem eq_ports_address (s t : Term n) (inputs : Fin n → ℕ) (offset : ℕ) :
    address (.eq s t) inputs offset ∘ atomEqualityPorts s t = equalityPorts offset (offset + 1) (offset + 1 + s.size) := by
  funext i
  fin_cases i <;> simp [address, atomEqualityPorts, atomPorts, slot, equalityPorts, Nat.add_assoc]

theorem lt_left_address (s t : Term n) (inputs : Fin n → ℕ) (offset : ℕ) :
    address (.lt s t) inputs offset ∘ atomLeft s t = NumberedTermEquations.address s inputs (offset + 1) := by
  funext a
  cases a <;> simp [address, NumberedTermEquations.address, atomLeft, slot, Nat.add_assoc]

theorem lt_right_address (s t : Term n) (inputs : Fin n → ℕ) (offset : ℕ) :
    address (.lt s t) inputs offset ∘ atomRight s t = NumberedTermEquations.address t inputs (offset + 1 + s.size) := by
  funext a
  cases a <;> simp [address, NumberedTermEquations.address, atomRight, slot, Nat.add_assoc]

theorem lt_ports_address (s t : Term n) (inputs : Fin n → ℕ) (offset : ℕ) :
    address (.lt s t) inputs offset ∘ atomPorts s t =
      signPorts offset (offset + 1) (offset + 1 + s.size) (offset + 1 + s.size + t.size) := by
  funext i
  fin_cases i <;> simp [address, atomPorts, slot, signPorts, Nat.add_assoc]

def equations : (p : Formula n) → (Fin n → ℕ) → ℕ → List (Poly ℕ)
  | .truth, _, offset => [product (atom offset) (sub (atom offset) (constant 1))]
  | .falsity, _, offset => [atom offset]
  | .eq s t, inputs, offset =>
      NumberedTermEquations.equations s inputs (offset + 1) ++
        NumberedTermEquations.equations t inputs (offset + 1 + s.size) ++
        SparseCircuit.equalityActivation.map (relabel (equalityPorts offset (offset + 1) (offset + 1 + s.size)))
  | .lt s t, inputs, offset =>
      NumberedTermEquations.equations s inputs (offset + 1) ++
        NumberedTermEquations.equations t inputs (offset + 1 + s.size) ++
        SparseCircuit.strictSign.map (relabel (signPorts offset (offset + 1) (offset + 1 + s.size)
          (offset + 1 + s.size + t.size)))
  | .conj p q, inputs, offset => equations p inputs (offset + 1) ++ equations q inputs (offset + 1 + formulaCount p) ++
      [product (atom offset) (sub (atom offset) (constant 1)),
        sub (atom (offset + 1)) (atom offset), sub (atom (offset + 1 + formulaCount p)) (atom offset)]
  | .disj p q, inputs, offset => equations p inputs (offset + 1) ++ equations q inputs (offset + 1 + formulaCount p) ++
      [product (atom offset) (sub (atom offset) (constant 1)),
        sub (add (atom (offset + 1)) (atom (offset + 1 + formulaCount p))) (atom offset)]

theorem equations_agree (p : Formula n) (inputs : Fin n → ℕ) (offset : ℕ) :
    (SparseCircuit.formulaEquations p).map (relabel (address p inputs offset)) = equations p inputs offset := by
  induction p generalizing offset with
  | truth => simp [SparseCircuit.formulaEquations, equations, relabel_product, relabel_sub,
      relabel_atom, relabel_constant, address, slot]
  | falsity => simp [SparseCircuit.formulaEquations, equations, relabel_atom, address, slot]
  | eq s t =>
    simp only [SparseCircuit.formulaEquations, equations, List.map_append, map_relabel_comp]
    rw [eq_left_address, eq_right_address, eq_ports_address, NumberedTermEquations.equations_agree,
      NumberedTermEquations.equations_agree]
  | lt s t =>
    simp only [SparseCircuit.formulaEquations, equations, List.map_append, map_relabel_comp]
    rw [lt_left_address, lt_right_address, lt_ports_address, NumberedTermEquations.equations_agree,
      NumberedTermEquations.equations_agree]
  | conj p q hp hq =>
    have hl : address (.conj p q) inputs offset ∘ formulaLeft p q = address p inputs (offset + 1) := by
      funext a; cases a <;> simp [address, formulaLeft, slot, Nat.add_assoc]
    have hr : address (.conj p q) inputs offset ∘ formulaRight p q = address q inputs (offset + 1 + formulaCount p) := by
      funext a; cases a <;> simp [address, formulaRight, slot, Nat.add_assoc]
    simp only [SparseCircuit.formulaEquations, equations, List.map_append, map_relabel_comp]
    rw [hl, hr, hp, hq]
    simp only [List.map_cons, List.map_nil, relabel_product, relabel_sub, relabel_atom, relabel_constant,
      address, Sum.elim_inr, slot, root_slot, Nat.add_zero, Nat.add_assoc]
  | disj p q hp hq =>
    have hl : address (.disj p q) inputs offset ∘ formulaLeft p q = address p inputs (offset + 1) := by
      funext a; cases a <;> simp [address, formulaLeft, slot, Nat.add_assoc]
    have hr : address (.disj p q) inputs offset ∘ formulaRight p q = address q inputs (offset + 1 + formulaCount p) := by
      funext a; cases a <;> simp [address, formulaRight, slot, Nat.add_assoc]
    simp only [SparseCircuit.formulaEquations, equations, List.map_append, map_relabel_comp]
    rw [hl, hr, hp, hq]
    simp only [List.map_cons, List.map_nil, relabel_product, relabel_sub, relabel_add, relabel_atom,
      relabel_constant, address, Sum.elim_inr, slot, root_slot, Nat.add_zero, Nat.add_assoc]

def closed (p : Formula n) (inputs : Fin n → ℕ) (offset : ℕ) : List (Poly ℕ) :=
  equations p inputs offset ++ [sub (atom offset) (constant 1)]

theorem closed_agree (p : Formula n) (inputs : Fin n → ℕ) (offset : ℕ) :
    (SparseCircuit.closedEquations p).map (relabel (address p inputs offset)) = closed p inputs offset := by
  simp only [SparseCircuit.closedEquations, closed, List.map_append]
  rw [equations_agree]
  simp only [List.map_cons, List.map_nil, relabel_sub, relabel_atom, relabel_constant,
    address, Sum.elim_inr, root_slot, Nat.add_zero]

end JointThermoComplexity.Complexity.NumberedFormulaEquations

#print axioms JointThermoComplexity.Complexity.NumberedFormulaEquations.slot_eq_enumeration
#print axioms JointThermoComplexity.Complexity.NumberedFormulaEquations.equations_agree
#print axioms JointThermoComplexity.Complexity.NumberedFormulaEquations.closed_agree
