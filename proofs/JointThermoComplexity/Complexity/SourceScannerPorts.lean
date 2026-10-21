module
public import proofs.JointThermoComplexity.Complexity.SourceSentenceEntry

set_option autoImplicit false
@[expose] public section

/-! A single eleven-work-tape source scanner layout, independent of the runtime arity. -/

namespace JointThermoComplexity.Complexity.SourceScannerPorts
open _root_.Complexity _root_.Complexity.TM SourceFormulaRegisters

def tags (i : Fin 3) : Fin 10 := ⟨i.val + 5, by omega⟩

def layout : Layout 9 where
  tags := tags
  termFuel := 0
  termPending := 1
  formulaPending := 2
  left := 3
  right := 4
  tagSep := ⟨by decide, by decide, by decide, by decide⟩
  operandSep := ⟨by decide, by decide, by decide⟩
  termSep := ⟨by decide, by decide, by decide, by decide⟩
  formulaSep := ⟨by decide, by decide, by decide, by decide⟩
  fuelSep := ⟨by decide, by decide, by decide, by decide⟩
  fuelTerm := by decide
  fuelFormula := by decide
  pendingDistinct := by decide

def fuel : Fin 10 := 8

theorem fuel_outside : Outside layout fuel :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

def values (L : ℕ) (j : Fin 11) : ℕ := if j = layout.termFuel.castSucc ∨ j = fuel.castSucc then L else 0
def lengthWork (L : ℕ) (j : Fin 11) : Tape := regTape (values L j)

theorem lengthWork_register (L : ℕ) (j : Fin 11) : IsReg (values L j) (lengthWork L j) := reg_regT _
theorem lengthWork_safe (L : ℕ) (j : Fin 11) : Parked (lengthWork L j) := parked_regTape _
theorem lengthWork_markers (L : ℕ) (j : Fin 11) : (lengthWork L j).cells 0 = Γ.start :=
  (lengthWork_register L j).cell0

theorem lengthWork_termFuel (L : ℕ) : lengthWork L layout.termFuel.castSucc = regTape L := by
  simp only [lengthWork, values, true_or, ↓reduceIte]

theorem lengthWork_fuel (L : ℕ) : lengthWork L fuel.castSucc = regTape L := by
  simp only [lengthWork, values, or_true, ↓reduceIte]

theorem lengthWork_other (L : ℕ) (j : Fin 11) (ht : j ≠ layout.termFuel.castSucc) (hf : j ≠ fuel.castSucc) :
    lengthWork L j = regTape 0 := by
  simp only [lengthWork, values, ht, hf, or_self, ↓reduceIte]

end JointThermoComplexity.Complexity.SourceScannerPorts

#print axioms JointThermoComplexity.Complexity.SourceScannerPorts.fuel_outside
