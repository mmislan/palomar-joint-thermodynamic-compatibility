module
public import proofs.JointThermoComplexity.Complexity.PowerReferenceEmit
public import proofs.JointThermoComplexity.Complexity.FiniteCodec

set_option autoImplicit false
@[expose] public section

/-! Exact dense catalyst words for a static list of selected binary references. -/

namespace JointThermoComplexity.Complexity.PowerVectorControl
open SmallCoefficientMatch (Ports)
variable {w : ℕ}

structure Layout (w : ℕ) where
  idx : Fin (w + 1)
  comparisons : List (Ports w)
  operand_eq : ∀ p ∈ comparisons, p.operand = idx
  separated : PowerCellCompare.Separated comparisons
  unique : PowerCellCompare.Unique comparisons

theorem constant_ne_idx (d : Layout w) (p : Ports w) (hp : p ∈ d.comparisons) : p.constant ≠ d.idx := by
  intro he
  exact p.separate.operands ((d.operand_eq p hp).trans he.symm)

theorem flag_ne_idx (d : Layout w) (p : Ports w) (hp : p ∈ d.comparisons) : p.flag ≠ d.idx := by
  intro he
  exact p.separate.flagLeft (he.trans (d.operand_eq p hp).symm)

def cell (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ) (i : ℕ) : ℕ :=
  (d.comparisons.map (fun p => if i = values p.constant then weights p else 0)).sum

theorem cell_eq_power (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ) (i : ℕ) :
    cell d weights values i = PowerReferenceEmit.power d.comparisons weights (Function.update values d.idx i) := by
  unfold cell PowerReferenceEmit.power
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [d.operand_eq p hp, Function.update_self, Function.update_of_ne (constant_ne_idx d p hp)]

def words (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ) (start count : ℕ) : List Bool :=
  (List.ofFn (fun j : Fin count => BitCodec.naturalCode (cell d weights values (start + j.val)))).flatten

theorem words_zero (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ) (start : ℕ) :
    words d weights values start 0 = [] := rfl

theorem words_succ (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ) (start count : ℕ) :
    words d weights values start (count + 1) = words d weights values start count ++
      BitCodec.naturalCode (cell d weights values (start + count)) := by
  unfold words
  rw [List.ofFn_succ_last, List.flatten_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, Fin.val_castSucc, Fin.val_last]

theorem words_code (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ) (start count : ℕ) :
    words d weights values start count = FiniteCodec.functionCode FiniteCodec.natural
      (fun j : Fin count => cell d weights values (start + j.val)) := by
  rw [FiniteCodec.functionCode_eq_flatMap, List.flatMap_def, List.map_ofFn]
  rfl

end JointThermoComplexity.Complexity.PowerVectorControl

#print axioms JointThermoComplexity.Complexity.PowerVectorControl.cell_eq_power
#print axioms JointThermoComplexity.Complexity.PowerVectorControl.words_succ
#print axioms JointThermoComplexity.Complexity.PowerVectorControl.words_code
