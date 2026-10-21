module
public import proofs.JointThermoComplexity.Complexity.DenseInternalBlocks
public import proofs.JointThermoComplexity.Complexity.DenseExternalPower

set_option autoImplicit false
@[expose] public section

/-! One cell index serves internal and external complex blocks with distinct physical fuels. -/

namespace JointThermoComplexity.Complexity.DenseComplexPorts
open _root_.Complexity

def target (product : Bool) : Fin 64 := if product then 41 else 38

def comparison (product : Bool) : SmallCoefficientMatch.Ports 63 where
  operand := 39
  constant := target product
  flag := 42
  separate := by cases product <;> constructor <;> decide

def ports (product : Bool) : DenseInternalBlocks.Ports 63 where
  comparison := comparison product
  count := 33
  branch := 34
  count_idx := by change (33 : Fin 64) ≠ 39; decide
  count_target := by cases product <;> decide
  count_flag := by change (33 : Fin 64) ≠ 42; decide
  branch_idx := by change (34 : Fin 64) ≠ 39; decide
  branch_target := by cases product <;> decide
  branch_flag := by change (34 : Fin 64) ≠ 42; decide
  count_branch := by decide

theorem target_range (product : Bool) : 38 ≤ (target product).val ∧ (target product).val ≤ 41 := by
  cases product <;> decide

def Outside (product : Bool) (j : Fin 64) : Prop :=
  j ≠ 39 ∧ j ≠ target product ∧ j ≠ 42 ∧ j ≠ 33 ∧ j ≠ 34 ∧ j ≠ 16 ∧ (j.val < 44 ∨ 48 ≤ j.val)

def Stable (product : Bool) (R : (Fin 64 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, Outside product j → next j = work j) → R work → R next

theorem internal_away (product : Bool) (j : Fin 64) (hj : j.val ≤ 16 ∨ 44 ≤ j.val ∧ j.val < 48) :
    j ≠ 39 ∧ j ≠ target product ∧ j ≠ 42 ∧ j ≠ 33 ∧ j ≠ 34 := by
  have hn (k : Fin 64) (hk : 33 ≤ k.val ∧ k.val ≤ 42) : j ≠ k := by
    intro he
    have hv := congrArg (fun t : Fin 64 => t.val) he
    omega
  have ht := target_range product
  exact ⟨hn 39 (by decide), hn (target product) (by omega), hn 42 (by decide), hn 33 (by decide), hn 34 (by decide)⟩

theorem power_flag_range (m : ℕ) (hm : m ≤ 4) :
    ∀ p ∈ (DensePowerPorts.cellLayout m hm).comparisons, 44 ≤ p.flag.val ∧ p.flag.val < 48 := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  change 44 ≤ 44 + i.val ∧ 44 + i.val < 48
  constructor <;> omega

end JointThermoComplexity.Complexity.DenseComplexPorts

#print axioms JointThermoComplexity.Complexity.DenseComplexPorts.ports
#print axioms JointThermoComplexity.Complexity.DenseComplexPorts.internal_away
