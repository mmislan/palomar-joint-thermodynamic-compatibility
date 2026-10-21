module
public import proofs.JointThermoComplexity.Complexity.DenseParserPorts
public import proofs.JointThermoComplexity.Complexity.ReusablePowerVector

set_option autoImplicit false
@[expose] public section

/-! Concrete selected source references2..5, binary index39, flags44..47 and fuel16. -/

namespace JointThermoComplexity.Complexity.DensePowerPorts
open _root_.Complexity

def index : Fin 64 := 39
def reference (m : ℕ) (hm : m ≤ 4) (i : Fin m) : Fin 64 := ⟨2 + i.val, by omega⟩
def flag (m : ℕ) (hm : m ≤ 4) (i : Fin m) : Fin 64 := ⟨44 + i.val, by omega⟩

def comparison (m : ℕ) (hm : m ≤ 4) (i : Fin m) : SmallCoefficientMatch.Ports 63 where
  operand := index
  constant := reference m hm i
  flag := flag m hm i
  separate := by
    constructor
    · intro he
      have hv := congrArg (fun j : Fin 64 => j.val) he
      change 39 = 2 + i.val at hv
      omega
    · intro he
      have hv := congrArg (fun j : Fin 64 => j.val) he
      change 44 + i.val = 39 at hv
      omega
    · intro he
      have hv := congrArg (fun j : Fin 64 => j.val) he
      change 44 + i.val = 2 + i.val at hv
      omega

def cellLayout (m : ℕ) (hm : m ≤ 4) : PowerVectorControl.Layout 63 where
  idx := index
  comparisons := List.ofFn (comparison m hm)
  operand_eq := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    rfl
  separated := by
    intro p hp q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    constructor
    · intro he
      have hv := congrArg (fun k : Fin 64 => k.val) he
      change 39 = 44 + j.val at hv
      omega
    · intro he
      have hv := congrArg (fun k : Fin 64 => k.val) he
      change 2 + i.val = 44 + j.val at hv
      omega
  unique := by
    apply List.pairwise_ofFn.mpr
    intro i j hij he
    have hv := congrArg (fun k : Fin 64 => k.val) he
    change 44 + i.val = 44 + j.val at hv
    have hlt : i.val < j.val := hij
    omega

def layout (m : ℕ) (hm : m ≤ 4) : PowerVectorLoop.Layout 63 where
  cell := cellLayout m hm
  fuel := DenseParserPorts.arity
  fuel_idx := by change (16 : Fin 64) ≠ 39; decide
  fuel_ref := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    intro he
    have hv := congrArg (fun k : Fin 64 => k.val) he
    change 16 = 2 + i.val at hv
    omega
  fuel_flag := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    intro he
    have hv := congrArg (fun k : Fin 64 => k.val) he
    change 16 = 44 + i.val at hv
    omega

theorem count (m : ℕ) (hm : m ≤ 4) : (cellLayout m hm).comparisons.length ≤ 4 := by
  simpa only [cellLayout, List.length_ofFn] using hm

theorem refs (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (work : Fin 64 → Tape)
    (hr : ∀ i : Fin m, BinaryIncrementRun.Register (values (reference m hm i)) (work (reference m hm i)))
    (hf : ∀ i : Fin m, (work (flag m hm i)).head = 1) :
    PowerVectorUnit.Refs (cellLayout m hm) values work := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨hr i, hf i⟩

end JointThermoComplexity.Complexity.DensePowerPorts

#print axioms JointThermoComplexity.Complexity.DensePowerPorts.cellLayout
#print axioms JointThermoComplexity.Complexity.DensePowerPorts.layout
#print axioms JointThermoComplexity.Complexity.DensePowerPorts.refs
