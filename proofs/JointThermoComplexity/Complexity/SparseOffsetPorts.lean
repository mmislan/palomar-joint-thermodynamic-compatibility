module
public import proofs.JointThermoComplexity.Complexity.SparseOffsetLayout

set_option autoImplicit false
@[expose] public section

/-! Concrete disjoint tapes for the sparse offset pass. -/

namespace JointThermoComplexity.Complexity.SparseOffsetPorts
open SparseOffsetLayout BoundedOccurrenceMachine

def slots : List (Fin 32 × Fin 32) := [(2, 6), (3, 7), (4, 8), (5, 9)]

def layout : Layout 32 where
  slots := slots
  ending := 10
  flag := 11
  idx := 0
  sign := 1
  adjusted := 12
  acc := 13
  aux := 14
  length := rfl
  parse_sep := by
    refine ⟨?_, by decide, ?_, ?_⟩
    · change HeadSeparate (2, 6) [(3, 7), (4, 8), (5, 9)] 10 11 ∧
        HeadSeparate (3, 7) [(4, 8), (5, 9)] 10 11 ∧
        HeadSeparate (4, 8) [(5, 9)] 10 11 ∧ HeadSeparate (5, 9) [] 10 11 ∧ (10 : Fin 33) ≠ 11
      refine ⟨?_, ?_, ?_, ?_, by decide⟩ <;> constructor <;> simp
    · simp [Touches, liftSlots, slots]
    · simp [Touches, liftSlots, slots]
  arithmetic_sep := by constructor <;> decide
  adjusted_outside := by simp [Touches, liftSlots, slots]
  acc_outside := by simp [Touches, liftSlots, slots]
  aux_outside := by simp [Touches, liftSlots, slots]

def marker : Fin 32 := 15
def arity : Fin 32 := 16
def rows : Fin 32 := 17
def fuel : Fin 32 := 18

def Outside (d : Layout 32) (j : Fin 32) : Prop :=
  j ≠ d.idx ∧ j ≠ d.sign ∧ ¬d.Touches j.castSucc ∧ j ≠ d.adjusted ∧ j ≠ d.acc ∧ j ≠ d.aux

theorem protected_outside (j : Fin 32) (hj : 16 ≤ j.val) : Outside layout j := by
  have hn (k : Fin 32) (hk : k.val < 16) : j ≠ k := by
    intro he
    have hv := congrArg (fun x : Fin 32 => x.val) he
    omega
  have hc (k : Fin 33) (hk : k.val < 16) : j.castSucc ≠ k := by
    intro he
    have hv := congrArg (fun x : Fin 33 => x.val) he
    change j.val = k.val at hv
    omega
  refine ⟨hn 0 (by decide), hn 1 (by decide), ?_, hn 12 (by decide), hn 13 (by decide), hn 14 (by decide)⟩
  change ¬(j.castSucc = 10 ∨ j.castSucc = 11 ∨
    ∃ p ∈ ([(2, 6), (3, 7), (4, 8), (5, 9)] : List (Fin 33 × Fin 33)), j.castSucc = p.1 ∨ j.castSucc = p.2)
  rintro (he | he | ⟨p, hp, he⟩)
  · exact hc 10 (by decide) he
  · exact hc 11 (by decide) he
  · simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals rcases he with he | he
    all_goals exact hc _ (by decide) he

theorem marker_outside : Outside layout marker := by
  simp [Outside, layout, marker, Layout.Touches, Layout.Physical, Touches, liftSlots, slots]
theorem arity_outside : Outside layout arity := protected_outside arity (by decide)
theorem rows_outside : Outside layout rows := protected_outside rows (by decide)
theorem fuel_outside : Outside layout fuel := protected_outside fuel (by decide)
theorem marker_fuel : marker ≠ fuel := by decide

end JointThermoComplexity.Complexity.SparseOffsetPorts

#print axioms JointThermoComplexity.Complexity.SparseOffsetPorts.layout
#print axioms JointThermoComplexity.Complexity.SparseOffsetPorts.fuel_outside
