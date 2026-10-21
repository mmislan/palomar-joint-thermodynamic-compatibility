module
public import proofs.JointThermoComplexity.Complexity.SparseOffsetPorts

set_option autoImplicit false
@[expose] public section

/-! The existing source layout in a 64-tape workspace, with final scratch63. -/

namespace JointThermoComplexity.Complexity.DenseParserPorts
open _root_.Complexity _root_.Complexity.TM
open SparseOffsetLayout BoundedOccurrenceMachine

def slots : List (Fin 63 × Fin 63) := [(2, 6), (3, 7), (4, 8), (5, 9)]

def layout : Layout 63 where
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
        HeadSeparate (4, 8) [(5, 9)] 10 11 ∧ HeadSeparate (5, 9) [] 10 11 ∧ (10 : Fin 64) ≠ 11
      refine ⟨?_, ?_, ?_, ?_, by decide⟩ <;> constructor <;> simp
    · simp [Touches, liftSlots, slots]
    · simp [Touches, liftSlots, slots]
  arithmetic_sep := by constructor <;> decide
  adjusted_outside := by simp [Touches, liftSlots, slots]
  acc_outside := by simp [Touches, liftSlots, slots]
  aux_outside := by simp [Touches, liftSlots, slots]

def marker : Fin 64 := 15
def arity : Fin 64 := 16
def rows : Fin 64 := 17
def fuel : Fin 64 := 18

abbrev sourceWork (work : Fin 64 → Tape) : Fin 32 → Tape := fun j => work ⟨j.val, by omega⟩

theorem ready_iff (L : ℕ) (work : Fin 64 → Tape) :
    SparseOffsetLayout.Ready L layout (BinaryScaleBuffer.oldWork work) ↔
      SparseOffsetLayout.Ready L SparseOffsetPorts.layout (sourceWork work) := by
  simp [SparseOffsetLayout.Ready, layout, slots, SparseOffsetPorts.layout, SparseOffsetPorts.slots,
    BinaryScaleBuffer.oldWork, sourceWork]

theorem parse_outside (j : Fin 64) (hj : 12 ≤ j.val) :
    j ≠ layout.idx.castSucc ∧ j ≠ layout.sign.castSucc ∧ ¬layout.Touches j := by
  have hn (k : Fin 64) (hk : k.val < 12) : j ≠ k := by
    intro he
    have hv := congrArg (fun x : Fin 64 => x.val) he
    omega
  refine ⟨hn 0 (by decide), hn 1 (by decide), ?_⟩
  change ¬(j = 10 ∨ j = 11 ∨ ∃ p ∈ ([(2, 6), (3, 7), (4, 8), (5, 9)] : List (Fin 64 × Fin 64)), j = p.1 ∨ j = p.2)
  rintro (he | he | ⟨p, hp, he⟩)
  · exact hn 10 (by decide) he
  · exact hn 11 (by decide) he
  · simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals rcases he with he | he
    all_goals exact hn _ (by decide) he

def machine : TM 64 := SparseTermCanonicalLoad.machine layout.Physical
  layout.ending.castSucc layout.flag.castSucc layout.idx.castSucc layout.sign.castSucc

theorem hoareTime (L : ℕ) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin 64 → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ layout.idx.castSucc → j ≠ layout.sign.castSucc → ¬layout.Touches j → next j = work j) →
      R work → R next) :
    machine.HoareTime
      (SparseTermCanonicalLoad.Pre L layout.Physical layout.ending.castSucc layout.flag.castSucc
        layout.idx.castSucc layout.sign.castSucc before input emitted R)
      (SparseTermCanonicalLoad.Post L layout.Physical layout.ending.castSucc layout.flag.castSucc
        layout.idx.castSucc layout.sign.castSucc before input emitted R) (75 * L + 118) :=
  SparseTermCanonicalLoad.four_hoareTime _ _ _ _ _ (physical_length layout) layout.parse_sep L before input emitted hlen R hR

end JointThermoComplexity.Complexity.DenseParserPorts

#print axioms JointThermoComplexity.Complexity.DenseParserPorts.ready_iff
#print axioms JointThermoComplexity.Complexity.DenseParserPorts.parse_outside
#print axioms JointThermoComplexity.Complexity.DenseParserPorts.hoareTime
