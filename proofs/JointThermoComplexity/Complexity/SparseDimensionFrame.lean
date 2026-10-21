module
public import proofs.JointThermoComplexity.Complexity.SparseCountedEntry
public import proofs.JointThermoComplexity.Complexity.BoundedUnaryEmit

set_option autoImplicit false
@[expose] public section

/-! Concrete reusable header ports preserve the parsed source and offset. -/

namespace JointThermoComplexity.Complexity.SparseDimensionFrame
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork)
open SparseOffsetPorts
open CountedSparseControl (State)

def ports : BoundedUnaryUnit.Ports 33 where
  idx := layout.aux.castSucc
  value := rows.castSucc
  flag := layout.adjusted.castSucc
  fuel := fuel.castSucc
  idx_value := by decide
  flag_idx := by decide
  flag_value := by decide
  fuel_idx := by decide
  fuel_value := by decide
  fuel_flag := by decide

def Protected (L n : ℕ) (s : State) (work : Fin 33 → Tape) : Prop :=
  SparseOffsetLayout.Ready L layout (oldWork work) ∧ Register s.base.offset (work layout.acc.castSucc) ∧
    OffsetContribution.Empty (work (Fin.last 32)) ∧ (work marker.castSucc).head = 1 ∧
      (work marker.castSucc).read = Γ.ofBool s.base.running ∧ IsReg n (work arity.castSucc)

theorem empty_iff_register (t : Tape) : OffsetContribution.Empty t ↔ Register 0 t := Iff.rfl

theorem protected_stable (L n : ℕ) (s : State) : BoundedUnaryLoop.Stable ports (Protected L n s) := by
  rintro work next he ⟨⟨hi, hs, hp, hend, hf⟩, ha, hl, hmh, hmr, har⟩
  have low (j : Fin 32) (hj : j.val ≤ 11) : next j.castSucc = work j.castSucc := by
    have hn (k : Fin 33) (hk : 11 < k.val) : j.castSucc ≠ k := by
      intro hjk
      have hv := congrArg (fun x : Fin 33 => x.val) hjk
      change j.val = k.val at hv
      omega
    exact he j.castSucc (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [oldWork]
    rw [low layout.idx (by decide)]; exact hi
  · simp only [oldWork]
    rw [low layout.sign (by decide)]; exact hs
  · intro p hmem
    have hm : p ∈ [(2, 6), (3, 7), (4, 8), (5, 9)] := hmem
    simp at hm
    have hd : p.1.val ≤ 11 := by rcases hm with rfl | rfl | rfl | rfl <;> decide
    have hmark : p.2.val ≤ 11 := by rcases hm with rfl | rfl | rfl | rfl <;> decide
    simp only [oldWork]
    rw [low p.1 hd, low p.2 hmark]
    exact hp p hmem
  · simp only [oldWork]
    rw [low layout.ending (by decide)]; exact hend
  · simp only [oldWork]
    rw [low layout.flag (by decide)]; exact hf
  · rw [he layout.acc.castSucc (by decide) (by decide) (by decide) (by decide)]; exact ha
  · rw [he (Fin.last 32) (by decide) (by decide) (by decide) (by decide)]; exact hl
  · rw [he marker.castSucc (by decide) (by decide) (by decide) (by decide)]; exact hmh
  · rw [he marker.castSucc (by decide) (by decide) (by decide) (by decide)]; exact hmr
  · rw [he arity.castSucc (by decide) (by decide) (by decide) (by decide)]; exact har

theorem state_iff (L n : ℕ) (s : State) (emitted : List Bool) (inp out : Tape) (work : Fin 33 → Tape) :
    (CountedMarkedStep.Inv L emitted (SparseCountedEntry.frame n) s inp work out ∧ IsReg L (work fuel.castSucc)) ↔
      BoundedUnaryEmit.Pre ports s.rows L s.base.before s.base.input emitted (Protected L n s) inp work out := by
  constructor
  · rintro ⟨⟨hc, hs, ⟨⟨hready, hadj, ha, hu, hl, har⟩, hn⟩, hmh, hmr⟩, hf⟩
    exact ⟨hc, hs, (empty_iff_register _).mp hu, hn, hadj, hf, hready, ha, hl, hmh, hmr, har⟩
  · rintro ⟨hc, hs, hu, hn, hadj, hf, hready, ha, hl, hmh, hmr, har⟩
    exact ⟨⟨hc, hs, ⟨⟨hready, hadj, ha, (empty_iff_register _).mpr hu, hl, har⟩, hn⟩, hmh, hmr⟩, hf⟩

end JointThermoComplexity.Complexity.SparseDimensionFrame

#print axioms JointThermoComplexity.Complexity.SparseDimensionFrame.protected_stable
#print axioms JointThermoComplexity.Complexity.SparseDimensionFrame.state_iff
