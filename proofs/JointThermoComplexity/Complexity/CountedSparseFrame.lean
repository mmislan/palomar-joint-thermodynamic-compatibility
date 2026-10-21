module
public import proofs.JointThermoComplexity.Complexity.SparseOffsetPorts
public import proofs.JointThermoComplexity.Complexity.SparseTermOffsetBody

set_option autoImplicit false
@[expose] public section

/-! Count-tape framing for reusable sparse parsing and offset arithmetic. -/

namespace JointThermoComplexity.Complexity.CountedSparseFrame
open _root_.Complexity _root_.Complexity.TM HeaderAt
open BinaryScaleBuffer (oldWork)
open SparseOffsetPorts

def Stable (R : (Fin 32 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ rows → next j = work j) → R work → R next

theorem row_stable (N : ℕ) : SparseOffsetLayout.Stable layout
    (fun work => BinaryIncrementRun.Register N (work rows)) := by
  intro work next he hr
  have hn := rows_outside
  rw [he rows hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2]
  exact hr

theorem touched_ne (j : Fin 33) (hj : layout.Touches j) : j ≠ rows.castSucc := by
  intro he
  exact rows_outside.2.2.1 (he ▸ hj)

theorem fields_stable (L A : ℕ) (R : (Fin 32 → Tape) → Prop) (hR : Stable R) :
    ∀ work next, (∀ j, j ≠ rows.castSucc → next j = work j) →
      SparseTermOffsetBody.Fields L layout A R work → SparseTermOffsetBody.Fields L layout A R next := by
  rintro work next he ⟨⟨hi, hs, hp, hend, hf⟩, hh, ha, hu, hl, hr⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [oldWork]
    rw [he layout.idx.castSucc (by decide)]; exact hi
  · simp only [oldWork]
    rw [he layout.sign.castSucc (by decide)]; exact hs
  · intro p hmem
    have hphys : (p.1.castSucc, p.2.castSucc) ∈ layout.Physical := List.mem_map.mpr ⟨p, hmem, rfl⟩
    simp only [oldWork]
    rw [he p.1.castSucc (touched_ne _ (Or.inr (Or.inr ⟨_, hphys, Or.inl rfl⟩))),
      he p.2.castSucc (touched_ne _ (Or.inr (Or.inr ⟨_, hphys, Or.inr rfl⟩)))]
    exact hp p hmem
  · simp only [oldWork]
    rw [he layout.ending.castSucc (by decide)]; exact hend
  · simp only [oldWork]
    rw [he layout.flag.castSucc (by decide)]; exact hf
  · rw [he layout.adjusted.castSucc (by decide)]; exact hh
  · rw [he layout.acc.castSucc (by decide)]; exact ha
  · rw [he layout.aux.castSucc (by decide)]; exact hu
  · rw [he (Fin.last 32) (by decide)]; exact hl
  · exact hR _ _ (fun j hj => he j.castSucc (TemplateFactorPipeline.cast_ne _ _ hj)) hr

theorem loaded_stable (raw : List Bool) :
    ∀ work next, (∀ j, j ≠ rows.castSucc → next j = work j) →
      BoundedOccurrenceMachine.Loaded layout.Physical layout.ending.castSucc layout.flag.castSucc raw work →
      BoundedOccurrenceMachine.Loaded layout.Physical layout.ending.castSucc layout.flag.castSucc raw next := by
  intro work next he hl
  exact SparseOffsetLayout.loaded_congr _ _ _ raw work next (fun j hj => he j (touched_ne j hj)) hl

end JointThermoComplexity.Complexity.CountedSparseFrame

#print axioms JointThermoComplexity.Complexity.CountedSparseFrame.fields_stable
#print axioms JointThermoComplexity.Complexity.CountedSparseFrame.loaded_stable
