module
public import proofs.JointThermoComplexity.Complexity.ProductionOperandLoad
public import proofs.JointThermoComplexity.Complexity.MotifPassFrame
public import proofs.JointThermoComplexity.Complexity.OuterFuelCopyFrame

set_option autoImplicit false
@[expose] public section

/-! Reusable production data reconstruct the full arithmetic State when all work tapes are parked. -/

namespace JointThermoComplexity.Complexity.ProductionOperandData
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts BoxBufferState

structure Data (m L n ri si : ℕ) (work : Fin (m + 20) → Tape) : Prop where
  productReusable : Reusable L (work (left m))
  reactantReusable : Reusable L (work (right m))
  magnitudeReusable : Reusable L (work (magnitude m))
  signHead : (work (sign m)).head = 1
  speciesPosition : IsReg si (work (species m))
  speciesCount : IsReg n (work (count m))
  reactionPosition : IsReg ri (work (reaction m))

theorem of_state (m L n ri si : ℕ) (work : Fin (m + 20) → Tape)
    (h : ProductionOperandLoad.State m L n ri si work) : Data m L n ri si work :=
  ⟨h.productReusable, h.reactantReusable, h.magnitudeReusable, h.signHead, h.speciesPosition, h.speciesCount, h.reactionPosition⟩

theorem to_state (m L n ri si : ℕ) (work : Fin (m + 20) → Tape)
    (hs : ∀ j, Parked (work j)) (h : Data m L n ri si work) : ProductionOperandLoad.State m L n ri si work :=
  ⟨hs, h.productReusable, h.reactantReusable, h.magnitudeReusable, h.signHead, h.speciesPosition, h.speciesCount, h.reactionPosition⟩

theorem motif_frame (m L n ri si : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : MotifPassFrame.Unchanged (m + 5) work work') (h : Data m L n ri si work) : Data m L n ri si work' := by
  have hx (j : Fin (m + 20)) (hj : j.val = 6 ∨ 8 ≤ j.val) : work' j = work j :=
    MotifPassFrame.outside (m + 5) work work' hw j hj
  exact ⟨by simpa only [hx (left m) (Or.inr (by change 8 ≤ (9 : ℕ); omega))] using h.productReusable,
    by simpa only [hx (right m) (Or.inr (by change 8 ≤ (10 : ℕ); omega))] using h.reactantReusable,
    by simpa only [hx (magnitude m) (Or.inr (by change 8 ≤ (8 : ℕ); omega))] using h.magnitudeReusable,
    by simpa only [hx (sign m) (Or.inr (by change 8 ≤ (11 : ℕ); omega))] using h.signHead,
    by simpa only [hx (species m) (Or.inr (by change 8 ≤ (12 : ℕ); omega))] using h.speciesPosition,
    by simpa only [hx (count m) (Or.inr (by change 8 ≤ m + 15; omega))] using h.speciesCount,
    by simpa only [hx (reaction m) (Or.inl rfl)] using h.reactionPosition⟩

theorem outer_frame (m L n ri si : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : OuterFuelCopyFrame.Unchanged m work work') (h : Data (m + 2) L n ri si work) : Data (m + 2) L n ri si work' := by
  have hx (j : Fin (m + 22)) (hj : j.val ≤ 13 ∨ 16 ≤ j.val) : work' j = work j :=
    OuterFuelCopyFrame.outside m work work' hw j hj
  exact ⟨by simpa only [hx (left (m + 2)) (Or.inl (by change (9 : ℕ) ≤ 13; omega))] using h.productReusable,
    by simpa only [hx (right (m + 2)) (Or.inl (by change (10 : ℕ) ≤ 13; omega))] using h.reactantReusable,
    by simpa only [hx (magnitude (m + 2)) (Or.inl (by change (8 : ℕ) ≤ 13; omega))] using h.magnitudeReusable,
    by simpa only [hx (sign (m + 2)) (Or.inl (by change (11 : ℕ) ≤ 13; omega))] using h.signHead,
    by simpa only [hx (species (m + 2)) (Or.inl (by change (12 : ℕ) ≤ 13; omega))] using h.speciesPosition,
    by simpa only [hx (count (m + 2)) (Or.inr (by change 16 ≤ m + 17; omega))] using h.speciesCount,
    by simpa only [hx (reaction (m + 2)) (Or.inl (by change (6 : ℕ) ≤ 13; omega))] using h.reactionPosition⟩

end JointThermoComplexity.Complexity.ProductionOperandData

#print axioms JointThermoComplexity.Complexity.ProductionOperandData.to_state
#print axioms JointThermoComplexity.Complexity.ProductionOperandData.motif_frame
#print axioms JointThermoComplexity.Complexity.ProductionOperandData.outer_frame
