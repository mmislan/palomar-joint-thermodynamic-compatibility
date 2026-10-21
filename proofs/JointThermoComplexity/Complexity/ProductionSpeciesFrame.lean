module
public import proofs.JointThermoComplexity.Complexity.OuterPreparedProduction
public import proofs.JointThermoComplexity.Complexity.ProductionSum

set_option autoImplicit false
@[expose] public section

/-! A full species iteration retains common orientations, core index, copied loop fuel and original dimensions. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesFrame
open _root_.Complexity
open _root_.Complexity.TM

def Unchanged (m : ℕ) (work work' : Fin (m + 22) → Tape) : Prop :=
  ∀ j, j ≠ MotifBufferPorts.buffer (m + 7) 0 → j ≠ MotifBufferPorts.buffer (m + 7) 1 →
    j ≠ PowerPorts.scratch (m + 9) → j ≠ ProductionPorts.reaction (m + 2) → j ≠ ProductionPorts.current (m + 2) →
    j ≠ ProductionPorts.magnitude (m + 2) → j ≠ ProductionPorts.left (m + 2) → j ≠ ProductionPorts.right (m + 2) →
    j ≠ ProductionPorts.sign (m + 2) → j ≠ ProductionPorts.species (m + 2) → work' j = work j

theorem of_production (m : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : ProductionReactionState.Unchanged (m + 2) work work') : Unchanged m work work' :=
  fun j _ hm hz hr hc hmag hl hright hs _ => hw j hm hz hr hc hmag hl hright hs

theorem of_start (m : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : ∀ j, j ≠ ProductionPorts.reaction (m + 2) → j ≠ ProductionPorts.current (m + 2) → work' j = work j) :
    Unchanged m work work' := fun j _ _ _ hr hc _ _ _ _ _ => hw j hr hc

theorem of_species (m : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : ∀ j, j ≠ ProductionPorts.species (m + 2) → work' j = work j) : Unchanged m work work' :=
  fun j _ _ _ _ _ _ _ _ _ hs => hw j hs

theorem of_mask (m : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : ∀ j, j ≠ MotifBufferPorts.buffer (m + 7) 0 → work' j = work j) : Unchanged m work work' :=
  fun j hm _ _ _ _ _ _ _ _ _ => hw j hm

theorem outside (m : ℕ) (work work' : Fin (m + 22) → Tape) (hw : Unchanged m work work')
    (j : Fin (m + 22)) (hj : j.val < 2 ∨ j.val = 4 ∨ 13 ≤ j.val) : work' j = work j := by
  apply hw j
  · intro he; have hv := congrArg Fin.val he; change j.val = 2 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 3 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 5 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 6 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 8 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 9 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 10 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 11 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 12 at hv; omega

theorem kept (m : ℕ) (input : List Bool) (work work' : Fin (m + 22) → Tape) (hw : Unchanged m work work') :
    CurrentPins.Kept (m + 7) input work → CurrentPins.Kept (m + 7) input work' := by
  have ho := outside m work work' hw (CountLayout.offset (m + 14)) (Or.inl (by change (0 : ℕ) < 2; omega))
  have hb := outside m work work' hw (CountLayout.binder (m + 14)) (Or.inl (by change (1 : ℕ) < 2; omega))
  have hm := outside m work work' hw (RoutedNetworkParser.master (m + 16)) (Or.inr (Or.inr (by change 13 ≤ m + 16; omega)))
  have hc : ∀ i : Fin 3, work' (RoutedNetworkParser.count (m + 16) i) = work (RoutedNetworkParser.count (m + 16) i) := by
    intro i
    exact outside m work work' hw _ (Or.inr (Or.inr (by change 13 ≤ m + 16 + 1 + i.val; omega)))
  intro hp
  change IsReg _ (work' (CountLayout.offset (m + 14))) ∧ IsReg _ (work' (CountLayout.binder (m + 14))) ∧
    (work' (RoutedNetworkParser.master (m + 16))).head = 1 ∧
    (work' (RoutedNetworkParser.master (m + 16))).read = Γ.ofBool (NetworkInputControl.accepted input) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 16) 0)) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 16) 1)) ∧ IsReg _ (work' (RoutedNetworkParser.count (m + 16) 2))
  rw [ho, hb, hm, hc 0, hc 1, hc 2]
  exact hp

theorem inner_species_mask (m : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : ProductionReactionState.Unchanged (m + 2) work work') :
    work' (MotifBufferPorts.buffer (m + 7) 0) = work (MotifBufferPorts.buffer (m + 7) 0) := by
  apply hw
  · intro he; have hv := congrArg Fin.val he; change (2 : ℕ) = 3 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change (2 : ℕ) = 5 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change (2 : ℕ) = 6 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change (2 : ℕ) = 7 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change (2 : ℕ) = 8 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change (2 : ℕ) = 9 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change (2 : ℕ) = 10 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change (2 : ℕ) = 11 at hv; omega

end JointThermoComplexity.Complexity.ProductionSpeciesFrame

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesFrame.kept
#print axioms JointThermoComplexity.Complexity.ProductionSpeciesFrame.inner_species_mask
