module
public import proofs.JointThermoComplexity.Complexity.MotifCompleteBody

set_option autoImplicit false
@[expose] public section

/-! Complete core processing and index advancement leave copied fuel and original metadata outside tapes2..13. -/

namespace JointThermoComplexity.Complexity.MotifCompleteFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def Unchanged (m : ℕ) (work work' : Fin (m + 22) → Tape) : Prop :=
  ∀ j, j.val < 2 ∨ 14 ≤ j.val → work' j = work j

theorem of_motif (m : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : MotifPassFrame.Unchanged (m + 7) work work') : Unchanged m work work' := by
  intro j hj
  apply hw j
  · intro he; have hv := congrArg Fin.val he; change j.val = 2 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 3 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 4 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega

theorem of_species (m : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : ProductionSpeciesFrame.Unchanged m work work') : Unchanged m work work' := by
  intro j hj
  exact ProductionSpeciesFrame.outside m work work' hw j (by omega)

theorem of_single (m : ℕ) (r : Fin (m + 22)) (hr : 2 ≤ r.val ∧ r.val ≤ 13)
    (work work' : Fin (m + 22) → Tape) (hw : ∀ j, j ≠ r → work' j = work j) : Unchanged m work work' := by
  intro j hj
  apply hw j
  intro he
  have hv := congrArg Fin.val he
  omega

theorem kept (m : ℕ) (input : List Bool) (work work' : Fin (m + 22) → Tape) (hw : Unchanged m work work') :
    CurrentPins.Kept (m + 7) input work → CurrentPins.Kept (m + 7) input work' := by
  have ho := hw (CountLayout.offset (m + 14)) (Or.inl (by change (0 : ℕ) < 2; omega))
  have hb := hw (CountLayout.binder (m + 14)) (Or.inl (by change (1 : ℕ) < 2; omega))
  have hm := hw (RoutedNetworkParser.master (m + 16)) (Or.inr (by change 14 ≤ m + 16; omega))
  have hc : ∀ i : Fin 3, work' (RoutedNetworkParser.count (m + 16) i) = work (RoutedNetworkParser.count (m + 16) i) := by
    intro i
    exact hw _ (Or.inr (by change 14 ≤ m + 16 + 1 + i.val; omega))
  intro hp
  change IsReg _ (work' (CountLayout.offset (m + 14))) ∧ IsReg _ (work' (CountLayout.binder (m + 14))) ∧
    (work' (RoutedNetworkParser.master (m + 16))).head = 1 ∧
    (work' (RoutedNetworkParser.master (m + 16))).read = Γ.ofBool (NetworkInputControl.accepted input) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 16) 0)) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 16) 1)) ∧ IsReg _ (work' (RoutedNetworkParser.count (m + 16) 2))
  rw [ho, hb, hm, hc 0, hc 1, hc 2]
  exact hp

end JointThermoComplexity.Complexity.MotifCompleteFrame

#print axioms JointThermoComplexity.Complexity.MotifCompleteFrame.of_motif
#print axioms JointThermoComplexity.Complexity.MotifCompleteFrame.of_species
#print axioms JointThermoComplexity.Complexity.MotifCompleteFrame.kept
