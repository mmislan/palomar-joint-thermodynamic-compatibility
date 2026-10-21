module
public import proofs.JointThermoComplexity.Complexity.BoxLoad
public import proofs.JointThermoComplexity.Complexity.CurrentResources
public import proofs.JointThermoComplexity.Complexity.CurrentReady

set_option autoImplicit false
@[expose] public section

/-! The four existing bounded registers become reusable box buffers while validated metadata stays fixed. -/

namespace JointThermoComplexity.Complexity.BoxBufferPorts
open _root_.Complexity
open _root_.Complexity.TM
open BoxBufferState PowerPorts MonomialPorts ReactionPorts

def loNum (m : ℕ) : Fin (m + 15) := next (m + 2)
def loDen (m : ℕ) : Fin (m + 15) := accumulator (m + 2)
def hiNum (m : ℕ) : Fin (m + 15) := power (m + 2)
def hiDen (m : ℕ) : Fin (m + 15) := saved m

def ports (m : ℕ) : List (Fin (m + 15)) := [loNum m, loDen m, hiNum m, hiDen m]

theorem separate (m : ℕ) : BoxLoad.Separate (loNum m) (loDen m) (hiNum m) (hiDen m) :=
  ⟨next_ne_accumulator (m + 2), next_ne_power (m + 2), (saved_ne_next m).symm,
    accumulator_ne_power (m + 2), (saved_ne_accumulator m).symm, (saved_ne_power m).symm⟩

theorem values (m : ℕ) (j : Fin (m + 15)) (hj : j ∈ ports m) :
    j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 8 := by
  have he : j = loNum m ∨ j = loDen m ∨ j = hiNum m ∨ j = hiDen m := by simpa [ports] using hj
  rcases he with h | h | h | h
  · exact Or.inl (congrArg Fin.val h)
  · exact Or.inr (Or.inl (congrArg Fin.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Fin.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Fin.val h)))

theorem source_separate (m : ℕ) : ∀ j ∈ ports m, species (m + 1) ≠ j := by
  intro j hj he
  have hv := values m j hj
  have hs := congrArg Fin.val he
  change (7 : ℕ) = j.val at hs
  omega

theorem scratch_separate (m : ℕ) : ∀ j ∈ ports m, scratch (m + 2) ≠ j := by
  intro j hj he
  have hv := values m j hj
  have hs := congrArg Fin.val he
  change (5 : ℕ) = j.val at hs
  omega

theorem metadata_frame (m : ℕ) (input : List Bool) (work work' : Fin (m + 15) → Tape)
    (hw : ∀ j, j ≠ loNum m → j ≠ loDen m → j ≠ hiNum m → j ≠ hiDen m → work' j = work j) :
    CurrentPins.Kept m input work → CurrentPins.Kept m input work' := by
  have hn (j : Fin (m + 15)) (hj : j.val < 2 ∨ (m + 9 ≤ j.val ∧ j.val ≤ m + 12))
      (r : Fin (m + 15)) (hr : r ∈ ports m) : j ≠ r := by
    intro he
    have hv := values m r hr
    have hsame := congrArg Fin.val he
    omega
  have hx : ∀ j : Fin (m + 15), j.val < 2 ∨ (m + 9 ≤ j.val ∧ j.val ≤ m + 12) → work' j = work j := by
    intro j hj
    exact hw j (hn j hj (loNum m) (by simp [ports])) (hn j hj (loDen m) (by simp [ports]))
      (hn j hj (hiNum m) (by simp [ports])) (hn j hj (hiDen m) (by simp [ports]))
  have ho := hx (CountLayout.offset (m + 7)) (by left; change (0 : ℕ) < 2; omega)
  have hb := hx (CountLayout.binder (m + 7)) (by left; change (1 : ℕ) < 2; omega)
  have hm := hx (RoutedNetworkParser.master (m + 9)) (by right; change m + 9 ≤ m + 9 ∧ m + 9 ≤ m + 12; omega)
  have hc : ∀ i : Fin 3, work' (RoutedNetworkParser.count (m + 9) i) = work (RoutedNetworkParser.count (m + 9) i) := by
    intro i
    apply hx
    right
    change m + 9 ≤ m + 9 + 1 + i.val ∧ m + 9 + 1 + i.val ≤ m + 12
    have hi := i.isLt
    omega
  intro hp
  change IsReg _ (work' (CountLayout.offset (m + 7))) ∧ IsReg _ (work' (CountLayout.binder (m + 7))) ∧
    (work' (RoutedNetworkParser.master (m + 9))).head = 1 ∧
    (work' (RoutedNetworkParser.master (m + 9))).read = Γ.ofBool (NetworkInputControl.accepted input) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 9) 0)) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 9) 1)) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 9) 2))
  rw [ho, hb, hm, hc 0, hc 1, hc 2]
  exact hp

def Buffers (m L : ℕ) (work : Fin (m + 15) → Tape) : Prop :=
  Reusable L (work (loNum m)) ∧ Reusable L (work (loDen m)) ∧
    Reusable L (work (hiNum m)) ∧ Reusable L (work (hiDen m))

theorem of_held (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape)
    (h : CurrentResources.Held m input work) : Buffers m input.length work := by
  rcases h with ⟨hn, ⟨a, p, ha, hp, har, hpr⟩, ⟨keep, hkeep, hk⟩⟩
  exact ⟨of_register (ArityValue.arity_bound input) hn, of_register ha har, of_register hp hpr, of_register hkeep hk⟩

def Ready (m : ℕ) (input : List Bool) (idx : ℕ) (R : (Fin (m + 15) → Tape) → Prop)
    (work : Fin (m + 15) → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
    IsReg idx (work (species (m + 1))) ∧ Buffers m input.length work ∧ CurrentPins.Kept m input work ∧ R work

theorem of_current (m : ℕ) (input : List Bool) (count idx n : ℕ)
    (R : (Fin (m + 15) → Tape) → Prop) (work : Fin (m + 15) → Tape)
    (h : CurrentReady.Ready m input.length count idx n
      (fun work => CurrentResources.State m input work ∧ R work) work) : Ready m input idx R work := by
  rcases h with ⟨hs, hz, _, hi, _, _, ⟨hp, hh⟩, hr⟩
  exact ⟨hs, hz, hi, of_held m input work hh, hp, hr⟩

end JointThermoComplexity.Complexity.BoxBufferPorts

#print axioms JointThermoComplexity.Complexity.BoxBufferPorts.metadata_frame
#print axioms JointThermoComplexity.Complexity.BoxBufferPorts.of_current
