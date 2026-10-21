module
public import proofs.JointThermoComplexity.Complexity.OuterFuelBank
public import proofs.JointThermoComplexity.Complexity.UnaryCopy

set_option autoImplicit false
@[expose] public section

/-! Fixed copied species/core fuel at14/15 leaves the original count registers and production ports separate. -/

namespace JointThermoComplexity.Complexity.OuterFuelPorts
open _root_.Complexity
open _root_.Complexity.TM

def destination (m : ℕ) (k : Fin 2) : Fin (m + 22) := ⟨14 + k.val, by have hk := k.isLt; omega⟩
def sourceOld (m : ℕ) (k : Fin 2) : Fin (m + 21) := ⟨m + 17 + 2 * k.val, by have hk := k.isLt; omega⟩
def source (m : ℕ) (k : Fin 2) : Fin (m + 22) := (sourceOld m k).castSucc
def zeroOld (m : ℕ) : Fin (m + 21) := ⟨5, by omega⟩
def zero (m : ℕ) : Fin (m + 22) := (zeroOld m).castSucc

def permutation (m : ℕ) (k : Fin 2) : Fin (m + 22) ≃ Fin (m + 22) :=
  Equiv.swap (Fin.last (m + 21)) (destination m k)

theorem destination_route (m : ℕ) (k : Fin 2) : CountSumAt.destination (permutation m k) = destination m k :=
  Equiv.swap_apply_left _ _

theorem source_route (m : ℕ) (k : Fin 2) : permutation m k (sourceOld m k).castSucc = source m k := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro he; have hv := congrArg Fin.val he
    change m + 17 + 2 * k.val = m + 21 at hv
    have hk := k.isLt
    omega
  · intro he; have hv := congrArg Fin.val he
    change m + 17 + 2 * k.val = 14 + k.val at hv
    have hk := k.isLt
    omega

theorem zero_route (m : ℕ) (k : Fin 2) : permutation m k (zeroOld m).castSucc = zero m := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro he; have hv := congrArg Fin.val he; change (5 : ℕ) = m + 21 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change (5 : ℕ) = 14 + k.val at hv; omega

theorem zero_ne_destination (m : ℕ) (k : Fin 2) : zero m ≠ destination m k := by
  intro he; have hv := congrArg Fin.val he; change (5 : ℕ) = 14 + k.val at hv; omega

theorem destination_ne (m : ℕ) : destination m 0 ≠ destination m 1 := by
  intro he; have hv := congrArg Fin.val he; change (14 : ℕ) = 15 at hv; omega

theorem source_species (m : ℕ) : source m 0 = ProductionPorts.count (m + 2) := rfl
theorem source_core (m : ℕ) : source m 1 = RoutedNetworkParser.count (m + 16) 2 := rfl
theorem zero_scratch (m : ℕ) : zero m = PowerPorts.scratch (m + 9) := rfl

theorem initial (m : ℕ) (work : Fin (m + 22) → Tape) (h : OuterFuelBank.State m work) (k : Fin 2) :
    IsReg 0 (work (destination m k)) := by
  apply OuterFuelBank.outer_zero m work h
  change 14 + k.val = 14 ∨ 14 + k.val = 15
  have hk := k.isLt
  omega

end JointThermoComplexity.Complexity.OuterFuelPorts

#print axioms JointThermoComplexity.Complexity.OuterFuelPorts.source_route
#print axioms JointThermoComplexity.Complexity.OuterFuelPorts.initial
