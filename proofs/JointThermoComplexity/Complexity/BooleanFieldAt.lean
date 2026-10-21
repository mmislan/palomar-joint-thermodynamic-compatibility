module
public import proofs.JointThermoComplexity.Complexity.BooleanFieldLoad
public import proofs.JointThermoComplexity.Complexity.BoxFieldLoad

set_option autoImplicit false
@[expose] public section

/-! Expose bounded Boolean loading at independent fixed physical buffer and fuel ports. -/

namespace JointThermoComplexity.Complexity.BooleanFieldAt
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState BoxFieldLoad

variable {w : ℕ}

def virtualFuel (idx fuel : Fin (w + 1)) (hne : fuel ≠ idx) : Fin w :=
  ⟨((permutation idx).symm fuel).val, by
    have hlast : (permutation idx).symm fuel ≠ Fin.last w := by
      intro he
      apply hne
      calc fuel = permutation idx ((permutation idx).symm fuel) := ((permutation idx).apply_symm_apply fuel).symm
           _ = idx := by rw [he]; exact destination idx
    have hv := ((permutation idx).symm fuel).isLt
    have hvne : ((permutation idx).symm fuel).val ≠ w := by
      intro he
      apply hlast
      exact Fin.ext he
    omega⟩

theorem physical_fuel (idx fuel : Fin (w + 1)) (hne : fuel ≠ idx) :
    BooleanBufferAt.fuel (permutation idx) (virtualFuel idx fuel hne) = fuel := by
  have he : (virtualFuel idx fuel hne).castSucc = (permutation idx).symm fuel := rfl
  change permutation idx (virtualFuel idx fuel hne).castSucc = fuel
  rw [he]
  exact (permutation idx).apply_symm_apply fuel

def machine (idx fuel : Fin (w + 1)) (hne : fuel ≠ idx) : TM (w + 1) :=
  BooleanFieldLoad.machine (permutation idx) (virtualFuel idx fuel hne)

theorem hoareTime (idx fuel : Fin (w + 1)) (hne : fuel ≠ idx) (L : ℕ)
    (bits before tail emitted : List Bool) (hlen : bits.length ≤ L) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx fuel hne).HoareTime
      (fun inp work out => Cursor before (bits ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Reusable L (work idx) ∧ IsReg bits.length (work fuel) ∧ R work)
      (fun inp work out => Cursor (before ++ bits) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Stored bits (work idx) ∧ Reusable L (work idx) ∧ IsReg bits.length (work fuel) ∧ R work) (16 * L + 12) := by
  have hs := BooleanFieldLoad.hoareTime (permutation idx) (virtualFuel idx fuel hne) L bits before tail emitted hlen R
    (by simpa only [destination] using hR)
  simpa only [machine, destination, physical_fuel] using hs

end JointThermoComplexity.Complexity.BooleanFieldAt

#print axioms JointThermoComplexity.Complexity.BooleanFieldAt.physical_fuel
#print axioms JointThermoComplexity.Complexity.BooleanFieldAt.hoareTime
