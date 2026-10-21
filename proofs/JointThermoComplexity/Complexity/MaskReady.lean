module
public import proofs.JointThermoComplexity.Complexity.MaskCodecBridge
public import proofs.JointThermoComplexity.Complexity.WriteStatus
public import proofs.Complexitylib.Models.TuringMachine.Hoare

set_option autoImplicit false
@[expose] public section

/-!
# Mask parsing with initialized local status

The local field status is initialized before the loop. Empty masks therefore
accept independently of the previous field's status. A distinct global validity
tape, supplied through the frame predicate, is preserved throughout this parser.
-/

namespace JointThermoComplexity.Complexity.MaskReady
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {n : ℕ}

def machine (r : Fin (n + 1)) : TM (n + 1) :=
  seqTM (WriteStatus.machine (NaturalMachine.flagIndex n) true) (BooleanMask.machine r)

theorem hoareTime (r : Fin (n + 1)) (hr : r ≠ NaturalMachine.flagIndex n)
    (v : ℕ) (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ r → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (machine r).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work (NaturalMachine.flagIndex n)).head = 1 ∧ IsReg v (work r) ∧ R work)
      (fun inp work out => IsReg v (work r) ∧ BooleanMask.StateInv before input emitted R v inp work out)
      (4 * v + 4) := by
  let RP : (Fin (n + 1) → Tape) → Prop := fun work => IsReg v (work r) ∧ R work
  have hRP : ∀ work work', (∀ j, j ≠ NaturalMachine.flagIndex n → work' j = work j) → RP work → RP work' := by
    rintro work work' h ⟨hreg, hr'⟩
    refine ⟨?_, hR work work' (fun j _ hj => h j hj) hr'⟩
    simpa only [h r hr] using hreg
  have hwrite := WriteStatus.hoareTime (NaturalMachine.flagIndex n) true before input emitted RP hRP
  have hmask := BooleanMask.hoareTime r hr v before input emitted R hR
  have hseq := seqTM_hoareTime (WriteStatus.machine (NaturalMachine.flagIndex n) true) (BooleanMask.machine r)
    hwrite (by
      rintro inp work out ⟨hc, hf, hv, hreg, hr'⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      refine ⟨hreg, ?_⟩
      simpa [BooleanMask.StateInv, BooleanVector.accepted] using
        (show Cursor before input emitted inp work out ∧ (work (NaturalMachine.flagIndex n)).head = 1 ∧
          (work (NaturalMachine.flagIndex n)).read = Γ.ofBool true ∧ R work from ⟨hc, hf, hv, hr'⟩)) hmask
  apply HoareTime.mono_bound (b := 1 + 1 + (4 * v + 2)) hseq
  omega

end JointThermoComplexity.Complexity.MaskReady

#print axioms JointThermoComplexity.Complexity.MaskReady.hoareTime
