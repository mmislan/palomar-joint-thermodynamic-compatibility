module
public import proofs.JointThermoComplexity.Complexity.GateStore

set_option autoImplicit false
@[expose] public section

/-! A reusable post-emission step stores the old target address and advances it. -/

namespace JointThermoComplexity.Complexity.StoreNext
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun

variable {w : ℕ}

def machine (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w) : TM (w + 1) :=
  seqTM (UnaryCopy.machine e source zero) (UnarySuccessor.machine (GateStore.next e source))

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w)
    (hne : GateStore.next e source ≠ GateStore.scratch e zero) (old value : ℕ)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ GateStore.next e source → j ≠ CountSumAt.destination e →
      work' j = work j) → R work → R work') :
    (machine e source zero).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work (GateStore.scratch e zero)) ∧ IsReg value (work (GateStore.next e source)) ∧
        IsReg old (work (CountSumAt.destination e)) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work (GateStore.scratch e zero)) ∧ IsReg (value + 1) (work (GateStore.next e source)) ∧
        IsReg value (work (CountSumAt.destination e)) ∧ R work) (2 * old + 7 * value + 22) := by
  let P : (Fin (w + 1) → Tape) → Prop := fun work => Register 0 (work (GateStore.scratch e zero)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hz, hr⟩
    exact ⟨by simpa only [GateStore.scratch, hw _ (UnaryCopy.source_ne_destination e zero)] using hz,
      hR work work' (fun j _ hj => hw j hj) hr⟩
  let S : (Fin (w + 1) → Tape) → Prop := fun work => Register 0 (work (GateStore.scratch e zero)) ∧
    IsReg value (work (CountSumAt.destination e)) ∧ R work
  have hS : ∀ work work', (∀ j, j ≠ GateStore.next e source → work' j = work j) → S work → S work' := by
    rintro work work' hw ⟨hz, hd, hr⟩
    exact ⟨by simpa only [hw _ hne.symm] using hz,
      by simpa only [GateStore.next, hw _ (UnaryCopy.source_ne_destination e source).symm] using hd,
      hR work work' (fun j hj _ => hw j hj) hr⟩
  have hcopy := UnaryCopy.hoareTime e source zero old value before input emitted P hP
  have hnext := UnarySuccessor.hoareTime (GateStore.next e source) value before input emitted S hS
  have hseq := seqTM_hoareTime (UnaryCopy.machine e source zero)
    (UnarySuccessor.machine (GateStore.next e source)) hcopy (by
      rintro inp work out ⟨hc, hs, hd, hn, _, hz, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, hn, hz, hd, hr⟩) hnext
  exact hseq.consequence (by
    rintro inp work out ⟨hc, hs, hz, hn, hd, hr⟩
    have hz' : IsReg 0 (work (GateStore.scratch e zero)) :=
      CountTape.register_of_string (by simpa only [Nat.zero_bits, List.replicate_zero] using hz.1) hz.2
    exact ⟨hc, hs, hd, hn, hz', hz, hr⟩)
    (fun _ _ _ ⟨hc, hs, hn, hz, hd, hr⟩ => ⟨hc, hs, hz, hn, hd, hr⟩) (by omega)

end JointThermoComplexity.Complexity.StoreNext

#print axioms JointThermoComplexity.Complexity.StoreNext.hoareTime
