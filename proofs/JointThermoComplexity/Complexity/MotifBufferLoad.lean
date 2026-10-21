module
public import proofs.JointThermoComplexity.Complexity.MotifBufferPorts

set_option autoImplicit false
@[expose] public section

/-! Bounded actual-bit loading preserves the complete ready state outside one selected motif buffer. -/

namespace JointThermoComplexity.Complexity.MotifBufferLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState MotifBufferPorts

def machine (m : ℕ) (k : Fin 3) (fuel : Fin (m + 15)) (hne : fuel ≠ buffer m k) : TM (m + 15) :=
  BooleanFieldAt.machine (buffer m k) fuel hne

theorem hoareTime (m L idx : ℕ) (k : Fin 3) (fuel : Fin (m + 15)) (hne : fuel ≠ buffer m k)
    (bits before tail emitted : List Bool) (hlen : bits.length ≤ L) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ buffer m k → work' j = work j) → R work → R work') :
    (machine m k fuel hne).HoareTime
      (fun inp work out => Cursor before (bits ++ tail) emitted inp work out ∧
        BoxState.Ready m L idx R work ∧ IsReg bits.length (work fuel))
      (fun inp work out => Cursor (before ++ bits) tail emitted inp work out ∧
        BoxState.Ready m L idx R work ∧ Stored bits (work (buffer m k))) (16 * L + 12) := by
  rintro inp work out ⟨hc, hp, hf⟩
  let S : (Fin (m + 15) → Tape) → Prop := fun work' => ∀ j, j ≠ buffer m k → work' j = work j
  have hS : ∀ work₁ work₂, (∀ j, j ≠ buffer m k → work₂ j = work₁ j) → S work₁ → S work₂ := by
    intro work₁ work₂ hw hs j hj
    exact (hw j hj).trans (hs j hj)
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hsafe, hstored, hreuse, _, hdw⟩ :=
    BooleanFieldAt.hoareTime (buffer m k) fuel hne L bits before tail emitted hlen S hS inp work out
      ⟨hc, hp.1, reusable m L idx k R work hp, hf, fun _ _ => rfl⟩
  exact ⟨d, t, ht, hreach, hhalt, hdc, frame_ready m L idx k R hR work d.work hdw hsafe hreuse hp, hstored⟩

end JointThermoComplexity.Complexity.MotifBufferLoad

#print axioms JointThermoComplexity.Complexity.MotifBufferLoad.hoareTime
