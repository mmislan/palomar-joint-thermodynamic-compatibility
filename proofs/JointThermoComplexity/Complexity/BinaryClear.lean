module
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementRun
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Clear a completed binary scratch tape while preserving the surrounding cursor. -/

namespace JointThermoComplexity.Complexity.BinaryClear
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun

variable {w : ℕ}

theorem hoareTime (idx : Fin w) (bits : List Bool) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (clearWorkTM idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ Register 0 (work idx) ∧ R work)
      ((bits.length + 1) + 1 + (bits.length + 1 + 2)) := by
  let P : _root_.Complexity.TM.TapePred w := fun inp work out => Cursor before input emitted inp work out ∧ R work
  have hp : ∀ (inp : Tape) (work : Fin w → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin w → Tape) (out' : Tape),
      P inp work out → work' idx = (Tape.init []).move Dir3.right →
      inp' = inp → out' = out → (∀ j, j ≠ idx → work' j = work j) → P inp' work' out' := by
    rintro inp work out inp' work' out' ⟨hc, hr⟩ hblank hi ho hw
    refine ⟨⟨by simpa only [hi] using hc.cells, by simpa only [hi] using hc.head, ?_,
      by simpa only [ho] using hc.tapePrefix, by simpa only [ho] using hc.zero⟩,
      hR work work' hw hr⟩
    intro j
    by_cases hj : j = idx
    · subst j
      simp [hblank, Tape.move, Tape.init, Tape.read]
    · rw [hw j hj]
      exact hc.works j
  rintro inp work out ⟨hc, hb, hz, hr⟩
  obtain ⟨d, t, ht, hreach, hhalt, hblank, hpost⟩ :=
    clearWorkTM_hoareTime_frame_of_binaryString idx bits hp inp work out
      ⟨Tape.eq_init_move_right_of_hasBinaryString hb hz, hc.input_read, hc.output_read,
        by rw [hc.tapePrefix.1]; omega, (fun j _ => hc.works j), hc, hr⟩
  refine ⟨d, t, ht, hreach, hhalt, hpost.1, ?_, hpost.2⟩
  constructor
  · rw [hblank]
    change ((Tape.init []).move Dir3.right).HasBinaryString []
    simpa only [List.map_nil] using Tape.init_move_right_hasBinaryString ([] : List Bool)
  · simp [hblank, Tape.move, Tape.init]

theorem natural_hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (clearWorkTM idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Register v (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ Register 0 (work idx) ∧ R work)
      (2 * v.bits.length + 5) := by
  have ht : (v.bits.length + 1) + 1 + (v.bits.length + 1 + 2) = 2 * v.bits.length + 5 := by omega
  simpa only [ht, Register, and_assoc] using hoareTime idx v.bits before input emitted R hR

end JointThermoComplexity.Complexity.BinaryClear

#print axioms JointThermoComplexity.Complexity.BinaryClear.natural_hoareTime
