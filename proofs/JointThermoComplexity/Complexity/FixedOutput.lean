module
public import proofs.JointThermoComplexity.Complexity.TapeSafety
public import proofs.Complexitylib.Models.TuringMachine.Registers.Emit

set_option autoImplicit false
@[expose] public section

/-! Fixed syntax words appended by the retained machine, with an exact cursor frame. -/

namespace JointThermoComplexity.Complexity.FixedOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

theorem outAcc_iff (bits : List Bool) (out : Tape) :
    OutAcc bits out ↔ out.HasBinaryPrefix bits ∧ out.cells 0 = Γ.start := by
  constructor
  · rintro ⟨hh, hz, hb, ht⟩
    refine ⟨⟨hh, hb, ?_⟩, hz⟩
    intro j hj
    exact ht (j + 1) (by omega)
  · rintro ⟨⟨hh, hb, ht⟩, hz⟩
    refine ⟨hh, hz, hb, ?_⟩
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact ht k (by omega)

theorem hoareTime (bits before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (emitBitsTM (n := w) bits).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ bits) inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      bits.length := by
  rintro inp work out ⟨hc, hs, hr⟩
  have hi : Parked inp := ⟨by rw [hc.head]; omega, fun j hj => by
    rw [hc.cells]
    exact Tape.init_ofBool_cells_ne_start _ j hj⟩
  obtain ⟨d, hreach, hhalt, hid, hwd, hod⟩ :=
    emitBitsTM_reachesIn_frame bits inp work out emitted hi hs ((outAcc_iff emitted out).mpr ⟨hc.tapePrefix, hc.zero⟩)
  have hout := (outAcc_iff (emitted ++ bits) d.output).mp hod
  refine ⟨d, bits.length, le_rfl, hreach, hhalt, ⟨?_, ?_, ?_, hout.1, hout.2⟩, ?_, ?_⟩
  · simpa only [hid] using hc.cells
  · simpa only [hid] using hc.head
  · simpa only [hwd] using hc.works
  · simpa only [hwd] using hs
  · simpa only [hwd] using hr

end JointThermoComplexity.Complexity.FixedOutput

#print axioms JointThermoComplexity.Complexity.FixedOutput.hoareTime
