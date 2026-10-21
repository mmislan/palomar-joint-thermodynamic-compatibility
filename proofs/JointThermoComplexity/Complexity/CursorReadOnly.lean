module
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Equal canonical output prefixes have identical output tapes, including the left marker. -/

namespace JointThermoComplexity.Complexity.CursorReadOnly
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

theorem output_eq {before remaining before' remaining' emitted : List Bool}
    {inp inp' out out' : Tape} {work work' : Fin w → Tape}
    (hc : Cursor before remaining emitted inp work out)
    (hc' : Cursor before' remaining' emitted inp' work' out') : out' = out := by
  apply Tape.ext
  · exact hc'.tapePrefix.1.trans hc.tapePrefix.1.symm
  · exact (hc'.tapePrefix.cells_eq_init hc'.zero).trans (hc.tapePrefix.cells_eq_init hc.zero).symm

theorem hoareTime (tm : TM w) (before remaining before' remaining' emitted : List Bool)
    (P : (Fin w → Tape) → Prop) (bound : ℕ)
    (hs : ∀ S : (Fin w → Tape) → Prop, tm.HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ P work ∧ S work)
      (fun inp work out => Cursor before' remaining' emitted inp work out ∧ P work ∧ S work) bound)
    (R : (Fin w → Tape) → Tape → Prop) :
    tm.HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ P work ∧ R work out)
      (fun inp work out => Cursor before' remaining' emitted inp work out ∧ P work ∧ R work out) bound := by
  rintro inp work out ⟨hc, hp, hr⟩
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdp, hdr⟩ := hs (fun work => R work out) inp work out ⟨hc, hp, hr⟩
  exact ⟨d, t, ht, hreach, hhalt, hdc, hdp, by simpa only [output_eq hc hdc] using hdr⟩

end JointThermoComplexity.Complexity.CursorReadOnly

#print axioms JointThermoComplexity.Complexity.CursorReadOnly.output_eq
#print axioms JointThermoComplexity.Complexity.CursorReadOnly.hoareTime
