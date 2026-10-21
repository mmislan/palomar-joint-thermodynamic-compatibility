module
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceRuntime

set_option autoImplicit false
@[expose] public section

/-! The emitting scan preserves the retained sign flag as well as every other nonoperand work tape. -/

namespace JointThermoComplexity.Complexity.BinaryDifferenceEmit
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryDifferenceMachine BinaryDifferenceCursor BinaryDifferenceRuntime

variable {w : ℕ}

theorem hoareTime (left right flag : Fin w) (sep : Separate left right flag)
    (xs ys before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → work' j = work j) → R work → R work') :
    (machine left right flag true).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Start left right flag xs ys work ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (BinaryDifference.subtract xs ys false).1) inp work out ∧
        Finish left right flag true xs ys work ∧ R work) (max xs.length ys.length + 1) := by
  rintro inp work out ⟨hc, hp, hr⟩
  let c : Cfg w (Option Bool) := ⟨some false, inp, work, out⟩
  have hready : Ready left right flag [] [] xs ys emitted c :=
    ⟨⟨hp.lhs.2, hp.lhs.1, hp.lhsZero⟩, ⟨hp.rhs.2, hp.rhs.1, hp.rhsZero⟩,
      hp.safe, hp.flagHead, hc.input_read, hc.tapePrefix, hc.zero⟩
  obtain ⟨d, hd, hh, hres⟩ := BinaryDifferenceScan.run left right flag sep true false [] [] xs ys emitted c rfl hready
  have hf : d.work flag = work flag := by simpa only [↓reduceIte] using hres.flag_tape
  have hw : ∀ j, j ≠ left → j ≠ right → d.work j = work j := by
    intro j hl hr
    by_cases hj : j = flag
    · subst j; exact hf
    · exact hres.others j hl hr hj
  refine ⟨d, max xs.length ys.length + 1, le_rfl, hd, hh, ?_, ?_, hR work d.work hw hr⟩
  · exact ⟨by simpa only [hres.input_eq] using hc.cells,
      by simpa only [hres.input_eq] using hc.head,
      fun j => ⟨(hres.safe j).read_ne_start, (hres.safe j).1⟩,
      by simpa only [↓reduceIte] using hres.outputPrefix, hres.zero⟩
  · refine ⟨hres.safe, ?_, ?_, hres.leftDone.zero, hres.rightDone.zero, ?_, by simp⟩
    · exact ⟨by simpa using hres.leftDone.head,
        by simpa only [List.nil_append, List.append_nil, Tape.HasBinaryContent] using hres.leftDone.content⟩
    · exact ⟨by simpa using hres.rightDone.head,
        by simpa only [List.nil_append, List.append_nil, Tape.HasBinaryContent] using hres.rightDone.content⟩
    · rw [hf]; exact hp.flagHead

end JointThermoComplexity.Complexity.BinaryDifferenceEmit

#print axioms JointThermoComplexity.Complexity.BinaryDifferenceEmit.hoareTime
