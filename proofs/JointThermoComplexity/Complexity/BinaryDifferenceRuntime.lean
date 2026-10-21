module
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceScan

set_option autoImplicit false
@[expose] public section

/-! Compositional linear-time subtraction and comparison from real raw binary work tapes. -/

namespace JointThermoComplexity.Complexity.BinaryDifferenceRuntime
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryDifferenceMachine BinaryDifferenceCursor BinaryDifferenceResult

variable {w : ℕ}

structure Start (left right flag : Fin w) (xs ys : List Bool) (work : Fin w → Tape) : Prop where
  safe : ∀ j, Parked (work j)
  lhs : (work left).HasBinaryString xs
  rhs : (work right).HasBinaryString ys
  lhsZero : (work left).cells 0 = Γ.start
  rhsZero : (work right).cells 0 = Γ.start
  flagHead : (work flag).head = 1

structure Finish (left right flag : Fin w) (emit : Bool) (xs ys : List Bool) (work : Fin w → Tape) : Prop where
  safe : ∀ j, Parked (work j)
  lhs : (work left).HasBinaryPrefix xs
  rhs : (work right).HasBinaryPrefix ys
  lhsZero : (work left).cells 0 = Γ.start
  rhsZero : (work right).cells 0 = Γ.start
  flagHead : (work flag).head = 1
  flagValue : emit = false → (work flag).read = Γ.ofBool (BinaryDifference.subtract xs ys false).2

theorem hoareTime (left right flag : Fin w) (sep : Separate left right flag) (emit : Bool)
    (xs ys before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ flag → work' j = work j) → R work → R work') :
    (machine left right flag emit).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Start left right flag xs ys work ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (if emit then (BinaryDifference.subtract xs ys false).1 else [])) inp work out ∧
        Finish left right flag emit xs ys work ∧ R work) (max xs.length ys.length + 1) := by
  rintro inp work out ⟨hc, hp, hr⟩
  let c : Cfg w (Option Bool) := ⟨some false, inp, work, out⟩
  have hready : Ready left right flag [] [] xs ys emitted c :=
    ⟨⟨hp.lhs.2, hp.lhs.1, hp.lhsZero⟩, ⟨hp.rhs.2, hp.rhs.1, hp.rhsZero⟩,
      hp.safe, hp.flagHead, hc.input_read, hc.tapePrefix, hc.zero⟩
  obtain ⟨d, hd, hh, hres⟩ := BinaryDifferenceScan.run left right flag sep emit false [] [] xs ys emitted c rfl hready
  have hl : (d.work left).HasBinaryPrefix xs :=
    ⟨by simpa using hres.leftDone.head,
      by simpa only [List.nil_append, List.append_nil, Tape.HasBinaryContent] using hres.leftDone.content⟩
  have hright : (d.work right).HasBinaryPrefix ys :=
    ⟨by simpa using hres.rightDone.head,
      by simpa only [List.nil_append, List.append_nil, Tape.HasBinaryContent] using hres.rightDone.content⟩
  have hflag : (d.work flag).head = 1 := by
    rw [hres.flag_tape]
    cases emit <;> simp [c, hp.flagHead, Tape.write_head]
  have hvalue : emit = false → (d.work flag).read = Γ.ofBool (BinaryDifference.subtract xs ys false).2 := by
    intro he
    subst emit
    rw [hres.flag_tape]
    simp [Tape.read, Tape.write, c, hp.flagHead]
  refine ⟨d, max xs.length ys.length + 1, le_rfl, hd, hh, ?_, ?_, hR work d.work hres.others hr⟩
  · exact ⟨by simpa only [hres.input_eq] using hc.cells,
      by simpa only [hres.input_eq] using hc.head,
      fun j => ⟨(hres.safe j).read_ne_start, (hres.safe j).1⟩, hres.outputPrefix, hres.zero⟩
  · exact ⟨hres.safe, hl, hright, hres.leftDone.zero, hres.rightDone.zero, hflag, hvalue⟩

end JointThermoComplexity.Complexity.BinaryDifferenceRuntime

#print axioms JointThermoComplexity.Complexity.BinaryDifferenceRuntime.hoareTime
