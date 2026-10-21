module
public import proofs.JointThermoComplexity.Complexity.BinarySignedRaw
public import proofs.JointThermoComplexity.Complexity.OutputRoute

set_option autoImplicit false
@[expose] public section

/-! Route signed arithmetic to one additional work buffer while preserving the real formula output. -/

namespace JointThermoComplexity.Complexity.BinarySignedBuffer
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryDifferenceCursor BinaryDifferenceRuntime SignedBinaryDifference

variable {w : ℕ}

def machine (left right flag : Fin w) : TM (w + 1) := (BinarySignedRaw.machine left right flag).retargetOutput

structure Buffered (left right flag : Fin w) (xs ys : List Bool) (work : Fin (w + 1) → Tape) : Prop where
  operands : Finish left right flag true xs ys (fun j => work j.castSucc)
  magnitude : (work (Fin.last w)).HasBinaryPrefix (BinaryMagnitudeSelect.rawMagnitude xs ys)
  zero : (work (Fin.last w)).cells 0 = Γ.start
  signValue : (work flag.castSucc).read = Γ.ofBool (negative xs ys)
  safe : ∀ j, Parked (work j)

theorem hoareTime (left right flag : Fin w) (sep : Separate left right flag)
    (xs ys before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ flag → work' j = work j) → R work → R work') :
    (machine left right flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        Start left right flag xs ys (fun j => work j.castSucc) ∧
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (fun j => work j.castSucc))
      (fun inp work out => Cursor before input emitted inp work out ∧ Buffered left right flag xs ys work ∧ R (fun j => work j.castSucc))
      (BinarySignedRaw.timeBound xs ys) := by
  have hbase := BinarySignedRaw.hoareTime left right flag sep xs ys before input [] R hR
  have hroute := OutputRoute.hoareTime (BinarySignedRaw.machine left right flag) _ _ _
    (fun out => out.HasBinaryPrefix emitted ∧ out.cells 0 = Γ.start) hbase
  exact hroute.consequence (by
    rintro inp work out ⟨hc, hp, hb, hz, hr⟩
    exact ⟨hc.output_read, ⟨hc.tapePrefix, hc.zero⟩,
      ⟨hc.cells, hc.head, fun j => ⟨(hp.safe j).read_ne_start, (hp.safe j).1⟩, hb, hz⟩, hp, hr⟩) (by
        rintro inp work out ⟨_, ⟨ho, hoz⟩, hc, hp, hf, hr⟩
        have hb : (work (Fin.last w)).HasBinaryPrefix (BinaryMagnitudeSelect.rawMagnitude xs ys) := by
          simpa only [List.nil_append] using hc.tapePrefix
        have hs : ∀ j, Parked (work j) := by
          intro j
          refine Fin.lastCases ?_ (fun k => hp.safe k) j
          exact ⟨by rw [hb.1]; omega, (show (work (Fin.last w)).HasBinaryContent _ from hb.2).cells_ne_start⟩
        exact ⟨⟨hc.cells, hc.head, fun j => ⟨(hs j).read_ne_start, (hs j).1⟩, ho, hoz⟩,
          ⟨hp, hb, hc.zero, hf, hs⟩, hr⟩) le_rfl

end JointThermoComplexity.Complexity.BinarySignedBuffer

#print axioms JointThermoComplexity.Complexity.BinarySignedBuffer.hoareTime
