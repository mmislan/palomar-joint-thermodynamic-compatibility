module
public import proofs.JointThermoComplexity.Complexity.MotifRecordSkip
public import proofs.JointThermoComplexity.Complexity.ReadOnlyFrame

set_option autoImplicit false
@[expose] public section

/-! A complete actual motif scan preserves every work tape and output under a displaced prefix-loop counter. -/

namespace JointThermoComplexity.Complexity.MotifRecordFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InvariantLoop

variable {w n r : ℕ}

theorem hoareTime (outer species reactions : Fin w) (hspecies : species ≠ outer) (hreactions : reactions ≠ outer)
    (v head : ℕ) (hh : 1 ≤ head) (a : NetworkData.Motif n r) (before tail emitted : List Bool)
    (R : (Fin w → Tape) → Tape → Prop) :
    (MotifRecordSkip.machine species reactions).HoareTime
      (Frame outer v head (fun inp work out => Cursor before ((DataCodec.motif n r).code a ++ tail) emitted inp work out ∧
        IsReg n (work species) ∧ IsReg r (work reactions) ∧ R work out))
      (Frame outer v head (fun inp work out => Cursor (before ++ (DataCodec.motif n r).code a) tail emitted inp work out ∧
        IsReg n (work species) ∧ IsReg r (work reactions) ∧ R work out)) (MotifRecordSkip.timeBound n r) := by
  let P : (Fin w → Tape) → Prop := fun work => IsReg n (work species) ∧ IsReg r (work reactions)
  have hP : ∀ work work', (∀ j, j ≠ outer → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hn, hr⟩
    exact ⟨by simpa only [hw species hspecies] using hn, by simpa only [hw reactions hreactions] using hr⟩
  have hc := ReadOnlyFrame.hoareTime (MotifRecordSkip.machine species reactions) outer v head hh
    ((DataCodec.motif n r).code a) before tail emitted P (MotifRecordSkip.timeBound n r) hP (by
      intro S
      simpa only [P, and_assoc] using MotifRecordSkip.hoareTime species reactions a before tail emitted S) R
  simpa only [P, and_assoc] using hc

end JointThermoComplexity.Complexity.MotifRecordFrame

#print axioms JointThermoComplexity.Complexity.MotifRecordFrame.hoareTime
