module
public import proofs.JointThermoComplexity.Complexity.NaturalScanBuffer
public import proofs.JointThermoComplexity.Complexity.SourceIndexLoad

set_option autoImplicit false
@[expose] public section

/-! Replay an already validated source index from a work buffer, preserving the source input. -/

namespace JointThermoComplexity.Complexity.SourceIndexReplay
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
open BinaryDifferenceCursor BinaryDifferenceRuntime
variable {n : ℕ}

def machine (left right flag : Fin (n + 1)) : TM (n + 2) :=
  (SourceIndexLoad.machine left right flag).retargetInput

theorem hoareTime (L : ℕ) (left right flag : Fin (n + 1)) (sep : Separate left right flag)
    (index arity : ℕ) (hi : (BitCodec.naturalCode index).length ≤ L) (ha : arity.bits.length ≤ L)
    (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ flag → work' j = work j) → R work → R work') :
    (machine left right flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ j, (work j).cells 0 = Γ.start) ∧
        (work (Fin.last (n + 1))).HasBinaryString (BitCodec.naturalCode index) ∧
        Reusable L (work left.castSucc) ∧
        (work right.castSucc).HasBinaryString arity.bits ∧ (work right.castSucc).cells 0 = Γ.start ∧
        (work flag.castSucc).head = 1 ∧ R (fun j => work j.castSucc))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ j, (work j).cells 0 = Γ.start) ∧
        (work (Fin.last (n + 1))).HasBinaryContent (BitCodec.naturalCode index) ∧
        (work (Fin.last (n + 1))).head = (BitCodec.naturalCode index).length + 1 ∧
        Start left right flag index.bits arity.bits (fun j => work j.castSucc) ∧
        (work flag.castSucc).read = Γ.ofBool (decide (index < arity)) ∧
        Reusable L (work left.castSucc) ∧ R (fun j => work j.castSucc)) (18 * L + 25) := by
  let P : (Fin (n + 1) → Tape) → Prop := fun work => Reusable L (work left) ∧
    (work right).HasBinaryString arity.bits ∧ (work right).cells 0 = Γ.start ∧ (work flag).head = 1 ∧ R work
  let Q : (Fin (n + 1) → Tape) → Prop := fun work => Start left right flag index.bits arity.bits work ∧
    (work flag).read = Γ.ofBool (decide (index < arity)) ∧ Reusable L (work left) ∧ R work
  have hload := SourceIndexLoad.hoareTime L left right flag sep index arity hi ha [] [] emitted R hR
  have hbase : (SourceIndexLoad.machine left right flag).HoareTime
      (fun inp work out => Cursor [] (BitCodec.naturalCode index) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ P work)
      (fun inp work out => Cursor (BitCodec.naturalCode index) [] emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Q work) (18 * L + 25) :=
    hload.consequence (by
      rintro inp work out ⟨hc, hs, hp⟩
      exact ⟨by simpa only [List.append_nil] using hc, hs, hp⟩) (by
      rintro inp work out ⟨hc, hs, hf, hu, hr⟩
      exact ⟨by simpa only [List.nil_append] using hc, hs.safe, hs, hf, hu, hr⟩) le_rfl
  exact VirtualCursor.hoareTime (SourceIndexLoad.machine left right flag)
    (BitCodec.naturalCode index) (BitCodec.naturalCode index) [] emitted emitted before input
    (List.append_nil _) P Q (18 * L + 25) hbase

end JointThermoComplexity.Complexity.SourceIndexReplay

#print axioms JointThermoComplexity.Complexity.SourceIndexReplay.hoareTime
