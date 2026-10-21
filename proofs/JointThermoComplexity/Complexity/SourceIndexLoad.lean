module
public import proofs.JointThermoComplexity.Complexity.SourceIndexRange
public import proofs.JointThermoComplexity.Complexity.NaturalRawLoad

set_option autoImplicit false
@[expose] public section

/-! Actual source variable payload loading followed by a binary arity check.
This is the canonical-payload branch; malformed-field rejection is separate. -/

namespace JointThermoComplexity.Complexity.SourceIndexLoad
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
open BinaryDifferenceCursor BinaryDifferenceRuntime
variable {w : ℕ}

def machine (left right flag : Fin (w + 1)) : TM (w + 1) :=
  seqTM (NaturalRawLoad.machine left) (SourceIndexRange.machine left right flag)

theorem hoareTime (L : ℕ) (left right flag : Fin (w + 1)) (sep : Separate left right flag)
    (index arity : ℕ) (hi : (BitCodec.naturalCode index).length ≤ L) (ha : arity.bits.length ≤ L)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ flag → work' j = work j) → R work → R work') :
    (machine left right flag).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode index ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Reusable L (work left) ∧
        (work right).HasBinaryString arity.bits ∧ (work right).cells 0 = Γ.start ∧
        (work flag).head = 1 ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode index) tail emitted inp work out ∧
        Start left right flag index.bits arity.bits work ∧
        (work flag).read = Γ.ofBool (decide (index < arity)) ∧ Reusable L (work left) ∧ R work) (18 * L + 25) := by
  have hbits : index.bits.length ≤ L := by rw [BitCodec.naturalCode_length] at hi; omega
  let RP : (Fin (w + 1) → Tape) → Prop := fun work =>
    (work right).HasBinaryString arity.bits ∧ (work right).cells 0 = Γ.start ∧ (work flag).head = 1 ∧ R work
  have hRP : ∀ work work', (∀ j, j ≠ left → work' j = work j) → RP work → RP work' := by
    rintro work work' hw ⟨hb, hz, hf, hr⟩
    have heq := hw right sep.operands.symm
    have hflag := hw flag sep.flagLeft
    exact ⟨by simpa only [heq] using hb, by simpa only [heq] using hz,
      by simpa only [hflag] using hf, hR work work' (fun j hj _ _ => hw j hj) hr⟩
  have hl := NaturalRawLoad.hoareTime L left index hi before tail emitted RP hRP
  have hc := SourceIndexRange.hoareTime L left right flag sep index.bits arity hbits ha
    (before ++ BitCodec.naturalCode index) tail emitted R hR
  have hall := seqTM_hoareTime (NaturalRawLoad.machine left) (SourceIndexRange.machine left right flag) hl (by
    rintro inp work out ⟨hcur, hs, hb, hz, _hu, hdata⟩
    obtain ⟨hip, hwp, hop⟩ := hcur.phase
    rw [hip, hwp, hop]
    exact ⟨hcur, ⟨hs, hb, hdata.1, hz, hdata.2.1, hdata.2.2.1⟩, hdata.2.2.2⟩) hc
  exact hall.consequence (by
    rintro inp work out ⟨hcur, hs, hl, hr, hz, hf, hdata⟩
    exact ⟨hcur, hs, hl, hr, hz, hf, hdata⟩) (by
    rintro inp work out ⟨hcur, hs, hf, hdata⟩
    have hu : Reusable L (work left) :=
      ⟨index.bits, by omega, hs.lhs.2, hs.lhsZero, by rw [hs.lhs.1]; omega⟩
    exact ⟨hcur, hs, by simpa only [BitCodec.readBits_bits] using hf, hu, hdata⟩) (by omega)

end JointThermoComplexity.Complexity.SourceIndexLoad

#print axioms JointThermoComplexity.Complexity.SourceIndexLoad.hoareTime
