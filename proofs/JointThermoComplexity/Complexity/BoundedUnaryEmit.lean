module
public import proofs.JointThermoComplexity.Complexity.BoundedUnaryLoop
public import proofs.JointThermoComplexity.Complexity.BinaryBufferReset
public import proofs.JointThermoComplexity.Complexity.RealSyntax

set_option autoImplicit false
@[expose] public section

/-! Emit a clipped unary dimension and clear the temporary binary index. -/

namespace JointThermoComplexity.Complexity.BoundedUnaryEmit
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BoundedUnaryUnit (Ports)
variable {w : ℕ}

def payload (d : Ports w) (word : List Bool) : TM w :=
  seqTM (BoundedUnaryLoop.machine d word) (BinaryBufferReset.machine d.idx)

def machine (d : Ports w) : TM w := seqTM (payload d [true]) (emitBitsTM [false])

def Pre (d : Ports w) (N L : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred w := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register 0 (work d.idx) ∧
    Register N (work d.value) ∧ (work d.flag).head = 1 ∧ IsReg L (work d.fuel) ∧ R work

def payloadBound (L B : ℕ) (word : List Bool) : ℕ := BoundedUnaryLoop.timeBound L B word + 48 * L + 10

def bound (L B : ℕ) : ℕ := payloadBound L B [true] + 2

theorem payload_hoareTime (d : Ports w) (word : List Bool) (N L B : ℕ) (hN : N.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : BoundedUnaryLoop.Stable d R) :
    (payload d word).HoareTime (Pre d N L before input emitted R)
      (Pre d N L before input (emitted ++ RepeatedOutput.copies word (min (16 * L) N)) R)
      (payloadBound L B word) := by
  let T : (Fin w → Tape) → Prop := fun work => Register N (work d.value) ∧
    (work d.flag).head = 1 ∧ IsReg L (work d.fuel) ∧ R work
  have hT : ∀ work next, (∀ j, j ≠ d.idx → next j = work j) → T work → T next := by
    rintro work next he ⟨hn, hh, hf, hr⟩
    exact ⟨by rw [he d.value d.idx_value.symm]; exact hn,
      by rw [he d.flag d.flag_idx]; exact hh, by rw [he d.fuel d.fuel_idx]; exact hf,
      hR work next (fun j hj _ _ _ => he j hj) hr⟩
  have hl := BoundedUnaryLoop.hoareTime d word N L B hN before input emitted R hR
  have hr := BinaryBufferReset.hoareTime d.idx (16 * L).bits before input
    (emitted ++ RepeatedOutput.copies word (min (16 * L) N)) T hT
  have hs := seqTM_hoareTime _ _ hl (by
    rintro inp work out ⟨⟨hc, hs, hi, hn, hh, hx⟩, hf⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨hc, hs, hi.1.2, hi.2, by rw [hi.1.1]; omega, hn, hh, hf, hx⟩) hr
  apply hs.consequence
  · rintro inp work out ⟨hc, hs, hi, hn, hh, hf, hr⟩
    exact ⟨⟨by simpa only [Nat.zero_min, RepeatedOutput.copies, List.append_nil] using hc, hs, hi, hn, hh, hr⟩, hf⟩
  · rintro inp work out ⟨hc, hs, hi, hn, hh, hf, hr⟩
    exact ⟨hc, hs, ⟨by simpa only [List.replicate_zero, Nat.zero_bits] using CountTape.string_of_register hi, hi.cell0⟩,
      hn, hh, hf, hr⟩
  · have hb := BoundedUnaryControl.bits_le (16 * L)
    unfold payloadBound
    omega

theorem hoareTime (d : Ports w) (N L B : ℕ) (hN : N.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : BoundedUnaryLoop.Stable d R) :
    (machine d).HoareTime (Pre d N L before input emitted R)
      (Pre d N L before input (emitted ++ RealSyntax.binderCode (min (16 * L) N)) R) (bound L B) := by
  have hp := payload_hoareTime d [true] N L B hN before input emitted R hR
  have hf := FixedOutput.hoareTime [false] before input
    (emitted ++ RepeatedOutput.copies [true] (min (16 * L) N))
    (fun work => Register 0 (work d.idx) ∧ Register N (work d.value) ∧ (work d.flag).head = 1 ∧
      IsReg L (work d.fuel) ∧ R work)
  have hs := seqTM_hoareTime _ _ hp (by
    rintro inp work out hh
    obtain ⟨hi, hw, ho⟩ := hh.1.phase
    rw [hi, hw, ho]
    exact hh) hf
  apply hs.consequence
  · exact fun _ _ _ hp => hp
  · intro inp work out hp
    simpa only [Pre, RealSyntax.binderCode, RepeatedOutput.copies_singleton, List.append_assoc] using hp
  · unfold bound
    simp only [List.length_cons, List.length_nil]
    omega

theorem exact_hoareTime (d : Ports w) (N L B : ℕ) (hN : N.bits.length ≤ B) (hNL : N ≤ 16 * L)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : BoundedUnaryLoop.Stable d R) :
    (machine d).HoareTime (Pre d N L before input emitted R)
      (Pre d N L before input (emitted ++ RealSyntax.binderCode N) R) (bound L B) := by
  simpa only [Nat.min_eq_right hNL] using hoareTime d N L B hN before input emitted R hR

theorem polynomial_bound (L B : ℕ) : bound L B = 1280 * L ^ 2 + (80 * B + 371) * L + 14 := by
  unfold bound payloadBound
  rw [BoundedUnaryLoop.polynomial_timeBound]
  simp only [List.length_cons, List.length_nil]
  ring1

end JointThermoComplexity.Complexity.BoundedUnaryEmit

#print axioms JointThermoComplexity.Complexity.BoundedUnaryEmit.exact_hoareTime
#print axioms JointThermoComplexity.Complexity.BoundedUnaryEmit.polynomial_bound
