module
public import proofs.JointThermoComplexity.Complexity.RationalFactorWords
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementFramed
public import proofs.JointThermoComplexity.Complexity.BinaryCoordinateReplay

set_option autoImplicit false
@[expose] public section

/-! Actual binary-TM emission of the two rational term factors. The left
routine increments its magnitude buffer; the right routine retains it.
All other work data and the input cursor survive in the stated frame. -/

namespace JointThermoComplexity.Complexity.RationalFactorEmission
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun RationalFactorWords
variable {w : ℕ}

abbrev Logical (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) := BinaryIncrementFramed.Logical idx v before input emitted R

def leftMachine (idx : Fin w) : TM w :=
  seqTM (BinaryIncrementMachine.machine idx) (BinaryCoordinateReplay.prefixed (BitCodec.naturalCode 1) idx)

def rightMachine (negative : Bool) (idx : Fin w) : TM w :=
  if negative then emitBitsTM (BitCodec.naturalCode 2 ++ BitCodec.naturalCode 1)
  else seqTM (emitBitsTM (BitCodec.naturalCode 2)) (BinaryCoordinateReplay.machine true idx)

def machine (right negative : Bool) (idx : Fin w) : TM w :=
  if right then rightMachine negative idx else leftMachine idx

def valueAfter (right : Bool) (v : ℕ) : ℕ := if right then v else v + 1

theorem literal_hoareTime (idx : Fin w) (v : ℕ) (bits before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (emitBitsTM bits).HoareTime (Logical idx v before input emitted R)
      (Logical idx v before input (emitted ++ bits) R) bits.length :=
  FixedOutput.hoareTime bits before input emitted (fun work => Register v (work idx) ∧ R work)

theorem prefix_hoareTime (idx : Fin w) (v : ℕ) (prefixBits before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (BinaryCoordinateReplay.prefixed prefixBits idx).HoareTime (Logical idx v before input emitted R)
      (Logical idx v before input (emitted ++ (prefixBits ++ BitCodec.naturalCode v)) R)
      (3 * v.bits.length + prefixBits.length + 6) := by
  have h := BinaryCoordinateReplay.prefixed_hoareTime prefixBits idx v.bits before input emitted R
  apply h.consequence
  · rintro inp work out ⟨hc, hs, hr, hx⟩
    exact ⟨hc, hs, hr.1, hr.2, hx⟩
  · rintro inp work out ⟨hc, hs, hb, hz, hx⟩
    exact ⟨hc, hs, ⟨hb, hz⟩, hx⟩
  · exact le_rfl

theorem paired_hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (BinaryCoordinateReplay.machine true idx).HoareTime (Logical idx v before input emitted R)
      (Logical idx v before input (emitted ++ BitCodec.naturalCode (2 * v + 1)) R)
      (3 * v.bits.length + 12) := by
  have h := BinaryCoordinateReplay.natural_hoareTime true idx v before input emitted R
  apply h.consequence
  · rintro inp work out ⟨hc, hs, hr, hx⟩
    exact ⟨hc, hs, hr.1, hr.2, hx⟩
  · rintro inp work out ⟨hc, hs, hb, hz, hx⟩
    exact ⟨hc, hs, ⟨hb, hz⟩, hx⟩
  · exact le_rfl

theorem left_hoareTime (negative : Bool) (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : BinaryIncrementFramed.Stable idx R) :
    (leftMachine idx).HoareTime (Logical idx v before input emitted R)
      (Logical idx (v + 1) before input (emitted ++ word false (coefficient negative v)) R)
      (5 * v.bits.length + 17) := by
  rw [left_word]
  have hi := BinaryIncrementFramed.hoareTime idx v before input emitted R hR
  have hp := prefix_hoareTime idx (v + 1) (BitCodec.naturalCode 1) before input emitted R
  have h := seqTM_hoareTime _ _ hi (by
    rintro inp work out hh
    obtain ⟨hin, hw, hout⟩ := hh.1.phase
    rw [hin, hw, hout]
    exact hh) hp
  apply h.mono_bound
  have hl := BinaryIncrementControl.length_increment v.bits
  rw [BinaryIncrementControl.increment_bits] at hl
  change 2 * v.bits.length + 4 + 1 + (3 * (v + 1).bits.length + 3 + 6) ≤ 5 * v.bits.length + 17
  omega

theorem right_hoareTime (negative : Bool) (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (rightMachine negative idx).HoareTime (Logical idx v before input emitted R)
      (Logical idx v before input (emitted ++ word true (coefficient negative v)) R)
      (3 * v.bits.length + 18) := by
  rw [right_word]
  cases negative
  · have hi := literal_hoareTime idx v (BitCodec.naturalCode 2) before input emitted R
    have hp := paired_hoareTime idx v before input (emitted ++ BitCodec.naturalCode 2) R
    have h := seqTM_hoareTime _ _ hi (by
      rintro inp work out hh
      obtain ⟨hin, hw, hout⟩ := hh.1.phase
      rw [hin, hw, hout]
      exact hh) hp
    apply h.consequence (fun _ _ _ hh => hh)
    · intro inp work out hh
      simpa [List.append_assoc] using hh
    · change 5 + 1 + (3 * v.bits.length + 12) ≤ 3 * v.bits.length + 18
      omega
  · have h := literal_hoareTime idx v (BitCodec.naturalCode 2 ++ BitCodec.naturalCode 1) before input emitted R
    exact h.mono_bound (by change 8 ≤ 3 * v.bits.length + 18; omega)

theorem hoareTime (right negative : Bool) (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : BinaryIncrementFramed.Stable idx R) :
    (machine right negative idx).HoareTime (Logical idx v before input emitted R)
      (Logical idx (valueAfter right v) before input (emitted ++ word right (coefficient negative v)) R)
      (5 * v.bits.length + 32) := by
  cases right
  · exact (left_hoareTime negative idx v before input emitted R hR).mono_bound (by omega)
  · exact (right_hoareTime negative idx v before input emitted R).mono_bound (by omega)

theorem bounded_hoareTime (right negative : Bool) (idx : Fin w) (v B : ℕ) (hB : v.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : BinaryIncrementFramed.Stable idx R) :
    (machine right negative idx).HoareTime (Logical idx v before input emitted R)
      (Logical idx (valueAfter right v) before input (emitted ++ word right (coefficient negative v)) R)
      (5 * B + 32) :=
  (hoareTime right negative idx v before input emitted R hR).mono_bound (by omega)

end JointThermoComplexity.Complexity.RationalFactorEmission

#print axioms JointThermoComplexity.Complexity.RationalFactorEmission.machine
#print axioms JointThermoComplexity.Complexity.RationalFactorEmission.left_hoareTime
#print axioms JointThermoComplexity.Complexity.RationalFactorEmission.right_hoareTime
#print axioms JointThermoComplexity.Complexity.RationalFactorEmission.hoareTime
#print axioms JointThermoComplexity.Complexity.RationalFactorEmission.bounded_hoareTime
