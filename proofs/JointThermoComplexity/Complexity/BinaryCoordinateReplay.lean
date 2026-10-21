module
public import proofs.JointThermoComplexity.Complexity.WorkSymbolBranch
public import proofs.JointThermoComplexity.Complexity.BinaryEmit
public import proofs.JointThermoComplexity.Complexity.FixedOutput

set_option autoImplicit false
@[expose] public section

/-! Emit paired coordinates directly from binary buffers, including even zero.
All work contents are retained; the bound is linear in the stored bit length.
-/

namespace JointThermoComplexity.Complexity.BinaryCoordinateReplay
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def pairedBits (odd : Bool) (bits : List Bool) : List Bool :=
  if odd then true :: bits else if bits = [] then [] else false :: bits

def pairedCode (odd : Bool) (bits : List Bool) : List Bool := BitCodec.encodeBits (pairedBits odd bits)

def prefixed (bits : List Bool) (idx : Fin w) : TM w := seqTM (emitBitsTM bits) (BinaryEmit.machine idx)

def machine (odd : Bool) (idx : Fin w) : TM w :=
  if odd then prefixed [true, true] idx
  else WorkSymbolBranch.machine Γ.blank idx (BinaryEmit.machine idx) (prefixed [true, false] idx)

theorem read_empty {t : Tape} (h : t.HasBinaryString []) : t.read = Γ.blank := by
  rw [Tape.read, h.1]
  exact h.2.2 0 (by decide)

theorem read_cons {t : Tape} {b : Bool} {bits : List Bool} (h : t.HasBinaryString (b :: bits)) :
    t.read ≠ Γ.blank := by
  rw [Tape.read, h.1, h.2.1 0 (by simp)]
  change Γ.ofBool b ≠ Γ.blank
  cases b <;> decide

theorem emit_hoareTime (idx : Fin w) (bits before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (BinaryEmit.machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ BitCodec.encodeBits bits) inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (3 * bits.length + 5) :=
  (BinaryEmit.hoareTime idx bits before input emitted (fun work => (∀ j, Parked (work j)) ∧ R work)).consequence
    (fun _ _ _ ⟨hc, hs, hb, hz, hr⟩ => ⟨hc, hb, hz, hs, hr⟩)
    (fun _ _ _ ⟨hc, hb, hz, hs, hr⟩ => ⟨hc, hs, hb, hz, hr⟩) le_rfl

theorem prefixed_hoareTime (prefixBits : List Bool) (idx : Fin w) (bits before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (prefixed prefixBits idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (prefixBits ++ BitCodec.encodeBits bits)) inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (3 * bits.length + prefixBits.length + 6) := by
  have hp := FixedOutput.hoareTime prefixBits before input emitted
    (fun work => (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
  have he := emit_hoareTime idx bits before input (emitted ++ prefixBits) R
  have h := seqTM_hoareTime (emitBitsTM prefixBits) (BinaryEmit.machine idx) hp (by
    rintro inp work out ⟨hc, hs, hb, hz, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hb, hz, hr⟩) he
  exact h.consequence (fun _ _ _ h => h)
    (fun _ _ _ h => by simpa only [List.append_assoc] using h) (by omega)

theorem hoareTime (odd : Bool) (idx : Fin w) (bits before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine odd idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ pairedCode odd bits) inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (3 * bits.length + 12) := by
  cases odd with
  | true =>
    have h := (prefixed_hoareTime [true, true] idx bits before input emitted R).mono_bound
      (by simp only [List.length_cons, List.length_nil]; omega : 3 * bits.length + [true, true].length + 6 ≤ 3 * bits.length + 12)
    simpa [machine, pairedCode, pairedBits, BitCodec.encodeBits, List.append_assoc] using h
  | false =>
    let P : (Fin w → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧
      (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work
    cases bits with
    | nil =>
      have h := WorkSymbolBranch.yes_hoareTime Γ.blank idx (BinaryEmit.machine idx) (prefixed [true, false] idx)
        before input emitted before input (emitted ++ BitCodec.encodeBits []) P P 5
        (emit_hoareTime idx [] before input emitted R)
      apply h.consequence
      · rintro inp work out hh
        exact ⟨hh, read_empty hh.2.2.1⟩
      · intro inp work out hh
        simpa [P, pairedCode, pairedBits] using hh
      · simp only [List.length_nil]; omega
    | cons b bits =>
      have h := WorkSymbolBranch.no_hoareTime Γ.blank idx (BinaryEmit.machine idx) (prefixed [true, false] idx)
        before input emitted before input (emitted ++ ([true, false] ++ BitCodec.encodeBits (b :: bits))) P P
        (3 * (b :: bits).length + [true, false].length + 6)
        (prefixed_hoareTime [true, false] idx (b :: bits) before input emitted R)
      apply h.consequence
      · rintro inp work out hh
        exact ⟨hh, read_cons hh.2.2.1⟩
      · intro inp work out hh
        simpa [P, pairedCode, pairedBits, BitCodec.encodeBits, List.append_assoc] using hh
      · simp only [List.length_cons, List.length_nil]; omega

theorem natural_code (odd : Bool) (v : ℕ) :
    pairedCode odd v.bits = BitCodec.naturalCode (2 * v + if odd then 1 else 0) := by
  cases odd with
  | true => simp [pairedCode, pairedBits, BitCodec.naturalCode, Nat.bit1_bits]
  | false =>
    by_cases hv : v = 0
    · subst v
      simp [pairedCode, pairedBits, BitCodec.naturalCode]
    · have hb : v.bits ≠ [] := by
        intro he
        have h := BitCodec.readBits_bits v
        rw [he] at h
        exact hv h.symm
      simp [pairedCode, pairedBits, hb, BitCodec.naturalCode, Nat.bit0_bits v hv]

theorem natural_hoareTime (odd : Bool) (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine odd idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryString v.bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ BitCodec.naturalCode (2 * v + if odd then 1 else 0)) inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString v.bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (3 * v.bits.length + 12) := by
  simpa only [natural_code] using hoareTime odd idx v.bits before input emitted R

end JointThermoComplexity.Complexity.BinaryCoordinateReplay

#print axioms JointThermoComplexity.Complexity.BinaryCoordinateReplay.hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryCoordinateReplay.natural_code
#print axioms JointThermoComplexity.Complexity.BinaryCoordinateReplay.natural_hoareTime
