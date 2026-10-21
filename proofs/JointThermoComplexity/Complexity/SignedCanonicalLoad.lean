module
public import proofs.JointThermoComplexity.Complexity.SignedRawControl

set_option autoImplicit false
@[expose] public section

/-! A total signed binary loader with a linear all-input runtime. Sign and
availability use distinct flags; every magnitude is canonical after loading. -/

namespace JointThermoComplexity.Complexity.SignedCanonicalLoad
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
variable {w : ℕ}

def machine (idx sign flag : Fin (w + 1)) : TM (w + 1) :=
  seqTM (SourceBitRead.machine sign flag) (NaturalCanonicalLoad.machine idx)

theorem hoareTime (L : ℕ) (idx sign flag : Fin (w + 1))
    (his : idx ≠ sign) (hif : idx ≠ flag) (hsf : sign ≠ flag)
    (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ idx → j ≠ sign → j ≠ flag → next j = work j) → R work → R next) :
    (machine idx sign flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Reusable L (work idx) ∧ (work sign).head = 1 ∧ (work flag).head = 1 ∧ R work)
      (fun inp work out => Cursor (before ++ SignedRawControl.taken input) (SignedRawControl.rest input) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register (SignedRawControl.magnitude input) (work idx) ∧
        Reusable L (work idx) ∧ (work sign).head = 1 ∧ (work flag).head = 1 ∧
        (work sign).read = Γ.ofBool (SignedRawControl.negative input) ∧
        (work flag).read = Γ.ofBool (BooleanMachine.accepted input) ∧ R work)
      (15 * L + 20) := by
  let S : (Fin (w + 1) → Tape) → Prop := fun work => Reusable L (work idx) ∧ R work
  have hs := SourceBitRead.hoareTime sign flag hsf before input emitted S (by
    rintro work next hsame ⟨hb, hr⟩
    exact ⟨by rw [hsame idx his hif]; exact hb,
      hR work next (fun j _ hjs hjf => hsame j hjs hjf) hr⟩)
  let T : (Fin (w + 1) → Tape) → Prop := fun work =>
    (work sign).head = 1 ∧ (work flag).head = 1 ∧
    (work sign).read = Γ.ofBool (SourceBitRead.value input) ∧
    (work flag).read = Γ.ofBool (BooleanMachine.accepted input) ∧ R work
  have hn := NaturalCanonicalLoad.hoareTime L idx (before ++ BooleanMachine.copied input)
    (BooleanMachine.suffix input) emitted ((SignedRawControl.suffix_length input).trans hlen) T (by
      rintro work next hsame ⟨hsh, hfh, hsr, hfr, hr⟩
      exact ⟨by rw [hsame sign his.symm]; exact hsh,
        by rw [hsame flag hif.symm]; exact hfh,
        by rw [hsame sign his.symm]; exact hsr,
        by rw [hsame flag hif.symm]; exact hfr,
        hR work next (fun j hji _ _ => hsame j hji) hr⟩)
  have hfull := seqTM_hoareTime _ _ hs (by
    rintro inp work out ⟨hc, hsafe, hsh, hfh, hsr, hfr, hb, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hsafe, hb, hsh, hfh, hsr, hfr, hr⟩) hn
  apply hfull.consequence
  · rintro inp work out ⟨hc, hsafe, hb, hsh, hfh, hr⟩
    exact ⟨hc, hsafe, hsh, hfh, hb, hr⟩
  · rintro inp work out ⟨hc, hsafe, hb, hreuse, hsh, hfh, hsr, hfr, hr⟩
    exact ⟨by simpa only [SignedRawControl.taken, SignedRawControl.rest, List.append_assoc] using hc,
      hsafe, hb, hreuse, hsh, hfh, hsr, hfr, hr⟩
  · omega

theorem integer_hoareTime (L : ℕ) (idx sign flag : Fin (w + 1))
    (his : idx ≠ sign) (hif : idx ≠ flag) (hsf : sign ≠ flag)
    (c : ℤ) (before suffix emitted : List Bool)
    (hlen : (BitCodec.integerCode c ++ suffix).length ≤ L)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ idx → j ≠ sign → j ≠ flag → next j = work j) → R work → R next) :
    (machine idx sign flag).HoareTime
      (fun inp work out => Cursor before (BitCodec.integerCode c ++ suffix) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧
        (work sign).head = 1 ∧ (work flag).head = 1 ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.integerCode c) suffix emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register c.natAbs (work idx) ∧
        Reusable L (work idx) ∧ (work sign).head = 1 ∧ (work flag).head = 1 ∧
        (work sign).read = Γ.ofBool (decide (c < 0)) ∧ (work flag).read = Γ.one ∧ R work)
      (15 * L + 20) := by
  simpa only [SignedRawControl.taken_integer, SignedRawControl.rest_integer,
    SignedRawControl.magnitude_integer, SignedRawControl.negative_integer,
    SignedRawControl.available_integer, Γ.ofBool] using
    hoareTime L idx sign flag his hif hsf before (BitCodec.integerCode c ++ suffix) emitted hlen R hR

end JointThermoComplexity.Complexity.SignedCanonicalLoad

#print axioms JointThermoComplexity.Complexity.SignedCanonicalLoad.machine
#print axioms JointThermoComplexity.Complexity.SignedCanonicalLoad.hoareTime
#print axioms JointThermoComplexity.Complexity.SignedCanonicalLoad.integer_hoareTime
