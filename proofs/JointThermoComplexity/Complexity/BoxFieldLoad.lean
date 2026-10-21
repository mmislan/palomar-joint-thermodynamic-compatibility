module
public import proofs.JointThermoComplexity.Complexity.BoxBufferState
public import proofs.JointThermoComplexity.Complexity.BinaryBufferLoad

set_option autoImplicit false
@[expose] public section

/-! Load one actual rational field into a bounded reusable buffer at a fixed physical port. -/

namespace JointThermoComplexity.Complexity.BoxFieldLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState

variable {w : ℕ}

def permutation (idx : Fin (w + 1)) : Fin (w + 1) ≃ Fin (w + 1) := Equiv.swap (Fin.last w) idx

theorem destination (idx : Fin (w + 1)) : CountSumAt.destination (permutation idx) = idx :=
  Equiv.swap_apply_left _ _

def integerMachine (idx : Fin (w + 1)) : TM (w + 1) := BinaryBufferLoad.integerMachine (permutation idx)

def naturalMachine (idx : Fin (w + 1)) : TM (w + 1) := BinaryBufferLoad.naturalMachine (permutation idx)

theorem integer_hoareTime (L : ℕ) (idx : Fin (w + 1)) (value : ℤ)
    (hlen : (BitCodec.integerCode value).length ≤ L) (before tail emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (integerMachine idx).HoareTime
      (fun inp work out => Cursor before (BitCodec.integerCode value ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.integerCode value) tail emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Stored (BitCodec.integerCode value) (work idx) ∧
        Reusable L (work idx) ∧ R work) (13 * L + 13) := by
  rintro inp work out ⟨hc, hsafe, ⟨old, hold, hcontent, hz, hhead⟩, hr⟩
  have hs := BinaryBufferLoad.integer_hoareTime (permutation idx) old value before tail emitted R
    (by simpa only [destination] using hR)
  simp only [destination] at hs
  obtain ⟨d, t, ht, hreach, hhalt, hdcur, hdsafe, hdp, hdz, hdr⟩ :=
    hs inp work out ⟨hc, hsafe, hcontent, hz, hhead, hr⟩
  have hstored : Stored (BitCodec.integerCode value) (d.work idx) := ⟨hdp, hdz⟩
  exact ⟨d, t, by omega, hreach, hhalt, hdcur, hdsafe, hstored, hstored.reusable (by omega), hdr⟩

theorem natural_hoareTime (L : ℕ) (idx : Fin (w + 1)) (value : ℕ)
    (hlen : (BitCodec.naturalCode value).length ≤ L) (before tail emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (naturalMachine idx).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Stored (BitCodec.naturalCode value) (work idx) ∧
        Reusable L (work idx) ∧ R work) (13 * L + 12) := by
  rintro inp work out ⟨hc, hsafe, ⟨old, hold, hcontent, hz, hhead⟩, hr⟩
  have hs := BinaryBufferLoad.natural_hoareTime (permutation idx) old value before tail emitted R
    (by simpa only [destination] using hR)
  simp only [destination] at hs
  obtain ⟨d, t, ht, hreach, hhalt, hdcur, hdsafe, hdp, hdz, hdr⟩ :=
    hs inp work out ⟨hc, hsafe, hcontent, hz, hhead, hr⟩
  have hstored : Stored (BitCodec.naturalCode value) (d.work idx) := ⟨hdp, hdz⟩
  exact ⟨d, t, by omega, hreach, hhalt, hdcur, hdsafe, hstored, hstored.reusable (by omega), hdr⟩

end JointThermoComplexity.Complexity.BoxFieldLoad

#print axioms JointThermoComplexity.Complexity.BoxFieldLoad.integer_hoareTime
#print axioms JointThermoComplexity.Complexity.BoxFieldLoad.natural_hoareTime
