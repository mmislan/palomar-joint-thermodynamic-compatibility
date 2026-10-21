module
public import proofs.JointThermoComplexity.Complexity.BinaryScratchRestore

set_option autoImplicit false
@[expose] public section

/-! Actual retained binary-register copying with a reusable destination and cleared final scratch. -/

namespace JointThermoComplexity.Complexity.BinaryCopyRegister
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork cast_ne_last)
variable {w : ℕ}

def Empty (t : Tape) : Prop := t.HasBinaryPrefix [] ∧ t.cells 0 = Γ.start

def Stable (dst : Fin w) (R : (Fin w → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ dst → next j = work j) → R work → R next

def EmptyPre (src dst : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register v (work src.castSucc) ∧
    Empty (work dst.castSucc) ∧ Empty (work (Fin.last w)) ∧ R (oldWork work)

def Post (src dst : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register v (work src.castSucc) ∧
    Register v (work dst.castSucc) ∧ Empty (work (Fin.last w)) ∧ R (oldWork work)

def emptyMachine (src dst : Fin w) : TM (w + 1) :=
  seqTM (BinaryScaleBuffer.machine 1 src) (BinaryScratchRestore.machine dst)

theorem empty_hoareTime (src dst : Fin w) (hsep : src ≠ dst) (v : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : Stable dst R) :
    (emptyMachine src dst).HoareTime (EmptyPre src dst v before input emitted R)
      (Post src dst v before input emitted R) (9 * v.bits.length + 35) := by
  let S : (Fin w → Tape) → Prop := fun work => Empty (work dst) ∧ R work
  let Q : (Fin w → Tape) → Prop := fun work => Register v (work src) ∧ R work
  have hQ : Stable dst Q := by
    rintro work next he ⟨hv, hx⟩
    exact ⟨by rw [he src hsep]; exact hv, hR work next he hx⟩
  have hs := BinaryScaleBuffer.natural_hoareTime 1 src v before input emitted S
  have hr := BinaryScratchRestore.hoareTime dst v before input emitted Q hQ
  have hh := seqTM_hoareTime _ _ hs (by
    rintro inp work out ⟨hc, hs, hv, ht, hd, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hd.1, hd.2, by simpa only [Nat.one_mul] using ht, hv, hx⟩) hr
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hv, hd, ht, hx⟩
    exact ⟨hc, hs, hv, ht.1, ht.2, hd, hx⟩
  · rintro inp work out ⟨hc, hs, hd, ht, hz, hv, hx⟩
    exact ⟨hc, hs, hv, hd, ⟨ht, hz⟩, hx⟩
  · omega

def Pre (src dst : Fin w) (v u : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register v (work src.castSucc) ∧
    Register u (work dst.castSucc) ∧ Empty (work (Fin.last w)) ∧ R (oldWork work)

def machine (src dst : Fin w) : TM (w + 1) :=
  seqTM (BinaryBufferReset.machine dst.castSucc) (emptyMachine src dst)

theorem hoareTime (src dst : Fin w) (hsep : src ≠ dst) (v u : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : Stable dst R) :
    (machine src dst).HoareTime (Pre src dst v u before input emitted R)
      (Post src dst v before input emitted R) (3 * u.bits.length + 9 * v.bits.length + 45) := by
  let S : (Fin (w + 1) → Tape) → Prop := fun work => Register v (work src.castSucc) ∧
    Empty (work (Fin.last w)) ∧ R (oldWork work)
  have hS : ∀ work next, (∀ j, j ≠ dst.castSucc → next j = work j) → S work → S next := by
    rintro work next he ⟨hv, ht, hx⟩
    have hsd : src.castSucc ≠ dst.castSucc := by
      intro hh
      apply hsep
      exact Fin.ext (congrArg (fun j : Fin (w + 1) => j.val) hh)
    have hold : ∀ j, j ≠ dst → oldWork next j = oldWork work j := by
      intro j hj
      apply he j.castSucc
      intro hh
      exact hj (Fin.ext (congrArg (fun k : Fin (w + 1) => k.val) hh))
    exact ⟨by rw [he src.castSucc hsd]; exact hv,
      by rw [he (Fin.last w) (cast_ne_last dst).symm]; exact ht, hR _ _ hold hx⟩
  have hz := BinaryBufferReset.hoareTime dst.castSucc u.bits before input emitted S hS
  have hc := empty_hoareTime src dst hsep v before input emitted R hR
  have hh := seqTM_hoareTime _ _ hz (by
    rintro inp work out ⟨hc, hs, hd, hv, ht, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hv, ⟨CountTape.empty_prefix_of_zero hd, hd.cell0⟩, ht, hx⟩) hc
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hv, hd, ht, hx⟩
    exact ⟨hc, hs, hd.1.2, hd.2, by rw [hd.1.1]; omega, hv, ht, hx⟩
  · exact fun _ _ _ hp => hp
  · omega

theorem bounded_hoareTime (src dst : Fin w) (hsep : src ≠ dst) (v u B : ℕ)
    (hv : v.bits.length ≤ B) (hu : u.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : Stable dst R) :
    (machine src dst).HoareTime (Pre src dst v u before input emitted R)
      (Post src dst v before input emitted R) (12 * B + 45) :=
  (hoareTime src dst hsep v u before input emitted R hR).mono_bound (by omega)

end JointThermoComplexity.Complexity.BinaryCopyRegister

#print axioms JointThermoComplexity.Complexity.BinaryCopyRegister.empty_hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryCopyRegister.hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryCopyRegister.bounded_hoareTime
