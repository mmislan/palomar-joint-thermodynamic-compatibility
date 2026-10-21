module
public import proofs.JointThermoComplexity.Complexity.BoundedUnaryUnit

set_option autoImplicit false
@[expose] public section

/-! Pre-input static packets of bounded comparison/emission units. -/

namespace JointThermoComplexity.Complexity.BoundedUnaryPacket
open _root_.Complexity _root_.Complexity.TM HeaderAt
open BoundedUnaryUnit (Ports Inv)
variable {w : ℕ}

def machine (d : Ports w) (word : List Bool) : ℕ → TM w
  | 0 => emitBitsTM []
  | k + 1 => seqTM (machine d word k) (BoundedUnaryUnit.machine d word)

def bound (k C : ℕ) (word : List Bool) : ℕ := k * (BoundedUnaryUnit.bound C word + 1)

theorem hoareTime (d : Ports w) (word : List Bool) (k i N T B : ℕ) (hi : i + k ≤ T)
    (hN : N.bits.length ≤ B) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : BoundedUnaryUnit.Stable d R) :
    (machine d word k).HoareTime (Inv d N before input emitted word R i)
      (Inv d N before input emitted word R (i + k)) (bound k (T + B) word) := by
  induction k with
  | zero =>
    rintro inp work out hp
    exact ⟨⟨(machine d word 0).qhalt, inp, work, out⟩, 0, Nat.zero_le _, .zero, rfl, hp⟩
  | succ k ih =>
    have hp := ih (by omega)
    have hi' : (i + k).bits.length ≤ T + B :=
      (BoundedUnaryControl.bits_le _).trans (by omega)
    have hn' : N.bits.length ≤ T + B := hN.trans (by omega)
    have hu := BoundedUnaryUnit.hoareTime d word (i + k) N (T + B) hi' hn' before input emitted R hR
    have hs := seqTM_hoareTime _ _ hp (by
      rintro inp work out hh
      obtain ⟨hin, hw, ho⟩ := hh.1.phase
      rw [hin, hw, ho]
      exact hh) hu
    apply hs.consequence
    · exact fun _ _ _ hp => hp
    · intro inp work out hp
      simpa only [Nat.add_assoc] using hp
    · unfold bound
      rw [Nat.succ_mul]
      omega

end JointThermoComplexity.Complexity.BoundedUnaryPacket

#print axioms JointThermoComplexity.Complexity.BoundedUnaryPacket.machine
#print axioms JointThermoComplexity.Complexity.BoundedUnaryPacket.hoareTime
