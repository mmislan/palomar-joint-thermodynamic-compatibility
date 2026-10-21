module
public import proofs.JointThermoComplexity.Complexity.BinaryEqualityFlag

set_option autoImplicit false
@[expose] public section

/-! The existing equality machine retains every work tape except its result flag. -/

namespace JointThermoComplexity.Complexity.RetainedBinaryEquality
open _root_.Complexity _root_.Complexity.TM BinaryIncrementRun
open SmallCoefficientMatch (Ports)
variable {w : ℕ}

def Stable (p : Ports w) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ p.flag → next j = work j) → R work → R next

theorem hoareTime (p : Ports w) (n m B : ℕ) (hn : n.bits.length ≤ B) (hm : m.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (BinaryEqualityFlag.machine p).HoareTime (BinaryEqualityFlag.Pre p n m before input emitted R)
      (fun inp work out => BinaryEqualityFlag.Pre p n m before input emitted R inp work out ∧
        (work p.flag).read = Γ.ofBool (decide (n ≠ m))) (24 * B + 21) := by
  rintro inp work out ⟨hc, hs, hl, hr, hf, hx⟩
  let C : (Fin (w + 1) → Tape) → Prop := fun next => ∀ j, j ≠ p.constant → j ≠ p.flag → next j = work j
  have hC : SmallCoefficientMatch.Stable p C := by
    intro old next he ho j hj hf
    exact (he j hj hf).trans (ho j hj hf)
  obtain ⟨d, t, ht, hreach, hhalt, ⟨hdcur, hdsafe, hdl, hdr, hdh, hdC⟩, hdflag⟩ :=
    BinaryEqualityFlag.hoareTime p n m B hn hm before input emitted C hC
      inp work out ⟨hc, hs, hl, hr, hf, fun _ _ _ => rfl⟩
  have hsame : ∀ j, j ≠ p.flag → d.work j = work j := by
    intro j hj
    by_cases hc : j = p.constant
    · subst j
      exact SmallCoefficientMatch.binary_unique m.bits _ _ hdr.1 hr.1 hdr.2 hr.2
    · exact hdC j hc hj
  exact ⟨d, t, ht, hreach, hhalt, ⟨hdcur, hdsafe, hdl, hdr, hdh, hR work d.work hsame hx⟩, hdflag⟩

end JointThermoComplexity.Complexity.RetainedBinaryEquality

#print axioms JointThermoComplexity.Complexity.RetainedBinaryEquality.hoareTime
