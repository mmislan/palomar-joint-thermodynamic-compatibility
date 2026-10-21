module
public import proofs.JointThermoComplexity.Complexity.BoxFieldLoad
public import proofs.JointThermoComplexity.Complexity.DataCodec

set_option autoImplicit false
@[expose] public section

/-! Store one unreduced rational point's signed numerator and positive denominator. -/

namespace JointThermoComplexity.Complexity.BoxPointLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState NetworkData

variable {w : ℕ}

def code (q : RationalPoint) : List Bool :=
  BitCodec.integerCode q.numerator ++ BitCodec.naturalCode q.denominator

theorem code_eq (q : RationalPoint) : DataCodec.rational.code q = code q := rfl

def machine (num den : Fin (w + 1)) : TM (w + 1) :=
  seqTM (BoxFieldLoad.integerMachine num) (BoxFieldLoad.naturalMachine den)

theorem hoareTime (L : ℕ) (num den : Fin (w + 1)) (hne : num ≠ den) (q : RationalPoint)
    (hn : (BitCodec.integerCode q.numerator).length ≤ L) (hd : (BitCodec.naturalCode q.denominator).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ num → j ≠ den → work' j = work j) → R work → R work') :
    (machine num den).HoareTime
      (fun inp work out => Cursor before (code q ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Reusable L (work num) ∧ Reusable L (work den) ∧ R work)
      (fun inp work out => Cursor (before ++ code q) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Stored (BitCodec.integerCode q.numerator) (work num) ∧ Stored (BitCodec.naturalCode q.denominator) (work den) ∧
        Reusable L (work num) ∧ Reusable L (work den) ∧ R work) (26 * L + 26) := by
  let P : (Fin (w + 1) → Tape) → Prop := fun work => Reusable L (work den) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ num → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hd, hr⟩
    exact ⟨by simpa only [hw den hne.symm] using hd,
      hR work work' (fun j hj _ => hw j hj) hr⟩
  let S : (Fin (w + 1) → Tape) → Prop := fun work =>
    Stored (BitCodec.integerCode q.numerator) (work num) ∧ Reusable L (work num) ∧ R work
  have hS : ∀ work work', (∀ j, j ≠ den → work' j = work j) → S work → S work' := by
    rintro work work' hw ⟨hn, hrn, hr⟩
    exact ⟨by simpa only [hw num hne] using hn, by simpa only [hw num hne] using hrn,
      hR work work' (fun j _ hj => hw j hj) hr⟩
  have hi := BoxFieldLoad.integer_hoareTime L num q.numerator hn before
    (BitCodec.naturalCode q.denominator ++ tail) emitted P hP
  have hd' := BoxFieldLoad.natural_hoareTime L den q.denominator hd
    (before ++ BitCodec.integerCode q.numerator) tail emitted S hS
  have hs := seqTM_hoareTime (BoxFieldLoad.integerMachine num) (BoxFieldLoad.naturalMachine den) hi (by
    rintro inp work out ⟨hc, hsafe, hstored, hnum, hden, hr⟩
    obtain ⟨hip, hw, ho⟩ := hc.phase
    rw [hip, hw, ho]
    exact ⟨hc, hsafe, hden, hstored, hnum, hr⟩) hd'
  exact hs.consequence (by
    rintro inp work out ⟨hc, hsafe, hnum, hden, hr⟩
    exact ⟨by simpa only [code, List.append_assoc] using hc, hsafe, hnum, hden, hr⟩) (by
      rintro inp work out ⟨hc, hsafe, hd, hden, hn, hnum, hr⟩
      exact ⟨by simpa only [code, List.append_assoc] using hc, hsafe, hn, hd, hnum, hden, hr⟩) (by omega)

end JointThermoComplexity.Complexity.BoxPointLoad

#print axioms JointThermoComplexity.Complexity.BoxPointLoad.hoareTime
