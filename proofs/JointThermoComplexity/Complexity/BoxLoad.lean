module
public import proofs.JointThermoComplexity.Complexity.BoxPointLoad

set_option autoImplicit false
@[expose] public section

/-! Store the four literal fields of one rational box, with bounded reusable state for every later box. -/

namespace JointThermoComplexity.Complexity.BoxLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState NetworkData

variable {w : ℕ}

structure Separate (loNum loDen hiNum hiDen : Fin (w + 1)) : Prop where
  lo : loNum ≠ loDen
  ln_hn : loNum ≠ hiNum
  ln_hd : loNum ≠ hiDen
  ld_hn : loDen ≠ hiNum
  ld_hd : loDen ≠ hiDen
  hi : hiNum ≠ hiDen

def code (b : ClosedBox) : List Bool := BoxPointLoad.code b.lower ++ BoxPointLoad.code b.upper

theorem code_eq (b : ClosedBox) : DataCodec.box.code b = code b := rfl

def machine (loNum loDen hiNum hiDen : Fin (w + 1)) : TM (w + 1) :=
  seqTM (BoxPointLoad.machine loNum loDen) (BoxPointLoad.machine hiNum hiDen)

theorem hoareTime (L : ℕ) (loNum loDen hiNum hiDen : Fin (w + 1))
    (sep : Separate loNum loDen hiNum hiDen) (b : ClosedBox)
    (hln : (BitCodec.integerCode b.lower.numerator).length ≤ L)
    (hld : (BitCodec.naturalCode b.lower.denominator).length ≤ L)
    (hhn : (BitCodec.integerCode b.upper.numerator).length ≤ L)
    (hhd : (BitCodec.naturalCode b.upper.denominator).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work',
      (∀ j, j ≠ loNum → j ≠ loDen → j ≠ hiNum → j ≠ hiDen → work' j = work j) → R work → R work') :
    (machine loNum loDen hiNum hiDen).HoareTime
      (fun inp work out => Cursor before (code b ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Reusable L (work loNum) ∧ Reusable L (work loDen) ∧
        Reusable L (work hiNum) ∧ Reusable L (work hiDen) ∧ R work)
      (fun inp work out => Cursor (before ++ code b) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Stored (BitCodec.integerCode b.lower.numerator) (work loNum) ∧
        Stored (BitCodec.naturalCode b.lower.denominator) (work loDen) ∧
        Stored (BitCodec.integerCode b.upper.numerator) (work hiNum) ∧
        Stored (BitCodec.naturalCode b.upper.denominator) (work hiDen) ∧
        Reusable L (work loNum) ∧ Reusable L (work loDen) ∧
        Reusable L (work hiNum) ∧ Reusable L (work hiDen) ∧ R work) (52 * L + 53) := by
  let P : (Fin (w + 1) → Tape) → Prop := fun work =>
    Reusable L (work hiNum) ∧ Reusable L (work hiDen) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ loNum → j ≠ loDen → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hn, hd, hr⟩
    exact ⟨by simpa only [hw hiNum sep.ln_hn.symm sep.ld_hn.symm] using hn,
      by simpa only [hw hiDen sep.ln_hd.symm sep.ld_hd.symm] using hd,
      hR work work' (fun j hj hk _ _ => hw j hj hk) hr⟩
  let S : (Fin (w + 1) → Tape) → Prop := fun work =>
    Stored (BitCodec.integerCode b.lower.numerator) (work loNum) ∧
    Stored (BitCodec.naturalCode b.lower.denominator) (work loDen) ∧
    Reusable L (work loNum) ∧ Reusable L (work loDen) ∧ R work
  have hS : ∀ work work', (∀ j, j ≠ hiNum → j ≠ hiDen → work' j = work j) → S work → S work' := by
    rintro work work' hw ⟨hn, hd, hrn, hrd, hr⟩
    exact ⟨by simpa only [hw loNum sep.ln_hn sep.ln_hd] using hn,
      by simpa only [hw loDen sep.ld_hn sep.ld_hd] using hd,
      by simpa only [hw loNum sep.ln_hn sep.ln_hd] using hrn,
      by simpa only [hw loDen sep.ld_hn sep.ld_hd] using hrd,
      hR work work' (fun j _ _ hj hk => hw j hj hk) hr⟩
  have hl := BoxPointLoad.hoareTime L loNum loDen sep.lo b.lower hln hld before
    (BoxPointLoad.code b.upper ++ tail) emitted P hP
  have hh := BoxPointLoad.hoareTime L hiNum hiDen sep.hi b.upper hhn hhd
    (before ++ BoxPointLoad.code b.lower) tail emitted S hS
  have hs := seqTM_hoareTime (BoxPointLoad.machine loNum loDen) (BoxPointLoad.machine hiNum hiDen) hl (by
    rintro inp work out ⟨hc, hsafe, hn, hd, hrn, hrd, hhiNum, hhiDen, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hsafe, hhiNum, hhiDen, hn, hd, hrn, hrd, hr⟩) hh
  exact hs.consequence (by
    rintro inp work out ⟨hc, hsafe, hln, hld, hhn, hhd, hr⟩
    exact ⟨by simpa only [code, List.append_assoc] using hc, hsafe, hln, hld, hhn, hhd, hr⟩) (by
      rintro inp work out ⟨hc, hsafe, hn, hd, hrn, hrd, hln, hld, hrln, hrld, hr⟩
      exact ⟨by simpa only [code, List.append_assoc] using hc, hsafe, hln, hld, hn, hd, hrln, hrld, hrn, hrd, hr⟩) (by omega)

end JointThermoComplexity.Complexity.BoxLoad

#print axioms JointThermoComplexity.Complexity.BoxLoad.hoareTime
