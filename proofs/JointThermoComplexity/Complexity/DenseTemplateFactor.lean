module
public import proofs.JointThermoComplexity.Complexity.DenseFixedFactor
public import proofs.JointThermoComplexity.Complexity.RawTemplateFactor
public import proofs.JointThermoComplexity.Complexity.SignedProductControl

set_option autoImplicit false
@[expose] public section

/-! A reusable raw template factor emitter, including negative zero, with the
exact original rational-network factor bytes. -/

namespace JointThermoComplexity.Complexity.DenseTemplateFactor
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork)

def machine (t : ℤ) (right : Bool) : TM 64 := ReusableTemplateFactor.machine t right (0 : Fin 63) 1 12

def Ready (v : ℕ) (negative : Bool) (R : (Fin 63 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ Register v (work 0) ∧ (work 1).read = Γ.ofBool negative ∧
    (work 12).head = 1 ∧ (work 63).HasBinaryPrefix [] ∧ (work 63).cells 0 = Γ.start ∧ R (oldWork work)

def Pre (v : ℕ) (negative : Bool) (before input emitted : List Bool) (R : (Fin 63 → Tape) → Prop)
    (inp : Tape) (work : Fin 64 → Tape) (out : Tape) : Prop :=
  Cursor before input emitted inp work out ∧ Ready v negative R work

theorem raw_product (t : ℤ) (v : ℕ) (negative : Bool) :
    RationalFactorWords.coefficient (Bool.xor negative (decide (t < 0))) (t.natAbs * v) =
      RationalFactorWords.coefficient negative v * t := by
  simpa only [RationalFactorDispatch.coefficient_sign_magnitude] using
    SignedProductControl.coefficient_mul negative (decide (t < 0)) v t.natAbs

theorem hoareTime (t : ℤ) (v B : ℕ) (negative right : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (before input emitted : List Bool) (R : (Fin 63 → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ (12 : Fin 63) → next j = work j) → R work → R next) :
    (machine t right).HoareTime (Pre v negative before input emitted R)
      (Pre v negative before input
        (emitted ++ RationalFactorWords.word right (RationalFactorWords.coefficient negative v * t)) R)
      (11 * B + 872) := by
  have hh := RawTemplateFactor.hoareTime t v negative right (0 : Fin 63) 1 12
    (by decide) (by decide) before input emitted R hR
  apply hh.consequence
  · exact fun _ _ _ hp => hp
  · rintro inp work out ⟨hc, hs, hv, hn, hh, _ha, hb, hz, hr⟩
    exact ⟨by simpa only [raw_product] using hc, hs, hv, hn, hh, hb, hz, hr⟩
  · omega

theorem original_hoareTime (boxed right : Bool) (p : SparsePolynomialCodec.PolynomialData) (j : Fin p.payload.length)
    (t : ℤ) (v B : ℕ) (negative : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (hcoef : RawChemicalPolynomial.coefficientInteger p.payload j = RationalFactorWords.coefficient negative v * t)
    (before input emitted : List Bool) (R : (Fin 63 → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ (12 : Fin 63) → next j = work j) → R work → R next) :
    (machine t right).HoareTime (Pre v negative before input emitted R)
      (Pre v negative before input
        (emitted ++ DenseFactorCode.factor right (RationalPolynomialNetwork.left boxed p)
          (RationalPolynomialNetwork.right boxed p) j.succ.succ) R) (11 * B + 872) := by
  rw [DenseFactorCode.regular_code, hcoef]
  exact hoareTime t v B negative right hB ht before input emitted R hR

end JointThermoComplexity.Complexity.DenseTemplateFactor

#print axioms JointThermoComplexity.Complexity.DenseTemplateFactor.raw_product
#print axioms JointThermoComplexity.Complexity.DenseTemplateFactor.hoareTime
#print axioms JointThermoComplexity.Complexity.DenseTemplateFactor.original_hoareTime
