module
public import proofs.JointThermoComplexity.Complexity.DenseFactorCode
public import proofs.JointThermoComplexity.Complexity.BinaryEmit

set_option autoImplicit false
@[expose] public section

/-! Fixed baseline and offset fields. The boxed denominator is read in binary
from register13; only the finite control choices enter the machine definition. -/

namespace JointThermoComplexity.Complexity.DenseFixedFactor
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun

def numeratorWord (right : Bool) : List Bool := BitCodec.naturalCode (if right then 2 else 1)
def unitWord : List Bool := BitCodec.naturalCode 1 ++ BitCodec.naturalCode 1
def machine (boxed right offset : Bool) : TM 64 :=
  if offset then
    if boxed then seqTM (emitBitsTM (numeratorWord right)) (BinaryEmit.machine 13)
    else emitBitsTM (numeratorWord right ++ BitCodec.naturalCode 1)
  else emitBitsTM unitWord

def Pre (U : ℕ) (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop)
    (inp : Tape) (work : Fin 64 → Tape) (out : Tape) : Prop :=
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register U (work 13) ∧ R work

theorem prefix_length (right : Bool) : (numeratorWord right).length ≤ 5 := by cases right <;> decide
theorem unit_length : unitWord.length = 6 := by decide
theorem one_length : (BitCodec.naturalCode 1).length = 3 := by decide

theorem hoareTime (boxed right offset : Bool) (U B : ℕ) (hB : U.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) :
    (machine boxed right offset).HoareTime (Pre U before input emitted R)
      (Pre U before input (emitted ++ DenseFactorCode.fixedWord boxed right offset U) R)
      (3 * B + 11) := by
  cases offset with
  | false =>
    have hh := FixedOutput.hoareTime (w := 64) unitWord before input emitted
      (fun work => Register U (work 13) ∧ R work)
    apply hh.consequence
    · exact fun _ _ _ hp => hp
    · exact fun _ _ _ hp => hp
    · rw [unit_length]; omega
  | true =>
    cases boxed with
    | false =>
      have hh := FixedOutput.hoareTime (w := 64) (numeratorWord right ++ BitCodec.naturalCode 1)
        before input emitted (fun work => Register U (work 13) ∧ R work)
      apply hh.consequence
      · exact fun _ _ _ hp => hp
      · exact fun _ _ _ hp => hp
      · rw [List.length_append, one_length]
        have hl := prefix_length right
        omega
    | true =>
      have h0 := FixedOutput.hoareTime (w := 64) (numeratorWord right) before input emitted
        (fun work => Register U (work 13) ∧ R work)
      have h1 := BinaryEmit.natural_hoareTime (13 : Fin 64) U before input (emitted ++ numeratorWord right)
        (fun work => (∀ j, Parked (work j)) ∧ R work)
      have hh := seqTM_hoareTime _ _ h0 (by
        rintro inp work out ⟨hc, hs, hu, hr⟩
        obtain ⟨hi, hw, ho⟩ := hc.phase
        rw [hi, hw, ho]
        exact ⟨hc, hu, hs, hr⟩) h1
      apply hh.consequence
      · exact fun _ _ _ hp => hp
      · rintro inp work out ⟨hc, hu, hs, hr⟩
        refine ⟨?_, hs, hu, hr⟩
        simpa only [DenseFactorCode.fixedWord, ↓reduceIte, numeratorWord, List.append_assoc] using hc
      · have hl := prefix_length right
        omega

theorem original_hoareTime (boxed right offset : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (B : ℕ) (hB : (RawOffsetBounds.offset p.payload).bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) :
    (machine boxed right offset).HoareTime
      (Pre (RawOffsetBounds.offset p.payload) before input emitted R)
      (Pre (RawOffsetBounds.offset p.payload) before input
        (emitted ++ DenseFactorCode.factor right (RationalPolynomialNetwork.left boxed p)
          (RationalPolynomialNetwork.right boxed p)
          (DenseFixedComplexOriginal.initialVertex offset p.payload.length)) R) (3 * B + 11) := by
  rw [DenseFactorCode.fixed_code]
  exact hoareTime boxed right offset _ B hB before input emitted R

end JointThermoComplexity.Complexity.DenseFixedFactor

#print axioms JointThermoComplexity.Complexity.DenseFixedFactor.hoareTime
#print axioms JointThermoComplexity.Complexity.DenseFixedFactor.original_hoareTime
