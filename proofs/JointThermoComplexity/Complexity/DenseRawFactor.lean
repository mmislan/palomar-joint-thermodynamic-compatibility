module
public import proofs.JointThermoComplexity.Complexity.DenseRawProduct

set_option autoImplicit false
@[expose] public section

/-! Full-bank raw factor emission requires no source polynomial or row identity. -/

namespace JointThermoComplexity.Complexity.DenseRawFactor
open _root_.Complexity _root_.Complexity.TM
open DenseFactorFrame

theorem hoareTime (t : ℤ) (v B : ℕ) (negative right : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    (DenseTemplateFactor.machine t right).HoareTime (Pre v negative before input emitted R)
      (Pre v negative before input
        (emitted ++ RationalFactorWords.word right (RationalFactorWords.coefficient negative v * t)) R) (11 * B + 872) := by
  have hh := DenseTemplateFactor.hoareTime t v B negative right hB ht before input emitted (Project R) (project_stable R hR)
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hv, hn, ha, hb, hz, hr⟩
    exact ⟨hc, hs, hv, hn, ha, hb, hz, work, rfl, hr⟩
  · rintro inp work out ⟨hc, hs, hv, hn, ha, hb, hz, hr⟩
    exact ⟨hc, hs, hv, hn, ha, hb, hz, of_project R hR work hr⟩
  · exact le_rfl

end JointThermoComplexity.Complexity.DenseRawFactor

#print axioms JointThermoComplexity.Complexity.DenseRawFactor.hoareTime
