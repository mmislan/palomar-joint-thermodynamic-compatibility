module
public import proofs.JointThermoComplexity.Complexity.DenseTemplateFactor

set_option autoImplicit false
@[expose] public section

/-! Lift the reusable factor's old-work frame to any full-bank predicate that
is insensitive to the adjusted sign and final scratch tapes. -/

namespace JointThermoComplexity.Complexity.DenseFactorFrame
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork)

def Stable (R : (Fin 64 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ 12 → j ≠ 63 → next j = work j) → R work → R next
def Project (R : (Fin 64 → Tape) → Prop) (old : Fin 63 → Tape) : Prop :=
  ∃ work, oldWork work = old ∧ R work

theorem project_stable (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    ∀ work next, (∀ j, j ≠ (12 : Fin 63) → next j = work j) → Project R work → Project R next := by
  rintro work next he ⟨full, hold, hr⟩
  let updated : Fin 64 → Tape := Fin.lastCases (full 63) next
  refine ⟨updated, ?_, hR full updated ?_ hr⟩
  · funext j
    simp only [oldWork, updated, Fin.lastCases_castSucc]
  · intro j h12 h63
    have hlt : j.val < 63 := by
      have hj := j.isLt
      have hn : j.val ≠ 63 := by
        intro hh
        apply h63
        exact Fin.ext hh
      omega
    let k : Fin 63 := ⟨j.val, hlt⟩
    have hj : j = k.castSucc := Fin.ext rfl
    rw [hj]
    simp only [updated, Fin.lastCases_castSucc]
    rw [he k (by intro hk; apply h12; rw [hj, hk]; rfl)]
    exact (congrFun hold k).symm

theorem of_project (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (work : Fin 64 → Tape)
    (hp : Project R (oldWork work)) : R work := by
  obtain ⟨full, hold, hr⟩ := hp
  apply hR full work _ hr
  intro j _ h63
  have hlt : j.val < 63 := by
    have hj := j.isLt
    have hn : j.val ≠ 63 := by
      intro hh
      apply h63
      exact Fin.ext hh
    omega
  let k : Fin 63 := ⟨j.val, hlt⟩
  have hj : j = k.castSucc := Fin.ext rfl
  rw [hj]
  exact (congrFun hold k).symm

def Ready (v : ℕ) (negative : Bool) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ Register v (work 0) ∧ (work 1).read = Γ.ofBool negative ∧
    (work 12).head = 1 ∧ (work 63).HasBinaryPrefix [] ∧ (work 63).cells 0 = Γ.start ∧ R work
def Pre (v : ℕ) (negative : Bool) (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => Cursor before input emitted inp work out ∧ Ready v negative R work

theorem original_hoareTime (boxed right : Bool) (p : SparsePolynomialCodec.PolynomialData) (j : Fin p.payload.length)
    (t : ℤ) (v B : ℕ) (negative : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (hcoef : RawChemicalPolynomial.coefficientInteger p.payload j = RationalFactorWords.coefficient negative v * t)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    (DenseTemplateFactor.machine t right).HoareTime (Pre v negative before input emitted R)
      (Pre v negative before input
        (emitted ++ DenseFactorCode.factor right (RationalPolynomialNetwork.left boxed p)
          (RationalPolynomialNetwork.right boxed p) j.succ.succ) R) (11 * B + 872) := by
  have hh := DenseTemplateFactor.original_hoareTime boxed right p j t v B negative hB ht hcoef
    before input emitted (Project R) (project_stable R hR)
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hv, hn, ha, hb, hz, hr⟩
    exact ⟨hc, hs, hv, hn, ha, hb, hz, work, rfl, hr⟩
  · rintro inp work out ⟨hc, hs, hv, hn, ha, hb, hz, hr⟩
    exact ⟨hc, hs, hv, hn, ha, hb, hz, of_project R hR work hr⟩
  · exact le_rfl

end JointThermoComplexity.Complexity.DenseFactorFrame

#print axioms JointThermoComplexity.Complexity.DenseFactorFrame.original_hoareTime
