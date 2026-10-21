module
public import proofs.JointThermoComplexity.Complexity.DenseFixedAdvance

set_option autoImplicit false
@[expose] public section

/-! Full-bank frames for the already checked binary cyclic successor. -/

namespace JointThermoComplexity.Complexity.DenseCycleFrame
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork)
open DenseFactorFrame (Project)
variable {N : ℕ}

def Stable (R : (Fin 64 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ 41 → j ≠ 43 → j ≠ 63 → next j = work j) → R work → R next

theorem below_last (j : Fin 64) (h : j ≠ 63) : j.val < 63 := by
  have hj := j.isLt
  have hn : j.val ≠ 63 := by intro hh; apply h; exact Fin.ext hh
  omega

theorem project_stable (R : (Fin 64 → Tape) → Prop) (hR : Stable R) : BinaryCycleSuccessor.Stable (Project R) := by
  rintro work next he ⟨full, hold, hr⟩
  let updated : Fin 64 → Tape := Fin.lastCases (full 63) next
  refine ⟨updated, ?_, hR full updated ?_ hr⟩
  · funext j
    simp only [oldWork, updated, Fin.lastCases_castSucc]
  · intro j h41 h43 h63
    let k : Fin 63 := ⟨j.val, below_last j h63⟩
    have hj : j = k.castSucc := Fin.ext rfl
    rw [hj]
    simp only [updated, Fin.lastCases_castSucc]
    rw [he k (by intro hk; apply h41; rw [hj, hk]; rfl) (by intro hk; apply h43; rw [hj, hk]; rfl)]
    exact (congrFun hold k).symm

theorem of_project (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (work : Fin 64 → Tape)
    (hp : Project R (oldWork work)) : R work := by
  obtain ⟨full, hold, hr⟩ := hp
  apply hR full work _ hr
  intro j _ _ h63
  let k : Fin 63 := ⟨j.val, below_last j h63⟩
  have hj : j = k.castSucc := Fin.ext rfl
  rw [hj]
  exact (congrFun hold k).symm

def Pre (i : Fin (N + 2)) (u : ℕ) (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) :
    _root_.Complexity.TM.TapePred 64 := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register i.val (work 38) ∧
    Register (N + 1) (work 40) ∧ Register u (work 41) ∧ (work 43).head = 1 ∧ BinaryCopyRegister.Empty (work 63) ∧ R work
def Post (i : Fin (N + 2)) (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) :
    _root_.Complexity.TM.TapePred 64 := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
    Register (DenseComplexOriginal.vertex true i).val (work 41) ∧ Register i.val (work 38) ∧
    Register (N + 1) (work 40) ∧ (work 43).head = 1 ∧
    (work 43).read = Γ.ofBool (decide (i.val ≠ N + 1)) ∧ BinaryCopyRegister.Empty (work 63) ∧ R work

theorem hoareTime (i : Fin (N + 2)) (u B : ℕ) (hi : i.val.bits.length ≤ B)
    (hend : (N + 1).bits.length ≤ B) (hu : u.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    BinaryCycleSuccessor.machine.HoareTime (Pre i u before input emitted R) (Post i before input emitted R) (38 * B + 74) := by
  have hh := DenseCycleData.hoareTime i u B hi hend hu before input emitted (Project R) (project_stable R hR)
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hi, he, hu, hf, ht, hr⟩
    exact ⟨hc, hs, hi, he, hu, hf, ht, work, rfl, hr⟩
  · rintro inp work out ⟨hc, hs, hn, hi, he, hf, hv, ht, hr⟩
    exact ⟨hc, hs, hn, hi, he, hf, hv, ht, of_project R hR work hr⟩
  · exact le_rfl

end JointThermoComplexity.Complexity.DenseCycleFrame

#print axioms JointThermoComplexity.Complexity.DenseCycleFrame.hoareTime
