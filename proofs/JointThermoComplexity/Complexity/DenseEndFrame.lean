module
public import proofs.JointThermoComplexity.Complexity.DenseEndRegister

set_option autoImplicit false
@[expose] public section

/-! Full-bank framing of one-time ending40 setup from binary count17. -/

namespace JointThermoComplexity.Complexity.DenseEndFrame
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork)
open DenseFactorFrame (Project)

def Stable (R : (Fin 64 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ 40 → j ≠ 63 → next j = work j) → R work → R next

theorem project_stable (R : (Fin 64 → Tape) → Prop) (hR : Stable R) : BinaryCopyRegister.Stable (40 : Fin 63) (Project R) := by
  rintro work next he ⟨full, hold, hr⟩
  let updated : Fin 64 → Tape := Fin.lastCases (full 63) next
  refine ⟨updated, ?_, hR full updated ?_ hr⟩
  · funext j
    simp only [oldWork, updated, Fin.lastCases_castSucc]
  · intro j h40 h63
    let k : Fin 63 := ⟨j.val, DenseCycleFrame.below_last j h63⟩
    have hj : j = k.castSucc := Fin.ext rfl
    rw [hj]
    simp only [updated, Fin.lastCases_castSucc]
    rw [he k (by intro hk; apply h40; rw [hj, hk]; rfl)]
    exact (congrFun hold k).symm

theorem of_project (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (work : Fin 64 → Tape)
    (hp : Project R (oldWork work)) : R work := by
  obtain ⟨full, hold, hr⟩ := hp
  apply hR full work _ hr
  intro j _ h63
  let k : Fin 63 := ⟨j.val, DenseCycleFrame.below_last j h63⟩
  have hj : j = k.castSucc := Fin.ext rfl
  rw [hj]
  exact (congrFun hold k).symm

def Pre (N u : ℕ) (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register N (work 17) ∧
    Register u (work 40) ∧ BinaryCopyRegister.Empty (work 63) ∧ R work
def Post (N : ℕ) (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register N (work 17) ∧
    Register (N + 1) (work 40) ∧ BinaryCopyRegister.Empty (work 63) ∧ R work

theorem hoareTime (N u B : ℕ) (hN : N.bits.length ≤ B) (hu : u.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    DenseEndRegister.machine.HoareTime (Pre N u before input emitted R) (Post N before input emitted R) (14 * B + 50) := by
  have hh := DenseEndRegister.hoareTime N u B hN hu before input emitted (Project R) (project_stable R hR)
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hn, hu', ht, hr⟩
    exact ⟨hc, hs, hn, hu', ht, work, rfl, hr⟩
  · rintro inp work out ⟨hc, hs, hn, he, ht, hr⟩
    exact ⟨hc, hs, hn, he, ht, of_project R hR work hr⟩
  · exact le_rfl

end JointThermoComplexity.Complexity.DenseEndFrame

#print axioms JointThermoComplexity.Complexity.DenseEndFrame.hoareTime
