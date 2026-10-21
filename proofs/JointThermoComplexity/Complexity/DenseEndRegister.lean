module
public import proofs.JointThermoComplexity.Complexity.DenseRecordPrepare

set_option autoImplicit false
@[expose] public section

/-! One-time binary setup of ending40=N+1 from the retained binary count17. -/

namespace JointThermoComplexity.Complexity.DenseEndRegister
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork)

def machine : TM 64 := seqTM (BinaryCopyRegister.machine (17 : Fin 63) 40)
  (BinaryIncrementMachine.machine (40 : Fin 64))

def Post (N : ℕ) (before input emitted : List Bool) (R : (Fin 63 → Tape) → Prop) :
    _root_.Complexity.TM.TapePred 64 := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register N (work 17) ∧
    Register (N + 1) (work 40) ∧ BinaryCopyRegister.Empty (work 63) ∧ R (oldWork work)

theorem hoareTime (N u B : ℕ) (hN : N.bits.length ≤ B) (hu : u.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 63 → Tape) → Prop) (hR : BinaryCopyRegister.Stable 40 R) :
    machine.HoareTime (BinaryCopyRegister.Pre (17 : Fin 63) 40 N u before input emitted R)
      (Post N before input emitted R) (14 * B + 50) := by
  let S : (Fin 64 → Tape) → Prop := fun work => Register N (work 17) ∧ BinaryCopyRegister.Empty (work 63) ∧ R (oldWork work)
  have hS : BinaryIncrementFramed.Stable (40 : Fin 64) S := by
    rintro work next he ⟨hn, ht, hr⟩
    refine ⟨by rw [he 17 (by decide)]; exact hn, by rw [he 63 (by decide)]; exact ht, ?_⟩
    apply hR (oldWork work) (oldWork next) _ hr
    intro j hj
    apply he j.castSucc
    intro hh
    exact hj (Fin.ext (congrArg (fun k : Fin 64 => k.val) hh))
  have hc := BinaryCopyRegister.bounded_hoareTime (17 : Fin 63) 40 (by decide) N u B hN hu before input emitted R hR
  have hi := BinaryIncrementFramed.bounded_hoareTime (40 : Fin 64) N B hN before input emitted S hS
  have hh := seqTM_hoareTime _ _ hc (by
    rintro inp work out ⟨hc, hs, hn, he, ht, hr⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨hc, hs, he, hn, ht, hr⟩) hi
  apply hh.consequence (fun _ _ _ h => h)
  · rintro inp work out ⟨hc, hs, he, hn, ht, hr⟩
    exact ⟨hc, hs, hn, he, ht, hr⟩
  · omega

theorem zero_hoareTime (N B : ℕ) (hN : N.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 63 → Tape) → Prop) (hR : BinaryCopyRegister.Stable 40 R) :
    machine.HoareTime (BinaryCopyRegister.Pre (17 : Fin 63) 40 N 0 before input emitted R)
      (Post N before input emitted R) (14 * B + 50) :=
  hoareTime N 0 B hN (by simp only [Nat.zero_bits, List.length_nil]; omega) before input emitted R hR

end JointThermoComplexity.Complexity.DenseEndRegister

#print axioms JointThermoComplexity.Complexity.DenseEndRegister.hoareTime
#print axioms JointThermoComplexity.Complexity.DenseEndRegister.zero_hoareTime
