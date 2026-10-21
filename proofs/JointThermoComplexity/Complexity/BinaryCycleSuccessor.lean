module
public import proofs.JointThermoComplexity.Complexity.BinaryCopyRegister
public import proofs.JointThermoComplexity.Complexity.RetainedBinaryEquality
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementFramed

set_option autoImplicit false
@[expose] public section

/-! Actual 64-tape cyclic successor: retain current38/end40, prepare next41 and lastflag43. -/

namespace JointThermoComplexity.Complexity.BinaryCycleSuccessor
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork)

def comparison : SmallCoefficientMatch.Ports 63 := ⟨38, 40, 43, by constructor <;> decide⟩
def nextValue (i ending : ℕ) : ℕ := if i = ending then 0 else i + 1

def Stable (R : (Fin 63 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ 41 → j ≠ 43 → next j = work j) → R work → R next

def Frame (i ending : ℕ) (R : (Fin 63 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register i (work 38) ∧ Register ending (work 40) ∧ (work 43).head = 1 ∧
    (work 43).read = Γ.ofBool (decide (i ≠ ending)) ∧ BinaryCopyRegister.Empty (work 63) ∧ R (oldWork work)

def At (i ending u : ℕ) (before input emitted : List Bool) (R : (Fin 63 → Tape) → Prop) :
    _root_.Complexity.TM.TapePred 64 := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register u (work 41) ∧ Frame i ending R work

theorem frame_stable (i ending : ℕ) (R : (Fin 63 → Tape) → Prop) (hR : Stable R) :
    BinaryIncrementFramed.Stable (41 : Fin 64) (Frame i ending R) := by
  rintro work next he ⟨hi, hend, hf, hv, ht, hx⟩
  refine ⟨by rw [he 38 (by decide)]; exact hi, by rw [he 40 (by decide)]; exact hend,
    by rw [he 43 (by decide)]; exact hf, by rw [he 43 (by decide)]; exact hv,
    by rw [he 63 (by decide)]; exact ht, ?_⟩
  apply hR (oldWork work) (oldWork next) _ hx
  intro j hj _
  apply he j.castSucc
  intro hh
  exact hj (Fin.ext (congrArg (fun k : Fin 64 => k.val) hh))

theorem clear_hoareTime (i ending u B : ℕ) (hu : u.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 63 → Tape) → Prop) (hR : Stable R) :
    (BinaryBufferReset.machine (41 : Fin 64)).HoareTime (At i ending u before input emitted R)
      (At i ending 0 before input emitted R) (3 * B + 9) := by
  have hh := BinaryBufferReset.hoareTime (41 : Fin 64) u.bits before input emitted (Frame i ending R) (frame_stable i ending R hR)
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hu, hf⟩
    exact ⟨hc, hs, hu.1.2, hu.2, by rw [hu.1.1]; omega, hf⟩
  · rintro inp work out ⟨hc, hs, hz, hf⟩
    have hzero : Register 0 (work 41) :=
      ⟨by simpa only [Nat.zero_bits, List.replicate_zero] using CountTape.string_of_register hz, hz.cell0⟩
    exact ⟨hc, hs, hzero, hf⟩
  · omega

def copyIncrement : TM 64 := seqTM (BinaryCopyRegister.machine (38 : Fin 63) 41)
  (BinaryIncrementMachine.machine (41 : Fin 64))

theorem copy_increment_hoareTime (i ending u B : ℕ) (hi : i.bits.length ≤ B) (hu : u.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 63 → Tape) → Prop) (hR : Stable R) :
    copyIncrement.HoareTime (At i ending u before input emitted R)
      (At i ending (i + 1) before input emitted R) (14 * B + 50) := by
  let P : (Fin 63 → Tape) → Prop := fun work => Register ending (work 40) ∧ (work 43).head = 1 ∧
    (work 43).read = Γ.ofBool (decide (i ≠ ending)) ∧ R work
  have hP : BinaryCopyRegister.Stable (41 : Fin 63) P := by
    rintro work next he ⟨hend, hf, hv, hx⟩
    exact ⟨by rw [he 40 (by decide)]; exact hend, by rw [he 43 (by decide)]; exact hf,
      by rw [he 43 (by decide)]; exact hv, hR work next (fun j hj _ => he j hj) hx⟩
  have hc := BinaryCopyRegister.bounded_hoareTime (38 : Fin 63) 41 (by decide) i u B hi hu before input emitted P hP
  have hn := BinaryIncrementFramed.bounded_hoareTime (41 : Fin 64) i B hi before input emitted (Frame i ending R) (frame_stable i ending R hR)
  have hh := seqTM_hoareTime _ _ hc (by
    rintro inp work out ⟨hc, hs, hi, hn, ht, hend, hf, hv, hx⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨hc, hs, hn, hi, hend, hf, hv, ht, hx⟩) hn
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hu, hi, hend, hf, hv, ht, hx⟩
    exact ⟨hc, hs, hi, hu, ht, hend, hf, hv, hx⟩
  · exact fun _ _ _ hp => hp
  · omega

def choose : TM 64 := WorkSymbolBranch.machine Γ.zero (43 : Fin 64)
  (BinaryBufferReset.machine (41 : Fin 64)) copyIncrement

theorem choose_hoareTime (i ending u B : ℕ) (hi : i.bits.length ≤ B) (hu : u.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 63 → Tape) → Prop) (hR : Stable R) :
    choose.HoareTime (At i ending u before input emitted R)
      (At i ending (nextValue i ending) before input emitted R) (14 * B + 52) := by
  let P : (Fin 64 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ Register u (work 41) ∧ Frame i ending R work
  let Q : (Fin 64 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ Register (nextValue i ending) (work 41) ∧ Frame i ending R work
  by_cases he : i = ending
  · have hb := clear_hoareTime i ending u B hu before input emitted R hR
    have hh := WorkSymbolBranch.yes_hoareTime Γ.zero (43 : Fin 64) (BinaryBufferReset.machine (41 : Fin 64)) copyIncrement
      before input emitted before input emitted P Q (3 * B + 9) (by
        apply hb.consequence
        · exact fun _ _ _ hp => hp
        · intro inp work out hp
          change At i ending (nextValue i ending) before input emitted R inp work out
          simpa only [nextValue, he, ↓reduceIte] using hp
        · exact le_rfl)
    apply hh.consequence
    · intro inp work out hp
      refine ⟨hp, ?_⟩
      have hv := hp.2.2.2.2.2.2.1
      simpa only [he, ne_eq, not_true_eq_false, decide_false, Γ.ofBool] using hv
    · exact fun _ _ _ hp => hp
    · omega
  · have hb := copy_increment_hoareTime i ending u B hi hu before input emitted R hR
    have hh := WorkSymbolBranch.no_hoareTime Γ.zero (43 : Fin 64) (BinaryBufferReset.machine (41 : Fin 64)) copyIncrement
      before input emitted before input emitted P Q (14 * B + 50) (by
        apply hb.consequence
        · exact fun _ _ _ hp => hp
        · intro inp work out hp
          change At i ending (nextValue i ending) before input emitted R inp work out
          simpa only [nextValue, he, ↓reduceIte] using hp
        · exact le_rfl)
    apply hh.consequence
    · intro inp work out hp
      refine ⟨hp, ?_⟩
      have hv := hp.2.2.2.2.2.2.1
      rw [hv]
      have hne : decide (i ≠ ending) = true := by simpa only [decide_eq_true_eq] using he
      rw [hne]
      decide
    · exact fun _ _ _ hp => hp
    · exact le_rfl

def Pre (i ending u : ℕ) (before input emitted : List Bool) (R : (Fin 63 → Tape) → Prop) :
    _root_.Complexity.TM.TapePred 64 := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register i (work 38) ∧
    Register ending (work 40) ∧ Register u (work 41) ∧ (work 43).head = 1 ∧ BinaryCopyRegister.Empty (work 63) ∧ R (oldWork work)

def machine : TM 64 := seqTM (BinaryEqualityFlag.machine comparison) choose

theorem hoareTime (i ending u B : ℕ) (hi : i.bits.length ≤ B) (hend : ending.bits.length ≤ B) (hu : u.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 63 → Tape) → Prop) (hR : Stable R) :
    machine.HoareTime (Pre i ending u before input emitted R)
      (At i ending (nextValue i ending) before input emitted R) (38 * B + 74) := by
  let C : (Fin 64 → Tape) → Prop := fun work => Register u (work 41) ∧ BinaryCopyRegister.Empty (work 63) ∧ R (oldWork work)
  have hC : RetainedBinaryEquality.Stable comparison C := by
    rintro work next he ⟨hu, ht, hx⟩
    refine ⟨by rw [he 41 (by decide)]; exact hu, by rw [he 63 (by decide)]; exact ht, ?_⟩
    apply hR (oldWork work) (oldWork next) _ hx
    intro j _ hj
    apply he j.castSucc
    intro hh
    exact hj (Fin.ext (congrArg (fun k : Fin 64 => k.val) hh))
  have hc := RetainedBinaryEquality.hoareTime comparison i ending B hi hend before input emitted C hC
  have hn := choose_hoareTime i ending u B hi hu before input emitted R hR
  have hh := seqTM_hoareTime _ _ hc (by
    rintro inp work out ⟨⟨hc, hs, hi, hend, hf, hu, ht, hx⟩, hv⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨hc, hs, hu, hi, hend, hf, hv, ht, hx⟩) hn
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hi, hend, hu, hf, ht, hx⟩
    exact ⟨hc, hs, hi, hend, hf, hu, ht, hx⟩
  · exact fun _ _ _ hp => hp
  · omega

end JointThermoComplexity.Complexity.BinaryCycleSuccessor

#print axioms JointThermoComplexity.Complexity.BinaryCycleSuccessor.hoareTime
