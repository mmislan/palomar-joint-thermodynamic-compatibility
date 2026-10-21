module
public import proofs.JointThermoComplexity.Complexity.DenseCycleFrame

set_option autoImplicit false
@[expose] public section

/-! The actual successor routine prepares the common original-record entry. -/

namespace JointThermoComplexity.Complexity.DenseRecordPrepare
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
variable {N : ℕ}

def Static (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N : ℕ) (R : (Fin 64 → Tape) → Prop)
    (work : Fin 64 → Tape) : Prop :=
  Register 0 (work 39) ∧ (work 42).head = 1 ∧ IsReg N (work 33) ∧ IsReg (N + 2) (work 34) ∧
    PowerVectorUnit.Refs (DensePowerPorts.cellLayout m hm) values work ∧ IsReg n (work 16) ∧ R work

theorem static_stable (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N : ℕ)
    (R : (Fin 64 → Tape) → Prop) (hR : DenseCycleFrame.Stable R) :
    DenseCycleFrame.Stable (Static m hm values n N R) := by
  rintro work next he ⟨hz, hh, hN, hb, href, ha, hr⟩
  refine ⟨by rw [he 39 (by decide) (by decide) (by decide)]; exact hz,
    by rw [he 42 (by decide) (by decide) (by decide)]; exact hh,
    by rw [he 33 (by decide) (by decide) (by decide)]; exact hN,
    by rw [he 34 (by decide) (by decide) (by decide)]; exact hb, ?_,
    by rw [he 16 (by decide) (by decide) (by decide)]; exact ha, hR work next he hr⟩
  intro p hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  have keep (q : Fin 64) (hq : q.val ≤ 5 ∨ 44 ≤ q.val ∧ q.val ≤ 47) : next q = work q := by
    apply he q
    · intro hh; have hv := congrArg Fin.val hh; change q.val = 41 at hv; omega
    · intro hh; have hv := congrArg Fin.val hh; change q.val = 43 at hv; omega
    · intro hh; have hv := congrArg Fin.val hh; change q.val = 63 at hv; omega
  have hc := keep (DensePowerPorts.reference m hm j) (Or.inl (by change 2 + j.val ≤ 5; omega))
  have hf := keep (DensePowerPorts.flag m hm j) (Or.inr (by change 44 ≤ 44 + j.val ∧ 44 + j.val ≤ 47; constructor <;> omega))
  change Register (values (DensePowerPorts.reference m hm j)) (next (DensePowerPorts.reference m hm j)) ∧
    (next (DensePowerPorts.flag m hm j)).head = 1
  rw [hc, hf]
  exact href (DensePowerPorts.comparison m hm j) (List.mem_ofFn.mpr ⟨j, rfl⟩)

def Retained (N : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register (N + 1) (work 40) ∧ (work 43).head = 1 ∧ BinaryCopyRegister.Empty (work 63) ∧ R work

theorem hoareTime (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N : ℕ) (i : Fin (N + 2))
    (u B : ℕ) (hi : i.val.bits.length ≤ B) (hend : (N + 1).bits.length ≤ B) (hu : u.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : DenseCycleFrame.Stable R) :
    BinaryCycleSuccessor.machine.HoareTime
      (DenseCycleFrame.Pre i u before input emitted (Static m hm values n N R))
      (DenseRecordFrame.Pre m hm values n N i before input emitted (Retained N R)) (38 * B + 74) := by
  have hh := DenseCycleFrame.hoareTime i u B hi hend hu before input emitted (Static m hm values n N R)
    (static_stable m hm values n N R hR)
  apply hh.consequence (fun _ _ _ h => h)
  · rintro inp work out ⟨hc, hs, hn, hi, he, hh, hf, ht, hz, h42, hN, hb, href, ha, hr⟩
    exact ⟨hc, hs, hi, hn, hf, hz, h42, hN, hb, href, ha, he, hh, ht, hr⟩
  · exact le_rfl

end JointThermoComplexity.Complexity.DenseRecordPrepare

#print axioms JointThermoComplexity.Complexity.DenseRecordPrepare.hoareTime
