module
public import proofs.JointThermoComplexity.Complexity.DenseFixedRecord

set_option autoImplicit false
@[expose] public section

/-! Advance the retained current index after a complete record. The post-index
is a natural number, so the last row correctly returns the N+2 sentinel. -/

namespace JointThermoComplexity.Complexity.DenseRecordAdvance
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseComplexOriginal RationalBranchData
variable {e N : ℕ}

def Tail (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N : ℕ) (i : Fin (N + 2))
    (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register (vertex true i).val (work 41) ∧ (work 43).read = Γ.ofBool (decide (i.val ≠ N + 1)) ∧
    Register 0 (work 39) ∧ (work 42).head = 1 ∧ IsReg N (work 33) ∧ IsReg (N + 2) (work 34) ∧
    PowerVectorUnit.Refs (DensePowerPorts.cellLayout m hm) values work ∧ IsReg n (work 16) ∧ R work
def At (current m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N : ℕ) (i : Fin (N + 2))
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
    Register current (work 38) ∧ Tail m hm values n N i R work

theorem tail_stable (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N : ℕ) (i : Fin (N + 2))
    (R : (Fin 64 → Tape) → Prop) (hR : BinaryIncrementFramed.Stable (38 : Fin 64) R) :
    BinaryIncrementFramed.Stable (38 : Fin 64) (Tail m hm values n N i R) := by
  rintro work next he ⟨hn, hf, hz, hh, hN, hb, href, ha, hr⟩
  refine ⟨by rw [he 41 (by decide)]; exact hn, by rw [he 43 (by decide)]; exact hf,
    by rw [he 39 (by decide)]; exact hz, by rw [he 42 (by decide)]; exact hh,
    by rw [he 33 (by decide)]; exact hN, by rw [he 34 (by decide)]; exact hb, ?_,
    by rw [he 16 (by decide)]; exact ha, hR work next he hr⟩
  intro p hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  have hc : DensePowerPorts.reference m hm j ≠ (38 : Fin 64) := by
    intro hh
    have hv := congrArg Fin.val hh
    change 2 + j.val = 38 at hv
    omega
  have hf : DensePowerPorts.flag m hm j ≠ (38 : Fin 64) := by
    intro hh
    have hv := congrArg Fin.val hh
    change 44 + j.val = 38 at hv
    omega
  change Register (values (DensePowerPorts.reference m hm j)) (next (DensePowerPorts.reference m hm j)) ∧
    (next (DensePowerPorts.flag m hm j)).head = 1
  rw [he _ hc, he _ hf]
  exact href (DensePowerPorts.comparison m hm j) (List.mem_ofFn.mpr ⟨j, rfl⟩)

def machine (record : TM 64) : TM 64 := seqTM record (BinaryIncrementMachine.machine (38 : Fin 64))

theorem hoareTime (record : TM 64) (right : Bool) (L Rdata : Data (Fin e) N) (i : Fin (N + 2))
    (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n B E : ℕ) (hi : i.val.bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hR : BinaryIncrementFramed.Stable (38 : Fin 64) R)
    (hr : ∀ before input emitted, record.HoareTime (DenseRecordFrame.Pre m hm values n N i before input emitted R)
      (DenseRecordFrame.Pre m hm values n N i before input
        (emitted ++ DenseRecordCore.recordWord right L Rdata i) R) E)
    (before input emitted : List Bool) :
    (machine record).HoareTime (DenseRecordFrame.Pre m hm values n N i before input emitted R)
      (At (i.val + 1) m hm values n N i before input (emitted ++ DenseRecordCore.recordWord right L Rdata i) R)
      (E + 2 * B + 5) := by
  have hinc := BinaryIncrementFramed.bounded_hoareTime (38 : Fin 64) i.val B hi before input
    (emitted ++ DenseRecordCore.recordWord right L Rdata i) (Tail m hm values n N i R)
    (tail_stable m hm values n N i R hR)
  have hh := seqTM_hoareTime _ _ (hr before input emitted) (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) hinc
  exact hh.mono_bound (by omega)

end JointThermoComplexity.Complexity.DenseRecordAdvance

#print axioms JointThermoComplexity.Complexity.DenseRecordAdvance.hoareTime
