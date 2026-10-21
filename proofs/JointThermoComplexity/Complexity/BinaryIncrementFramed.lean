module
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementRun
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! A framed actual binary-register increment with all tapes parked again.
Input/output and every other work tape are retained exactly.
-/

namespace JointThermoComplexity.Complexity.BinaryIncrementFramed
open _root_.Complexity _root_.Complexity.TM BinaryIncrementRun
open HeaderAt (Cursor)
variable {w : ℕ}

theorem parked_register (value : ℕ) (t : Tape) (h : Register value t) : Parked t :=
  ⟨by rw [h.1.1], fun j hj => h.1.hasBinaryContent.cells_ne_start j hj⟩

def Stable (idx : Fin w) (R : (Fin w → Tape) → Prop) : Prop :=
  ∀ work next, (∀ k, k ≠ idx → next k = work k) → R work → R next

def Logical (idx : Fin w) (value : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred w := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ k, Parked (work k)) ∧ Register value (work idx) ∧ R work

theorem hoareTime (idx : Fin w) (value : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable idx R) :
    (BinaryIncrementMachine.machine idx).HoareTime (Logical idx value before input emitted R)
      (Logical idx (value + 1) before input emitted R) (2 * value.bits.length + 4) := by
  rintro inp work out ⟨hc, hs, hr, hx⟩
  obtain ⟨d, time, ht, hd, hh, hi, ho, he, hreg⟩ := run_nat idx value ⟨.carry, inp, work, out⟩ rfl hr
    hc.input_read hc.output_read (by rw [hc.tapePrefix.1]; omega)
    (fun k _ => ⟨(hs k).read_ne_start, (hs k).1⟩)
  have hs' : ∀ k, Parked (d.work k) := by
    intro k
    by_cases hk : k = idx
    · subst k
      exact parked_register (value + 1) _ hreg
    · rw [he k hk]
      exact hs k
  refine ⟨d, time, ht, hd, hh, ?_, hs', hreg, hR work d.work he hx⟩
  exact ⟨by simpa only [hi] using hc.cells, by simpa only [hi] using hc.head,
    fun k => ⟨(hs' k).read_ne_start, (hs' k).1⟩,
    by simpa only [ho] using hc.tapePrefix, by simpa only [ho] using hc.zero⟩

theorem bounded_hoareTime (idx : Fin w) (value W : ℕ) (hW : value.bits.length ≤ W)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : Stable idx R) :
    (BinaryIncrementMachine.machine idx).HoareTime (Logical idx value before input emitted R)
      (Logical idx (value + 1) before input emitted R) (2 * W + 4) :=
  (hoareTime idx value before input emitted R hR).mono_bound (by omega)

end JointThermoComplexity.Complexity.BinaryIncrementFramed

#print axioms JointThermoComplexity.Complexity.BinaryIncrementFramed.hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryIncrementFramed.bounded_hoareTime
