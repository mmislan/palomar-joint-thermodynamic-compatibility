module
public import proofs.JointThermoComplexity.Complexity.NaturalIndexedLoad
public import proofs.JointThermoComplexity.Complexity.NaturalSelectionCode

set_option autoImplicit false
@[expose] public section

/-! Load one indexed dense-array natural as raw Nat.bits using the actual retained position register. -/

namespace JointThermoComplexity.Complexity.NaturalArrayIndexedLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState NaturalSelectionCode

variable {w n : ℕ}

abbrev machine (idx fuel : Fin (w + 1)) : TM (w + 1) := NaturalIndexedLoad.machine idx fuel

theorem hoareTime (idx fuel : Fin (w + 1)) (hne : fuel ≠ idx) (L : ℕ) (hn : n ≤ L)
    (values : Fin n → ℕ) (s : Fin n) (hsize : ∀ j, (BitCodec.naturalCode (values j)).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx fuel).HoareTime
      (fun inp work out => Cursor before (NaturalArraySkip.code values ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ IsReg s.val (work fuel) ∧ R work)
      (fun inp work out => Cursor ((before ++ leading values s) ++ BitCodec.naturalCode (values s)) (trailing values s ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString (values s).bits ∧ (work idx).cells 0 = Γ.start ∧
        Reusable L (work idx) ∧ IsReg s.val (work fuel) ∧ R work) (NaturalIndexedLoad.timeBound L) := by
  have hp : ((List.ofFn values).take s.val).length ≤ L := by rw [leading_count]; omega
  have hs : ∀ x ∈ (List.ofFn values).take s.val, (BitCodec.naturalCode x).length ≤ L := by
    intro x hx
    have hm : x ∈ List.ofFn values := List.mem_of_mem_take hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hm
    exact hsize j
  have h := NaturalIndexedLoad.hoareTime idx fuel hne L ((List.ofFn values).take s.val) hp (values s) hs (hsize s)
    before (trailing values s ++ tail) emitted R hR
  exact h.consequence (by
    intro inp work out h
    simpa only [NaturalSelectionCode.split values s, leading, List.append_assoc, leading_count] using h)
    (by intro inp work out h; simpa only [leading, leading_count] using h) le_rfl

end JointThermoComplexity.Complexity.NaturalArrayIndexedLoad

#print axioms JointThermoComplexity.Complexity.NaturalArrayIndexedLoad.hoareTime
