module
public import proofs.JointThermoComplexity.Complexity.ActivityBuild
public import proofs.JointThermoComplexity.Complexity.UnaryReset

set_option autoImplicit false
@[expose] public section

/-! Reset the bounded current cursor and emit the leading constraint conjunction plus complete activity positivity. -/

namespace JointThermoComplexity.Complexity.ActivityStart
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ActivityState CircuitSerialization

def machine (m : ℕ) : TM (m + 15) := seqTM (clearWorkTM (species (m + 1)))
  (seqTM (emitBitsTM conjunctionTag) (ActivityBuild.machine m))

def timeBound (L : ℕ) : ℕ := 32 * L ^ 3 + 56 * L ^ 2 + 45 * L + 16

theorem hoareTime {n arity : ℕ} (m L old : ℕ) (ha : arity ≤ 4 * L) (hn : n ≤ L) (hold : old ≤ L)
    (indices : Fin n → Fin arity) (hindices : ∀ i, (indices i).val = i.val)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready m old R work ∧
        IsReg n (work (MonomialFuel.slot (m + 1))))
      (fun inp work out => Cursor before input (emitted ++ (conjunctionTag ++ (ActivityCode.formula indices).code)) inp work out ∧
        Ready m n R work ∧ IsReg n (work (MonomialFuel.slot (m + 1)))) (timeBound L) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work => BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
    IsReg n (work (MonomialFuel.slot (m + 1))) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hz, hf, hr⟩
    exact ⟨by simpa only [hw _ (species_ne_scratch (m + 1)).symm] using hz,
      by simpa only [hw _ (MonomialFuel.slot_separate (m + 1)).species] using hf, hR work work' hw hr⟩
  have hr := UnaryReset.hoareTime (species (m + 1)) old before input emitted P hP
  have ht := FixedOutput.hoareTime conjunctionTag before input emitted (fun work =>
    Ready m 0 R work ∧ IsReg n (work (MonomialFuel.slot (m + 1))))
  have hb := ActivityBuild.hoareTime m L ha hn indices hindices before input (emitted ++ conjunctionTag) R hR
  have hrest := seqTM_hoareTime (emitBitsTM conjunctionTag) (ActivityBuild.machine m) ht (by
    rintro inp work out ⟨hc, _, hready, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hready, hf⟩) hb
  have hfull := seqTM_hoareTime (clearWorkTM (species (m + 1)))
    (seqTM (emitBitsTM conjunctionTag) (ActivityBuild.machine m)) hr (by
      rintro inp work out ⟨hc, hs, hi, hz, hf, hr⟩
      obtain ⟨hip, hw, ho⟩ := hc.phase
      rw [hip, hw, ho]
      exact ⟨hc, hs, ⟨hs, hz, hi, hr⟩, hf⟩) hrest
  exact hfull.consequence (by
    rintro inp work out ⟨hc, ⟨hs, hz, hi, hr⟩, hf⟩
    exact ⟨hc, hs, hi, hz, hf, hr⟩) (by
      rintro inp work out ⟨hc, hr, hf⟩
      exact ⟨by simpa only [List.append_assoc] using hc, hr, hf⟩) (by
        unfold timeBound ActivityBuild.timeBound
        simp only [conjunctionTag, List.length_cons, List.length_nil]
        omega)

end JointThermoComplexity.Complexity.ActivityStart

#print axioms JointThermoComplexity.Complexity.ActivityStart.hoareTime
