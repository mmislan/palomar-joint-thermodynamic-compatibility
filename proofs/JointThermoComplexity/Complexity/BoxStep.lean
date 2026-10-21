module
public import proofs.JointThermoComplexity.Complexity.BoxOptionalRuntime
public import proofs.JointThermoComplexity.Complexity.UnarySuccessor
public import proofs.JointThermoComplexity.Complexity.CircuitSerialization

set_option autoImplicit false
@[expose] public section

/-! Emit one allFin box clause and advance its actual activity-variable cursor. -/

namespace JointThermoComplexity.Complexity.BoxStep
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts BoxState NetworkData CircuitSerialization

def machine (m : ℕ) : TM (m + 15) := seqTM (emitBitsTM conjunctionTag)
  (seqTM (BoxOptionalRuntime.machine m) (UnarySuccessor.machine (species (m + 1))))

def word {arity : ℕ} (box : Option ClosedBox) (idx : Fin arity) : List Bool :=
  conjunctionTag ++ (NetworkFormula.boxFormula box idx).code

def timeBound (L : ℕ) : ℕ := 128 * L ^ 2 + 268 * L + 271

theorem hoareTime {arity : ℕ} (m L : ℕ) (ha : arity ≤ 4 * L) (box : Option ClosedBox)
    (hsize : BoxOptionalRuntime.Bounded L box) (idx : Fin arity) (before tail emitted : List Bool)
    (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before ((FiniteCodec.optional DataCodec.box).code box ++ tail) emitted inp work out ∧
        Ready m L idx.val R work)
      (fun inp work out => Cursor (before ++ (FiniteCodec.optional DataCodec.box).code box) tail
        (emitted ++ word box idx) inp work out ∧ Ready m L (idx.val + 1) R work) (timeBound L) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work =>
    BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧ Buffers m L work ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hz, ⟨hln, hld, hhn, hhd⟩, hr⟩
    have hsave : saved m ≠ species (m + 1) :=
      (BoxOptionalRuntime.source_separate m (saved m) (by simp [BoxOptionalRuntime.bufferPorts])).symm
    exact ⟨by simpa only [hw _ (species_ne_scratch (m + 1)).symm] using hz,
      ⟨by simpa only [hw _ (species_ne_next (m + 1)).symm] using hln,
        by simpa only [hw _ (species_ne_accumulator (m + 1)).symm] using hld,
        by simpa only [hw _ (species_ne_power (m + 1)).symm] using hhn,
        by simpa only [hw _ hsave] using hhd⟩,
      hR work work' (fun j _ _ _ _ hj => hw j hj) hr⟩
  have ht := FixedOutput.hoareTime conjunctionTag before ((FiniteCodec.optional DataCodec.box).code box ++ tail)
    emitted (Ready m L idx.val R)
  have hb := BoxOptionalRuntime.hoareTime m L ha box hsize idx before tail (emitted ++ conjunctionTag) R hR
  have hn := UnarySuccessor.hoareTime (species (m + 1)) idx.val
    (before ++ (FiniteCodec.optional DataCodec.box).code box) tail
    ((emitted ++ conjunctionTag) ++ (NetworkFormula.boxFormula box idx).code) P hP
  have hrest := seqTM_hoareTime (BoxOptionalRuntime.machine m) (UnarySuccessor.machine (species (m + 1))) hb (by
    rintro inp work out ⟨hc, hs, hz, hi, hbuf, hr⟩
    obtain ⟨hip, hw, ho⟩ := hc.phase
    rw [hip, hw, ho]
    exact ⟨hc, hs, hi, hz, hbuf, hr⟩) hn
  have hfull := seqTM_hoareTime (emitBitsTM conjunctionTag)
    (seqTM (BoxOptionalRuntime.machine m) (UnarySuccessor.machine (species (m + 1)))) ht (by
      rintro inp work out ⟨hc, _, hr⟩
      obtain ⟨hip, hw, ho⟩ := hc.phase
      rw [hip, hw, ho]
      exact ⟨hc, hr⟩) hrest
  exact hfull.consequence (fun _ _ _ ⟨hc, hr⟩ => ⟨hc, hr.1, hr⟩) (by
    rintro inp work out ⟨hc, hs, hi, hz, hbuf, hr⟩
    exact ⟨by simpa only [word, List.append_assoc] using hc, hs, hz, hi, hbuf, hr⟩) (by
      have hi := idx.isLt
      unfold BoxOptionalRuntime.timeBound SomeBoxBuild.timeBound timeBound
      simp only [conjunctionTag, List.length_cons, List.length_nil]
      omega)

end JointThermoComplexity.Complexity.BoxStep

#print axioms JointThermoComplexity.Complexity.BoxStep.hoareTime
