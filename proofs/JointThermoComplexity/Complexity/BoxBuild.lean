module
public import proofs.JointThermoComplexity.Complexity.BoxLoopEntry
public import proofs.JointThermoComplexity.Complexity.BoxDenseCode

set_option autoImplicit false
@[expose] public section

/-! The retained species loop emits the complete exact allFin rational-box formula, including its final truth. -/

namespace JointThermoComplexity.Complexity.BoxBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxState NetworkData CurrentTraversal

theorem fuel_separate (m : ℕ) : Separate m (MonomialFuel.slot (m + 1)) :=
  ⟨(MonomialFuel.slot_separate (m + 1)).species, (MonomialFuel.slot_separate (m + 1)).scratch,
    (MonomialFuel.slot_separate (m + 1)).next, (MonomialFuel.slot_separate (m + 1)).accumulator,
    (MonomialFuel.slot_separate (m + 1)).power, (ReactionPorts.saved_ne_fuel m).symm⟩

def machine (m : ℕ) : TM (m + 15) :=
  seqTM (BoxLoop.machine m (MonomialFuel.slot (m + 1))) (emitBitsTM [false, false, false])

def timeBound (L : ℕ) : ℕ := 128 * L ^ 3 + 268 * L ^ 2 + 274 * L + 6

theorem hoareTime {n arity : ℕ} (m L : ℕ) (ha : arity ≤ 4 * L) (hn : n ≤ L)
    (boxes : Fin n → Option ClosedBox) (hsize : ∀ i, BoxOptionalRuntime.Bounded L (boxes i))
    (indices : Fin n → Fin arity) (hindices : ∀ i, (indices i).val = i.val)
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before ((FiniteCodec.finiteFunction (FiniteCodec.optional DataCodec.box) n).code boxes ++ tail)
        emitted inp work out ∧ Ready m L 0 R work ∧ IsReg n (work (MonomialFuel.slot (m + 1))))
      (fun inp work out => Cursor (before ++ (FiniteCodec.finiteFunction (FiniteCodec.optional DataCodec.box) n).code boxes) tail
        (emitted ++ (BoxDenseCode.formula boxes indices).code) inp work out ∧ Ready m L n R work ∧
        IsReg n (work (MonomialFuel.slot (m + 1)))) (timeBound L) := by
  have hitems : ∀ box ∈ List.ofFn boxes, BoxOptionalRuntime.Bounded L box := by
    intro box hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact hsize i
  have hl := BoxLoopEntry.hoareTime m L ha hn (MonomialFuel.slot (m + 1)) (fuel_separate m)
    indices hindices (List.ofFn boxes) (by simp only [List.length_ofFn]) hitems
    (BoxDenseCode.clauses boxes indices) (BoxDenseCode.clauses_length boxes indices) (BoxDenseCode.clause_at boxes indices)
    before tail emitted R hR
  have ht := FixedOutput.hoareTime [false, false, false] (before ++ BoxRecordTraversal.code (List.ofFn boxes)) tail
    (emitted ++ output (BoxDenseCode.clauses boxes indices))
    (fun work => Ready m L n R work ∧ IsReg n (work (MonomialFuel.slot (m + 1))))
  have hs := seqTM_hoareTime (BoxLoop.machine m (MonomialFuel.slot (m + 1))) (emitBitsTM [false, false, false]) hl (by
    rintro inp work out ⟨hc, hr, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr.1, hr, hf⟩) ht
  exact hs.consequence (by
    rintro inp work out ⟨hc, hr, hf⟩
    exact ⟨by simpa only [BoxDenseCode.finiteFunction_code] using hc, hr, hf⟩) (by
      rintro inp work out ⟨hc, _, hr, hf⟩
      refine ⟨?_, hr, hf⟩
      rw [BoxDenseCode.finiteFunction_code, ← BoxDenseCode.output_eq]
      simpa only [List.append_assoc] using hc) (by
        unfold timeBound BoxLoopEntry.timeBound
        simp only [List.length_cons, List.length_nil]
        omega)

end JointThermoComplexity.Complexity.BoxBuild

#print axioms JointThermoComplexity.Complexity.BoxBuild.hoareTime
