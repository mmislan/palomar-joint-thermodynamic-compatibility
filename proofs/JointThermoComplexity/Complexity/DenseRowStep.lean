module
public import proofs.JointThermoComplexity.Complexity.DenseRowFrame

set_option autoImplicit false
@[expose] public section

/-! One actual precompiled row step prepares the successor, emits its complete
raw record and advances the current index, returning a reusable boundary. -/

namespace JointThermoComplexity.Complexity.DenseRowStep
open _root_.Complexity _root_.Complexity.TM
open DenseRowFrame DenseComplexOriginal

def machine (right : Bool) (external : TM 64) (t : ℤ) : TM 64 :=
  seqTM BinaryCycleSuccessor.machine (DenseRecordAdvance.machine (DenseRegularRecord.machine right external t))
def timeBound (right : Bool) (N B E : ℕ) : ℕ := DenseRegularRecord.timeBound right N B E + 40 * B + 80

theorem hoareTime (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N B : ℕ) (i : Fin (N + 2))
    (u : ℕ) (e : ℕ) (gamma : Fin e → ℕ) (external : TM 64) (E : ℕ)
    (he : DenseComplexCore.Emits external m hm values n (FiniteCodec.functionCode FiniteCodec.natural gamma) E)
    (t : ℤ) (v : ℕ) (negative : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (hI : i.val.bits.length ≤ B) (hM : (vertex true i).val.bits.length ≤ B)
    (hend : (N + 1).bits.length ≤ B) (hu : u.bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (before input emitted : List Bool) :
    (machine right external t).HoareTime (At i.val u m hm values n N v negative before input emitted R)
      (At (i.val + 1) (vertex true i).val m hm values n N v negative before input
        (emitted ++ DenseRawRecord.word right N i e gamma t v negative) R) (timeBound right N B E) := by
  have hp := DenseRecordPrepare.hoareTime m hm values n N i u B hI hend hu before input emitted (Source v negative R)
    (source_cycle v negative R hR)
  have h1 := hp.consequence (cycle_pre m hm values n N v negative i u before input emitted R)
    (prepared m hm values n N v negative i before input emitted R) le_rfl
  have hr := DenseRawRecord.advanced_hoareTime right m hm values n N B i e gamma external E he t v negative hB ht hI hM
    (EndFrame N R) (end_complex false N R hR) (end_complex true N R hR) (end_factor N R hR) (end_increment N R hR)
    before input emitted
  have h2 := hr.consequence (fun _ _ _ h => h)
    (advanced m hm values n N v negative i before input (emitted ++ DenseRawRecord.word right N i e gamma t v negative) R) le_rfl
  have hh := seqTM_hoareTime _ _ h1 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) h2
  exact hh.mono_bound (by unfold timeBound; omega)

end JointThermoComplexity.Complexity.DenseRowStep

#print axioms JointThermoComplexity.Complexity.DenseRowStep.hoareTime
