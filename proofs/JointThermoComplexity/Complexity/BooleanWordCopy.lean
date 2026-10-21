module
public import proofs.JointThermoComplexity.Complexity.BooleanCopyFrame

set_option autoImplicit false
@[expose] public section

/-! Copy a fixed-count Boolean vector using its actual input symbols and restore the count register. -/

namespace JointThermoComplexity.Complexity.BooleanWordCopy
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InvariantLoop

variable {w : ℕ}

def machine (fuel : Fin w) : TM w := forRegTM BooleanCopy.machine fuel

def Invariant (bits before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) (i : ℕ) :
    _root_.Complexity.TapePred w :=
  fun inp work out => Cursor (before ++ bits.take i) (bits.drop i ++ tail) (emitted ++ bits.take i) inp work out ∧ R work

theorem hoareTime (fuel : Fin w) (bits before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine fuel).HoareTime
      (fun inp work out => Cursor before (bits ++ tail) emitted inp work out ∧ IsReg bits.length (work fuel) ∧ R work)
      (fun inp work out => Cursor (before ++ bits) tail (emitted ++ bits) inp work out ∧ IsReg bits.length (work fuel) ∧ R work)
      (4 * bits.length + 2) := by
  have hb : ∀ i, i < bits.length → (BooleanCopy.machine (w := w)).HoareTime
      (Frame fuel bits.length (i + 2) (Invariant bits before tail emitted R i))
      (Frame fuel bits.length (i + 2) (Invariant bits before tail emitted R (i + 1))) 1 := by
    intro i hi
    have hs := BooleanCopyFrame.hoareTime fuel bits.length (i + 2) (by omega) bits[i]
      (before ++ bits.take i) (bits.drop (i + 1) ++ tail) (emitted ++ bits.take i) R
    exact hs.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, List.drop_eq_getElem_cons hi, List.cons_append] using hp.invariant) (by
        intro inp work out hp
        refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
        simpa only [Invariant, List.take_succ_eq_append_getElem hi, List.append_assoc] using hp.invariant) le_rfl
  have hs := InvariantLoop.hoareTime (BooleanCopy.machine (w := w)) fuel
    (Invariant bits before tail emitted R) 1 bits.length hb
  exact hs.consequence (by
    rintro inp work out ⟨hc, hf, hr⟩
    refine ⟨hf.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work fuel bits.length hf.eq_regT]
    simpa only [Invariant, List.take_zero, List.drop_zero, List.append_nil] using And.intro hc hr) (by
      intro inp work out hp
      have h := hp.on_work
      exact ⟨by simpa only [Invariant, List.take_length, List.drop_length, List.nil_append] using h.1,
        hp.register, h.2⟩) (by omega)

end JointThermoComplexity.Complexity.BooleanWordCopy

#print axioms JointThermoComplexity.Complexity.BooleanWordCopy.hoareTime
