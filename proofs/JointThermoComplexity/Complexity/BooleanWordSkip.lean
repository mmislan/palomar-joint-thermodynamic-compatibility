module
public import proofs.JointThermoComplexity.Complexity.BooleanSkip

set_option autoImplicit false
@[expose] public section

/-! Count-controlled traversal of a Boolean word, including the empty word. -/

namespace JointThermoComplexity.Complexity.BooleanWordSkip
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InvariantLoop

variable {w : ℕ}

def machine (r : Fin w) : TM w := forRegTM BooleanSkip.machine r

def Invariant (bits before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop)
    (i : ℕ) : _root_.Complexity.TapePred w :=
  fun inp work out => Cursor (before ++ bits.take i) (bits.drop i ++ tail) emitted inp work out ∧ R work out

theorem framed (r : Fin w) (bits before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (machine r).HoareTime
      (Frame r bits.length 1 (Invariant bits before tail emitted R 0))
      (Frame r bits.length 1 (Invariant bits before tail emitted R bits.length))
      (4 * bits.length + 2) := by
  have hb : ∀ i, i < bits.length → (BooleanSkip.machine (w := w)).HoareTime
      (Frame r bits.length (i + 2) (Invariant bits before tail emitted R i))
      (Frame r bits.length (i + 2) (Invariant bits before tail emitted R (i + 1))) 1 := by
    intro i hi
    have hdrop : bits.drop i = bits[i] :: bits.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hs := BooleanSkip.framed r bits.length (i + 2) (by omega) bits[i]
      (before ++ bits.take i) (bits.drop (i + 1) ++ tail) emitted R
    exact hs.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, hdrop, List.cons_append] using hp.invariant) (by
        intro inp work out hp
        refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_, hp.invariant.2⟩
        simpa only [Invariant, List.take_succ_eq_append_getElem hi, List.append_assoc] using hp.invariant.1) le_rfl
  have hs := InvariantLoop.hoareTime (BooleanSkip.machine (w := w)) r
    (Invariant bits before tail emitted R) 1 bits.length hb
  exact hs.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega)

theorem hoareTime (r : Fin w) (bits before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (machine r).HoareTime
      (fun inp work out => Cursor before (bits ++ tail) emitted inp work out ∧
        IsReg bits.length (work r) ∧ R work out)
      (fun inp work out => Cursor (before ++ bits) tail emitted inp work out ∧
        IsReg bits.length (work r) ∧ R work out) (4 * bits.length + 2) := by
  exact (framed r bits before tail emitted R).consequence (by
    rintro inp work out ⟨hc, hr, hp⟩
    refine ⟨hr.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work r bits.length hr.eq_regT]
    simpa only [Invariant, List.take_zero, List.drop_zero, List.append_nil] using And.intro hc hp) (by
      intro inp work out hp
      have h := hp.on_work
      exact ⟨by simpa only [Invariant, List.take_length, List.drop_length, List.nil_append] using h.1,
        hp.register, h.2⟩) le_rfl

end JointThermoComplexity.Complexity.BooleanWordSkip

#print axioms JointThermoComplexity.Complexity.BooleanWordSkip.hoareTime
