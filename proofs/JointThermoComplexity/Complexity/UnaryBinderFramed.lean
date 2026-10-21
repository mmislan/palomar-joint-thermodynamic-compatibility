module
public import proofs.JointThermoComplexity.Complexity.CounterProgramFrame
public import proofs.JointThermoComplexity.Complexity.FixedOutput
public import proofs.JointThermoComplexity.Complexity.SparseListCodec
public import proofs.DInstabilityComplexity.UnaryCodeEmitter

set_option autoImplicit false
@[expose] public section

/-! Unary binder output from a named counter retains the entire physical work frame. -/

namespace JointThermoComplexity.Complexity.UnaryBinderFramed
open _root_.Complexity _root_.Complexity.TM HeaderAt
open DInstabilityComplexity.MachineConstruction
variable {w : ℕ}

theorem unaryCode_eq (v : ℕ) : SparseListCodec.unaryCode v = List.replicate v true ++ [false] := by
  induction v with
  | zero => rfl
  | succ v ih => simp only [SparseListCodec.unaryCode, List.replicate_succ, List.cons_append, ih]

theorem hoareTime (r : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (emitUnaryCodeTM r).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg v (work r) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ SparseListCodec.unaryCode v) inp work out ∧
        (∀ j, Parked (work j)) ∧ IsReg v (work r) ∧ R work) (4 * v + 4) := by
  rintro inp work out ⟨hc, hs, hv, hx⟩
  have h := emitUnaryCodeTM_hoareTime r v inp work emitted (CounterProgramFrame.input_parked hc) hs hv.eq_regT
  obtain ⟨d, t, ht, hr, hh, hi, hw, ho⟩ := h inp work out ⟨rfl, rfl, CounterProgramFrame.output_acc hc⟩
  have hprefix := (FixedOutput.outAcc_iff _ d.output).mp ho
  have hdSafe : ∀ j, Parked (d.work j) := by rw [hw]; exact hs
  have hdCur : Cursor before input (emitted ++ SparseListCodec.unaryCode v) d.input d.work d.output :=
    ⟨by rw [hi]; exact hc.cells, by rw [hi]; exact hc.head,
      (fun j => ⟨(hdSafe j).read_ne_start, (hdSafe j).1⟩),
      by simpa only [unaryCode_eq] using hprefix.1, hprefix.2⟩
  exact ⟨d, t, ht, hr, hh, hdCur, hdSafe, by rw [hw]; exact hv, by rw [hw]; exact hx⟩

end JointThermoComplexity.Complexity.UnaryBinderFramed

#print axioms JointThermoComplexity.Complexity.UnaryBinderFramed.hoareTime
