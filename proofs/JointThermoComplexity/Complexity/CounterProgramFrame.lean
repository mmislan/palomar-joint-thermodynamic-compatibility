module
public import proofs.JointThermoComplexity.Complexity.CounterPlacement
public import proofs.JointThermoComplexity.Complexity.HeaderAt
public import proofs.DInstabilityComplexity.CounterProgramBounds

set_option autoImplicit false
@[expose] public section

/-! Actual counter programs retain the input cursor, output and every work tape
outside their selected unary registers, including parked binary buffers and flags. -/

namespace JointThermoComplexity.Complexity.CounterProgramFrame
open _root_.Complexity _root_.Complexity.TM
open DInstabilityComplexity.MachineConstruction
open HeaderAt (Cursor)
variable {n w : ℕ}

structure Ports (n w : ℕ) where
  index : Fin n → Fin w
  injective : Function.Injective index

def Stable (ports : Ports n w) (R : (Fin w → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, (∀ k, j ≠ ports.index k) → next j = work j) → R work → R next

def Logical (ports : Ports n w) (v : Fin n → ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred w := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
    (∀ k, IsReg (v k) (work (ports.index k))) ∧ R work

theorem input_parked {before input emitted : List Bool} {inp out : Tape} {work : Fin w → Tape}
    (hc : Cursor before input emitted inp work out) : Parked inp := by
  refine ⟨by rw [hc.head]; omega, ?_⟩
  intro j hj
  rw [hc.cells]
  exact Tape.init_ofBool_cells_ne_start _ j hj

theorem output_acc {before input emitted : List Bool} {inp out : Tape} {work : Fin w → Tape}
    (hc : Cursor before input emitted inp work out) : OutAcc emitted out := by
  refine ⟨hc.tapePrefix.1, hc.zero, hc.tapePrefix.2.1, ?_⟩
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact hc.tapePrefix.2.2 i (by omega)

theorem cursor_of_acc {before input emitted : List Bool} {inp out nextInp nextOut : Tape}
    {work nextWork : Fin w → Tape} (hc : Cursor before input emitted inp work out)
    (hi : nextInp = inp) (hsafe : ∀ j, Parked (nextWork j)) (ho : OutAcc emitted nextOut) :
    Cursor before input emitted nextInp nextWork nextOut := by
  refine ⟨by rw [hi]; exact hc.cells, by rw [hi]; exact hc.head,
    (fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩), ?_, ho.2.1⟩
  exact ⟨ho.1, ho.2.2.1, fun i hi => ho.2.2.2 (i + 1) (by omega)⟩

theorem instruction_hoareTime (ports : Ports n w) (i : CounterInstruction n)
    (v : Fin n → ℕ) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : Stable ports R) :
    (CounterPlacement.instruction ports.index ports.injective i).machine.HoareTime
      (Logical ports v before input emitted R)
      (Logical ports (i.eval v) before input emitted R) (i.time v) := by
  rintro inp work out ⟨hc, hs, hv, hx⟩
  have h := CounterPlacement.hoareTime ports.index ports.injective i v inp work emitted
    (input_parked hc) hs hv
  obtain ⟨d, t, ht, hr, hh, hi, hw, ho⟩ := h inp work out ⟨rfl, rfl, output_acc hc⟩
  have hsafe : ∀ j, Parked (d.work j) := by
    rw [hw]
    exact CounterPlacement.parked_updated ports.index i v work hs
  have hregs : ∀ k, IsReg (i.eval v k) (d.work (ports.index k)) := by
    rw [hw]
    exact CounterPlacement.registers_updated ports.index ports.injective i v work hv
  have hother : ∀ j, (∀ k, j ≠ ports.index k) → d.work j = work j := by
    intro j hj
    rw [hw]
    exact CounterPlacement.other_updated ports.index i v work j hj
  exact ⟨d, t, ht, hr, hh, cursor_of_acc hc hi hsafe ho, hsafe, hregs, hR work d.work hother hx⟩

def machine (ports : Ports n w) : CounterProgram n → TM w
  | [] => skipTM
  | i :: rest => seqTM (CounterPlacement.instruction ports.index ports.injective i).machine (machine ports rest)

theorem hoareTime (ports : Ports n w) (program : CounterProgram n)
    (v : Fin n → ℕ) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : Stable ports R) :
    (machine ports program).HoareTime (Logical ports v before input emitted R)
      (Logical ports (counterProgramEval program v) before input emitted R)
      (counterProgramTime program v) := by
  induction program generalizing v with
  | nil =>
    rintro inp work out ⟨hc, hs, hv, hx⟩
    obtain ⟨d, t, ht, hr, hh, hi, hw, ho⟩ :=
      skipTM_hoareTime inp work emitted (input_parked hc) hs inp work out ⟨rfl, rfl, output_acc hc⟩
    have hsafe : ∀ j, Parked (d.work j) := by rw [hw]; exact hs
    exact ⟨d, t, ht, hr, hh, cursor_of_acc hc hi hsafe ho, hsafe,
      by rw [hw]; exact hv, by rw [hw]; exact hx⟩
  | cons i rest ih =>
    have hfirst := instruction_hoareTime ports i v before input emitted R hR
    have hnext := ih (i.eval v)
    exact seqTM_hoareTime _ _ hfirst (by
      rintro inp work out ⟨hc, hs, hv, hx⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, hv, hx⟩) hnext

theorem bounded_hoareTime (ports : Ports n w) (program : CounterProgram n)
    (v : Fin n → ℕ) (B : ℕ) (hv : ∀ j, v j ≤ B) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable ports R) :
    (machine ports program).HoareTime (Logical ports v before input emitted R)
      (Logical ports (counterProgramEval program v) before input emitted R)
      (counterIterTime program.length B) :=
  (hoareTime ports program v before input emitted R hR).mono_bound
    (counterProgramTime_bound program v B hv)

end JointThermoComplexity.Complexity.CounterProgramFrame

#print axioms JointThermoComplexity.Complexity.CounterProgramFrame.instruction_hoareTime
#print axioms JointThermoComplexity.Complexity.CounterProgramFrame.hoareTime
#print axioms JointThermoComplexity.Complexity.CounterProgramFrame.bounded_hoareTime
