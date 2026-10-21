module
public import proofs.JointThermoComplexity.Complexity.SourceScannerPorts
public import proofs.JointThermoComplexity.Complexity.CounterInputEntry

set_option autoImplicit false
@[expose] public section

/-! Measure original input length into both fixed fuel tapes and initialize the source scanner from blank tapes. -/

namespace JointThermoComplexity.Complexity.SourceScannerInit
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters SourceScannerPorts

def Initial (input : List Bool) : _root_.Complexity.TM.TapePred 11 := fun inp work out =>
  inp = Tape.init (input.map Γ.ofBool) ∧ (∀ j, work j = Tape.init []) ∧ out = Tape.init []

def Prepared (input : List Bool) : _root_.Complexity.TM.TapePred 11 := fun inp work out =>
  Inv layout input.length 0 [] (fun _ => True) ⟨[], input, 0, false⟩ inp work out ∧
    IsReg 0 (work (NaturalScanBuffer.buffer 9)) ∧ IsReg input.length (work fuel.castSucc)

def lengthMachine : TM 11 :=
  seqTM (BoundedCounters.entry layout.termFuel.castSucc) (inputLenRegTM fuel.castSucc)

theorem length_hoareTime (input : List Bool) :
    lengthMachine.HoareTime (Initial input)
      (EmitPred ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩ (lengthWork input.length) []) (4 * input.length + 11) := by
  let first := BoundedCounters.inputWork layout.termFuel.castSucc input
  have hsafe : ∀ j, Parked (first j) := by
    intro j
    simp only [first, BoundedCounters.inputWork, Function.update_apply]
    split <;> exact parked_regTape _
  have hzero : first fuel.castSucc = regTape 0 := by
    exact Function.update_of_ne (by decide : fuel.castSucc ≠ layout.termFuel.castSucc) _ _
  have hfirst := BoundedCounters.entry_hoareTime layout.termFuel.castSucc input
  rw [BoundedCounters.inputWork_eq] at hfirst
  have hsecond := inputLenRegTM_hoareTime fuel.castSucc input first [] (fun j _ => hsafe j) hzero
  have hfull := seqTM_hoareTime (BoundedCounters.entry layout.termFuel.castSucc) (inputLenRegTM fuel.castSucc)
    hfirst (emitPred_transition (parked_init_input input) hsafe []) hsecond
  have heq : Function.update first fuel.castSucc (regTape input.length) = lengthWork input.length := by
    funext j
    by_cases hf : j = fuel.castSucc
    · subst j
      rw [Function.update_self, lengthWork_fuel]
    · by_cases ht : j = layout.termFuel.castSucc
      · subst j
        rw [Function.update_of_ne hf, lengthWork_termFuel]
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne hf, lengthWork_other input.length j ht hf]
        exact Function.update_of_ne ht _ _
  exact hfull.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hi, hw, ho⟩
    exact ⟨hi, hw.trans heq, ho⟩) (by omega)

theorem status_hoareTime (input : List Bool) :
    (SourceTermToken.setStatus (NaturalScanBuffer.flag 9) false).HoareTime
      (EmitPred ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩ (lengthWork input.length) []) (Prepared input) 1 := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  let C : (Fin 11 → Tape) → Prop := fun work =>
    ∀ j, j ≠ NaturalScanBuffer.flag 9 → work j = lengthWork input.length j
  have hC : ∀ work work', (∀ j, j ≠ NaturalScanBuffer.flag 9 → work' j = work j) → C work → C work' := by
    intro work work' he hp j hj
    exact (he j hj).trans (hp j hj)
  have hc : Cursor [] input [] ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩ (lengthWork input.length) out :=
    ⟨rfl, rfl, fun j => ⟨(lengthWork_safe input.length j).read_ne_start, (lengthWork_safe input.length j).1⟩,
      ((FixedOutput.outAcc_iff [] out).mp hout).1, hout.2.1⟩
  obtain ⟨c, t, ht, hd, hh, hc', hs', hfh, hfv, hother⟩ :=
    SourceTermToken.setStatus_hoareTime (NaturalScanBuffer.flag 9) false [] input [] C hC
      _ _ out ⟨hc, lengthWork_safe input.length, rfl, fun _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨lengthWork_markers input.length j, (lengthWork_safe input.length j).2⟩) (VirtualCursor.output_safe hc)
  have hzero (j : Fin 11) (ht : j ≠ layout.termFuel.castSucc) (hf : j ≠ fuel.castSucc)
      (hs : j ≠ NaturalScanBuffer.flag 9) : IsReg 0 (c.work j) := by
    rw [hother j hs, lengthWork_other input.length j ht hf]
    exact reg_regT 0
  have hencoded : IsReg 0 (c.work (NaturalScanBuffer.buffer 9)) := hzero _ (by decide) (by decide) (by decide)
  have hleft : IsReg 0 (c.work layout.left.castSucc) := hzero _ (by decide) (by decide) (by decide)
  have hright : IsReg 0 (c.work layout.right.castSucc) := hzero _ (by decide) (by decide) (by decide)
  have hterm : IsReg input.length (c.work layout.termFuel.castSucc) := by
    rw [hother _ (by decide), lengthWork_termFuel]
    exact reg_regT _
  have houter : IsReg input.length (c.work fuel.castSucc) := by
    rw [hother _ (by decide), lengthWork_fuel]
    exact reg_regT _
  have hr : Ready layout input.length 0 (fun _ => True) c.work :=
    ⟨⟨hs', fun j => (hm.2.1 j).1, BoxBufferState.of_register (by omega) hencoded,
      BoxBufferState.of_register (by omega) hleft,
      by simpa only [Nat.zero_bits, List.replicate_zero] using CountTape.string_of_register hright,
      hright.cell0, hfh, trivial⟩,
      hterm, ⟨0, by omega, hzero _ (by decide) (by decide) (by decide)⟩,
      fun i => by
        rw [hother _ (SourcePendingFrame.cast_ne (layout.tagSep.flag i))]
        rfl⟩
  exact ⟨c, t, ht, hd, hh, ⟨hc', hr, hzero _ (by decide) (by decide) (by decide), hfv⟩, hencoded, houter⟩

def machine : TM 11 := seqTM lengthMachine (SourceTermToken.setStatus (NaturalScanBuffer.flag 9) false)

theorem hoareTime (input : List Bool) : machine.HoareTime (Initial input) (Prepared input) (4 * input.length + 13) := by
  have hlength := length_hoareTime input
  have hstatus := status_hoareTime input
  have hfull := seqTM_hoareTime lengthMachine (SourceTermToken.setStatus (NaturalScanBuffer.flag 9) false) hlength
    (emitPred_transition (parked_init_input input) (lengthWork_safe input.length) []) hstatus
  exact hfull.mono_bound (by omega)

end JointThermoComplexity.Complexity.SourceScannerInit

#print axioms JointThermoComplexity.Complexity.SourceScannerInit.length_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceScannerInit.hoareTime
