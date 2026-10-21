module
public import proofs.JointThermoComplexity.Complexity.RoutedEquationHeader
public import proofs.JointThermoComplexity.Complexity.CountTape

set_option autoImplicit false
@[expose] public section

/-! The actual blank-tape entry prepares every main/query field, retaining the routed old header on spare31. -/

namespace JointThermoComplexity.Complexity.EquationBootstrapState
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryCounterInit MainEquationWork
open HeaderAt (Cursor)

def values (L : ℕ) (j : Fin 32) : ℕ := if j = 7 then 1 else EquationLengthEntry.values L j
def work (L : ℕ) (j : Fin 32) : Tape := regTape (values L j)
def state (input : List Bool) : FormulaSpanControl.State := ⟨HeaderControl.copied input, HeaderControl.suffix input, 0, 1, 0⟩

def Kept (input : List Bool) (tapes : Work) : Prop :=
  ∀ j, j ≠ RoutedEquationHeader.arity → j ≠ RoutedEquationHeader.flag → j ≠ RoutedEquationHeader.sink → tapes j = work input.length j

structure HeaderReady (input : List Bool) (tapes : Work) : Prop where
  safe : ∀ j, Parked (tapes j)
  markers : ∀ j, (tapes j).cells 0 = Γ.start
  arityReg : IsReg (HeaderControl.count input) (tapes RoutedEquationHeader.arity)
  flagHead : (tapes RoutedEquationHeader.flag).head = 1
  flagValue : (tapes RoutedEquationHeader.flag).read = Γ.ofBool (HeaderControl.valid input)
  sinkPrefix : (tapes RoutedEquationHeader.sink).HasBinaryPrefix (HeaderControl.copied input)
  kept : Kept input tapes

theorem work_register (L : ℕ) (j : Fin 32) : IsReg (values L j) (work L j) := reg_regT _
theorem work_safe (L : ℕ) (j : Fin 32) : Parked (work L j) := (work_register L j).parked

theorem seed_hoareTime (input : List Bool) :
    (UnarySuccessor.machine (7 : Fin 32)).HoareTime
      (EmitPred ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩ (EquationLengthEntry.work input.length) [])
      (EmitPred ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩ (work input.length) []) 6 := by
  rintro inp tapes out ⟨rfl, rfl, hout⟩
  have ho := (FixedOutput.outAcc_iff [] out).mp hout
  have hc : Cursor [] input [] ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩ (EquationLengthEntry.work input.length) out :=
    ⟨rfl, rfl, fun j => ⟨(EquationLengthEntry.work_safe input.length j).read_ne_start,
      (EquationLengthEntry.work_safe input.length j).1⟩, ho.1, ho.2⟩
  let C : Work → Prop := fun tapes => ∀ j, j ≠ 7 → tapes j = EquationLengthEntry.work input.length j
  have hC : ∀ tapes tapes', (∀ j, j ≠ (7 : Fin 32) → tapes' j = tapes j) → C tapes → C tapes' := by
    intro tapes tapes' he hh j hj
    exact (he j hj).trans (hh j hj)
  have hz : IsReg 0 (EquationLengthEntry.work input.length 7) := by
    simpa [EquationLengthEntry.values] using EquationLengthEntry.work_register input.length 7
  obtain ⟨d, t, ht, hd, hh, hc', _, hreg, he⟩ :=
    UnarySuccessor.hoareTime (7 : Fin 32) 0 [] input [] C hC _ _ out
      ⟨hc, EquationLengthEntry.work_safe input.length, hz, fun _ _ => rfl⟩
  have hw : d.work = work input.length := by
    funext j
    by_cases hj : j = 7
    · subst j
      simpa only [work, values, ↓reduceIte, Nat.zero_add] using hreg.eq_regT
    · rw [he j hj]
      simp only [work, values, ite_eq_right hj, EquationLengthEntry.work]
  have hi : d.input = ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩ := by
    apply Tape.ext
    · simpa only [List.length_nil, Nat.zero_add] using hc'.head
    · simpa only [List.nil_append] using hc'.cells
  exact ⟨d, t, ht, hd, hh, hi, hw, (FixedOutput.outAcc_iff [] d.output).mpr ⟨hc'.tapePrefix, hc'.zero⟩⟩

theorem kept_stable (input : List Bool) : RoutedEquationHeader.Stable (Kept input) := by
  intro tapes tapes' he hh j ha hf hs
  exact (he j ha hf hs).trans (hh j ha hf hs)

theorem header_hoareTime (input : List Bool) :
    RoutedEquationHeader.machine.HoareTime
      (EmitPred ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩ (work input.length) [])
      (fun inp tapes out => Cursor (HeaderControl.copied input) (HeaderControl.suffix input) [] inp tapes out ∧ HeaderReady input tapes)
      (2 * HeaderControl.count input + 5) := by
  rintro inp tapes out ⟨rfl, rfl, hout⟩
  have ho := (FixedOutput.outAcc_iff [] out).mp hout
  have hc : Cursor [] input [] ⟨1, (Tape.init (input.map Γ.ofBool)).cells⟩ (work input.length) out :=
    ⟨rfl, rfl, fun j => ⟨(work_safe input.length j).read_ne_start, (work_safe input.length j).1⟩, ho.1, ho.2⟩
  have ha : IsReg 0 (work input.length RoutedEquationHeader.arity) := by
    simpa [values, EquationLengthEntry.values, RoutedEquationHeader.arity] using work_register input.length RoutedEquationHeader.arity
  have hf := (work_register input.length RoutedEquationHeader.flag).head_eq
  have hs : (work input.length RoutedEquationHeader.sink).HasBinaryString [] := by
    have hz : IsReg 0 (work input.length RoutedEquationHeader.sink) := by
      simpa [values, EquationLengthEntry.values, RoutedEquationHeader.sink] using work_register input.length RoutedEquationHeader.sink
    simpa only [List.replicate_zero] using CountTape.string_of_register hz
  obtain ⟨d, t, ht, hd, hh, hc', hs', hm', ha', hf', hv', hb', hk'⟩ :=
    RoutedEquationHeader.hoareTime [] input [] (Kept input) (kept_stable input) _ _ out
      ⟨hc, work_safe input.length, fun j => (work_register input.length j).cell0, ha, hf, hs, fun _ _ _ _ => rfl⟩
  exact ⟨d, t, ht, hd, hh, by simpa only [List.nil_append] using hc', hs', hm', ha', hf', hv', hb', hk'⟩

def machine : TM 32 := seqTM EquationLengthEntry.machine (seqTM (UnarySuccessor.machine 7) RoutedEquationHeader.machine)

theorem hoareTime (input : List Bool) :
    machine.HoareTime (EquationLengthEntry.Initial input)
      (fun inp tapes out => Cursor (HeaderControl.copied input) (HeaderControl.suffix input) [] inp tapes out ∧ HeaderReady input tapes)
      (8 * input.length + 32) := by
  have hs := seed_hoareTime input
  have hh := header_hoareTime input
  have hrest := seqTM_hoareTime (UnarySuccessor.machine (7 : Fin 32)) RoutedEquationHeader.machine hs
    (emitPred_transition (parked_init_input input) (work_safe input.length) []) hh
  have hseq := seqTM_hoareTime EquationLengthEntry.machine
    (seqTM (UnarySuccessor.machine 7) RoutedEquationHeader.machine) (EquationLengthEntry.hoareTime input)
    (emitPred_transition (parked_init_input input) (EquationLengthEntry.work_safe input.length) []) hrest
  apply hseq.mono_bound
  have hn := (HeaderControl.count_le_copied input).trans (HeaderControl.copied_length_le input)
  omega

theorem kept_register (input : List Bool) (tapes : Work) (hr : HeaderReady input tapes) (j : Fin 32)
    (ha : j ≠ RoutedEquationHeader.arity) (hf : j ≠ RoutedEquationHeader.flag) (hs : j ≠ RoutedEquationHeader.sink) :
    IsReg (values input.length j) (tapes j) := by
  rw [hr.kept j ha hf hs]
  exact work_register input.length j

theorem prepared (input : List Bool) (tapes : Work) (hr : HeaderReady input tapes) (R : Work → Prop) (hR : R tapes) :
    Before (state input) (HeaderControl.count input) input.length 0 EquationWorkReset.zeroCounts EquationWorkReset.zeroValues
      R tapes ∧ IsReg input.length (tapes EquationFuelFrame.fuel) := by
  have mainTags_kept : ∀ i, mainTags i ≠ RoutedEquationHeader.arity ∧ mainTags i ≠ RoutedEquationHeader.flag ∧ mainTags i ≠ RoutedEquationHeader.sink := by decide
  have queryTags_kept : ∀ i, QueryWorkFrame.tags i ≠ RoutedEquationHeader.arity ∧ QueryWorkFrame.tags i ≠ RoutedEquationHeader.flag ∧ QueryWorkFrame.tags i ≠ RoutedEquationHeader.sink := by decide
  have slots_kept : ∀ i, AddressCounterPlacement.slot i ≠ RoutedEquationHeader.arity ∧ AddressCounterPlacement.slot i ≠ RoutedEquationHeader.flag ∧ AddressCounterPlacement.slot i ≠ RoutedEquationHeader.sink := by decide
  have hmain : Frame (state input) (HeaderControl.count input) input.length 0 R tapes := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hR⟩
    · simpa [state, values, EquationLengthEntry.values, mainTerm, TermSpanRegisters.pending] using kept_register input tapes hr 3 (by decide) (by decide) (by decide)
    · simpa [state, values, EquationLengthEntry.values, mainFormula, FormulaSpanRegisters.formulaPending] using kept_register input tapes hr 7 (by decide) (by decide) (by decide)
    · simpa [state, values, EquationLengthEntry.values, mainCoordinates, TermSpanRegisters.nodeCounter] using kept_register input tapes hr 5 (by decide) (by decide) (by decide)
    · intro i
      exact (kept_register input tapes hr _ (mainTags_kept i).1 (mainTags_kept i).2.1 (mainTags_kept i).2.2).head_eq
    · exact (kept_register input tapes hr _ (by decide : mainFlag ≠ RoutedEquationHeader.arity)
        (by decide : mainFlag ≠ RoutedEquationHeader.flag) (by decide : mainFlag ≠ RoutedEquationHeader.sink)).head_eq
    · simpa [values, EquationLengthEntry.values, lengthPort] using kept_register input tapes hr 16 (by decide) (by decide) (by decide)
    · simpa only [arityPort, RoutedEquationHeader.arity] using hr.arityReg
    · simpa [values, EquationLengthEntry.values, adjustedPort] using kept_register input tapes hr 28 (by decide) (by decide) (by decide)
  have hbasic : LocalBranchState.Basic EquationWorkReset.zeroCounts input.length
      (Frame (state input) (HeaderControl.count input) input.length 0 R) tapes := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmain⟩
    · intro i
      exact (kept_register input tapes hr _ (queryTags_kept i).1 (queryTags_kept i).2.1 (queryTags_kept i).2.2).head_eq
    · rw [show QueryWorkFrame.flag = RoutedEquationHeader.flag from by decide]
      exact hr.flagHead
    · simpa [values, EquationLengthEntry.values, QueryWorkFrame.pending, EquationWorkReset.zeroCounts] using kept_register input tapes hr 11 (by decide) (by decide) (by decide)
    · simpa [values, EquationLengthEntry.values, QueryWorkFrame.formulas, EquationWorkReset.zeroCounts] using kept_register input tapes hr 15 (by decide) (by decide) (by decide)
    · simpa [values, EquationLengthEntry.values, QueryWorkFrame.result, EquationWorkReset.zeroCounts] using kept_register input tapes hr 13 (by decide) (by decide) (by decide)
    · simpa [values, EquationLengthEntry.values, QueryWorkFrame.fuel] using kept_register input tapes hr 12 (by decide) (by decide) (by decide)
    · simpa [values, EquationLengthEntry.values, QueryWorkFrame.position] using kept_register input tapes hr 17 (by decide) (by decide) (by decide)
    · simpa [values, EquationLengthEntry.values, LocalBranchState.scratch] using kept_register input tapes hr 29 (by decide) (by decide) (by decide)
  have haddr : AddressCounterPlacement.Registers EquationWorkReset.zeroValues tapes := by
    intro i
    have hreg := kept_register input tapes hr _ (slots_kept i).1 (slots_kept i).2.1 (slots_kept i).2.2
    have hv : values input.length (AddressCounterPlacement.slot i) = 0 := by
      fin_cases i <;> simp [values, EquationLengthEntry.values, AddressCounterPlacement.slot, placeWorkIdx]
    simpa only [hv, EquationWorkReset.zeroValues] using hreg
  refine ⟨⟨hr.safe, ?_, hbasic, fun j _ => hr.markers j, haddr⟩, ?_⟩
  · simpa [values, EquationLengthEntry.values, LocalBranchState.anchor] using kept_register input tapes hr 30 (by decide) (by decide) (by decide)
  · simpa [values, EquationLengthEntry.values, EquationFuelFrame.fuel, FormulaSpanLoop.fuel, TermSpanRegisters.fuel] using kept_register input tapes hr 4 (by decide) (by decide) (by decide)

end JointThermoComplexity.Complexity.EquationBootstrapState

#print axioms JointThermoComplexity.Complexity.EquationBootstrapState.hoareTime
#print axioms JointThermoComplexity.Complexity.EquationBootstrapState.prepared
