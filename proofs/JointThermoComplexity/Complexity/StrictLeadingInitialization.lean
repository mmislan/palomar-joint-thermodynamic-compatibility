module
public import proofs.JointThermoComplexity.Complexity.StrictInitialComposition
public import proofs.JointThermoComplexity.Complexity.UnaryBinderFramed
public import proofs.JointThermoComplexity.Complexity.StrictGeneratedBytes

set_option autoImplicit false
@[expose] public section

/-! Actual binder and leading strict terms, preserving the prepared original-row frame. -/

namespace JointThermoComplexity.Complexity.StrictLeadingInitialization
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DInstabilityComplexity.MachineConstruction StrictRowInitialization

def leadAddress (L n : ℕ) : ℕ :=
  (n + SourcePolynomialSchedules.scaleLength L + 1) * 2 + SourcePolynomialSchedules.thresholdLength L
def binder (L n : ℕ) : ℕ := leadAddress L n + 1
def rawPorts : Fin 2 → Fin 64 := ![42, 43]
def rawValues (L n : ℕ) : Fin 2 → ℕ := ![leadAddress L n, 0]
def kind (boxed : Bool) : StrictGeneratedTemplates.Kind := if boxed then .boxedLead else .unboxedLead

def Saved (L n scratch : ℕ) (work : Fin 64 → Tape) : Prop :=
  ∀ i, i ≠ 14 → i ≠ 15 → IsReg (StrictScheduleProgram.values L n scratch i)
    (work (StrictScheduleEntry.ports.index i))

def Extra (L n scratch : ℕ) (original : List Bool) (work : Fin 64 → Tape) : Prop :=
  Saved L n scratch work ∧ Register (leadAddress L n) (work 42) ∧
    Register 0 (work 43) ∧ Header original work

def Framed (L n : ℕ) (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) :
    _root_.Complexity.TM.TapePred 64 := fun inp work out =>
  RowEnergyStep.Logical rowPorts (state before input emitted)
    (n + SourcePolynomialSchedules.scaleLength L).bits (L + 2) (width L n) R inp work out ∧
    IsReg (L + 2) (work 29)

theorem square_ne_raw : ∀ a, rowPorts.square.index a ≠ 42 := by decide
theorem counter_ne_raw : ∀ i, StrictScheduleEntry.ports.index i ≠ 42 := by decide

theorem row_transport (s : RowEnergyControl.State) (scaleBits : List Bool) (B W : ℕ)
    (R T : (Fin 64 → Tape) → Prop) (work next : Fin 64 → Tape)
    (he : ∀ j, j ≠ 42 → next j = work j) (hs : ∀ j, Parked (next j))
    (hx : T next) (h : RowEnergyStep.Ready rowPorts s scaleBits B W R work) :
    RowEnergyStep.Ready rowPorts s scaleBits B W T next := by
  have hsq (a : Fin 28) : next (rowPorts.square.index a) = work (rowPorts.square.index a) :=
    he _ (square_ne_raw a)
  have hrow (a : Fin 25) : next (rowPorts.square.row.index a) = work (rowPorts.square.row.index a) := hsq _
  have hr : EquationRowFrame.Ready rowPorts.square.row s.row B T next := by
    refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hx⟩
    · intro i
      simpa only [EquationRowFrame.Ports.presence, hrow] using h.square.saved.presence i
    · intro i j
      simpa only [EquationRowFrame.Ports.flag, EquationRowFrame.Ports.slot, hrow] using h.square.saved.flags i j
    · intro i j
      simpa only [EquationRowFrame.Ports.word, EquationRowFrame.Ports.slot, hrow] using h.square.saved.words i j
    · intro i
      simpa only [EquationRowFrame.Ports.coefficient, EquationRowFrame.Ports.slot, hrow] using h.square.saved.coefficients i
    · simpa only [EquationRowFrame.Ports.available, hrow] using h.square.saved.available_head
    · simpa only [EquationRowFrame.Ports.available, hrow] using h.square.saved.available_read
    · simpa only [EquationRowFrame.Ports.loopAvailable, hrow] using h.square.saved.loop_head
    · simpa only [EquationRowFrame.Ports.scratch, hrow] using h.square.saved.scratch
    · simpa only [EquationRowFrame.Ports.fuel, hrow] using h.square.saved.fuel
  have hsquare : RowSquareFrame.Ready rowPorts.square s.row scaleBits B W T next :=
    ⟨hr, by simpa only [RowSquareFrame.Ports.scale, hsq] using h.square.scale,
      by simpa only [RowSquareFrame.Ports.scale, hsq] using h.square.scale_zero,
      h.square.scale_length, h.square.word_bound,
      by simpa only [RowSquareFrame.Ports.constant, hsq] using h.square.constant,
      by simpa only [RowSquareFrame.Ports.compare, hsq] using h.square.compare_head⟩
  exact ⟨hsquare, by simpa only [he _ (by decide : rowPorts.active ≠ 42)] using h.active_head,
    by simpa only [he _ (by decide : rowPorts.active ≠ 42)] using h.active_read⟩

theorem build_hoareTime (L n scratch : ℕ) (original before input emitted : List Bool) :
    (UnaryBinaryBuild.machine (37 : Fin 64) 42).HoareTime
      (Framed L n before input emitted (StrictRowInitialization.Extra L n scratch original))
      (Framed L n before input emitted (Extra L n scratch original))
      (leadAddress L n * (2 * leadAddress L n + 6) + (leadAddress L n + 2)) := by
  rintro inp work out ⟨⟨hc, hr⟩, hf⟩
  have hJ : IsReg (leadAddress L n) (work 37) := hr.square.saved.extra.1 9 (by decide) (by decide)
  have hz42 := hr.square.saved.extra.2.1
  have hz43 := hr.square.saved.extra.2.2.1
  have hraw : Register 0 (work 42) :=
    ⟨by simpa only [List.replicate_zero, Nat.zero_bits] using CountTape.string_of_register hz42, hz42.cell0⟩
  let C : (Fin 64 → Tape) → Prop := fun next => ∀ j, j ≠ 37 → j ≠ 42 → next j = work j
  have hC : ∀ a b, (∀ j, j ≠ 37 → j ≠ 42 → b j = a j) → C a → C b := by
    intro a b he ha j hj hk
    exact (he j hj hk).trans (ha j hj hk)
  have hbuild := UnaryBinaryBuildFramed.hoareTime (37 : Fin 64) 42 (by decide) (leadAddress L n)
    before input emitted C hC
  obtain ⟨d, t, ht, hd, hh, hc', hs, hJ', hb, he⟩ :=
    hbuild inp work out ⟨hc, hr.square.saved.safe, hJ, hraw, fun _ _ _ => rfl⟩
  have hother : ∀ j, j ≠ 42 → d.work j = work j := by
    intro j hj
    by_cases hfuel : j = 37
    · subst j
      exact hJ'.eq_regT.trans hJ.eq_regT.symm
    · exact he j hfuel hj
  have hx : Extra L n scratch original d.work := by
    refine ⟨fun i hi hf => ?_, hb, ?_, ?_⟩
    · simpa only [hother _ (counter_ne_raw i)] using hr.square.saved.extra.1 i hi hf
    · refine ⟨?_, ?_⟩
      · simpa only [hother 43 (by decide), List.replicate_zero, Nat.zero_bits] using CountTape.string_of_register hz43
      · simpa only [hother 43 (by decide)] using hz43.cell0
    · simpa only [Header, hother 62 (by decide), hother 63 (by decide)] using hr.square.saved.extra.2.2.2
  have hready := row_transport _ _ _ _ _ _ work d.work hother hs hx hr
  exact ⟨d, t, ht, hd, hh, ⟨hc', hready⟩, by simpa only [hother 29 (by decide)] using hf⟩

theorem binder_hoareTime (L n scratch : ℕ) (original before input emitted : List Bool) :
    (emitUnaryCodeTM (38 : Fin 64)).HoareTime
      (Framed L n before input emitted (StrictRowInitialization.Extra L n scratch original))
      (Framed L n before input (emitted ++ SparseListCodec.unaryCode (binder L n))
        (StrictRowInitialization.Extra L n scratch original)) (4 * binder L n + 4) := by
  let R : (Fin 64 → Tape) → Prop := fun work =>
    RowEnergyStep.Ready rowPorts (state before input emitted)
      (n + SourcePolynomialSchedules.scaleLength L).bits (L + 2) (width L n)
      (StrictRowInitialization.Extra L n scratch original) work ∧ IsReg (L + 2) (work 29)
  have h := UnaryBinderFramed.hoareTime (38 : Fin 64) (binder L n) before input emitted R
  exact h.consequence (by
    rintro inp work out ⟨⟨hc, hr⟩, hf⟩
    exact ⟨hc, hr.square.saved.safe, hr.square.saved.extra.1 10 (by decide) (by decide), hr, hf⟩) (by
    rintro inp work out ⟨hc, _, _, hr, hf⟩
    exact ⟨⟨hc, hr.square, hr.active_head, hr.active_read⟩, hf⟩) le_rfl

theorem emit_hoareTime (L n scratch W : ℕ) (hW : (leadAddress L n).bits.length ≤ W)
    (boxed : Bool) (original before input emitted : List Bool) :
    (StrictGeneratedBytes.machine rawPorts (kind boxed)).HoareTime
      (Framed L n before input emitted (Extra L n scratch original))
      (Framed L n before input
        (emitted ++ RowSquareCanonical.entries (StrictGeneratedTemplates.data (rawValues L n) (kind boxed)))
        (Extra L n scratch original)) (StrictGeneratedBytes.timeBound W (kind boxed)) := by
  let R : (Fin 64 → Tape) → Prop := fun work =>
    RowEnergyStep.Ready rowPorts (state before input emitted)
      (n + SourcePolynomialSchedules.scaleLength L).bits (L + 2) (width L n)
      (Extra L n scratch original) work ∧ IsReg (L + 2) (work 29)
  have hvalues : ∀ i, (rawValues L n i).bits.length ≤ W := by
    intro i
    fin_cases i
    · exact hW
    · change (0 : ℕ).bits.length ≤ W
      simp only [Nat.zero_bits, List.length_nil]
      exact Nat.zero_le _
  have h := StrictGeneratedBytes.hoareTime rawPorts (rawValues L n) W hvalues (kind boxed) before input emitted R
  exact h.consequence (by
    rintro inp work out ⟨⟨hc, hr⟩, hf⟩
    refine ⟨hc, hr.square.saved.safe, ?_, hr, hf⟩
    intro i
    fin_cases i
    · exact hr.square.saved.extra.2.1
    · exact hr.square.saved.extra.2.2.1) (by
    rintro inp work out ⟨hc, _, _, hr, hf⟩
    exact ⟨⟨hc, hr.square, hr.active_head, hr.active_read⟩, hf⟩) le_rfl

def machine (boxed : Bool) : TM 64 := seqTM (emitUnaryCodeTM 38)
  (seqTM (UnaryBinaryBuild.machine 37 42) (StrictGeneratedBytes.machine rawPorts (kind boxed)))

def timeBound (L n W : ℕ) (boxed : Bool) : ℕ :=
  (4 * binder L n + 4) + 1 + (leadAddress L n * (2 * leadAddress L n + 6) + (leadAddress L n + 2) + 1 +
    StrictGeneratedBytes.timeBound W (kind boxed))

theorem hoareTime (L n scratch W : ℕ) (hW : (leadAddress L n).bits.length ≤ W)
    (boxed : Bool) (original before input emitted : List Bool) :
    (machine boxed).HoareTime
      (Framed L n before input emitted (StrictRowInitialization.Extra L n scratch original))
      (Framed L n before input
        ((emitted ++ SparseListCodec.unaryCode (binder L n)) ++
          RowSquareCanonical.entries (StrictGeneratedTemplates.data (rawValues L n) (kind boxed)))
        (Extra L n scratch original)) (timeBound L n W boxed) := by
  have hb := binder_hoareTime L n scratch original before input emitted
  have hr := build_hoareTime L n scratch original before input (emitted ++ SparseListCodec.unaryCode (binder L n))
  have he := emit_hoareTime L n scratch W hW boxed original before input
    (emitted ++ SparseListCodec.unaryCode (binder L n))
  have hrest := seqTM_hoareTime _ _ hr (by
    rintro inp work out ⟨⟨hc, hr⟩, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨⟨hc, hr⟩, hf⟩) he
  exact seqTM_hoareTime _ _ hb (by
    rintro inp work out ⟨⟨hc, hr⟩, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨⟨hc, hr⟩, hf⟩) hrest

end JointThermoComplexity.Complexity.StrictLeadingInitialization

#print axioms JointThermoComplexity.Complexity.StrictLeadingInitialization.row_transport
#print axioms JointThermoComplexity.Complexity.StrictLeadingInitialization.build_hoareTime
#print axioms JointThermoComplexity.Complexity.StrictLeadingInitialization.hoareTime
