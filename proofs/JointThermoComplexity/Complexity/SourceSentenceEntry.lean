module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaStart

set_option autoImplicit false
@[expose] public section

/-! Compose the actual binder, arity build, pending reset and complete formula parser on a fixed initialized layout. -/

namespace JointThermoComplexity.Complexity.SourceSentenceEntry
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters
variable {n : ℕ}

def startState (before input : List Bool) : SourceTermLoopState.State :=
  ⟨before ++ HeaderControl.copied input, HeaderControl.suffix input, 1, HeaderControl.valid input⟩

def setupMachine (d : Layout (n + 1)) : TM (n + 3) :=
  seqTM (seqTM (SourceBinderReady.machine d) (SourceArityBuild.machine d)) (SourceFormulaStart.machine d)

def setupTimeBound (input : List Bool) : ℕ :=
  SourceArityBuild.timeBound (HeaderControl.count input) + 4 * HeaderControl.count input + 19

theorem setup_hoareTime (d : Layout (n + 1)) (L : ℕ) (old : Bool) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 2) → Tape) → Prop) (hR : Stable d R) :
    (setupMachine d).HoareTime
      (fun inp work out => Inv d L 0 emitted R ⟨before, input, 0, old⟩ inp work out ∧
        IsReg 0 (work (NaturalScanBuffer.buffer (n + 1))))
      (Inv d L (HeaderControl.count input) emitted R (startState before input)) (setupTimeBound input) := by
  have hh := SourceBinderReady.hoareTime d L old before input emitted hlen R hR
  have ha := SourceArityBuild.hoareTime d L (HeaderControl.count input) (HeaderControl.valid input)
    (before ++ HeaderControl.copied input) (HeaderControl.suffix input) emitted R hR
  have hs := SourceFormulaStart.hoareTime d L (HeaderControl.count input) (HeaderControl.count input)
    (HeaderControl.valid input) (before ++ HeaderControl.copied input) (HeaderControl.suffix input) emitted R hR
  have hha := seqTM_hoareTime (SourceBinderReady.machine d) (SourceArityBuild.machine d) hh (by
    rintro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) ha
  have hfull := seqTM_hoareTime (seqTM (SourceBinderReady.machine d) (SourceArityBuild.machine d))
    (SourceFormulaStart.machine d) hha (by
      rintro inp work out h
      obtain ⟨hi, hw, ho⟩ := h.1.phase
      rw [hi, hw, ho]
      exact h) hs
  exact hfull.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold setupTimeBound; omega)

theorem setupTimeBound_le (L : ℕ) (input : List Bool) (hlen : input.length ≤ L) :
    setupTimeBound input ≤ 2 * L ^ 2 + 11 * L + 21 := by
  have hc := (SourceBinderControl.input_bounds L input hlen).1
  have hb := SourceArityBuild.timeBound_le L (HeaderControl.count input) hc
  unfold setupTimeBound
  omega

def finalState (L : ℕ) (before input : List Bool) : SourceTermLoopState.State :=
  SourceFormulaEOF.finalState (HeaderControl.count input) L L (startState before input)

def machine (d : Layout (n + 1)) (fuel : Fin (n + 2)) : TM (n + 3) :=
  seqTM (setupMachine d) (SourceFormulaEOF.machine d fuel)

def timeBound (L : ℕ) (input : List Bool) : ℕ := setupTimeBound input + 1 + SourceFormulaEOF.timeBound L 1 L

theorem hoareTime (d : Layout (n + 1)) (fuel : Fin (n + 2)) (hfu : Outside d fuel)
    (L : ℕ) (old : Bool) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 2) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, Outside d j → j ≠ fuel → work' j = work j) → R work → R work') :
    (machine d fuel).HoareTime
      (fun inp work out => Inv d L 0 emitted R ⟨before, input, 0, old⟩ inp work out ∧
        IsReg 0 (work (NaturalScanBuffer.buffer (n + 1))) ∧ IsReg L (work fuel.castSucc))
      (fun inp work out => Inv d L (HeaderControl.count input) emitted R (finalState L before input) inp work out ∧
        IsReg L (work fuel.castSucc)) (timeBound L input) := by
  let RF : (Fin (n + 2) → Tape) → Prop := fun work => IsReg L (work fuel) ∧ R work
  have hRF : Stable d RF := by
    rintro work work' hw ⟨hf, hr⟩
    exact ⟨by simpa only [hw fuel hfu] using hf, hR _ _ (fun j hj _ => hw j hj) hr⟩
  have hsetup := setup_hoareTime d L old before input emitted hlen RF hRF
  have hbounds := SourceBinderControl.input_bounds L input hlen
  have hformula := SourceFormulaEOF.hoareTime d fuel hfu L (HeaderControl.count input) L hbounds.2.1
    emitted R (startState before input) hbounds.2.2.1 hR
  have hfull := seqTM_hoareTime (setupMachine d) (SourceFormulaEOF.machine d fuel) hsetup (by
    rintro inp work out ⟨hc, hr, hp, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨⟨hc, ⟨⟨hr.base.safe, hr.base.markers, hr.base.encoded, hr.base.candidate, hr.base.arityBits,
      hr.base.arityZero, hr.base.flagHead, hr.base.frame.2⟩, hr.termFuel, hr.termPending, hr.tagHeads⟩, hp, hf⟩,
      hr.base.frame.1⟩) hformula
  exact hfull.consequence (by
    rintro inp work out ⟨⟨hc, hr, hp, hf⟩, hb, hFuel⟩
    exact ⟨⟨hc, ⟨⟨hr.base.safe, hr.base.markers, hr.base.encoded, hr.base.candidate, hr.base.arityBits,
      hr.base.arityZero, hr.base.flagHead, hFuel, hr.base.frame⟩, hr.termFuel, hr.termPending, hr.tagHeads⟩, hp, hf⟩, hb⟩)
    (fun _ _ _ h => h) le_rfl

theorem cubic_timeBound (L : ℕ) (input : List Bool) (hlen : input.length ≤ L) :
    timeBound L input ≤ 34 * L ^ 3 + 97 * L ^ 2 + 78 * L + 29 := by
  have hs := setupTimeBound_le L input hlen
  unfold timeBound
  rw [SourceFormulaEOF.cubic_timeBound]
  omega

theorem status_criterion (L : ℕ) (input : List Bool) (hlen : input.length ≤ L) :
    (finalState L [] input).valid = true ↔ (RealSyntax.decodeSentence input).isSome = true :=
  SourceBinderControl.decode_criterion L input hlen

end JointThermoComplexity.Complexity.SourceSentenceEntry

#print axioms JointThermoComplexity.Complexity.SourceSentenceEntry.setup_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceSentenceEntry.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceSentenceEntry.cubic_timeBound
#print axioms JointThermoComplexity.Complexity.SourceSentenceEntry.status_criterion
