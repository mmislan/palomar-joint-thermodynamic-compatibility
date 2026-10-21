module
public import proofs.JointThermoComplexity.Complexity.SmallIntegerStreamCode

set_option autoImplicit false
@[expose] public section

/-! An actual sign reader and retained branch add negation before the linear magnitude expansion. -/

namespace JointThermoComplexity.Complexity.SmallIntegerStreamRun
open _root_.Complexity _root_.Complexity.TM HeaderAt SmallIntegerStream
variable {w : ℕ}

def Kept (data flag : Fin w) (R : (Fin w → Tape) → Prop) (work : Fin w → Tape) : Prop :=
  (work data).head = 1 ∧ (work flag).head = 1 ∧ R work
def Extra (data flag : Fin w) (R : (Fin w → Tape) → Prop) (work : Fin w → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ Kept data flag R work

def negativeMachine (w : ℕ) : TM w := seqTM (emitBitsTM (signPrefix true)) (SmallLiteralStreamMachine.machine w)
def branch (data : Fin w) : TM w := FlagBranch.machine data (negativeMachine w) (SmallLiteralStreamMachine.machine w)
def machine (data flag : Fin w) : TM w := seqTM (SourceBitRead.machine data flag) (branch data)

theorem branch_hoareTime (data flag : Fin w) (negative : Bool) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (branch data).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Extra data flag R work ∧
        (work data).read = Γ.ofBool negative)
      (fun inp work out => Cursor (before ++ (SmallLiteralStream.scan input).taken) (SmallLiteralStream.scan input).rest
        ((emitted ++ signPrefix negative) ++ SmallLiteralStream.output (SmallLiteralStream.scan input).bits) inp work out ∧
          Extra data flag R work) (12 * input.length + 11) := by
  cases negative with
  | false =>
    have hp := SmallLiteralStreamRun.hoareTime before input emitted (Kept data flag R)
    have hb := FlagBranchRun.no_hoareTime data (negativeMachine w) (SmallLiteralStreamMachine.machine w)
      before input emitted (before ++ (SmallLiteralStream.scan input).taken) (SmallLiteralStream.scan input).rest
      (emitted ++ SmallLiteralStream.output (SmallLiteralStream.scan input).bits)
      (Extra data flag R) (Extra data flag R) (12 * input.length + 6) hp
    exact hb.consequence (by rintro inp work out ⟨hc, he, hv⟩; exact ⟨⟨hc, he⟩, hv⟩)
      (by intro inp work out hp; simpa only [signPrefix, Bool.false_eq_true, ↓reduceIte, List.append_nil] using hp) (by omega)
  | true =>
    have he := FixedOutput.hoareTime (signPrefix true) before input emitted (Kept data flag R)
    have hp := SmallLiteralStreamRun.hoareTime before input (emitted ++ signPrefix true) (Kept data flag R)
    have hn := seqTM_hoareTime (emitBitsTM (n := w) (signPrefix true)) (SmallLiteralStreamMachine.machine w) he (by
      rintro inp work out ⟨hc, hs, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, hr⟩) hp
    have hn' : (negativeMachine w).HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ Extra data flag R work)
        (fun inp work out => Cursor (before ++ (SmallLiteralStream.scan input).taken) (SmallLiteralStream.scan input).rest
          ((emitted ++ signPrefix true) ++ SmallLiteralStream.output (SmallLiteralStream.scan input).bits) inp work out ∧
            Extra data flag R work) (12 * input.length + 10) := hn.mono_bound (by change 3 + 1 + (12 * input.length + 6) ≤ _; omega)
    have hb := FlagBranchRun.yes_hoareTime data (negativeMachine w) (SmallLiteralStreamMachine.machine w)
      before input emitted (before ++ (SmallLiteralStream.scan input).taken) (SmallLiteralStream.scan input).rest
      ((emitted ++ signPrefix true) ++ SmallLiteralStream.output (SmallLiteralStream.scan input).bits)
      (Extra data flag R) (Extra data flag R) (12 * input.length + 10) hn'
    exact hb.consequence (by rintro inp work out ⟨hc, he, hv⟩; exact ⟨⟨hc, he⟩, hv⟩) (fun _ _ _ hp => hp) le_rfl

theorem hoareTime (data flag : Fin w) (hne : data ≠ flag) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ data → j ≠ flag → work' j = work j) → R work → R work') :
    (machine data flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Extra data flag R work)
      (fun inp work out => Cursor (before ++ taken input) (rest input) (emitted ++ output input) inp work out ∧
        Extra data flag R work) (12 * input.length + 13) := by
  have hs := SourceBitRead.hoareTime data flag hne before input emitted R hR
  have hb := branch_hoareTime data flag (SourceBitRead.value input) (before ++ BooleanMachine.copied input)
    (BooleanMachine.suffix input) emitted R
  have hfull := seqTM_hoareTime (SourceBitRead.machine data flag) (branch data) hs (by
    rintro inp work out ⟨hc, hs, hd, hf, hv, _ha, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, ⟨hs, hd, hf, hr⟩, hv⟩) hb
  have hlen := suffix_bound input
  exact hfull.consequence (fun _ _ _ hp => hp) (by
    intro inp work out hp
    simpa only [taken, rest, output, List.append_assoc] using hp) (by omega)

theorem encoded_hoareTime (n : ℕ) (data flag : Fin w) (hne : data ≠ flag) (z : ℤ)
    (before suffix emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ data → j ≠ flag → work' j = work j) → R work → R work') :
    (machine data flag).HoareTime
      (fun inp work out => Cursor before (BitCodec.integerCode z ++ suffix) emitted inp work out ∧ Extra data flag R work)
      (fun inp work out => Cursor (before ++ BitCodec.integerCode z) suffix
        (emitted ++ (SourceSmallLiterals.integerTerm z : RealSyntax.Term n).code) inp work out ∧ Extra data flag R work)
      (12 * (BitCodec.integerCode z ++ suffix).length + 13) := by
  obtain ⟨ht, hr, ho⟩ := code_result n z suffix
  simpa only [ht, hr, ho] using hoareTime data flag hne before (BitCodec.integerCode z ++ suffix) emitted R hR

end JointThermoComplexity.Complexity.SmallIntegerStreamRun

#print axioms JointThermoComplexity.Complexity.SmallIntegerStreamRun.hoareTime
#print axioms JointThermoComplexity.Complexity.SmallIntegerStreamRun.encoded_hoareTime
