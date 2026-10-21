module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaTagRead

set_option autoImplicit false
@[expose] public section

/-! An actual total formula-head and pending-count step, including truncated tag rejection. -/

namespace JointThermoComplexity.Complexity.SourceFormulaStep
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters SourceFormulaScan
variable {n : ℕ}

def afterStep (arity L v : ℕ) (before input : List Bool) : SourceTermLoopState.State :=
  ⟨before ++ SourceFormulaToken.taken arity L input, SourceFormulaToken.rest arity L input,
    if SourceFormulaToken.accepted arity L input then v + (classify (SourceTermToken.tagBits input)).children else v + 1,
    SourceFormulaToken.accepted arity L input⟩

def presenceMachine (d : Layout n) : TM (n + 2) :=
  FlagBranch.machine (NaturalScanBuffer.flag n) (SourceFormulaBranches.dispatchMachine d) (emitBitsTM [])

def machine (d : Layout n) : TM (n + 2) := seqTM (SourceFormulaTagRead.machine d) (presenceMachine d)
def timeBound (L v : ℕ) : ℕ := SourceFormulaBranches.timeBound L v + 14

theorem presence_hoareTime (d : Layout n) (L arity v : ℕ) (ha : arity.bits.length ≤ L)
    (before source emitted : List Bool) (hlen : source.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R) :
    (presenceMachine d).HoareTime
      (fun inp work out => Inv d L arity emitted R (SourceFormulaTagRead.afterTag (v + 1) before source) inp work out ∧
        SourceTagDispatch.Reads (List.ofFn (fun i => (d.tags i).castSucc)) (SourceTermToken.tagBits source) work)
      (Inv d L arity emitted R (afterStep arity L v before source)) (SourceFormulaBranches.timeBound L v + 7) := by
  cases htag : SourceTags.accepted source with
  | false =>
    let P : (Fin (n + 2) → Tape) → Prop := fun work => Ready d L arity R work ∧
      IsReg (v + 1) (work d.formulaPending.castSucc) ∧ (work (NaturalScanBuffer.flag n)).read = Γ.zero
    have hem := FixedOutput.hoareTime (w := n + 2) [] (before ++ source.take 3) (source.drop 3) emitted P
    have hno : (emitBitsTM (n := n + 2) []).HoareTime
        (fun inp work out => Cursor (before ++ source.take 3) (source.drop 3) emitted inp work out ∧ P work)
        (fun inp work out => Cursor (before ++ source.take 3) (source.drop 3) emitted inp work out ∧ P work) 0 :=
      hem.consequence (by rintro inp work out ⟨hc, hr, hp⟩; exact ⟨hc, hr.base.safe, hr, hp⟩)
        (by simpa only [List.append_nil] using fun _ _ _ h => ⟨h.1, h.2.2⟩) le_rfl
    have hb := FlagBranchRun.no_hoareTime (NaturalScanBuffer.flag n) (SourceFormulaBranches.dispatchMachine d) (emitBitsTM [])
      (before ++ source.take 3) (source.drop 3) emitted (before ++ source.take 3) (source.drop 3) emitted P P 0 hno
    exact hb.consequence (by
      rintro inp work out ⟨⟨hc, hr, hp, hf⟩, _ht⟩
      have hf' : (work (NaturalScanBuffer.flag n)).read = Γ.zero := by simpa only [SourceFormulaTagRead.afterTag, htag, Γ.ofBool] using hf
      exact ⟨⟨hc, hr, hp, hf'⟩, hf'⟩) (by
      intro inp work out h
      simpa only [SourceFormulaRegisters.Inv, P, afterStep, SourceFormulaToken.taken, SourceFormulaToken.rest, SourceFormulaToken.accepted,
        htag, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil, Γ.ofBool] using h) (by omega)
  | true =>
    let sb := SourceFormulaBranches.bodyState arity L v (SourceTermToken.tagBits source) (before ++ source.take 3) (source.drop 3)
    let P : (Fin (n + 2) → Tape) → Prop := fun work =>
      (Ready d L arity R work ∧ IsReg (v + 1) (work d.formulaPending.castSucc) ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.one) ∧
      SourceTagDispatch.Reads (List.ofFn (fun i => (d.tags i).castSucc)) (SourceTermToken.tagBits source) work
    let Q : (Fin (n + 2) → Tape) → Prop := fun work => Ready d L arity R work ∧
      IsReg sb.pending (work d.formulaPending.castSucc) ∧ (work (NaturalScanBuffer.flag n)).read = Γ.ofBool sb.valid
    have hdrop : (source.drop 3).length ≤ L := by rw [List.length_drop]; omega
    have hdis := SourceFormulaBranches.dispatch_hoareTime d (SourceTermToken.tagBits source) (by simp [SourceTermToken.tagBits])
      L arity v ha (before ++ source.take 3) (source.drop 3) emitted hdrop R hR
    have hy : (SourceFormulaBranches.dispatchMachine d).HoareTime
        (fun inp work out => Cursor (before ++ source.take 3) (source.drop 3) emitted inp work out ∧ P work)
        (fun inp work out => Cursor sb.before sb.input emitted inp work out ∧ Q work)
        (SourceFormulaBranches.timeBound L v + 6) :=
      hdis.consequence (by rintro inp work out ⟨hc, ⟨hr, hp, hf⟩, ht⟩; exact ⟨⟨hc, hr, hp, hf⟩, ht⟩)
        (fun _ _ _ h => h) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (NaturalScanBuffer.flag n) (SourceFormulaBranches.dispatchMachine d) (emitBitsTM [])
      (before ++ source.take 3) (source.drop 3) emitted sb.before sb.input emitted P Q (SourceFormulaBranches.timeBound L v + 6) hy
    exact hb.consequence (by
      rintro inp work out ⟨⟨hc, hr, hp, hf⟩, ht⟩
      have hf' : (work (NaturalScanBuffer.flag n)).read = Γ.one := by simpa only [SourceFormulaTagRead.afterTag, htag, Γ.ofBool] using hf
      exact ⟨⟨hc, ⟨hr, hp, hf'⟩, ht⟩, hf'⟩) (by
      intro inp work out h
      simpa only [SourceFormulaRegisters.Inv, Q, sb, SourceFormulaBranches.bodyState, afterStep, SourceFormulaToken.taken,
        SourceFormulaToken.rest, SourceFormulaToken.accepted, htag, ↓reduceIte, Bool.true_and, List.append_assoc] using h) (by omega)

theorem hoareTime (d : Layout n) (L arity v : ℕ) (ha : arity.bits.length ≤ L) (initial : Bool)
    (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop) (hR : Stable d R) :
    (machine d).HoareTime (Inv d L arity emitted R ⟨before, input, v + 1, initial⟩)
      (Inv d L arity emitted R (afterStep arity L v before input)) (timeBound L v) := by
  have ht := SourceFormulaTagRead.hoareTime d L arity (v + 1) initial before input emitted R hR
  have hb := presence_hoareTime d L arity v ha before input emitted hlen R hR
  have hfull := seqTM_hoareTime (SourceFormulaTagRead.machine d) (presenceMachine d) ht (by
    rintro inp work out ⟨⟨hc, hr, hp, hf⟩, hv⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨⟨hc, hr, hp, hf⟩, hv⟩) hb
  exact hfull.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold timeBound; omega)

theorem timeBound_eq (L v : ℕ) : timeBound L v = 34 * L ^ 2 + 93 * L + 2 * v + 60 := by
  unfold timeBound SourceFormulaBranches.timeBound
  omega

end JointThermoComplexity.Complexity.SourceFormulaStep

#print axioms JointThermoComplexity.Complexity.SourceFormulaStep.presence_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceFormulaStep.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceFormulaStep.timeBound_eq
