module
public import proofs.JointThermoComplexity.Complexity.SourceValidityRewind
public import proofs.JointThermoComplexity.Complexity.BooleanWordCopy
public import proofs.JointThermoComplexity.Complexity.SourceNormalization

set_option autoImplicit false
@[expose] public section

/-! An actual retained-status branch copies a valid source word or emits the fixed false sentence. -/

namespace JointThermoComplexity.Complexity.SourceNormalizationBranch
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceScannerPorts SourceValidityRewind

def code (input : List Bool) : List Bool :=
  if (RealSyntax.decodeSentence input).isSome then input else SourceNormalization.falseSentence.code

theorem code_eq_normalize (input : List Bool) : code input = (SourceNormalization.normalize input).code := by
  cases hd : RealSyntax.decodeSentence input with
  | none => simp only [code, hd, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, SourceNormalization.normalize_of_none hd]
  | some s =>
    have hi := RealSyntax.decodeSentence_sound hd
    rw [SourceNormalization.normalize_of_some hd]
    simpa only [code, hd, Option.isSome_some, ↓reduceIte] using hi

def machine : TM 11 := FlagBranch.machine (NaturalScanBuffer.flag 9) (BooleanWordCopy.machine fuel.castSucc)
  (emitBitsTM SourceNormalization.falseSentence.code)

def Post (input : List Bool) : _root_.Complexity.TM.TapePred 11 := fun _ _ out =>
  out.HasBinaryPrefix (code input) ∧ out.cells 0 = Γ.start

theorem hoareTime (input : List Bool) : machine.HoareTime
    (fun inp work out => Cursor [] input [] inp work out ∧ Ready input work) (Post input) (4 * input.length + 6) := by
  cases hv : (RealSyntax.decodeSentence input).isSome with
  | false =>
    let P : (Fin 11 → Tape) → Prop := fun work => IsReg input.length (work fuel.castSucc) ∧ Kept false work
    have hemit := FixedOutput.hoareTime (w := 11) SourceNormalization.falseSentence.code [] input [] P
    have hno : (emitBitsTM (n := 11) SourceNormalization.falseSentence.code).HoareTime
        (fun inp work out => Cursor [] input [] inp work out ∧ P work)
        (fun inp work out => Cursor [] input SourceNormalization.falseSentence.code inp work out ∧ True) 4 :=
      hemit.consequence (by rintro inp work out ⟨hc, hr, hs, hf⟩; exact ⟨hc, hs, hr, hs, hf⟩)
        (by rintro inp work out h; exact ⟨by simpa only [List.nil_append] using h.1, trivial⟩) le_rfl
    have hb := FlagBranchRun.no_hoareTime (NaturalScanBuffer.flag 9) (BooleanWordCopy.machine fuel.castSucc)
      (emitBitsTM SourceNormalization.falseSentence.code) [] input [] [] input SourceNormalization.falseSentence.code
      P (fun _ => True) 4 hno
    exact hb.consequence (by
      rintro inp work out ⟨hc, hr, hs, hf⟩
      have hf' : (work (NaturalScanBuffer.flag 9)).read = Γ.zero := by simpa only [hv, Γ.ofBool] using hf
      exact ⟨⟨hc, hr, hs, hf'⟩, hf'⟩) (by
      intro inp work out h
      simpa only [Post, code, hv, Bool.false_eq_true, ↓reduceIte] using And.intro h.1.tapePrefix h.1.zero) (by omega)
  | true =>
    let P : (Fin 11 → Tape) → Prop := fun work => IsReg input.length (work fuel.castSucc) ∧ Kept true work
    have hcopy := BooleanWordCopy.hoareTime fuel.castSucc input [] [] [] (fun _ => True)
    have hyes : (BooleanWordCopy.machine fuel.castSucc).HoareTime
        (fun inp work out => Cursor [] input [] inp work out ∧ P work)
        (fun inp work out => Cursor input [] input inp work out ∧ True) (4 * input.length + 2) :=
      hcopy.consequence (by
        rintro inp work out ⟨hc, hr, _hs, _hf⟩
        exact ⟨by simpa only [List.append_nil] using hc, hr, trivial⟩)
        (by intro inp work out h; exact ⟨by simpa only [List.nil_append] using h.1, trivial⟩) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (NaturalScanBuffer.flag 9) (BooleanWordCopy.machine fuel.castSucc)
      (emitBitsTM SourceNormalization.falseSentence.code) [] input [] input [] input P (fun _ => True) (4 * input.length + 2) hyes
    exact hb.consequence (by
      rintro inp work out ⟨hc, hr, hs, hf⟩
      have hf' : (work (NaturalScanBuffer.flag 9)).read = Γ.one := by simpa only [hv, Γ.ofBool] using hf
      exact ⟨⟨hc, hr, hs, hf'⟩, hf'⟩) (by
      intro inp work out h
      simpa only [Post, code, hv, ↓reduceIte] using And.intro h.1.tapePrefix h.1.zero) (by omega)

end JointThermoComplexity.Complexity.SourceNormalizationBranch

#print axioms JointThermoComplexity.Complexity.SourceNormalizationBranch.code_eq_normalize
#print axioms JointThermoComplexity.Complexity.SourceNormalizationBranch.hoareTime
