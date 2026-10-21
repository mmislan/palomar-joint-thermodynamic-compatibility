module
public import proofs.JointThermoComplexity.Complexity.ProductionTermOutput

set_option autoImplicit false
@[expose] public section

/-! An actual reaction-mask bit selects the original coefficient/current product or exact integer zero. -/

namespace JointThermoComplexity.Complexity.ProductionSelectedTerm
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts

def zeroCode : List Bool := [false, false, false] ++ BitCodec.integerCode 0

def zeroMachine (m : ℕ) : TM (m + 20) := seqTM (emitBitsTM zeroCode) rewindInputTM

theorem zero_hoareTime (m : ℕ) (input before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (m + 20) → Tape) → Prop) (hSafe : ∀ work, R work → ∀ j, Parked (work j)) :
    (zeroMachine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ R work)
      (fun inp work out => Cursor [] input (emitted ++ zeroCode) inp work out ∧ R work) (input.length + 9) := by
  have hf := FixedOutput.hoareTime zeroCode before remaining emitted R
  have hr := InputRewind.hoareTime before remaining (emitted ++ zeroCode) R
  have hs := seqTM_hoareTime (emitBitsTM zeroCode) rewindInputTM hf (by
    rintro inp work out ⟨hc, _, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hr
  have hlength := congrArg List.length hsplit
  simp only [List.length_append] at hlength
  have hzero : zeroCode.length = 5 := rfl
  exact hs.consequence (fun _ work _ ⟨hc, hr⟩ => ⟨hc, hSafe work hr, hr⟩)
    (fun _ _ _ ⟨hc, hr⟩ => ⟨by simpa only [hsplit] using hc, hr⟩) (by rw [hzero]; omega)

def term (selected : Bool) (Q : NetworkCodec.Input) (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) :
    RealSyntax.Term (NetworkMembership.arity Q.network) :=
  if selected then ProductionTermOutput.term Q i s else .int 0

def machine (m : ℕ) : TM (m + 20) :=
  FlagBranch.machine (MotifBufferPorts.buffer (m + 5) 1) (ProductionTermOutput.machine m) (zeroMachine m)

def timeBound (L : ℕ) : ℕ := ProductionTermOutput.timeBound L + 2

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (selected : Bool)
    (before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', ProductionTermFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧
        (ProductionOperandLoad.State m input.length Q.speciesCount i.val s.val work ∧
          IsReg (NetworkMembership.currentIndex Q.network i).val (work (current m)) ∧
          BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧ R work) ∧
        (work (MotifBufferPorts.buffer (m + 5) 1)).read = Γ.ofBool selected)
      (fun inp work out => Cursor [] input (emitted ++ (term selected Q i s).code) inp work out ∧
        ProductionOperandLoad.State m input.length Q.speciesCount i.val s.val work ∧
        IsReg (NetworkMembership.currentIndex Q.network i).val (work (current m)) ∧
        BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧ R work) (timeBound input.length) := by
  let P : (Fin (m + 20) → Tape) → Prop := fun work =>
    ProductionOperandLoad.State m input.length Q.speciesCount i.val s.val work ∧
    IsReg (NetworkMembership.currentIndex Q.network i).val (work (current m)) ∧
    BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧ R work
  have ht := ProductionTermOutput.hoareTime m input Q hd i s before remaining emitted hsplit R hR
  have hf := zero_hoareTime m input before remaining emitted hsplit P (fun _ h => h.1.safe)
  have hf' := hf.mono_bound (b' := ProductionTermOutput.timeBound input.length) (by
    unfold ProductionTermOutput.timeBound
    omega)
  cases selected with
  | false =>
    have hbranch := FlagBranchRun.no_hoareTime (MotifBufferPorts.buffer (m + 5) 1) (ProductionTermOutput.machine m) (zeroMachine m)
      before remaining emitted [] input (emitted ++ (term false Q i s).code) P P
      (ProductionTermOutput.timeBound input.length) (by
        simpa only [term, Bool.false_eq_true, ↓reduceIte, RealSyntax.Term.code, zeroCode] using hf')
    rintro inp work out ⟨hc, hp, hflag⟩
    exact hbranch inp work out ⟨⟨hc, hp⟩, by simpa only [Γ.ofBool] using hflag⟩
  | true =>
    have hbranch := FlagBranchRun.yes_hoareTime (MotifBufferPorts.buffer (m + 5) 1) (ProductionTermOutput.machine m) (zeroMachine m)
      before remaining emitted [] input (emitted ++ (term true Q i s).code) P P
      (ProductionTermOutput.timeBound input.length) (by simpa only [term, ↓reduceIte] using ht)
    have hbranch' := hbranch.mono_bound (b' := timeBound input.length) (by unfold timeBound; omega)
    rintro inp work out ⟨hc, hp, hflag⟩
    exact hbranch' inp work out ⟨⟨hc, hp⟩, by simpa only [Γ.ofBool] using hflag⟩

end JointThermoComplexity.Complexity.ProductionSelectedTerm

#print axioms JointThermoComplexity.Complexity.ProductionSelectedTerm.zero_hoareTime
#print axioms JointThermoComplexity.Complexity.ProductionSelectedTerm.hoareTime
