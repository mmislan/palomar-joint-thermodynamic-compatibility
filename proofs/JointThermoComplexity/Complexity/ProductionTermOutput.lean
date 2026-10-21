module
public import proofs.JointThermoComplexity.Complexity.ProductionVariable

set_option autoImplicit false
@[expose] public section

/-! Emit one exact original stoichiometric coefficient times its shared current, then restore a common input cursor. -/

namespace JointThermoComplexity.Complexity.ProductionTermOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts

def outputPrefix : List Bool := [false, true, true] ++ [false, false, false]

def term (Q : NetworkCodec.Input) (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) :
    RealSyntax.Term (NetworkMembership.arity Q.network) :=
  .mul (.int (NetworkData.stoich (Q.network.reactions i) s)) (.var (NetworkMembership.currentIndex Q.network i))

def machine (m : ℕ) : TM (m + 20) := seqTM
  (seqTM (seqTM (emitBitsTM outputPrefix) (ProductionCoefficient.machine m)) (ProductionVariable.machine m)) rewindInputTM

def timeBound (L : ℕ) : ℕ := 4 * L ^ 3 + 52 * L ^ 2 + 140 * L + 140

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', ProductionTermFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionOperandLoad.State m input.length Q.speciesCount i.val s.val work ∧
        IsReg (NetworkMembership.currentIndex Q.network i).val (work (current m)) ∧
        BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧ R work)
      (fun inp work out => Cursor [] input (emitted ++ (term Q i s).code) inp work out ∧
        ProductionOperandLoad.State m input.length Q.speciesCount i.val s.val work ∧
        IsReg (NetworkMembership.currentIndex Q.network i).val (work (current m)) ∧
        BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧ R work) (timeBound input.length) := by
  let P : (Fin (m + 20) → Tape) → Prop := fun work =>
    IsReg (NetworkMembership.currentIndex Q.network i).val (work (current m)) ∧
    BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧ R work
  let S : (Fin (m + 20) → Tape) → Prop := fun work =>
    ProductionOperandLoad.State m input.length Q.speciesCount i.val s.val work ∧ P work
  have hP : ∀ work work', ProductionFrame.Unchanged m work work' → P work → P work' := by
    rintro work work' hw ⟨hi, hz, hr⟩
    have hcur := (ProductionFrame.indices_eq m work work' hw).2.1
    have hzero := ProductionFrame.outside m work work' hw (PowerPorts.scratch (m + 7)) (by left; change (5 : ℕ) < 8; omega)
    exact ⟨by simpa only [hcur] using hi, by simpa only [hzero] using hz,
      hR work work' (ProductionTermFrame.of_arithmetic m work work' hw) hr⟩
  have hf := FixedOutput.hoareTime outputPrefix before remaining emitted S
  have hc := ProductionCoefficient.hoareTime m input Q hd i s before remaining (emitted ++ outputPrefix) hsplit P hP
  have hv := ProductionVariable.hoareTime m input.length Q.speciesCount i.val s.val
    (NetworkMembership.currentIndex Q.network i) (NetworkNumbering.decoded_index_bound hd _).le
    (DecodedReactionFieldLoad.atPrefix Q i s true) (DecodedReactionFieldLoad.atSuffix Q i s true)
    ((emitted ++ outputPrefix) ++ BitCodec.integerCode (NetworkData.stoich (Q.network.reactions i) s)) R hR
  have hr := InputRewind.hoareTime (DecodedReactionFieldLoad.atPrefix Q i s true) (DecodedReactionFieldLoad.atSuffix Q i s true)
    (((emitted ++ outputPrefix) ++ BitCodec.integerCode (NetworkData.stoich (Q.network.reactions i) s)) ++
      (RealSyntax.Term.var (NetworkMembership.currentIndex Q.network i)).code) S
  have hfc := seqTM_hoareTime (emitBitsTM outputPrefix) (ProductionCoefficient.machine m) hf (by
    rintro inp work out ⟨hcur, _, hp, hi, hz, hr⟩
    obtain ⟨hinp, hw, ho⟩ := hcur.phase
    rw [hinp, hw, ho]
    exact ⟨hcur, hp, hi, hz, hr⟩) hc
  have hfcv := seqTM_hoareTime (seqTM (emitBitsTM outputPrefix) (ProductionCoefficient.machine m))
    (ProductionVariable.machine m) hfc (by
      rintro inp work out ⟨hcur, hp, hi, hz, hr⟩
      obtain ⟨hinp, hw, ho⟩ := hcur.phase
      rw [hinp, hw, ho]
      exact ⟨hcur, hp, hi, hz, hr⟩) hv
  have hfull := seqTM_hoareTime (seqTM (seqTM (emitBitsTM outputPrefix) (ProductionCoefficient.machine m))
    (ProductionVariable.machine m)) rewindInputTM hfcv (by
      rintro inp work out ⟨hcur, hp, hi, hz, hr⟩
      obtain ⟨hinp, hw, ho⟩ := hcur.phase
      rw [hinp, hw, ho]
      exact ⟨hcur, hp, hi, hz, hr⟩) hr
  have hinput := DecodedReactionFieldLoad.input_split input Q hd i s true
  have hlength := congrArg List.length hinput
  simp only [List.length_append] at hlength
  exact hfull.consequence (by
    rintro inp work out ⟨hcur, hp, hi, hz, hr⟩
    exact ⟨hcur, hp.safe, hp, hi, hz, hr⟩) (by
    rintro inp work out ⟨hcur, hp, hi, hz, hr⟩
    exact ⟨by simpa only [hinput, term, RealSyntax.Term.code, outputPrefix, List.append_assoc] using hcur, hp, hi, hz, hr⟩) (by
      unfold timeBound ProductionCoefficient.timeBound outputPrefix
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)

end JointThermoComplexity.Complexity.ProductionTermOutput

#print axioms JointThermoComplexity.Complexity.ProductionTermOutput.hoareTime
