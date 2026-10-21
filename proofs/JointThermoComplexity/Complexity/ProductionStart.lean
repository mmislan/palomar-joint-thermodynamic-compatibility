module
public import proofs.JointThermoComplexity.Complexity.ProductionReactionReset
public import proofs.JointThermoComplexity.Complexity.ProductionCurrentReset

set_option autoImplicit false
@[expose] public section

/-! Initialize the production reaction/current loop from actual prepared motif resources in linear time. -/

namespace JointThermoComplexity.Complexity.ProductionStart
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts

def machine (m : ℕ) : TM (m + 20) := seqTM (clearWorkTM (reaction m)) (CurrentStart.cursorMachine (m + 5))

def timeBound (L : ℕ) : ℕ := 15 * L + 21

theorem hoareTime (m L n old si idx : ℕ) (hold : old ≤ 4 * L) (hn : n ≤ L) (hi : idx ≤ L)
    (before remaining emitted : List Bool) (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ reaction m → j ≠ current m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionOperandLoad.State m L n old si work ∧
        IsReg idx (work (current m)) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧ R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionOperandLoad.State m L n 0 si work ∧
        IsReg n (work (current m)) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧ R work)
      (timeBound L) := by
  let P : (Fin (m + 20) → Tape) → Prop := fun work => IsReg idx (work (current m)) ∧
    BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ reaction m → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hi, hz, hr⟩
    have hcur : current m ≠ reaction m := by intro he; have hv := congrArg Fin.val he; change (7 : ℕ) = 6 at hv; omega
    have hzero : PowerPorts.scratch (m + 7) ≠ reaction m := by intro he; have hv := congrArg Fin.val he; change (5 : ℕ) = 6 at hv; omega
    exact ⟨by simpa only [hw _ hcur] using hi, by simpa only [hw _ hzero] using hz,
      hR work work' (fun j hj _ => hw j hj) hr⟩
  have hr := ProductionReactionReset.hoareTime m L n old si before remaining emitted P hP
  have hc := ProductionCurrentReset.hoareTime m L n 0 si idx before remaining emitted R
    (fun work work' hw => hR work work' (fun j _ hj => hw j hj))
  have hs := seqTM_hoareTime (clearWorkTM (reaction m)) (CurrentStart.cursorMachine (m + 5)) hr (by
    rintro inp work out ⟨hcur, hp, hi, hz, hr⟩
    obtain ⟨hinp, hw, ho⟩ := hcur.phase
    rw [hinp, hw, ho]
    exact ⟨hcur, hp, hi, hz, hr⟩) hc
  exact hs.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold timeBound; omega)

theorem from_directions (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before remaining emitted : List Bool) (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ reaction m → j ≠ current m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧
        MotifDecodedDirections.Ready (m + 5) input Q a (Q.speciesCount + Q.reactionCount) work ∧ ProductionBank.State m work ∧ R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionOperandLoad.State m input.length Q.speciesCount 0 0 work ∧
        IsReg Q.speciesCount (work (current m)) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧
        ProductionBank.State m work ∧ R work) (timeBound input.length) := by
  let P : (Fin (m + 20) → Tape) → Prop := fun work => ProductionBank.State m work ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ reaction m → j ≠ current m → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hb, hr⟩
    exact ⟨CurrentBankFrame.build_frame m work work' (fun j _ hp hs => hw j hp hs) hb, hR work work' hw hr⟩
  rintro inp work out ⟨hc, hp, hb, hr⟩
  obtain ⟨old, hold, hstate, _⟩ := ProductionInitialState.of_directions m (Q.speciesCount + Q.reactionCount) input Q hd a work hp hb
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  exact hoareTime m input.length Q.speciesCount old 0 (Q.speciesCount + Q.reactionCount) hold (by omega) (by omega)
    before remaining emitted P hP inp work out ⟨hc, hstate, hp.1.2.2.1, hp.1.2.1, hb, hr⟩

end JointThermoComplexity.Complexity.ProductionStart

#print axioms JointThermoComplexity.Complexity.ProductionStart.hoareTime
#print axioms JointThermoComplexity.Complexity.ProductionStart.from_directions
