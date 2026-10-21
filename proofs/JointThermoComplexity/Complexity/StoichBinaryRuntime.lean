module
public import proofs.JointThermoComplexity.Complexity.BinarySignedOutput
public import proofs.JointThermoComplexity.Complexity.StoichBinaryDifference

set_option autoImplicit false
@[expose] public section

/-! Actual binary stoichiometric integer output with cost bounded in the original encoded input length. -/

namespace JointThermoComplexity.Complexity.StoichBinaryRuntime
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryDifferenceCursor BinaryDifferenceRuntime BinarySignedOutput

variable {w n : ℕ}

theorem hoareTime (left right flag : Fin w) (sep : Separate left right flag)
    (q : ReactionCircuit.Reaction n) (s : Fin n) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ flag → work' j = work j) → R work → R work') :
    (machine left right flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        Start left right flag (q.product s).bits (q.reactant s).bits (fun j => work j.castSucc) ∧
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (fun j => work j.castSucc))
      (fun inp work out => Cursor before input (emitted ++ BitCodec.integerCode (NetworkData.stoich q s)) inp work out ∧
        Serialized left right flag (q.product s).bits (q.reactant s).bits work ∧ R (fun j => work j.castSucc))
      (timeBound (q.product s).bits (q.reactant s).bits) :=
  naturals_hoareTime left right flag sep (q.product s) (q.reactant s) before input emitted R hR

theorem decoded_bound (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) :
    timeBound ((Q.network.reactions i).product s).bits ((Q.network.reactions i).reactant s).bits ≤ 9 * input.length + 30 := by
  have hf := InputSize.complex_entries_le_input Q i s
  have hl : Q.code.length = input.length := by rw [NetworkCodec.decode_sound hd]
  simp only [BitCodec.naturalCode_length] at hf
  have hm : max ((Q.network.reactions i).product s).bits.length ((Q.network.reactions i).reactant s).bits.length ≤ input.length :=
    max_le (by omega) (by omega)
  unfold timeBound
  omega

theorem decoded_hoareTime (left right flag : Fin w) (sep : Separate left right flag)
    (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (before remaining emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ flag → work' j = work j) → R work → R work') :
    (machine left right flag).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧
        Start left right flag ((Q.network.reactions i).product s).bits ((Q.network.reactions i).reactant s).bits (fun j => work j.castSucc) ∧
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (fun j => work j.castSucc))
      (fun inp work out => Cursor before remaining (emitted ++ BitCodec.integerCode (NetworkData.stoich (Q.network.reactions i) s)) inp work out ∧
        Serialized left right flag ((Q.network.reactions i).product s).bits ((Q.network.reactions i).reactant s).bits work ∧ R (fun j => work j.castSucc))
      (9 * input.length + 30) :=
  (hoareTime left right flag sep (Q.network.reactions i) s before remaining emitted R hR).consequence
    (fun _ _ _ h => h) (fun _ _ _ h => h) (decoded_bound input Q hd i s)

end JointThermoComplexity.Complexity.StoichBinaryRuntime

#print axioms JointThermoComplexity.Complexity.StoichBinaryRuntime.hoareTime
#print axioms JointThermoComplexity.Complexity.StoichBinaryRuntime.decoded_hoareTime
