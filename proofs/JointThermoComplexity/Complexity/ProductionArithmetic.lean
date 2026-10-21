module
public import proofs.JointThermoComplexity.Complexity.ProductionFrame
public import proofs.JointThermoComplexity.Complexity.StoichBinaryRuntime

set_option autoImplicit false
@[expose] public section

/-! Canonical signed coefficient output at fixed physical production ports, preserving the full surrounding frame. -/

namespace JointThermoComplexity.Complexity.ProductionArithmetic
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts BoxBufferState ReactionCircuit

variable {n : ℕ}

def machine (m : ℕ) : TM (m + 20) := WorkPermutation.machine (permutation m)
  (BinarySignedOutput.machine (leftOld m) (rightOld m) (signOld m))

structure Ready (m : ℕ) (q : Reaction n) (s : Fin n) (work : Fin (m + 20) → Tape) : Prop where
  safe : ∀ j, Parked (work j)
  productString : (work (left m)).HasBinaryString (q.product s).bits
  reactantString : (work (right m)).HasBinaryString (q.reactant s).bits
  productZero : (work (left m)).cells 0 = Γ.start
  reactantZero : (work (right m)).cells 0 = Γ.start
  signHead : (work (sign m)).head = 1
  emptyMagnitude : (work (magnitude m)).HasBinaryPrefix []
  magnitudeZero : (work (magnitude m)).cells 0 = Γ.start

structure Done (m L : ℕ) (q : Reaction n) (s : Fin n) (work : Fin (m + 20) → Tape) : Prop where
  safe : ∀ j, Parked (work j)
  productReusable : Reusable L (work (left m))
  reactantReusable : Reusable L (work (right m))
  magnitudeReusable : Reusable L (work (magnitude m))
  signHead : (work (sign m)).head = 1
  signValue : (work (sign m)).read = Γ.ofBool (SignedBinaryDifference.negative (q.product s).bits (q.reactant s).bits)
  canonicalMagnitude : (work (magnitude m)).HasBinaryString (SignedBinaryDifference.magnitude (q.product s).bits (q.reactant s).bits)
  magnitudeZero : (work (magnitude m)).cells 0 = Γ.start

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (before remaining emitted : List Bool)
    (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', ProductionFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ Ready m (Q.network.reactions i) s work ∧ R work)
      (fun inp work out => Cursor before remaining (emitted ++ BitCodec.integerCode (NetworkData.stoich (Q.network.reactions i) s)) inp work out ∧
        Done m input.length (Q.network.reactions i) s work ∧ R work) (9 * input.length + 30) := by
  rintro inp work out ⟨hc, hp, hr⟩
  let original : Fin (m + 19) → Tape := fun j => work (permutation m j.castSucc)
  let P : (Fin (m + 19) → Tape) → Prop := fun old =>
    ∀ j, j ≠ leftOld m → j ≠ rightOld m → j ≠ signOld m → old j = original j
  have hP : ∀ old old', (∀ j, j ≠ leftOld m → j ≠ rightOld m → j ≠ signOld m → old' j = old j) → P old → P old' := by
    intro old old' hw h j hl hr hs
    exact (hw j hl hr hs).trans (h j hl hr hs)
  have hb := StoichBinaryRuntime.decoded_hoareTime (leftOld m) (rightOld m) (signOld m) (arithmetic_separate m)
    input Q hd i s before remaining emitted P hP
  have hroute := WorkPermutation.hoareTime (permutation m)
    (BinarySignedOutput.machine (leftOld m) (rightOld m) (signOld m)) _ _ (9 * input.length + 30) hb
  obtain ⟨d, t, ht, hreach, hh, hc', hp', hframe⟩ := hroute inp work out
    ⟨⟨hc.cells, hc.head, (fun j => hc.works (permutation m j)), hc.tapePrefix, hc.zero⟩,
      ⟨(fun j => hp.safe (permutation m j.castSucc)),
        by simpa only [left_route] using hp.productString,
        by simpa only [right_route] using hp.reactantString,
        by simpa only [left_route] using hp.productZero,
        by simpa only [right_route] using hp.reactantZero,
        by simpa only [sign_route] using hp.signHead⟩,
      by simpa only [magnitude_route] using hp.emptyMagnitude,
      by simpa only [magnitude_route] using hp.magnitudeZero, (fun _ _ _ _ => rfl)⟩
  have hw : ProductionFrame.Unchanged m work d.work := by
    intro j hl hr hs hm
    have hne : j ≠ CountSumAt.destination (permutation m) := by
      simpa only [CountSumAt.destination, magnitude_route] using hm
    obtain ⟨k, hk⟩ := CountSumAt.preimage (permutation m) j hne
    have hkl : k ≠ leftOld m := by
      intro he
      apply hl
      exact hk.symm.trans (by rw [he, left_route])
    have hkr : k ≠ rightOld m := by
      intro he
      apply hr
      exact hk.symm.trans (by rw [he, right_route])
    have hks : k ≠ signOld m := by
      intro he
      apply hs
      exact hk.symm.trans (by rw [he, sign_route])
    have hv := hframe k hkl hkr hks
    change d.work (permutation m k.castSucc) = work (permutation m k.castSucc) at hv
    simpa only [hk] using hv
  have hsafe : ∀ j, Parked (d.work j) := by
    intro j
    simpa only [(permutation m).apply_symm_apply] using hp'.safe ((permutation m).symm j)
  have hl : (d.work (left m)).HasBinaryPrefix ((Q.network.reactions i).product s).bits := by
    simpa only [left_route] using hp'.operands.lhs
  have hright : (d.work (right m)).HasBinaryPrefix ((Q.network.reactions i).reactant s).bits := by
    simpa only [right_route] using hp'.operands.rhs
  have hlz : (d.work (left m)).cells 0 = Γ.start := by simpa only [left_route] using hp'.operands.lhsZero
  have hrz : (d.work (right m)).cells 0 = Γ.start := by simpa only [right_route] using hp'.operands.rhsZero
  have hmag : (d.work (magnitude m)).HasBinaryString
      (SignedBinaryDifference.magnitude ((Q.network.reactions i).product s).bits ((Q.network.reactions i).reactant s).bits) := by
    simpa only [magnitude_route] using hp'.magnitudeBuffer
  have hmz : (d.work (magnitude m)).cells 0 = Γ.start := by simpa only [magnitude_route] using hp'.zero
  have hfields := InputSize.complex_entries_le_input Q i s
  have hlen : Q.code.length = input.length := by rw [NetworkCodec.decode_sound hd]
  simp only [BitCodec.naturalCode_length] at hfields
  have hmax : max ((Q.network.reactions i).product s).bits.length ((Q.network.reactions i).reactant s).bits.length ≤ input.length :=
    max_le (by omega) (by omega)
  have hmlen := SignedBinaryDifference.magnitude_length_le ((Q.network.reactions i).product s).bits ((Q.network.reactions i).reactant s).bits
  have hdone : Done m input.length (Q.network.reactions i) s d.work :=
    ⟨hsafe, ⟨_, by omega, hl.2, hlz, hl.1.le⟩, ⟨_, by omega, hright.2, hrz, hright.1.le⟩,
      ⟨_, by omega, hmag.2, hmz, by rw [hmag.1]; omega⟩,
      by simpa only [sign_route] using hp'.operands.flagHead,
      by simpa only [sign_route] using hp'.signValue, hmag, hmz⟩
  exact ⟨d, t, ht, hreach, hh, ⟨hc'.cells, hc'.head, fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩, hc'.tapePrefix, hc'.zero⟩,
    hdone, hR work d.work hw hr⟩

end JointThermoComplexity.Complexity.ProductionArithmetic

#print axioms JointThermoComplexity.Complexity.ProductionArithmetic.hoareTime
