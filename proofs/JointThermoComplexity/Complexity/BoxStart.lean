module
public import proofs.JointThermoComplexity.Complexity.BoxDecodedBuild
public import proofs.JointThermoComplexity.Complexity.BoxSourceFrame
public import proofs.JointThermoComplexity.Complexity.UnaryReset

set_option autoImplicit false
@[expose] public section

/-! Reset the bounded activity cursor, emit the next constraint conjunction and build all rational boxes. -/

namespace JointThermoComplexity.Complexity.BoxStart
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts BoxState CircuitSerialization

def machine (m : ℕ) : TM (m + 15) := seqTM (clearWorkTM (species (m + 1)))
  (seqTM (emitBitsTM conjunctionTag) (BoxBuild.machine m))

def timeBound (L : ℕ) : ℕ := 128 * L ^ 3 + 268 * L ^ 2 + 276 * L + 16

theorem hoareTime (m old : ℕ) (input : List Bool) (Q : NetworkCodec.Input)
    (hd : NetworkCodec.decode input = some Q) (hold : old ≤ input.length)
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before (BoxTraversalData.boxes Q ++ tail) emitted inp work out ∧
        Ready m input.length old (fun work => CurrentPins.Kept m input work ∧ R work) work)
      (fun inp work out => Cursor (before ++ BoxTraversalData.boxes Q) tail
        (emitted ++ (conjunctionTag ++ (BoxDenseCode.formula Q.network.boxes (NetworkMembership.activityIndex Q.network)).code))
        inp work out ∧ Ready m input.length Q.speciesCount (fun work => CurrentPins.Kept m input work ∧ R work) work)
      (timeBound input.length) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work => CurrentPins.Kept m input work ∧ R work
  have hP : ∀ work work', Unchanged m work work' → P work → P work' := by
    rintro work work' hw ⟨hp, hr⟩
    exact ⟨BoxPins.frame m input work work' hw hp, hR work work' hw hr⟩
  have hc := UnaryReset.hoareTime (species (m + 1)) old before (BoxTraversalData.boxes Q ++ tail) emitted
    (BoxSourceFrame.Fixed m input.length P) (BoxSourceFrame.frame m input.length P hP)
  have ht := FixedOutput.hoareTime conjunctionTag before (BoxTraversalData.boxes Q ++ tail) emitted
    (Ready m input.length 0 P)
  have hb := BoxDecodedBuild.hoareTime m input Q hd before tail (emitted ++ conjunctionTag) R hR
  have hrest := seqTM_hoareTime (emitBitsTM conjunctionTag) (BoxBuild.machine m) ht (by
    rintro inp work out ⟨hcur, _, hr⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨hcur, hr⟩) hb
  have hs := seqTM_hoareTime (clearWorkTM (species (m + 1)))
    (seqTM (emitBitsTM conjunctionTag) (BoxBuild.machine m)) hc (by
      rintro inp work out ⟨hcur, hsafe, hi, hz, hbuf, hr⟩
      obtain ⟨hip, hw, ho⟩ := hcur.phase
      rw [hip, hw, ho]
      exact ⟨hcur, hsafe, hsafe, hz, hi, hbuf, hr⟩) hrest
  exact hs.consequence (by
    rintro inp work out ⟨hcur, hsafe, hz, hi, hbuf, hr⟩
    exact ⟨hcur, hsafe, hi, hz, hbuf, hr⟩) (by
      rintro inp work out ⟨hcur, hr⟩
      exact ⟨by simpa only [List.append_assoc] using hcur, hr⟩) (by
        unfold timeBound BoxBuild.timeBound
        simp only [conjunctionTag, List.length_cons, List.length_nil]
        omega)

end JointThermoComplexity.Complexity.BoxStart

#print axioms JointThermoComplexity.Complexity.BoxStart.hoareTime
