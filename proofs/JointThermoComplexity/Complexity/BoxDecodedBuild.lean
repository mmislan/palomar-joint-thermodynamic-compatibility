module
public import proofs.JointThermoComplexity.Complexity.BoxBuild
public import proofs.JointThermoComplexity.Complexity.BoxPins
public import proofs.JointThermoComplexity.Complexity.BoxDecodedBounds
public import proofs.JointThermoComplexity.Complexity.BoxTraversalData

set_option autoImplicit false
@[expose] public section

/-! Complete exact decoded-network box-table emission with original metadata retained and species fuel restored. -/

namespace JointThermoComplexity.Complexity.BoxDecodedBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxState

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (BoxBuild.machine m).HoareTime
      (fun inp work out => Cursor before (BoxTraversalData.boxes Q ++ tail) emitted inp work out ∧
        Ready m input.length 0 (fun work => CurrentPins.Kept m input work ∧ R work) work)
      (fun inp work out => Cursor (before ++ BoxTraversalData.boxes Q) tail
        (emitted ++ (BoxDenseCode.formula Q.network.boxes (NetworkMembership.activityIndex Q.network)).code) inp work out ∧
        Ready m input.length Q.speciesCount (fun work => CurrentPins.Kept m input work ∧ R work) work)
      (BoxBuild.timeBound input.length) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work => CurrentPins.Kept m input work ∧ R work
  have hP : ∀ work work', Unchanged m work work' → P work → P work' := by
    rintro work work' hw ⟨hp, hr⟩
    exact ⟨BoxPins.frame m input work work' hw hp, hR work work' hw hr⟩
  have hs := BoxBuild.hoareTime m input.length (BoxDecodedBounds.arity input Q hd) (BoxDecodedBounds.species input Q hd)
    Q.network.boxes (BoxDecodedBounds.bounded input Q hd) (NetworkMembership.activityIndex Q.network)
    (BoxDecodedBounds.index_value Q) before tail emitted P hP
  exact hs.consequence (by
    rintro inp work out ⟨hc, hr⟩
    have hk : CurrentPins.Kept m input work := hr.2.2.2.2.1
    exact ⟨hc, hr, (CurrentPins.counts m input Q hd work hk).1⟩)
    (fun _ _ _ ⟨hc, hr, _⟩ => ⟨hc, hr⟩) le_rfl

end JointThermoComplexity.Complexity.BoxDecodedBuild

#print axioms JointThermoComplexity.Complexity.BoxDecodedBuild.hoareTime
