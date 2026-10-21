module
public import proofs.JointThermoComplexity.Complexity.MotifBufferLoad
public import proofs.JointThermoComplexity.Complexity.MotifBufferMeta

set_option autoImplicit false
@[expose] public section

/-! Connect fixed motif-buffer loading to the original validated species or reaction count. -/

namespace JointThermoComplexity.Complexity.MotifVectorLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts BoxBufferState

def fuel (m : ℕ) : Bool → Fin (m + 15)
  | true => MonomialFuel.slot (m + 1)
  | false => ReactionFuel.slot m

def count (Q : NetworkCodec.Input) : Bool → ℕ
  | true => Q.speciesCount
  | false => Q.reactionCount

theorem fuel_separate (m : ℕ) (k : Fin 3) (which : Bool) : fuel m which ≠ buffer m k := by
  intro he
  have hv := congrArg Fin.val he
  have hk := k.isLt
  cases which
  · change m + 11 = k.val + 2 at hv
    omega
  · change m + 1 + 9 = k.val + 2 at hv
    omega

def machine (m : ℕ) (k : Fin 3) (which : Bool) : TM (m + 15) :=
  MotifBufferLoad.machine m k (fuel m which) (fuel_separate m k which)

theorem hoareTime (m idx : ℕ) (input : List Bool) (Q : NetworkCodec.Input)
    (hd : NetworkCodec.decode input = some Q) (k : Fin 3) (which : Bool)
    (bits before tail emitted : List Bool) (hlen : bits.length = count Q which)
    (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ buffer m k → work' j = work j) → R work → R work')
    (hK : ∀ work, R work → CurrentPins.Kept m input work) :
    (machine m k which).HoareTime
      (fun inp work out => Cursor before (bits ++ tail) emitted inp work out ∧ BoxState.Ready m input.length idx R work)
      (fun inp work out => Cursor (before ++ bits) tail emitted inp work out ∧
        BoxState.Ready m input.length idx R work ∧ Stored bits (work (buffer m k))) (16 * input.length + 12) := by
  have hdim := NetworkCodec.decoded_dimensions_le_length hd
  have hsize : bits.length ≤ input.length := by cases which <;> simp only [count] at hlen <;> omega
  have hs := MotifBufferLoad.hoareTime m input.length idx k (fuel m which) (fuel_separate m k which)
    bits before tail emitted hsize R hR
  exact hs.consequence (by
    rintro inp work out ⟨hc, hp⟩
    have hcounts := CurrentPins.counts m input Q hd work (hK work hp.2.2.2.2)
    have hf : IsReg bits.length (work (fuel m which)) := by
      cases which
      · simpa only [fuel, hlen, count] using hcounts.2
      · simpa only [fuel, hlen, count] using hcounts.1
    exact ⟨hc, hp, hf⟩) (fun _ _ _ hp => hp) le_rfl

end JointThermoComplexity.Complexity.MotifVectorLoad

#print axioms JointThermoComplexity.Complexity.MotifVectorLoad.fuel_separate
#print axioms JointThermoComplexity.Complexity.MotifVectorLoad.hoareTime
