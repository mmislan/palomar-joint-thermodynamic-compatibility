module
public import proofs.JointThermoComplexity.Complexity.ReactionDifference
public import proofs.JointThermoComplexity.Complexity.ReactionCoefficient
public import proofs.JointThermoComplexity.Complexity.ReactionMultiply

set_option autoImplicit false
@[expose] public section

/-! The actual four-gate reaction tail reads its coefficient from the binary input. -/

namespace JointThermoComplexity.Complexity.ReactionArithmetic
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts ReactionGateFrame RealSyntax

def first (m : ℕ) : TM (m + 15) := seqTM (ReactionDifference.machine m) (ReactionCoefficient.machine m)
def machine (m : ℕ) : TM (m + 15) := seqTM (first m) (ReactionMultiply.machine m)

def word {arity : ℕ} (target prev keep : Fin arity) (value : ℕ) (room : target.val + 3 < arity) : List Bool :=
  (ReactionDifference.word target prev keep (by omega) ++
    (Formula.eq (.var (⟨target.val + 2, by omega⟩ : Fin arity)) (.int (value : ℤ))).code) ++
    BinaryPowerCode.multiply (⟨target.val + 3, room⟩ : Fin arity)
      ⟨target.val + 1, by omega⟩ ⟨target.val + 2, by omega⟩

theorem hoareTime (m arity L : ℕ) (ha : arity ≤ 4 * L) (target prev keep : Fin arity)
    (value : ℕ) (room : target.val + 3 < arity) (hv : (BitCodec.naturalCode value).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ previous (m + 1) → j ≠ saved m →
      work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧
        Ready m target.val prev.val keep.val R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail
        (emitted ++ word target prev keep value room) inp work out ∧
        Ready m (target.val + 4) (target.val + 3) (target.val + 2) R work)
      (288 * L ^ 2 + 577 * L + 302) := by
  have hd := ReactionDifference.hoareTime m arity L ha target prev keep (by omega)
    before (BitCodec.naturalCode value ++ tail) emitted R
    (fun work work' hw hr => hR work work' (fun j hn hp _ => hw j hn hp) hr)
  have hc := ReactionCoefficient.hoareTime m arity L ha ⟨target.val + 2, by omega⟩ ⟨target.val + 1, by omega⟩ keep value hv
    before tail (emitted ++ ReactionDifference.word target prev keep (by omega)) R
    (fun work work' hw hr => hR work work' (fun j hn _ hs => hw j hn hs) hr)
  have hs := seqTM_hoareTime (ReactionDifference.machine m) (ReactionCoefficient.machine m) hd (by
    rintro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.phase
    rw [hi, hw, ho]
    exact hp) hc
  have hm := ReactionMultiply.hoareTime m arity L ha ⟨target.val + 3, room⟩ ⟨target.val + 1, by omega⟩ ⟨target.val + 2, by omega⟩
    (before ++ BitCodec.naturalCode value) tail
    ((emitted ++ ReactionDifference.word target prev keep (by omega)) ++
      (Formula.eq (.var (⟨target.val + 2, by omega⟩ : Fin arity)) (.int (value : ℤ))).code) R
    (fun work work' hw hr => hR work work' (fun j hn hp _ => hw j hn hp) hr)
  have hseq := seqTM_hoareTime (first m) (ReactionMultiply.machine m) hs (by
    rintro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.phase
    rw [hi, hw, ho]
    exact hp) hm
  exact hseq.consequence (fun _ _ _ h => h)
    (fun _ _ _ hp => by simpa only [word, List.append_assoc] using hp) (by omega)

end JointThermoComplexity.Complexity.ReactionArithmetic

#print axioms JointThermoComplexity.Complexity.ReactionArithmetic.hoareTime
