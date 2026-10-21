module
public import proofs.JointThermoComplexity.Complexity.ReactionNegate
public import proofs.JointThermoComplexity.Complexity.ReactionAdd

set_option autoImplicit false
@[expose] public section

/-! The actual two-gate literal difference keeps its input cursor unchanged. -/

namespace JointThermoComplexity.Complexity.ReactionDifference
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionGateFrame RealSyntax

def machine (m : ℕ) : TM (m + 15) := seqTM (ReactionNegate.machine m) (ReactionAdd.machine m)

def word {arity : ℕ} (target prev keep : Fin arity) (room : target.val + 1 < arity) : List Bool :=
  (Formula.eq (.var target) (.neg (.var prev))).code ++
    (Formula.eq (.var (⟨target.val + 1, room⟩ : Fin arity)) (.add (.var keep) (.var target))).code

theorem hoareTime (m arity L : ℕ) (ha : arity ≤ 4 * L) (target prev keep : Fin arity) (room : target.val + 1 < arity)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ previous (m + 1) → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready m target.val prev.val keep.val R work)
      (fun inp work out => Cursor before input (emitted ++ word target prev keep room) inp work out ∧
        Ready m (target.val + 2) (target.val + 1) keep.val R work) (160 * L ^ 2 + 312 * L + 158) := by
  have hn := ReactionNegate.hoareTime m arity L ha target prev keep before input emitted R hR
  have ha := ReactionAdd.hoareTime m arity L ha ⟨target.val + 1, room⟩ target keep before input
    (emitted ++ (Formula.eq (.var target) (.neg (.var prev))).code) R hR
  have hseq := seqTM_hoareTime (ReactionNegate.machine m) (ReactionAdd.machine m) hn (by
    rintro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.phase
    rw [hi, hw, ho]
    exact hp) ha
  exact hseq.consequence (fun _ _ _ h => h)
    (fun _ _ _ hp => by simpa only [word, List.append_assoc] using hp) (by omega)

end JointThermoComplexity.Complexity.ReactionDifference

#print axioms JointThermoComplexity.Complexity.ReactionDifference.hoareTime
