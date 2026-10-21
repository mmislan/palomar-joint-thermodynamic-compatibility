module
public import proofs.JointThermoComplexity.Complexity.MotifDirectionClause
public import proofs.JointThermoComplexity.Complexity.MotifDirectionSuccessor

set_option autoImplicit false
@[expose] public section

/-! One actual reaction-direction iteration emits its clause, advances both stored-bit heads and increments the current address. -/

namespace JointThermoComplexity.Complexity.MotifDirectionStep
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifDirectionState MotifDirectionFrame MonomialPorts

variable {arity : ℕ}

def machine (m : ℕ) : TM (m + 15) := seqTM
  (seqTM (MotifDirectionClause.machine m) (MotifDirectionState.machine m)) (UnarySuccessor.machine (species (m + 1)))

def timeBound (L : ℕ) : ℕ := 32 * L ^ 2 + 56 * L + 49

theorem hoareTime (m L : ℕ) (ha : arity ≤ 4 * L) (idx : Fin arity) (mask flags : List Bool) (i : ℕ)
    (hm : mask.length ≤ L) (hf : flags.length ≤ L) (him : i < mask.length) (hif : i < flags.length)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ State m L idx.val mask flags i R work)
      (fun inp work out => Cursor before input (emitted ++ MotifDirectionClause.word mask[i] flags[i] idx) inp work out ∧
        State m L (idx.val + 1) mask flags (i + 1) R work) (timeBound L) := by
  have hc := MotifDirectionClause.hoareTime m L ha idx mask flags i him hif before input emitted R
  have hh := MotifDirectionFrame.hoareTime m L idx.val mask flags i hm hf him hif before input
    (emitted ++ MotifDirectionClause.word mask[i] flags[i] idx) R hR
  have hs := MotifDirectionSuccessor.hoareTime m L idx.val mask flags (i + 1) before input
    (emitted ++ MotifDirectionClause.word mask[i] flags[i] idx) R hR
  have hch := seqTM_hoareTime (MotifDirectionClause.machine m) (MotifDirectionState.machine m) hc (by
    rintro inp work out ⟨hcur, hp⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨hcur, hp⟩) hh
  have hfull := seqTM_hoareTime (seqTM (MotifDirectionClause.machine m) (MotifDirectionState.machine m))
    (UnarySuccessor.machine (species (m + 1))) hch (by
      rintro inp work out ⟨hcur, hp⟩
      obtain ⟨hi, hw, ho⟩ := hcur.phase
      rw [hi, hw, ho]
      exact ⟨hcur, hp⟩) hs
  exact hfull.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by
    have hi := idx.isLt.le.trans ha
    unfold MotifDirectionClause.timeBound timeBound
    omega)

end JointThermoComplexity.Complexity.MotifDirectionStep

#print axioms JointThermoComplexity.Complexity.MotifDirectionStep.hoareTime
