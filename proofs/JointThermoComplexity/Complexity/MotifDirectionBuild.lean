module
public import proofs.JointThermoComplexity.Complexity.MotifDirectionLoopEntry
public import proofs.JointThermoComplexity.Complexity.MotifDirectionDenseCode

set_option autoImplicit false
@[expose] public section

/-! Complete canonical direction allFin output with restored reaction fuel and final truth, including zero reactions. -/

namespace JointThermoComplexity.Complexity.MotifDirectionBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifDirectionState MotifDirectionFrame MotifDirectionDenseCode CurrentTraversal

variable {n arity : ℕ}

def machine (m : ℕ) (r : Fin (m + 15)) : TM (m + 15) :=
  seqTM (MotifDirectionLoop.machine m r) (emitBitsTM [false, false, false])

def timeBound (L : ℕ) : ℕ := 32 * L ^ 3 + 56 * L ^ 2 + 52 * L + 6

theorem hoareTime (m L base : ℕ) (ha : arity ≤ 4 * L) (hn : n ≤ L)
    (r : Fin (m + 15)) (sep : BoxState.Separate m r) (indices : Fin n → Fin arity)
    (hindices : ∀ i, (indices i).val = base + i.val) (mask flags : Fin n → Bool)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m r).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        State m L base (List.ofFn mask) (List.ofFn flags) 0 R work ∧ IsReg n (work r))
      (fun inp work out => Cursor before input (emitted ++ (formula mask flags indices).code) inp work out ∧
        State m L (base + n) (List.ofFn mask) (List.ofFn flags) n R work ∧ IsReg n (work r)) (timeBound L) := by
  have hl := MotifDirectionLoopEntry.hoareTime m L base ha hn r sep indices hindices (List.ofFn mask) (List.ofFn flags)
    (by simp only [List.length_ofFn]) (by simp only [List.length_ofFn]) (clauses mask flags indices) (clauses_length mask flags indices)
    (clause_at mask flags indices) before input emitted R hR
  have ht := FixedOutput.hoareTime [false, false, false] before input (emitted ++ output (clauses mask flags indices))
    (fun work => State m L (base + n) (List.ofFn mask) (List.ofFn flags) n R work ∧ IsReg n (work r))
  have hs := seqTM_hoareTime (MotifDirectionLoop.machine m r) (emitBitsTM [false, false, false]) hl (by
    rintro inp work out ⟨hc, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp.1.1, hp, hr⟩) ht
  exact hs.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, _, hp, hr⟩
    exact ⟨by simpa only [List.append_assoc, output_eq] using hc, hp, hr⟩) (by
      unfold MotifDirectionLoopEntry.timeBound timeBound
      simp only [List.length_cons, List.length_nil]
      omega)

end JointThermoComplexity.Complexity.MotifDirectionBuild

#print axioms JointThermoComplexity.Complexity.MotifDirectionBuild.hoareTime
