module
public import proofs.JointThermoComplexity.Complexity.MotifDirectionInit
public import proofs.JointThermoComplexity.Complexity.MotifDirectionBuild

set_option autoImplicit false
@[expose] public section

/-! Initialized complete direction-formula emission returns both vectors to their stored end positions. -/

namespace JointThermoComplexity.Complexity.MotifDirections
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts MotifDirectionState MotifDirectionFrame BoxBufferState

variable {n arity : ℕ}

def machine (m : ℕ) (r : Fin (m + 15)) : TM (m + 15) :=
  seqTM (MotifDirectionInit.machine m) (MotifDirectionBuild.machine m r)

def timeBound (L : ℕ) : ℕ := 32 * L ^ 3 + 56 * L ^ 2 + 54 * L + 14

theorem hoareTime (m L base : ℕ) (ha : arity ≤ 4 * L) (hn : n ≤ L)
    (r : Fin (m + 15)) (sep : BoxState.Separate m r) (indices : Fin n → Fin arity)
    (hindices : ∀ i, (indices i).val = base + i.val) (mask flags : Fin n → Bool)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m r).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ BoxState.Ready m L base R work ∧
        Stored (List.ofFn mask) (work (buffer m 1)) ∧ Stored (List.ofFn flags) (work (buffer m 2)) ∧ IsReg n (work r))
      (fun inp work out => Cursor before input (emitted ++ (MotifDirectionDenseCode.formula mask flags indices).code) inp work out ∧
        BoxState.Ready m L (base + n) R work ∧ Stored (List.ofFn mask) (work (buffer m 1)) ∧
        Stored (List.ofFn flags) (work (buffer m 2)) ∧ IsReg n (work r)) (timeBound L) := by
  let S : (Fin (m + 15) → Tape) → Prop := fun work => R work ∧ IsReg n (work r)
  have hS : ∀ work work', Unchanged m work work' → S work → S work' := by
    rintro work work' hw ⟨hr, hf⟩
    exact ⟨hR work work' hw hr, by rw [hw r sep.loDen sep.hiNum sep.source]; exact hf⟩
  have hi := MotifDirectionInit.hoareTime m L base (List.ofFn mask) (List.ofFn flags)
    (by simpa only [List.length_ofFn] using hn) (by simpa only [List.length_ofFn] using hn) before input emitted S hS
  have hb := MotifDirectionBuild.hoareTime m L base ha hn r sep indices hindices mask flags before input emitted R hR
  have hs := seqTM_hoareTime (MotifDirectionInit.machine m) (MotifDirectionBuild.machine m r) hi (by
    rintro inp work out ⟨hc, hp⟩
    obtain ⟨hip, hw, ho⟩ := hc.phase
    rw [hip, hw, ho]
    exact ⟨hc, map_state m L base (List.ofFn mask) (List.ofFn flags) 0 S R work (fun h => h.1) hp,
      hp.1.2.2.2.2.2⟩) hb
  exact hs.consequence (by
    rintro inp work out ⟨hc, ⟨hsa, hz, hidx, hbuf, hr⟩, hm, hf, hcount⟩
    exact ⟨hc, ⟨hsa, hz, hidx, hbuf, hr, hcount⟩, hm, hf⟩) (by
      rintro inp work out ⟨hc, hp, hr⟩
      have hm : At (List.ofFn mask) (List.ofFn mask).length (work (buffer m 1)) := by
        simpa only [List.length_ofFn] using hp.2.1
      have hf : At (List.ofFn flags) (List.ofFn flags).length (work (buffer m 2)) := by
        simpa only [List.length_ofFn] using hp.2.2
      exact ⟨hc, hp.1, hm.stored, hf.stored, hr⟩) (by
        unfold MotifDirectionBuild.timeBound timeBound
        omega)

end JointThermoComplexity.Complexity.MotifDirections

#print axioms JointThermoComplexity.Complexity.MotifDirections.hoareTime
