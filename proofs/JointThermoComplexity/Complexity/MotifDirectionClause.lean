module
public import proofs.JointThermoComplexity.Complexity.MotifDirectionState
public import proofs.JointThermoComplexity.Complexity.MaskedDirectionOutput
public import proofs.JointThermoComplexity.Complexity.TemplateRuntime

set_option autoImplicit false
@[expose] public section

/-! Emit one exact right-nested direction clause from actual synchronized stored bits. -/

namespace JointThermoComplexity.Complexity.MotifDirectionClause
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts MotifDirectionState PowerPorts MonomialPorts CircuitSerialization

variable {arity : ℕ}

def machine (m : ℕ) : TM (m + 15) := seqTM (emitBitsTM conjunctionTag)
  (MaskedDirectionOutput.machine (buffer m 1) (buffer m 2) (scratch (m + 2)) (species (m + 1)))

def word (selected forward : Bool) (idx : Fin arity) : List Bool :=
  conjunctionTag ++ MaskedDirectionOutput.word selected forward idx

def timeBound (L : ℕ) : ℕ := 32 * L ^ 2 + 48 * L + 40

theorem hoareTime (m L : ℕ) (ha : arity ≤ 4 * L) (idx : Fin arity) (mask flags : List Bool) (i : ℕ)
    (him : i < mask.length) (hif : i < flags.length) (before input emitted : List Bool)
    (R : (Fin (m + 15) → Tape) → Prop) :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ State m L idx.val mask flags i R work)
      (fun inp work out => Cursor before input (emitted ++ word mask[i] flags[i] idx) inp work out ∧
        State m L idx.val mask flags i R work) (timeBound L) := by
  have hc := FixedOutput.hoareTime conjunctionTag before input emitted (State m L idx.val mask flags i R)
  have hm : (MaskedDirectionOutput.machine (buffer m 1) (buffer m 2) (scratch (m + 2)) (species (m + 1))).HoareTime
      (fun inp work out => Cursor before input (emitted ++ conjunctionTag) inp work out ∧ State m L idx.val mask flags i R work)
      (fun inp work out => Cursor before input ((emitted ++ conjunctionTag) ++ MaskedDirectionOutput.word mask[i] flags[i] idx) inp work out ∧
        State m L idx.val mask flags i R work) (VariableOutput.timeBound idx.val + 18) := by
    rintro inp work out ⟨hcur, hp⟩
    obtain ⟨d, t, ht, hreach, hhalt, hdc, hdready, _⟩ :=
      MaskedDirectionOutput.hoareTime (buffer m 1) (buffer m 2) (scratch (m + 2)) (species (m + 1))
        (species_ne_scratch (m + 1)) mask[i] flags[i] idx before input (emitted ++ conjunctionTag)
        (fun work' => work' = work) inp work out
        ⟨hcur, ⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, rfl⟩, hp.2.2.read hif, hp.2.1.read him⟩
    have hdw : d.work = work := hdready.2.2.2
    exact ⟨d, t, ht, hreach, hhalt, hdc, by simpa only [hdw] using hp⟩
  have hs := seqTM_hoareTime (emitBitsTM conjunctionTag)
    (MaskedDirectionOutput.machine (buffer m 1) (buffer m 2) (scratch (m + 2)) (species (m + 1))) hc (by
      rintro inp work out ⟨hcur, _, hp⟩
      obtain ⟨hi, hw, ho⟩ := hcur.phase
      rw [hi, hw, ho]
      exact ⟨hcur, hp⟩) hm
  exact hs.consequence (fun _ _ _ ⟨hc, hp⟩ => ⟨hc, hp.1.1, hp⟩)
    (fun _ _ _ h => by simpa only [word, List.append_assoc] using h) (by
      have hv := TemplateRuntime.variable_bound (idx.isLt.le.trans ha)
      unfold timeBound
      simp only [conjunctionTag, List.length_cons, List.length_nil]
      omega)

end JointThermoComplexity.Complexity.MotifDirectionClause

#print axioms JointThermoComplexity.Complexity.MotifDirectionClause.hoareTime
