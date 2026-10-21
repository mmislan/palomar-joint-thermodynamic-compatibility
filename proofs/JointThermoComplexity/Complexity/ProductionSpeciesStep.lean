module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesClause
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesAdvance

set_option autoImplicit false
@[expose] public section

/-! One supplied-species iteration emits its exact conjunction clause and advances the index and mask. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesStep
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState

def word (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (s : Fin Q.speciesCount) : List Bool :=
  CircuitSerialization.conjunctionTag ++ (ProductionSpeciesClause.formula Q a s).code

def machine (m : ℕ) : TM (m + 22) := seqTM
  (seqTM (emitBitsTM CircuitSerialization.conjunctionTag) (ProductionSpeciesClause.machine m))
  (ProductionSpeciesAdvance.machine m)

def timeBound (L : ℕ) : ℕ := 4 * L ^ 4 + 52 * L ^ 3 + 150 * L ^ 2 + 184 * L + 62

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (s : Fin Q.speciesCount) (emitted : List Bool)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ State m input Q a s.val R work)
      (fun inp work out => Cursor [] input (emitted ++ word Q a s) inp work out ∧ State m input Q a (s.val + 1) R work)
      (timeBound input.length) := by
  have hf := FixedOutput.hoareTime CircuitSerialization.conjunctionTag [] input emitted (State m input Q a s.val R)
  have hc := ProductionSpeciesClause.hoareTime m input Q hd a s (emitted ++ CircuitSerialization.conjunctionTag) R hR
  have ha := ProductionSpeciesAdvance.hoareTime m input Q a s.val [] input
    ((emitted ++ CircuitSerialization.conjunctionTag) ++ (ProductionSpeciesClause.formula Q a s).code) R hR
  have hfc := seqTM_hoareTime (emitBitsTM CircuitSerialization.conjunctionTag) (ProductionSpeciesClause.machine m) hf (by
    rintro inp work out ⟨hcur, _, hp⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨hcur, hp⟩) hc
  have hfull := seqTM_hoareTime
    (seqTM (emitBitsTM CircuitSerialization.conjunctionTag) (ProductionSpeciesClause.machine m))
    (ProductionSpeciesAdvance.machine m) hfc (by
      rintro inp work out ⟨hcur, hp⟩
      obtain ⟨hi, hw, ho⟩ := hcur.phase
      rw [hi, hw, ho]
      exact ⟨hcur, hp⟩) ha
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  have hsi : s.val ≤ input.length := by have hs := s.isLt; omega
  exact hfull.consequence (fun _ work _ ⟨hcur, hp⟩ => ⟨hcur, safe m input Q a s.val R work hp, hp⟩) (by
    rintro inp work out ⟨hcur, hp⟩
    exact ⟨by simpa only [word, List.append_assoc] using hcur, hp⟩) (by
      unfold timeBound ProductionSpeciesClause.timeBound ProductionPositiveOutput.timeBound CircuitSerialization.conjunctionTag
      simp only [List.length_cons, List.length_nil]
      omega)

end JointThermoComplexity.Complexity.ProductionSpeciesStep

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesStep.hoareTime
