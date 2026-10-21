module
public import proofs.JointThermoComplexity.Complexity.MotifNextStart
public import proofs.JointThermoComplexity.Complexity.MotifIndexedAccess

set_option autoImplicit false
@[expose] public section

/-! One complete actual core iteration locates its supplied record, emits both constraints and returns to original input start. -/

namespace JointThermoComplexity.Complexity.MotifCoreStep
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifCoreState

def word (Q : NetworkCodec.Input) (a : Fin Q.coreCount) : List Bool :=
  CircuitSerialization.conjunctionTag ++ (MotifCompleteBody.formula Q a).code

def machine (m : ℕ) : TM (m + 22) := seqTM (MotifIndexedAccess.machine m)
  (seqTM (emitBitsTM CircuitSerialization.conjunctionTag) (seqTM (MotifCompleteBody.machine m) (MotifNextStart.machine m)))

def timeBound (L : ℕ) : ℕ := 4 * L ^ 5 + 52 * L ^ 4 + 184 * L ^ 3 + 252 * L ^ 2 + 192 * L + 114

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', MotifCompleteFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ State m input Q a.val R work ∧
        IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)))
      (fun inp work out => Cursor [] input (emitted ++ word Q a) inp work out ∧ State m input Q (a.val + 1) R work ∧
        IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0))) (timeBound input.length) := by
  let R' : (Fin (m + 22) → Tape) → Prop := fun work => R work ∧ IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0))
  have hR' : ∀ work work', MotifCompleteFrame.Unchanged m work work' → R' work → R' work' := by
    rintro work work' hw ⟨hr, hf⟩
    have hfu := hw (OuterFuelPorts.destination m 0) (Or.inr (by change 14 ≤ (14 : ℕ); omega))
    exact ⟨hR work work' hw hr, by simpa only [hfu] using hf⟩
  let P : (Fin (m + 22) → Tape) → Prop := fun work => State m input Q a.val R work ∧
    IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0))
  have ha := MotifIndexedAccess.hoareTime m a.val input Q hd a.isLt.le [] input emitted rfl (fun work _ => P work)
  have hf := FixedOutput.hoareTime CircuitSerialization.conjunctionTag (MotifPrefixData.before Q a.val)
    ((DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a) ++ MotifPrefixData.remaining Q (a.val + 1)) emitted P
  have hbody : (MotifCompleteBody.machine m).HoareTime
      (fun inp work out => Cursor (MotifPrefixData.before Q a.val)
        ((DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a) ++ MotifPrefixData.remaining Q (a.val + 1))
        (emitted ++ CircuitSerialization.conjunctionTag) inp work out ∧ P work)
      (fun inp work out => Cursor [] input
        ((emitted ++ CircuitSerialization.conjunctionTag) ++ (MotifCompleteBody.formula Q a).code) inp work out ∧
        ProductionSpeciesState.State m input Q a Q.speciesCount R work ∧
        IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)) ∧
        BoxBufferState.Stored (MotifMaskData.species (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 7) 0)))
      (MotifCompleteBody.timeBound input.length) := by
    rintro inp work out ⟨hc, ⟨hready, ri, hdata, hr⟩, hfuel⟩
    exact MotifCompleteBody.hoareTime m ri input Q hd a (MotifPrefixData.before Q a.val)
      (MotifPrefixData.remaining Q (a.val + 1)) (emitted ++ CircuitSerialization.conjunctionTag) (by
        rw [← MotifPrefixData.remaining_at Q a]
        exact MotifPrefixData.input_split input Q hd a.val) R
      (fun work work' hw => hR work work' (MotifCompleteFrame.of_motif m work work' hw))
      (fun work work' hw => hR work work' (MotifCompleteFrame.of_species m work work' hw))
      inp work out ⟨hc, hready, hdata, hr, hfuel⟩
  have hn := MotifNextStart.hoareTime m input Q hd a [] input
    ((emitted ++ CircuitSerialization.conjunctionTag) ++ (MotifCompleteBody.formula Q a).code) R' hR'
  have hbn := seqTM_hoareTime (MotifCompleteBody.machine m) (MotifNextStart.machine m) hbody (by
    rintro inp work out ⟨hc, hp, hfuel, _⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, ProductionSpeciesState.map_state m input Q a Q.speciesCount R R' work (fun hr => ⟨hr, hfuel⟩) hp⟩) hn
  have hfbn := seqTM_hoareTime (emitBitsTM CircuitSerialization.conjunctionTag)
    (seqTM (MotifCompleteBody.machine m) (MotifNextStart.machine m)) hf (by
      rintro inp work out ⟨hc, _, hp⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hp⟩) hbn
  have hfull := seqTM_hoareTime (MotifIndexedAccess.machine m)
    (seqTM (emitBitsTM CircuitSerialization.conjunctionTag) (seqTM (MotifCompleteBody.machine m) (MotifNextStart.machine m))) ha (by
      rintro inp work out ⟨hc, hs, _, _, hp⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨by simpa only [MotifPrefixData.remaining_at Q a] using hc, hs, hp⟩) hfbn
  exact hfull.consequence (by
    rintro inp work out ⟨hc, hp, hfuel⟩
    have hcore : IsReg a.val (work (MotifIndexedAccess.core m)) := by
      obtain ⟨_, _, hdata, _⟩ := hp
      exact hdata.corePosition
    exact ⟨hc, hp.1.1, hp.1.2.2.2.2.1.1, hcore, hp, hfuel⟩) (by
      rintro inp work out ⟨hc, hp⟩
      have hfuel : IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)) := by
        obtain ⟨_, _, _, hr⟩ := hp
        exact hr.2
      exact ⟨by simpa only [word, List.append_assoc] using hc,
        map_state m input Q (a.val + 1) R' R work (fun h => h.1) hp, hfuel⟩) (by
          unfold timeBound MotifIndexedAccess.timeBound MotifCompleteBody.timeBound MotifNextStart.timeBound
            CircuitSerialization.conjunctionTag
          simp only [List.length_cons, List.length_nil]
          omega)

end JointThermoComplexity.Complexity.MotifCoreStep

#print axioms JointThermoComplexity.Complexity.MotifCoreStep.hoareTime
