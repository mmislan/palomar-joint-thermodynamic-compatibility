module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesState

set_option autoImplicit false
@[expose] public section

/-! The actual species index and supplied-mask head advance together, retaining bounded production state. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesAdvance
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState

def WorkState (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (pos k : ℕ)
    (R : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape) : Prop :=
  ∃ ri, ri ≤ 4 * input.length ∧ ∃ idx, idx ≤ input.length ∧
    ProductionOperandLoad.State (m + 2) input.length Q.speciesCount ri pos work ∧
    IsReg idx (work (ProductionPorts.current (m + 2))) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 9))) ∧
    MotifDirectionState.At (MotifMaskData.species (Q.network.motifs a)) k (work (MotifBufferPorts.buffer (m + 7) 0)) ∧
    BoxBufferState.Stored (MotifMaskData.reactions (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 7) 1)) ∧ Fixed m input Q a R work

theorem index_hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (pos k : ℕ)
    (before remaining emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (UnarySuccessor.machine (ProductionPorts.species (m + 2))).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ WorkState m input Q a pos k R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ WorkState m input Q a (pos + 1) k R work) (2 * pos + 6) := by
  rintro inp work out ⟨hc, hp⟩
  obtain ⟨ri, hri, idx, hidx, hdata, hi, hz, hm, hr, hf⟩ := hp
  let P : (Fin (m + 22) → Tape) → Prop := fun work' => ∀ j, j ≠ ProductionPorts.species (m + 2) → work' j = work j
  have hP : ∀ work' work'', (∀ j, j ≠ ProductionPorts.species (m + 2) → work'' j = work' j) → P work' → P work'' := by
    intro work' work'' hw hp j hj
    exact (hw j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hs, hpos, hw⟩ :=
    UnarySuccessor.hoareTime (ProductionPorts.species (m + 2)) pos before remaining emitted P hP
      inp work out ⟨hc, hdata.safe, hdata.speciesPosition, fun _ _ => rfl⟩
  have hx (j : Fin (m + 22)) (hj : j.val ≠ 12) : d.work j = work j := by
    apply hw j
    intro he
    exact hj (congrArg Fin.val he)
  have hdata' : ProductionOperandLoad.State (m + 2) input.length Q.speciesCount ri (pos + 1) d.work :=
    ⟨hs, by simpa only [hx (ProductionPorts.left (m + 2)) (by change (9 : ℕ) ≠ 12; omega)] using hdata.productReusable,
      by simpa only [hx (ProductionPorts.right (m + 2)) (by change (10 : ℕ) ≠ 12; omega)] using hdata.reactantReusable,
      by simpa only [hx (ProductionPorts.magnitude (m + 2)) (by change (8 : ℕ) ≠ 12; omega)] using hdata.magnitudeReusable,
      by simpa only [hx (ProductionPorts.sign (m + 2)) (by change (11 : ℕ) ≠ 12; omega)] using hdata.signHead,
      hpos, by simpa only [hx (ProductionPorts.count (m + 2)) (by change m + 17 ≠ 12; omega)] using hdata.speciesCount,
      by simpa only [hx (ProductionPorts.reaction (m + 2)) (by change (6 : ℕ) ≠ 12; omega)] using hdata.reactionPosition⟩
  exact ⟨d, t, ht, hreach, hhalt, hdc, ri, hri, idx, hidx, hdata',
    by simpa only [hx (ProductionPorts.current (m + 2)) (by change (7 : ℕ) ≠ 12; omega)] using hi,
    by simpa only [hx (PowerPorts.scratch (m + 9)) (by change (5 : ℕ) ≠ 12; omega)] using hz,
    by simpa only [hx (MotifBufferPorts.buffer (m + 7) 0) (by change (2 : ℕ) ≠ 12; omega)] using hm,
    by simpa only [hx (MotifBufferPorts.buffer (m + 7) 1) (by change (3 : ℕ) ≠ 12; omega)] using hr,
    fixed_frame m input Q a R hR work d.work (ProductionSpeciesFrame.of_species m work d.work hw) hf⟩

def ports (m : ℕ) : List (Fin (m + 22)) := [MotifBufferPorts.buffer (m + 7) 0]

theorem advance_mask_state (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (pos k : ℕ)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work')
    (work : Fin (m + 22) → Tape) (hp : WorkState m input Q a pos k R work) :
    WorkState m input Q a pos (k + 1) R (WorkHeadsAdvance.advance (ports m) work) := by
  obtain ⟨ri, hri, idx, hidx, hdata, hi, hz, hm, hr, hf⟩ := hp
  let work' := WorkHeadsAdvance.advance (ports m) work
  have hw (j : Fin (m + 22)) (hj : j ≠ MotifBufferPorts.buffer (m + 7) 0) : work' j = work j := by
    simp only [work', WorkHeadsAdvance.advance, ports, List.mem_singleton, hj, ↓reduceIte]
  have hx (j : Fin (m + 22)) (hj : j.val ≠ 2) : work' j = work j := by
    apply hw j
    intro he
    exact hj (congrArg Fin.val he)
  have hs := WorkHeadsAdvance.parked (ports m) work hdata.safe
  have hdata' : ProductionOperandLoad.State (m + 2) input.length Q.speciesCount ri pos work' :=
    ⟨hs, by simpa only [hx (ProductionPorts.left (m + 2)) (by change (9 : ℕ) ≠ 2; omega)] using hdata.productReusable,
      by simpa only [hx (ProductionPorts.right (m + 2)) (by change (10 : ℕ) ≠ 2; omega)] using hdata.reactantReusable,
      by simpa only [hx (ProductionPorts.magnitude (m + 2)) (by change (8 : ℕ) ≠ 2; omega)] using hdata.magnitudeReusable,
      by simpa only [hx (ProductionPorts.sign (m + 2)) (by change (11 : ℕ) ≠ 2; omega)] using hdata.signHead,
      by simpa only [hx (ProductionPorts.species (m + 2)) (by change (12 : ℕ) ≠ 2; omega)] using hdata.speciesPosition,
      by simpa only [hx (ProductionPorts.count (m + 2)) (by change m + 17 ≠ 2; omega)] using hdata.speciesCount,
      by simpa only [hx (ProductionPorts.reaction (m + 2)) (by change (6 : ℕ) ≠ 2; omega)] using hdata.reactionPosition⟩
  have hm' : MotifDirectionState.At (MotifMaskData.species (Q.network.motifs a)) (k + 1)
      (work' (MotifBufferPorts.buffer (m + 7) 0)) := by
    simpa only [work', WorkHeadsAdvance.advance, ports, List.mem_singleton, ↓reduceIte] using hm.advance
  refine ⟨ri, hri, idx, hidx, hdata', ?_, ?_, hm', ?_, ?_⟩
  · change IsReg idx (work' (ProductionPorts.current (m + 2)))
    rw [hx _ (by change (7 : ℕ) ≠ 2; omega)]
    exact hi
  · change BinaryIncrementRun.Register 0 (work' (PowerPorts.scratch (m + 9)))
    rw [hx _ (by change (5 : ℕ) ≠ 2; omega)]
    exact hz
  · change BoxBufferState.Stored _ (work' (MotifBufferPorts.buffer (m + 7) 1))
    rw [hx _ (by change (3 : ℕ) ≠ 2; omega)]
    exact hr
  · exact fixed_frame m input Q a R hR work work' (ProductionSpeciesFrame.of_mask m work work' hw) hf

theorem mask_hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (pos k : ℕ)
    (before remaining emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (WorkHeadsAdvance.machine (ports m)).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ WorkState m input Q a pos k R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ WorkState m input Q a pos (k + 1) R work) 1 := by
  have hs := WorkHeadsAdvance.hoareTime (ports m) before remaining emitted
    (fun work _ => WorkState m input Q a pos k R work) (fun work _ => WorkState m input Q a pos (k + 1) R work)
    (fun work _ hp => advance_mask_state m input Q a pos k R hR work hp)
  exact hs.consequence (by
    rintro inp work out ⟨hc, hp⟩
    have hsafe : ∀ j, Parked (work j) := by
      obtain ⟨_, _, _, _, hdata, _⟩ := hp
      exact hdata.safe
    exact ⟨hc, hsafe, hp⟩) (fun _ _ _ ⟨hc, _, hp⟩ => ⟨hc, hp⟩) le_rfl

def machine (m : ℕ) : TM (m + 22) := seqTM (UnarySuccessor.machine (ProductionPorts.species (m + 2)))
  (WorkHeadsAdvance.machine (ports m))

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (pos : ℕ)
    (before remaining emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m input Q a pos R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ State m input Q a (pos + 1) R work) (2 * pos + 8) := by
  have hi := index_hoareTime m input Q a pos pos before remaining emitted R hR
  have hm := mask_hoareTime m input Q a (pos + 1) pos before remaining emitted R hR
  have hs := seqTM_hoareTime (UnarySuccessor.machine (ProductionPorts.species (m + 2))) (WorkHeadsAdvance.machine (ports m)) hi (by
    rintro inp work out ⟨hc, hp⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp⟩) hm
  exact hs.mono_bound (by omega)

end JointThermoComplexity.Complexity.ProductionSpeciesAdvance

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesAdvance.index_hoareTime
#print axioms JointThermoComplexity.Complexity.ProductionSpeciesAdvance.advance_mask_state
#print axioms JointThermoComplexity.Complexity.ProductionSpeciesAdvance.hoareTime
