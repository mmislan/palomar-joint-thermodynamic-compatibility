module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesFrame

set_option autoImplicit false
@[expose] public section

/-! A species iteration retains bounded actual reaction/current values and the two supplied-mask states. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesState
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState

def Fixed (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount)
    (R : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape) : Prop :=
  CurrentPins.Kept (m + 7) input work ∧ IsReg (ArityValue.arity input) (work (CurrentPorts.raw (m + 7))) ∧
    Stored (BoxTraversalData.forward Q) (work (MotifBufferPorts.buffer (m + 7) 2)) ∧
    IsReg a.val (work (ProductionPorts.core (m + 2))) ∧ R work

def State (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (pos : ℕ)
    (R : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape) : Prop :=
  ∃ ri, ri ≤ 4 * input.length ∧ ∃ idx, idx ≤ input.length ∧
    ProductionOperandLoad.State (m + 2) input.length Q.speciesCount ri pos work ∧
    IsReg idx (work (ProductionPorts.current (m + 2))) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 9))) ∧
    MotifDirectionState.At (MotifMaskData.species (Q.network.motifs a)) pos (work (MotifBufferPorts.buffer (m + 7) 0)) ∧
    Stored (MotifMaskData.reactions (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 7) 1)) ∧ Fixed m input Q a R work

def AtStart (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (pos : ℕ)
    (R : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape) : Prop :=
  ProductionOperandLoad.State (m + 2) input.length Q.speciesCount 0 pos work ∧
    IsReg Q.speciesCount (work (ProductionPorts.current (m + 2))) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 9))) ∧
    MotifDirectionState.At (MotifMaskData.species (Q.network.motifs a)) pos (work (MotifBufferPorts.buffer (m + 7) 0)) ∧
    Stored (MotifMaskData.reactions (Q.network.motifs a)) (work (MotifBufferPorts.buffer (m + 7) 1)) ∧ Fixed m input Q a R work

theorem safe (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (pos : ℕ)
    (R : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape) (h : State m input Q a pos R work) :
    ∀ j, Parked (work j) := by
  obtain ⟨_, _, _, _, hp, _⟩ := h
  exact hp.safe

theorem fixed_frame (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work')
    (work work' : Fin (m + 22) → Tape) (hw : ProductionSpeciesFrame.Unchanged m work work') :
    Fixed m input Q a R work → Fixed m input Q a R work' := by
  have hraw := ProductionSpeciesFrame.outside m work work' hw (CurrentPorts.raw (m + 7))
    (Or.inr (Or.inr (by change 13 ≤ m + 21; omega)))
  have hforward := ProductionSpeciesFrame.outside m work work' hw (MotifBufferPorts.buffer (m + 7) 2) (Or.inr (Or.inl rfl))
  have hcore := ProductionSpeciesFrame.outside m work work' hw (ProductionPorts.core (m + 2))
    (Or.inr (Or.inr (by change 13 ≤ (13 : ℕ); omega)))
  rintro ⟨hk, hr, hf, hc, hrest⟩
  exact ⟨ProductionSpeciesFrame.kept m input work work' hw hk,
    by simpa only [hraw] using hr, by simpa only [hforward] using hf,
    by simpa only [hcore] using hc, hR work work' hw hrest⟩

theorem map_state (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (pos : ℕ)
    (R S : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape)
    (hr : R work → S work) (hp : State m input Q a pos R work) : State m input Q a pos S work := by
  obtain ⟨ri, hri, idx, hidx, hdata, hi, hz, hm, hreact, hk, hraw, hf, hc, hR⟩ := hp
  exact ⟨ri, hri, idx, hidx, hdata, hi, hz, hm, hreact, hk, hraw, hf, hc, hr hR⟩

theorem start_to_state (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (pos : ℕ)
    (hn : Q.speciesCount ≤ input.length) (R : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape)
    (hp : AtStart m input Q a pos R work) : State m input Q a pos R work :=
  ⟨0, by omega, Q.speciesCount, hn, hp⟩

end JointThermoComplexity.Complexity.ProductionSpeciesState

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesState.fixed_frame
#print axioms JointThermoComplexity.Complexity.ProductionSpeciesState.start_to_state
