module
public import proofs.JointThermoComplexity.Complexity.OuterFuelCopy
public import proofs.JointThermoComplexity.Complexity.OuterMotifForwardEntryBank

set_option autoImplicit false
@[expose] public section

/-! Changing only copied outer fuel preserves original counts, production-bank resources and prepared motif state. -/

namespace JointThermoComplexity.Complexity.OuterFuelCopyFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt OuterFuelPorts

def Unchanged (m : ℕ) (work work' : Fin (m + 22) → Tape) : Prop :=
  ∀ j, j ≠ destination m 0 → j ≠ destination m 1 → work' j = work j

theorem of_single (m : ℕ) (k : Fin 2) (work work' : Fin (m + 22) → Tape)
    (hw : ∀ j, j ≠ destination m k → work' j = work j) : Unchanged m work work' := by
  intro j h0 h1
  have hk : k = 0 ∨ k = 1 := by
    have hi := k.isLt
    rcases show k.val = 0 ∨ k.val = 1 by omega with he | he
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Fin.ext he)
  rcases hk with rfl | rfl
  · exact hw j h0
  · exact hw j h1

theorem outside (m : ℕ) (work work' : Fin (m + 22) → Tape) (hw : Unchanged m work work')
    (j : Fin (m + 22)) (hj : j.val ≤ 13 ∨ 16 ≤ j.val) : work' j = work j := by
  apply hw j
  · intro he; have hv := congrArg Fin.val he; change j.val = 14 at hv; omega
  · intro he; have hv := congrArg Fin.val he; change j.val = 15 at hv; omega

theorem kept (m : ℕ) (input : List Bool) (work work' : Fin (m + 22) → Tape) (hw : Unchanged m work work') :
    CurrentPins.Kept (m + 7) input work → CurrentPins.Kept (m + 7) input work' := by
  have ho := outside m work work' hw (CountLayout.offset (m + 14)) (Or.inl (by change (0 : ℕ) ≤ 13; omega))
  have hb := outside m work work' hw (CountLayout.binder (m + 14)) (Or.inl (by change (1 : ℕ) ≤ 13; omega))
  have hm := outside m work work' hw (RoutedNetworkParser.master (m + 16)) (Or.inr (by change 16 ≤ m + 16; omega))
  have hc : ∀ i : Fin 3, work' (RoutedNetworkParser.count (m + 16) i) = work (RoutedNetworkParser.count (m + 16) i) := by
    intro i
    exact outside m work work' hw _ (Or.inr (by change 16 ≤ m + 16 + 1 + i.val; omega))
  intro hp
  change IsReg _ (work' (CountLayout.offset (m + 14))) ∧ IsReg _ (work' (CountLayout.binder (m + 14))) ∧
    (work' (RoutedNetworkParser.master (m + 16))).head = 1 ∧
    (work' (RoutedNetworkParser.master (m + 16))).read = Γ.ofBool (NetworkInputControl.accepted input) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 16) 0)) ∧
    IsReg _ (work' (RoutedNetworkParser.count (m + 16) 1)) ∧ IsReg _ (work' (RoutedNetworkParser.count (m + 16) 2))
  rw [ho, hb, hm, hc 0, hc 1, hc 2]
  exact hp

theorem metadata (m : ℕ) (input : List Bool) (work work' : Fin (m + 22) → Tape) (hw : Unchanged m work work') :
    MotifBufferMeta.State (m + 7) input work → MotifBufferMeta.State (m + 7) input work' := by
  have hraw := outside m work work' hw (CurrentPorts.raw (m + 7)) (Or.inr (by change 16 ≤ m + 21; omega))
  have hprev := outside m work work' hw (MonomialPorts.previous (m + 8)) (Or.inl (by change (6 : ℕ) ≤ 13; omega))
  rintro ⟨hk, hr, old, hold, hp⟩
  exact ⟨kept m input work work' hw hk, by simpa only [hraw] using hr,
    old, hold, by simpa only [hprev] using hp⟩

theorem bank (m : ℕ) (work work' : Fin (m + 22) → Tape) (hw : Unchanged m work work') :
    ProductionBank.State (m + 2) work → ProductionBank.State (m + 2) work' := by
  intro hb j hlo hhi
  exact (outside m work work' hw j (Or.inl hhi)).trans (hb j hlo hhi)

theorem separate (m : ℕ) (k : Fin 2) : BoxState.Separate (m + 7) (destination m k) := by
  have hx (j : Fin (m + 22)) (hj : j.val ≤ 8) : destination m k ≠ j := by
    intro he; have hv := congrArg Fin.val he; change 14 + k.val = j.val at hv; omega
  exact ⟨hx _ (by change (7 : ℕ) ≤ 8; omega), hx _ (by change (5 : ℕ) ≤ 8; omega),
    hx _ (by change (2 : ℕ) ≤ 8; omega), hx _ (by change (3 : ℕ) ≤ 8; omega),
    hx _ (by change (4 : ℕ) ≤ 8; omega), hx _ (by change (8 : ℕ) ≤ 8; omega)⟩

theorem prepared_replace (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (k : Fin 2)
    (work work' : Fin (m + 22) → Tape) (hw : ∀ j, j ≠ destination m k → work' j = work j)
    (ht : Parked (work' (destination m k))) (hp : MotifPreparedMasks.Ready (m + 7) input Q work) :
    MotifPreparedMasks.Ready (m + 7) input Q work' := by
  have hmeta : MotifPreparedMasks.Metadata (m + 7) input Q work → MotifPreparedMasks.Metadata (m + 7) input Q work' := by
    rintro ⟨hm, hf⟩
    have hu := of_single m k work work' hw
    exact ⟨metadata m input work work' hu hm,
      by simpa only [outside m work work' hu (MotifBufferPorts.buffer (m + 7) 2) (Or.inl (by change (4 : ℕ) ≤ 13; omega))] using hf⟩
  exact BoxState.replace (m + 7) input.length Q.speciesCount
    (MotifPreparedMasks.Metadata (m + 7) input Q) (MotifPreparedMasks.Metadata (m + 7) input Q)
    (destination m k) (separate m k) work work' hw ht hmeta hp

theorem counts (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (work : Fin (m + 22) → Tape) (h : CurrentPins.Kept (m + 7) input work) :
    IsReg Q.speciesCount (work (source m 0)) ∧ IsReg Q.coreCount (work (source m 1)) := by
  have hc := ParserRegisters.decoded_counts (m + 16) input (CountAppend.oldWork work) h.2.2 hd
  exact ⟨hc.1, hc.2.2⟩

end JointThermoComplexity.Complexity.OuterFuelCopyFrame

#print axioms JointThermoComplexity.Complexity.OuterFuelCopyFrame.prepared_replace
#print axioms JointThermoComplexity.Complexity.OuterFuelCopyFrame.counts
