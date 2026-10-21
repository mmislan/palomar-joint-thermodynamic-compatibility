module
public import proofs.JointThermoComplexity.Complexity.PreparedLocalEquation
public import proofs.JointThermoComplexity.Complexity.InitializedForwardQuery

set_option autoImplicit false
@[expose] public section

/-! A shared physical frame joins query counters, address registers and an outer cursor checkpoint. -/

namespace JointThermoComplexity.Complexity.LocalBranchState
open _root_.Complexity _root_.Complexity.TM HeaderAt RelocatedSpanQuery QueryWorkFrame QueryCounterInit

def anchor : Fin 32 := ⟨30, by decide⟩
def scratch : Fin 32 := ⟨29, by decide⟩

def Protected (j : Fin 32) : Prop := j.val < 8 ∨ j.val = 16 ∨ j.val = 18 ∨ j.val = 28 ∨ j.val = 29 ∨ j.val = 31

def Stable (R : Work → Prop) : Prop :=
  ∀ work work', (∀ j, Protected j → work' j = work j) → R work → R work'

def BasicPorts (j : Fin 32) : Prop := j.val < 19 ∨ j = scratch

structure Basic (counts : Counts) (L : ℕ) (R : Work → Prop) (work : Work) : Prop where
  tagHeads : ∀ i, (work (tags i)).head = 1
  flagHead : (work flag).head = 1
  termReg : IsReg counts.terms (work pending)
  formulaReg : IsReg counts.formulas (work formulas)
  nodeReg : IsReg counts.nodes (work result)
  fuelReg : IsReg L (work fuel)
  positionReg : IsReg 0 (work position)
  scratchReg : IsReg 0 (work scratch)
  frame : R work

structure Ready (counts : Counts) (values : Fin 9 → ℕ) (L : ℕ) (R : Work → Prop) (work : Work) : Prop where
  basic : Basic counts L R work
  markers : ∀ j, j ≠ anchor → (work j).cells 0 = Γ.start
  addresses : AddressCounterPlacement.Registers values work

theorem protected_anchor : ∀ j, Protected j → j ≠ anchor := by unfold Protected; decide
theorem basic_anchor : ∀ j, BasicPorts j → j ≠ anchor := by unfold BasicPorts; decide
theorem protected_query : ∀ j, Protected j → QueryWorkFrame.Outside j := by
  unfold Protected QueryWorkFrame.Outside
  decide
theorem protected_address : ∀ j, Protected j → ¬AddressCounterPlacement.InBlock j := by
  unfold Protected AddressCounterPlacement.InBlock placeWorkInMiddle
  decide
theorem basic_address : ∀ j, BasicPorts j → ¬AddressCounterPlacement.InBlock j := by
  unfold BasicPorts AddressCounterPlacement.InBlock placeWorkInMiddle
  decide

theorem slot_anchor (i : Fin 9) : AddressCounterPlacement.slot i ≠ anchor := by
  intro he
  have hv := congrArg Fin.val he
  change 19 + i.val = 30 at hv
  omega

theorem slot_query (i : Fin 9) : QueryWorkFrame.Outside (AddressCounterPlacement.slot i) := by
  refine ⟨Or.inr ?_, ?_⟩
  · change 16 ≤ 19 + i.val
    omega
  · intro he
    have hv := congrArg Fin.val he
    change 19 + i.val = 17 at hv
    omega

theorem basic_transfer (counts : Counts) (L : ℕ) (R : Work → Prop) (work work' : Work)
    (hr : Basic counts L R work) (he : ∀ j, BasicPorts j → work' j = work j) (hR : R work') :
    Basic counts L R work' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hR⟩
  · intro i
    have hi : BasicPorts (tags i) := Or.inl (by change i.val + 8 < 19; omega)
    simpa only [he _ hi] using hr.tagHeads i
  · simpa only [he _ (by left; decide : BasicPorts flag)] using hr.flagHead
  · simpa only [he _ (by left; decide : BasicPorts pending)] using hr.termReg
  · simpa only [he _ (by left; decide : BasicPorts formulas)] using hr.formulaReg
  · simpa only [he _ (by left; decide : BasicPorts result)] using hr.nodeReg
  · simpa only [he _ (by left; decide : BasicPorts fuel)] using hr.fuelReg
  · simpa only [he _ (by left; decide : BasicPorts position)] using hr.positionReg
  · simpa only [he _ (Or.inr rfl)] using hr.scratchReg

theorem ready_anchor (counts : Counts) (values : Fin 9 → ℕ) (L : ℕ) (R : Work → Prop) (hR : Stable R) :
    ∀ work work', (∀ j, j ≠ anchor → work' j = work j) → Ready counts values L R work → Ready counts values L R work' := by
  rintro work work' he hr
  refine ⟨basic_transfer counts L R work work' hr.basic (fun j hj => he j (basic_anchor j hj))
    (hR work work' (fun j hj => he j (protected_anchor j hj)) hr.basic.frame), ?_, ?_⟩
  · intro j hj
    simpa only [he j hj] using hr.markers j hj
  · intro i
    simpa only [he _ (slot_anchor i)] using hr.addresses i

def QueryExtra (p : ℕ) (values : Fin 9 → ℕ) (R : Work → Prop) (work : Work) : Prop :=
  AddressCounterPlacement.Registers values work ∧ IsReg p (work anchor) ∧ IsReg 0 (work scratch) ∧ R work

theorem query_extra_stable (p : ℕ) (values : Fin 9 → ℕ) (R : Work → Prop) (hR : Stable R) :
    QueryWorkFrame.Stable (QueryExtra p values R) := by
  rintro work work' he ⟨ha, hp, hs, hr⟩
  refine ⟨?_, ?_, ?_, hR work work' (fun j hj => he j (protected_query j hj)) hr⟩
  · intro i
    simpa only [he _ (slot_query i)] using ha i
  · simpa only [he _ (by unfold QueryWorkFrame.Outside; decide : QueryWorkFrame.Outside anchor)] using hp
  · simpa only [he _ (by unfold QueryWorkFrame.Outside; decide : QueryWorkFrame.Outside scratch)] using hs

theorem to_query (counts : Counts) (values : Fin 9 → ℕ) (L p : ℕ) (R : Work → Prop) (work : Work)
    (hr : Ready counts values L R work) (hp : IsReg p (work anchor)) :
    QueryWorkFrame.Ready counts.terms counts.formulas counts.nodes L (QueryExtra p values R) work := by
  refine ⟨?_, hr.basic.tagHeads, hr.basic.flagHead, hr.basic.termReg, hr.basic.formulaReg, hr.basic.nodeReg,
    hr.basic.fuelReg, hr.addresses, hp, hr.basic.scratchReg, hr.basic.frame⟩
  intro j _
  by_cases hj : j = anchor
  · subst j
    exact hp.cell0
  · exact hr.markers j hj

theorem from_query (counts : Counts) (values : Fin 9 → ℕ) (L p : ℕ) (R : Work → Prop) (work : Work)
    (hr : QueryWorkFrame.Ready counts.terms counts.formulas counts.nodes L (QueryExtra p values R) work)
    (hp : IsReg 0 (work position)) : Ready counts values L R work ∧ IsReg p (work anchor) := by
  refine ⟨⟨⟨hr.tagHeads, hr.flagHead, hr.termReg, hr.formulaReg, hr.nodeReg, hr.fuelReg,
    hp, hr.frame.2.2.1, hr.frame.2.2.2⟩, ?_, hr.frame.1⟩, hr.frame.2.1⟩
  intro j _
  by_cases hj : j = position
  · subst j
    exact hp.cell0
  · exact hr.markers j hj

end JointThermoComplexity.Complexity.LocalBranchState

#print axioms JointThermoComplexity.Complexity.LocalBranchState.ready_anchor
#print axioms JointThermoComplexity.Complexity.LocalBranchState.query_extra_stable
#print axioms JointThermoComplexity.Complexity.LocalBranchState.from_query
