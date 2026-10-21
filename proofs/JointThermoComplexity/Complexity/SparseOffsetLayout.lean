module
public import proofs.JointThermoComplexity.Complexity.OffsetTemplateDispatch
public import proofs.JointThermoComplexity.Complexity.SparseTermCanonicalLoad

set_option autoImplicit false
@[expose] public section

/-! A fixed physical layout joining source parsing and offset arithmetic.
Only old work ports hold source fields; final scratch is reserved. -/

namespace JointThermoComplexity.Complexity.SparseOffsetLayout
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
open BinaryScaleBuffer (oldWork cast_ne_last)
variable {w : ℕ}

def liftSlots (slots : List (Fin w × Fin w)) : List (BoundedOccurrenceMachine.Port w) :=
  slots.map (fun p => (p.1.castSucc, p.2.castSucc))

structure Layout (w : ℕ) where
  slots : List (Fin w × Fin w)
  ending : Fin w
  flag : Fin w
  idx : Fin w
  sign : Fin w
  adjusted : Fin w
  acc : Fin w
  aux : Fin w
  length : slots.length = 4
  parse_sep : SparseTermCanonicalLoad.Separate (liftSlots slots) ending.castSucc flag.castSucc idx.castSucc sign.castSucc
  arithmetic_sep : OffsetContribution.Separate idx sign adjusted acc aux
  adjusted_outside : ¬BoundedOccurrenceMachine.Touches (liftSlots slots) ending.castSucc flag.castSucc adjusted.castSucc
  acc_outside : ¬BoundedOccurrenceMachine.Touches (liftSlots slots) ending.castSucc flag.castSucc acc.castSucc
  aux_outside : ¬BoundedOccurrenceMachine.Touches (liftSlots slots) ending.castSucc flag.castSucc aux.castSucc

abbrev Layout.Physical (d : Layout w) := liftSlots d.slots
abbrev Layout.Touches (d : Layout w) (j : Fin (w + 1)) :=
  BoundedOccurrenceMachine.Touches d.Physical d.ending.castSucc d.flag.castSucc j

theorem physical_length (d : Layout w) : d.Physical.length = 4 := by
  simpa only [Layout.Physical, liftSlots, List.length_map] using d.length

theorem Layout.last_untouched (d : Layout w) : ¬d.Touches (Fin.last w) := by
  rintro (he | hf | ⟨p, hp, hj⟩)
  · exact cast_ne_last d.ending he.symm
  · exact cast_ne_last d.flag hf.symm
  · obtain ⟨q, _hq, rfl⟩ := List.mem_map.mp hp
    rcases hj with hl | hr
    · exact cast_ne_last q.1 hl.symm
    · exact cast_ne_last q.2 hr.symm

theorem touched_separate (d : Layout w) (j : Fin w) (hj : d.Touches j.castSucc) :
    j ≠ d.adjusted ∧ j ≠ d.acc ∧ j ≠ d.aux := by
  exact ⟨fun he => d.adjusted_outside (by simpa only [he] using hj),
    fun he => d.acc_outside (by simpa only [he] using hj),
    fun he => d.aux_outside (by simpa only [he] using hj)⟩

def Stable (d : Layout w) (R : (Fin w → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ d.idx → j ≠ d.sign → ¬d.Touches j.castSucc →
    j ≠ d.adjusted → j ≠ d.acc → j ≠ d.aux → next j = work j) → R work → R next

def Ready (L : ℕ) (d : Layout w) (work : Fin w → Tape) : Prop :=
  Reusable L (work d.idx) ∧ (work d.sign).head = 1 ∧
    (∀ p ∈ d.slots, Reusable L (work p.1) ∧ (work p.2).head = 1) ∧
    (work d.ending).head = 1 ∧ (work d.flag).head = 1

theorem ready_parts (L : ℕ) (d : Layout w) (work : Fin (w + 1) → Tape) (h : Ready L d (oldWork work)) :
    Reusable L (work d.idx.castSucc) ∧ (work d.sign.castSucc).head = 1 ∧
      BoundedOccurrenceMachine.Ready L d.Physical d.ending.castSucc d.flag.castSucc work := by
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact h.2.2.1 q hq

theorem ready_from_parts (L : ℕ) (d : Layout w) (work : Fin (w + 1) → Tape)
    (hidx : Reusable L (work d.idx.castSucc)) (hsign : (work d.sign.castSucc).head = 1)
    (h : BoundedOccurrenceMachine.Ready L d.Physical d.ending.castSucc d.flag.castSucc work) :
    Ready L d (oldWork work) := by
  refine ⟨hidx, hsign, ?_, h.2⟩
  intro p hp
  exact h.1 (p.1.castSucc, p.2.castSucc) (List.mem_map.mpr ⟨p, hp, rfl⟩)

theorem ready_stable (L : ℕ) (d : Layout w) : OffsetContribution.Stable d.adjusted d.acc d.aux (Ready L d) := by
  rintro work next he ⟨hi, hs, hp, hend, hf⟩
  have ht (j : Fin w) (hj : d.Touches j.castSucc) : next j = work j := by
    have hn := touched_separate d j hj
    exact he j hn.1 hn.2.1 hn.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [he d.idx d.arithmetic_sep.idx_adjusted d.arithmetic_sep.idx_acc d.arithmetic_sep.idx_aux]
    exact hi
  · rw [he d.sign d.arithmetic_sep.sign_adjusted d.arithmetic_sep.sign_acc d.arithmetic_sep.sign_aux]
    exact hs
  · intro p hmem
    have hm : (p.1.castSucc, p.2.castSucc) ∈ d.Physical := List.mem_map.mpr ⟨p, hmem, rfl⟩
    rw [ht p.1 (Or.inr (Or.inr ⟨_, hm, Or.inl rfl⟩)), ht p.2 (Or.inr (Or.inr ⟨_, hm, Or.inr rfl⟩))]
    exact hp p hmem
  · rw [ht d.ending (Or.inl rfl)]; exact hend
  · rw [ht d.flag (Or.inr (Or.inl rfl))]; exact hf

def liftWork (work : Fin w → Tape) : Fin (w + 1) → Tape := Fin.lastCases (Tape.init []) work

theorem lift_old_eq (work : Fin (w + 1) → Tape) (j : Fin (w + 1)) (hj : j ≠ Fin.last w) :
    liftWork (oldWork work) j = work j := by
  revert hj
  refine Fin.lastCases ?_ ?_ j
  · intro he
    exact (he rfl).elim
  · intro i _
    simp only [liftWork, Fin.lastCases_castSucc, oldWork]

theorem loaded_congr (slots : List (BoundedOccurrenceMachine.Port w)) (ending flag : Fin (w + 1))
    (raw : List Bool) (work next : Fin (w + 1) → Tape)
    (he : ∀ j, BoundedOccurrenceMachine.Touches slots ending flag j → next j = work j)
    (h : BoundedOccurrenceMachine.Loaded slots ending flag raw work) :
    BoundedOccurrenceMachine.Loaded slots ending flag raw next := by
  induction slots generalizing raw with
  | nil =>
    exact ⟨by rw [he ending (Or.inl rfl)]; exact h.1,
      by rw [he flag (Or.inr (Or.inl rfl))]; exact h.2⟩
  | cons p slots ih =>
    refine ⟨?_, ?_⟩
    · rw [he p.2 (Or.inr (Or.inr ⟨p, List.mem_cons_self, Or.inr rfl⟩))]
      exact h.1
    · cases hv : SourceBitRead.value raw
      · have hf : (work flag).read = Γ.ofBool (BooleanMachine.accepted raw) := by
          simpa only [hv, Bool.false_eq_true, ↓reduceIte] using h.2
        simpa only [hv, Bool.false_eq_true, ↓reduceIte] using
          (show (next flag).read = Γ.ofBool (BooleanMachine.accepted raw) from by
            rw [he flag (Or.inr (Or.inl rfl))]; exact hf)
      · have hp : BinaryIncrementRun.Register (NaturalCanonicalLoad.value (BooleanMachine.suffix raw)) (work p.1) ∧
            BoundedOccurrenceMachine.Loaded slots ending flag (NaturalRawControl.scan (BooleanMachine.suffix raw)).rest work := by
          simpa only [hv, ↓reduceIte] using h.2
        simp only [↓reduceIte]
        exact ⟨by rw [he p.1 (Or.inr (Or.inr ⟨p, List.mem_cons_self, Or.inl rfl⟩))]; exact hp.1,
          ih _ (fun j hj => he j (BoundedOccurrenceMachine.touches_tail hj)) hp.2⟩

def Loaded (d : Layout w) (raw : List Bool) (work : Fin w → Tape) : Prop :=
  BoundedOccurrenceMachine.Loaded d.Physical d.ending.castSucc d.flag.castSucc raw (liftWork work)

theorem loaded_iff (d : Layout w) (raw : List Bool) (work : Fin (w + 1) → Tape) :
    Loaded d raw (oldWork work) ↔ BoundedOccurrenceMachine.Loaded d.Physical d.ending.castSucc d.flag.castSucc raw work := by
  have he (j : Fin (w + 1)) (hj : d.Touches j) : liftWork (oldWork work) j = work j :=
    lift_old_eq work j (fun he => d.last_untouched (by simpa only [he] using hj))
  exact ⟨loaded_congr _ _ _ raw _ _ (fun j hj => (he j hj).symm),
    loaded_congr _ _ _ raw _ _ he⟩

theorem loaded_stable (d : Layout w) (raw : List Bool) :
    OffsetContribution.Stable d.adjusted d.acc d.aux (Loaded d raw) := by
  intro work next he hp
  apply loaded_congr _ _ _ raw _ _ _ hp
  intro j hj
  revert hj
  refine Fin.lastCases ?_ ?_ j
  · intro hj
    exact (d.last_untouched hj).elim
  · intro i hi
    have hn := touched_separate d i hi
    simpa only [liftWork, Fin.lastCases_castSucc] using he i hn.1 hn.2.1 hn.2.2

end JointThermoComplexity.Complexity.SparseOffsetLayout

#print axioms JointThermoComplexity.Complexity.SparseOffsetLayout.ready_stable
#print axioms JointThermoComplexity.Complexity.SparseOffsetLayout.loaded_iff
#print axioms JointThermoComplexity.Complexity.SparseOffsetLayout.loaded_stable
