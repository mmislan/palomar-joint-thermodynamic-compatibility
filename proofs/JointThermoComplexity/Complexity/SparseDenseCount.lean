module
public import proofs.JointThermoComplexity.Complexity.SparseDenseWorkspace
public import proofs.JointThermoComplexity.Complexity.BoundedUnaryStore

set_option autoImplicit false
@[expose] public section

/-! Materialize the normalized row count on tape33, retaining fresh34..63. -/

namespace JointThermoComplexity.Complexity.SparseDenseCount
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open CountedSparseControl (State)

def ports : BoundedUnaryUnit.Ports 63 where
  idx := 14
  value := 17
  flag := 12
  fuel := 18
  idx_value := by decide
  flag_idx := by decide
  flag_value := by decide
  fuel_idx := by decide
  fuel_value := by decide
  fuel_flag := by decide

def first33 (work : Fin 63 → Tape) : Fin 33 → Tape := fun j => work (Fin.castAdd 30 j)
def permutation : Fin 64 ≃ Fin 64 := Equiv.swap 33 63
def machine : TM 64 := WorkPermutation.machine permutation (BoundedUnaryStore.machine ports)

def Frame (L n : ℕ) (s : State) (work : Fin 63 → Tape) : Prop :=
  SparseDimensionFrame.Protected L n s (first33 work) ∧ ∀ j, 33 ≤ j.val → work j = regTape 0

def Pred (L n : ℕ) (s : State) (emitted : List Bool) : _root_.Complexity.TM.TapePred 64 := fun inp work out =>
  SparseDimensionEmit.Pred L n s emitted inp (SparseDenseWorkspace.oldWork work) out ∧
    IsReg s.rows (work 33) ∧ ∀ j, 34 ≤ j.val → work j = regTape 0

theorem permutation_fixed (j : Fin 64) (h33 : j ≠ 33) (h63 : j ≠ 63) : permutation j = j :=
  Equiv.swap_apply_of_ne_of_ne h33 h63

theorem permutation_low (j : Fin 64) (hj : j.val < 33) : permutation j = j := by
  apply permutation_fixed
  · intro h; have hv := congrArg Fin.val h; change j.val = 33 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change j.val = 63 at hv; omega

theorem permutation_high (j : Fin 64) (hj : 33 ≤ j.val) : 33 ≤ (permutation j).val := by
  by_cases h33 : j = 33
  · subst j; decide
  · by_cases h63 : j = 63
    · subst j; decide
    · rw [permutation_fixed j h33 h63]; exact hj

theorem first_virtual (work : Fin 64 → Tape) :
    first33 (BoundedUnaryStore.oldWork (fun j => work (permutation j))) = SparseDenseWorkspace.oldWork work := by
  funext j
  change work (permutation (Fin.castAdd 30 j).castSucc) = work (Fin.castAdd 31 j)
  rw [permutation_low _ j.isLt]
  rfl

theorem frame_stable (L n : ℕ) (s : State) : BoundedUnaryLoop.Stable ports (Frame L n s) := by
  rintro work next he ⟨hp, hf⟩
  have hprotected := SparseDimensionFrame.protected_stable L n s (first33 work) (first33 next)
  refine ⟨hprotected ?_ hp, ?_⟩
  · intro j hi hv hh hfu
    apply he (Fin.castAdd 30 j)
    · intro h; apply hi; exact Fin.ext (congrArg (fun k : Fin 63 => k.val) h)
    · intro h; apply hv; exact Fin.ext (congrArg (fun k : Fin 63 => k.val) h)
    · intro h; apply hh; exact Fin.ext (congrArg (fun k : Fin 63 => k.val) h)
    · intro h; apply hfu; exact Fin.ext (congrArg (fun k : Fin 63 => k.val) h)
  · intro j hj
    have hn (k : Fin 63) (hk : k.val < 33) : j ≠ k := by
      intro h; subst j; omega
    rw [he j (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))]
    exact hf j hj

theorem pre (L n : ℕ) (s : State) (emitted : List Bool) (inp : Tape) (work : Fin 64 → Tape) (out : Tape)
    (hp : SparseDenseWorkspace.Pred L n s emitted inp work out) :
    BoundedUnaryStore.Pred ports s.rows L 0 s.base.before s.base.input emitted (Frame L n s)
      inp (fun j => work (permutation j)) out := by
  obtain ⟨hc, _, hi, hn, hh, hf, hr⟩ := (SparseDimensionFrame.state_iff L n s emitted inp out _).mp hp.1
  have hs := SparseDenseWorkspace.allParked L n s emitted inp work out hp
  refine ⟨⟨hc.cells, hc.head, fun j => ⟨(hs (permutation j)).read_ne_start, (hs (permutation j)).1⟩,
    hc.tapePrefix, hc.zero⟩, fun j => hs (permutation j), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change IsReg 0 (work (permutation (Fin.last 63)))
    rw [show permutation (Fin.last 63) = 33 from by decide, hp.2 33 (by decide)]
    exact reg_regT 0
  · change Register 0 (work (permutation (14 : Fin 64)))
    rw [permutation_low _ (by decide)]
    exact hi
  · change Register s.rows (work (permutation (17 : Fin 64)))
    rw [permutation_low _ (by decide)]
    exact hn
  · change (work (permutation (12 : Fin 64))).head = 1
    rw [permutation_low _ (by decide)]
    exact hh
  · change IsReg L (work (permutation (18 : Fin 64)))
    rw [permutation_low _ (by decide)]
    exact hf
  · rw [first_virtual]
    exact hr
  · intro j hj
    exact hp.2 (permutation j.castSucc) (permutation_high _ hj)

theorem post (L n : ℕ) (s : State) (emitted : List Bool) (inp : Tape) (work : Fin 64 → Tape) (out : Tape)
    (hp : BoundedUnaryStore.Pred ports s.rows L s.rows s.base.before s.base.input emitted (Frame L n s)
      inp (fun j => work (permutation j)) out) : Pred L n s emitted inp work out := by
  obtain ⟨hc, hs, hv, hi, hn, hh, hf, hr, hz⟩ := hp
  have hsafe : ∀ j, Parked (work j) := fun j => by
    simpa only [permutation.apply_symm_apply] using hs (permutation.symm j)
  have hcursor : Cursor s.base.before s.base.input emitted inp (SparseDenseWorkspace.oldWork work) out :=
    ⟨hc.cells, hc.head, fun j => ⟨(hsafe (Fin.castAdd 31 j)).read_ne_start, (hsafe (Fin.castAdd 31 j)).1⟩,
      hc.tapePrefix, hc.zero⟩
  have hpold : SparseDimensionEmit.Pred L n s emitted inp (SparseDenseWorkspace.oldWork work) out := by
    apply (SparseDimensionFrame.state_iff L n s emitted inp out _).mpr
    refine ⟨hcursor, fun j => hsafe (Fin.castAdd 31 j), ?_, ?_, ?_, ?_, ?_⟩
    · change Register 0 (work (permutation (14 : Fin 64))) at hi
      rw [permutation_low _ (by decide)] at hi
      exact hi
    · change Register s.rows (work (permutation (17 : Fin 64))) at hn
      rw [permutation_low _ (by decide)] at hn
      exact hn
    · change (work (permutation (12 : Fin 64))).head = 1 at hh
      rw [permutation_low _ (by decide)] at hh
      exact hh
    · change IsReg L (work (permutation (18 : Fin 64))) at hf
      rw [permutation_low _ (by decide)] at hf
      exact hf
    · rw [first_virtual] at hr
      exact hr
  refine ⟨hpold, ?_, ?_⟩
  · change IsReg s.rows (work (permutation (Fin.last 63))) at hv
    rw [show permutation (Fin.last 63) = 33 from by decide] at hv
    exact hv
  · intro j hj
    by_cases hj63 : j = 63
    · subst j
      have hh := hz (33 : Fin 63) (by decide)
      change work (permutation (33 : Fin 64)) = regTape 0 at hh
      rw [show permutation (33 : Fin 64) = 63 from by decide] at hh
      exact hh
    · have hj33 : j ≠ 33 := by intro h; subst j; change 34 ≤ 33 at hj; omega
      have hlt : j.val < 63 := by
        by_contra h
        apply hj63
        apply Fin.ext
        change j.val = 63
        omega
      let k : Fin 63 := ⟨j.val, hlt⟩
      have he : k.castSucc = j := Fin.ext rfl
      have hh := hz k (by change 33 ≤ j.val; omega)
      change work (permutation k.castSucc) = regTape 0 at hh
      rw [he, permutation_fixed j hj33 hj63] at hh
      exact hh

def bound (L : ℕ) : ℕ := BoundedUnaryStore.bound L (16 * L)

theorem hoareTime (L n : ℕ) (s : State) (ht : s.rows ≤ 16 * L) (emitted : List Bool) :
    machine.HoareTime (SparseDenseWorkspace.Pred L n s emitted) (Pred L n s emitted) (bound L) := by
  have hh := BoundedUnaryStore.hoareTime ports s.rows L (16 * L)
    ((BoundedUnaryControl.bits_le s.rows).trans ht) s.base.before s.base.input emitted (Frame L n s) (frame_stable L n s)
  rw [Nat.min_eq_right ht] at hh
  have hp := WorkPermutation.hoareTime permutation (BoundedUnaryStore.machine ports) _ _ _ hh
  exact hp.consequence (pre L n s emitted) (post L n s emitted) le_rfl

theorem polynomial_bound (L : ℕ) : bound L = 2560 * L ^ 2 + 387 * L + 16 := by
  unfold bound
  rw [BoundedUnaryStore.polynomial_bound]
  ring1

theorem cursor (L n : ℕ) (s : State) (emitted : List Bool)
    (inp : Tape) (work : Fin 64 → Tape) (out : Tape) (hp : Pred L n s emitted inp work out) :
    Cursor s.base.before s.base.input emitted inp work out := by
  have hc := hp.1.1.1
  refine ⟨hc.cells, hc.head, ?_, hc.tapePrefix, hc.zero⟩
  intro j
  by_cases hj : j.val < 33
  · let k : Fin 33 := ⟨j.val, hj⟩
    have he : Fin.castAdd 31 k = j := Fin.ext rfl
    simpa only [SparseDenseWorkspace.oldWork, InitialTapeLift.oldWork, he] using hc.works k
  · by_cases h33 : j = 33
    · subst j; exact ⟨hp.2.1.parked.read_ne_start, hp.2.1.parked.1⟩
    · have hge : 34 ≤ j.val := by
        have hne : j.val ≠ 33 := by intro h; apply h33; exact Fin.ext h
        omega
      rw [hp.2.2 j hge]
      exact ⟨(parked_regTape 0).read_ne_start, (parked_regTape 0).1⟩

theorem phase (L n : ℕ) (s : State) (emitted : List Bool) :
    ∀ inp work out, Pred L n s emitted inp work out →
      Pred L n s emitted (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out hp
  obtain ⟨hi, hw, ho⟩ := (cursor L n s emitted inp work out hp).phase
  rw [hi, hw, ho]
  exact hp

def entry (boxed : Bool) : TM 64 := seqTM (SparseDenseWorkspace.machine boxed) machine
def entryBound (L : ℕ) : ℕ := SparseDimensionRewind.timeBound L + 1 + bound L

theorem entry_hoareTime (boxed : Bool) (input : List Bool) :
    (entry boxed).HoareTime (InitialTapeLift.Initial 64 input)
      (Pred input.length (HeaderControl.count input)
        (SparseDimensionRewind.restart (SparseDimensionEntry.outcome boxed input) input)
        (SparseDimensionWords.header boxed (HeaderControl.count input) (SparseDimensionEntry.outcome boxed input).rows))
      (entryBound input.length) := by
  have hh := hoareTime input.length (HeaderControl.count input)
    (SparseDimensionRewind.restart (SparseDimensionEntry.outcome boxed input) input)
    (SparseDimensionEntry.rows_bound boxed input)
    (SparseDimensionWords.header boxed (HeaderControl.count input) (SparseDimensionEntry.outcome boxed input).rows)
  exact seqTM_hoareTime _ _ (SparseDenseWorkspace.hoareTime boxed input)
    (SparseDenseWorkspace.phase _ _ _ _) hh

theorem cubic_entryBound (L : ℕ) :
    entryBound L = 3328 * L ^ 3 + 8695211 * L ^ 2 + 10898966 * L + 101 := by
  unfold entryBound
  rw [SparseDimensionRewind.cubic_timeBound, polynomial_bound]
  ring1

theorem canonical_entry_hoareTime (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (hp : SparseInteger.DegreeLE 4 p.payload) :
    (entry boxed).HoareTime (InitialTapeLift.Initial 64 (SparsePolynomialCodec.code p))
      (Pred (SparsePolynomialCodec.code p).length p.arity
        ⟨⟨false, [], SparsePolynomialCodec.code p, 1 + SparseOffsetCode.total boxed p.payload⟩,
          CountedSparseCode.rowTotal p.payload⟩
        (SparseDimensionWords.header boxed p.arity (CountedSparseCode.rowTotal p.payload)))
      (entryBound (SparsePolynomialCodec.code p).length) := by
  have ht := entry_hoareTime boxed (SparsePolynomialCodec.code p)
  rw [SparseCountedEntry.count_code, SparseDimensionEntry.outcome_code boxed p hp] at ht
  exact ht

end JointThermoComplexity.Complexity.SparseDenseCount

#print axioms JointThermoComplexity.Complexity.SparseDenseCount.hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDenseCount.polynomial_bound
#print axioms JointThermoComplexity.Complexity.SparseDenseCount.entry_hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDenseCount.canonical_entry_hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDenseCount.cubic_entryBound
