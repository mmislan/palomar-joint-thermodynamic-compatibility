module
public import proofs.JointThermoComplexity.Complexity.DenseDimensionProgram
public import proofs.JointThermoComplexity.Complexity.SparseDenseCount

set_option autoImplicit false
@[expose] public section

/-! Actual structural dimensions retain the source, computed offset and header. -/

namespace JointThermoComplexity.Complexity.SparseDenseDimensions
open _root_.Complexity _root_.Complexity.TM HeaderAt
open DInstabilityComplexity.MachineConstruction
open CountedSparseControl (State)

def index : Fin 6 → Fin 64 := ![16, 33, 34, 35, 36, 37]
def ports : CounterProgramFrame.Ports 6 64 where
  index := index
  injective := by decide

def restored (n : ℕ) (work : Fin 64 → Tape) : Fin 64 → Tape := Function.update work 16 (regTape n)
def Frame (L n : ℕ) (s : State) (work : Fin 64 → Tape) : Prop :=
  SparseDimensionEmit.Work L n s (SparseDenseWorkspace.oldWork (restored n work)) ∧
    ∀ j, 38 ≤ j.val → work j = regTape 0

def Pred (boxed : Bool) (L n : ℕ) (s : State) (emitted : List Bool) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => SparseDimensionEmit.Pred L n s emitted inp (SparseDenseWorkspace.oldWork work) out ∧
    (∀ j, Parked (work j)) ∧ (∀ k, IsReg (DenseDimensionProgram.result boxed n s.rows k) (work (index k))) ∧
      ∀ j, 38 ≤ j.val → work j = regTape 0

def machine (boxed : Bool) : TM 64 := CounterProgramFrame.machine ports (DenseDimensionProgram.program boxed)

theorem species_matches_header (boxed : Bool) (n t : ℕ) :
    DenseDimensionProgram.result boxed n t 4 = SparseDimensionWords.species boxed n t := by
  cases boxed
  · change 2 * n + 1 + 2 * t + 2 = 2 * n + 2 * t + 3
    omega
  · rfl

theorem reactions_match_header (boxed : Bool) (n t : ℕ) :
    DenseDimensionProgram.result boxed n t 5 = SparseDimensionWords.reactions t := rfl

theorem index_high (k : Fin 6) (hk : k ≠ 0) : 33 ≤ (index k).val := by
  have h : ∀ k : Fin 6, k ≠ 0 → 33 ≤ (index k).val := by decide
  exact h k hk

theorem index_lt (k : Fin 6) : (index k).val < 38 := by
  have h : ∀ k : Fin 6, (index k).val < 38 := by decide
  exact h k

theorem restored_eq (n : ℕ) (work : Fin 64 → Tape) (h : IsReg n (work 16)) : restored n work = work := by
  unfold restored
  rw [← h.eq_regT, Function.update_eq_self]

theorem frame_stable (L n : ℕ) (s : State) : CounterProgramFrame.Stable ports (Frame L n s) := by
  rintro work next he ⟨hw, hf⟩
  have hold : SparseDenseWorkspace.oldWork (restored n next) = SparseDenseWorkspace.oldWork (restored n work) := by
    funext j
    change Function.update next 16 (regTape n) (Fin.castAdd 31 j) = Function.update work 16 (regTape n) (Fin.castAdd 31 j)
    by_cases hj : Fin.castAdd 31 j = (16 : Fin 64)
    · simp only [hj, Function.update_self]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
      apply he (Fin.castAdd 31 j)
      intro k
      by_cases hk : k = 0
      · subst k; exact hj
      · intro h
        have hv := congrArg (fun z : Fin 64 => z.val) h
        have hh := index_high k hk
        change j.val = (index k).val at hv
        omega
  refine ⟨by rw [hold]; exact hw, ?_⟩
  intro j hj
  rw [he j (fun k h => by
    have hv := congrArg (fun z : Fin 64 => z.val) h
    have hk := index_lt k
    change j.val = (index k).val at hv
    omega)]
  exact hf j hj

theorem pre (L n : ℕ) (s : State) (emitted : List Bool) (inp : Tape) (work : Fin 64 → Tape) (out : Tape)
    (hp : SparseDenseCount.Pred L n s emitted inp work out) :
    CounterProgramFrame.Logical ports (DenseDimensionProgram.initial n s.rows) s.base.before s.base.input emitted
      (Frame L n s) inp work out := by
  obtain ⟨⟨hc, _, hfields, hmh, hmr⟩, hf⟩ := hp.1
  have har : IsReg n (work 16) := hfields.1.2.2.2.2.2
  have hs : ∀ j, Parked (work j) := by
    intro j
    by_cases hj : j.val < 33
    · let k : Fin 33 := ⟨j.val, hj⟩
      have he : Fin.castAdd 31 k = j := Fin.ext rfl
      simpa only [SparseDenseWorkspace.oldWork, InitialTapeLift.oldWork, he] using hp.1.1.2.1 k
    · by_cases h33 : j = 33
      · subst j; exact hp.2.1.parked
      · have hge : 34 ≤ j.val := by
          have hne : j.val ≠ 33 := by intro h; apply h33; exact Fin.ext h
          omega
        rw [hp.2.2 j hge]
        exact parked_regTape 0
  refine ⟨SparseDenseCount.cursor L n s emitted inp work out hp, hs, ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · exact har
    · exact hp.2.1
    all_goals
      change IsReg 0 (work _)
      rw [hp.2.2 _ (by decide)]
      exact reg_regT 0
  · rw [restored_eq n work har]
    exact ⟨hfields, hmh, hmr, hf⟩
  · intro j hj
    exact hp.2.2 j (by omega)

theorem post (boxed : Bool) (L n : ℕ) (s : State) (emitted : List Bool)
    (inp : Tape) (work : Fin 64 → Tape) (out : Tape)
    (hp : CounterProgramFrame.Logical ports (DenseDimensionProgram.result boxed n s.rows) s.base.before s.base.input emitted
      (Frame L n s) inp work out) : Pred boxed L n s emitted inp work out := by
  obtain ⟨hc, hs, hv, hw, hf⟩ := hp
  have har : IsReg n (work 16) := hv 0
  rw [restored_eq n work har] at hw
  obtain ⟨hfields, hmh, hmr, hfu⟩ := hw
  have hcursor : Cursor s.base.before s.base.input emitted inp (SparseDenseWorkspace.oldWork work) out :=
    ⟨hc.cells, hc.head, fun j => hc.works (Fin.castAdd 31 j), hc.tapePrefix, hc.zero⟩
  exact ⟨⟨⟨hcursor, fun j => hs (Fin.castAdd 31 j), hfields, hmh, hmr⟩, hfu⟩, hs, hv, hf⟩

theorem hoareTime (boxed : Bool) (L n : ℕ) (s : State) (hn : n ≤ L) (ht : s.rows ≤ 16 * L) (emitted : List Bool) :
    (machine boxed).HoareTime (SparseDenseCount.Pred L n s emitted) (Pred boxed L n s emitted)
      (DenseDimensionProgram.timeBound boxed L) := by
  have hh := CounterProgramFrame.bounded_hoareTime ports (DenseDimensionProgram.program boxed)
    (DenseDimensionProgram.initial n s.rows) (16 * L) (DenseDimensionProgram.initial_bound L n s.rows hn ht)
    s.base.before s.base.input emitted (Frame L n s) (frame_stable L n s)
  rw [DenseDimensionProgram.eval] at hh
  exact hh.consequence (pre L n s emitted) (post boxed L n s emitted) le_rfl

theorem phase (boxed : Bool) (L n : ℕ) (s : State) (emitted : List Bool) :
    ∀ inp work out, Pred boxed L n s emitted inp work out →
      Pred boxed L n s emitted (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out hp
  have hc := hp.1.1.1
  have hcursor : Cursor s.base.before s.base.input emitted inp work out :=
    ⟨hc.cells, hc.head, fun j => ⟨(hp.2.1 j).read_ne_start, (hp.2.1 j).1⟩, hc.tapePrefix, hc.zero⟩
  obtain ⟨hi, hw, ho⟩ := hcursor.phase
  rw [hi, hw, ho]
  exact hp

def entry (boxed : Bool) : TM 64 := seqTM (SparseDenseCount.entry boxed) (machine boxed)
def entryBound (boxed : Bool) (L : ℕ) : ℕ := SparseDenseCount.entryBound L + 1 + DenseDimensionProgram.timeBound boxed L

theorem entry_hoareTime (boxed : Bool) (input : List Bool) :
    (entry boxed).HoareTime (InitialTapeLift.Initial 64 input)
      (Pred boxed input.length (HeaderControl.count input)
        (SparseDimensionRewind.restart (SparseDimensionEntry.outcome boxed input) input)
        (SparseDimensionWords.header boxed (HeaderControl.count input) (SparseDimensionEntry.outcome boxed input).rows))
      (entryBound boxed input.length) := by
  have hh := hoareTime boxed input.length (HeaderControl.count input)
    (SparseDimensionRewind.restart (SparseDimensionEntry.outcome boxed input) input)
    (HeaderControl.count_le_length input) (SparseDimensionEntry.rows_bound boxed input)
    (SparseDimensionWords.header boxed (HeaderControl.count input) (SparseDimensionEntry.outcome boxed input).rows)
  exact seqTM_hoareTime _ _ (SparseDenseCount.entry_hoareTime boxed input) (SparseDenseCount.phase _ _ _ _) hh

noncomputable def entryPolynomial (boxed : Bool) : Polynomial ℕ :=
  3328 * Polynomial.X ^ 3 + 8695211 * Polynomial.X ^ 2 + 10898966 * Polynomial.X + 102 + DenseDimensionProgram.timePolynomial boxed

theorem entryPolynomial_eval (boxed : Bool) (L : ℕ) : (entryPolynomial boxed).eval L = entryBound boxed L := by
  simp [entryPolynomial, entryBound, DenseDimensionProgram.timePolynomial_eval, SparseDenseCount.cubic_entryBound]

theorem canonical_entry_hoareTime (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (hp : SparseInteger.DegreeLE 4 p.payload) :
    (entry boxed).HoareTime (InitialTapeLift.Initial 64 (SparsePolynomialCodec.code p))
      (Pred boxed (SparsePolynomialCodec.code p).length p.arity
        ⟨⟨false, [], SparsePolynomialCodec.code p, 1 + SparseOffsetCode.total boxed p.payload⟩,
          CountedSparseCode.rowTotal p.payload⟩
        (SparseDimensionWords.header boxed p.arity (CountedSparseCode.rowTotal p.payload)))
      (entryBound boxed (SparsePolynomialCodec.code p).length) := by
  have ht := entry_hoareTime boxed (SparsePolynomialCodec.code p)
  rw [SparseCountedEntry.count_code, SparseDimensionEntry.outcome_code boxed p hp] at ht
  exact ht

end JointThermoComplexity.Complexity.SparseDenseDimensions

#print axioms JointThermoComplexity.Complexity.SparseDenseDimensions.hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDenseDimensions.entry_hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDenseDimensions.canonical_entry_hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDenseDimensions.entryPolynomial_eval
#print axioms JointThermoComplexity.Complexity.SparseDenseDimensions.species_matches_header
