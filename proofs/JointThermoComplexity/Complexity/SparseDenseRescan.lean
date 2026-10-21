module
public import proofs.JointThermoComplexity.Complexity.HeaderSkipRaw
public import proofs.JointThermoComplexity.Complexity.SparseDenseDimensions
public import proofs.JointThermoComplexity.Complexity.SourceTermToken

set_option autoImplicit false
@[expose] public section

/-! Restart marked source-term processing without changing computed dimensions. -/

namespace JointThermoComplexity.Complexity.SparseDenseRescan
open _root_.Complexity _root_.Complexity.TM HeaderAt
open CountedSparseControl (State)
open SparseOffsetPorts

def skipped (s : State) : State :=
  ⟨⟨s.base.running, s.base.before ++ HeaderControl.copied s.base.input,
    HeaderControl.suffix s.base.input, s.base.offset⟩, s.rows⟩
def activated (s : State) : State := ⟨⟨true, s.base.before, s.base.input, s.base.offset⟩, s.rows⟩
def outcome (s : State) : State := activated (skipped s)

def Frame (boxed : Bool) (L n : ℕ) (s : State) (work : Fin 64 → Tape) : Prop :=
  CountedMarkedStep.Fields L s.base.offset s.rows (SparseCountedEntry.frame n) (SparseDenseWorkspace.oldWork work) ∧
    IsReg L (work 18) ∧ (∀ k, IsReg (DenseDimensionProgram.result boxed n s.rows k) (work (SparseDenseDimensions.index k))) ∧
      ∀ j, 38 ≤ j.val → work j = regTape 0

theorem fields_stable (L n : ℕ) (s : State) (work next : Fin 64 → Tape)
    (he : ∀ j, j ≠ 15 → next j = work j)
    (hp : CountedMarkedStep.Fields L s.base.offset s.rows (SparseCountedEntry.frame n) (SparseDenseWorkspace.oldWork work)) :
    CountedMarkedStep.Fields L s.base.offset s.rows (SparseCountedEntry.frame n) (SparseDenseWorkspace.oldWork next) := by
  have hold (j : Fin 33) (hj : j ≠ 15) : SparseDenseWorkspace.oldWork next j = SparseDenseWorkspace.oldWork work j := by
    apply he (Fin.castAdd 31 j)
    intro h
    apply hj
    exact Fin.ext (congrArg (fun k : Fin 64 => k.val) h)
  have low (j : Fin 32) (hj : j.val ≤ 11) :
      SparseDenseWorkspace.oldWork next j.castSucc = SparseDenseWorkspace.oldWork work j.castSucc := by
    apply hold j.castSucc
    intro h
    have hv := congrArg (fun k : Fin 33 => k.val) h
    change j.val = 15 at hv
    omega
  obtain ⟨⟨⟨hi, hs, hports, hend, hf⟩, hadj, ha, hu, hlast, har⟩, hn⟩ := hp
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [BinaryScaleBuffer.oldWork]
    rw [low layout.idx (by decide)]; exact hi
  · simp only [BinaryScaleBuffer.oldWork]
    rw [low layout.sign (by decide)]; exact hs
  · intro p hp
    have hm : p ∈ [(2, 6), (3, 7), (4, 8), (5, 9)] := hp
    simp at hm
    have hd : p.1.val ≤ 11 := by rcases hm with rfl | rfl | rfl | rfl <;> decide
    have hflag : p.2.val ≤ 11 := by rcases hm with rfl | rfl | rfl | rfl <;> decide
    simp only [BinaryScaleBuffer.oldWork]
    rw [low p.1 hd, low p.2 hflag]
    exact hports p hp
  · simp only [BinaryScaleBuffer.oldWork]
    rw [low layout.ending (by decide)]; exact hend
  · simp only [BinaryScaleBuffer.oldWork]
    rw [low layout.flag (by decide)]; exact hf
  · rw [hold layout.adjusted.castSucc (by decide)]; exact hadj
  · rw [hold layout.acc.castSucc (by decide)]; exact ha
  · rw [hold layout.aux.castSucc (by decide)]; exact hu
  · rw [hold (Fin.last 32) (by decide)]; exact hlast
  · change IsReg n (SparseDenseWorkspace.oldWork next arity.castSucc)
    rw [hold arity.castSucc (by decide)]; exact har
  · rw [hold rows.castSucc (by decide)]; exact hn

theorem frame_stable (boxed : Bool) (L n : ℕ) (s : State) :
    ∀ work next, (∀ j, j ≠ 15 → next j = work j) → Frame boxed L n s work → Frame boxed L n s next := by
  rintro work next he ⟨hp, hf, hd, hz⟩
  refine ⟨fields_stable L n s work next he hp, ?_, ?_, ?_⟩
  · rw [he 18 (by decide)]; exact hf
  · intro k
    have h : ∀ k : Fin 6, SparseDenseDimensions.index k ≠ 15 := by decide
    rw [he _ (h k)]; exact hd k
  · intro j hj
    have hn : j ≠ 15 := by
      intro h
      have hv := congrArg (fun k : Fin 64 => k.val) h
      change j.val = 15 at hv
      omega
    rw [he j hn]; exact hz j hj

theorem activate_hoareTime (boxed : Bool) (L n : ℕ) (s : State) (emitted : List Bool) :
    (SourceTermToken.setStatus (15 : Fin 64) true).HoareTime
      (SparseDenseDimensions.Pred boxed L n s emitted)
      (SparseDenseDimensions.Pred boxed L n (activated s) emitted) 1 := by
  have hh := SourceTermToken.setStatus_hoareTime (15 : Fin 64) true s.base.before s.base.input emitted
    (Frame boxed L n s) (frame_stable boxed L n s)
  apply hh.consequence
  · rintro inp work out ⟨⟨⟨hc, _, hp, hmh, _⟩, hf⟩, hs, hd, hz⟩
    have hcur : Cursor s.base.before s.base.input emitted inp work out :=
      ⟨hc.cells, hc.head, fun j => ⟨(hs j).read_ne_start, (hs j).1⟩, hc.tapePrefix, hc.zero⟩
    exact ⟨hcur, hs, hmh, hp, hf, hd, hz⟩
  · rintro inp work out ⟨hc, hs, hh, hv, hp, hf, hd, hz⟩
    have hcur : Cursor s.base.before s.base.input emitted inp (SparseDenseWorkspace.oldWork work) out :=
      ⟨hc.cells, hc.head, fun j => hc.works (Fin.castAdd 31 j), hc.tapePrefix, hc.zero⟩
    exact ⟨⟨⟨hcur, fun j => hs (Fin.castAdd 31 j), hp, hh, hv⟩, hf⟩, hs, hd, hz⟩
  · exact le_rfl

theorem skip_hoareTime (boxed : Bool) (L n : ℕ) (s : State) (emitted : List Bool) :
    (HeaderSkip.machine (w := 64)).HoareTime
      (SparseDenseDimensions.Pred boxed L n s emitted)
      (SparseDenseDimensions.Pred boxed L n (skipped s) emitted) (HeaderControl.count s.base.input + 1) := by
  let R : (Fin 64 → Tape) → Prop := fun work => SparseDimensionEmit.Work L n s (SparseDenseWorkspace.oldWork work) ∧
    (∀ k, IsReg (DenseDimensionProgram.result boxed n s.rows k) (work (SparseDenseDimensions.index k))) ∧
      ∀ j, 38 ≤ j.val → work j = regTape 0
  have hh := HeaderSkipRaw.hoareTime s.base.before s.base.input emitted R
  apply hh.consequence
  · rintro inp work out ⟨⟨⟨hc, _, hp, hmh, hmr⟩, hf⟩, hs, hd, hz⟩
    have hcur : Cursor s.base.before s.base.input emitted inp work out :=
      ⟨hc.cells, hc.head, fun j => ⟨(hs j).read_ne_start, (hs j).1⟩, hc.tapePrefix, hc.zero⟩
    exact ⟨hcur, hs, ⟨hp, hmh, hmr, hf⟩, hd, hz⟩
  · rintro inp work out ⟨hc, hs, ⟨hp, hmh, hmr, hf⟩, hd, hz⟩
    have hcur : Cursor (s.base.before ++ HeaderControl.copied s.base.input) (HeaderControl.suffix s.base.input) emitted
        inp (SparseDenseWorkspace.oldWork work) out :=
      ⟨hc.cells, hc.head, fun j => hc.works (Fin.castAdd 31 j), hc.tapePrefix, hc.zero⟩
    exact ⟨⟨⟨hcur, fun j => hs (Fin.castAdd 31 j), hp, hmh, hmr⟩, hf⟩, hs, hd, hz⟩
  · exact le_rfl

def machine : TM 64 := seqTM HeaderSkip.machine (SourceTermToken.setStatus 15 true)

theorem hoareTime (boxed : Bool) (L n : ℕ) (s : State) (emitted : List Bool) :
    machine.HoareTime (SparseDenseDimensions.Pred boxed L n s emitted)
      (SparseDenseDimensions.Pred boxed L n (outcome s) emitted) (HeaderControl.count s.base.input + 3) := by
  exact seqTM_hoareTime _ _ (skip_hoareTime boxed L n s emitted)
    (SparseDenseDimensions.phase boxed L n (skipped s) emitted) (activate_hoareTime boxed L n (skipped s) emitted)

def entry (boxed : Bool) : TM 64 := seqTM (SparseDenseDimensions.entry boxed) machine
def entryBound (boxed : Bool) (L : ℕ) : ℕ := SparseDenseDimensions.entryBound boxed L + L + 4

theorem entry_hoareTime (boxed : Bool) (input : List Bool) :
    (entry boxed).HoareTime (InitialTapeLift.Initial 64 input)
      (SparseDenseDimensions.Pred boxed input.length (HeaderControl.count input)
        (outcome (SparseDimensionRewind.restart (SparseDimensionEntry.outcome boxed input) input))
        (SparseDimensionWords.header boxed (HeaderControl.count input) (SparseDimensionEntry.outcome boxed input).rows))
      (entryBound boxed input.length) := by
  have hh := hoareTime boxed input.length (HeaderControl.count input)
    (SparseDimensionRewind.restart (SparseDimensionEntry.outcome boxed input) input)
    (SparseDimensionWords.header boxed (HeaderControl.count input) (SparseDimensionEntry.outcome boxed input).rows)
  have hall := seqTM_hoareTime _ _ (SparseDenseDimensions.entry_hoareTime boxed input)
    (SparseDenseDimensions.phase _ _ _ _ _) hh
  exact hall.mono_bound (by
    have hn := HeaderControl.count_le_length input
    unfold entryBound
    change SparseDenseDimensions.entryBound boxed input.length + 1 + (HeaderControl.count input + 3) ≤ _
    omega)

noncomputable def entryPolynomial (boxed : Bool) : Polynomial ℕ := SparseDenseDimensions.entryPolynomial boxed + Polynomial.X + 4

theorem entryPolynomial_eval (boxed : Bool) (L : ℕ) : (entryPolynomial boxed).eval L = entryBound boxed L := by
  simp [entryPolynomial, entryBound, SparseDenseDimensions.entryPolynomial_eval]

theorem outcome_code (p : SparsePolynomialCodec.PolynomialData) (A N : ℕ) :
    outcome ⟨⟨false, [], SparsePolynomialCodec.code p, A⟩, N⟩ =
      ⟨⟨true, RealSyntax.binderCode p.arity, SparseOffsetCode.code p.payload, A⟩, N⟩ := by
  unfold outcome activated skipped
  simp only [List.nil_append]
  rw [SparseCountedEntry.code_eq, HeaderControl.copied_code, HeaderControl.suffix_code]

theorem canonical_entry_hoareTime (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (hp : SparseInteger.DegreeLE 4 p.payload) :
    (entry boxed).HoareTime (InitialTapeLift.Initial 64 (SparsePolynomialCodec.code p))
      (SparseDenseDimensions.Pred boxed (SparsePolynomialCodec.code p).length p.arity
        ⟨⟨true, RealSyntax.binderCode p.arity, SparseOffsetCode.code p.payload, 1 + SparseOffsetCode.total boxed p.payload⟩,
          CountedSparseCode.rowTotal p.payload⟩
        (SparseDimensionWords.header boxed p.arity (CountedSparseCode.rowTotal p.payload)))
      (entryBound boxed (SparsePolynomialCodec.code p).length) := by
  have ht := entry_hoareTime boxed (SparsePolynomialCodec.code p)
  rw [SparseCountedEntry.count_code, SparseDimensionEntry.outcome_code boxed p hp] at ht
  dsimp only [SparseDimensionRewind.restart] at ht
  rw [outcome_code] at ht
  exact ht

end JointThermoComplexity.Complexity.SparseDenseRescan

#print axioms JointThermoComplexity.Complexity.SparseDenseRescan.hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDenseRescan.entry_hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDenseRescan.canonical_entry_hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDenseRescan.entryPolynomial_eval
