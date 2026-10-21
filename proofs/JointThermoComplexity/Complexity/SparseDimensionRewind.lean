module
public import proofs.JointThermoComplexity.Complexity.SparseSourceWord
public import proofs.JointThermoComplexity.Complexity.InputRewind

set_option autoImplicit false
@[expose] public section

/-! Restart the source scan after computing its exact network headers. -/

namespace JointThermoComplexity.Complexity.SparseDimensionRewind
open _root_.Complexity _root_.Complexity.TM HeaderAt

def restart (s : CountedSparseControl.State) (input : List Bool) : CountedSparseControl.State :=
  ⟨⟨s.base.running, [], input, s.base.offset⟩, s.rows⟩

def machine (boxed : Bool) : TM 33 := seqTM (SparseDimensionEntry.machine boxed) rewindInputTM
def timeBound (L : ℕ) : ℕ := SparseDimensionEntry.timeBound L + L + 4

theorem hoareTime (boxed : Bool) (input : List Bool) :
    (machine boxed).HoareTime (SparseInputInitialization.Initial input)
      (SparseDimensionEmit.Pred input.length (HeaderControl.count input)
        (restart (SparseDimensionEntry.outcome boxed input) input)
        (SparseDimensionWords.header boxed (HeaderControl.count input) (SparseDimensionEntry.outcome boxed input).rows))
      (timeBound input.length) := by
  let s := SparseDimensionEntry.outcome boxed input
  let n := HeaderControl.count input
  let emitted := SparseDimensionWords.header boxed n s.rows
  let R : (Fin 33 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ SparseDimensionEmit.Work input.length n s work
  have hr := InputRewind.hoareTime s.base.before s.base.input emitted R
  have hr' : (rewindInputTM (n := 33)).HoareTime
      (SparseDimensionEmit.Pred input.length n s emitted)
      (SparseDimensionEmit.Pred input.length n (restart s input) emitted) (s.base.before.length + 3) := by
    apply hr.consequence
    · rintro inp work out ⟨⟨hc, hs, hf, hmh, hmr⟩, hfu⟩
      exact ⟨hc, hs, hf, hmh, hmr, hfu⟩
    · rintro inp work out ⟨hc, hs, hf, hmh, hmr, hfu⟩
      rw [show s.base.before ++ s.base.input = input from SparseSourceWord.outcome_word boxed input] at hc
      exact ⟨⟨hc, hs, hf, hmh, hmr⟩, hfu⟩
    · exact le_rfl
  have hh := SparseDimensionEntry.hoareTime boxed input
  have hall := seqTM_hoareTime _ _ hh (SparseDimensionEmit.phase input.length n s emitted) hr'
  exact hall.mono_bound (by
    have hb := SparseSourceWord.outcome_before_length boxed input
    unfold timeBound
    dsimp only [s]
    omega)

theorem cubic_timeBound (L : ℕ) :
    timeBound L = 3328 * L ^ 3 + 8692651 * L ^ 2 + 10898579 * L + 84 := by
  unfold timeBound
  rw [SparseDimensionEntry.cubic_timeBound]
  ring1

theorem canonical_hoareTime (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (hp : SparseInteger.DegreeLE 4 p.payload) :
    (machine boxed).HoareTime (SparseInputInitialization.Initial (SparsePolynomialCodec.code p))
      (SparseDimensionEmit.Pred (SparsePolynomialCodec.code p).length p.arity
        ⟨⟨false, [], SparsePolynomialCodec.code p, 1 + SparseOffsetCode.total boxed p.payload⟩,
          CountedSparseCode.rowTotal p.payload⟩
        (SparseDimensionWords.header boxed p.arity (CountedSparseCode.rowTotal p.payload)))
      (timeBound (SparsePolynomialCodec.code p).length) := by
  have ht := hoareTime boxed (SparsePolynomialCodec.code p)
  rw [SparseCountedEntry.count_code, SparseDimensionEntry.outcome_code boxed p hp] at ht
  exact ht

end JointThermoComplexity.Complexity.SparseDimensionRewind

#print axioms JointThermoComplexity.Complexity.SparseDimensionRewind.hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDimensionRewind.canonical_hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDimensionRewind.cubic_timeBound
