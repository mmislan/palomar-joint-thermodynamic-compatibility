module
public import proofs.JointThermoComplexity.Complexity.SparseDimensionRewind
public import proofs.JointThermoComplexity.Complexity.InitialTapeLift

set_option autoImplicit false
@[expose] public section

/-! A fixed 64-tape entry retains computed headers and verified empty workspace. -/

namespace JointThermoComplexity.Complexity.SparseDenseWorkspace
open _root_.Complexity _root_.Complexity.TM HeaderAt

abbrev oldWork (work : Fin 64 → Tape) : Fin 33 → Tape := InitialTapeLift.oldWork 31 work

def Pred (L n : ℕ) (s : CountedSparseControl.State) (emitted : List Bool) :
    _root_.Complexity.TM.TapePred 64 := fun inp work out =>
  SparseDimensionEmit.Pred L n s emitted inp (oldWork work) out ∧ InitialTapeLift.Fresh 33 31 work

def machine (boxed : Bool) : TM 64 := (SparseDimensionRewind.machine boxed).liftTM 31

theorem allParked (L n : ℕ) (s : CountedSparseControl.State) (emitted : List Bool)
    (inp : Tape) (work : Fin 64 → Tape) (out : Tape) (hp : Pred L n s emitted inp work out) :
    ∀ j, Parked (work j) := by
  intro j
  by_cases hj : j.val < 33
  · let k : Fin 33 := ⟨j.val, hj⟩
    have he : Fin.castAdd 31 k = j := Fin.ext rfl
    simpa only [oldWork, InitialTapeLift.oldWork, he] using hp.1.1.2.1 k
  · rw [hp.2 j (by omega)]
    exact parked_regTape 0

theorem cursor (L n : ℕ) (s : CountedSparseControl.State) (emitted : List Bool)
    (inp : Tape) (work : Fin 64 → Tape) (out : Tape) (hp : Pred L n s emitted inp work out) :
    Cursor s.base.before s.base.input emitted inp work out := by
  have hc := hp.1.1.1
  have hs := allParked L n s emitted inp work out hp
  exact ⟨hc.cells, hc.head, fun j => ⟨(hs j).read_ne_start, (hs j).1⟩, hc.tapePrefix, hc.zero⟩

theorem phase (L n : ℕ) (s : CountedSparseControl.State) (emitted : List Bool) :
    ∀ inp work out, Pred L n s emitted inp work out →
      Pred L n s emitted (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out hp
  obtain ⟨hi, hw, ho⟩ := (cursor L n s emitted inp work out hp).phase
  rw [hi, hw, ho]
  exact hp

theorem hoareTime (boxed : Bool) (input : List Bool) :
    (machine boxed).HoareTime (InitialTapeLift.Initial 64 input)
      (Pred input.length (HeaderControl.count input)
        (SparseDimensionRewind.restart (SparseDimensionEntry.outcome boxed input) input)
        (SparseDimensionWords.header boxed (HeaderControl.count input) (SparseDimensionEntry.outcome boxed input).rows))
      (SparseDimensionRewind.timeBound input.length) := by
  have hh := SparseDimensionRewind.hoareTime boxed input
  exact InitialTapeLift.hoareTime (SparseDimensionRewind.machine boxed) 31 input _ _ hh (by
    intro h
    cases h)

theorem canonical_hoareTime (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (hp : SparseInteger.DegreeLE 4 p.payload) :
    (machine boxed).HoareTime (InitialTapeLift.Initial 64 (SparsePolynomialCodec.code p))
      (Pred (SparsePolynomialCodec.code p).length p.arity
        ⟨⟨false, [], SparsePolynomialCodec.code p, 1 + SparseOffsetCode.total boxed p.payload⟩,
          CountedSparseCode.rowTotal p.payload⟩
        (SparseDimensionWords.header boxed p.arity (CountedSparseCode.rowTotal p.payload)))
      (SparseDimensionRewind.timeBound (SparsePolynomialCodec.code p).length) := by
  have ht := hoareTime boxed (SparsePolynomialCodec.code p)
  rw [SparseCountedEntry.count_code, SparseDimensionEntry.outcome_code boxed p hp] at ht
  exact ht

end JointThermoComplexity.Complexity.SparseDenseWorkspace

#print axioms JointThermoComplexity.Complexity.SparseDenseWorkspace.hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDenseWorkspace.canonical_hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDenseWorkspace.cursor
