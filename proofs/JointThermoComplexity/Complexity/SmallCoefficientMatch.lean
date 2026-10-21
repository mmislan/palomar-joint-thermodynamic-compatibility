module
public import proofs.JointThermoComplexity.Complexity.SmallCoefficientTable
public import proofs.JointThermoComplexity.Complexity.ConstantWordLoad
public import proofs.JointThermoComplexity.Complexity.BinaryCompareRewind
public import proofs.JointThermoComplexity.Complexity.WorkSymbolBranch

set_option autoImplicit false
@[expose] public section

/-! Actual encoded-coefficient matching by two retained binary comparisons.
Only the constant and flag tapes may change; the operand tape is restored exactly.
-/

namespace JointThermoComplexity.Complexity.SmallCoefficientMatch
open _root_.Complexity _root_.Complexity.TM BoxBufferState
open HeaderAt (Cursor)
open BinaryDifferenceCursor (Separate)
open BinaryDifferenceRuntime (Start)
variable {w : ℕ}

structure Ports (w : ℕ) where
  operand : Fin (w + 1)
  constant : Fin (w + 1)
  flag : Fin (w + 1)
  separate : Separate operand constant flag

def Stable (p : Ports w) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work work', (∀ j, j ≠ p.constant → j ≠ p.flag → work' j = work j) → R work → R work'

def Ready (p : Ports w) (bits : List Bool) (B : ℕ) (R : (Fin (w + 1) → Tape) → Prop)
    (work : Fin (w + 1) → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ (work p.operand).HasBinaryString bits ∧ (work p.operand).cells 0 = Γ.start ∧
    bits.length ≤ 4 * B ∧ Reusable B (work p.constant) ∧ (work p.flag).head = 1 ∧ R work

def Logical (p : Ports w) (bits : List Bool) (B : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) :=
  fun inp work out => Cursor before input emitted inp work out ∧ Ready p bits B R work

theorem binary_unique (bits : List Bool) (a b : Tape) (ha : a.HasBinaryString bits) (hb : b.HasBinaryString bits)
    (hza : a.cells 0 = Γ.start) (hzb : b.cells 0 = Γ.start) : a = b := by
  apply Tape.ext (ha.1.trans hb.1.symm)
  funext j
  cases j with
  | zero => exact hza.trans hzb.symm
  | succ k =>
    by_cases hk : k < bits.length
    · exact (ha.2.1 k hk).trans (hb.2.1 k hk).symm
    · exact (ha.2.2 k (by omega)).trans (hb.2.2 k (by omega)).symm

theorem compare_retained (left right flag : Fin (w + 1)) (sep : Separate left right flag)
    (xs ys before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ flag → work' j = work j) → R work → R work') :
    (BinaryCompareRewind.machine left right flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Start left right flag xs ys work ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ Start left right flag xs ys work ∧
        (work flag).read = Γ.ofBool (BinaryDifference.subtract xs ys false).2 ∧ R work)
      (BinaryCompareRewind.timeBound xs ys) := by
  rintro inp work out ⟨hc, hs, hr⟩
  let C : (Fin (w + 1) → Tape) → Prop := fun next =>
    ∀ j, j ≠ left → j ≠ right → j ≠ flag → next j = work j
  have hC : ∀ a b, (∀ j, j ≠ left → j ≠ right → j ≠ flag → b j = a j) → C a → C b := by
    intro a b he ha j hl hr hf
    exact (he j hl hr hf).trans (ha j hl hr hf)
  obtain ⟨d, time, ht, hd, hh, hc', hs', hf, he⟩ :=
    BinaryCompareRewind.hoareTime left right flag sep xs ys before input emitted C hC
      inp work out ⟨hc, hs, fun _ _ _ _ => rfl⟩
  have hsame : ∀ j, j ≠ flag → d.work j = work j := by
    intro j hj
    by_cases hl : j = left
    · subst j
      exact binary_unique xs _ _ hs'.lhs hs.lhs hs'.lhsZero hs.lhsZero
    · by_cases hr : j = right
      · subst j
        exact binary_unique ys _ _ hs'.rhs hs.rhs hs'.rhsZero hs.rhsZero
      · exact he j hl hr hj
  exact ⟨d, time, ht, hd, hh, hc', hs', hf, hR work d.work hsame hr⟩

def Known (p : Ports w) (xs ys : List Bool) (B : ℕ) (R : (Fin (w + 1) → Tape) → Prop)
    (work : Fin (w + 1) → Tape) : Prop :=
  Start p.operand p.constant p.flag xs ys work ∧ xs.length ≤ 4 * B ∧ ys.length ≤ 4 * B ∧ R work

theorem load_hoareTime (p : Ports w) (xs ys : List Bool) (B : ℕ) (hy : ys.length ≤ 4 * B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (ConstantWordLoad.machine p.constant ys).HoareTime
      (Logical p xs B before input emitted R)
      (fun inp work out => Cursor before input emitted inp work out ∧ Known p xs ys B R work) (20 * B + 14) := by
  let C : (Fin (w + 1) → Tape) → Prop := fun work =>
    (work p.operand).HasBinaryString xs ∧ (work p.operand).cells 0 = Γ.start ∧
    xs.length ≤ 4 * B ∧ (work p.flag).head = 1 ∧ R work
  have hC : ∀ work work', (∀ j, j ≠ p.constant → work' j = work j) → C work → C work' := by
    rintro work work' he ⟨hb, hz, hl, hf, hr⟩
    exact ⟨by simpa only [he _ p.separate.operands] using hb,
      by simpa only [he _ p.separate.operands] using hz, hl,
      by simpa only [he _ p.separate.flagRight] using hf,
      hR work work' (fun j hj _ => he j hj) hr⟩
  have h := ConstantWordLoad.hoareTime B p.constant ys before input emitted hy C hC
  exact h.consequence
    (fun _ _ _ ⟨hc, hs, hb, hz, hl, hy, hf, hr⟩ => ⟨hc, hs, hy, hb, hz, hl, hf, hr⟩)
    (fun _ _ _ ⟨hc, hs, hy', hz', _, hb, hz, hl, hf, hr⟩ =>
      ⟨hc, ⟨hs, hb, hy', hz, hz', hf⟩, hl, hy, hr⟩) le_rfl

theorem compare_hoareTime (p : Ports w) (xs ys : List Bool) (B : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (BinaryCompareRewind.machine p.operand p.constant p.flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Known p xs ys B R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ Known p xs ys B R work ∧
        (work p.flag).read = Γ.ofBool (BinaryDifference.subtract xs ys false).2) (12 * B + 9) := by
  rintro inp work out ⟨hc, hs, hx, hy, hr⟩
  have hframe : ∀ work work', (∀ j, j ≠ p.flag → work' j = work j) → R work → R work' :=
    fun work work' he => hR work work' (fun j _ hf => he j hf)
  obtain ⟨d, time, ht, hd, hh, hc', hs', hf, hr'⟩ :=
    compare_retained p.operand p.constant p.flag p.separate xs ys before input emitted R hframe inp work out ⟨hc, hs, hr⟩
  refine ⟨d, time, ?_, hd, hh, hc', ⟨hs', hx, hy, hr'⟩, hf⟩
  unfold BinaryCompareRewind.timeBound at ht
  omega

theorem reverse_hoareTime (p : Ports w) (xs ys : List Bool) (B : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (BinaryCompareRewind.machine p.constant p.operand p.flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Known p xs ys B R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ Known p xs ys B R work ∧
        (work p.flag).read = Γ.ofBool (BinaryDifference.subtract ys xs false).2) (12 * B + 9) := by
  rintro inp work out ⟨hc, hs, hx, hy, hr⟩
  have sep : Separate p.constant p.operand p.flag := ⟨p.separate.operands.symm, p.separate.flagRight, p.separate.flagLeft⟩
  have hframe : ∀ work work', (∀ j, j ≠ p.flag → work' j = work j) → R work → R work' :=
    fun work work' he => hR work work' (fun j _ hf => he j hf)
  have hswap : Start p.constant p.operand p.flag ys xs work := ⟨hs.safe, hs.rhs, hs.lhs, hs.rhsZero, hs.lhsZero, hs.flagHead⟩
  obtain ⟨d, time, ht, hd, hh, hc', hs', hf, hr'⟩ :=
    compare_retained p.constant p.operand p.flag sep ys xs before input emitted R hframe inp work out ⟨hc, hswap, hr⟩
  refine ⟨d, time, ?_, hd, hh, hc', ⟨⟨hs'.safe, hs'.rhs, hs'.lhs, hs'.rhsZero, hs'.lhsZero, hs'.flagHead⟩, hx, hy, hr'⟩, hf⟩
  unfold BinaryCompareRewind.timeBound at ht
  omega

def secondMachine (p : Ports w) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one p.flag (emitBitsTM []) (BinaryCompareRewind.machine p.constant p.operand p.flag)

theorem second_hoareTime (p : Ports w) (xs ys : List Bool) (B : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (secondMachine p).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Known p xs ys B R work ∧
        (work p.flag).read = Γ.ofBool (BinaryDifference.subtract xs ys false).2)
      (fun inp work out => Cursor before input emitted inp work out ∧ Known p xs ys B R work ∧
        (work p.flag).read = Γ.ofBool (!((!(BinaryDifference.subtract xs ys false).2) &&
          (!(BinaryDifference.subtract ys xs false).2)))) (12 * B + 11) := by
  cases (BinaryDifference.subtract xs ys false).2 with
  | true =>
    let P := fun work => Known p xs ys B R work ∧ (work p.flag).read = Γ.one
    have hid : (emitBitsTM (n := w + 1) []).HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ P work)
        (fun inp work out => Cursor before input emitted inp work out ∧ P work) 0 :=
      (FixedOutput.hoareTime [] before input emitted P).consequence
      (fun _ _ _ ⟨hc, hp⟩ => ⟨hc, hp.1.1.safe, hp⟩)
      (fun _ _ _ ⟨hc, _, hp⟩ => by simpa only [List.append_nil] using And.intro hc hp) le_rfl
    have h := WorkSymbolBranch.yes_hoareTime Γ.one p.flag (emitBitsTM [])
      (BinaryCompareRewind.machine p.constant p.operand p.flag) before input emitted before input emitted P P 0 hid
    apply h.consequence
    · rintro inp work out ⟨hc, hk, hf⟩
      have he : (work p.flag).read = Γ.one := by simpa only [Γ.ofBool] using hf
      exact ⟨⟨hc, hk, he⟩, he⟩
    · rintro inp work out ⟨hc, hk, hf⟩
      exact ⟨hc, hk, by simpa only [Bool.not_true, Bool.false_and, Bool.not_false, Γ.ofBool] using hf⟩
    · omega
  | false =>
    have h := WorkSymbolBranch.no_hoareTime Γ.one p.flag (emitBitsTM [])
      (BinaryCompareRewind.machine p.constant p.operand p.flag) before input emitted before input emitted
      (Known p xs ys B R) (fun work => Known p xs ys B R work ∧
        (work p.flag).read = Γ.ofBool (BinaryDifference.subtract ys xs false).2) (12 * B + 9)
      (reverse_hoareTime p xs ys B before input emitted R hR)
    apply h.consequence
    · rintro inp work out ⟨hc, hk, hf⟩
      refine ⟨⟨hc, hk⟩, ?_⟩
      rw [hf]
      decide
    · rintro inp work out ⟨hc, hk, hf⟩
      exact ⟨hc, hk, by simpa only [Bool.not_false, Bool.true_and, Bool.not_not] using hf⟩
    · exact le_rfl

def pairMachine (p : Ports w) : TM (w + 1) :=
  seqTM (BinaryCompareRewind.machine p.operand p.constant p.flag) (secondMachine p)

def machine (p : Ports w) (z : ℤ) : TM (w + 1) :=
  seqTM (ConstantWordLoad.machine p.constant (BitCodec.integerCode z)) (pairMachine p)

def timeBound (B : ℕ) : ℕ := 44 * B + 50

theorem hoareTime (p : Ports w) (bits : List Bool) (z : ℤ) (hz : z.natAbs ≤ 5) (B : ℕ) (hB : 2 ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p z).HoareTime (Logical p bits B before input emitted R)
      (fun inp work out => Logical p bits B before input emitted R inp work out ∧
        (work p.flag).read = Γ.ofBool (!(SmallCoefficientTable.equalCode bits z))) (timeBound B) := by
  have hzlen : (BitCodec.integerCode z).length ≤ 4 * B := by have := SmallCoefficientTable.word_bound z hz; omega
  have hload := load_hoareTime p bits (BitCodec.integerCode z) B hzlen before input emitted R hR
  have hpair := seqTM_hoareTime _ _ (compare_hoareTime p bits (BitCodec.integerCode z) B before input emitted R hR) (by
    rintro inp work out ⟨hc, hk, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hk, hf⟩) (second_hoareTime p bits (BitCodec.integerCode z) B before input emitted R hR)
  have h := seqTM_hoareTime _ _ hload (by
    rintro inp work out ⟨hc, hk⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hk⟩) hpair
  apply h.consequence (fun _ _ _ hh => hh)
  · rintro inp work out ⟨hc, ⟨hs, hx, hy, hr⟩, hf⟩
    refine ⟨⟨hc, hs.safe, hs.lhs, hs.lhsZero, hx,
      ⟨BitCodec.integerCode z, hy, hs.rhs.2, hs.rhsZero, by rw [hs.rhs.1]; omega⟩, hs.flagHead, hr⟩, hf⟩
  · unfold timeBound
    omega

end JointThermoComplexity.Complexity.SmallCoefficientMatch

#print axioms JointThermoComplexity.Complexity.SmallCoefficientMatch.compare_retained
#print axioms JointThermoComplexity.Complexity.SmallCoefficientMatch.hoareTime
