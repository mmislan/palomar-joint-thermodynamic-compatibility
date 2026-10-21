module
public import proofs.JointThermoComplexity.Complexity.RowSquareControl
public import proofs.JointThermoComplexity.Complexity.EquationRowFrame

set_option autoImplicit false
@[expose] public section

/-! Row-square output keeps all saved row data. Three additional ports hold
the lookup constant, comparison flag and raw shared-scale coordinate.
-/

namespace JointThermoComplexity.Complexity.RowSquareFrame
open _root_.Complexity _root_.Complexity.TM BoxBufferState EquationRowControl
open HeaderAt (Cursor)
variable {w : ℕ}

structure Ports (w : ℕ) where
  index : Fin 28 → Fin (w + 1)
  injective : Function.Injective index

namespace Ports
def row (p : Ports w) : EquationRowFrame.Ports w :=
  ⟨fun a => p.index ⟨a.val, by omega⟩, fun a b h => Fin.ext (congrArg (fun j : Fin 28 => j.val) (p.injective h))⟩
def constant (p : Ports w) : Fin (w + 1) := p.index 25
def compare (p : Ports w) : Fin (w + 1) := p.index 26
def scale (p : Ports w) : Fin (w + 1) := p.index 27

theorem separate (p : Ports w) (a b : Fin 28) (h : a.val ≠ b.val) : p.index a ≠ p.index b :=
  p.injective.ne (Fin.ne_of_val_ne h)
theorem constant_row (p : Ports w) (a : Fin 25) : p.constant ≠ p.row.index a := p.separate _ _ (by dsimp; omega)
theorem compare_row (p : Ports w) (a : Fin 25) : p.compare ≠ p.row.index a := p.separate _ _ (by dsimp; omega)
theorem scale_constant (p : Ports w) : p.scale ≠ p.constant := p.separate _ _ (by decide)
theorem scale_compare (p : Ports w) : p.scale ≠ p.compare := p.separate _ _ (by decide)
theorem compare_constant (p : Ports w) : p.compare ≠ p.constant := p.separate _ _ (by decide)

def productPorts (p : Ports w) (i j : Fin 3) : EquationProductReplay.Ports w where
  left := p.row.coefficient i
  right := p.row.coefficient j
  constant := p.constant
  flag := p.compare
  left_separate := ⟨(p.constant_row (EquationRowFrame.Ports.slotIndex i 5)).symm,
    p.compare_row (EquationRowFrame.Ports.slotIndex i 5), p.compare_constant⟩
  right_separate := ⟨(p.constant_row (EquationRowFrame.Ports.slotIndex j 5)).symm,
    p.compare_row (EquationRowFrame.Ports.slotIndex j 5), p.compare_constant⟩

def raw (p : Ports w) : Fin 7 → Fin (w + 1) :=
  ![p.row.word 0 0, p.row.word 0 1, p.row.word 1 0, p.row.word 1 1, p.row.word 2 0, p.row.word 2 1, p.scale]
end Ports

def Stable (p : Ports w) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work work', (∀ j, j ≠ p.constant → j ≠ p.compare → work' j = work j) → R work → R work'

structure Ready (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape) : Prop where
  saved : EquationRowFrame.Ready p.row s B R work
  scale : (work p.scale).HasBinaryString scaleBits
  scale_zero : (work p.scale).cells 0 = Γ.start
  scale_length : scaleBits.length ≤ W
  word_bound : 4 * B ≤ W
  constant : Reusable B (work p.constant)
  compare_head : (work p.compare).head = 1

def Logical (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) :=
  fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s scaleBits B W R work

theorem reframe (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) (work next : Fin (w + 1) → Tape)
    (he : ∀ j, j ≠ p.constant → j ≠ p.compare → next j = work j) (hs : ∀ j, Parked (next j))
    (hc : Reusable B (next p.constant)) (hf : (next p.compare).head = 1)
    (h : Ready p s scaleBits B W R work) : Ready p s scaleBits B W R next := by
  have hrow (a : Fin 25) : next (p.row.index a) = work (p.row.index a) :=
    he _ (p.constant_row a).symm (p.compare_row a).symm
  have hsaved : EquationRowFrame.Ready p.row s B R next := by
    refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hR work next he h.saved.extra⟩
    · intro i
      simpa only [EquationRowFrame.Ports.presence, hrow] using h.saved.presence i
    · intro i j
      simpa only [EquationRowFrame.Ports.flag, EquationRowFrame.Ports.slot, hrow] using h.saved.flags i j
    · intro i j
      simpa only [EquationRowFrame.Ports.word, EquationRowFrame.Ports.slot, hrow] using h.saved.words i j
    · intro i
      simpa only [EquationRowFrame.Ports.coefficient, EquationRowFrame.Ports.slot, hrow] using h.saved.coefficients i
    · simpa only [EquationRowFrame.Ports.available, hrow] using h.saved.available_head
    · simpa only [EquationRowFrame.Ports.available, hrow] using h.saved.available_read
    · simpa only [EquationRowFrame.Ports.loopAvailable, hrow] using h.saved.loop_head
    · simpa only [EquationRowFrame.Ports.scratch, hrow] using h.saved.scratch
    · simpa only [EquationRowFrame.Ports.fuel, hrow] using h.saved.fuel
  exact ⟨hsaved, by simpa only [he p.scale p.scale_constant p.scale_compare] using h.scale,
    by simpa only [he p.scale p.scale_constant p.scale_compare] using h.scale_zero,
    h.scale_length, h.word_bound, hc, hf⟩

theorem raw_ready (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape) (h : Ready p s scaleBits B W R work) :
    WordCodeProgram.Ready p.raw (RowSquareControl.values s scaleBits) (Ready p s scaleBits B W R) work := by
  refine ⟨?_, h⟩
  intro a
  fin_cases a
  · exact ⟨(h.saved.words 0 0).1, (h.saved.words 0 0).2.1⟩
  · exact ⟨(h.saved.words 0 1).1, (h.saved.words 0 1).2.1⟩
  · exact ⟨(h.saved.words 1 0).1, (h.saved.words 1 0).2.1⟩
  · exact ⟨(h.saved.words 1 1).1, (h.saved.words 1 1).2.1⟩
  · exact ⟨(h.saved.words 2 0).1, (h.saved.words 2 0).2.1⟩
  · exact ⟨(h.saved.words 2 1).1, (h.saved.words 2 1).2.1⟩
  · exact ⟨h.scale, h.scale_zero⟩

theorem raw_bound (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape) (h : Ready p s scaleBits B W R work) :
    ∀ a, (RowSquareControl.values s scaleBits a).length ≤ W := by
  intro a
  fin_cases a
  · exact (h.saved.words 0 0).2.2.trans h.word_bound
  · exact (h.saved.words 0 1).2.2.trans h.word_bound
  · exact (h.saved.words 1 0).2.2.trans h.word_bound
  · exact (h.saved.words 1 1).2.2.trans h.word_bound
  · exact (h.saved.words 2 0).2.2.trans h.word_bound
  · exact (h.saved.words 2 1).2.2.trans h.word_bound
  · exact h.scale_length

theorem literal_hoareTime (p : Ports w) (s : State) (scaleBits bits : List Bool) (B W : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) :
    (emitBitsTM (n := w + 1) bits).HoareTime (Logical p s scaleBits B W emitted R)
      (Logical p s scaleBits B W (emitted ++ bits) R) bits.length :=
  (FixedOutput.hoareTime bits s.before s.input emitted (Ready p s scaleBits B W R)).consequence
    (fun _ _ _ ⟨hc, hr⟩ => ⟨hc, hr.saved.safe, hr⟩) (fun _ _ _ ⟨hc, _, hr⟩ => ⟨hc, hr⟩) le_rfl

end JointThermoComplexity.Complexity.RowSquareFrame

#print axioms JointThermoComplexity.Complexity.RowSquareFrame.reframe
#print axioms JointThermoComplexity.Complexity.RowSquareFrame.raw_ready
