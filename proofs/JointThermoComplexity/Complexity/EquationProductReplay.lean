module
public import proofs.JointThermoComplexity.Complexity.SmallCoefficientDispatch

set_option autoImplicit false
@[expose] public section

/-! Actual signed row-square coefficient output from two stored words.
The operand ports may coincide. A shared constant buffer and flag implement
the two finite lookups while every operand and surrounding tape is retained.
-/

namespace JointThermoComplexity.Complexity.EquationProductReplay
open _root_.Complexity _root_.Complexity.TM BoxBufferState
open HeaderAt (Cursor)
open BinaryDifferenceCursor (Separate)
variable {w : ℕ}

structure Ports (w : ℕ) where
  left : Fin (w + 1)
  right : Fin (w + 1)
  constant : Fin (w + 1)
  flag : Fin (w + 1)
  left_separate : Separate left constant flag
  right_separate : Separate right constant flag

def leftPorts (p : Ports w) : SmallCoefficientMatch.Ports w := ⟨p.left, p.constant, p.flag, p.left_separate⟩
def rightPorts (p : Ports w) : SmallCoefficientMatch.Ports w := ⟨p.right, p.constant, p.flag, p.right_separate⟩
def Stable (p : Ports w) (R : (Fin (w + 1) → Tape) → Prop) : Prop := SmallCoefficientMatch.Stable (leftPorts p) R

def LeftFrame (p : Ports w) (xs : List Bool) (B : ℕ) (R : (Fin (w + 1) → Tape) → Prop)
    (work : Fin (w + 1) → Tape) : Prop :=
  (work p.left).HasBinaryString xs ∧ (work p.left).cells 0 = Γ.start ∧ xs.length ≤ 4 * B ∧ R work
def RightFrame (p : Ports w) (ys : List Bool) (B : ℕ) (R : (Fin (w + 1) → Tape) → Prop)
    (work : Fin (w + 1) → Tape) : Prop :=
  (work p.right).HasBinaryString ys ∧ (work p.right).cells 0 = Γ.start ∧ ys.length ≤ 4 * B ∧ R work

def Logical (p : Ports w) (xs ys : List Bool) (B : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) :=
  SmallCoefficientMatch.Logical (leftPorts p) xs B before input emitted (RightFrame p ys B R)

theorem left_frame_stable (p : Ports w) (xs : List Bool) (B : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    SmallCoefficientMatch.Stable (rightPorts p) (LeftFrame p xs B R) := by
  rintro work work' he ⟨hx, hz, hl, hr⟩
  exact ⟨by simpa only [he p.left p.left_separate.operands p.left_separate.flagLeft.symm] using hx,
    by simpa only [he p.left p.left_separate.operands p.left_separate.flagLeft.symm] using hz, hl,
    hR work work' he hr⟩

theorem right_frame_stable (p : Ports w) (ys : List Bool) (B : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    SmallCoefficientMatch.Stable (leftPorts p) (RightFrame p ys B R) := by
  rintro work work' he ⟨hy, hz, hl, hr⟩
  exact ⟨by simpa only [he p.right p.right_separate.operands p.right_separate.flagLeft.symm] using hy,
    by simpa only [he p.right p.right_separate.operands p.right_separate.flagLeft.symm] using hz, hl,
    hR work work' he hr⟩

theorem literal_hoareTime (p : SmallCoefficientMatch.Ports w) (xs bits : List Bool) (B : ℕ)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) :
    (emitBitsTM (n := w + 1) bits).HoareTime
      (SmallCoefficientMatch.Logical p xs B before input emitted R)
      (SmallCoefficientMatch.Logical p xs B before input (emitted ++ bits) R) bits.length :=
  (FixedOutput.hoareTime bits before input emitted (SmallCoefficientMatch.Ready p xs B R)).consequence
    (fun _ _ _ ⟨hc, hr⟩ => ⟨hc, hr.1, hr⟩) (fun _ _ _ ⟨hc, _, hr⟩ => ⟨hc, hr⟩) le_rfl

def bodyMachine (p : Ports w) (z : ℤ) : TM (w + 1) :=
  SmallCoefficientDispatch.machine (rightPorts p) (fun q => emitBitsTM (SmallCoefficientTable.product z q))
    (emitBitsTM []) SmallCoefficientTable.catalog

def machine (p : Ports w) : TM (w + 1) :=
  SmallCoefficientDispatch.machine (leftPorts p) (bodyMachine p) (emitBitsTM []) SmallCoefficientTable.catalog

def innerOutput (ys : List Bool) (z : ℤ) : List Bool :=
  SmallCoefficientTable.select ys (SmallCoefficientTable.product z) [] SmallCoefficientTable.catalog
def output (xs ys : List Bool) : List Bool :=
  SmallCoefficientTable.select xs (innerOutput ys) [] SmallCoefficientTable.catalog
def innerTime (B : ℕ) : ℕ := SmallCoefficientDispatch.timeBound B 28 11
def timeBound (B : ℕ) : ℕ := 22 * (SmallCoefficientMatch.timeBound B + 3) + 28

theorem body_hoareTime (p : Ports w) (xs ys : List Bool) (z : ℤ) (hz : z.natAbs ≤ 5) (B : ℕ) (hB : 2 ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (bodyMachine p z).HoareTime (Logical p xs ys B before input emitted R)
      (Logical p xs ys B before input (emitted ++ innerOutput ys z) R) (innerTime B) := by
  have hbody : ∀ q ∈ SmallCoefficientTable.catalog, (emitBitsTM (n := w + 1) (SmallCoefficientTable.product z q)).HoareTime
      (SmallCoefficientMatch.Logical (rightPorts p) ys B before input emitted (LeftFrame p xs B R))
      (SmallCoefficientMatch.Logical (rightPorts p) ys B before input (emitted ++ SmallCoefficientTable.product z q)
        (LeftFrame p xs B R)) 28 := by
    intro q hq
    exact (literal_hoareTime (rightPorts p) ys (SmallCoefficientTable.product z q) B before input emitted
      (LeftFrame p xs B R)).mono_bound (SmallCoefficientTable.product_bound z q hz (SmallCoefficientTable.catalog_bound q hq))
  have hf := (literal_hoareTime (rightPorts p) ys [] B before input emitted (LeftFrame p xs B R)).mono_bound
    (show ([] : List Bool).length ≤ 28 by decide)
  have h := SmallCoefficientDispatch.hoareTime (rightPorts p) ys SmallCoefficientTable.catalog
    SmallCoefficientTable.catalog_bound B 28 hB before input emitted (LeftFrame p xs B R)
    (left_frame_stable p xs B R hR) (fun q => emitBitsTM (SmallCoefficientTable.product z q))
    (SmallCoefficientTable.product z) (emitBitsTM []) [] hbody hf
  apply h.consequence
  · rintro inp work out ⟨hc, hs, hx, hxz, hxl, hb, hflag, hy, hyz, hyl, hr⟩
    exact ⟨hc, hs, hy, hyz, hyl, hb, hflag, hx, hxz, hxl, hr⟩
  · rintro inp work out ⟨hc, hs, hy, hyz, hyl, hb, hflag, hx, hxz, hxl, hr⟩
    exact ⟨hc, hs, hx, hxz, hxl, hb, hflag, hy, hyz, hyl, hr⟩
  · simp only [SmallCoefficientTable.catalog_length]
    exact le_rfl

theorem hoareTime (p : Ports w) (xs ys : List Bool) (B : ℕ) (hB : 2 ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p).HoareTime (Logical p xs ys B before input emitted R)
      (Logical p xs ys B before input (emitted ++ output xs ys) R) (timeBound B) := by
  have hbody : ∀ z ∈ SmallCoefficientTable.catalog, (bodyMachine p z).HoareTime
      (Logical p xs ys B before input emitted R)
      (Logical p xs ys B before input (emitted ++ innerOutput ys z) R) (innerTime B) :=
    fun z hz => body_hoareTime p xs ys z (SmallCoefficientTable.catalog_bound z hz) B hB before input emitted R hR
  have hf := (literal_hoareTime (leftPorts p) xs [] B before input emitted (RightFrame p ys B R)).mono_bound
    (show ([] : List Bool).length ≤ innerTime B by simp only [List.length_nil]; omega)
  have h := SmallCoefficientDispatch.hoareTime (leftPorts p) xs SmallCoefficientTable.catalog
    SmallCoefficientTable.catalog_bound B (innerTime B) hB before input emitted (RightFrame p ys B R)
    (right_frame_stable p ys B R hR) (bodyMachine p) (innerOutput ys) (emitBitsTM []) [] hbody hf
  exact h.mono_bound (by simp only [timeBound, innerTime, SmallCoefficientDispatch.timeBound, SmallCoefficientTable.catalog_length]; omega)

theorem output_code (a b : ℤ) (ha : a.natAbs ≤ 5) (hb : b.natAbs ≤ 5) :
    output (BitCodec.integerCode a) (BitCodec.integerCode b) = BitCodec.integerCode (-256 * a * b) := by
  unfold output
  rw [SmallCoefficientTable.select_catalog a ha]
  unfold innerOutput
  rw [SmallCoefficientTable.select_catalog b hb]
  rfl

theorem encoded_hoareTime (p : Ports w) (a b : ℤ) (ha : a.natAbs ≤ 5) (hb : b.natAbs ≤ 5) (B : ℕ) (hB : 2 ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p).HoareTime (Logical p (BitCodec.integerCode a) (BitCodec.integerCode b) B before input emitted R)
      (Logical p (BitCodec.integerCode a) (BitCodec.integerCode b) B before input
        (emitted ++ BitCodec.integerCode (-256 * a * b)) R) (timeBound B) := by
  simpa only [output_code a b ha hb] using
    hoareTime p (BitCodec.integerCode a) (BitCodec.integerCode b) B hB before input emitted R hR

end JointThermoComplexity.Complexity.EquationProductReplay

#print axioms JointThermoComplexity.Complexity.EquationProductReplay.hoareTime
#print axioms JointThermoComplexity.Complexity.EquationProductReplay.output_code
#print axioms JointThermoComplexity.Complexity.EquationProductReplay.encoded_hoareTime
