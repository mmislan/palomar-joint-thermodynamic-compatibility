module
public import proofs.JointThermoComplexity.Complexity.BoxLoad
public import proofs.JointThermoComplexity.Complexity.BoxOutputReady

set_option autoImplicit false
@[expose] public section

/-! Identify the four physical literal buffers with the fixed rational-box output template. -/

namespace JointThermoComplexity.Complexity.BoxStoredWords
open _root_.Complexity
open _root_.Complexity.TM
open BoxBufferState NetworkData

variable {w : ℕ}

def buffers (loNum loDen hiNum hiDen : Fin (w + 1)) (b : ClosedBox) (j : Fin (w + 1)) : List Bool :=
  if j = loNum then BitCodec.integerCode b.lower.numerator else
  if j = loDen then BitCodec.naturalCode b.lower.denominator else
  if j = hiNum then BitCodec.integerCode b.upper.numerator else
  if j = hiDen then BitCodec.naturalCode b.upper.denominator else []

theorem lo_num (loNum loDen hiNum hiDen : Fin (w + 1)) (b : ClosedBox) :
    buffers loNum loDen hiNum hiDen b loNum = BitCodec.integerCode b.lower.numerator := by simp [buffers]

theorem lo_den (loNum loDen hiNum hiDen : Fin (w + 1)) (sep : BoxLoad.Separate loNum loDen hiNum hiDen) (b : ClosedBox) :
    buffers loNum loDen hiNum hiDen b loDen = BitCodec.naturalCode b.lower.denominator := by simp [buffers, sep.lo.symm]

theorem hi_num (loNum loDen hiNum hiDen : Fin (w + 1)) (sep : BoxLoad.Separate loNum loDen hiNum hiDen) (b : ClosedBox) :
    buffers loNum loDen hiNum hiDen b hiNum = BitCodec.integerCode b.upper.numerator := by
  simp [buffers, sep.ln_hn.symm, sep.ld_hn.symm]

theorem hi_den (loNum loDen hiNum hiDen : Fin (w + 1)) (sep : BoxLoad.Separate loNum loDen hiNum hiDen) (b : ClosedBox) :
    buffers loNum loDen hiNum hiDen b hiDen = BitCodec.naturalCode b.upper.denominator := by
  simp [buffers, sep.ln_hd.symm, sep.ld_hd.symm, sep.hi.symm]

theorem ready {arity : ℕ} (loNum loDen hiNum hiDen source : Fin (w + 1))
    (sep : BoxLoad.Separate loNum loDen hiNum hiDen) (b : ClosedBox) (idx : Fin arity)
    (work : Fin (w + 1) → Tape) (hs : IsReg idx.val (work source))
    (hln : Stored (BitCodec.integerCode b.lower.numerator) (work loNum))
    (hld : Stored (BitCodec.naturalCode b.lower.denominator) (work loDen))
    (hhn : Stored (BitCodec.integerCode b.upper.numerator) (work hiNum))
    (hhd : Stored (BitCodec.naturalCode b.upper.denominator) (work hiDen)) :
    BoxOutput.Ready loNum loDen hiNum hiDen source (fun _ => idx.val) (buffers loNum loDen hiNum hiDen b) work := by
  refine ⟨hs, ?_⟩
  intro j hj
  have he : j = loNum ∨ j = loDen ∨ j = hiNum ∨ j = hiDen := by simpa using hj
  rcases he with h | h | h | h
  · subst j; simpa only [lo_num, Stored] using hln
  · subst j; simpa only [lo_den loNum loDen hiNum hiDen sep b, Stored] using hld
  · subst j; simpa only [hi_num loNum loDen hiNum hiDen sep b, Stored] using hhn
  · subst j; simpa only [hi_den loNum loDen hiNum hiDen sep b, Stored] using hhd

theorem sizes (L : ℕ) (loNum loDen hiNum hiDen : Fin (w + 1))
    (sep : BoxLoad.Separate loNum loDen hiNum hiDen) (b : ClosedBox)
    (hln : (BitCodec.integerCode b.lower.numerator).length ≤ L)
    (hld : (BitCodec.naturalCode b.lower.denominator).length ≤ L)
    (hhn : (BitCodec.integerCode b.upper.numerator).length ≤ L)
    (hhd : (BitCodec.naturalCode b.upper.denominator).length ≤ L) :
    ∀ j ∈ [loNum, loDen, hiNum, hiDen], (buffers loNum loDen hiNum hiDen b j).length ≤ L := by
  intro j hj
  have he : j = loNum ∨ j = loDen ∨ j = hiNum ∨ j = hiDen := by simpa using hj
  rcases he with h | h | h | h
  · subst j; simpa only [lo_num] using hln
  · subst j; simpa only [lo_den loNum loDen hiNum hiDen sep b] using hld
  · subst j; simpa only [hi_num loNum loDen hiNum hiDen sep b] using hhn
  · subst j; simpa only [hi_den loNum loDen hiNum hiDen sep b] using hhd

end JointThermoComplexity.Complexity.BoxStoredWords

#print axioms JointThermoComplexity.Complexity.BoxStoredWords.ready
#print axioms JointThermoComplexity.Complexity.BoxStoredWords.sizes
