module
public import proofs.JointThermoComplexity.Complexity.DenseComplexCore

set_option autoImplicit false
@[expose] public section

/-! Actual baseline/offset external arrays need no canonical absent source references. -/

namespace JointThermoComplexity.Complexity.DenseFixedExternalPower
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseComplexCore

def boxedMachine : TM 64 := RepeatedOutput.machine (16 : Fin 64) (BitCodec.naturalCode 0)
def boxedBound (n : ℕ) : ℕ := DenseInternalBlocks.zeroBound n

theorem boxed_emits (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n : ℕ) :
    Emits boxedMachine m hm values n (FiniteCodec.functionCode FiniteCodec.natural (fun _ : Fin n => 0)) (boxedBound n) := by
  intro before input emitted R _
  let S : (Fin 64 → Tape) → Prop := fun work => Register 0 (work DensePowerPorts.index) ∧
    PowerVectorUnit.Refs (DensePowerPorts.cellLayout m hm) values work ∧ R work
  have hz : RepeatedOutput.copies (BitCodec.naturalCode 0) n =
      FiniteCodec.functionCode FiniteCodec.natural (fun _ : Fin n => 0) := DenseBlockWords.zeros_code n
  have hh := RepeatedOutput.hoareTime (16 : Fin 64) n before input emitted (BitCodec.naturalCode 0) S
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hi, hr, hf, hx⟩
    exact ⟨hf, hc, hs, hi, hr, hx⟩
  · rintro inp work out ⟨hf, hc, hs, hi, hr, hx⟩
    exact ⟨by simpa only [hz] using hc, hs, hi, hr, hf, hx⟩
  · exact le_rfl

theorem zero_tail_code (n : ℕ) :
    FiniteCodec.functionCode FiniteCodec.natural (fun _ : Fin (n + n) => 0) =
      DenseBlockWords.zeros n ++ DenseBlockWords.zeros n := by
  have he : Fin.append (fun _ : Fin n => (0 : ℕ)) (fun _ : Fin n => (0 : ℕ)) = (fun _ : Fin (n + n) => 0) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  rw [← he, DenseBlockWords.code_append]
  simp only [DenseBlockWords.zeros_code]

theorem unboxed_code (n a : ℕ) :
    FiniteCodec.functionCode FiniteCodec.natural (Fin.cons a (fun _ : Fin (n + n) => 0)) =
      BitCodec.naturalCode a ++ (DenseBlockWords.zeros n ++ DenseBlockWords.zeros n) := by
  simpa only [FiniteCodec.functionCode, Fin.cons_zero, Fin.cons_succ, FiniteCodec.natural] using
    congrArg (fun rest => BitCodec.naturalCode a ++ rest) (zero_tail_code n)

def unboxedMachine (a : ℕ) : TM 64 :=
  seqTM (emitBitsTM (BitCodec.naturalCode a)) (seqTM boxedMachine boxedMachine)
def unboxedBound (n a : ℕ) : ℕ := 2 * boxedBound n + (BitCodec.naturalCode a).length + 2

theorem unboxed_emits (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n a : ℕ) :
    Emits (unboxedMachine a) m hm values n
      (FiniteCodec.functionCode FiniteCodec.natural (Fin.cons a (fun _ : Fin (n + n) => 0))) (unboxedBound n a) := by
  intro before input emitted R hR
  let z := FiniteCodec.functionCode FiniteCodec.natural (fun _ : Fin n => 0)
  have h1 := boxed_emits m hm values n before input (emitted ++ BitCodec.naturalCode a) R hR
  have h2 := boxed_emits m hm values n before input ((emitted ++ BitCodec.naturalCode a) ++ z) R hR
  have hh := seqTM_hoareTime _ _ h1 (by
    intro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.phase
    rw [hi, hw, ho]
    exact hp) h2
  let S : (Fin 64 → Tape) → Prop := fun work => Register 0 (work DensePowerPorts.index) ∧
    PowerVectorUnit.Refs (DensePowerPorts.cellLayout m hm) values work ∧ IsReg n (work 16) ∧ R work
  have h0 := FixedOutput.hoareTime (BitCodec.naturalCode a) before input emitted S
  have hall := seqTM_hoareTime _ _ h0 (by
    intro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.phase
    rw [hi, hw, ho]
    exact hp) hh
  have hc : FiniteCodec.functionCode FiniteCodec.natural (Fin.cons a (fun _ : Fin (n + n) => 0)) =
      BitCodec.naturalCode a ++ (z ++ z) := by
    rw [unboxed_code]
    simp only [DenseBlockWords.zeros_code, z]
  apply hall.consequence
  · exact fun _ _ _ hp => hp
  · rintro inp work out ⟨hcur, hs, hi, hr, hf, hx⟩
    refine ⟨?_, hs, hi, hr, hf, hx⟩
    rw [hc]
    simpa only [z, List.append_assoc] using hcur
  · unfold unboxedBound
    omega

end JointThermoComplexity.Complexity.DenseFixedExternalPower

#print axioms JointThermoComplexity.Complexity.DenseFixedExternalPower.boxed_emits
#print axioms JointThermoComplexity.Complexity.DenseFixedExternalPower.unboxed_emits
