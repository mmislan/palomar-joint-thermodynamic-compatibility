module
public import proofs.JointThermoComplexity.Complexity.RowSquareFrame

set_option autoImplicit false
@[expose] public section

/-! Actual one-entry output: marker, signed coefficient product, then the four
homogenized coordinates. The complete saved row and shared scale word survive.
-/

namespace JointThermoComplexity.Complexity.RowPairEntry
open _root_.Complexity _root_.Complexity.TM EquationRowControl RowSquareFrame
open HeaderAt (Cursor)
variable {w : ℕ}

theorem product_hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (i j : Fin 3) (B W : ℕ) (hB : 2 ≤ B)
    (emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (EquationProductReplay.machine (p.productPorts i j)).HoareTime (Logical p s scaleBits B W emitted R)
      (Logical p s scaleBits B W
        (emitted ++ EquationProductReplay.output (s.terms i).coefficient (s.terms j).coefficient) R)
      (EquationProductReplay.timeBound B) := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin (w + 1) → Tape) → Prop := fun next => ∀ k, k ≠ p.constant → k ≠ p.compare → next k = work k
  have hC : EquationProductReplay.Stable (p.productPorts i j) C := by
    intro a b he ha k hk hf
    exact (he k hk hf).trans (ha k hk hf)
  have hi := hr.saved.coefficients i
  have hj := hr.saved.coefficients j
  obtain ⟨d, time, ht, hd, hh, hc', hs, _, _, _, hconst, hflag, _, _, _, he⟩ :=
    EquationProductReplay.hoareTime (p.productPorts i j) (s.terms i).coefficient (s.terms j).coefficient
      B hB s.before s.input emitted C hC inp work out
      ⟨hc, hr.saved.safe, hi.1, hi.2.1, hi.2.2, hr.constant, hr.compare_head, hj.1, hj.2.1, hj.2.2, fun _ _ _ => rfl⟩
  exact ⟨d, time, ht, hd, hh, hc', reframe p s scaleBits B W R hR work d.work he hs hconst hflag hr⟩

theorem monomial_hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (i j di dj : Fin 3) (B W : ℕ)
    (emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) :
    (WordCodeProgram.machine p.raw (RowSquareControl.program i j di dj)).HoareTime
      (Logical p s scaleBits B W emitted R)
      (Logical p s scaleBits B W
        (emitted ++ WordCodeProgram.output (RowSquareControl.values s scaleBits) (RowSquareControl.program i j di dj)) R)
      (12 * W + 62) := by
  rintro inp work out ⟨hc, hr⟩
  have h := WordCodeProgram.hoareTime p.raw (RowSquareControl.values s scaleBits) W
    (raw_bound p s scaleBits B W R work hr) (RowSquareControl.program i j di dj) s.before s.input emitted
    (Ready p s scaleBits B W R)
  obtain ⟨d, time, ht, hd, hh, hc', _, _, hr'⟩ := h inp work out
    ⟨hc, hr.saved.safe, raw_ready p s scaleBits B W R work hr⟩
  exact ⟨d, time, by simpa only [RowSquareControl.program_time] using ht, hd, hh, hc', hr'⟩

def machine (p : Ports w) (i j di dj : Fin 3) : TM (w + 1) :=
  seqTM (seqTM (emitBitsTM [true]) (EquationProductReplay.machine (p.productPorts i j)))
    (WordCodeProgram.machine p.raw (RowSquareControl.program i j di dj))

def timeBound (B W : ℕ) : ℕ := EquationProductReplay.timeBound B + 12 * W + 70

theorem hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (i j di dj : Fin 3) (B W : ℕ) (hB : 2 ≤ B)
    (emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p i j di dj).HoareTime (Logical p s scaleBits B W emitted R)
      (Logical p s scaleBits B W (emitted ++ RowSquareControl.entry s scaleBits i j di dj) R) (timeBound B W) := by
  have hm := literal_hoareTime p s scaleBits [true] B W emitted R
  have hc := product_hoareTime p s scaleBits i j B W hB (emitted ++ [true]) R hR
  have hmc := seqTM_hoareTime _ _ hm (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hc
  have hw := monomial_hoareTime p s scaleBits i j di dj B W
    ((emitted ++ [true]) ++ EquationProductReplay.output (s.terms i).coefficient (s.terms j).coefficient) R
  have h := seqTM_hoareTime _ _ hmc (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hw
  apply h.consequence (fun _ _ _ hh => hh)
  · intro inp work out hh
    simpa only [Logical, RowSquareControl.entry, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using hh
  · unfold timeBound
    simp only [List.length_singleton]
    omega

end JointThermoComplexity.Complexity.RowPairEntry

#print axioms JointThermoComplexity.Complexity.RowPairEntry.product_hoareTime
#print axioms JointThermoComplexity.Complexity.RowPairEntry.monomial_hoareTime
#print axioms JointThermoComplexity.Complexity.RowPairEntry.hoareTime
