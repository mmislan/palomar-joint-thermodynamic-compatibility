module
public import proofs.JointThermoComplexity.Complexity.DenseBankSelect
public import proofs.JointThermoComplexity.Complexity.SparseTermOffsetControl

set_option autoImplicit false
@[expose] public section

/-! Complete actual sparse-term execution: canonicalize the raw coefficient and
references, select a finite packet, and return the reusable source-pass state. -/

namespace JointThermoComplexity.Complexity.DenseLoadedPacket
open _root_.Complexity _root_.Complexity.TM HeaderAt
open DenseSourceFrame

def machine (boxed right : Bool) : TM 64 := seqTM DenseParserPorts.machine (DenseBankSelect.machine boxed right)
def word (boxed right : Bool) (n N current : ℕ) (input : List Bool) : List Bool :=
  DenseBankSelect.word boxed right n N current (SignedRawControl.magnitude input) (SignedRawControl.negative input) (SignedRawControl.rest input)
def timeBound (boxed right : Bool) (L n N B : ℕ) : ℕ :=
  (75 * L + 118) + (DenseBankSelect.timeBound boxed right L n N B + 7) + 1

theorem count_eq (input : List Bool) : DenseBankSelect.count (SignedRawControl.rest input) = SparseTermOffsetControl.count input := rfl

theorem hoareTime (boxed right : Bool) (L n N B current : ℕ) (before input emitted : List Bool)
    (hlen : input.length ≤ L) (hLB : L ≤ B) (hbase : N + 2 ≤ B)
    (hfit : current + SparseTermOffsetControl.count input ≤ N + 2)
    (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    (machine boxed right).HoareTime (Pre L n N current before input emitted R)
      (Pre L n N (current + SparseTermOffsetControl.count input) (before ++ SparseTermOffsetControl.taken input)
        (SparseTermOffsetControl.rest input) (emitted ++ word boxed right n N current input) R) (timeBound boxed right L n N B) := by
  have hp := DenseParserPorts.hoareTime L before input emitted hlen (Core n N current R) (core_parser_stable n N current R hR)
  have h1 : DenseParserPorts.machine.HoareTime (Pre L n N current before input emitted R)
      (DenseBankSelect.Pre L n N current (SignedRawControl.magnitude input) (SignedRawControl.negative input)
        (SignedRawControl.rest input) (before ++ SparseTermOffsetControl.taken input) (SparseTermOffsetControl.rest input) emitted R)
      (75 * L + 118) := by
    apply hp.consequence
    · rintro inp work out ⟨hc, hs, hparser, hcore⟩
      exact ⟨hc, hs, hparser.1, hparser.2.1, hparser.2.2, hcore⟩
    · rintro inp work out ⟨hc, hs, hbuffer, hvalue, hsignHead, hsign, hready, hloaded, hcore⟩
      have hcur : Cursor (before ++ SparseTermOffsetControl.taken input) (SparseTermOffsetControl.rest input) emitted inp work out := by
        simpa only [SparseOffsetLayout.physical_length, SparseTermOffsetControl.taken, SparseTermOffsetControl.rest] using hc
      exact ⟨hcur, hs, ⟨⟨hbuffer, hsignHead, hready⟩, hcore⟩, hvalue, hsign, hloaded⟩
    · exact le_rfl
  have h2 := DenseBankSelect.hoareTime boxed right L n N B current (SignedRawControl.magnitude input) (SignedRawControl.negative input)
    (SignedRawControl.rest input) ((SignedRawControl.rest_length input).trans hlen)
    (((SignedRawControl.magnitude_bits_length input).trans hlen).trans hLB) hLB hbase
    (by simpa only [count_eq] using hfit) R hR (before ++ SparseTermOffsetControl.taken input) (SparseTermOffsetControl.rest input) emitted
  have hh := seqTM_hoareTime _ _ h1 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) h2
  apply hh.consequence (fun _ _ _ h => h)
  · intro inp work out h
    simpa only [count_eq, word] using h
  · unfold timeBound
    omega

end JointThermoComplexity.Complexity.DenseLoadedPacket

#print axioms JointThermoComplexity.Complexity.DenseLoadedPacket.hoareTime
