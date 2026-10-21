module
public import proofs.JointThermoComplexity.Complexity.GeneratedEnergyLoop

set_option autoImplicit false
@[expose] public section

/-! Generated address traversal retains any frame outside its two buffers.
The restored unary fuel may itself occur in that frame. -/

namespace JointThermoComplexity.Complexity.GeneratedLoopFramed
open _root_.Complexity _root_.Complexity.TM
open GeneratedEnergyStep GeneratedEnergyLoop StrictGeneratedTemplates
variable {w : ℕ}

theorem hoareTime (p : Ports w) (r : Fin w) (hp : ∀ i, r ≠ p.index i) (values : Fin 2 → ℕ)
    (W count : ℕ) (hW : ∀ j, values j + count ≤ W) (kind : Kind)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : Stable p R) :
    (GeneratedEnergyLoop.machine p r kind).HoareTime
      (fun inp work out => Logical p values before input emitted R inp work out ∧ IsReg count (work r))
      (fun inp work out => Logical p (valuesAt values count) before input
        (emitted ++ entries values kind count) R inp work out ∧ IsReg count (work r))
      (GeneratedEnergyLoop.timeBound W count kind) := by
  rintro inp work out ⟨⟨hc, hr⟩, hf⟩
  let C : (Fin w → Tape) → Prop := fun next => ∀ j, j ≠ r → (∀ i, j ≠ p.index i) → next j = work j
  have hC : Stable p C := by
    intro a b he ha j hj hp
    exact (he j hp).trans (ha j hj hp)
  have hCF : FuelStable r C := by
    intro a b he ha j hj hp
    exact (he j hj).trans (ha j hj hp)
  have h := GeneratedEnergyLoop.bounded_hoareTime p r hp values W count hW kind before input emitted C hC hCF
  obtain ⟨d, t, ht, hd, hh, ⟨hc', hr'⟩, hf'⟩ :=
    h inp work out ⟨⟨hc, ⟨hr.safe, hr.registers, fun _ _ _ => rfl⟩⟩, hf⟩
  have hother : ∀ j, (∀ i, j ≠ p.index i) → d.work j = work j := by
    intro j hj
    by_cases hjr : j = r
    · subst j
      exact hf'.eq_regT.trans hf.eq_regT.symm
    · exact hr'.extra j hjr hj
  exact ⟨d, t, ht, hd, hh, ⟨hc', ⟨hr'.safe, hr'.registers, hR work d.work hother hr.extra⟩⟩, hf'⟩

def Framed (p : Ports w) (r : Fin w) (count : ℕ) (values : Fin 2 → ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred w :=
  fun inp work out => Logical p values before input emitted R inp work out ∧ IsReg count (work r)

def sectionMachine (p : Ports w) (r : Fin w) (initial edge : Kind) : TM w :=
  seqTM (StrictGeneratedBytes.machine p.index initial) (GeneratedEnergyLoop.machine p r edge)

def sectionTime (W count : ℕ) (initial edge : Kind) : ℕ :=
  StrictGeneratedBytes.timeBound W initial + 1 + GeneratedEnergyLoop.timeBound W count edge

theorem section_hoareTime (p : Ports w) (r : Fin w) (hp : ∀ i, r ≠ p.index i) (values : Fin 2 → ℕ)
    (W count : ℕ) (hW : ∀ j, values j + count ≤ W) (initial edge : Kind)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : Stable p R) :
    (sectionMachine p r initial edge).HoareTime (Framed p r count values before input emitted R)
      (Framed p r count (valuesAt values count) before input
        ((emitted ++ RowSquareCanonical.entries (data values initial)) ++ entries values edge count) R)
      (sectionTime W count initial edge) := by
  have hv : ∀ j, (values j).bits.length ≤ W := fun j =>
    (BinaryIncrementControl.bits_length_le _).trans (by have := hW j; omega)
  have he := StrictGeneratedBytes.hoareTime p.index values W hv initial before input emitted
    (fun work => R work ∧ IsReg count (work r))
  have hi : (StrictGeneratedBytes.machine p.index initial).HoareTime
      (Framed p r count values before input emitted R)
      (Framed p r count values before input (emitted ++ RowSquareCanonical.entries (data values initial)) R)
      (StrictGeneratedBytes.timeBound W initial) := he.consequence (by
    rintro inp work out ⟨⟨hc, hr⟩, hf⟩
    exact ⟨hc, hr.safe, hr.registers, hr.extra, hf⟩) (by
    rintro inp work out ⟨hc, hs, hv, hx, hf⟩
    exact ⟨⟨hc, ⟨hs, hv, hx⟩⟩, hf⟩) le_rfl
  have hl := hoareTime p r hp values W count hW edge before input
    (emitted ++ RowSquareCanonical.entries (data values initial)) R hR
  exact seqTM_hoareTime _ _ hi (by
    rintro inp work out ⟨⟨hc, hr⟩, hf⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨⟨hc, hr⟩, hf⟩) hl

end JointThermoComplexity.Complexity.GeneratedLoopFramed

#print axioms JointThermoComplexity.Complexity.GeneratedLoopFramed.hoareTime
#print axioms JointThermoComplexity.Complexity.GeneratedLoopFramed.section_hoareTime
