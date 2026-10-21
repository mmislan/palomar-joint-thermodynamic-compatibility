module
public import proofs.JointThermoComplexity.Complexity.NaturalArrayIndexedLoad
public import proofs.JointThermoComplexity.Complexity.ReactionSkip

set_option autoImplicit false
@[expose] public section

/-! Fixed-port machines load the selected actual reactant or product payload from a literal reaction record. -/

namespace JointThermoComplexity.Complexity.ReactionNaturalSelect
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState NaturalSelectionCode ReactionCircuit

variable {w n : ℕ}

def factors (q : Reaction n) (tail : List Bool) : List Bool :=
  BitCodec.naturalCode q.numerator ++ BitCodec.naturalCode q.denominator ++ tail

abbrev reactantMachine (idx position : Fin (w + 1)) : TM (w + 1) := NaturalArrayIndexedLoad.machine idx position

theorem reactant_hoareTime (idx position : Fin (w + 1)) (hne : position ≠ idx) (L : ℕ)
    (q : Reaction n) (hq : ReactionSkip.Bounded L q) (s : Fin n)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (reactantMachine idx position).HoareTime
      (fun inp work out => Cursor before ((DataCodec.reaction n).code q ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ IsReg s.val (work position) ∧ R work)
      (fun inp work out => Cursor ((before ++ leading q.reactant s) ++ BitCodec.naturalCode (q.reactant s))
        (trailing q.reactant s ++ NaturalArraySkip.code q.product ++ factors q tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString (q.reactant s).bits ∧ (work idx).cells 0 = Γ.start ∧
        Reusable L (work idx) ∧ IsReg s.val (work position) ∧ R work) (NaturalIndexedLoad.timeBound L) := by
  have h := NaturalArrayIndexedLoad.hoareTime idx position hne L hq.1 q.reactant s hq.2.1 before
    (NaturalArraySkip.code q.product ++ factors q tail) emitted R hR
  exact h.consequence (by
    intro inp work out h
    simpa only [ReactionSkip.code_eq, factors, List.append_assoc] using h) (by
      intro inp work out h
      simpa only [List.append_assoc] using h) le_rfl

def productMachine (idx count position : Fin (w + 1)) : TM (w + 1) :=
  seqTM (NaturalArraySkip.machine count) (NaturalArrayIndexedLoad.machine idx position)

def productTimeBound (L : ℕ) : ℕ := 2 * L ^ 2 + 21 * L + 21

theorem product_hoareTime (idx count position : Fin (w + 1)) (hcount : count ≠ idx) (hposition : position ≠ idx) (L : ℕ)
    (q : Reaction n) (hq : ReactionSkip.Bounded L q) (s : Fin n)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (productMachine idx count position).HoareTime
      (fun inp work out => Cursor before ((DataCodec.reaction n).code q ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ IsReg s.val (work position) ∧ IsReg n (work count) ∧ R work)
      (fun inp work out => Cursor (((before ++ NaturalArraySkip.code q.reactant) ++ leading q.product s) ++ BitCodec.naturalCode (q.product s))
        (trailing q.product s ++ factors q tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString (q.product s).bits ∧ (work idx).cells 0 = Γ.start ∧
        Reusable L (work idx) ∧ IsReg s.val (work position) ∧ IsReg n (work count) ∧ R work) (productTimeBound L) := by
  let R' : (Fin (w + 1) → Tape) → Prop := fun work => IsReg n (work count) ∧ R work
  have hR' : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R' work → R' work' := by
    rintro work work' hw ⟨hc, hr⟩
    exact ⟨by simpa only [hw count hcount] using hc, hR work work' hw hr⟩
  have hs := NaturalArraySkip.hoareTime count L hq.1 q.reactant hq.2.1 before
    (NaturalArraySkip.code q.product ++ factors q tail) emitted
    (fun work _ => (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ IsReg s.val (work position) ∧ R work)
  have hl := NaturalArrayIndexedLoad.hoareTime idx position hposition L hq.1 q.product s hq.2.2.1
    (before ++ NaturalArraySkip.code q.reactant) (factors q tail) emitted R' hR'
  have hfull := seqTM_hoareTime (NaturalArraySkip.machine count) (NaturalArrayIndexedLoad.machine idx position) hs (by
    rintro inp work out ⟨hc, hn, hs, hb, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hb, hp, hn, hr⟩) hl
  exact hfull.consequence (by
    rintro inp work out ⟨hc, hs, hb, hp, hn, hr⟩
    exact ⟨by simpa only [ReactionSkip.code_eq, factors, List.append_assoc] using hc, hn, hs, hb, hp, hr⟩)
    (fun _ _ _ h => h) (by unfold NaturalArraySkip.timeBound NaturalIndexedLoad.timeBound productTimeBound; omega)

end JointThermoComplexity.Complexity.ReactionNaturalSelect

#print axioms JointThermoComplexity.Complexity.ReactionNaturalSelect.reactant_hoareTime
#print axioms JointThermoComplexity.Complexity.ReactionNaturalSelect.product_hoareTime
