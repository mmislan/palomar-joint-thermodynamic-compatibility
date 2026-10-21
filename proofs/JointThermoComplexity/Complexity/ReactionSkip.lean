module
public import proofs.JointThermoComplexity.Complexity.NaturalArraySkip
public import proofs.JointThermoComplexity.Complexity.DataCodec

set_option autoImplicit false
@[expose] public section

/-! A read-only pass over one literal reaction, including its fixed rational factor. -/

namespace JointThermoComplexity.Complexity.ReactionSkip
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ReactionCircuit

variable {w n : ℕ}

def Bounded (L : ℕ) (q : Reaction n) : Prop := n ≤ L ∧
  (∀ i, (BitCodec.naturalCode (q.reactant i)).length ≤ L) ∧
  (∀ i, (BitCodec.naturalCode (q.product i)).length ≤ L) ∧
  (BitCodec.naturalCode q.numerator).length ≤ L ∧
  (BitCodec.naturalCode q.denominator).length ≤ L

def machine (species : Fin w) : TM w := seqTM
  (seqTM (seqTM (NaturalArraySkip.machine species) (NaturalArraySkip.machine species)) NaturalSkip.machine)
  NaturalSkip.machine

def timeBound (L : ℕ) : ℕ := 2 * L ^ 2 + 8 * L + 7

theorem code_eq (q : Reaction n) : (DataCodec.reaction n).code q =
    (NaturalArraySkip.code q.reactant ++ NaturalArraySkip.code q.product) ++
      (BitCodec.naturalCode q.numerator ++ BitCodec.naturalCode q.denominator) := rfl

theorem hoareTime (species : Fin w) (L : ℕ) (q : Reaction n) (hq : Bounded L q)
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (machine species).HoareTime
      (fun inp work out => Cursor before ((DataCodec.reaction n).code q ++ tail) emitted inp work out ∧
        IsReg n (work species) ∧ R work out)
      (fun inp work out => Cursor (before ++ (DataCodec.reaction n).code q) tail emitted inp work out ∧
        IsReg n (work species) ∧ R work out) (timeBound L) := by
  let a := NaturalArraySkip.code q.reactant
  let b := NaturalArraySkip.code q.product
  let p := BitCodec.naturalCode q.numerator
  let d := BitCodec.naturalCode q.denominator
  have ha := NaturalArraySkip.hoareTime species L hq.1 q.reactant hq.2.1
    before (b ++ p ++ d ++ tail) emitted R
  have hb := NaturalArraySkip.hoareTime species L hq.1 q.product hq.2.2.1
    (before ++ a) (p ++ d ++ tail) emitted R
  have hp := (NaturalSkipExact.hoareTime q.numerator ((before ++ a) ++ b) (d ++ tail) emitted
    (fun work out => IsReg n (work species) ∧ R work out)).consequence
    (fun _ _ _ h => h) (fun _ _ _ h => h) hq.2.2.2.1
  have hd := (NaturalSkipExact.hoareTime q.denominator (((before ++ a) ++ b) ++ p) tail emitted
    (fun work out => IsReg n (work species) ∧ R work out)).consequence
    (fun _ _ _ h => h) (fun _ _ _ h => h) hq.2.2.2.2
  have hab := seqTM_hoareTime (NaturalArraySkip.machine species) (NaturalArraySkip.machine species) ha (by
    rintro inp work out ⟨hc, hs, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨by simpa only [a, b, List.append_assoc] using hc, hs, hr⟩) hb
  have habp := seqTM_hoareTime (seqTM (NaturalArraySkip.machine species) (NaturalArraySkip.machine species))
    NaturalSkip.machine hab (by
      rintro inp work out ⟨hc, hs, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨by simpa only [b, p, List.append_assoc] using hc, hs, hr⟩) hp
  have habpd := seqTM_hoareTime
    (seqTM (seqTM (NaturalArraySkip.machine species) (NaturalArraySkip.machine species)) NaturalSkip.machine)
    NaturalSkip.machine habp (by
      rintro inp work out ⟨hc, hs, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨by simpa only [p, List.append_assoc] using hc, hs, hr⟩) hd
  exact habpd.consequence
    (fun _ _ _ h => by simpa only [code_eq, a, b, p, d, List.append_assoc] using h)
    (fun _ _ _ h => by simpa only [code_eq, a, b, p, d, List.append_assoc] using h)
    (by unfold NaturalArraySkip.timeBound timeBound; omega)

end JointThermoComplexity.Complexity.ReactionSkip

#print axioms JointThermoComplexity.Complexity.ReactionSkip.hoareTime
