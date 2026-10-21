module
public import proofs.JointThermoComplexity.Complexity.ReactionSkip
public import proofs.JointThermoComplexity.Complexity.NaturalArrayFrame
public import proofs.JointThermoComplexity.Complexity.ReactionArrayData

set_option autoImplicit false
@[expose] public section

/-! Traverse an entire reaction table with distinct species and reaction fuel tapes. -/

namespace JointThermoComplexity.Complexity.ReactionListSkip
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InvariantLoop ReactionCircuit ReactionArrayData

variable {w n : ℕ}

def machine (species reactions : Fin w) : TM w := forRegTM (ReactionSkip.machine species) reactions

def timeBound (L count : ℕ) : ℕ := count * (ReactionSkip.timeBound L + 2) + (count + 2)

def Invariant (species : Fin w) (items : List (Reaction n)) (before tail emitted : List Bool)
    (R : (Fin w → Tape) → Tape → Prop) (i : ℕ) : _root_.Complexity.TapePred w :=
  fun inp work out => Cursor (before ++ code (items.take i)) (code (items.drop i) ++ tail) emitted inp work out ∧
    IsReg n (work species) ∧ R work out

theorem hoareTime (species reactions : Fin w) (hne : species ≠ reactions) (L : ℕ)
    (items : List (Reaction n)) (hsize : ∀ q ∈ items, ReactionSkip.Bounded L q)
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (machine species reactions).HoareTime
      (fun inp work out => Cursor before (code items ++ tail) emitted inp work out ∧
        IsReg items.length (work reactions) ∧ IsReg n (work species) ∧ R work out)
      (fun inp work out => Cursor (before ++ code items) tail emitted inp work out ∧
        IsReg items.length (work reactions) ∧ IsReg n (work species) ∧ R work out)
      (timeBound L items.length) := by
  have hb : ∀ i, i < items.length → (ReactionSkip.machine species).HoareTime
      (Frame reactions items.length (i + 2) (Invariant species items before tail emitted R i))
      (Frame reactions items.length (i + 2) (Invariant species items before tail emitted R (i + 1)))
      (ReactionSkip.timeBound L) := by
    intro i hi
    have hs := ReadOnlyFrame.hoareTime (ReactionSkip.machine species) reactions items.length (i + 2) (by omega)
      ((DataCodec.reaction n).code items[i]) (before ++ code (items.take i)) (code (items.drop (i + 1)) ++ tail) emitted
      (fun work => IsReg n (work species)) (ReactionSkip.timeBound L)
      (by intro work work' he hp; simpa only [he species hne] using hp)
      (fun S => ReactionSkip.hoareTime species L items[i] (hsize items[i] (List.getElem_mem hi))
        (before ++ code (items.take i)) (code (items.drop (i + 1)) ++ tail) emitted S) R
    exact hs.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, drop_code items i hi, List.append_assoc] using hp.invariant) (by
        intro inp work out hp
        refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
        simpa only [Invariant, take_code_succ items i hi, List.append_assoc] using hp.invariant) le_rfl
  have hs := InvariantLoop.hoareTime (ReactionSkip.machine species) reactions
    (Invariant species items before tail emitted R) (ReactionSkip.timeBound L) items.length hb
  exact hs.consequence (by
    rintro inp work out ⟨hc, hr, hs, hp⟩
    refine ⟨hr.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work reactions items.length hr.eq_regT]
    simpa only [Invariant, List.take_zero, List.drop_zero, code, List.append_nil]
      using And.intro hc (And.intro hs hp)) (by
        intro inp work out hp
        have h := hp.on_work
        exact ⟨by simpa only [Invariant, List.take_length, List.drop_length, code, List.nil_append] using h.1,
          hp.register, h.2⟩) le_rfl

end JointThermoComplexity.Complexity.ReactionListSkip

#print axioms JointThermoComplexity.Complexity.ReactionListSkip.hoareTime
