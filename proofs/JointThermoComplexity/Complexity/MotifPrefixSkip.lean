module
public import proofs.JointThermoComplexity.Complexity.MotifRecordFrame

set_option autoImplicit false
@[expose] public section

/-! An actual retained-counter loop traverses a prefix of supplied motif records and restores all registers. -/

namespace JointThermoComplexity.Complexity.MotifPrefixSkip
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InvariantLoop

variable {w n r : ℕ}

def code (items : List (NetworkData.Motif n r)) : List Bool := items.flatMap (DataCodec.motif n r).code

theorem code_append (left right : List (NetworkData.Motif n r)) : code (left ++ right) = code left ++ code right :=
  List.flatMap_append

theorem code_take_succ (items : List (NetworkData.Motif n r)) (i : ℕ) (hi : i < items.length) :
    code (items.take (i + 1)) = code (items.take i) ++ (DataCodec.motif n r).code items[i] := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [code, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem code_drop_succ (items : List (NetworkData.Motif n r)) (i : ℕ) (hi : i < items.length) :
    code (items.drop i) = (DataCodec.motif n r).code items[i] ++ code (items.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

def machine (species reactions outer : Fin w) : TM w := forRegTM (MotifRecordSkip.machine species reactions) outer

def timeBound (n r count : ℕ) : ℕ := count * (MotifRecordSkip.timeBound n r + 2) + (count + 2)

def Invariant (species reactions : Fin w) (items : List (NetworkData.Motif n r)) (before tail emitted : List Bool)
    (R : (Fin w → Tape) → Tape → Prop) (i : ℕ) : _root_.Complexity.TapePred w :=
  fun inp work out => Cursor (before ++ code (items.take i)) (code (items.drop i) ++ tail) emitted inp work out ∧
    IsReg n (work species) ∧ IsReg r (work reactions) ∧ R work out

theorem hoareTime (species reactions outer : Fin w) (hspecies : species ≠ outer) (hreactions : reactions ≠ outer)
    (items : List (NetworkData.Motif n r)) (before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (machine species reactions outer).HoareTime
      (fun inp work out => Cursor before (code items ++ tail) emitted inp work out ∧
        IsReg items.length (work outer) ∧ IsReg n (work species) ∧ IsReg r (work reactions) ∧ R work out)
      (fun inp work out => Cursor (before ++ code items) tail emitted inp work out ∧
        IsReg items.length (work outer) ∧ IsReg n (work species) ∧ IsReg r (work reactions) ∧ R work out)
      (timeBound n r items.length) := by
  have hb : ∀ i, i < items.length → (MotifRecordSkip.machine species reactions).HoareTime
      (Frame outer items.length (i + 2) (Invariant species reactions items before tail emitted R i))
      (Frame outer items.length (i + 2) (Invariant species reactions items before tail emitted R (i + 1)))
      (MotifRecordSkip.timeBound n r) := by
    intro i hi
    have hs := MotifRecordFrame.hoareTime outer species reactions hspecies hreactions items.length (i + 2) (by omega)
      items[i] (before ++ code (items.take i)) (code (items.drop (i + 1)) ++ tail) emitted R
    exact hs.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, code_drop_succ items i hi, List.append_assoc] using hp.invariant) (by
        intro inp work out hp
        refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
        simpa only [Invariant, code_take_succ items i hi, List.append_assoc] using hp.invariant) le_rfl
  have hs := InvariantLoop.hoareTime (MotifRecordSkip.machine species reactions) outer
    (Invariant species reactions items before tail emitted R) (MotifRecordSkip.timeBound n r) items.length hb
  exact hs.consequence (by
    rintro inp work out ⟨hc, houter, hn, hr, hR⟩
    refine ⟨houter.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work outer items.length houter.eq_regT]
    simpa only [Invariant, List.take_zero, List.drop_zero, code, List.flatMap_nil, List.append_nil]
      using And.intro hc (And.intro hn (And.intro hr hR))) (by
        intro inp work out hp
        have h := hp.on_work
        exact ⟨by simpa only [Invariant, List.take_length, List.drop_length, code, List.flatMap_nil, List.nil_append] using h.1,
          hp.register, h.2⟩) le_rfl

end JointThermoComplexity.Complexity.MotifPrefixSkip

#print axioms JointThermoComplexity.Complexity.MotifPrefixSkip.hoareTime
