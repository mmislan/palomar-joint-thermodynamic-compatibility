module
public import proofs.JointThermoComplexity.Complexity.NaturalSkipFrame

set_option autoImplicit false
@[expose] public section

/-! A register-controlled pass over binary natural fields, preserving all work and output. -/

namespace JointThermoComplexity.Complexity.NaturalListSkip
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InvariantLoop

variable {w : ℕ}

def code (items : List ℕ) : List Bool := items.flatMap BitCodec.naturalCode

def machine (fuel : Fin w) : TM w := forRegTM NaturalSkip.machine fuel

def timeBound (L count : ℕ) : ℕ := count * (L + 2) + (count + 2)

def Invariant (items : List ℕ) (before tail emitted : List Bool)
    (R : (Fin w → Tape) → Tape → Prop) (i : ℕ) : _root_.Complexity.TapePred w :=
  fun inp work out => Cursor (before ++ code (items.take i)) (code (items.drop i) ++ tail) emitted inp work out ∧ R work out

theorem code_take_succ (items : List ℕ) (i : ℕ) (hi : i < items.length) :
    code (items.take (i + 1)) = code (items.take i) ++ BitCodec.naturalCode items[i] := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [code, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem code_drop_succ (items : List ℕ) (i : ℕ) (hi : i < items.length) :
    code (items.drop i) = BitCodec.naturalCode items[i] ++ code (items.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem hoareTime (fuel : Fin w) (L : ℕ) (items : List ℕ)
    (hsize : ∀ value ∈ items, (BitCodec.naturalCode value).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (machine fuel).HoareTime
      (fun inp work out => Cursor before (code items ++ tail) emitted inp work out ∧ IsReg items.length (work fuel) ∧ R work out)
      (fun inp work out => Cursor (before ++ code items) tail emitted inp work out ∧ IsReg items.length (work fuel) ∧ R work out)
      (timeBound L items.length) := by
  have hb : ∀ i, i < items.length → (NaturalSkip.machine (w := w)).HoareTime
      (Frame fuel items.length (i + 2) (Invariant items before tail emitted R i))
      (Frame fuel items.length (i + 2) (Invariant items before tail emitted R (i + 1))) L := by
    intro i hi
    have hs := NaturalSkipFrame.hoareTime fuel items.length (i + 2) (by omega) items[i]
      (before ++ code (items.take i)) (code (items.drop (i + 1)) ++ tail) emitted R
    exact hs.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, code_drop_succ items i hi, List.append_assoc] using hp.invariant) (by
        intro inp work out hp
        refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
        simpa only [Invariant, code_take_succ items i hi, List.append_assoc] using hp.invariant)
      (hsize items[i] (List.getElem_mem hi))
  have hs := InvariantLoop.hoareTime (NaturalSkip.machine (w := w)) fuel
    (Invariant items before tail emitted R) L items.length hb
  exact hs.consequence (by
    rintro inp work out ⟨hc, hf, hr⟩
    refine ⟨hf.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work fuel items.length hf.eq_regT]
    simpa only [Invariant, List.take_zero, List.drop_zero, code, List.flatMap_nil, List.append_nil]
      using And.intro hc hr) (by
        intro inp work out hp
        have h := hp.on_work
        exact ⟨by simpa only [Invariant, List.take_length, List.drop_length, code, List.flatMap_nil, List.nil_append] using h.1,
          hp.register, h.2⟩) le_rfl

end JointThermoComplexity.Complexity.NaturalListSkip

#print axioms JointThermoComplexity.Complexity.NaturalListSkip.hoareTime
