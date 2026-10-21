module
public import proofs.JointThermoComplexity.Complexity.BooleanWordFrame

set_option autoImplicit false
@[expose] public section

/-! Nested traversal of a fixed-width table, with both count registers restored. -/

namespace JointThermoComplexity.Complexity.FixedWordsSkip
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InvariantLoop

variable {w : ℕ}

def code (items : List (List Bool)) : List Bool := items.flatMap id

def machine (inner outer : Fin w) : TM w := forRegTM (BooleanWordSkip.machine inner) outer

def timeBound (width count : ℕ) : ℕ := count * (4 * width + 4) + (count + 2)

def Invariant (inner : Fin w) (width : ℕ) (items : List (List Bool)) (before tail emitted : List Bool)
    (R : (Fin w → Tape) → Tape → Prop) (i : ℕ) : _root_.Complexity.TapePred w :=
  fun inp work out => Cursor (before ++ code (items.take i)) (code (items.drop i) ++ tail) emitted inp work out ∧
    IsReg width (work inner) ∧ R work out

theorem code_take_succ (items : List (List Bool)) (i : ℕ) (hi : i < items.length) :
    code (items.take (i + 1)) = code (items.take i) ++ items[i] := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [code, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, id_eq]

theorem code_drop_succ (items : List (List Bool)) (i : ℕ) (hi : i < items.length) :
    code (items.drop i) = items[i] ++ code (items.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem hoareTime (inner outer : Fin w) (hne : inner ≠ outer) (width : ℕ) (items : List (List Bool))
    (hlen : ∀ bits ∈ items, bits.length = width) (before tail emitted : List Bool)
    (R : (Fin w → Tape) → Tape → Prop) :
    (machine inner outer).HoareTime
      (fun inp work out => Cursor before (code items ++ tail) emitted inp work out ∧
        IsReg items.length (work outer) ∧ IsReg width (work inner) ∧ R work out)
      (fun inp work out => Cursor (before ++ code items) tail emitted inp work out ∧
        IsReg items.length (work outer) ∧ IsReg width (work inner) ∧ R work out)
      (timeBound width items.length) := by
  have hb : ∀ i, i < items.length → (BooleanWordSkip.machine inner).HoareTime
      (Frame outer items.length (i + 2) (Invariant inner width items before tail emitted R i))
      (Frame outer items.length (i + 2) (Invariant inner width items before tail emitted R (i + 1)))
      (4 * width + 2) := by
    intro i hi
    have hw := hlen items[i] (List.getElem_mem hi)
    have hs := BooleanWordFrame.hoareTime outer inner hne items.length (i + 2) (by omega) items[i]
      (before ++ code (items.take i)) (code (items.drop (i + 1)) ++ tail) emitted R
    exact hs.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, code_drop_succ items i hi, List.append_assoc, hw] using hp.invariant) (by
        intro inp work out hp
        refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
        simpa only [Invariant, code_take_succ items i hi, List.append_assoc, hw] using hp.invariant)
      (by rw [hw])
  have hs := InvariantLoop.hoareTime (BooleanWordSkip.machine inner) outer
    (Invariant inner width items before tail emitted R) (4 * width + 2) items.length hb
  exact hs.consequence (by
    rintro inp work out ⟨hc, hr, hi, hp⟩
    refine ⟨hr.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work outer items.length hr.eq_regT]
    simpa only [Invariant, List.take_zero, List.drop_zero, code, List.flatMap_nil, List.append_nil]
      using And.intro hc (And.intro hi hp)) (by
        intro inp work out hp
        have h := hp.on_work
        exact ⟨by simpa only [Invariant, List.take_length, List.drop_length, code, List.flatMap_nil, List.nil_append] using h.1,
          hp.register, h.2⟩) (Nat.add_le_add_right
            (Nat.mul_le_mul_left items.length (show 4 * width + 2 + 2 ≤ 4 * width + 4 by omega)) _)

end JointThermoComplexity.Complexity.FixedWordsSkip

#print axioms JointThermoComplexity.Complexity.FixedWordsSkip.hoareTime
