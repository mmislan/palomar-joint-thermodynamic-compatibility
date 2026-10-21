module
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Advance a static set of work heads by one cell, preserving every tape's contents and real input/output. -/

namespace JointThermoComplexity.Complexity.WorkHeadsAdvance
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def advance (ports : List (Fin w)) (work : Fin w → Tape) : Fin w → Tape :=
  fun j => if j ∈ ports then (work j).move .right else work j

def machine (ports : List (Fin w)) : TM w where
  Q := Bool
  qstart := false
  qhalt := true
  δ _ si sw so := (true, (fun j => readBackWrite (sw j)), readBackWrite so,
    idleDir si, (fun j => if j ∈ ports then .right else idleDir (sw j)), idleDir so)
  δ_right_of_start _ _ _ _ := by
    refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
    intro j hj
    by_cases he : j ∈ ports
    · simp only [he, ↓reduceIte]
    · simpa only [he, ↓reduceIte] using idleDir_right_of_start hj

theorem step (ports : List (Fin w)) (c : Cfg w (machine ports).Q) (hs : c.state = false)
    (hi : c.input.read ≠ Γ.start) (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine ports).step c = some ⟨true, c.input, advance ports c.work, c.output⟩ := by
  rw [TM.step, ite_eq_right (by simp [machine, hs])]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · exact transitionInput_eq_self hi
  · funext j
    by_cases hj : j ∈ ports
    · change (c.work j).writeAndMove (readBackWrite (c.work j).read) (if j ∈ ports then .right else idleDir (c.work j).read) =
        if j ∈ ports then (c.work j).move .right else c.work j
      simp only [hj, ↓reduceIte]
      exact writeAndMove_readBack _ (hw j) .right
    · change (c.work j).writeAndMove (readBackWrite (c.work j).read) (if j ∈ ports then .right else idleDir (c.work j).read) =
        if j ∈ ports then (c.work j).move .right else c.work j
      simp only [hj, ↓reduceIte]
      exact transitionTape_eq_self (hw j)
  · exact transitionTape_eq_self ho

theorem parked (ports : List (Fin w)) (work : Fin w → Tape) (hs : ∀ j, Parked (work j)) :
    ∀ j, Parked (advance ports work j) := by
  intro j
  by_cases hj : j ∈ ports
  · exact ⟨by simp only [advance, hj, ↓reduceIte, Tape.move]; have hh := (hs j).1; omega,
      by simpa only [advance, hj, ↓reduceIte, Tape.move] using (hs j).2⟩
  · simpa only [advance, hj, ↓reduceIte] using hs j

theorem hoareTime (ports : List (Fin w)) (before input emitted : List Bool)
    (R S : (Fin w → Tape) → Tape → Prop) (hR : ∀ work out, R work out → S (advance ports work) out) :
    (machine ports).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work out)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ S work out) 1 := by
  rintro inp work out ⟨hc, hs, hr⟩
  let d : Cfg w (machine ports).Q := ⟨true, inp, advance ports work, out⟩
  have hd := step ports ⟨false, inp, work, out⟩ rfl hc.input_read (fun j => (hc.works j).1) hc.output_read
  have hsafe := parked ports work hs
  exact ⟨d, 1, le_rfl, .step hd .zero, rfl,
    ⟨hc.cells, hc.head, (fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩), hc.tapePrefix, hc.zero⟩,
    hsafe, hR work out hr⟩

end JointThermoComplexity.Complexity.WorkHeadsAdvance

#print axioms JointThermoComplexity.Complexity.WorkHeadsAdvance.step
#print axioms JointThermoComplexity.Complexity.WorkHeadsAdvance.hoareTime
