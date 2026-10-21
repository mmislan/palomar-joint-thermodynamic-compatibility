module
public import proofs.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

set_option autoImplicit false
@[expose] public section

/-!
# Sticky parser validity

One actual TM step combines a retained validity bit with the latest field's
status. A later valid field cannot erase an earlier invalid status. No input,
output or other work tape changes at the combination boundary.
-/

namespace JointThermoComplexity.Complexity.ValidityAnd
open _root_.Complexity
open _root_.Complexity.TM

variable {n : ℕ}

def both : Γ → Γ → Bool
  | .one, .one => true
  | _, _ => false

theorem both_ofBool (a b : Bool) : both (Γ.ofBool a) (Γ.ofBool b) = (a && b) := by
  cases a <;> cases b <;> rfl

def machine (dst src : Fin n) : TM n where
  Q := Bool
  qstart := false
  qhalt := true
  δ _ si sw so :=
    (true, fun i => if i = dst then Γw.ofBool (both (sw dst) (sw src)) else readBackWrite (sw i),
      readBackWrite so, idleDir si, fun i => idleDir (sw i), idleDir so)
  δ_right_of_start _ _si _sw _so :=
    ⟨idleDir_right_of_start, fun _ h => idleDir_right_of_start h, idleDir_right_of_start⟩

def writeFlag (work : Fin n → Tape) (dst : Fin n) (b : Bool) : Fin n → Tape :=
  Function.update work dst ((work dst).write (Γ.ofBool b))

theorem writeFlag_other (work : Fin n → Tape) (dst i : Fin n) (b : Bool) (h : i ≠ dst) :
    writeFlag work dst b i = work i := by rw [writeFlag, Function.update_of_ne h]

theorem writeFlag_head (work : Fin n → Tape) (dst : Fin n) (b : Bool) :
    (writeFlag work dst b dst).head = (work dst).head := by
  simp [writeFlag, Tape.write_head]

theorem writeFlag_read (work : Fin n → Tape) (dst : Fin n) (b : Bool)
    (h : (work dst).head = 1) : (writeFlag work dst b dst).read = Γ.ofBool b := by
  simp [writeFlag, Tape.read, Tape.write, h]

theorem step (dst src : Fin n) (a b : Bool) (c : Cfg n Bool)
    (hs : c.state = false) (hi : c.input.read ≠ Γ.start) (ho : c.output.read ≠ Γ.start)
    (hw : ∀ i, (c.work i).read ≠ Γ.start)
    (ha : (c.work dst).read = Γ.ofBool a) (hb : (c.work src).read = Γ.ofBool b) :
    (machine dst src).step c = some {
      state := true, input := c.input, work := writeFlag c.work dst (a && b), output := c.output } := by
  have hboth : both (c.work dst).read (c.work src).read = (a && b) := by
    rw [ha, hb, both_ofBool]
  simp only [TM.step, hs, machine, Bool.false_eq_true, ↓reduceIte, hboth]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · exact transitionInput_eq_self hi
  · funext i
    change (c.work i).writeAndMove
      (if i = dst then Γw.ofBool (a && b) else readBackWrite (c.work i).read).toΓ
      (idleDir (c.work i).read) = Function.update c.work dst ((c.work dst).write (Γ.ofBool (a && b))) i
    by_cases hid : i = dst
    · subst i
      rw [Function.update_self]
      simp only [↓reduceIte, Γw.ofBool_toΓ, idleDir, hw dst, ↓reduceIte, Tape.writeAndMove, Tape.move]
    · rw [Function.update_of_ne hid]
      simp only [ite_eq_right hid]
      exact transitionTape_eq_self (hw i)
  · exact transitionTape_eq_self ho

theorem run (dst src : Fin n) (a b : Bool) (c : Cfg n Bool)
    (hs : c.state = false) (hi : c.input.read ≠ Γ.start) (ho : c.output.read ≠ Γ.start)
    (hw : ∀ i, (c.work i).read ≠ Γ.start) (hh : (c.work dst).head = 1)
    (ha : (c.work dst).read = Γ.ofBool a) (hb : (c.work src).read = Γ.ofBool b) :
    ∃ d, (machine dst src).reachesIn 1 c d ∧ (machine dst src).halted d ∧
      d.input = c.input ∧ d.output = c.output ∧
      (∀ i, i ≠ dst → d.work i = c.work i) ∧ (d.work dst).head = 1 ∧
      (d.work dst).read = Γ.ofBool (a && b) := by
  refine ⟨⟨true, c.input, writeFlag c.work dst (a && b), c.output⟩,
    .step (step dst src a b c hs hi ho hw ha hb) .zero, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro i h
    exact writeFlag_other c.work dst i (a && b) h
  · exact (writeFlag_head c.work dst (a && b)).trans hh
  · exact writeFlag_read c.work dst (a && b) hh

theorem fold_iff (statuses : List Bool) (initial : Bool) :
    statuses.foldl (fun a b => a && b) initial = true ↔ initial = true ∧ ∀ b ∈ statuses, b = true := by
  induction statuses generalizing initial with
  | nil => simp
  | cons b rest ih => simp [List.foldl, ih, Bool.and_eq_true, and_assoc]

end JointThermoComplexity.Complexity.ValidityAnd

#print axioms JointThermoComplexity.Complexity.ValidityAnd.run
#print axioms JointThermoComplexity.Complexity.ValidityAnd.fold_iff
