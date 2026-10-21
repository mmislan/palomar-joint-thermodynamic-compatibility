module
public import proofs.JointThermoComplexity.Complexity.BinaryAddControl
public import proofs.JointThermoComplexity.Complexity.BinaryEmitMachine

set_option autoImplicit false
@[expose] public section

/-! A two-source finite Boolean-carry transducer. A source advances only when
its current cell contains a bit, so exhausted sources stay at their own ends. -/

namespace JointThermoComplexity.Complexity.BinaryAddMachine
open _root_.Complexity _root_.Complexity.TM
variable {w : ℕ}

inductive State where
  | scan : Bool → State
  | done
  deriving DecidableEq

instance : Fintype State where
  elems := {.done, .scan false, .scan true}
  complete q := by cases q with
    | scan b => cases b <;> simp
    | done => simp

def present : Γ → Bool
  | .zero | .one => true
  | _ => false

def asBool : Γ → Bool
  | .one => true
  | _ => false

def head : List Bool → Bool
  | [] => false
  | b :: _ => b

def direction (left right j : Fin w) (symbol : Γ) : Dir3 :=
  if decide (j = left ∨ j = right) && present symbol then .right else idleDir symbol

def readWork (left right : Fin w) (work : Fin w → Tape) : Fin w → Tape := fun j =>
  (work j).writeAndMove (readBackWrite (work j).read).toΓ (direction left right j (work j).read)

def outputAction (left right : Fin w) (q : State) (b : Bool) (si : Γ) (sw : Fin w → Γ) :
    State × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (q, fun j => readBackWrite (sw j), Γw.ofBool b, idleDir si,
    fun j => direction left right j (sw j), .right)

def action (left right : Fin w) (q : State) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    State × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  match q with
  | .scan carry =>
    if present (sw left) || present (sw right) then
      outputAction left right (.scan (BinaryAddControl.next carry (asBool (sw left)) (asBool (sw right))))
        (BinaryAddControl.digit carry (asBool (sw left)) (asBool (sw right))) si sw
    else if carry then outputAction left right .done true si sw
    else allReadBack .done si sw so
  | .done => allReadBack .done si sw so

def machine (left right : Fin w) : TM w where
  Q := State
  qstart := .scan false
  qhalt := .done
  δ := action left right
  δ_right_of_start q si sw so := by
    cases q with
    | scan carry =>
      cases carry <;> by_cases h : (present (sw left) || present (sw right)) = true <;>
        simp [action, h, outputAction, allReadBack, idleDir]
      all_goals intro j hj; simp [direction, hj, present, idleDir]
    | done => exact rightOfStart_allReadBack si sw so

theorem emit_step (left right : Fin w) (carry : Bool) (c : Cfg w State)
    (hs : c.state = .scan carry) (ha : (present (c.work left).read || present (c.work right).read) = true) :
    (machine left right).step c = some ⟨.scan (BinaryAddControl.next carry (asBool (c.work left).read) (asBool (c.work right).read)),
      transitionInput c.input, readWork left right c.work,
      c.output.writeAndMove (Γ.ofBool (BinaryAddControl.digit carry (asBool (c.work left).read) (asBool (c.work right).read))) .right⟩ := by
  cases hd : BinaryAddControl.digit carry (asBool (c.work left).read) (asBool (c.work right).read) <;>
    simp [TM.step, machine, action, outputAction, hs, ha, hd, transitionInput, Γw.ofBool, Γ.ofBool]
  all_goals rfl

theorem finish_false_step (left right : Fin w) (c : Cfg w State)
    (hs : c.state = .scan false) (hl : (c.work left).read = Γ.blank) (hr : (c.work right).read = Γ.blank) :
    (machine left right).step c = some ⟨.done, transitionInput c.input,
      (fun j => transitionTape (c.work j)), transitionTape c.output⟩ := by
  simp [TM.step, machine, action, hs, hl, hr, present, allReadBack, transitionInput, transitionTape]

theorem finish_true_step (left right : Fin w) (c : Cfg w State)
    (hs : c.state = .scan true) (hl : (c.work left).read = Γ.blank) (hr : (c.work right).read = Γ.blank) :
    (machine left right).step c = some ⟨.done, transitionInput c.input,
      readWork left right c.work, c.output.writeAndMove Γ.one .right⟩ := by
  simp [TM.step, machine, action, outputAction, hs, hl, hr, present, transitionInput, Γw.ofBool]
  rfl

theorem readWork_eq (left right j : Fin w) (work : Fin w → Tape) (hn : (work j).read ≠ Γ.start) :
    readWork left right work j = (work j).move (direction left right j (work j).read) :=
  writeAndMove_readBack (work j) hn _

theorem readWork_hit (left right j : Fin w) (work : Fin w → Tape)
    (hj : j = left ∨ j = right) (hn : (work j).read ≠ Γ.start) :
    readWork left right work j = if present (work j).read then (work j).move .right else work j := by
  rw [readWork_eq left right j work hn]
  cases hp : present (work j).read <;> simp [direction, hj, hp, idleDir, hn, Tape.move]

theorem readWork_other (left right j : Fin w) (work : Fin w → Tape)
    (hl : j ≠ left) (hr : j ≠ right) (hn : (work j).read ≠ Γ.start) :
    readWork left right work j = work j := by
  rw [readWork_eq left right j work hn]
  simp [direction, hl, hr, idleDir, hn, Tape.move]

theorem source_read (before remaining : List Bool) (t : Tape)
    (hc : t.HasBinaryContent (before ++ remaining)) (hh : t.head = before.length + 1) :
    present t.read = decide (remaining ≠ []) ∧ asBool t.read = head remaining ∧ t.read ≠ Γ.start := by
  cases remaining with
  | nil =>
    have hr : t.read = Γ.blank := BinaryTape.read_end before (by simpa only [List.append_nil] using hc) hh
    simp [hr, present, asBool, head]
  | cons b rest =>
    have hr := BinaryTape.read_cons before rest b hc hh
    cases b <;> simp [hr, present, asBool, head, Γ.ofBool]

theorem source_advance (left right j : Fin w) (work : Fin w → Tape) (hj : j = left ∨ j = right)
    (before remaining : List Bool) (hc : (work j).HasBinaryContent (before ++ remaining))
    (hh : (work j).head = before.length + 1) :
    (readWork left right work j).HasBinaryContent ((before ++ remaining.take 1) ++ remaining.drop 1) ∧
      (readWork left right work j).head = (before ++ remaining.take 1).length + 1 ∧
      (readWork left right work j).cells = (work j).cells := by
  have hn := (source_read before remaining (work j) hc hh).2.2
  rw [readWork_hit left right j work hj hn]
  cases remaining with
  | nil =>
    have hr := source_read before [] (work j) hc hh
    have hp : present (work j).read = false := by simpa using hr.1
    simpa only [hp, Bool.false_eq_true, ↓reduceIte, List.take_nil, List.drop_nil,
      List.append_nil] using And.intro hc (And.intro hh (show (work j).cells = (work j).cells from rfl))
  | cons b rest =>
    have hr := source_read before (b :: rest) (work j) hc hh
    have hp : present (work j).read = true := by simpa using hr.1
    simp only [hp, ↓reduceIte,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
    exact ⟨by simpa only [List.append_assoc, List.singleton_append] using hc.move .right,
      by simp [Tape.move, hh, Nat.add_assoc], rfl⟩

theorem add_step (carry : Bool) (left right : List Bool) (hn : left ≠ [] ∨ right ≠ []) :
    BinaryAddControl.add carry left right =
      BinaryAddControl.digit carry (head left) (head right) ::
        BinaryAddControl.add (BinaryAddControl.next carry (head left) (head right)) (left.drop 1) (right.drop 1) := by
  cases left with
  | nil => cases right with
    | nil => simp at hn
    | cons b rest => rw [BinaryAddControl.add]; rfl
  | cons a rest => cases right with
    | nil => rw [BinaryAddControl.add]; rfl
    | cons b tail => rw [BinaryAddControl.add]; rfl

end JointThermoComplexity.Complexity.BinaryAddMachine

#print axioms JointThermoComplexity.Complexity.BinaryAddMachine.machine
#print axioms JointThermoComplexity.Complexity.BinaryAddMachine.emit_step
#print axioms JointThermoComplexity.Complexity.BinaryAddMachine.source_advance
