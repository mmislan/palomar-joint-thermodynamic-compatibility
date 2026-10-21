module
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceValue
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! A binary-TM borrow scan compares read-only operand buffers or emits padded difference digits. -/

namespace JointThermoComplexity.Complexity.BinaryDifferenceMachine
open _root_.Complexity
open _root_.Complexity.TM
open BinaryBorrow

variable {w : ℕ}

def readBit (g : Γ) : Bool := decide (g = Γ.one)

def symbol : Option Bool → Γ
  | none => .blank
  | some b => Γ.ofBool b

theorem symbol_blank (b : Option Bool) : symbol b = Γ.blank ↔ b = none := by
  cases b with
  | none => simp [symbol]
  | some b => simp [symbol, Γ.ofBool_ne_blank]

theorem read_symbol (b : Option Bool) : readBit (symbol b) = b.getD false := by
  cases b with
  | none => rfl
  | some b => cases b <;> rfl

def direction (left right : Fin w) (sw : Fin w → Γ) (j : Fin w) : Dir3 :=
  if j = left ∨ j = right then if sw j = Γ.blank then .stay else .right else idleDir (sw j)

theorem direction_right_of_start (left right : Fin w) (sw : Fin w → Γ) (j : Fin w) (h : sw j = Γ.start) :
    direction left right sw j = .right := by simp [direction, h, idleDir]

def dataAction (left right : Fin w) (emit carry : Bool) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Option Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (some (borrow (readBit (sw left)) (readBit (sw right)) carry), (fun j => readBackWrite (sw j)),
    (if emit then Γw.ofBool (digit (readBit (sw left)) (readBit (sw right)) carry) else readBackWrite so),
    idleDir si, direction left right sw, if emit then .right else idleDir so)

def finishAction (flag : Fin w) (emit carry : Bool) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Option Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (none, (fun j => if j = flag ∧ emit = false then Γw.ofBool carry else readBackWrite (sw j)),
    readBackWrite so, idleDir si, (fun j => idleDir (sw j)), idleDir so)

def action (left right flag : Fin w) (emit : Bool) (q : Option Bool) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Option Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  match q with
  | none => allReadBack none si sw so
  | some carry => if sw left = Γ.blank ∧ sw right = Γ.blank then finishAction flag emit carry si sw so
      else dataAction left right emit carry si sw so

def machine (left right flag : Fin w) (emit : Bool) : TM w where
  Q := Option Bool
  qstart := some false
  qhalt := none
  δ := action left right flag emit
  δ_right_of_start q si sw so := by
    cases q with
    | none => exact rightOfStart_allReadBack si sw so
    | some carry =>
      by_cases he : sw left = Γ.blank ∧ sw right = Γ.blank
      · simp only [action, he, finishAction]
        exact ⟨idleDir_right_of_start, (fun _ hj => idleDir_right_of_start hj), idleDir_right_of_start⟩
      · simp only [action, he, ↓reduceIte, dataAction]
        refine ⟨idleDir_right_of_start, (fun j hj => direction_right_of_start left right sw j hj), ?_⟩
        cases emit
        · exact idleDir_right_of_start
        · exact fun _ => rfl

def dataWork (left right : Fin w) (work : Fin w → Tape) : Fin w → Tape :=
  fun j => (work j).writeAndMove (readBackWrite (work j).read) (direction left right (fun k => (work k).read) j)

def finishWork (flag : Fin w) (emit carry : Bool) (work : Fin w → Tape) : Fin w → Tape :=
  fun j => (work j).writeAndMove (if j = flag ∧ emit = false then Γw.ofBool carry else readBackWrite (work j).read)
    (idleDir (work j).read)

end JointThermoComplexity.Complexity.BinaryDifferenceMachine

#print axioms JointThermoComplexity.Complexity.BinaryDifferenceMachine.direction_right_of_start
