module
public import proofs.JointThermoComplexity.Complexity.ReadBitFlagMachine
public import proofs.JointThermoComplexity.Complexity.BooleanMachine
public import proofs.JointThermoComplexity.Complexity.ValidityAnd

set_option autoImplicit false
@[expose] public section

/-! One actual transition reads an available source bit into a data flag and
sets a separate presence flag. End of input stays in place and reports false. -/

namespace JointThermoComplexity.Complexity.SourceBitReadMachine
open _root_.Complexity _root_.Complexity.TM
variable {w : ℕ}

def changedWork (work : Fin w → Tape) (data flag : Fin w) (bit good : Bool) : Fin w → Tape :=
  ValidityAnd.writeFlag (ValidityAnd.writeFlag work data bit) flag good

theorem changed_data (work : Fin w → Tape) (data flag : Fin w) (hne : data ≠ flag) (bit good : Bool) :
    changedWork work data flag bit good data = (work data).write (Γ.ofBool bit) := by
  simp only [changedWork, ValidityAnd.writeFlag, Function.update_of_ne hne, Function.update_self]

theorem changed_flag (work : Fin w → Tape) (data flag : Fin w) (hne : data ≠ flag) (bit good : Bool) :
    changedWork work data flag bit good flag = (work flag).write (Γ.ofBool good) := by
  simp only [changedWork, ValidityAnd.writeFlag, Function.update_self, Function.update_of_ne hne.symm]

theorem changed_other (work : Fin w → Tape) (data flag j : Fin w) (hd : j ≠ data) (hf : j ≠ flag) (bit good : Bool) :
    changedWork work data flag bit good j = work j := by
  simp only [changedWork, ValidityAnd.writeFlag, Function.update_of_ne hf, Function.update_of_ne hd]

def action (data flag : Fin w) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (true, (fun j => if j = flag then Γw.ofBool (BooleanMachine.isBit si)
    else if j = data then ReadBitFlagMachine.asWrite si else readBackWrite (sw j)), readBackWrite so,
    (if BooleanMachine.isBit si then .right else idleDir si), (fun j => idleDir (sw j)), idleDir so)

def machine (data flag : Fin w) : TM w where
  Q := Bool
  qstart := false
  qhalt := true
  δ _ := action data flag
  δ_right_of_start _ _ _ _ :=
    ⟨by intro h; rw [h]; rfl, fun _ hj => idleDir_right_of_start hj, idleDir_right_of_start⟩

theorem step (data flag : Fin w) (hne : data ≠ flag) (bit good : Bool) (c : Cfg w (machine data flag).Q)
    (hs : c.state = false) (hi : c.input.read ≠ Γ.start) (ho : c.output.read ≠ Γ.start)
    (hw : ∀ j, (c.work j).read ≠ Γ.start)
    (hg : BooleanMachine.isBit c.input.read = good)
    (hb : (ReadBitFlagMachine.asWrite c.input.read).toΓ = Γ.ofBool bit) :
    (machine data flag).step c = some ⟨true, c.input.move (if good then .right else .stay),
      changedWork c.work data flag bit good, c.output⟩ := by
  have hd : (machine data flag).δ c.state c.input.read (fun j => (c.work j).read) c.output.read =
      action data flag c.input.read (fun j => (c.work j).read) c.output.read := rfl
  rw [TM.step, ite_eq_right (by simp [machine, hs]), hd]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · change c.input.move (if BooleanMachine.isBit c.input.read then .right else idleDir c.input.read) =
      c.input.move (if good then .right else .stay)
    rw [hg]
    cases good with
    | false => rw [idleDir, ite_eq_right hi]
    | true => rfl
  · funext j
    change (c.work j).writeAndMove
      ((if j = flag then Γw.ofBool (BooleanMachine.isBit c.input.read)
        else if j = data then ReadBitFlagMachine.asWrite c.input.read else readBackWrite (c.work j).read).toΓ)
      (idleDir (c.work j).read) = changedWork c.work data flag bit good j
    rw [hg]
    by_cases hjf : j = flag
    · subst j
      rw [changed_flag c.work data flag hne bit good]
      simp only [↓reduceIte, Γw.ofBool_toΓ]
      rw [idleDir, ite_eq_right (hw flag)]
      rfl
    · by_cases hjd : j = data
      · subst j
        rw [changed_data c.work data flag hne bit good]
        simp only [ite_eq_right hne, ↓reduceIte]
        rw [hb, idleDir, ite_eq_right (hw data)]
        rfl
      · rw [changed_other c.work data flag j hjd hjf bit good]
        simp only [ite_eq_right hjf, ite_eq_right hjd]
        exact transitionTape_eq_self (hw j)
  · exact transitionTape_eq_self ho

end JointThermoComplexity.Complexity.SourceBitReadMachine

#print axioms JointThermoComplexity.Complexity.SourceBitReadMachine.step
