module
public import proofs.JointThermoComplexity.Complexity.SourceIntegerField
public import proofs.JointThermoComplexity.Complexity.SourceIndexField
public import proofs.JointThermoComplexity.Complexity.SourceTagDispatch
public import proofs.JointThermoComplexity.Complexity.SourceTermHead

set_option autoImplicit false
@[expose] public section

/-! Total source-token control and its independent grammar criterion.
The closed machine is defined here; its composed all-input runtime is separate. -/

namespace JointThermoComplexity.Complexity.SourceTermToken
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
variable {w n : ℕ}

inductive Kind where
  | integer | variable | add | mul | neg | invalid
  deriving DecidableEq

def classify : List Bool → Kind
  | [false, false, false] => .integer
  | [false, false, true] => .variable
  | [false, true, false] => .add
  | [false, true, true] => .mul
  | [true, false, false] => .neg
  | _ => .invalid

def children : Kind → ℕ
  | .add | .mul => 2
  | .neg => 1
  | _ => 0

def tagBits (input : List Bool) : List Bool :=
  [SourceBitRead.value input, SourceBitRead.value (input.drop 1), SourceBitRead.value (input.drop 2)]

def branchTaken (bits input : List Bool) : List Bool := match classify bits with
  | .integer => IntegerMachineRun.copied input
  | .variable => PayloadControl.copied .empty input
  | _ => []

def branchRest (bits input : List Bool) : List Bool := match classify bits with
  | .integer => NumericCursor.integerRest input
  | .variable => NumericCursor.naturalRest input
  | _ => input

def branchStatus (arity : ℕ) (bits input : List Bool) : Bool := match classify bits with
  | .integer => NaturalMachineParser.integerAccepted input
  | .variable => SourceIndexField.status input arity
  | .add | .mul | .neg => true
  | .invalid => false

def taken (input : List Bool) : List Bool :=
  input.take 3 ++ if SourceTags.accepted input then branchTaken (tagBits input) (input.drop 3) else []

def rest (input : List Bool) : List Bool :=
  if SourceTags.accepted input then branchRest (tagBits input) (input.drop 3) else input.drop 3

def accepted (arity : ℕ) (input : List Bool) : Bool :=
  SourceTags.accepted input && branchStatus arity (tagBits input) (input.drop 3)

theorem branch_split (bits input : List Bool) : branchTaken bits input ++ branchRest bits input = input := by
  unfold branchTaken branchRest
  cases classify bits <;> simp only [List.nil_append]
  · exact NumericCursor.integer_split input
  · exact NumericCursor.natural_split input

theorem split (input : List Bool) : taken input ++ rest input = input := by
  unfold taken rest
  cases hp : SourceTags.accepted input with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]; exact List.take_append_drop 3 input
  | true => rw [ite_eq_left rfl, ite_eq_left rfl, List.append_assoc, branch_split]; exact List.take_append_drop 3 input

theorem taken_length (input : List Bool) : (taken input).length ≤ input.length := by
  have h := congrArg List.length (split input)
  rw [List.length_append] at h
  omega

theorem branch_status_iff (arity : ℕ) (a b c : Bool) (input : List Bool) :
    branchStatus arity [a, b, c] input = true ↔
      ∃ head suffix, SourceTermScan.parseHead arity (a :: b :: c :: input) = some (head, suffix) := by
  cases a <;> cases b <;> cases c
  · cases hp : BitCodec.parseInteger input with
    | none =>
      have hn : NaturalMachineParser.integerAccepted input ≠ true := by
        intro h
        obtain ⟨z, tail, he⟩ := (NaturalMachineParser.integerAccepted_iff input).mp h
        rw [hp] at he
        contradiction
      simp [branchStatus, classify, SourceTermScan.parseHead, hp, hn]
    | some pair =>
      obtain ⟨z, tail⟩ := pair
      have hy : NaturalMachineParser.integerAccepted input = true :=
        (NaturalMachineParser.integerAccepted_iff input).mpr ⟨z, tail, hp⟩
      simp [branchStatus, classify, SourceTermScan.parseHead, hp, hy]
  · cases hp : BitCodec.parseNatural input with
    | none => simp [branchStatus, classify, SourceIndexField.status, SourceTermScan.parseHead, hp]
    | some pair =>
      obtain ⟨index, tail⟩ := pair
      by_cases hi : index < arity <;>
        simp [branchStatus, classify, SourceIndexField.status, SourceTermScan.parseHead, hp, hi]
  all_goals simp [branchStatus, classify, SourceTermScan.parseHead]

theorem accepted_iff (arity : ℕ) (input : List Bool) : accepted arity input = true ↔
    ∃ head suffix, SourceTermScan.parseHead arity input = some (head, suffix) := by
  cases input with
  | nil => simp [accepted, SourceTags.accepted, SourceTermScan.parseHead]
  | cons a input =>
    cases input with
    | nil => simp [accepted, SourceTags.accepted, SourceTermScan.parseHead]
    | cons b input =>
      cases input with
      | nil => simp [accepted, SourceTags.accepted, SourceTermScan.parseHead]
      | cons c input =>
        have htag : SourceTags.accepted (a :: b :: c :: input) = true := by simp [SourceTags.accepted]
        simpa only [accepted, htag, Bool.true_and,
          tagBits, SourceBitRead.value, List.drop_succ_cons, List.drop_zero] using branch_status_iff arity a b c input

theorem taken_code {arity : ℕ} (head : SourceTermScan.Head arity) (suffix : List Bool) :
    taken (head.code ++ suffix) = head.code := by
  cases head <;> simp [taken, SourceTags.accepted, SourceTermScan.Head.code, tagBits, SourceBitRead.value,
    branchTaken, classify, NumericCursor.integer_copied_code, NumericCursor.natural_copied_code]

theorem rest_code {arity : ℕ} (head : SourceTermScan.Head arity) (suffix : List Bool) :
    rest (head.code ++ suffix) = suffix := by
  cases head <;> simp [rest, SourceTags.accepted, SourceTermScan.Head.code, tagBits, SourceBitRead.value,
    branchRest, classify, NumericCursor.integer_rest_code, NumericCursor.natural_rest_code]

theorem children_code {arity : ℕ} (head : SourceTermScan.Head arity) (suffix : List Bool) :
    children (classify (tagBits (head.code ++ suffix))) = head.children := by
  cases head <;> simp [SourceTermScan.Head.code, tagBits, SourceBitRead.value, classify, children,
    SourceTermScan.Head.children]

theorem accepted_code {arity : ℕ} (head : SourceTermScan.Head arity) (suffix : List Bool) :
    accepted arity (head.code ++ suffix) = true :=
  (accepted_iff _ _).mpr ⟨head, suffix, SourceTermScan.parseHead_code head suffix⟩

theorem sound (arity : ℕ) (input : List Bool) (h : accepted arity input = true) :
    ∃ head : SourceTermScan.Head arity, input = head.code ++ rest input ∧ taken input = head.code ∧
      children (classify (tagBits input)) = head.children := by
  obtain ⟨head, suffix, hp⟩ := (accepted_iff arity input).mp h
  have hi := SourceTermScan.parseHead_sound hp
  refine ⟨head, ?_, ?_, ?_⟩
  · rw [hi, rest_code]
  · rw [hi, taken_code]
  · rw [hi, children_code]

theorem success_consumes (arity : ℕ) (input : List Bool) (h : accepted arity input = true) :
    (rest input).length + 3 ≤ input.length := by
  obtain ⟨head, suffix, hp⟩ := (accepted_iff arity input).mp h
  have hr : rest input = suffix := by rw [SourceTermScan.parseHead_sound hp, rest_code]
  rw [hr]
  exact SourceTermScan.parseHead_consumes hp

def setStatus (flag : Fin w) (value : Bool) : TM w where
  Q := Bool
  qstart := false
  qhalt := true
  δ _ si sw so := (true, (fun j => if j = flag then Γw.ofBool value else readBackWrite (sw j)),
    readBackWrite so, idleDir si, fun j => idleDir (sw j), idleDir so)
  δ_right_of_start _ _ _ _ :=
    ⟨idleDir_right_of_start, fun _ hj => idleDir_right_of_start hj, idleDir_right_of_start⟩

theorem setStatus_step (flag : Fin w) (value : Bool) (c : Cfg w (setStatus flag value).Q)
    (hs : c.state = false) (hi : c.input.read ≠ Γ.start) (ho : c.output.read ≠ Γ.start)
    (hw : ∀ j, (c.work j).read ≠ Γ.start) :
    (setStatus flag value).step c = some ⟨true, c.input, ValidityAnd.writeFlag c.work flag value, c.output⟩ := by
  simp only [TM.step, setStatus, hs, Bool.false_eq_true, ↓reduceIte]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · exact transitionInput_eq_self hi
  · funext j
    change (c.work j).writeAndMove
      ((if j = flag then Γw.ofBool value else readBackWrite (c.work j).read).toΓ) (idleDir (c.work j).read) =
      ValidityAnd.writeFlag c.work flag value j
    by_cases hj : j = flag
    · subst j
      simp only [↓reduceIte, Γw.ofBool_toΓ, ValidityAnd.writeFlag, Function.update_self]
      rw [idleDir, ite_eq_right (hw flag)]
      rfl
    · simp only [ite_eq_right hj, ValidityAnd.writeFlag_other _ _ _ _ hj]
      exact transitionTape_eq_self (hw j)
  · exact transitionTape_eq_self ho

theorem setStatus_hoareTime (flag : Fin w) (value : Bool) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ flag → work' j = work j) → R work → R work') :
    (setStatus flag value).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work flag).head = 1 ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work flag).head = 1 ∧ (work flag).read = Γ.ofBool value ∧ R work) 1 := by
  rintro inp work out ⟨hc, hs, hf, hr⟩
  let c : Cfg w (setStatus flag value).Q := ⟨false, inp, work, out⟩
  let d : Cfg w (setStatus flag value).Q := ⟨true, inp, ValidityAnd.writeFlag work flag value, out⟩
  have hstep : (setStatus flag value).step c = some d :=
    setStatus_step flag value c rfl hc.input_read hc.output_read (fun j => (hc.works j).1)
  have hh : (d.work flag).head = 1 := by simpa only [d, ValidityAnd.writeFlag_head] using hf
  have hv : (d.work flag).read = Γ.ofBool value := ValidityAnd.writeFlag_read work flag value hf
  have hother : ∀ j, j ≠ flag → d.work j = work j := fun j hj => ValidityAnd.writeFlag_other work flag j value hj
  have hsafe : ∀ j, Parked (d.work j) := by
    intro j
    by_cases hj : j = flag
    · subst j
      exact ⟨by rw [hh], TapeSafety.work_step (flag) hstep (hs _).2⟩
    · rw [hother j hj]
      exact hs j
  exact ⟨d, 1, le_rfl, .step hstep .zero, rfl,
    ⟨hc.cells, hc.head, fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩, hc.tapePrefix, hc.zero⟩,
    hsafe, hh, hv, hR work d.work hother hr⟩

def branchMachine (left right : Fin (n + 1)) (bits : List Bool) : TM (n + 2) := match classify bits with
  | .integer => SourceIntegerField.machine n
  | .variable => SourceIndexField.machine left right
  | .add | .mul | .neg => setStatus (NaturalScanBuffer.flag n) true
  | .invalid => setStatus (NaturalScanBuffer.flag n) false

def dispatchMachine (ports : Fin 3 → Fin (n + 1)) (left right : Fin (n + 1)) : TM (n + 2) :=
  SourceTagDispatch.machine (List.ofFn (fun i => (ports i).castSucc)) (branchMachine left right)

def machine (ports : Fin 3 → Fin (n + 1)) (left right : Fin (n + 1)) : TM (n + 2) :=
  seqTM (SourceTagFlags.machine (fun i => (ports i).castSucc) (NaturalScanBuffer.flag n))
    (FlagBranch.machine (NaturalScanBuffer.flag n) (dispatchMachine ports left right) (emitBitsTM []))

end JointThermoComplexity.Complexity.SourceTermToken

#print axioms JointThermoComplexity.Complexity.SourceTermToken.split
#print axioms JointThermoComplexity.Complexity.SourceTermToken.accepted_iff
#print axioms JointThermoComplexity.Complexity.SourceTermToken.sound
#print axioms JointThermoComplexity.Complexity.SourceTermToken.success_consumes
#print axioms JointThermoComplexity.Complexity.SourceTermToken.setStatus_hoareTime
