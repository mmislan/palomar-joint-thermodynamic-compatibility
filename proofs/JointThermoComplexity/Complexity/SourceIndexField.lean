module
public import proofs.JointThermoComplexity.Complexity.SourceIndexReplay
public import proofs.JointThermoComplexity.Complexity.FlagBranchRun

set_option autoImplicit false
@[expose] public section

/-! A total binary source-variable field: reject malformed data before replaying its numeric value. -/

namespace JointThermoComplexity.Complexity.SourceIndexField
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
open BinaryDifferenceCursor BinaryDifferenceRuntime
variable {n : ℕ}

def status (input : List Bool) (arity : ℕ) : Bool :=
  match BitCodec.parseNatural input with
  | none => false
  | some (index, _) => decide (index < arity)

structure Ready (L : ℕ) (left right : Fin (n + 1)) (arity : ℕ)
    (R : (Fin (n + 1) → Tape) → Prop) (work : Fin (n + 2) → Tape) : Prop where
  safe : ∀ j, Parked (work j)
  markers : ∀ j, (work j).cells 0 = Γ.start
  encoded : Reusable L (work (NaturalScanBuffer.buffer n))
  candidate : Reusable L (work left.castSucc)
  arityBits : (work right.castSucc).HasBinaryString arity.bits
  arityZero : (work right.castSucc).cells 0 = Γ.start
  flagHead : (work (NaturalScanBuffer.flag n)).head = 1
  frame : R (fun j => work j.castSucc)

def branch (left right : Fin (n + 1)) : TM (n + 2) :=
  FlagBranch.machine (NaturalScanBuffer.flag n)
    (SourceIndexReplay.machine left right (NaturalMachine.flagIndex n)) (emitBitsTM [])

def machine (left right : Fin (n + 1)) : TM (n + 2) :=
  seqTM (NaturalScanBuffer.machine false n) (branch left right)

theorem branch_hoareTime (L : ℕ) (left right : Fin (n + 1))
    (sep : Separate left right (NaturalMachine.flagIndex n)) (arity : ℕ) (ha : arity.bits.length ≤ L)
    (before input emitted source : List Bool) (hlen : source.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (branch left right).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work ∧
        (work (NaturalScanBuffer.buffer n)).HasBinaryString (PayloadControl.copied .empty source) ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (NaturalMachineParser.accepted false source))
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (status source arity)) (18 * L + 27) := by
  cases hp : BitCodec.parseNatural source with
  | none =>
    let P : (Fin (n + 2) → Tape) → Prop := fun work => Ready L left right arity R work ∧
      (work (NaturalScanBuffer.flag n)).read = Γ.zero
    have hemit := FixedOutput.hoareTime (w := n + 2) [] before input emitted P
    have hno : (emitBitsTM (n := n + 2) []).HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ P work)
        (fun inp work out => Cursor before input emitted inp work out ∧ P work) 0 :=
      hemit.consequence (by rintro inp work out ⟨hc, hr, hf⟩; exact ⟨hc, hr.safe, hr, hf⟩)
        (by simpa only [List.append_nil] using fun _ _ _ h => ⟨h.1, h.2.2⟩) le_rfl
    have hbranch := FlagBranchRun.no_hoareTime (NaturalScanBuffer.flag n)
      (SourceIndexReplay.machine left right (NaturalMachine.flagIndex n)) (emitBitsTM [])
      before input emitted before input emitted P P 0 hno
    exact hbranch.consequence (by
      rintro inp work out ⟨hc, hr, _hb, hf⟩
      have hv : (work (NaturalScanBuffer.flag n)).read = Γ.zero := by
        simpa only [NaturalMachineParser.accepted, Bool.false_eq_true, ↓reduceIte, hp, Option.isSome_none, Γ.ofBool] using hf
      exact ⟨⟨hc, hr, hv⟩, hv⟩) (by
      rintro inp work out ⟨hc, hr, hf⟩
      exact ⟨hc, hr, by simpa only [status, hp, Γ.ofBool] using hf⟩) (by omega)
  | some pair =>
    obtain ⟨index, tail⟩ := pair
    have hc := NumericCursor.natural_parsed hp
    have hi : (BitCodec.naturalCode index).length ≤ L := by
      have he := congrArg List.length (NumericCursor.natural_split source)
      rw [List.length_append, hc.1] at he
      omega
    let P : (Fin (n + 2) → Tape) → Prop := fun work => Ready L left right arity R work ∧
      (work (NaturalScanBuffer.buffer n)).HasBinaryString (BitCodec.naturalCode index)
    let Q : (Fin (n + 2) → Tape) → Prop := fun work => Ready L left right arity R work ∧
      (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (decide (index < arity))
    have hrep := SourceIndexReplay.hoareTime L left right (NaturalMachine.flagIndex n) sep index arity hi ha
      before input emitted R hR
    have hyes : (SourceIndexReplay.machine left right (NaturalMachine.flagIndex n)).HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ P work)
        (fun inp work out => Cursor before input emitted inp work out ∧ Q work) (18 * L + 25) :=
      hrep.consequence (by
        rintro inp work out ⟨hc, hr, hb⟩
        exact ⟨hc, hr.safe, hr.markers, hb, hr.candidate, hr.arityBits, hr.arityZero, hr.flagHead, hr.frame⟩) (by
        rintro inp work out ⟨hc, hs, hz, hb, hh, hstart, hf, hu, hr⟩
        have henc : Reusable L (work (NaturalScanBuffer.buffer n)) :=
          ⟨BitCodec.naturalCode index, by omega, hb, hz _, hh.le⟩
        exact ⟨hc, ⟨hs, hz, henc, hu, hstart.rhs, hstart.rhsZero, hstart.flagHead, hr⟩, hf⟩) le_rfl
    have hbranch := FlagBranchRun.yes_hoareTime (NaturalScanBuffer.flag n)
      (SourceIndexReplay.machine left right (NaturalMachine.flagIndex n)) (emitBitsTM [])
      before input emitted before input emitted P Q (18 * L + 25) hyes
    exact hbranch.consequence (by
      rintro inp work out ⟨hc', hr, hb, hf⟩
      exact ⟨⟨hc', hr, by simpa only [hc.1] using hb⟩, by
        simpa only [NaturalMachineParser.accepted, Bool.false_eq_true, ↓reduceIte, hp, Option.isSome_some, Γ.ofBool] using hf⟩) (by
      rintro inp work out ⟨hc', hr, hf⟩
      exact ⟨hc', hr, by simpa only [status, hp] using hf⟩) (by omega)

theorem scan_hoareTime (L : ℕ) (left right : Fin (n + 1))
    (sep : Separate left right (NaturalMachine.flagIndex n)) (arity : ℕ)
    (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (NaturalScanBuffer.machine false n).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work)
      (fun inp work out => Cursor (before ++ PayloadControl.copied .empty input) (NumericCursor.naturalRest input)
          emitted inp work out ∧ Ready L left right arity R work ∧
        (work (NaturalScanBuffer.buffer n)).HasBinaryString (PayloadControl.copied .empty input) ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (NaturalMachineParser.accepted false input)) (14 * L + 18) := by
  let R0 : (Fin (n + 2) → Tape) → Prop := fun work => Reusable L (work left.castSucc) ∧
    (work right.castSucc).HasBinaryString arity.bits ∧ (work right.castSucc).cells 0 = Γ.start ∧
    R (fun j => work j.castSucc)
  have hR0 : ∀ work work', (∀ j, j ≠ NaturalScanBuffer.buffer n → j ≠ NaturalScanBuffer.flag n →
      work' j = work j) → R0 work → R0 work' := by
    rintro work work' hw ⟨hl, hr, hz, hframe⟩
    have hinner : ∀ j : Fin (n + 1), j ≠ NaturalMachine.flagIndex n → work' j.castSucc = work j.castSucc := by
      intro j hj
      apply hw
      · intro he
        have hv := congrArg Fin.val he
        simp only [NaturalScanBuffer.buffer, Fin.val_castSucc, Fin.val_last] at hv
        omega
      · intro he
        apply hj
        apply Fin.ext
        have hv := congrArg (fun i : Fin (n + 2) => i.val) he
        simpa only [NaturalScanBuffer.flag, Fin.val_castSucc] using hv
    have hl' := hinner left sep.flagLeft.symm
    have hr' := hinner right sep.flagRight.symm
    exact ⟨by simpa only [hl'] using hl, by simpa only [hr'] using hr, by simpa only [hr'] using hz,
      hR _ _ (fun j _ _ hj => hinner j hj) hframe⟩
  have hscan := NaturalScanBuffer.hoareTime false L before input emitted hlen R0 hR0
  rintro inp work out ⟨hc, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', hb', hz', hu', hf', hv', hl', hr', hrz', hframe'⟩ :=
    hscan inp work out ⟨hc, hr.safe, hr.encoded, hr.flagHead, hr.candidate, hr.arityBits, hr.arityZero, hr.frame⟩
  have hm := VirtualCursor.markers_reaches (NaturalScanBuffer.machine false n) hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  exact ⟨d, t, ht, hd, hh, hc', ⟨hs', fun j => (hm.2.1 j).1, hu', hl', hr', hrz', hf', hframe'⟩, hb', hv'⟩

theorem hoareTime (L : ℕ) (left right : Fin (n + 1))
    (sep : Separate left right (NaturalMachine.flagIndex n)) (arity : ℕ) (ha : arity.bits.length ≤ L)
    (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (machine left right).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work)
      (fun inp work out => Cursor (before ++ PayloadControl.copied .empty input) (NumericCursor.naturalRest input)
          emitted inp work out ∧ Ready L left right arity R work ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (status input arity)) (32 * L + 46) := by
  have hs := scan_hoareTime L left right sep arity before input emitted hlen R hR
  have hb := branch_hoareTime L left right sep arity ha (before ++ PayloadControl.copied .empty input)
    (NumericCursor.naturalRest input) emitted input hlen R hR
  have hfull := seqTM_hoareTime (NaturalScanBuffer.machine false n) (branch left right) hs (by
    rintro inp work out ⟨hc, hr, hb, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr, hb, hf⟩) hb
  exact hfull.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega)

theorem status_iff (input : List Bool) (arity : ℕ) :
    status input arity = true ↔ ∃ index tail, BitCodec.parseNatural input = some (index, tail) ∧ index < arity := by
  cases hp : BitCodec.parseNatural input with
  | none => simp [status, hp]
  | some pair => obtain ⟨index, tail⟩ := pair; simp [status, hp]

end JointThermoComplexity.Complexity.SourceIndexField

#print axioms JointThermoComplexity.Complexity.SourceIndexField.branch_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceIndexField.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceIndexField.status_iff
