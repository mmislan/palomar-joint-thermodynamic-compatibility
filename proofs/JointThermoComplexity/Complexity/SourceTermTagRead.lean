module
public import proofs.JointThermoComplexity.Complexity.SourceTermFields

set_option autoImplicit false
@[expose] public section

/-! Actual source tag loading preserves shared field buffers and arity registers. -/

namespace JointThermoComplexity.Complexity.SourceTermTagRead
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
open BinaryDifferenceCursor SourceIndexField SourceTermToken
variable {n : ℕ}

structure Separate (ports : Fin 3 → Fin (n + 1)) (left right : Fin (n + 1)) : Prop where
  injective : Function.Injective ports
  left : ∀ i, ports i ≠ left
  right : ∀ i, ports i ≠ right
  flag : ∀ i, ports i ≠ NaturalMachine.flagIndex n

theorem reads_of_values (ports : Fin 3 → Fin (n + 1)) (input : List Bool) (work : Fin (n + 2) → Tape)
    (h : ∀ i, (work (ports i).castSucc).read = Γ.ofBool (SourceBitRead.value (input.drop i.val))) :
    SourceTagDispatch.Reads (List.ofFn (fun i => (ports i).castSucc)) (tagBits input) work := by
  change (work (ports 0).castSucc).read = Γ.ofBool (SourceBitRead.value input) ∧
    (work (ports 1).castSucc).read = Γ.ofBool (SourceBitRead.value (input.drop 1)) ∧
    (work (ports 2).castSucc).read = Γ.ofBool (SourceBitRead.value (input.drop 2)) ∧ True
  exact ⟨by simpa only [Fin.val_zero, List.drop_zero] using h 0, h 1, h 2, trivial⟩

theorem hoareTime (ports : Fin 3 → Fin (n + 1)) (left right : Fin (n + 1))
    (hs : Separate ports left right) (sep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n))
    (L arity : ℕ) (initial : Bool) (before input emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ i, j ≠ ports i) → work' j = work j) → R work → R work') :
    (SourceTagFlags.machine (fun i => (ports i).castSucc) (NaturalScanBuffer.flag n)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work ∧
        (∀ i, (work (ports i).castSucc).head = 1) ∧ (work (NaturalScanBuffer.flag n)).read = Γ.ofBool initial)
      (fun inp work out => Cursor (before ++ input.take 3) (input.drop 3) emitted inp work out ∧
        Ready L left right arity R work ∧ (∀ i, (work (ports i).castSucc).head = 1) ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (SourceTags.accepted input) ∧
        SourceTagDispatch.Reads (List.ofFn (fun i => (ports i).castSucc)) (tagBits input) work) 6 := by
  let physical : Fin 3 → Fin (n + 2) := fun i => (ports i).castSucc
  have hinj : Function.Injective physical := by
    intro i j he
    apply hs.injective
    apply Fin.ext
    exact congrArg (fun k : Fin (n + 2) => k.val) he
  have hflag : ∀ i, physical i ≠ NaturalScanBuffer.flag n := by
    intro i he
    apply hs.flag i
    apply Fin.ext
    exact congrArg (fun k : Fin (n + 2) => k.val) he
  let R0 : (Fin (n + 2) → Tape) → Prop := fun work => Reusable L (work (NaturalScanBuffer.buffer n)) ∧
    SourceTermFields.Kept L left right arity R work
  have hR0 : ∀ work work', (∀ j, (∀ i, j ≠ physical i) → j ≠ NaturalScanBuffer.flag n → work' j = work j) →
      R0 work → R0 work' := by
    rintro work work' hw ⟨hb, hl, hr, hz, hframe⟩
    have hinner : ∀ j : Fin (n + 1), (∀ i, j ≠ ports i) → j ≠ NaturalMachine.flagIndex n →
        work' j.castSucc = work j.castSucc := by
      intro j hj hf
      apply hw
      · intro i he
        apply hj i
        apply Fin.ext
        exact congrArg (fun k : Fin (n + 2) => k.val) he
      · intro he
        apply hf
        apply Fin.ext
        exact congrArg (fun k : Fin (n + 2) => k.val) he
    have hbuf : work' (NaturalScanBuffer.buffer n) = work (NaturalScanBuffer.buffer n) := by
      apply hw
      · intro i he
        have hv := congrArg (fun k : Fin (n + 2) => k.val) he
        change n + 1 = (ports i).val at hv
        have := (ports i).isLt
        omega
      · exact NaturalScanBuffer.separate.symm
    have hl' := hinner left (fun i => (hs.left i).symm) sep.flagLeft.symm
    have hr' := hinner right (fun i => (hs.right i).symm) sep.flagRight.symm
    exact ⟨by simpa only [hbuf] using hb, by simpa only [hl'] using hl,
      by simpa only [hr'] using hr, by simpa only [hr'] using hz,
      hR _ _ (fun j _ _ hf hp => hinner j hp hf) hframe⟩
  have htag := SourceTagFlags.tag_hoareTime physical hinj (NaturalScanBuffer.flag n) hflag initial before input emitted R0 hR0
  rintro inp work out ⟨hc, hr, hheads, hf⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', hheads', hfh', hfv', hdata', hb', hl', hright', hz', hframe'⟩ :=
    htag inp work out ⟨hc, hr.safe, hheads, hr.flagHead, hf, hr.encoded, hr.candidate, hr.arityBits, hr.arityZero, hr.frame⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  exact ⟨d, t, ht, hd, hh, hc', ⟨hs', fun j => (hm.2.1 j).1, hb', hl', hright', hz', hfh', hframe'⟩,
    hheads', hfv', reads_of_values ports input d.work hdata'⟩

end JointThermoComplexity.Complexity.SourceTermTagRead

#print axioms JointThermoComplexity.Complexity.SourceTermTagRead.hoareTime
