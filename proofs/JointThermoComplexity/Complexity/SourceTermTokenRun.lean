module
public import proofs.JointThermoComplexity.Complexity.SourceTermBranch
public import proofs.JointThermoComplexity.Complexity.SourceTermTagRead

set_option autoImplicit false
@[expose] public section

/-! Total actual term-token scanning, with retained tags for pending-child control. -/

namespace JointThermoComplexity.Complexity.SourceTermTokenRun
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
open SourceIndexField SourceTermToken
variable {n : ℕ}

def TagState (ports : Fin 3 → Fin (n + 1)) (input : List Bool) (work : Fin (n + 1) → Tape) : Prop :=
  ∀ i, (work (ports i)).head = 1 ∧ (work (ports i)).read = Γ.ofBool (SourceBitRead.value (input.drop i.val))

theorem state_of_reads (ports : Fin 3 → Fin (n + 1)) (input : List Bool) (work : Fin (n + 2) → Tape)
    (hh : ∀ i, (work (ports i).castSucc).head = 1)
    (hr : SourceTagDispatch.Reads (List.ofFn (fun i => (ports i).castSucc)) (tagBits input) work) :
    TagState ports input (fun j => work j.castSucc) := by
  change (work (ports 0).castSucc).read = Γ.ofBool (SourceBitRead.value input) ∧
    (work (ports 1).castSucc).read = Γ.ofBool (SourceBitRead.value (input.drop 1)) ∧
    (work (ports 2).castSucc).read = Γ.ofBool (SourceBitRead.value (input.drop 2)) ∧ True at hr
  intro i
  refine ⟨hh i, ?_⟩
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i
  · simpa only [Fin.val_zero, List.drop_zero] using hr.1
  · exact hr.2.1
  · exact hr.2.2.1

theorem afterTag_hoareTime (ports : Fin 3 → Fin (n + 1)) (L : ℕ) (left right : Fin (n + 1))
    (sep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n))
    (arity : ℕ) (ha : arity.bits.length ≤ L) (before source emitted : List Bool) (hlen : source.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (FlagBranch.machine (NaturalScanBuffer.flag n) (dispatchMachine ports left right) (emitBitsTM [])).HoareTime
      (fun inp work out => Cursor (before ++ source.take 3) (source.drop 3) emitted inp work out ∧
        Ready L left right arity R work ∧
        SourceTagDispatch.Reads (List.ofFn (fun i => (ports i).castSucc)) (tagBits source) work ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (SourceTags.accepted source))
      (fun inp work out => Cursor (before ++ taken source) (rest source) emitted inp work out ∧
        Ready L left right arity R work ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (accepted arity source)) (32 * L + 54) := by
  cases hp : SourceTags.accepted source with
  | false =>
    let P : (Fin (n + 2) → Tape) → Prop := fun work => Ready L left right arity R work ∧
      (work (NaturalScanBuffer.flag n)).read = Γ.zero
    have hemit := FixedOutput.hoareTime (w := n + 2) [] (before ++ source.take 3) (source.drop 3) emitted P
    have hno : (emitBitsTM (n := n + 2) []).HoareTime
        (fun inp work out => Cursor (before ++ source.take 3) (source.drop 3) emitted inp work out ∧ P work)
        (fun inp work out => Cursor (before ++ source.take 3) (source.drop 3) emitted inp work out ∧ P work) 0 :=
      hemit.consequence (by rintro inp work out ⟨hc, hr, hf⟩; exact ⟨hc, hr.safe, hr, hf⟩)
        (by simpa only [List.append_nil] using fun _ _ _ h => ⟨h.1, h.2.2⟩) le_rfl
    have hb := FlagBranchRun.no_hoareTime (NaturalScanBuffer.flag n) (dispatchMachine ports left right) (emitBitsTM [])
      (before ++ source.take 3) (source.drop 3) emitted (before ++ source.take 3) (source.drop 3) emitted P P 0 hno
    exact hb.consequence (by
      rintro inp work out ⟨hc, hr, _hreads, hf⟩
      have hf' : (work (NaturalScanBuffer.flag n)).read = Γ.zero := by simpa only [hp, Γ.ofBool] using hf
      exact ⟨⟨hc, hr, hf'⟩, hf'⟩) (by
      rintro inp work out ⟨hc, hr, hf⟩
      exact ⟨by simpa only [taken, rest, hp, Bool.false_eq_true, ↓reduceIte, List.append_nil] using hc,
        hr, by simpa only [accepted, hp, Bool.false_and, Γ.ofBool] using hf⟩) (by omega)
  | true =>
    have hdrop : (source.drop 3).length ≤ L := by rw [List.length_drop]; omega
    have hdis := SourceTermBranch.dispatch_hoareTime ports (tagBits source) (by simp [tagBits]) L left right sep arity ha
      (before ++ source.take 3) (source.drop 3) emitted hdrop R hR
    have hb := FlagBranchRun.yes_hoareTime (NaturalScanBuffer.flag n) (dispatchMachine ports left right) (emitBitsTM [])
      (before ++ source.take 3) (source.drop 3) emitted
      ((before ++ source.take 3) ++ branchTaken (tagBits source) (source.drop 3))
      (branchRest (tagBits source) (source.drop 3)) emitted
      (fun work => Ready L left right arity R work ∧
        SourceTagDispatch.Reads (List.ofFn (fun i => (ports i).castSucc)) (tagBits source) work)
      (fun work => Ready L left right arity R work ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (branchStatus arity (tagBits source) (source.drop 3)))
      (32 * L + 52) hdis
    exact hb.consequence (by
      rintro inp work out ⟨hc, hr, hreads, hf⟩
      exact ⟨⟨hc, hr, hreads⟩, by simpa only [hp, Γ.ofBool] using hf⟩) (by
      rintro inp work out ⟨hc, hr, hf⟩
      exact ⟨by simpa only [taken, rest, hp, ↓reduceIte, List.append_assoc] using hc,
        hr, by simpa only [accepted, hp, Bool.true_and] using hf⟩) (by omega)

theorem hoareTime (ports : Fin 3 → Fin (n + 1)) (left right : Fin (n + 1))
    (hs : SourceTermTagRead.Separate ports left right)
    (sep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n))
    (L arity : ℕ) (ha : arity.bits.length ≤ L) (initial : Bool)
    (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ i, j ≠ ports i) → work' j = work j) → R work → R work') :
    (SourceTermToken.machine ports left right).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work ∧
        (∀ i, (work (ports i).castSucc).head = 1) ∧ (work (NaturalScanBuffer.flag n)).read = Γ.ofBool initial)
      (fun inp work out => Cursor (before ++ taken input) (rest input) emitted inp work out ∧
        Ready L left right arity R work ∧
        TagState ports input (fun j => work j.castSucc) ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (accepted arity input)) (32 * L + 61) := by
  let R1 : (Fin (n + 1) → Tape) → Prop := fun work => R work ∧ TagState ports input work
  have hR1 : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n → work' j = work j) →
      R1 work → R1 work' := by
    rintro work work' hw ⟨hr, ht⟩
    refine ⟨hR _ _ (fun j hl hr hf _ => hw j hl hr hf) hr, ?_⟩
    intro i
    rw [hw (ports i) (hs.left i) (hs.right i) (hs.flag i)]
    exact ht i
  have htag := SourceTermTagRead.hoareTime ports left right hs sep L arity initial before input emitted R hR
  have hbody := afterTag_hoareTime ports L left right sep arity ha before input emitted hlen R1 hR1
  have hfull := seqTM_hoareTime
    (SourceTagFlags.machine (fun i => (ports i).castSucc) (NaturalScanBuffer.flag n))
    (FlagBranch.machine (NaturalScanBuffer.flag n) (dispatchMachine ports left right) (emitBitsTM [])) htag (by
      rintro inp work out ⟨hc, hr, hh, hf, hv⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      have ht := state_of_reads ports input work hh hv
      exact ⟨hc, ⟨hr.safe, hr.markers, hr.encoded, hr.candidate, hr.arityBits, hr.arityZero, hr.flagHead, hr.frame, ht⟩, hv, hf⟩) hbody
  exact hfull.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hr, hf⟩
    exact ⟨hc, ⟨hr.safe, hr.markers, hr.encoded, hr.candidate, hr.arityBits, hr.arityZero, hr.flagHead, hr.frame.1⟩,
      hr.frame.2, hf⟩) (by omega)

end JointThermoComplexity.Complexity.SourceTermTokenRun

#print axioms JointThermoComplexity.Complexity.SourceTermTokenRun.afterTag_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceTermTokenRun.hoareTime
