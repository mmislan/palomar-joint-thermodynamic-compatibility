module
public import proofs.JointThermoComplexity.Complexity.SourcePendingFrame

set_option autoImplicit false
@[expose] public section

/-! One actual total scanner step consumes a token and updates its positive pending count only on acceptance. -/

namespace JointThermoComplexity.Complexity.SourceTermStep
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceIndexField SourceTermToken SourceTermTokenRun
variable {n : ℕ}

def nextPending (arity v : ℕ) (input : List Bool) : ℕ :=
  if accepted arity input then v + children (classify (tagBits input)) else v + 1

def updateMachine (ports : Fin 3 → Fin (n + 1)) (pending : Fin (n + 1)) : TM (n + 2) :=
  FlagBranch.machine (NaturalScanBuffer.flag n)
    (SourcePendingUpdate.machine (fun i => (ports i).castSucc) pending.castSucc) (emitBitsTM [])

def machine (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1)) : TM (n + 2) :=
  seqTM (SourceTermToken.machine ports left right) (updateMachine ports pending)

theorem update_hoareTime (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1))
    (sep : SourcePendingFrame.Separate ports pending left right) (L arity v : ℕ)
    (source before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ pending → work' j = work j) → R work → R work') :
    (updateMachine ports pending).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work ∧
        IsReg (v + 1) (work pending.castSucc) ∧ TagState ports source (fun j => work j.castSucc) ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (accepted arity source))
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work ∧
        IsReg (nextPending arity v source) (work pending.castSucc) ∧ TagState ports source (fun j => work j.castSucc) ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (accepted arity source)) (2 * v + 20) := by
  cases ha : accepted arity source with
  | false =>
    let P : (Fin (n + 2) → Tape) → Prop := fun work => Ready L left right arity R work ∧
      IsReg (v + 1) (work pending.castSucc) ∧ TagState ports source (fun j => work j.castSucc) ∧
      (work (NaturalScanBuffer.flag n)).read = Γ.zero
    have hem := FixedOutput.hoareTime (w := n + 2) [] before input emitted P
    have hno : (emitBitsTM (n := n + 2) []).HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ P work)
        (fun inp work out => Cursor before input emitted inp work out ∧ P work) 0 :=
      hem.consequence (by rintro inp work out ⟨hc, hr, hp⟩; exact ⟨hc, hr.safe, hr, hp⟩)
        (by simpa only [List.append_nil] using fun _ _ _ h => ⟨h.1, h.2.2⟩) le_rfl
    have hb := FlagBranchRun.no_hoareTime (NaturalScanBuffer.flag n)
      (SourcePendingUpdate.machine (fun i => (ports i).castSucc) pending.castSucc) (emitBitsTM [])
      before input emitted before input emitted P P 0 hno
    exact hb.consequence (by
      rintro inp work out ⟨hc, hr, hp, ht, hf⟩
      have hf' : (work (NaturalScanBuffer.flag n)).read = Γ.zero := by simpa only [ha, Γ.ofBool] using hf
      exact ⟨⟨hc, hr, hp, ht, hf'⟩, hf'⟩) (by
      rintro inp work out ⟨hc, hr, hp, ht, hf⟩
      exact ⟨hc, hr, by simpa only [nextPending, ha, Bool.false_eq_true, ↓reduceIte] using hp,
        ht, by simpa only [ha, Γ.ofBool] using hf⟩) (by omega)
  | true =>
    let P : (Fin (n + 2) → Tape) → Prop := fun work => Ready L left right arity R work ∧
      IsReg (v + 1) (work pending.castSucc) ∧ TagState ports source (fun j => work j.castSucc) ∧
      (work (NaturalScanBuffer.flag n)).read = Γ.one
    let Q : (Fin (n + 2) → Tape) → Prop := fun work => Ready L left right arity R work ∧
      IsReg (v + children (classify (tagBits source))) (work pending.castSucc) ∧
      TagState ports source (fun j => work j.castSucc) ∧ (work (NaturalScanBuffer.flag n)).read = Γ.one
    have hyes := SourcePendingFrame.hoareTime ports pending left right sep L arity v true source before input emitted R hR
    have hb := FlagBranchRun.yes_hoareTime (NaturalScanBuffer.flag n)
      (SourcePendingUpdate.machine (fun i => (ports i).castSucc) pending.castSucc) (emitBitsTM [])
      before input emitted before input emitted P Q (2 * v + 18) hyes
    exact hb.consequence (by
      rintro inp work out ⟨hc, hr, hp, ht, hf⟩
      have hf' : (work (NaturalScanBuffer.flag n)).read = Γ.one := by simpa only [ha, Γ.ofBool] using hf
      exact ⟨⟨hc, hr, hp, ht, hf'⟩, hf'⟩) (by
      rintro inp work out ⟨hc, hr, hp, ht, hf⟩
      exact ⟨hc, hr, by simpa only [nextPending, ha, ↓reduceIte] using hp,
        ht, by simpa only [ha, Γ.ofBool] using hf⟩) (by omega)

theorem hoareTime (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1))
    (hs : SourceTermTagRead.Separate ports left right)
    (sep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n))
    (hp : SourcePendingFrame.Separate ports pending left right) (L arity v : ℕ) (ha : arity.bits.length ≤ L)
    (initial : Bool) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ i, j ≠ ports i) → j ≠ pending → work' j = work j) → R work → R work') :
    (machine ports pending left right).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work ∧
        IsReg (v + 1) (work pending.castSucc) ∧ (∀ i, (work (ports i).castSucc).head = 1) ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool initial)
      (fun inp work out => Cursor (before ++ taken input) (rest input) emitted inp work out ∧
        Ready L left right arity R work ∧ IsReg (nextPending arity v input) (work pending.castSucc) ∧
        TagState ports input (fun j => work j.castSucc) ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool (accepted arity input)) (32 * L + 2 * v + 82) := by
  let RT : (Fin (n + 1) → Tape) → Prop := fun work => IsReg (v + 1) (work pending) ∧ R work
  have hRT : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ i, j ≠ ports i) → work' j = work j) → RT work → RT work' := by
    rintro work work' hw ⟨hv, hr⟩
    exact ⟨by simpa only [hw pending hp.left hp.right hp.flag hp.tags] using hv,
      hR _ _ (fun j hl hr hf ht _ => hw j hl hr hf ht) hr⟩
  have htoken := SourceTermTokenRun.hoareTime ports left right hs sep L arity ha initial before input emitted hlen RT hRT
  have hupdate := update_hoareTime ports pending left right hp L arity v input
    (before ++ taken input) (rest input) emitted R
    (fun work work' hw => hR work work' (fun j _ _ _ _ hj => hw j hj))
  have hfull := seqTM_hoareTime (SourceTermToken.machine ports left right) (updateMachine ports pending) htoken (by
    rintro inp work out ⟨hc, hr, ht, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, ⟨hr.safe, hr.markers, hr.encoded, hr.candidate, hr.arityBits, hr.arityZero, hr.flagHead, hr.frame.2⟩,
      hr.frame.1, ht, hf⟩) hupdate
  exact hfull.consequence (by
    rintro inp work out ⟨hc, hr, hv, hh, hf⟩
    exact ⟨hc, ⟨hr.safe, hr.markers, hr.encoded, hr.candidate, hr.arityBits, hr.arityZero, hr.flagHead, hv, hr.frame⟩, hh, hf⟩)
    (fun _ _ _ h => h) (by omega)

end JointThermoComplexity.Complexity.SourceTermStep

#print axioms JointThermoComplexity.Complexity.SourceTermStep.update_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceTermStep.hoareTime
