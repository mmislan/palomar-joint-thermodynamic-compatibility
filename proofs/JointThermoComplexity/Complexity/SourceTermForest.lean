module
public import proofs.JointThermoComplexity.Complexity.SourceTermFinish

set_option autoImplicit false
@[expose] public section

/-! An actual bounded forest parser returns one status flag with exact independent syntax semantics. -/

namespace JointThermoComplexity.Complexity.SourceTermForest
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceIndexField SourceTermLoopState
open SourceTermLoopBody (Inv)
variable {n : ℕ}

def finalState (arity count : ℕ) (s : State) : State := SourceTermFinish.finishState (run arity count s)

def machine (ports : Fin 3 → Fin (n + 1)) (fuel pending left right : Fin (n + 1)) : TM (n + 2) :=
  seqTM (SourceTermLoop.machine ports fuel pending left right) (SourceTermFinish.machine pending)

def timeBound (L pending count : ℕ) : ℕ := SourceTermLoop.timeBound L pending count + 3

theorem hoareTime (ports : Fin 3 → Fin (n + 1)) (fuel pending left right : Fin (n + 1))
    (hs : SourceTermTagRead.Separate ports left right)
    (sep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n))
    (hp : SourcePendingFrame.Separate ports pending left right)
    (hfu : SourcePendingFrame.Separate ports fuel left right) (hfp : fuel ≠ pending)
    (L arity count : ℕ) (ha : arity.bits.length ≤ L) (emitted : List Bool)
    (R : (Fin (n + 1) → Tape) → Prop) (s : State) (hlen : s.input.length ≤ L)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ k, j ≠ ports k) → j ≠ pending → j ≠ fuel → work' j = work j) → R work → R work') :
    (machine ports fuel pending left right).HoareTime
      (fun inp work out => Inv ports pending left right L arity emitted R s inp work out ∧ IsReg count (work fuel.castSucc))
      (fun inp work out => Inv ports pending left right L arity emitted R (finalState arity count s) inp work out ∧
        IsReg count (work fuel.castSucc)) (timeBound L s.pending count) := by
  let RF : (Fin (n + 1) → Tape) → Prop := fun work => IsReg count (work fuel) ∧ R work
  have hRF : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ k, j ≠ ports k) → j ≠ pending → work' j = work j) → RF work → RF work' := by
    rintro work work' hw ⟨hf, hr⟩
    exact ⟨by simpa only [hw fuel hfu.left hfu.right hfu.flag hfu.tags hfp] using hf,
      hR _ _ (fun j hl hr hf ht hp _ => hw j hl hr hf ht hp) hr⟩
  have hloop := SourceTermLoop.hoareTime ports fuel pending left right hs sep hp hfu hfp L arity count ha emitted R s hlen hR
  have hfinish := SourceTermFinish.hoareTime ports pending left right hs sep hp L arity emitted RF (run arity count s) hRF
  have hfull := seqTM_hoareTime (SourceTermLoop.machine ports fuel pending left right) (SourceTermFinish.machine pending) hloop (by
    rintro inp work out ⟨⟨hc, hr, hv, hh, hf⟩, hFuel⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, ⟨hr.safe, hr.markers, hr.encoded, hr.candidate, hr.arityBits, hr.arityZero, hr.flagHead, hFuel, hr.frame⟩,
      hv, hh, hf⟩) hfinish
  exact hfull.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hr, hv, hh, hf⟩
    exact ⟨⟨hc, ⟨hr.safe, hr.markers, hr.encoded, hr.candidate, hr.arityBits, hr.arityZero, hr.flagHead, hr.frame.2⟩,
      hv, hh, hf⟩, hr.frame.1⟩) (by unfold timeBound; omega)

theorem quadratic_timeBound (L pending : ℕ) (hp : pending ≤ L) :
    timeBound L pending L ≤ 36 * L ^ 2 + 87 * L + 5 := by
  have h := SourceTermLoop.quadratic_timeBound L pending hp
  unfold timeBound
  omega

theorem status_criterion (arity count pending : ℕ) (before input : List Bool) :
    (finalState arity count ⟨before, input, pending, true⟩).valid = true ↔
      ∃ ts : List (RealSyntax.Term arity), ts.length = pending ∧ SourceTermScan.forestNodes ts ≤ count ∧
        input = SourceTermScan.forestCode ts ++ (finalState arity count ⟨before, input, pending, true⟩).input := by
  let sf := run arity count ⟨before, input, pending, true⟩
  have he : (sf.valid && decide (sf.pending = 0)) = true ↔ outcome sf = some sf.input := by
    cases hb : sf.valid && decide (sf.pending = 0) <;> simp [outcome, hb]
  change (sf.valid && decide (sf.pending = 0)) = true ↔ _
  rw [he]
  exact SourceTermLoop.source_forest_criterion arity count pending before input sf.input

theorem code_result (arity count : ℕ) (ts : List (RealSyntax.Term arity)) (before suffix : List Bool)
    (hn : SourceTermScan.forestNodes ts ≤ count) :
    (finalState arity count ⟨before, SourceTermScan.forestCode ts ++ suffix, ts.length, true⟩).input = suffix ∧
    (finalState arity count ⟨before, SourceTermScan.forestCode ts ++ suffix, ts.length, true⟩).valid = true := by
  let sf := run arity count ⟨before, SourceTermScan.forestCode ts ++ suffix, ts.length, true⟩
  have ho : outcome sf = some suffix := by
    rw [outcome_run, SourceTermControl.scan_eq]
    exact SourceTermScan.scan_complete count ts suffix hn
  cases hb : sf.valid && decide (sf.pending = 0) with
  | false => simp [outcome, hb] at ho
  | true =>
    have hi : sf.input = suffix := by simpa only [outcome, hb, ↓reduceIte, Option.some.injEq] using ho
    exact ⟨hi, hb⟩

end JointThermoComplexity.Complexity.SourceTermForest

#print axioms JointThermoComplexity.Complexity.SourceTermForest.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceTermForest.quadratic_timeBound
#print axioms JointThermoComplexity.Complexity.SourceTermForest.status_criterion
#print axioms JointThermoComplexity.Complexity.SourceTermForest.code_result
