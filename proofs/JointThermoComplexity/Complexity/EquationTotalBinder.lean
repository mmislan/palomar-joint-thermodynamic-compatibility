module
public import proofs.JointThermoComplexity.Complexity.EquationBootstrapState
public import proofs.JointThermoComplexity.Complexity.BinderOutput
public import proofs.JointThermoComplexity.Complexity.InitializedSpanQuery

set_option autoImplicit false
@[expose] public section

/-! Compute and emit the actual total variable binder before the equation loop. -/

namespace JointThermoComplexity.Complexity.EquationTotalBinder
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryCounterInit MainEquationWork
open HeaderAt (Cursor)

def counts (L : ℕ) (input : List Bool) : Counts := LocalBranchQuery.formulaCounts (PreorderLookahead.formulaResult L input)
def total (arity L : ℕ) (input : List Bool) : ℕ := arity + PreorderLookahead.formulaSize L input

def sumMachine : TM 32 := SelectedAddressArithmetic.machine adjustedPort arityPort QueryWorkFrame.result (by decide) (by decide)
def machine : TM 32 := seqTM InitializedSpanQuery.formulaMachine (seqTM sumMachine (BinderOutput.machine adjustedPort))

theorem query_hoareTime (s : FormulaSpanControl.State) (arity L : ℕ) (emitted : List Bool)
    (R : Work → Prop) (hR : Stable R) (hlen : s.input.length ≤ L) :
    InitializedSpanQuery.formulaMachine.HoareTime
      (fun inp tapes out => Cursor s.before s.input emitted inp tapes out ∧
        Before s arity L 0 EquationWorkReset.zeroCounts EquationWorkReset.zeroValues R tapes)
      (fun inp tapes out => Cursor s.before s.input emitted inp tapes out ∧
        Before s arity L 0 (counts L s.input) EquationWorkReset.zeroValues R tapes)
      (InitializedSpanQuery.formulaTime L s.before.length EquationWorkReset.zeroCounts) := by
  rintro inp tapes out ⟨hc, hs, hp, hr⟩
  let F := Frame s arity L 0 R
  have hF := frame_stable s arity L 0 R hR
  obtain ⟨d, t, ht, hd, hh, hc', hs', hpos, hquery⟩ :=
    InitializedSpanQuery.formula_hoareTime L EquationWorkReset.zeroCounts s.before s.input emitted
      (LocalBranchState.QueryExtra 0 EquationWorkReset.zeroValues F)
      (LocalBranchState.query_extra_stable 0 EquationWorkReset.zeroValues F hF) hlen inp tapes out
      ⟨hc, hs, hr.basic.positionReg, LocalBranchState.to_query EquationWorkReset.zeroCounts EquationWorkReset.zeroValues L 0 F tapes hr hp⟩
  have hfinal := LocalBranchState.from_query (counts L s.input) EquationWorkReset.zeroValues L 0 F d.work hquery hpos
  exact ⟨d, t, ht, hd, hh, hc', hs', hfinal.2, hfinal.1⟩

theorem sum_hoareTime (s : FormulaSpanControl.State) (arity L : ℕ) (q : Counts) (emitted : List Bool)
    (R : Work → Prop) (hR : Stable R) :
    sumMachine.HoareTime
      (fun inp tapes out => Cursor s.before s.input emitted inp tapes out ∧
        Before s arity L 0 q EquationWorkReset.zeroValues R tapes)
      (fun inp tapes out => Cursor s.before s.input emitted inp tapes out ∧
        Before s arity L (arity + q.nodes) q EquationWorkReset.zeroValues R tapes)
      (5 * (arity + q.nodes) + 15) := by
  rintro inp tapes out ⟨hc, hs, hp, hr⟩
  let C : Work → Prop := fun tapes' => ∀ j, j ≠ adjustedPort → tapes' j = tapes j
  have hC : ∀ tapes' tapes'', (∀ j, j ≠ adjustedPort → tapes'' j = tapes' j) → C tapes' → C tapes'' := by
    intro tapes' tapes'' he hh j hj
    exact (he j hj).trans (hh j hj)
  obtain ⟨d, t, ht, hd, hh, hc', hs', hadj, _, _, he⟩ :=
    SelectedAddressArithmetic.hoareTime adjustedPort arityPort QueryWorkFrame.result (by decide) (by decide)
      0 arity q.nodes s.before s.input emitted C hC inp tapes out
      ⟨hc, hs, hr.basic.frame.adjustedReg, hr.basic.frame.arityReg, hr.basic.nodeReg, fun _ _ => rfl⟩
  have hframe := MainNodeEquation.frame_address s arity L 0 (arity + q.nodes) R hR tapes d.work hr.basic.frame
    (fun j hj _ => he j hj) hadj
  have hb0 : LocalBranchState.Basic q L (fun _ => True) tapes :=
    ⟨hr.basic.tagHeads, hr.basic.flagHead, hr.basic.termReg, hr.basic.formulaReg, hr.basic.nodeReg,
      hr.basic.fuelReg, hr.basic.positionReg, hr.basic.scratchReg, trivial⟩
  have hbasic_other : ∀ j, LocalBranchState.BasicPorts j → j ≠ adjustedPort := by
    unfold LocalBranchState.BasicPorts
    decide
  have hb := LocalBranchState.basic_transfer q L (fun _ => True) tapes d.work hb0
    (fun j hj => he j (hbasic_other j hj)) trivial
  have hm : ∀ j, j ≠ LocalBranchState.anchor → (d.work j).cells 0 = Γ.start := by
    intro j hj
    by_cases hj' : j = adjustedPort
    · subst j
      exact hadj.cell0
    · rw [he j hj']
      exact hr.markers j hj
  have ha : AddressCounterPlacement.Registers EquationWorkReset.zeroValues d.work := by
    intro i
    have hi : AddressCounterPlacement.slot i ≠ adjustedPort := by
      intro h
      have hv := congrArg Fin.val h
      change 19 + i.val = 28 at hv
      omega
    rw [he _ hi]
    exact hr.addresses i
  exact ⟨d, t, by omega, hd, hh, hc', hs', by simpa only [he LocalBranchState.anchor (by decide)] using hp,
    ⟨hb.tagHeads, hb.flagHead, hb.termReg, hb.formulaReg, hb.nodeReg, hb.fuelReg, hb.positionReg, hb.scratchReg, hframe⟩, hm, ha⟩

noncomputable def timeBound (s : FormulaSpanControl.State) (arity L : ℕ) : ℕ :=
  InitializedSpanQuery.formulaTime L s.before.length EquationWorkReset.zeroCounts + 9 * total arity L s.input + 21

theorem hoareTime (s : FormulaSpanControl.State) (arity L : ℕ) (emitted : List Bool)
    (R : Work → Prop) (hR : Stable R) (hlen : s.input.length ≤ L) :
    machine.HoareTime
      (fun inp tapes out => Cursor s.before s.input emitted inp tapes out ∧
        Before s arity L 0 EquationWorkReset.zeroCounts EquationWorkReset.zeroValues R tapes)
      (fun inp tapes out => Cursor s.before s.input (emitted ++ RealSyntax.binderCode (total arity L s.input)) inp tapes out ∧
        Before s arity L (total arity L s.input) (counts L s.input) EquationWorkReset.zeroValues R tapes)
      (timeBound s arity L) := by
  let m := total arity L s.input
  let q := counts L s.input
  have hq := query_hoareTime s arity L emitted R hR hlen
  have hsum := sum_hoareTime s arity L q emitted R hR
  have he := BinderOutput.hoareTime adjustedPort m s.before s.input emitted (Before s arity L m q EquationWorkReset.zeroValues R)
  have hrest := seqTM_hoareTime sumMachine (BinderOutput.machine adjustedPort) hsum (by
    rintro inp tapes out ⟨hc, hs, hp, hr⟩
    obtain ⟨hin, hwork, hout⟩ := hc.phase
    rw [hin, hwork, hout]
    exact ⟨hr.basic.frame.adjustedReg, hc, hs, hs, hp, hr⟩) he
  have hseq := seqTM_hoareTime InitializedSpanQuery.formulaMachine (seqTM sumMachine (BinderOutput.machine adjustedPort)) hq (by
    rintro inp tapes out ⟨hc, hs, hp, hr⟩
    obtain ⟨hin, hwork, hout⟩ := hc.phase
    rw [hin, hwork, hout]
    exact ⟨hc, hs, hp, hr⟩) hrest
  apply hseq.consequence (fun _ _ _ hp => hp)
  · rintro inp tapes out ⟨_, hc, _, hr⟩
    exact ⟨hc, hr⟩
  · dsimp [timeBound, m, q, counts, total, LocalBranchQuery.formulaCounts, PreorderLookahead.formulaSize]
    omega

theorem total_le (arity L : ℕ) (input : List Bool) : total arity L input ≤ arity + 4 * L := by
  have h := PreorderLookahead.formula_bound L input
  dsimp [total]
  omega

end JointThermoComplexity.Complexity.EquationTotalBinder

#print axioms JointThermoComplexity.Complexity.EquationTotalBinder.hoareTime
