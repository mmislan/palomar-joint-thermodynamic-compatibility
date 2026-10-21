module
public import proofs.JointThermoComplexity.Complexity.BinaryGateOutput
public import proofs.JointThermoComplexity.Complexity.UnaryCopy
public import proofs.JointThermoComplexity.Complexity.UnarySuccessor

set_option autoImplicit false
@[expose] public section

/-! Emit one multiplication gate, store its old target address, then advance the next address. -/

namespace JointThermoComplexity.Complexity.GateStore
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun

variable {w arity : ℕ}

def next (e : Fin (w + 1) ≃ Fin (w + 1)) (source : Fin w) : Fin (w + 1) := e source.castSucc
def scratch (e : Fin (w + 1) ≃ Fin (w + 1)) (zero : Fin w) : Fin (w + 1) := e zero.castSucc

def machine (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w) (left right : Fin (w + 1)) : TM (w + 1) :=
  seqTM (BinaryGateOutput.machine true (scratch e zero) (next e source) left right)
    (seqTM (UnaryCopy.machine e source zero) (UnarySuccessor.machine (next e source)))

def timeBound (values : Fin (w + 1) → ℕ) (old : ℕ)
    (target left right : Fin (w + 1)) : ℕ :=
  BinaryGateOutput.timeBound values target left right + 2 * old + 7 * values target + 23

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w) (left right : Fin (w + 1))
    (hn : next e source ≠ scratch e zero) (hl : left ≠ scratch e zero) (hr : right ≠ scratch e zero)
    (values : Fin (w + 1) → Fin arity) (old : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next e source → j ≠ CountSumAt.destination e → work' j = work j) → R work → R work') :
    (machine e source zero left right).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work (scratch e zero)) ∧ IsReg (values (next e source)).val (work (next e source)) ∧
        IsReg (values left).val (work left) ∧ IsReg (values right).val (work right) ∧
        IsReg old (work (CountSumAt.destination e)) ∧ R work)
      (fun inp work out => Cursor before input
          (emitted ++ (BinaryGateOutput.formula true values (next e source) left right).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work (scratch e zero)) ∧
        IsReg ((values (next e source)).val + 1) (work (next e source)) ∧
        IsReg (values (next e source)).val (work (CountSumAt.destination e)) ∧ R work)
      (timeBound (fun j => (values j).val) old (next e source) left right) := by
  rintro inp work out ⟨hc, hs, hz, hnext, hleft, hright, hold, hrest⟩
  obtain ⟨c, tc, htc, hcreach, hchalt, hccur, hcsafe, hczero, hcnext, _hcleft, _hcright, hcold, hcR⟩ :=
    BinaryGateOutput.hoareTime true (scratch e zero) (next e source) left right hn hl hr values before input emitted
      (fun work => IsReg old (work (CountSumAt.destination e)) ∧ R work)
      inp work out ⟨hc, hs, hz, hnext, hleft, hright, hold, hrest⟩
  let P : (Fin (w + 1) → Tape) → Prop := fun work => Register 0 (work (scratch e zero)) ∧
    IsReg (values (next e source)).val (work (next e source)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hz, hn, hrest⟩
    exact ⟨by simpa only [scratch, hw _ (UnaryCopy.source_ne_destination e zero)] using hz,
      by simpa only [next, hw _ (UnaryCopy.source_ne_destination e source)] using hn,
      hR work work' (fun j _ hj => hw j hj) hrest⟩
  have hzero : IsReg 0 (c.work (scratch e zero)) :=
    CountTape.register_of_string (by simpa only [Nat.zero_bits, List.replicate_zero] using hczero.1) hczero.2
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdsafe, hdresult, hdnext, _hdzero, hdzero, _hdnext', hdR⟩ :=
    UnaryCopy.hoareTime e source zero old (values (next e source)).val before input
      (emitted ++ (BinaryGateOutput.formula true values (next e source) left right).code) P hP
      c.input c.work c.output ⟨hccur, hcsafe, hcold, hcnext, hzero, hczero, hcnext, hcR⟩
  let S : (Fin (w + 1) → Tape) → Prop := fun work => Register 0 (work (scratch e zero)) ∧
    IsReg (values (next e source)).val (work (CountSumAt.destination e)) ∧ R work
  have hS : ∀ work work', (∀ j, j ≠ next e source → work' j = work j) → S work → S work' := by
    rintro work work' hw ⟨hz, hd, hrest⟩
    exact ⟨by simpa only [hw _ hn.symm] using hz,
      by simpa only [hw _ (UnaryCopy.source_ne_destination e source).symm] using hd,
      hR work work' (fun j hj _ => hw j hj) hrest⟩
  obtain ⟨f, tf, htf, hfreach, hfhalt, hfcur, hfsafe, hfnext, hfzero, hfresult, hfR⟩ :=
    UnarySuccessor.hoareTime (next e source) (values (next e source)).val before input
      (emitted ++ (BinaryGateOutput.formula true values (next e source) left right).code) S hS
      d.input d.work d.output ⟨hdcur, hdsafe, hdnext, hdzero, hdresult, hdR⟩
  obtain ⟨hdi, hdw, hdo⟩ := hdcur.phase
  have hfr : (UnarySuccessor.machine (next e source)).reachesIn tf
      ⟨(UnarySuccessor.machine (next e source)).qstart, transitionInput d.input,
        (fun j => transitionTape (d.work j)), transitionTape d.output⟩ f := by
    simpa only [hdi, hdw, hdo] using hfreach
  have hrestreach := seqTM_reachesIn_of_reachesIn (UnaryCopy.machine e source zero)
    (UnarySuccessor.machine (next e source)) hdreach hdhalt hfr
  have hstart : phase1Wrap (UnaryCopy.machine e source zero) (UnarySuccessor.machine (next e source))
      ⟨(UnaryCopy.machine e source zero).qstart, c.input, c.work, c.output⟩ =
      ⟨(seqTM (UnaryCopy.machine e source zero) (UnarySuccessor.machine (next e source))).qstart,
        c.input, c.work, c.output⟩ := rfl
  rw [hstart] at hrestreach
  obtain ⟨hci, hcw, hco⟩ := hccur.phase
  have hrr : (seqTM (UnaryCopy.machine e source zero) (UnarySuccessor.machine (next e source))).reachesIn (td + 1 + tf)
      ⟨(seqTM (UnaryCopy.machine e source zero) (UnarySuccessor.machine (next e source))).qstart,
        transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩
      (phase2Wrap (UnaryCopy.machine e source zero) (UnarySuccessor.machine (next e source)) f) := by
    rw [hci, hcw, hco]
    exact hrestreach
  have hreach := seqTM_reachesIn_of_reachesIn
    (BinaryGateOutput.machine true (scratch e zero) (next e source) left right)
    (seqTM (UnaryCopy.machine e source zero) (UnarySuccessor.machine (next e source)))
    hcreach hchalt hrr
  have hbound : tc + 1 + (td + 1 + tf) ≤
      BinaryGateOutput.timeBound (fun j => (values j).val) (next e source) left right +
        2 * old + 7 * (values (next e source)).val + 23 := by omega
  exact ⟨phase2Wrap (BinaryGateOutput.machine true (scratch e zero) (next e source) left right)
      (seqTM (UnaryCopy.machine e source zero) (UnarySuccessor.machine (next e source)))
      (phase2Wrap (UnaryCopy.machine e source zero) (UnarySuccessor.machine (next e source)) f),
    tc + 1 + (td + 1 + tf), hbound, hreach,
    (phase2Wrap_halted_iff _ _ _).mpr ((phase2Wrap_halted_iff _ _ f).mpr hfhalt),
    hfcur, hfsafe, hfzero, hfnext, hfresult, hfR⟩

end JointThermoComplexity.Complexity.GateStore

#print axioms JointThermoComplexity.Complexity.GateStore.hoareTime
