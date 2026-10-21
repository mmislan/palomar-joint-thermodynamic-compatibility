module
public import proofs.JointThermoComplexity.Complexity.FreshGateCountFree
public import proofs.JointThermoComplexity.Complexity.ArityPrelude

set_option autoImplicit false
@[expose] public section

/-! Fresh total preparation of the gate count, auxiliary offset and binder count. -/

namespace JointThermoComplexity.Complexity.FreshArity
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountLayout

def Spare (m : ℕ) (work : Fin (m + 8) → Tape) : Prop :=
  ∀ i : Fin (m + 2), 2 ≤ i.val → work (NetworkParserFree.port (m + 2) i).castSucc = DimensionEntry.blankRegister

theorem spare_frame (m : ℕ) (work work' : Fin (m + 8) → Tape)
    (hw : ∀ j, j ≠ offset m → j ≠ binder m → work' j = work j) (h : Spare m work) : Spare m work' := by
  intro i hi
  have ho : (NetworkParserFree.port (m + 2) i).castSucc ≠ offset m := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = 0 at hv
    omega
  have hb : (NetworkParserFree.port (m + 2) i).castSucc ≠ binder m := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = 1 at hv
    omega
  exact (hw _ ho hb).trans (h i hi)

def machine (m : ℕ) : TM (m + 8) := seqTM (FreshGateCount.machine (m + 2)) (ArityPrelude.machine m)

def timeBound (L : ℕ) : ℕ := FreshGateCount.timeBound L + 25 * L + 20

theorem timeBound_eq (L : ℕ) : timeBound L = 4 * L ^ 3 + 44 * L ^ 2 + 116 * L + 90 := by
  rw [timeBound, FreshGateCount.timeBound_eq]
  ring1

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine m).reachesIn t ((machine m).initCfg input) d ∧
      (machine m).halted d ∧ Cursor [] input [] d.input d.work d.output ∧ (∀ j, Parked (d.work j)) ∧
      IsReg (GateCountValue.count input) (d.work (raw m)) ∧ IsReg (ArityValue.offset input) (d.work (offset m)) ∧
      IsReg (ArityValue.arity input) (d.work (binder m)) ∧ ParserRegisters.Kept (m + 2) input (CountAppend.oldWork d.work) ∧ Spare m d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hs, hg, hk, hfree⟩ := FreshGateCountFree.run (m + 2) input
  obtain ⟨ho, hb⟩ := CountLayout.zeros m c.work hfree
  have hspare : Spare m c.work := fun i _ => hfree i
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdsafe, hdgate, hdoffset, hdbinder, hdkept, hdspare⟩ :=
    ArityPrelude.hoareTime m input [] input [] (Spare m) (spare_frame m)
      c.input c.work c.output ⟨hc, hs, hg, ho, hb, hk, hspare⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (ArityPrelude.machine m).reachesIn td
      ⟨(ArityPrelude.machine m).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, hout] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (FreshGateCount.machine (m + 2)) (ArityPrelude.machine m) hcreach hchalt hr
  have hstart : phase1Wrap (FreshGateCount.machine (m + 2)) (ArityPrelude.machine m)
      ((FreshGateCount.machine (m + 2)).initCfg input) = (machine m).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (FreshGateCount.machine (m + 2)) (ArityPrelude.machine m) d, tc + 1 + td,
    by unfold timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt,
    hdcur, hdsafe, hdgate, hdoffset, hdbinder, hdkept, hdspare⟩

end JointThermoComplexity.Complexity.FreshArity

#print axioms JointThermoComplexity.Complexity.FreshArity.run
