module
public import proofs.JointThermoComplexity.Complexity.SourceScannerInit

set_option autoImplicit false
@[expose] public section

/-! Actual source validity from blank initCfg, with fixed work-tape count and an independent decoder criterion. -/

namespace JointThermoComplexity.Complexity.SourceValidityRun
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceFormulaRegisters SourceScannerPorts

def Post (input : List Bool) : _root_.Complexity.TM.TapePred 11 := fun inp work out =>
  Inv layout input.length (HeaderControl.count input) [] (fun _ => True)
    (SourceSentenceEntry.finalState input.length [] input) inp work out ∧ IsReg input.length (work fuel.castSucc)

def machine : TM 11 := seqTM SourceScannerInit.machine (SourceSentenceEntry.machine layout fuel)
def timeBound (L : ℕ) : ℕ := 34 * L ^ 3 + 97 * L ^ 2 + 82 * L + 43

theorem hoareTime (input : List Bool) : machine.HoareTime (SourceScannerInit.Initial input) (Post input) (timeBound input.length) := by
  have hi := SourceScannerInit.hoareTime input
  have hs := SourceSentenceEntry.hoareTime layout fuel fuel_outside input.length false [] input [] le_rfl
    (fun _ => True) (fun _ _ _ _ => trivial)
  have hfull := seqTM_hoareTime SourceScannerInit.machine (SourceSentenceEntry.machine layout fuel) hi (by
    rintro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.1.phase
    rw [hi, hw, ho]
    exact h) hs
  have hb := SourceSentenceEntry.cubic_timeBound input.length input le_rfl
  exact hfull.mono_bound (by unfold timeBound; omega)

theorem run (input : List Bool) :
    ∃ c t, t ≤ timeBound input.length ∧ machine.reachesIn t (machine.initCfg input) c ∧ machine.halted c ∧
      Post input c.input c.work c.output :=
  hoareTime input _ _ _ ⟨rfl, fun _ => rfl, rfl⟩

theorem valid_eq (input : List Bool) :
    (SourceSentenceEntry.finalState input.length [] input).valid = (RealSyntax.decodeSentence input).isSome := by
  have hc := SourceSentenceEntry.status_criterion input.length input le_rfl
  cases hv : (SourceSentenceEntry.finalState input.length [] input).valid <;>
    cases hd : (RealSyntax.decodeSentence input).isSome <;> simp_all

theorem post_status (input : List Bool) (inp : Tape) (work : Fin 11 → Tape) (out : Tape) (h : Post input inp work out) :
    (work (NaturalScanBuffer.flag 9)).read = Γ.ofBool (RealSyntax.decodeSentence input).isSome := by
  rw [← valid_eq]
  exact h.1.2.2.2

end JointThermoComplexity.Complexity.SourceValidityRun

#print axioms JointThermoComplexity.Complexity.SourceValidityRun.hoareTime
#print axioms JointThermoComplexity.Complexity.SourceValidityRun.run
#print axioms JointThermoComplexity.Complexity.SourceValidityRun.post_status
