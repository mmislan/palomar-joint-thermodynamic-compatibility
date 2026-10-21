module
public import proofs.JointThermoComplexity.Complexity.StrictLeadingInitialization
public import proofs.JointThermoComplexity.Complexity.BinaryAddressLoad
public import proofs.JointThermoComplexity.Complexity.GeneratedLoopFramed

set_option autoImplicit false
@[expose] public section

/-! The concrete two-buffer generated tail retains every saved schedule counter and header. -/

namespace JointThermoComplexity.Complexity.GeneratedTailFrame
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun

def ports : GeneratedEnergyStep.Ports 64 := ⟨StrictLeadingInitialization.rawPorts, by decide⟩
def countValue (L n s : ℕ) (i : Fin 16) : ℕ := StrictScheduleProgram.values L n s i
def Keep (L n s : ℕ) (original : List Bool) (work : Fin 64 → Tape) : Prop :=
  StrictLeadingInitialization.Saved L n s work ∧ StrictRowInitialization.Header original work
def Logical (L n s : ℕ) (original : List Bool) (values : Fin 2 → ℕ)
    (before input emitted : List Bool) : _root_.Complexity.TM.TapePred 64 :=
  GeneratedEnergyStep.Logical ports values before input emitted (Keep L n s original)

theorem counter_separate : ∀ i j, StrictScheduleEntry.ports.index i ≠ ports.index j := by decide
theorem header_separate : ∀ j, (62 : Fin 64) ≠ ports.index j ∧ (63 : Fin 64) ≠ ports.index j := by decide

theorem keep_stable (L n s : ℕ) (original : List Bool) : GeneratedEnergyStep.Stable ports (Keep L n s original) := by
  rintro work next he ⟨hc, hh, hv, hb⟩
  exact ⟨fun i hi hf => by simpa only [he _ (counter_separate i)] using hc i hi hf,
    by simpa only [he 62 (fun j => (header_separate j).1)] using hh,
    by simpa only [he 62 (fun j => (header_separate j).1)] using hv,
    by simpa only [he 63 (fun j => (header_separate j).2)] using hb⟩

theorem keep_single (L n s : ℕ) (original : List Bool) (j : Fin 2) :
    BinaryAddressLoad.Stable (ports.index j) (Keep L n s original) := by
  intro work next he hk
  exact keep_stable L n s original work next (fun k h => he k (h j)) hk

def loadMachine (source : Fin 16) (dst : Fin 2) : TM 64 :=
  BinaryAddressLoad.machine (StrictScheduleEntry.ports.index source) (ports.index dst)

theorem load_hoareTime (L n s : ℕ) (original : List Bool) (values : Fin 2 → ℕ)
    (source : Fin 16) (h14 : source ≠ 14) (h15 : source ≠ 15) (dst : Fin 2)
    (before input emitted : List Bool) :
    (loadMachine source dst).HoareTime (Logical L n s original values before input emitted)
      (Logical L n s original (Function.update values dst (countValue L n s source)) before input emitted)
      (BinaryAddressLoad.timeBound (values dst) (countValue L n s source)) := by
  let C : (Fin 64 → Tape) → Prop := fun work =>
    (∀ j, j ≠ dst → Register (values j) (work (ports.index j))) ∧ Keep L n s original work
  have hC : BinaryAddressLoad.Stable (ports.index dst) C := by
    rintro work next he ⟨hr, hk⟩
    exact ⟨fun j hj => by simpa only [he _ (ports.injective.ne hj)] using hr j hj,
      keep_single L n s original dst work next he hk⟩
  have h := BinaryAddressLoad.hoareTime (StrictScheduleEntry.ports.index source) (ports.index dst)
    (counter_separate source dst) (values dst) (countValue L n s source) before input emitted C hC
  exact h.consequence (by
    rintro inp work out ⟨hc, hr⟩
    exact ⟨hc, hr.safe, hr.registers dst, hr.extra.1 source h14 h15,
      (fun j _ => hr.registers j), hr.extra⟩) (by
    rintro inp work out ⟨hc, hs, hd, _hf, hother, hk⟩
    refine ⟨hc, ⟨hs, ?_, hk⟩⟩
    intro j
    by_cases hj : j = dst
    · subst j
      simpa only [Function.update_self] using hd
    · simpa only [Function.update_of_ne hj] using hother j hj) le_rfl

theorem pair_update (values : Fin 2 → ℕ) (a b : ℕ) :
    Function.update (Function.update values 0 a) 1 b = ![a, b] := by
  funext j
  fin_cases j
  · change Function.update (Function.update values 0 a) 1 b 0 = a
    rw [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), Function.update_self]
  · change Function.update (Function.update values 0 a) 1 b 1 = b
    rw [Function.update_self]

def pairMachine (a b : Fin 16) : TM 64 := seqTM (loadMachine a 0) (loadMachine b 1)
def pairTime (L n s : ℕ) (values : Fin 2 → ℕ) (a b : Fin 16) : ℕ :=
  BinaryAddressLoad.timeBound (values 0) (countValue L n s a) + 1 +
    BinaryAddressLoad.timeBound (values 1) (countValue L n s b)

theorem pair_hoareTime (L n s : ℕ) (original : List Bool) (values : Fin 2 → ℕ)
    (a b : Fin 16) (ha14 : a ≠ 14) (ha15 : a ≠ 15) (hb14 : b ≠ 14) (hb15 : b ≠ 15)
    (before input emitted : List Bool) :
    (pairMachine a b).HoareTime (Logical L n s original values before input emitted)
      (Logical L n s original ![countValue L n s a, countValue L n s b] before input emitted)
      (pairTime L n s values a b) := by
  have ha := load_hoareTime L n s original values a ha14 ha15 0 before input emitted
  have hb := load_hoareTime L n s original (Function.update values 0 (countValue L n s a)) b hb14 hb15 1
    before input emitted
  have hseq := seqTM_hoareTime _ _ ha (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hb
  simpa only [pairMachine, pairTime, pair_update, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)] using hseq

end JointThermoComplexity.Complexity.GeneratedTailFrame

#print axioms JointThermoComplexity.Complexity.GeneratedTailFrame.keep_stable
#print axioms JointThermoComplexity.Complexity.GeneratedTailFrame.load_hoareTime
#print axioms JointThermoComplexity.Complexity.GeneratedTailFrame.pair_hoareTime
