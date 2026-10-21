module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxLoop
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxHeader
public import proofs.JointThermoComplexity.Complexity.CounterInputEntry

set_option autoImplicit false
@[expose] public section

/-! Actual six-tape syntax expansion from blank work tapes, on every raw binary input. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxEmitter
open _root_.Complexity _root_.Complexity.TM SmallSyntaxRegisters
open HeaderAt (Cursor)

def Initial (input : List Bool) : _root_.Complexity.TM.TapePred 6 := fun inp work out =>
  inp = Tape.init (input.map Γ.ofBool) ∧ (∀ j, work j = Tape.init []) ∧ out = Tape.init []

def Frame (L : ℕ) (work : Fin 6 → Tape) : Prop := IsReg L (work fuel)

theorem frame_stable (L : ℕ) : Stable (Frame L) := by
  intro work work' he hr
  simpa only [Frame, he] using hr

def startState (input : List Bool) : SmallSyntaxControl.State := ⟨[], input, [], 0⟩
def headerState (input : List Bool) : SmallSyntaxControl.State :=
  SmallSyntaxHeader.setupState (startState input)

theorem entry_hoareTime (input : List Bool) :
    (BoundedCounters.entry fuel).HoareTime (Initial input)
      (Inv (Frame input.length) (startState input)) (2 * input.length + 6) := by
  have h := BoundedCounters.entry_hoareTime fuel input
  rw [BoundedCounters.inputWork_eq] at h
  apply h.strengthen_post
  rintro inp work out ⟨rfl, rfl, hout⟩
  let bank := BoundedCounters.inputWork fuel input
  have hs : ∀ j, Parked (bank j) := by
    intro j
    simp only [bank, BoundedCounters.inputWork, Function.update_apply]
    split <;> exact parked_regTape _
  have hz : ∀ j, (bank j).cells 0 = Γ.start := by
    intro j
    simp only [bank, BoundedCounters.inputWork, Function.update_apply]
    split <;> rfl
  have hpend : IsReg 0 (bank pending) := by
    rw [show bank pending = regTape 0 from Function.update_of_ne (by decide) _ _]
    exact reg_regT 0
  have ht : ∀ i, (bank (tags i)).head = 1 := by
    intro i
    rw [show bank (tags i) = regTape 0 from Function.update_of_ne (fuel_tags i).symm _ _]
    rfl
  have hf : (bank flag).head = 1 := by
    rw [show bank flag = regTape 0 from Function.update_of_ne (by decide) _ _]
    rfl
  have hreg : Frame input.length bank := by
    change IsReg input.length (Function.update (fun _ => regTape 0) fuel (regTape input.length) fuel)
    rw [Function.update_self]
    exact reg_regT _
  exact ⟨⟨rfl, rfl, fun j => ⟨(hs j).read_ne_start, (hs j).1⟩,
    ((FixedOutput.outAcc_iff [] out).mp hout).1, hout.2.1⟩, hs, hz, hpend, ht, hf, hreg⟩

def continuation : TM 6 := seqTM SmallSyntaxHeader.setupMachine SmallSyntaxLoop.machine
def machine : TM 6 := seqTM (BoundedCounters.entry fuel) continuation
def timeBound (L : ℕ) : ℕ := 16 * L ^ 2 + 59 * L + 21

def Post (input : List Bool) : _root_.Complexity.TM.TapePred 6 := fun _inp _work out =>
  out.HasBinaryPrefix (SmallSyntaxControl.code input) ∧ out.cells 0 = Γ.start

theorem continuation_hoareTime (input : List Bool) :
    continuation.HoareTime (Inv (Frame input.length) (startState input)) (Post input)
      (4 * HeaderControl.count input + 11 + 1 + SmallSyntaxLoop.timeBound input.length 0 input.length) := by
  have hh := SmallSyntaxHeader.setup_hoareTime (startState input) rfl (Frame input.length) (frame_stable input.length)
  have hlen : (headerState input).input.length ≤ input.length := by
    have hw := congrArg List.length (HeaderControl.consumed_and_suffix input)
    simp only [List.length_append] at hw
    change (HeaderControl.suffix input).length ≤ input.length
    omega
  have hl := SmallSyntaxLoop.hoareTime input.length input.length (headerState input) hlen
  have h := seqTM_hoareTime SmallSyntaxHeader.setupMachine SmallSyntaxLoop.machine hh (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨⟨hc, hr.safe, hr.markers, hr.counter, hr.tagHeads, hr.flagHead, trivial⟩, hr.frame⟩) hl
  exact h.strengthen_post (by
    rintro inp work out ⟨⟨hc, _hr⟩, _hf⟩
    exact ⟨hc.tapePrefix, hc.zero⟩)

theorem hoareTime (input : List Bool) : machine.HoareTime (Initial input) (Post input) (timeBound input.length) := by
  have he := entry_hoareTime input
  have hc := continuation_hoareTime input
  have h := seqTM_hoareTime (BoundedCounters.entry fuel) continuation he (by
    rintro inp work out ⟨hcur, hr⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨hcur, hr⟩) hc
  exact h.mono_bound (by
    have hn := HeaderControl.count_le_length input
    rw [SmallSyntaxLoop.quadratic_timeBound]
    unfold timeBound
    omega)

theorem run (input : List Bool) :
    ∃ c t, t ≤ timeBound input.length ∧ machine.reachesIn t (machine.initCfg input) c ∧ machine.halted c ∧
      c.output.HasBinaryPrefix (SmallSyntaxControl.code input) ∧ c.output.cells 0 = Γ.start := by
  obtain ⟨c, t, ht, hr, hh, hp⟩ := hoareTime input _ _ _ ⟨rfl, fun _ => rfl, rfl⟩
  exact ⟨c, t, ht, hr, hh, hp⟩

theorem computesInTime : machine.ComputesInTime SmallSyntaxControl.code timeBound := by
  intro input
  obtain ⟨c, t, ht, hr, hh, hp, _hz⟩ := run input
  exact ⟨c, t, ht, hr, hh, hp.2.1, hp.2.2 _ le_rfl⟩

end JointThermoComplexity.Complexity.SmallSyntaxEmitter

#print axioms JointThermoComplexity.Complexity.SmallSyntaxEmitter.entry_hoareTime
#print axioms JointThermoComplexity.Complexity.SmallSyntaxEmitter.hoareTime
#print axioms JointThermoComplexity.Complexity.SmallSyntaxEmitter.computesInTime
