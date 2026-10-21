module
public import proofs.JointThermoComplexity.Complexity.DenseRescanEntry
public import proofs.JointThermoComplexity.Complexity.DenseSourceLoop

set_option autoImplicit false
@[expose] public section

/-! One complete actual branch pass emits baseline, offset and all counted
source packets. Its initial-input endpoint derives every raw budget premise. -/

namespace JointThermoComplexity.Complexity.DenseBranchPass
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open CountedSparseControl (State)

def Frame (count : ℕ) (running : Bool) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  DenseMarkedFrame.Status running work ∧ IsReg count (work 18) ∧ R work
def word (boxed right : Bool) (n N U count : ℕ) (s : State) : List Bool :=
  DenseFixedPacket.word boxed right n N U ++ DenseMarkedControl.runWords boxed right n N count s
def machine (boxed right : Bool) : TM 64 := seqTM (DenseFixedPacket.machine boxed right) (DenseSourceLoop.machine boxed right)
def timeBound (boxed right : Bool) (L n N B count : ℕ) : ℕ :=
  DenseFixedPacket.timeBound boxed right n N B + 1 + DenseSourceLoop.timeBound boxed right L n N B count

theorem frame_stable (count : ℕ) (running : Bool) (R : (Fin 64 → Tape) → Prop) (hR : DenseSourceLoop.Stable R) :
    DenseSourceFrame.Stable (Frame count running R) := by
  rintro work next he ⟨⟨hh, hv⟩, hf, hr⟩
  have h15 : DenseSourceFrame.Outside (15 : Fin 64) := by unfold DenseSourceFrame.Outside DenseRowFrame.Outside; decide
  have h18 : DenseSourceFrame.Outside (18 : Fin 64) := by unfold DenseSourceFrame.Outside DenseRowFrame.Outside; decide
  exact ⟨⟨by rw [he 15 h15]; exact hh, by rw [he 15 h15]; exact hv⟩,
    by rw [he 18 h18]; exact hf, hR work next (fun j hj _ => he j hj.1) hr⟩

theorem hoareTime (boxed right : Bool) (L n N U B count : ℕ) (s : State) (hz : s.rows = 0)
    (values : Fin 64 → ℕ) (emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (hR : DenseSourceLoop.Stable R)
    (hlen : s.base.input.length ≤ L) (hU : U.bits.length ≤ B) (hLB : L ≤ B) (hbase : N + 2 ≤ B)
    (hN : (CountedSparseControl.run boxed count s).rows ≤ N) :
    (machine boxed right).HoareTime
      (DenseFixedSourceBank.Pre L n N U 0 values s.base.before s.base.input emitted (Frame count s.base.running R))
      (fun inp work out => DenseMarkedFrame.Inv L n N (emitted ++ word boxed right n N U count s) R
        (CountedSparseControl.run boxed count s) inp work out ∧ IsReg count (work 18)) (timeBound boxed right L n N B count) := by
  have h1 := DenseFixedSourceBank.hoareTime boxed right L n N U B values hU hbase (Frame count s.base.running R)
    (frame_stable count s.base.running R hR) s.base.before s.base.input emitted
  have hloop := DenseSourceLoop.hoareTime boxed right L n N B count (emitted ++ DenseFixedPacket.word boxed right n N U)
    R hR s hlen hLB hbase hN
  have h2 : (DenseSourceLoop.machine boxed right).HoareTime
      (DenseFixedSourceBank.Pre L n N U 2 values s.base.before s.base.input
        (emitted ++ DenseFixedPacket.word boxed right n N U) (Frame count s.base.running R))
      (fun inp work out => DenseMarkedFrame.Inv L n N (emitted ++ word boxed right n N U count s) R
        (CountedSparseControl.run boxed count s) inp work out ∧ IsReg count (work 18))
      (DenseSourceLoop.timeBound boxed right L n N B count) := by
    apply hloop.consequence
    · rintro inp work out ⟨⟨hc, hs, hp, hcore⟩, _hu, _href⟩
      have hcore' := DenseMarkedStep.core_frame n N 2 (Frame count s.base.running R) R work hcore hcore.frame.2.2
      have hw : DenseSourceFrame.Work L n N (2 + s.rows) R work := by
        rw [hz, Nat.add_zero]
        exact ⟨hp, hcore'⟩
      exact ⟨⟨hc, hs, hw, hcore.frame.1⟩, hcore.frame.2.1⟩
    · intro inp work out h
      simpa only [word, List.append_assoc] using h
    · exact le_rfl
  exact seqTM_hoareTime _ _ h1 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.1.phase
    rw [hi, hw, ho]
    exact h) h2

def Dims (boxed : Bool) (n N : ℕ) (work : Fin 64 → Tape) : Prop :=
  IsReg (DenseDimensionProgram.result boxed n N 3) (work 35) ∧
    IsReg (DenseDimensionProgram.result boxed n N 4) (work 36) ∧
    IsReg (DenseDimensionProgram.result boxed n N 5) (work 37)
def Retained (boxed : Bool) (n N U : ℕ) : (Fin 64 → Tape) → Prop := DenseLiveInitialize.Retained N U (Dims boxed n N)

theorem retained_stable (boxed : Bool) (n N U : ℕ) : DenseSourceLoop.Stable (Retained boxed n N U) := by
  rintro work next he ⟨hN, hU, h3, h4, h5⟩
  have safe : ∀ j : Fin 64, j ∈ ([17, 13, 35, 36, 37] : List (Fin 64)) → DenseMarkedFrame.Outside j ∧ j ≠ 18 := by
    unfold DenseMarkedFrame.Outside DenseSourceFrame.Outside DenseRowFrame.Outside
    decide
  have eq (j : Fin 64) (hj : j ∈ ([17, 13, 35, 36, 37] : List (Fin 64))) : next j = work j := he j (safe j hj).1 (safe j hj).2
  exact ⟨by rw [eq 17 (by decide)]; exact hN, by rw [eq 13 (by decide)]; exact hU,
    by rw [eq 35 (by decide)]; exact h3, by rw [eq 36 (by decide)]; exact h4, by rw [eq 37 (by decide)]; exact h5⟩

theorem rescan_pre (boxed : Bool) (input : List Bool) (emitted : List Bool) :
    ∀ inp work out, DenseFixedSourceBank.Pre input.length (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows
      (DenseReplayControl.rescan boxed input).base.offset 0 (DenseRawReady.values [])
      (DenseReplayControl.rescan boxed input).base.before (DenseReplayControl.rescan boxed input).base.input emitted
      (DenseLiveInitialize.Retained (DenseReplayControl.rescan boxed input).rows (DenseReplayControl.rescan boxed input).base.offset
        (DenseRescanEntry.Outer boxed input.length (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows
          (DenseReplayControl.rescan boxed input).base.running)) inp work out →
      DenseFixedSourceBank.Pre input.length (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows
        (DenseReplayControl.rescan boxed input).base.offset 0 (DenseRawReady.values [])
        (DenseReplayControl.state boxed input).base.before (DenseReplayControl.state boxed input).base.input emitted
        (Frame input.length (DenseReplayControl.state boxed input).base.running
          (Retained boxed (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows (DenseReplayControl.rescan boxed input).base.offset)) inp work out := by
  rintro inp work out ⟨⟨hc, hs, hp, hcore⟩, hu, href⟩
  have hr := hcore.frame
  have hf : Frame input.length (DenseReplayControl.state boxed input).base.running
      (Retained boxed (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows (DenseReplayControl.rescan boxed input).base.offset) work :=
    ⟨hr.2.2.1, hr.2.2.2.1, hr.1, hr.2.1, hr.2.2.2.2⟩
  exact ⟨⟨hc, hs, hp, DenseMarkedStep.core_frame _ _ _ _ _ work hcore hf⟩, hu, href⟩

def entry (boxed right : Bool) : TM 64 := seqTM (DenseRescanEntry.machine boxed) (machine boxed right)
def entryBound (boxed right : Bool) (input : List Bool) : ℕ := DenseRescanEntry.timeBound boxed input.length + 1 +
  timeBound boxed right input.length (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows
    (DenseReplayControl.budget input.length) input.length

theorem entry_hoareTime (boxed right : Bool) (input : List Bool) :
    (entry boxed right).HoareTime (InitialTapeLift.Initial 64 input)
      (fun inp work out => DenseMarkedFrame.Inv input.length (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows
        (SparseDimensionWords.header boxed (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows ++
          word boxed right (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows
            (DenseReplayControl.rescan boxed input).base.offset input.length (DenseReplayControl.state boxed input))
        (Retained boxed (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows (DenseReplayControl.rescan boxed input).base.offset)
        (CountedSparseControl.run boxed input.length (DenseReplayControl.state boxed input)) inp work out ∧ IsReg input.length (work 18))
      (entryBound boxed right input) := by
  have h2 := hoareTime boxed right input.length (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows
    (DenseReplayControl.rescan boxed input).base.offset (DenseReplayControl.budget input.length) input.length
    (DenseReplayControl.state boxed input) rfl (DenseRawReady.values [])
    (SparseDimensionWords.header boxed (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows)
    (Retained boxed (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows (DenseReplayControl.rescan boxed input).base.offset)
    (retained_stable _ _ _ _) (DenseReplayControl.input_length boxed input) (DenseReplayControl.offset_bits_le_budget boxed input)
    (DenseReplayControl.length_le_budget input.length) (DenseReplayControl.rows_le_budget boxed input)
    (by rw [DenseReplayControl.run_rows, DenseReplayControl.rescan_rows])
  have h2' := h2.consequence (rescan_pre boxed input _) (fun _ _ _ h => h) le_rfl
  exact seqTM_hoareTime _ _ (DenseRescanEntry.hoareTime boxed input) (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.1.phase
    rw [hi, hw, ho]
    exact h) h2'

end JointThermoComplexity.Complexity.DenseBranchPass

#print axioms JointThermoComplexity.Complexity.DenseBranchPass.hoareTime
#print axioms JointThermoComplexity.Complexity.DenseBranchPass.entry_hoareTime
