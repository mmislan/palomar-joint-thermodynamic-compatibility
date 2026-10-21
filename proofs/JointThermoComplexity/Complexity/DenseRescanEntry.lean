module
public import proofs.JointThermoComplexity.Complexity.DenseReplayControl
public import proofs.JointThermoComplexity.Complexity.DenseLiveInitialize
public import proofs.JointThermoComplexity.Complexity.DenseMarkedFrame

set_option autoImplicit false
@[expose] public section

/-! The actual all-input rescan supplies the one-time live allocation. Computed
dimensions, status, fuel, binary total and offset are retained explicitly. -/

namespace JointThermoComplexity.Complexity.DenseRescanEntry
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open CountedSparseControl (State)

def Outer (boxed : Bool) (L n N : ℕ) (running : Bool) (work : Fin 64 → Tape) : Prop :=
  DenseMarkedFrame.Status running work ∧ IsReg L (work 18) ∧
    IsReg (DenseDimensionProgram.result boxed n N 3) (work 35) ∧
    IsReg (DenseDimensionProgram.result boxed n N 4) (work 36) ∧
    IsReg (DenseDimensionProgram.result boxed n N 5) (work 37)

theorem outer_end (boxed : Bool) (L n N : ℕ) (running : Bool) : DenseEndFrame.Stable (Outer boxed L n N running) := by
  rintro work next he ⟨⟨hh, hv⟩, hf, hext, hs, hr⟩
  exact ⟨⟨by rw [he 15 (by decide) (by decide)]; exact hh,
    by rw [he 15 (by decide) (by decide)]; exact hv⟩,
    by rw [he 18 (by decide) (by decide)]; exact hf,
    by rw [he 35 (by decide) (by decide)]; exact hext,
    by rw [he 36 (by decide) (by decide)]; exact hs,
    by rw [he 37 (by decide) (by decide)]; exact hr⟩

theorem outer_source (boxed : Bool) (L n N : ℕ) (running : Bool) : DenseSourceFrame.Stable (Outer boxed L n N running) := by
  rintro work next he ⟨⟨hh, hv⟩, hf, hext, hs, hr⟩
  have safe : ∀ j : Fin 64, j ∈ ([15, 18, 35, 36, 37] : List (Fin 64)) → DenseSourceFrame.Outside j := by
    unfold DenseSourceFrame.Outside DenseRowFrame.Outside
    decide
  exact ⟨⟨by rw [he 15 (safe 15 (by decide))]; exact hh, by rw [he 15 (safe 15 (by decide))]; exact hv⟩,
    by rw [he 18 (safe 18 (by decide))]; exact hf,
    by rw [he 35 (safe 35 (by decide))]; exact hext,
    by rw [he 36 (safe 36 (by decide))]; exact hs,
    by rw [he 37 (safe 37 (by decide))]; exact hr⟩

theorem pre (boxed : Bool) (L n : ℕ) (s : State) (emitted : List Bool) :
    ∀ inp work out, SparseDenseDimensions.Pred boxed L n s emitted inp work out →
      DenseLiveInitialize.Pre L n s.rows s.base.offset s.base.before s.base.input emitted
        (Outer boxed L n s.rows s.base.running) inp work out := by
  rintro inp work out ⟨⟨⟨hc, _, hfields, hmh, hmr⟩, hf⟩, hs, hd, hz⟩
  rcases hfields with ⟨⟨hready, hadj, hU, _haux, _ht, har⟩, hN⟩
  have hparser : DenseSourceFrame.Parser L work := by
    rcases hready with ⟨hi, hh, hslots, hend, hflag⟩
    refine ⟨hi, hh, ?_, hend, hflag⟩
    intro p hp
    have hm : p ∈ ([(2, 6), (3, 7), (4, 8), (5, 9)] : List (Fin 64 × Fin 64)) := hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · exact hslots (2, 6) (by decide)
    · exact hslots (3, 7) (by decide)
    · exact hslots (4, 8) (by decide)
    · exact hslots (5, 9) (by decide)
  have hcur : Cursor s.base.before s.base.input emitted inp work out :=
    ⟨hc.cells, hc.head, fun j => ⟨(hs j).read_ne_start, (hs j).1⟩, hc.tapePrefix, hc.zero⟩
  exact ⟨hcur, hs, hparser, hadj, har, hd 1, hd 2, hN, hU, hz, ⟨hmh, hmr⟩, hf, hd 3, hd 4, hd 5⟩

theorem initialize_hoareTime (boxed : Bool) (L n : ℕ) (s : State) (B : ℕ) (hB : s.rows.bits.length ≤ B) (emitted : List Bool) :
    DenseLiveInitialize.machine.HoareTime (SparseDenseDimensions.Pred boxed L n s emitted)
      (DenseFixedSourceBank.Pre L n s.rows s.base.offset 0 (DenseRawReady.values []) s.base.before s.base.input emitted
        (DenseLiveInitialize.Retained s.rows s.base.offset (Outer boxed L n s.rows s.base.running)))
      (DenseLiveInitialize.timeBound L B) :=
  (DenseLiveInitialize.hoareTime L n s.rows s.base.offset B hB s.base.before s.base.input emitted
    (Outer boxed L n s.rows s.base.running) (outer_end boxed L n s.rows s.base.running) (outer_source boxed L n s.rows s.base.running)).consequence
      (pre boxed L n s emitted) (fun _ _ _ h => h) le_rfl

def machine (boxed : Bool) : TM 64 := seqTM (SparseDenseRescan.entry boxed) DenseLiveInitialize.machine
def timeBound (boxed : Bool) (L : ℕ) : ℕ :=
  SparseDenseRescan.entryBound boxed L + 1 + DenseLiveInitialize.timeBound L (DenseReplayControl.budget L)

theorem hoareTime (boxed : Bool) (input : List Bool) :
    (machine boxed).HoareTime (InitialTapeLift.Initial 64 input)
      (DenseFixedSourceBank.Pre input.length (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows
        (DenseReplayControl.rescan boxed input).base.offset 0 (DenseRawReady.values [])
        (DenseReplayControl.rescan boxed input).base.before (DenseReplayControl.rescan boxed input).base.input
        (SparseDimensionWords.header boxed (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows)
        (DenseLiveInitialize.Retained (DenseReplayControl.rescan boxed input).rows (DenseReplayControl.rescan boxed input).base.offset
          (Outer boxed input.length (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows
            (DenseReplayControl.rescan boxed input).base.running))) (timeBound boxed input.length) := by
  have h1 := SparseDenseRescan.entry_hoareTime boxed input
  have h2 := initialize_hoareTime boxed input.length (HeaderControl.count input) (DenseReplayControl.rescan boxed input)
    (DenseReplayControl.budget input.length) (DenseReplayControl.count_bits_le_budget boxed input)
    (SparseDimensionWords.header boxed (HeaderControl.count input) (DenseReplayControl.rescan boxed input).rows)
  exact seqTM_hoareTime _ _ h1
    (SparseDenseDimensions.phase boxed input.length (HeaderControl.count input) (DenseReplayControl.rescan boxed input) _) h2

end JointThermoComplexity.Complexity.DenseRescanEntry

#print axioms JointThermoComplexity.Complexity.DenseRescanEntry.hoareTime
