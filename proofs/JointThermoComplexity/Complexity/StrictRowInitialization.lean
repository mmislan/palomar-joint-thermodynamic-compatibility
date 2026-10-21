module
public import proofs.JointThermoComplexity.Complexity.StrictScheduleEntry
public import proofs.JointThermoComplexity.Complexity.FlagInitialization
public import proofs.JointThermoComplexity.Complexity.UnaryBinaryBuildFramed
public import proofs.JointThermoComplexity.Complexity.RowEnergyLoop

set_option autoImplicit false
@[expose] public section

/-! Concrete flags and shared binary scale for the actual64-tape strict row loop. -/

namespace JointThermoComplexity.Complexity.StrictRowInitialization
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open StrictScheduleProgram (values)

def flags : Fin 14 → Fin 64 := ![0, 1, 2, 6, 7, 8, 12, 13, 14, 18, 19, 20, 21, 28]
def flagValues (i : Fin 14) : Bool := decide (i = 13)
theorem flags_injective : Function.Injective flags := by decide
theorem counter_flags : ∀ i a, StrictScheduleEntry.ports.index i ≠ flags a := by decide
theorem counter_scale : ∀ i, StrictScheduleEntry.ports.index i ≠ 27 := by decide
theorem flags_scale : ∀ a, flags a ≠ 27 := by decide
theorem flags_fuel : ∀ a, flags a ≠ 34 := by decide
theorem flags_header : ∀ a, flags a ≠ 62 ∧ flags a ≠ 63 := by decide

def Counts (L n scratch : ℕ) (work : Fin 64 → Tape) : Prop :=
  ∀ i, IsReg (values L n scratch i) (work (StrictScheduleEntry.ports.index i))

def Header (original : List Bool) (work : Fin 64 → Tape) : Prop :=
  (work 62).head = 1 ∧ (work 62).read = Γ.ofBool (HeaderControl.valid original) ∧
    BoxBufferState.Stored (HeaderControl.copied original) (work 63)

def Spare (work : Fin 64 → Tape) : Prop :=
  ∀ j, (∀ i, j ≠ StrictScheduleEntry.ports.index i) → (∀ a, j ≠ flags a) →
    j ≠ 27 → j ≠ 62 → j ≠ 63 → IsReg 0 (work j)

def Kept (L n scratch : ℕ) (original : List Bool) (work : Fin 64 → Tape) : Prop :=
  Counts L n scratch work ∧ IsReg 0 (work 27) ∧ Spare work ∧ Header original work

theorem kept_flag_stable (L n scratch : ℕ) (original : List Bool) (work next : Fin 64 → Tape)
    (he : ∀ j, (∀ a, j ≠ flags a) → next j = work j) :
    Kept L n scratch original work → Kept L n scratch original next := by
  rintro ⟨hc, hz, hs, hh, hv, hb⟩
  exact ⟨fun i => by simpa only [he _ (counter_flags i)] using hc i,
    by simpa only [he 27 (fun a => (flags_scale a).symm)] using hz,
    fun j hi ha hd hf hb => by simpa only [he j ha] using hs j hi ha hd hf hb,
    by simpa only [he 62 (fun a => (flags_header a).1.symm)] using hh,
    by simpa only [he 62 (fun a => (flags_header a).1.symm)] using hv,
    by simpa only [he 63 (fun a => (flags_header a).2.symm)] using hb⟩

def Flagged (L n scratch : ℕ) (original before input emitted : List Bool) :
    _root_.Complexity.TM.TapePred 64 := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
    (∀ a, (work (flags a)).head = 1) ∧
    (∀ a, (work (flags a)).read = Γ.ofBool (flagValues a)) ∧ Kept L n scratch original work

theorem flags_hoareTime (L n scratch : ℕ) (original before input emitted : List Bool) :
    (FlagInitialization.machine flags flagValues).HoareTime
      (CounterProgramFrame.Logical StrictScheduleEntry.ports (values L n scratch) before input emitted
        (StrictScheduleEntry.Frame original))
      (Flagged L n scratch original before input emitted) 28 := by
  have h := FlagInitialization.hoareTime 14 flags flags_injective flagValues before input emitted
    (Kept L n scratch original) (kept_flag_stable L n scratch original)
  apply h.weaken_pre
  rintro inp work out ⟨hc, hs, hv, hfh, hfr, hb, hz⟩
  have hflags : ∀ a, IsReg 0 (work (flags a)) := fun a => hz _
    (fun i => (counter_flags i a).symm) (flags_header a).1 (flags_header a).2
  exact ⟨hc, hs, (fun a => (hflags a).head_eq), hv,
    hz 27 (fun i => (counter_scale i).symm) (by decide) (by decide),
    (fun j hi _ha _hd hf hb => hz j hi hf hb), hfh, hfr, hb⟩

def BuildKept (L n scratch : ℕ) (original : List Bool) (work : Fin 64 → Tape) : Prop :=
  (∀ i, i ≠ 6 → IsReg (values L n scratch i) (work (StrictScheduleEntry.ports.index i))) ∧
    (∀ a, (work (flags a)).head = 1) ∧
    (∀ a, (work (flags a)).read = Γ.ofBool (flagValues a)) ∧ Spare work ∧ Header original work

theorem build_kept_stable (L n scratch : ℕ) (original : List Bool) (work next : Fin 64 → Tape)
    (he : ∀ j, j ≠ 34 → j ≠ 27 → next j = work j) :
    BuildKept L n scratch original work → BuildKept L n scratch original next := by
  rintro ⟨hc, hh, hv, hs, hfh, hfr, hb⟩
  have hcounter (i : Fin 16) (hi : i ≠ 6) : StrictScheduleEntry.ports.index i ≠ 34 :=
    StrictScheduleEntry.ports.injective.ne hi
  exact ⟨fun i hi => by simpa only [he _ (hcounter i hi) (counter_scale i)] using hc i hi,
    (fun a => by simpa only [he _ (flags_fuel a) (flags_scale a)] using hh a),
    (fun a => by simpa only [he _ (flags_fuel a) (flags_scale a)] using hv a),
    (fun j hi ha hd hf hb => by simpa only [he j (hi 6) hd] using hs j hi ha hd hf hb),
    by simpa only [he 62 (by decide) (by decide)] using hfh,
    by simpa only [he 62 (by decide) (by decide)] using hfr,
    by simpa only [he 63 (by decide) (by decide)] using hb⟩

structure Ready (L n scratch : ℕ) (original : List Bool) (work : Fin 64 → Tape) : Prop where
  safe : ∀ j, Parked (work j)
  counts : Counts L n scratch work
  heads : ∀ a, (work (flags a)).head = 1
  bits : ∀ a, (work (flags a)).read = Γ.ofBool (flagValues a)
  scale : Register (n + SourcePolynomialSchedules.scaleLength L) (work 27)
  spare : Spare work
  header : Header original work

def machine : TM 64 := seqTM (FlagInitialization.machine flags flagValues) (UnaryBinaryBuild.machine 34 27)
def timeBound (L n : ℕ) : ℕ :=
  let S := n + SourcePolynomialSchedules.scaleLength L
  S * (2 * S + 6) + S + 31

theorem hoareTime (L n scratch : ℕ) (original before input emitted : List Bool) :
    machine.HoareTime
      (CounterProgramFrame.Logical StrictScheduleEntry.ports (values L n scratch) before input emitted
        (StrictScheduleEntry.Frame original))
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L n scratch original work)
      (timeBound L n) := by
  have hf := flags_hoareTime L n scratch original before input emitted
  have hb := UnaryBinaryBuildFramed.hoareTime (34 : Fin 64) 27 (by decide)
    (n + SourcePolynomialSchedules.scaleLength L) before input emitted (BuildKept L n scratch original)
    (build_kept_stable L n scratch original)
  have hs := seqTM_hoareTime _ _ hf (by
    rintro inp work out ⟨hc, hs, hh, hv, hcount, hz, hspare, hheader⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    have hraw : Register 0 (work 27) :=
      ⟨by simpa only [List.replicate_zero, Nat.zero_bits] using CountTape.string_of_register hz, hz.cell0⟩
    exact ⟨hc, hs, hcount 6, hraw, (fun i _ => hcount i), hh, hv, hspare, hheader⟩) hb
  exact hs.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hs, hfuel, hscale, hcount, hh, hv, hspare, hheader⟩
    have hcounts : Counts L n scratch work := by
      intro i
      by_cases hi : i = 6
      · subst i
        exact hfuel
      · exact hcount i hi
    exact ⟨hc, hs, hcounts, hh, hv, hscale, hspare, hheader⟩) (by dsimp only [timeBound]; omega)

def rowPorts : RowEnergyStep.Ports 63 where
  square := ⟨fun a => ⟨a.val, by omega⟩, fun a b h => Fin.ext (congrArg (fun z : Fin 64 => z.val) h)⟩
  active := 28
  active_ne_square := by
    intro a h
    have he := congrArg Fin.val h
    change 28 = a.val at he
    omega

def blanks : Fin 15 → Fin 64 := ![3, 4, 5, 9, 10, 11, 15, 16, 17, 22, 23, 25, 26, 42, 43]
theorem blanks_counter : ∀ b i, blanks b ≠ StrictScheduleEntry.ports.index i := by decide
theorem blanks_flags : ∀ b a, blanks b ≠ flags a := by decide
theorem blanks_scale : ∀ b, blanks b ≠ 27 := by decide
theorem blanks_header : ∀ b, blanks b ≠ 62 ∧ blanks b ≠ 63 := by decide

theorem blank_registers (L n scratch : ℕ) (original : List Bool) (work : Fin 64 → Tape)
    (h : Ready L n scratch original work) : ∀ b, IsReg 0 (work (blanks b)) := fun b =>
  h.spare _ (blanks_counter b) (blanks_flags b) (blanks_scale b) (blanks_header b).1 (blanks_header b).2

def state (before input emitted : List Bool) : RowEnergyControl.State :=
  ⟨⟨before, input, fun _ => ⟨false, [], fun _ => false, fun _ => []⟩, false⟩, true, emitted⟩

def width (L n : ℕ) : ℕ := 4 * (L + 2) + (n + SourcePolynomialSchedules.scaleLength L)

def Extra (L n scratch : ℕ) (original : List Bool) (work : Fin 64 → Tape) : Prop :=
  (∀ i, i ≠ 14 → i ≠ 15 → IsReg (values L n scratch i) (work (StrictScheduleEntry.ports.index i))) ∧
    IsReg 0 (work 42) ∧ IsReg 0 (work 43) ∧ Header original work

theorem flag_slot (i j : Fin 3) : rowPorts.square.row.flag i j =
    flags ⟨3 * i.val + j.val, by omega⟩ := by
  fin_cases i <;> fin_cases j <;> rfl

theorem presence_slot (i : Fin 3) : rowPorts.square.row.presence i =
    flags ⟨9 + i.val, by omega⟩ := by fin_cases i <;> rfl

theorem low_flag (a : Fin 14) (ha : a.val < 13) : flagValues a = false := by
  have he : a ≠ 13 := Fin.ne_of_val_ne (by change a.val ≠ 13; omega)
  simp only [flagValues, he, decide_false]

theorem row_ready (L n scratch : ℕ) (original before input emitted : List Bool)
    (work : Fin 64 → Tape) (h : Ready L n scratch original work) :
    RowEnergyStep.Ready rowPorts (state before input emitted)
      (n + SourcePolynomialSchedules.scaleLength L).bits (L + 2) (width L n)
      (Extra L n scratch original) work ∧ IsReg (L + 2) (work 29) := by
  have hz := blank_registers L n scratch original work h
  have hwords (i : Fin 3) (j : Fin 2) : IsReg 0 (work (rowPorts.square.row.word i j)) := by
    fin_cases i <;> fin_cases j
    · exact hz 0
    · exact hz 1
    · exact hz 3
    · exact hz 4
    · exact hz 6
    · exact hz 7
  have hcoeff (i : Fin 3) : IsReg 0 (work (rowPorts.square.row.coefficient i)) := by
    fin_cases i
    · exact hz 2
    · exact hz 5
    · exact hz 8
  have hextra : Extra L n scratch original work :=
    ⟨fun i _ _ => h.counts i, hz 13, hz 14, h.header⟩
  have hrow : EquationRowFrame.Ready rowPorts.square.row (state before input emitted).row (L + 2)
      (Extra L n scratch original) work := by
    refine ⟨h.safe, ?_, ?_, ?_, ?_, h.heads 12, h.bits 12, (hz 9).head_eq,
      BoxBufferState.of_register (Nat.zero_le _) (hz 10), h.counts 14, hextra⟩
    · intro i
      rw [presence_slot]
      exact ⟨h.heads _, by simp only [state]; rw [h.bits, low_flag _ (by dsimp; omega)]⟩
    · intro i j
      rw [flag_slot]
      exact ⟨h.heads _, by simp only [state]; rw [h.bits, low_flag _ (by dsimp; omega)]⟩
    · intro i j
      exact ⟨by simpa only [List.replicate_zero, state] using CountTape.string_of_register (hwords i j),
        (hwords i j).cell0, Nat.zero_le _⟩
    · intro i
      exact ⟨by simpa only [List.replicate_zero, state] using CountTape.string_of_register (hcoeff i),
        (hcoeff i).cell0, Nat.zero_le _⟩
  have hlen := BinaryIncrementControl.bits_length_le (n + SourcePolynomialSchedules.scaleLength L)
  have hsquare : RowSquareFrame.Ready rowPorts.square (state before input emitted).row
      (n + SourcePolynomialSchedules.scaleLength L).bits (L + 2) (width L n)
      (Extra L n scratch original) work :=
    ⟨hrow, h.scale.1, h.scale.2, by unfold width; omega, by unfold width; omega,
      BoxBufferState.of_register (Nat.zero_le _) (hz 11), (hz 12).head_eq⟩
  exact ⟨⟨hsquare, h.heads 13, h.bits 13⟩, h.counts 15⟩

end JointThermoComplexity.Complexity.StrictRowInitialization

#print axioms JointThermoComplexity.Complexity.StrictRowInitialization.flags_hoareTime
#print axioms JointThermoComplexity.Complexity.StrictRowInitialization.hoareTime
#print axioms JointThermoComplexity.Complexity.StrictRowInitialization.row_ready
