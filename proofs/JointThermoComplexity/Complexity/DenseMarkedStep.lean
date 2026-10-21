module
public import proofs.JointThermoComplexity.Complexity.DenseMarkedFrame

set_option autoImplicit false
@[expose] public section

/-! Actual source-list token dispatch and packet emission. The counted prefix is
logical control; previously computed physical offset and total remain framed. -/

namespace JointThermoComplexity.Complexity.DenseMarkedStep
open _root_.Complexity _root_.Complexity.TM HeaderAt
open CountedSparseControl (State)
open DenseMarkedFrame

def choose (boxed right : Bool) : TM 64 :=
  WorkSymbolBranch.machine Γ.one 15 (DenseLoadedPacket.machine boxed right) (emitBitsTM [])
def active (boxed right : Bool) : TM 64 := seqTM (SourceBitRead.machine 15 11) (choose boxed right)
def machine (boxed right : Bool) : TM 64 :=
  WorkSymbolBranch.machine Γ.one 15 (active boxed right) (emitBitsTM [])
def bound (boxed right : Bool) (L n N B : ℕ) : ℕ := DenseLoadedPacket.timeBound boxed right L n N B + 6

theorem core_frame (n N current : ℕ) (R S : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape)
    (hp : DenseSourceFrame.Core n N current R work) (hs : S work) : DenseSourceFrame.Core n N current S work :=
  ⟨hp.adjusted, hp.arity, hp.total, hp.branch, hp.position, hp.next, hp.cell,
    hp.comparison, hp.ending, hp.lastHead, hp.powers, hp.scratch, hs⟩

theorem active_hoareTime (boxed right : Bool) (L n N B : ℕ) (emitted : List Bool)
    (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (s : State) (hrun : s.base.running = true)
    (hlen : s.base.input.length ≤ L) (hLB : L ≤ B) (hbase : N + 2 ≤ B)
    (hfit : (CountedSparseControl.step boxed s).rows ≤ N) :
    (active boxed right).HoareTime (DenseMarkedFrame.Inv L n N emitted R s)
      (DenseMarkedFrame.Inv L n N (emitted ++ DenseMarkedControl.word boxed right n N s) R (CountedSparseControl.step boxed s))
      (DenseLoadedPacket.timeBound boxed right L n N B + 4) := by
  have hread := SourceBitRead.hoareTime (15 : Fin 64) 11 (by decide) s.base.before s.base.input emitted
    (Rest L n N (2 + s.rows) R) (rest_stable L n N (2 + s.rows) R hR)
  let nextBefore := s.base.before ++ BooleanMachine.copied s.base.input
  let raw := BooleanMachine.suffix s.base.input
  let P : (Fin 64 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧
    DenseSourceFrame.Work L n N (2 + s.rows) R work ∧ Status (SourceBitRead.value s.base.input) work
  have hchoose : (choose boxed right).HoareTime
      (fun inp work out => Cursor nextBefore raw emitted inp work out ∧ P work)
      (DenseMarkedFrame.Inv L n N (emitted ++ DenseMarkedControl.word boxed right n N s) R (CountedSparseControl.step boxed s))
      (DenseLoadedPacket.timeBound boxed right L n N B + 2) := by
    cases hv : SourceBitRead.value s.base.input with
    | false =>
      have hn := BoundedOccurrenceMachine.noop_hoareTime nextBefore raw emitted P
      have hb := WorkSymbolBranch.no_hoareTime Γ.one (15 : Fin 64) (DenseLoadedPacket.machine boxed right)
        (emitBitsTM []) nextBefore raw emitted nextBefore raw emitted P P 0 hn
      apply hb.consequence
      · rintro inp work out ⟨hc, hs, hf, hh, hv'⟩
        exact ⟨⟨hc, hs, hf, hh, hv'⟩, by rw [hv', hv]; decide⟩
      · rintro inp work out ⟨hc, hs, hf, hh, hv'⟩
        simpa only [DenseMarkedFrame.Inv, DenseMarkedControl.word, CountedSparseControl.step, CountedSparseControl.increment,
          SparseOffsetLoopControl.step, hrun, hv, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, List.append_nil] using
          (show DenseMarkedFrame.Inv L n N emitted R ⟨⟨false, nextBefore, raw, s.base.offset⟩, s.rows⟩ inp work out from
            ⟨hc, hs, hf, hh, by simpa only [hv] using hv'⟩)
      · omega
    | true =>
      let T : (Fin 64 → Tape) → Prop := fun work => R work ∧ Status true work
      have hraw : raw.length ≤ L := (show raw.length ≤ s.base.input.length from by
        cases hi : s.base.input <;> simp [raw, hi, BooleanMachine.suffix]).trans hlen
      have ht := DenseLoadedPacket.hoareTime boxed right L n N B (2 + s.rows) nextBefore raw emitted
        hraw hLB hbase (DenseMarkedControl.step_fit boxed s N hfit hrun hv) T (body_stable true R hR)
      let Q : (Fin 64 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧
        DenseSourceFrame.Work L n N (2 + s.rows + SparseTermOffsetControl.count raw) R work ∧ Status true work
      have ht' : (DenseLoadedPacket.machine boxed right).HoareTime
          (fun inp work out => Cursor nextBefore raw emitted inp work out ∧ P work)
          (fun inp work out => Cursor (nextBefore ++ SparseTermOffsetControl.taken raw)
            (SparseTermOffsetControl.rest raw) (emitted ++ DenseLoadedPacket.word boxed right n N (2 + s.rows) raw) inp work out ∧ Q work)
          (DenseLoadedPacket.timeBound boxed right L n N B) := by
        apply ht.consequence
        · rintro inp work out ⟨hc, hs, ⟨hp, hcore⟩, hh, hr⟩
          have hstatus : Status true work := ⟨hh, by simpa only [hv] using hr⟩
          exact ⟨hc, hs, hp, core_frame n N (2 + s.rows) R T work hcore ⟨hcore.frame, hstatus⟩⟩
        · rintro inp work out ⟨hc, hs, hp, hcore⟩
          exact ⟨hc, hs, ⟨hp, core_frame n N _ T R work hcore hcore.frame.1⟩, hcore.frame.2⟩
        · exact le_rfl
      have hb := WorkSymbolBranch.yes_hoareTime Γ.one (15 : Fin 64) (DenseLoadedPacket.machine boxed right)
        (emitBitsTM []) nextBefore raw emitted (nextBefore ++ SparseTermOffsetControl.taken raw)
        (SparseTermOffsetControl.rest raw) (emitted ++ DenseLoadedPacket.word boxed right n N (2 + s.rows) raw) P Q _ ht'
      apply hb.consequence
      · rintro inp work out ⟨hc, hs, hf, hh, hv'⟩
        exact ⟨⟨hc, hs, hf, hh, hv'⟩, by simpa only [hv, Γ.ofBool] using hv'⟩
      · rintro inp work out ⟨hc, hs, hf, hstatus⟩
        have hwork : DenseSourceFrame.Work L n N (2 + (s.rows + SparseTermOffsetControl.count raw)) R work := by
          simpa only [Nat.add_assoc] using hf
        simpa only [DenseMarkedFrame.Inv, DenseMarkedControl.word, CountedSparseControl.step, CountedSparseControl.increment,
          SparseOffsetLoopControl.step, hrun, hv, ↓reduceIte] using
          (show DenseMarkedFrame.Inv L n N (emitted ++ DenseLoadedPacket.word boxed right n N (2 + s.rows) raw) R
            ⟨⟨true, nextBefore ++ SparseTermOffsetControl.taken raw, SparseTermOffsetControl.rest raw,
              s.base.offset + SparseTermOffsetControl.delta boxed raw⟩, s.rows + SparseTermOffsetControl.count raw⟩ inp work out from
            ⟨hc, hs, hwork, hstatus⟩)
      · omega
  have hf := seqTM_hoareTime _ _ hread (by
    rintro inp work out ⟨hc, hs, hh, hfh, hv, _hav, hrest⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, (rest_iff L n N (2 + s.rows) R work).mpr ⟨hrest, hfh⟩, hh, hv⟩) hchoose
  apply hf.consequence
  · rintro inp work out ⟨hc, hs, hwork, hh, _⟩
    have hp := (rest_iff L n N (2 + s.rows) R work).mp hwork
    exact ⟨hc, hs, hh, hp.2, hp.1⟩
  · exact fun _ _ _ hp => hp
  · omega

theorem hoareTime (boxed right : Bool) (L n N B : ℕ) (emitted : List Bool)
    (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (s : State)
    (hlen : s.base.input.length ≤ L) (hLB : L ≤ B) (hbase : N + 2 ≤ B)
    (hfit : (CountedSparseControl.step boxed s).rows ≤ N) :
    (machine boxed right).HoareTime (DenseMarkedFrame.Inv L n N emitted R s)
      (DenseMarkedFrame.Inv L n N (emitted ++ DenseMarkedControl.word boxed right n N s) R (CountedSparseControl.step boxed s))
      (bound boxed right L n N B) := by
  let P : (Fin 64 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧
    DenseSourceFrame.Work L n N (2 + s.rows) R work ∧ Status s.base.running work
  cases hr : s.base.running with
  | false =>
    have hn := BoundedOccurrenceMachine.noop_hoareTime s.base.before s.base.input emitted P
    have hb := WorkSymbolBranch.no_hoareTime Γ.one (15 : Fin 64) (active boxed right) (emitBitsTM [])
      s.base.before s.base.input emitted s.base.before s.base.input emitted P P 0 hn
    apply hb.consequence
    · rintro inp work out ⟨hc, hs, hf, hh, hv⟩
      exact ⟨⟨hc, hs, hf, hh, hv⟩, by rw [hv, hr]; decide⟩
    · rintro inp work out hp
      change DenseMarkedFrame.Inv L n N emitted R s inp work out at hp
      simpa only [CountedSparseControl.step_stopped boxed s hr, DenseMarkedControl.word, hr,
        Bool.false_eq_true, ↓reduceIte, List.append_nil] using hp
    · unfold bound; omega
  | true =>
    have ht := active_hoareTime boxed right L n N B emitted R hR s hr hlen hLB hbase hfit
    let Q : (Fin 64 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧
      DenseSourceFrame.Work L n N (2 + (CountedSparseControl.step boxed s).rows) R work ∧
        Status (CountedSparseControl.step boxed s).base.running work
    have hb := WorkSymbolBranch.yes_hoareTime Γ.one (15 : Fin 64) (active boxed right) (emitBitsTM [])
      s.base.before s.base.input emitted (CountedSparseControl.step boxed s).base.before
      (CountedSparseControl.step boxed s).base.input (emitted ++ DenseMarkedControl.word boxed right n N s) P Q _ ht
    apply hb.consequence
    · rintro inp work out ⟨hc, hs, hf, hh, hv⟩
      exact ⟨⟨hc, hs, hf, hh, hv⟩, by simpa only [hr, Γ.ofBool] using hv⟩
    · exact fun _ _ _ hp => hp
    · unfold bound; omega

end JointThermoComplexity.Complexity.DenseMarkedStep

#print axioms JointThermoComplexity.Complexity.DenseMarkedStep.hoareTime
