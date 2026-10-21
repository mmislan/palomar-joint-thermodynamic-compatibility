module
public import proofs.JointThermoComplexity.Complexity.CountedSparseTermBody
public import proofs.JointThermoComplexity.Complexity.CountedSparseControl
public import proofs.JointThermoComplexity.Complexity.SparseOffsetMarkedStep

set_option autoImplicit false
@[expose] public section

/-! An actual marked step carries offset and normalized-row count together. -/

namespace JointThermoComplexity.Complexity.CountedMarkedStep
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork)
open SparseOffsetPorts
open CountedSparseControl (State)

def Stable (R : (Fin 32 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, 16 ≤ j.val → j ≠ rows → next j = work j) → R work → R next

def Fields (L A N : ℕ) (R : (Fin 32 → Tape) → Prop) (work : Fin 33 → Tape) : Prop :=
  SparseTermOffsetBody.Fields L layout A R work ∧ Register N (work rows.castSucc)

def Inv (L : ℕ) (emitted : List Bool) (R : (Fin 32 → Tape) → Prop) (s : State) :
    _root_.Complexity.TM.TapePred 33 := fun inp work out =>
  Cursor s.base.before s.base.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
    Fields L s.base.offset s.rows R work ∧ (work marker.castSucc).head = 1 ∧
      (work marker.castSucc).read = Γ.ofBool s.base.running

theorem old_stable (R : (Fin 32 → Tape) → Prop) (hR : Stable R) : SparseOffsetMarkedStep.Stable R :=
  fun work next he => hR work next (fun j hj _ => he j hj)

theorem count_stable (R : (Fin 32 → Tape) → Prop) (hR : Stable R) : CountedSparseFrame.Stable R :=
  fun work next he => hR work next (fun j _ hj => he j hj)

def choose (boxed : Bool) : TM 33 :=
  WorkSymbolBranch.machine Γ.one marker.castSucc (CountedSparseTermBody.machine boxed) (emitBitsTM [])

def active (boxed : Bool) : TM 33 := seqTM (SourceBitRead.machine marker.castSucc layout.flag.castSucc) (choose boxed)

def machine (boxed : Bool) : TM 33 := WorkSymbolBranch.machine Γ.one marker.castSucc (active boxed) (emitBitsTM [])

def bound (L C B : ℕ) : ℕ := 75 * L + 733 + OffsetTemplateProgram.bound 16 L C + 32 * B

theorem active_hoareTime (boxed : Bool) (L C B : ℕ) (emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) (hR : Stable R) (s : State) (hrun : s.base.running = true)
    (hlen : s.base.input.length ≤ L) (hA : s.base.offset.bits.length ≤ C) (hN : s.rows.bits.length ≤ B) :
    (active boxed).HoareTime (Inv L emitted R s)
      (Inv L emitted R (CountedSparseControl.step boxed s)) (bound L C B - 1) := by
  let S : (Fin 32 → Tape) → Prop := fun work => R work ∧ Register s.rows (work rows)
  have hS : SparseOffsetMarkedStep.Stable S := by
    rintro work next he ⟨hr, hn⟩
    exact ⟨old_stable R hR work next he hr, by rw [he rows (by decide)]; exact hn⟩
  have hread := SourceBitRead.hoareTime marker.castSucc layout.flag.castSucc (by decide)
    s.base.before s.base.input emitted (SparseOffsetMarkedStep.restFields L s.base.offset S)
    (SparseOffsetMarkedStep.rest_stable L s.base.offset S hS)
  let nextBefore := s.base.before ++ BooleanMachine.copied s.base.input
  let raw := BooleanMachine.suffix s.base.input
  let P : (Fin 33 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ Fields L s.base.offset s.rows R work ∧
    (work marker.castSucc).head = 1 ∧ (work marker.castSucc).read = Γ.ofBool (SourceBitRead.value s.base.input)
  have hchoose : (choose boxed).HoareTime
      (fun inp work out => Cursor nextBefore raw emitted inp work out ∧ P work)
      (Inv L emitted R (CountedSparseControl.step boxed s))
      (75 * L + 728 + OffsetTemplateProgram.bound 16 L C + 32 * B) := by
    cases hv : SourceBitRead.value s.base.input with
    | false =>
      have hn := BoundedOccurrenceMachine.noop_hoareTime nextBefore raw emitted P
      have hb := WorkSymbolBranch.no_hoareTime Γ.one marker.castSucc (CountedSparseTermBody.machine boxed)
        (emitBitsTM []) nextBefore raw emitted nextBefore raw emitted P P 0 hn
      apply hb.consequence
      · rintro inp work out ⟨hc, hs, hf, hh, hv'⟩
        exact ⟨⟨hc, hs, hf, hh, hv'⟩, by rw [hv', hv]; decide⟩
      · rintro inp work out ⟨hc, hs, hf, hh, hv'⟩
        simpa only [Inv, CountedSparseControl.step, CountedSparseControl.increment,
          SparseOffsetLoopControl.step, hrun, hv, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using
          (show Inv L emitted R ⟨⟨false, nextBefore, raw, s.base.offset⟩, s.rows⟩ inp work out from
            ⟨hc, hs, hf, hh, by simpa only [hv] using hv'⟩)
      · omega
    | true =>
      let T : (Fin 32 → Tape) → Prop := fun work => R work ∧ (work marker).head = 1 ∧ (work marker).read = Γ.one
      have hT : SparseOffsetLayout.Stable layout T := by
        rintro work next he ⟨hx, hh, hv'⟩
        have hn := marker_outside
        have hm := he marker hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2
        exact ⟨SparseOffsetMarkedStep.body_stable R (old_stable R hR) work next he hx,
          by rw [hm]; exact hh, by rw [hm]; exact hv'⟩
      have hTr : CountedSparseFrame.Stable T := by
        rintro work next he ⟨hx, hh, hv'⟩
        exact ⟨count_stable R hR work next he hx, by rw [he marker (by decide)]; exact hh,
          by rw [he marker (by decide)]; exact hv'⟩
      have hraw : raw.length ≤ L := (show raw.length ≤ s.base.input.length from by
        cases hi : s.base.input <;> simp [raw, hi, BooleanMachine.suffix]).trans hlen
      have ht := CountedSparseTermBody.hoareTime boxed L s.base.offset C s.rows B nextBefore raw emitted hraw hA hN T hT hTr
      let Q : (Fin 33 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧
        Fields L (s.base.offset + SparseTermOffsetControl.delta boxed raw) (s.rows + SparseTermOffsetControl.count raw) R work ∧
          (work marker.castSucc).head = 1 ∧ (work marker.castSucc).read = Γ.one
      have ht' : (CountedSparseTermBody.machine boxed).HoareTime
          (fun inp work out => Cursor nextBefore raw emitted inp work out ∧ P work)
          (fun inp work out => Cursor (nextBefore ++ SparseTermOffsetControl.taken raw)
            (SparseTermOffsetControl.rest raw) emitted inp work out ∧ Q work)
          (75 * L + 726 + OffsetTemplateProgram.bound 16 L C + 32 * B) := by
        apply ht.consequence
        · rintro inp work out ⟨hc, hs, ⟨hfields, hn⟩, hmh, hmr⟩
          rcases hfields with ⟨hready, hh, ha, hu, hl, hx⟩
          exact ⟨⟨hc, hs, hready, hh, ha, hu, hl, hx, hmh, by simpa only [hv, Γ.ofBool, oldWork] using hmr⟩, hn⟩
        · rintro inp work out ⟨⟨⟨hc, hs, hready, hh, ha, hu, hl, hx, hmh, hmr⟩, _⟩, hn⟩
          exact ⟨hc, hs, ⟨⟨hready, hh, ha, hu, hl, hx⟩, hn⟩, hmh, hmr⟩
        · exact le_rfl
      have hb := WorkSymbolBranch.yes_hoareTime Γ.one marker.castSucc (CountedSparseTermBody.machine boxed)
        (emitBitsTM []) nextBefore raw emitted (nextBefore ++ SparseTermOffsetControl.taken raw)
        (SparseTermOffsetControl.rest raw) emitted P Q _ ht'
      apply hb.consequence
      · rintro inp work out ⟨hc, hs, hf, hh, hv'⟩
        exact ⟨⟨hc, hs, hf, hh, hv'⟩, by simpa only [hv, Γ.ofBool] using hv'⟩
      · rintro inp work out ⟨hc, hs, hf, hh, hv'⟩
        simpa only [Inv, CountedSparseControl.step, CountedSparseControl.increment,
          SparseOffsetLoopControl.step, hrun, hv, ↓reduceIte] using
          (show Inv L emitted R ⟨⟨true, nextBefore ++ SparseTermOffsetControl.taken raw,
            SparseTermOffsetControl.rest raw, s.base.offset + SparseTermOffsetControl.delta boxed raw⟩,
              s.rows + SparseTermOffsetControl.count raw⟩ inp work out from ⟨hc, hs, hf, hh, hv'⟩)
      · omega
  have hf := seqTM_hoareTime _ _ hread (by
    rintro inp work out ⟨hc, hs, hh, hfh, hv, _hav, hrest⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    have hp := (SparseOffsetMarkedStep.fields_parts L s.base.offset S work).mpr ⟨hrest, hfh⟩
    rcases hp with ⟨hready, hadj, hacc, haux, hlast, hx, hn⟩
    exact ⟨hc, hs, ⟨⟨hready, hadj, hacc, haux, hlast, hx⟩, hn⟩, hh, hv⟩) hchoose
  apply hf.consequence
  · rintro inp work out ⟨hc, hs, ⟨hfields, hn⟩, hh, _⟩
    rcases hfields with ⟨hready, hadj, hacc, haux, hlast, hx⟩
    have hp : SparseTermOffsetBody.Fields L layout s.base.offset S work :=
      ⟨hready, hadj, hacc, haux, hlast, hx, hn⟩
    have hp' := (SparseOffsetMarkedStep.fields_parts L s.base.offset S work).mp hp
    exact ⟨hc, hs, hh, hp'.2, hp'.1⟩
  · exact fun _ _ _ hp => hp
  · unfold bound; omega

theorem hoareTime (boxed : Bool) (L C B : ℕ) (emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) (hR : Stable R) (s : State)
    (hlen : s.base.input.length ≤ L) (hA : s.base.offset.bits.length ≤ C) (hN : s.rows.bits.length ≤ B) :
    (machine boxed).HoareTime (Inv L emitted R s)
      (Inv L emitted R (CountedSparseControl.step boxed s)) (bound L C B) := by
  let P : (Fin 33 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ Fields L s.base.offset s.rows R work ∧
    (work marker.castSucc).head = 1 ∧ (work marker.castSucc).read = Γ.ofBool s.base.running
  cases hr : s.base.running with
  | false =>
    have hn := BoundedOccurrenceMachine.noop_hoareTime s.base.before s.base.input emitted P
    have hb := WorkSymbolBranch.no_hoareTime Γ.one marker.castSucc (active boxed) (emitBitsTM [])
      s.base.before s.base.input emitted s.base.before s.base.input emitted P P 0 hn
    apply hb.consequence
    · rintro inp work out ⟨hc, hs, hf, hh, hv⟩
      exact ⟨⟨hc, hs, hf, hh, hv⟩, by rw [hv, hr]; decide⟩
    · rintro inp work out hp
      change Inv L emitted R s inp work out at hp
      rw [CountedSparseControl.step_stopped boxed s hr]
      exact hp
    · unfold bound; omega
  | true =>
    have ht := active_hoareTime boxed L C B emitted R hR s hr hlen hA hN
    have hb := WorkSymbolBranch.yes_hoareTime Γ.one marker.castSucc (active boxed) (emitBitsTM [])
      s.base.before s.base.input emitted (CountedSparseControl.step boxed s).base.before
      (CountedSparseControl.step boxed s).base.input emitted P
      (fun work => (∀ j, Parked (work j)) ∧
        Fields L (CountedSparseControl.step boxed s).base.offset (CountedSparseControl.step boxed s).rows R work ∧
          (work marker.castSucc).head = 1 ∧ (work marker.castSucc).read = Γ.ofBool (CountedSparseControl.step boxed s).base.running)
      (bound L C B - 1) ht
    apply hb.consequence
    · rintro inp work out ⟨hc, hs, hf, hh, hv⟩
      exact ⟨⟨hc, hs, hf, hh, hv⟩, by simpa only [hr, Γ.ofBool] using hv⟩
    · exact fun _ _ _ hp => hp
    · unfold bound; omega

end JointThermoComplexity.Complexity.CountedMarkedStep

#print axioms JointThermoComplexity.Complexity.CountedMarkedStep.machine
#print axioms JointThermoComplexity.Complexity.CountedMarkedStep.hoareTime
