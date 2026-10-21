module
public import proofs.JointThermoComplexity.Complexity.SparseOffsetPorts
public import proofs.JointThermoComplexity.Complexity.SparseOffsetLoopControl
public import proofs.JointThermoComplexity.Complexity.SparseTermOffsetBody

set_option autoImplicit false
@[expose] public section

/-! Actual marked iteration, preserving all work tapes from sixteen onward. -/

namespace JointThermoComplexity.Complexity.SparseOffsetMarkedStep
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState BinaryIncrementRun
open BinaryScaleBuffer (oldWork)
open SparseOffsetPorts
open SparseOffsetLoopControl (State)
open OffsetContribution (Empty)

def Stable (R : (Fin 32 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, 16 ≤ j.val → next j = work j) → R work → R next

def Fields (L A : ℕ) (R : (Fin 32 → Tape) → Prop) := SparseTermOffsetBody.Fields L layout A R

def Inv (L : ℕ) (emitted : List Bool) (R : (Fin 32 → Tape) → Prop) (s : State) :
    _root_.Complexity.TM.TapePred 33 := fun inp work out =>
  Cursor s.before s.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Fields L s.offset R work ∧
    (work marker.castSucc).head = 1 ∧ (work marker.castSucc).read = Γ.ofBool s.running

def restFields (L A : ℕ) (R : (Fin 32 → Tape) → Prop) (work : Fin 33 → Tape) : Prop :=
  Reusable L (work layout.idx.castSucc) ∧ (work layout.sign.castSucc).head = 1 ∧
    (∀ p ∈ slots, Reusable L (work p.1.castSucc) ∧ (work p.2.castSucc).head = 1) ∧
    (work layout.ending.castSucc).head = 1 ∧ (work layout.adjusted.castSucc).head = 1 ∧
    Register A (work layout.acc.castSucc) ∧ Empty (work layout.aux.castSucc) ∧
    Empty (work (Fin.last 32)) ∧ R (oldWork work)

theorem fields_parts (L A : ℕ) (R : (Fin 32 → Tape) → Prop) (work : Fin 33 → Tape) :
    Fields L A R work ↔ restFields L A R work ∧ (work layout.flag.castSucc).head = 1 := by
  constructor
  · rintro ⟨⟨hi, hs, hp, hend, hf⟩, hh, ha, hu, hl, hr⟩
    exact ⟨⟨hi, hs, hp, hend, hh, ha, hu, hl, hr⟩, hf⟩
  · rintro ⟨⟨hi, hs, hp, hend, hh, ha, hu, hl, hr⟩, hf⟩
    exact ⟨⟨hi, hs, hp, hend, hf⟩, hh, ha, hu, hl, hr⟩

theorem high_ne (j k : Fin 32) (hj : 16 ≤ j.val) (hk : k.val < 16) : j.castSucc ≠ k.castSucc := by
  intro he
  have hv := congrArg (fun x : Fin 33 => x.val) he
  change j.val = k.val at hv
  omega

theorem body_stable (R : (Fin 32 → Tape) → Prop) (hR : Stable R) : SparseOffsetLayout.Stable layout R := by
  intro work next he hr
  apply hR work next _ hr
  intro j hj
  have hn := protected_outside j hj
  exact he j hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2

theorem rest_stable (L A : ℕ) (R : (Fin 32 → Tape) → Prop) (hR : Stable R) :
    ∀ work next, (∀ j, j ≠ marker.castSucc → j ≠ layout.flag.castSucc → next j = work j) →
      restFields L A R work → restFields L A R next := by
  rintro work next he ⟨hi, hs, hp, hend, hh, ha, hu, hl, hr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he layout.idx.castSucc (by decide) (by decide)]; exact hi
  · rw [he layout.sign.castSucc (by decide) (by decide)]; exact hs
  · intro p hmem
    have hm : p ∈ [(2, 6), (3, 7), (4, 8), (5, 9)] := hmem
    simp at hm
    have hdata : p.1.castSucc ≠ marker.castSucc ∧ p.1.castSucc ≠ layout.flag.castSucc := by
      rcases hm with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
    have hmark : p.2.castSucc ≠ marker.castSucc ∧ p.2.castSucc ≠ layout.flag.castSucc := by
      rcases hm with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
    rw [he p.1.castSucc hdata.1 hdata.2, he p.2.castSucc hmark.1 hmark.2]
    exact hp p hmem
  · rw [he layout.ending.castSucc (by decide) (by decide)]; exact hend
  · rw [he layout.adjusted.castSucc (by decide) (by decide)]; exact hh
  · rw [he layout.acc.castSucc (by decide) (by decide)]; exact ha
  · rw [he layout.aux.castSucc (by decide) (by decide)]; exact hu
  · rw [he (Fin.last 32) (by decide) (by decide)]; exact hl
  · exact hR _ _ (fun j hj => he j.castSucc (high_ne j marker hj (by decide))
      (high_ne j layout.flag hj (by decide))) hr

def choose (boxed : Bool) : TM 33 :=
  WorkSymbolBranch.machine Γ.one marker.castSucc (SparseTermOffsetBody.machine boxed layout) (emitBitsTM [])

def active (boxed : Bool) : TM 33 := seqTM (SourceBitRead.machine marker.castSucc layout.flag.castSucc) (choose boxed)

def machine (boxed : Bool) : TM 33 := WorkSymbolBranch.machine Γ.one marker.castSucc (active boxed) (emitBitsTM [])

def bound (L C : ℕ) : ℕ := 75 * L + 133 + OffsetTemplateProgram.bound 16 L C

theorem active_hoareTime (boxed : Bool) (L C : ℕ) (emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) (hR : Stable R) (s : State) (hrun : s.running = true)
    (hlen : s.input.length ≤ L) (hA : s.offset.bits.length ≤ C) :
    (active boxed).HoareTime (Inv L emitted R s)
      (Inv L emitted R (SparseOffsetLoopControl.step boxed s)) (bound L C - 1) := by
  have hread := SourceBitRead.hoareTime marker.castSucc layout.flag.castSucc (by decide)
    s.before s.input emitted (restFields L s.offset R) (rest_stable L s.offset R hR)
  let nextBefore := s.before ++ BooleanMachine.copied s.input
  let raw := BooleanMachine.suffix s.input
  let P : (Fin 33 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ Fields L s.offset R work ∧
    (work marker.castSucc).head = 1 ∧ (work marker.castSucc).read = Γ.ofBool (SourceBitRead.value s.input)
  have hchoose : (choose boxed).HoareTime
      (fun inp work out => Cursor nextBefore raw emitted inp work out ∧ P work)
      (Inv L emitted R (SparseOffsetLoopControl.step boxed s))
      (75 * L + 128 + OffsetTemplateProgram.bound 16 L C) := by
    cases hv : SourceBitRead.value s.input with
    | false =>
      have hn := BoundedOccurrenceMachine.noop_hoareTime nextBefore raw emitted P
      have hb := WorkSymbolBranch.no_hoareTime Γ.one marker.castSucc (SparseTermOffsetBody.machine boxed layout)
        (emitBitsTM []) nextBefore raw emitted nextBefore raw emitted P P 0 hn
      apply hb.consequence
      · rintro inp work out ⟨hc, hs, hf, hh, hv'⟩
        exact ⟨⟨hc, hs, hf, hh, hv'⟩, by rw [hv', hv]; decide⟩
      · rintro inp work out ⟨hc, hs, hf, hh, hv'⟩
        simpa only [Inv, SparseOffsetLoopControl.step, hrun, hv, Bool.false_eq_true, ↓reduceIte] using
          (show Inv L emitted R ⟨false, nextBefore, raw, s.offset⟩ inp work out from
            ⟨hc, hs, hf, hh, by simpa only [hv] using hv'⟩)
      · omega
    | true =>
      let T : (Fin 32 → Tape) → Prop := fun work => R work ∧ (work marker).head = 1 ∧ (work marker).read = Γ.one
      have hT : SparseOffsetLayout.Stable layout T := by
        rintro work next he ⟨hx, hh, hv'⟩
        have hn := marker_outside
        have hm := he marker hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2
        exact ⟨body_stable R hR work next he hx, by rw [hm]; exact hh, by rw [hm]; exact hv'⟩
      have hraw : raw.length ≤ L := (show raw.length ≤ s.input.length from by
        cases hi : s.input <;> simp [raw, hi, BooleanMachine.suffix]).trans hlen
      have ht := SparseTermOffsetBody.hoareTime boxed layout L s.offset C nextBefore raw emitted hraw hA T hT
      let Q : (Fin 33 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧
        Fields L (s.offset + SparseTermOffsetControl.delta boxed raw) R work ∧
          (work marker.castSucc).head = 1 ∧ (work marker.castSucc).read = Γ.one
      have ht' : (SparseTermOffsetBody.machine boxed layout).HoareTime
          (fun inp work out => Cursor nextBefore raw emitted inp work out ∧ P work)
          (fun inp work out => Cursor (nextBefore ++ SparseTermOffsetControl.taken raw)
            (SparseTermOffsetControl.rest raw) emitted inp work out ∧ Q work)
          (75 * L + 126 + OffsetTemplateProgram.bound 16 L C) := by
        apply ht.consequence
        · rintro inp work out ⟨hc, hs, hfields, hmh, hmr⟩
          rcases hfields with ⟨hready, hh, ha, hu, hl, hx⟩
          exact ⟨hc, hs, hready, hh, ha, hu, hl, hx, hmh, by simpa only [hv, Γ.ofBool, oldWork] using hmr⟩
        · rintro inp work out ⟨⟨hc, hs, hready, hh, ha, hu, hl, hx, hmh, hmr⟩, _⟩
          exact ⟨hc, hs, ⟨hready, hh, ha, hu, hl, hx⟩, hmh, hmr⟩
        · exact le_rfl
      have hb := WorkSymbolBranch.yes_hoareTime Γ.one marker.castSucc (SparseTermOffsetBody.machine boxed layout)
        (emitBitsTM []) nextBefore raw emitted (nextBefore ++ SparseTermOffsetControl.taken raw)
        (SparseTermOffsetControl.rest raw) emitted P Q _ ht'
      apply hb.consequence
      · rintro inp work out ⟨hc, hs, hf, hh, hv'⟩
        exact ⟨⟨hc, hs, hf, hh, hv'⟩, by simpa only [hv, Γ.ofBool] using hv'⟩
      · rintro inp work out ⟨hc, hs, hf, hh, hv'⟩
        simpa only [Inv, SparseOffsetLoopControl.step, hrun, hv, ↓reduceIte] using
          (show Inv L emitted R ⟨true, nextBefore ++ SparseTermOffsetControl.taken raw,
            SparseTermOffsetControl.rest raw, s.offset + SparseTermOffsetControl.delta boxed raw⟩ inp work out from
            ⟨hc, hs, hf, hh, hv'⟩)
      · omega
  have hf := seqTM_hoareTime _ _ hread (by
    rintro inp work out ⟨hc, hs, hh, hfh, hv, _hav, hrest⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, (fields_parts L s.offset R work).mpr ⟨hrest, hfh⟩, hh, hv⟩) hchoose
  apply hf.consequence
  · rintro inp work out ⟨hc, hs, hfields, hh, _⟩
    have hp := (fields_parts L s.offset R work).mp hfields
    exact ⟨hc, hs, hh, hp.2, hp.1⟩
  · exact fun _ _ _ hp => hp
  · unfold bound
    omega

theorem hoareTime (boxed : Bool) (L C : ℕ) (emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) (hR : Stable R) (s : State)
    (hlen : s.input.length ≤ L) (hA : s.offset.bits.length ≤ C) :
    (machine boxed).HoareTime (Inv L emitted R s)
      (Inv L emitted R (SparseOffsetLoopControl.step boxed s)) (bound L C) := by
  let P : (Fin 33 → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ Fields L s.offset R work ∧
    (work marker.castSucc).head = 1 ∧ (work marker.castSucc).read = Γ.ofBool s.running
  cases hr : s.running with
  | false =>
    have hn := BoundedOccurrenceMachine.noop_hoareTime s.before s.input emitted P
    have hb := WorkSymbolBranch.no_hoareTime Γ.one marker.castSucc (active boxed) (emitBitsTM [])
      s.before s.input emitted s.before s.input emitted P P 0 hn
    apply hb.consequence
    · rintro inp work out ⟨hc, hs, hf, hh, hv⟩
      exact ⟨⟨hc, hs, hf, hh, hv⟩, by rw [hv, hr]; decide⟩
    · rintro inp work out hp
      change Inv L emitted R s inp work out at hp
      simpa only [SparseOffsetLoopControl.step, hr, Bool.false_eq_true, ↓reduceIte] using hp
    · unfold bound; omega
  | true =>
    have ht := active_hoareTime boxed L C emitted R hR s hr hlen hA
    have hb := WorkSymbolBranch.yes_hoareTime Γ.one marker.castSucc (active boxed) (emitBitsTM [])
      s.before s.input emitted (SparseOffsetLoopControl.step boxed s).before
      (SparseOffsetLoopControl.step boxed s).input emitted P
      (fun work => (∀ j, Parked (work j)) ∧ Fields L (SparseOffsetLoopControl.step boxed s).offset R work ∧
        (work marker.castSucc).head = 1 ∧ (work marker.castSucc).read = Γ.ofBool (SparseOffsetLoopControl.step boxed s).running)
      (bound L C - 1) ht
    apply hb.consequence
    · rintro inp work out ⟨hc, hs, hf, hh, hv⟩
      exact ⟨⟨hc, hs, hf, hh, hv⟩, by simpa only [hr, Γ.ofBool] using hv⟩
    · exact fun _ _ _ hp => hp
    · unfold bound; omega

end JointThermoComplexity.Complexity.SparseOffsetMarkedStep

#print axioms JointThermoComplexity.Complexity.SparseOffsetMarkedStep.machine
#print axioms JointThermoComplexity.Complexity.SparseOffsetMarkedStep.hoareTime
