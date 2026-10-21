module
public import proofs.JointThermoComplexity.Complexity.BinaryScaleScan
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementRun
public import proofs.JointThermoComplexity.Complexity.HeaderAt
public import proofs.JointThermoComplexity.Complexity.FixedOutput

set_option autoImplicit false
@[expose] public section

/-! Actual constant scaling emits canonical magnitude bits and restores its
source register exactly. Multiplier zero has an explicit empty-output branch. -/

namespace JointThermoComplexity.Complexity.BinaryScaleRun
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def rawMachine (k : ℕ) (idx : Fin w) : TM w := seqTM (BinaryScaleMachine.machine k idx) (rewindWorkTM idx)

def machine (k : ℕ) (idx : Fin w) : TM w := if k = 0 then emitBitsTM [] else rawMachine k idx

theorem raw_hoareTime (k : ℕ) (idx : Fin w) (bits : List Bool) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (rawMachine k idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ BinaryScaleControl.scale k 0 bits) inp work out ∧
        (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (2 * bits.length + k + 6) := by
  rintro inp work out ⟨hc, hbits, hz, hr⟩
  obtain ⟨d, td, htd, hreachd, hhaltd, hid, hcd, hhd, hwd, hpd, hzd⟩ :=
    BinaryScaleScan.scan (k := k) bits [] emitted idx 0 ⟨.scan 0, inp, work, out⟩ rfl hbits.2 hbits.1 hc.input_read
      (fun j _ => (hc.works j).1) hc.tapePrefix hc.zero
  let P : Tape → (Fin w → Tape) → Tape → Prop := fun inp' work' out' =>
    inp' = d.input ∧ out' = d.output ∧ (work' idx).cells = (d.work idx).cells ∧
      ∀ j, j ≠ idx → work' j = d.work j
  have hP : ∀ (inp' : Tape) (work' : Fin w → Tape) (out' : Tape)
      (inp'' : Tape) (work'' : Fin w → Tape) (out'' : Tape),
      P inp' work' out' → (work'' idx).cells = (work' idx).cells → (work'' idx).head = 1 →
      (∀ j, j ≠ idx → work'' j = work' j) → inp'' = inp' → out''.cells = out'.cells →
      out''.head = out'.head → P inp'' work'' out'' := by
    rintro inp' work' out' inp'' work'' out'' ⟨hinp, hout, hcells, hothers⟩ hc' _ hw' hi' hoc hoh
    exact ⟨hi'.trans hinp, (Tape.ext hoh hoc).trans hout, hc'.trans hcells,
      fun j hj => (hw' j hj).trans (hothers j hj)⟩
  have hcontent : (d.work idx).HasBinaryContent bits := by simpa only [Tape.HasBinaryContent, hcd] using hbits.2
  have hdinput : d.input.read ≠ Γ.start := by simpa only [hid] using hc.input_read
  have hdout : d.output.read ≠ Γ.start := by
    have hb : d.output.read = Γ.blank := by
      rw [Tape.read, hpd.1]
      exact hpd.2.2 (emitted ++ BinaryScaleControl.scale k 0 bits).length le_rfl
    simp [hb]
  have hhead : (d.work idx).head ≤ bits.length + 1 := by simpa using hhd.le
  obtain ⟨e, te, hte, hreache, hhalte, hehead, hp⟩ :=
    rewindWorkTM_hoareTime_frame idx (bits.length + 1) hP d.input d.work d.output
      ⟨by simpa only [hcd] using hz, hcontent.cells_ne_start, hhead, hdinput, hdout,
        by rw [hpd.1]; omega,
        (fun j hj => by simpa only [hwd j hj] using hc.works j), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hwork : e.work = work := by
    funext j
    by_cases hj : j = idx
    · subst j
      apply Tape.ext (hehead.trans hbits.1.symm)
      exact hp.2.2.1.trans hcd
    · exact (hp.2.2.2 j hj).trans (hwd j hj)
  have hcurd : Cursor before input (emitted ++ BinaryScaleControl.scale k 0 bits) e.input e.work e.output := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hp.1, hid] using hc.cells
    · simpa only [hp.1, hid] using hc.head
    · simpa only [hwork] using hc.works
    · simpa only [hp.2.1, Fin.val_zero] using hpd
    · simpa only [hp.2.1] using hzd
  have hreach₂ : (rewindWorkTM idx).reachesIn te
      ⟨(rewindWorkTM idx).qstart, transitionInput d.input, (fun j => transitionTape (d.work j)), transitionTape d.output⟩ e := by
    have hi' := transitionInput_eq_self hdinput
    have ho' := transitionTape_eq_self hdout
    have hw' : (fun j => transitionTape (d.work j)) = d.work := by
      funext j
      apply transitionTape_eq_self
      by_cases hj : j = idx
      · subst j
        exact hcontent.cells_ne_start _ (by rw [hhd]; simp)
      · simpa only [hwd j hj] using (hc.works j).1
    simpa only [hi', ho', hw'] using hreache
  have hreach := seqTM_reachesIn_of_reachesIn (BinaryScaleMachine.machine k idx) (rewindWorkTM idx) hreachd hhaltd hreach₂
  refine ⟨phase2Wrap (BinaryScaleMachine.machine k idx) (rewindWorkTM idx) e, td + 1 + te, by omega,
    hreach, (phase2Wrap_halted_iff _ _ e).mpr hhalte, hcurd, ?_, ?_, ?_⟩
  · simpa only [phase2Wrap, hwork] using hbits
  · simpa only [phase2Wrap, hwork] using hz
  · simpa only [phase2Wrap, hwork] using hr

theorem natural_hoareTime (k : ℕ) (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine k idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        BinaryIncrementRun.Register v (work idx) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (k * v).bits) inp work out ∧ (∀ j, Parked (work j)) ∧
        BinaryIncrementRun.Register v (work idx) ∧ R work)
      (2 * v.bits.length + k + 6) := by
  by_cases hk : k = 0
  · subst k
    have h := FixedOutput.hoareTime [] before input emitted (fun work => BinaryIncrementRun.Register v (work idx) ∧ R work)
    simpa [machine] using h.mono_bound (by change 0 ≤ 2 * v.bits.length + 0 + 6; omega)
  · rw [machine, ite_eq_right hk]
    have h := raw_hoareTime k idx v.bits before input emitted (fun work => (∀ j, Parked (work j)) ∧ R work)
    rw [BinaryScaleCanonical.scale_bits k v (Nat.pos_of_ne_zero hk)] at h
    apply h.consequence
    · rintro inp work out ⟨hc, hs, hr, hx⟩
      exact ⟨hc, hr.1, hr.2, hs, hx⟩
    · rintro inp work out ⟨hc, hb, hz, hs, hx⟩
      exact ⟨hc, hs, ⟨hb, hz⟩, hx⟩
    · exact le_rfl

end JointThermoComplexity.Complexity.BinaryScaleRun

#print axioms JointThermoComplexity.Complexity.BinaryScaleRun.machine
#print axioms JointThermoComplexity.Complexity.BinaryScaleRun.raw_hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryScaleRun.natural_hoareTime
