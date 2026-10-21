module
public import proofs.JointThermoComplexity.Complexity.BinaryTrimScan

set_option autoImplicit false
@[expose] public section

/-! Complete marker-safe high-zero erasure from a raw prefix end, including the zero word. -/

namespace JointThermoComplexity.Complexity.BinaryTrimRuntime
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryTrimMachine BinaryTrimStep

variable {w : ℕ}

theorem hoareTime (idx : Fin w) (bits before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix (BinaryTrim.trim bits) ∧ (work idx).cells 0 = Γ.start ∧ R work) (bits.length + 2) := by
  rintro inp work out ⟨hc, hs, hb, hz, hr⟩
  let c : Cfg w (Option Bool) := ⟨some false, inp, work, out⟩
  let d := cfg idx (some true) false .left c
  have hsel : d.work idx = (work idx).move .left := move_selected idx .left work (hs idx).read_ne_start
  have hdi : d.input = inp := cfg_input idx (some true) false .left c hc.input_read
  have hdo : d.output = out := cfg_output idx (some true) false .left c hc.output_read
  have hdw : ∀ j, j ≠ idx → d.work j = work j := fun j hj => cfg_other idx j (some true) false .left c hj (hs j).read_ne_start
  have hdc : (d.work idx).HasBinaryContent bits := by
    rw [hsel]
    exact (show (work idx).HasBinaryContent bits from hb.2).move .left
  have hdh : (d.work idx).head = bits.length := by
    rw [hsel]
    simp only [Tape.move, hb.1, Nat.add_sub_cancel]
  have hdz : (d.work idx).cells 0 = Γ.start := by simpa only [hsel, Tape.move_cells] using hz
  obtain ⟨e, t, ht, he, hh, hres⟩ := BinaryTrimScan.scan bits idx d rfl hdc hdh hdz
    (by simpa only [hdi] using hc.input_read) (by simpa only [hdo] using hc.output_read)
    (fun j hj => by simpa only [hdw j hj] using (hs j).read_ne_start)
  have hei : e.input = inp := hres.input_eq.trans hdi
  have heo : e.output = out := hres.output_eq.trans hdo
  have hew : ∀ j, j ≠ idx → e.work j = work j := fun j hj => (hres.others j hj).trans (hdw j hj)
  have hes : ∀ j, Parked (e.work j) := by
    intro j
    by_cases hj : j = idx
    · subst j
      exact ⟨by rw [hres.normalized.1]; omega,
        (show (e.work idx).HasBinaryContent _ from hres.normalized.2).cells_ne_start⟩
    · rw [hew j hj]; exact hs j
  refine ⟨e, t + 1, by omega, .step (start_step idx c rfl) he, hh, ?_, hes, hres.normalized, hres.zero,
    hR work e.work hew hr⟩
  exact ⟨by simpa only [hei] using hc.cells, by simpa only [hei] using hc.head,
    fun j => ⟨(hes j).read_ne_start, (hes j).1⟩,
    by simpa only [heo] using hc.tapePrefix, by simpa only [heo] using hc.zero⟩

theorem canonical_hoareTime (idx : Fin w) (bits before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix (BitCodec.readBits bits).bits ∧ (work idx).cells 0 = Γ.start ∧ R work) (bits.length + 2) := by
  simpa only [BinaryTrim.canonical] using hoareTime idx bits before input emitted R hR

end JointThermoComplexity.Complexity.BinaryTrimRuntime

#print axioms JointThermoComplexity.Complexity.BinaryTrimRuntime.hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryTrimRuntime.canonical_hoareTime
