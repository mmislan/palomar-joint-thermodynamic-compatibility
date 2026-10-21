module
public import proofs.JointThermoComplexity.Complexity.UnaryPredecessor
public import proofs.JointThermoComplexity.Complexity.FlagBranchRun

set_option autoImplicit false
@[expose] public section

/-! Total bounded address subtraction branches on the actual unary register, including zero. -/

namespace JointThermoComplexity.Complexity.SaturatingAddressCut
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def one (idx : Fin w) : TM w := FlagBranch.machine idx (UnaryPredecessor.machine idx) (emitBitsTM [])

theorem blank_step (idx : Fin w) (yes no : TM w) (before input emitted : List Bool)
    (inp out : Tape) (work : Fin w → Tape) (hc : Cursor before input emitted inp work out)
    (hf : (work idx).read = Γ.blank) :
    (FlagBranch.machine idx yes no).step ⟨(FlagBranch.machine idx yes no).qstart, inp, work, out⟩ =
      some (FlagBranch.wrapNo idx yes no ⟨no.qstart, inp, work, out⟩) := by
  simp only [TM.step, FlagBranch.machine, reduceCtorEq, ↓reduceIte, hf, FlagBranch.wrapNo, allReadBack]
  change some (⟨some (.inr no.qstart), transitionInput inp, (fun j => transitionTape (work j)), transitionTape out⟩ :
    Cfg w (Option (yes.Q ⊕ no.Q))) = _
  obtain ⟨hi, hw, ho⟩ := hc.phase
  rw [hi, hw, ho]

theorem one_hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (one idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg v (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg (v - 1) (work idx) ∧ R work)
      (2 * v + 14) := by
  cases v with
  | zero =>
    rintro inp work out ⟨hc, hs, hv, hr⟩
    have hf : (work idx).read = Γ.blank := by
      rw [Tape.read, hv.head_eq]
      exact hv.cells_blank (by omega)
    have hstart := blank_step idx (UnaryPredecessor.machine idx) (emitBitsTM []) before input emitted inp out work hc hf
    have hend := FlagBranch.finish_no idx (UnaryPredecessor.machine idx) (emitBitsTM []) before input emitted
      ⟨(emitBitsTM (n := w) []).qhalt, inp, work, out⟩ rfl hc
    exact ⟨⟨(one idx).qhalt, inp, work, out⟩, 2, by omega, .step hstart (.step hend .zero), rfl, hc, hs, hv, hr⟩
  | succ v =>
    have hp := UnaryPredecessor.hoareTime idx v before input emitted R hR
    have hb := FlagBranchRun.yes_hoareTime idx (UnaryPredecessor.machine idx) (emitBitsTM [])
      before input emitted before input emitted (fun work => (∀ j, Parked (work j)) ∧ IsReg (v + 1) (work idx) ∧ R work)
      (fun work => (∀ j, Parked (work j)) ∧ IsReg v (work idx) ∧ R work) (2 * v + 12) hp
    apply hb.consequence
    · rintro inp work out ⟨hc, hs, hv, hr⟩
      refine ⟨⟨hc, hs, hv, hr⟩, ?_⟩
      rw [Tape.read, hv.head_eq]
      exact hv.cells_one (by omega)
    · rintro inp work out h
      simpa only [Nat.add_sub_cancel] using h
    · omega

def machine : ℕ → Fin w → TM w
  | 0, _ => emitBitsTM []
  | n + 1, idx => seqTM (one idx) (machine n idx)

theorem hoareTime (offset : ℕ) (idx : Fin w) (v B : ℕ) (hv : v ≤ B)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine offset idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg v (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg (v - offset) (work idx) ∧ R work)
      (offset * (2 * B + 15)) := by
  induction offset generalizing v with
  | zero =>
    simpa only [machine, Nat.sub_zero, Nat.zero_mul, List.append_nil, List.length_nil] using
      FixedOutput.hoareTime [] before input emitted (fun work => IsReg v (work idx) ∧ R work)
  | succ offset ih =>
    have ho := (one_hoareTime idx v before input emitted R hR).mono_bound (show 2 * v + 14 ≤ 2 * B + 14 by omega)
    have ht := ih (v - 1) (by omega)
    have hseq := seqTM_hoareTime (one idx) (machine offset idx) ho (by
      rintro inp work out ⟨hc, hs, hval, hr⟩
      obtain ⟨hi, hw, hout⟩ := hc.phase
      rw [hi, hw, hout]
      exact ⟨hc, hs, hval, hr⟩) ht
    apply hseq.consequence (fun _ _ _ h => h)
    · rintro inp work out h
      simpa only [Nat.sub_sub, Nat.add_comm 1 offset] using h
    · have he : (offset + 1) * (2 * B + 15) = offset * (2 * B + 15) + (2 * B + 15) := by rw [Nat.add_mul, Nat.one_mul]
      rw [he]
      omega

end JointThermoComplexity.Complexity.SaturatingAddressCut

#print axioms JointThermoComplexity.Complexity.SaturatingAddressCut.one_hoareTime
#print axioms JointThermoComplexity.Complexity.SaturatingAddressCut.hoareTime
