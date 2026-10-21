module
public import proofs.JointThermoComplexity.Complexity.UnarySuccessorMachine
public import proofs.JointThermoComplexity.Complexity.CountTape

set_option autoImplicit false
@[expose] public section

/-! Exact bounded unary-address scan and its preserved input/output frame. -/

namespace JointThermoComplexity.Complexity.UnarySuccessorScan
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt UnarySuccessorMachine

variable {w : ℕ}

theorem scan (idx : Fin w) (m : ℕ) : ∀ v i, v = i + m → ∀ c : Cfg w (machine idx).Q,
    c.state = false → c.work idx = ⟨i + 1, regCells v⟩ → c.input.read ≠ Γ.start →
    (∀ j, j ≠ idx → (c.work j).read ≠ Γ.start) → c.output.read ≠ Γ.start →
    ∃ e t, t ≤ m + 1 ∧ (machine idx).reachesIn t c e ∧ (machine idx).halted e ∧
      e.input = c.input ∧ e.output = c.output ∧ e.work idx = ⟨v + 2, regCells (v + 1)⟩ ∧
      (∀ j, j ≠ idx → e.work j = c.work j) := by
  induction m with
  | zero =>
    intro v i hv c hs ht hi hw ho
    have hvi : v = i := by omega
    subst v
    have hall : ∀ j, (c.work j).read ≠ Γ.start := by
      intro j
      by_cases hj : j = idx
      · subst j
        rw [ht]
        change regCells i (i + 1) ≠ Γ.start
        exact regCells_ne_start (by omega)
      · exact hw j hj
    let e : Cfg w (machine idx).Q := ⟨true, c.input, Function.update c.work idx ⟨i + 2, regCells (i + 1)⟩, c.output⟩
    have hstep : (machine idx).step c = some e := blank_step idx i c hs ht hi hall ho
    exact ⟨e, 1, by omega, .step hstep .zero, rfl, rfl, rfl, by simp only [e, Function.update_self],
      fun j hj => Function.update_of_ne hj _ _⟩
  | succ m ih =>
    intro v i hv c hs ht hi hw ho
    have hall : ∀ j, (c.work j).read ≠ Γ.start := by
      intro j
      by_cases hj : j = idx
      · subst j
        rw [ht]
        change regCells v (i + 1) ≠ Γ.start
        exact regCells_ne_start (by omega)
      · exact hw j hj
    let c₁ : Cfg w (machine idx).Q := ⟨false, c.input, Function.update c.work idx ⟨i + 2, regCells v⟩, c.output⟩
    have hstep : (machine idx).step c = some c₁ := one_step idx v (i + 1) (by omega) (by omega) c hs ht hi hall ho
    obtain ⟨e, t, ht', hreach, hhalt, heI, heO, heT, heOther⟩ :=
      ih v (i + 1) (by omega) c₁ rfl (Function.update_self _ _ _) hi
        (fun j hj => by simpa only [c₁, Function.update_of_ne hj] using hw j hj) ho
    exact ⟨e, t + 1, by omega, .step hstep hreach, hhalt, heI, heO, heT,
      fun j hj => (heOther j hj).trans (Function.update_of_ne hj _ _)⟩

theorem hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg v (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix (List.replicate (v + 1) true) ∧ (work idx).cells 0 = Γ.start ∧ R work) (v + 1) := by
  rintro inp work out ⟨hc, hs, hv, hr⟩
  obtain ⟨e, t, ht, hreach, hhalt, heI, heO, heT, heOther⟩ :=
    scan idx v v 0 (by omega) ⟨false, inp, work, out⟩ rfl hv.eq_regT hc.input_read
      (fun j _ => (hc.works j).1) hc.output_read
  have heSafe : ∀ j, Parked (e.work j) := by
    intro j
    by_cases hj : j = idx
    · subst j
      rw [heT]
      exact parked_regCells (by omega)
    · rw [heOther j hj]
      exact hs j
  have hePrefix : (e.work idx).HasBinaryPrefix (List.replicate (v + 1) true) := by
    rw [heT]
    refine ⟨by simp only [List.length_replicate], ?_⟩
    exact (CountTape.string_of_register (reg_regT (v + 1))).2
  exact ⟨e, t, ht, hreach, hhalt,
    ⟨by simpa only [heI] using hc.cells, by simpa only [heI] using hc.head,
      (fun j => ⟨(heSafe j).read_ne_start, (heSafe j).1⟩),
      by simpa only [heO] using hc.tapePrefix, by simpa only [heO] using hc.zero⟩,
    heSafe, hePrefix, by rw [heT]; rfl, hR work e.work heOther hr⟩

end JointThermoComplexity.Complexity.UnarySuccessorScan

#print axioms JointThermoComplexity.Complexity.UnarySuccessorScan.hoareTime
