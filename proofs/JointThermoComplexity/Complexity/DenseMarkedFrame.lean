module
public import proofs.JointThermoComplexity.Complexity.DenseMarkedControl

set_option autoImplicit false
@[expose] public section

/-! Exact marker15/availability11 frames and physical fuel18 restoration for
the marked source loop. No full-register assertion is made at advanced fuel. -/

namespace JointThermoComplexity.Complexity.DenseMarkedFrame
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun BoxBufferState
open CountedSparseControl (State)

def Outside (j : Fin 64) : Prop := DenseSourceFrame.Outside j ∧ j ≠ 15
def Stable (R : (Fin 64 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, Outside j → next j = work j) → R work → R next
def Status (running : Bool) (work : Fin 64 → Tape) : Prop :=
  (work 15).head = 1 ∧ (work 15).read = Γ.ofBool running
def Inv (L n N : ℕ) (emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (s : State) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => Cursor s.base.before s.base.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
    DenseSourceFrame.Work L n N (2 + s.rows) R work ∧ Status s.base.running work

def coreKeys : List (Fin 64) := [12, 16, 33, 34, 38, 41, 39, 42, 40, 43, 44, 45, 46, 47, 63]
theorem keys_safe : ∀ j : Fin 64, j ∈ coreKeys → j ≠ 15 ∧ j ≠ 11 ∧ j ≠ 18 := by decide
theorem power_key : ∀ i : Fin 4, DensePowerPorts.flag 4 (by decide) i ∈ coreKeys := by decide

theorem core_transfer (n N current : ℕ) (R : (Fin 64 → Tape) → Prop) (work next : Fin 64 → Tape)
    (he : ∀ j ∈ coreKeys, next j = work j) (hR : R work → R next) (hp : DenseSourceFrame.Core n N current R work) :
    DenseSourceFrame.Core n N current R next := by
  obtain ⟨u, hu, hn⟩ := hp.next
  refine ⟨by rw [he 12 (by decide)]; exact hp.adjusted, by rw [he 16 (by decide)]; exact hp.arity,
    by rw [he 33 (by decide)]; exact hp.total, by rw [he 34 (by decide)]; exact hp.branch,
    by rw [he 38 (by decide)]; exact hp.position, ⟨u, hu, by rw [he 41 (by decide)]; exact hn⟩,
    by rw [he 39 (by decide)]; exact hp.cell, by rw [he 42 (by decide)]; exact hp.comparison,
    by rw [he 40 (by decide)]; exact hp.ending, by rw [he 43 (by decide)]; exact hp.lastHead, ?_,
    by rw [he 63 (by decide)]; exact hp.scratch, hR hp.frame⟩
  intro i
  rw [he _ (power_key i)]
  exact hp.powers i

theorem source_stable (R : (Fin 64 → Tape) → Prop) (hR : Stable R) : DenseSourceFrame.Stable R :=
  fun work next he => hR work next (fun j hj => he j hj.1)

theorem body_stable (running : Bool) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    DenseSourceFrame.Stable (fun work => R work ∧ Status running work) := by
  rintro work next he ⟨hr, hh, hv⟩
  have h15 : DenseSourceFrame.Outside (15 : Fin 64) := by unfold DenseSourceFrame.Outside DenseRowFrame.Outside; decide
  exact ⟨hR work next (fun j hj => he j hj.1) hr, by rw [he 15 h15]; exact hh, by rw [he 15 h15]; exact hv⟩

def ParserRest (L : ℕ) (work : Fin 64 → Tape) : Prop :=
  Reusable L (work 0) ∧ (work 1).head = 1 ∧
    (∀ p ∈ DenseParserPorts.layout.Physical, Reusable L (work p.1) ∧ (work p.2).head = 1) ∧
    (work DenseParserPorts.layout.ending.castSucc).head = 1
def Rest (L n N current : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  ParserRest L work ∧ DenseSourceFrame.Core n N current R work

theorem rest_iff (L n N current : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) :
    DenseSourceFrame.Work L n N current R work ↔ Rest L n N current R work ∧ (work 11).head = 1 := by
  constructor
  · rintro ⟨⟨hb, hs, hslots, hend, hflag⟩, hcore⟩
    exact ⟨⟨⟨hb, hs, hslots, hend⟩, hcore⟩, hflag⟩
  · rintro ⟨⟨⟨hb, hs, hslots, hend⟩, hcore⟩, hflag⟩
    exact ⟨⟨hb, hs, hslots, hend, hflag⟩, hcore⟩

theorem rest_stable (L n N current : ℕ) (R : (Fin 64 → Tape) → Prop) (hR : Stable R) :
    ∀ work next, (∀ j, j ≠ (15 : Fin 64) → j ≠ 11 → next j = work j) → Rest L n N current R work → Rest L n N current R next := by
  rintro work next he ⟨⟨hb, hs, hslots, hend⟩, hcore⟩
  have low (j : Fin 64) (hj : j.val < 11) : next j = work j := by
    apply he j
    · intro hh; have hv := congrArg Fin.val hh; change j.val = 15 at hv; omega
    · intro hh; have hv := congrArg Fin.val hh; change j.val = 11 at hv; omega
  refine ⟨⟨by rw [low 0 (by decide)]; exact hb, by rw [low 1 (by decide)]; exact hs, ?_,
    by rw [low DenseParserPorts.layout.ending.castSucc (by decide)]; exact hend⟩, ?_⟩
  · intro p hp
    have hm : p ∈ ([(2, 6), (3, 7), (4, 8), (5, 9)] : List (Fin 64 × Fin 64)) := hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have hd : p.1.val < 11 := by rcases hm with rfl | rfl | rfl | rfl <;> decide
    have hf : p.2.val < 11 := by rcases hm with rfl | rfl | rfl | rfl <;> decide
    rw [low p.1 hd, low p.2 hf]
    exact hslots p hp
  · apply core_transfer n N current R work next (fun j hj => he j (keys_safe j hj).1 (keys_safe j hj).2.1) _ hcore
    apply hR work next
    intro j hj
    apply he j hj.2
    intro hh
    have hv := congrArg Fin.val hh
    change j.val = 11 at hv
    have hge := hj.1.1
    omega

theorem reframe (L n N : ℕ) (emitted : List Bool) (R : (Fin 64 → Tape) → Prop) (s : State)
    (work next : Fin 64 → Tape) (he : ∀ j, j ≠ (18 : Fin 64) → next j = work j) (hsafe : Parked (next 18))
    (hR : ∀ old new, (∀ j, j ≠ (18 : Fin 64) → new j = old j) → R old → R new) :
    ∀ inp out, Inv L n N emitted R s inp work out → Inv L n N emitted R s inp next out := by
  rintro inp out ⟨hc, hs, ⟨hp, hcore⟩, hh, hv⟩
  have hs' : ∀ j, Parked (next j) := by
    intro j
    by_cases hj : j = (18 : Fin 64)
    · subst j; exact hsafe
    · rw [he j hj]; exact hs j
  have hparser := DenseSourceFrame.parser_transfer L work next (by
    intro j hj
    apply he j
    intro hn
    have hv := congrArg Fin.val hn
    change j.val = 18 at hv
    omega) hp
  have hcore' := core_transfer n N (2 + s.rows) R work next
    (fun j hj => he j (keys_safe j hj).2.2) (hR work next he) hcore
  have hc' : Cursor s.base.before s.base.input emitted inp next out :=
    ⟨hc.cells, hc.head, fun j => ⟨(hs' j).read_ne_start, (hs' j).1⟩, hc.tapePrefix, hc.zero⟩
  exact ⟨hc', hs', ⟨hparser, hcore'⟩, by rw [he 15 (by decide)]; exact hh, by rw [he 15 (by decide)]; exact hv⟩

end JointThermoComplexity.Complexity.DenseMarkedFrame

#print axioms JointThermoComplexity.Complexity.DenseMarkedFrame.rest_stable
#print axioms JointThermoComplexity.Complexity.DenseMarkedFrame.reframe
