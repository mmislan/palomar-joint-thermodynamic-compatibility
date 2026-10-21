module
public import proofs.JointThermoComplexity.Complexity.QueryWorkFrame
public import proofs.JointThermoComplexity.Complexity.UnaryReset
public import proofs.JointThermoComplexity.Complexity.UnarySuccessor

set_option autoImplicit false
@[expose] public section

/-! Reusable physical query counters are cleared on every raw branch and seeded for traversal. -/

namespace JointThermoComplexity.Complexity.QueryCounterInit
open _root_.Complexity _root_.Complexity.TM HeaderAt RelocatedSpanQuery QueryWorkFrame

inductive Counter where
  | term | formula | node
  deriving DecidableEq

def Counter.port : Counter → Fin 32
  | .term => pending
  | .formula => formulas
  | .node => result

structure Counts where
  terms : ℕ
  formulas : ℕ
  nodes : ℕ

def Counts.get (s : Counts) : Counter → ℕ
  | .term => s.terms
  | .formula => s.formulas
  | .node => s.nodes

def Counts.set (s : Counts) (c : Counter) (v : ℕ) : Counts := match c with
  | .term => {s with terms := v}
  | .formula => {s with formulas := v}
  | .node => {s with nodes := v}

def Counts.total (s : Counts) : ℕ := s.terms + s.formulas + s.nodes

def HasCounts (s : Counts) (L : ℕ) (R : Work → Prop) : Work → Prop := Ready s.terms s.formulas s.nodes L R

theorem port_position (c : Counter) : c.port ≠ position := by cases c <;> decide

theorem tags_port (i : Fin 3) (c : Counter) : tags i ≠ c.port := by
  intro he
  have hv := congrArg Fin.val he
  cases c <;> simp only [tags, Counter.port, pending, formulas, result] at hv <;> omega

theorem outside_port (j : Fin 32) (hj : Outside j) (c : Counter) : j ≠ c.port := by
  intro he
  have hv := congrArg Fin.val he
  rcases hj.1 with ⟨i, rfl⟩ | hh
  · cases c <;> simp only [EquationQueryLayout.main, Counter.port, pending, formulas, result] at hv <;> omega
  · cases c <;> simp only [Counter.port, pending, formulas, result] at hv <;> omega

theorem counter_frame (c : Counter) (tm : TM 32) (s : Counts) (new L p bound : ℕ)
    (before input emitted : List Bool) (R : Work → Prop) (hR : Stable R)
    (h : ∀ C : Work → Prop,
      (∀ work work', (∀ j, j ≠ c.port → work' j = work j) → C work → C work') →
      tm.HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg (s.get c) (work c.port) ∧ C work)
        (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg new (work c.port) ∧ C work) bound) :
    tm.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts s L R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts (s.set c new) L R work) bound := by
  rintro inp work out ⟨hc, hs, hp, hr⟩
  let C : Work → Prop := fun work' => ∀ j, j ≠ c.port → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ c.port → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hh j hj
    exact (he j hj).trans (hh j hj)
  have hold : IsReg (s.get c) (work c.port) := by cases c <;> first | exact hr.termReg | exact hr.formulaReg | exact hr.nodeReg
  obtain ⟨d, t, ht, hd, hh, hc', hs', hn, ho⟩ := h C hC inp work out ⟨hc, hs, hold, fun _ _ => rfl⟩
  have hp' : IsReg p (d.work position) := by rw [ho _ (port_position c).symm]; exact hp
  have hm : ∀ j, j ≠ position → (d.work j).cells 0 = Γ.start := by
    intro j hj
    by_cases he : j = c.port
    · subst j
      exact hn.cell0
    · rw [ho j he]
      exact hr.markers j hj
  have htags : ∀ i, (d.work (tags i)).head = 1 := fun i => by rw [ho _ (tags_port i c)]; exact hr.tagHeads i
  have hflag : (d.work flag).head = 1 := by
    rw [ho _ (by cases c <;> decide)]
    exact hr.flagHead
  have htp : IsReg (s.set c new).terms (d.work pending) := by
    cases c <;> first | exact hn | (rw [ho _ (by decide)]; exact hr.termReg)
  have hfp : IsReg (s.set c new).formulas (d.work formulas) := by
    cases c <;> first | exact hn | (rw [ho _ (by decide)]; exact hr.formulaReg)
  have hnodes : IsReg (s.set c new).nodes (d.work result) := by
    cases c <;> first | exact hn | (rw [ho _ (by decide)]; exact hr.nodeReg)
  have hfuel : IsReg L (d.work fuel) := by
    rw [ho _ (by cases c <;> decide)]
    exact hr.fuelReg
  exact ⟨d, t, ht, hd, hh, hc', hs', hp', hm, htags, hflag, htp, hfp, hnodes, hfuel,
    hR work d.work (fun j hj => ho j (outside_port j hj c)) hr.frame⟩

theorem reset_hoareTime (c : Counter) (s : Counts) (L p : ℕ) (before input emitted : List Bool)
    (R : Work → Prop) (hR : Stable R) :
    (clearWorkTM c.port).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts s L R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts (s.set c 0) L R work) (2 * s.get c + 5) :=
  counter_frame c _ s 0 L p _ before input emitted R hR
    (fun C hC => UnaryReset.hoareTime c.port (s.get c) before input emitted C hC)

theorem increment_hoareTime (c : Counter) (s : Counts) (L p : ℕ) (before input emitted : List Bool)
    (R : Work → Prop) (hR : Stable R) :
    (UnarySuccessor.machine c.port).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts s L R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts (s.set c (s.get c + 1)) L R work) (2 * s.get c + 6) :=
  counter_frame c _ s _ L p _ before input emitted R hR
    (fun C hC => UnarySuccessor.hoareTime c.port (s.get c) before input emitted C hC)

def clear : TM 32 := seqTM (clearWorkTM pending) (seqTM (clearWorkTM formulas) (clearWorkTM result))
def machine (c : Counter) : TM 32 := seqTM clear (UnarySuccessor.machine c.port)

theorem clear_hoareTime (s : Counts) (L p : ℕ) (before input emitted : List Bool)
    (R : Work → Prop) (hR : Stable R) :
    clear.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts s L R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts ⟨0, 0, 0⟩ L R work) (2 * s.total + 17) := by
  have hn := reset_hoareTime .node ((s.set .term 0).set .formula 0) L p before input emitted R hR
  have hf := reset_hoareTime .formula (s.set .term 0) L p before input emitted R hR
  have hfn := seqTM_hoareTime (clearWorkTM formulas) (clearWorkTM result) hf (by
    rintro inp work out ⟨hc, hs, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hp, hr⟩) hn
  have ht := reset_hoareTime .term s L p before input emitted R hR
  have hall := seqTM_hoareTime (clearWorkTM pending) (seqTM (clearWorkTM formulas) (clearWorkTM result)) ht (by
    rintro inp work out ⟨hc, hs, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hp, hr⟩) hfn
  exact hall.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by simp only [Counts.get, Counts.set, Counts.total]; omega)

theorem hoareTime (c : Counter) (s : Counts) (L p : ℕ) (before input emitted : List Bool)
    (R : Work → Prop) (hR : Stable R) :
    (machine c).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts s L R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ HasCounts ((⟨0, 0, 0⟩ : Counts).set c 1) L R work) (2 * s.total + 24) := by
  have hc := clear_hoareTime s L p before input emitted R hR
  have hi := increment_hoareTime c ⟨0, 0, 0⟩ L p before input emitted R hR
  have hall := seqTM_hoareTime clear (UnarySuccessor.machine c.port) hc (by
    rintro inp work out ⟨hcur, hs, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨hcur, hs, hp, hr⟩) hi
  have hz : (⟨0, 0, 0⟩ : Counts).get c = 0 := by cases c <;> rfl
  simpa only [machine, hz, Nat.zero_add, Nat.mul_zero, Nat.add_assoc, Nat.reduceAdd] using hall

end JointThermoComplexity.Complexity.QueryCounterInit

#print axioms JointThermoComplexity.Complexity.QueryCounterInit.clear_hoareTime
#print axioms JointThermoComplexity.Complexity.QueryCounterInit.hoareTime
