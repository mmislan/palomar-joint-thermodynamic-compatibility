module
public import proofs.JointThermoComplexity.Complexity.MarkedNaturalStep
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! Actual bounded marked-list traversal, including exact list termination.
Fuel is restored and each scratch-field load retains the real output.
-/

namespace JointThermoComplexity.Complexity.MarkedNaturalLoop
open _root_.Complexity _root_.Complexity.TM MarkedNaturalControl MarkedNaturalStep
open HeaderAt (Cursor)
variable {w : ℕ}

def FuelStable (r : Fin (w + 1)) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work work', (∀ j, j ≠ r → work' j = work j) → R work → R work'

def Logical (p : Ports w) (s : State) (L : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) :=
  fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s L R work

def ExactFuel (r : Fin (w + 1)) (v head : ℕ) (work : Fin (w + 1) → Tape) : Prop :=
  work r = ⟨head, regCells v⟩

theorem exact_stable (p : Ports w) (r : Fin (w + 1)) (ha : r ≠ p.active) (hp : r ≠ p.presence)
    (hb : r ≠ p.buffer) (v head : ℕ) : Stable p (ExactFuel r v head) := by
  intro work work' he hf
  exact (he r ha hp hb).trans hf

theorem reframe (p : Ports w) (r : Fin (w + 1)) (ha : r ≠ p.active) (hp : r ≠ p.presence)
    (hb : r ≠ p.buffer) (s : State) (L : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hRF : FuelStable r R) (work work' : Fin (w + 1) → Tape)
    (he : ∀ j, j ≠ r → work' j = work j) (hs : Parked (work' r)) :
    ∀ inp out, Logical p s L emitted R inp work out → Logical p s L emitted R inp work' out := by
  rintro inp out ⟨hc, hsafe, hactive, hpresence, hread, hbuffer, hr⟩
  have hs' : ∀ j, Parked (work' j) := by
    intro j
    by_cases hj : j = r
    · subst j
      exact hs
    · rw [he j hj]
      exact hsafe j
  have hc' : Cursor s.before s.input emitted inp work' out :=
    ⟨hc.cells, hc.head, fun j => ⟨(hs' j).read_ne_start, (hs' j).1⟩, hc.tapePrefix, hc.zero⟩
  exact ⟨hc', hs', by simpa only [he _ ha.symm] using hactive,
    by simpa only [he _ hp.symm] using hpresence, by simpa only [he _ ha.symm] using hread,
    by simpa only [he _ hb.symm] using hbuffer, hRF work work' he hr⟩

theorem to_actual (p : Ports w) (r : Fin (w + 1)) (ha : r ≠ p.active) (hp : r ≠ p.presence)
    (hb : r ≠ p.buffer) (s : State) (L v head : ℕ) (hhead : 1 ≤ head) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hRF : FuelStable r R)
    (inp : Tape) (work : Fin (w + 1) → Tape) (out : Tape)
    (hf : InvariantLoop.Frame r v head (Logical p s L emitted R) inp work out) :
    Cursor s.before s.input emitted inp work out ∧ Ready p s L (fun work => R work ∧ ExactFuel r v head work) work := by
  have h := reframe p r ha hp hb s L emitted R hRF (InvariantLoop.restore work r v) work
    (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
    (by rw [hf.fuel]; exact ⟨hhead, fun j hj => regCells_ne_start hj⟩) inp out hf.invariant
  obtain ⟨hc, hs, hactive, hpresence, hread, hbuffer, hr⟩ := h
  exact ⟨hc, hs, hactive, hpresence, hread, hbuffer, hr, hf.fuel⟩

theorem from_actual (p : Ports w) (r : Fin (w + 1)) (ha : r ≠ p.active) (hp : r ≠ p.presence)
    (hb : r ≠ p.buffer) (s : State) (L v head : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hRF : FuelStable r R)
    (inp : Tape) (work : Fin (w + 1) → Tape) (out : Tape)
    (hc : Cursor s.before s.input emitted inp work out)
    (hr : Ready p s L (fun work => R work ∧ ExactFuel r v head work) work) :
    InvariantLoop.Frame r v head (Logical p s L emitted R) inp work out := by
  obtain ⟨hs, hactive, hpresence, hread, hbuffer, hr, hfuel⟩ := hr
  have hbase : Logical p s L emitted R inp work out := ⟨hc, hs, hactive, hpresence, hread, hbuffer, hr⟩
  have hrest := reframe p r ha hp hb s L emitted R hRF work (InvariantLoop.restore work r v)
    (fun j hj => by simp only [InvariantLoop.restore, Function.update_of_ne hj])
    (by simpa only [InvariantLoop.restore, Function.update_self] using parked_regTape v) inp out hbase
  exact ⟨hfuel, hc.input_read, fun j _ => (hs j).read_ne_start, hc.output_read, hrest⟩

def machine (p : Ports w) (r : Fin (w + 1)) : TM (w + 1) := forRegTM (MarkedNaturalStep.machine p) r

def timeBound (L fuel : ℕ) : ℕ := fuel * ((14 * L + 30) + 2) + (fuel + 2)

theorem hoareTime (p : Ports w) (r : Fin (w + 1)) (ha : r ≠ p.active) (hp : r ≠ p.presence)
    (hb : r ≠ p.buffer) (s : State) (L fuel : ℕ) (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) (hRF : FuelStable r R) :
    (machine p r).HoareTime
      (fun inp work out => Logical p s L emitted R inp work out ∧ IsReg fuel (work r))
      (fun inp work out => Logical p (run fuel s) L emitted R inp work out ∧ IsReg fuel (work r))
      (timeBound L fuel) := by
  let P : ℕ → _root_.Complexity.TM.TapePred (w + 1) := fun i => Logical p (run i s) L emitted R
  have hbody : ∀ i, i < fuel → (MarkedNaturalStep.machine p).HoareTime
      (InvariantLoop.Frame r fuel (i + 2) (P i)) (InvariantLoop.Frame r fuel (i + 2) (P (i + 1))) (14 * L + 30) := by
    intro i _
    have hframe : Stable p (fun work => R work ∧ ExactFuel r fuel (i + 2) work) := by
      rintro work work' he ⟨hr, hf⟩
      exact ⟨hR work work' he hr, exact_stable p r ha hp hb fuel (i + 2) work work' he hf⟩
    have h := MarkedNaturalStep.hoareTime p (run i s) L ((run_length i s).trans hlen) emitted
      (fun work => R work ∧ ExactFuel r fuel (i + 2) work) hframe
    exact h.consequence
      (fun inp work out hf => to_actual p r ha hp hb (run i s) L fuel (i + 2) (by omega) emitted R hRF inp work out hf)
      (fun inp work out ⟨hc, hr⟩ => from_actual p r ha hp hb (step (run i s)) L fuel (i + 2) emitted R hRF inp work out hc hr)
      le_rfl
  have h := InvariantLoop.hoareTime (MarkedNaturalStep.machine p) r P (14 * L + 30) fuel hbody
  apply h.consequence
  · rintro inp work out ⟨⟨hc, hr⟩, hf⟩
    refine ⟨hf.eq_regT, hc.input_read, fun j _ => (hr.1 j).read_ne_start, hc.output_read, ?_⟩
    rw [InvariantLoop.restore_self work r fuel hf.eq_regT]
    exact ⟨hc, hr⟩
  · intro inp work out hf
    exact ⟨hf.on_work, hf.register⟩
  · exact le_rfl

theorem code_hoareTime (p : Ports w) (r : Fin (w + 1)) (ha : r ≠ p.active) (hp : r ≠ p.presence)
    (hb : r ≠ p.buffer) (items : List ℕ) (before suffix emitted : List Bool) (L fuel : ℕ)
    (hlen : (code items ++ suffix).length ≤ L) (hf : items.length + 1 ≤ fuel)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) (hRF : FuelStable r R) :
    (machine p r).HoareTime
      (fun inp work out => Logical p ⟨before, code items ++ suffix, true⟩ L emitted R inp work out ∧ IsReg fuel (work r))
      (fun inp work out => Logical p ⟨before ++ code items, suffix, false⟩ L emitted R inp work out ∧ IsReg fuel (work r))
      (timeBound L fuel) := by
  simpa only [run_code fuel items hf before suffix] using
    hoareTime p r ha hp hb ⟨before, code items ++ suffix, true⟩ L fuel hlen emitted R hR hRF

theorem encoded_hoareTime (p : Ports w) (r : Fin (w + 1)) (ha : r ≠ p.active) (hp : r ≠ p.presence)
    (hb : r ≠ p.buffer) (items : List ℕ) (before suffix emitted : List Bool) (L : ℕ)
    (hlen : (code items ++ suffix).length ≤ L)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) (hRF : FuelStable r R) :
    (machine p r).HoareTime
      (fun inp work out => Logical p ⟨before, code items ++ suffix, true⟩ L emitted R inp work out ∧ IsReg L (work r))
      (fun inp work out => Logical p ⟨before ++ code items, suffix, false⟩ L emitted R inp work out ∧ IsReg L (work r))
      (timeBound L L) := by
  have hc := code_length items
  have hf : items.length + 1 ≤ L := by rw [List.length_append] at hlen; omega
  exact code_hoareTime p r ha hp hb items before suffix emitted L L hlen hf R hR hRF

end JointThermoComplexity.Complexity.MarkedNaturalLoop

#print axioms JointThermoComplexity.Complexity.MarkedNaturalLoop.hoareTime
#print axioms JointThermoComplexity.Complexity.MarkedNaturalLoop.code_hoareTime
#print axioms JointThermoComplexity.Complexity.MarkedNaturalLoop.encoded_hoareTime
