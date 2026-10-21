module
public import proofs.JointThermoComplexity.Complexity.MonomialPrefixStep
public import proofs.JointThermoComplexity.Complexity.MarkedNaturalLoop

set_option autoImplicit false
@[expose] public section

/-! Actual bounded monomial prefix/discard parser. Its nine distinct ports may
be embedded in a larger machine. Saved flags and raw words survive tail disposal,
and an arbitrary frame retains coefficient buffers and surrounding row data.
-/

namespace JointThermoComplexity.Complexity.MonomialPrefixMachine
open _root_.Complexity _root_.Complexity.TM BoxBufferState MonomialPrefixControl
open HeaderAt (Cursor)
variable {w : ℕ}

structure Ports (w : ℕ) where
  index : Fin 9 → Fin (w + 1)
  injective : Function.Injective index

namespace Ports
def flag (p : Ports w) (i : Fin 3) : Fin (w + 1) := p.index ⟨i.val, by omega⟩
def word (p : Ports w) (j : Fin 2) : Fin (w + 1) := p.index ⟨5 + j.val, by omega⟩
def available (p : Ports w) : Fin (w + 1) := p.index 3
def loopAvailable (p : Ports w) : Fin (w + 1) := p.index 4
def scratch (p : Ports w) : Fin (w + 1) := p.index 7
def fuel (p : Ports w) : Fin (w + 1) := p.index 8

theorem separate (p : Ports w) (a b : Fin 9) (h : a.val ≠ b.val) : p.index a ≠ p.index b :=
  p.injective.ne (Fin.ne_of_val_ne h)

theorem flag_ne (p : Ports w) {i k : Fin 3} (h : i ≠ k) : p.flag i ≠ p.flag k := by
  apply p.injective.ne
  intro he
  exact h (Fin.ext (congrArg (fun a : Fin 9 => a.val) he))

theorem word_ne (p : Ports w) {j k : Fin 2} (h : j ≠ k) : p.word j ≠ p.word k := by
  apply p.injective.ne
  intro he
  apply h
  apply Fin.ext
  have := congrArg Fin.val he
  dsimp at this
  omega

theorem flag_available (p : Ports w) (i : Fin 3) : p.flag i ≠ p.available := p.separate _ _ (by dsimp; omega)
theorem word_flag (p : Ports w) (j : Fin 2) (i : Fin 3) : p.word j ≠ p.flag i := p.separate _ _ (by dsimp; omega)
theorem word_available (p : Ports w) (j : Fin 2) : p.word j ≠ p.available := p.separate _ _ (by dsimp; omega)
theorem loop_flag (p : Ports w) (i : Fin 3) : p.loopAvailable ≠ p.flag i := p.separate _ _ (by dsimp; omega)
theorem loop_available (p : Ports w) : p.loopAvailable ≠ p.available := p.separate _ _ (by decide)
theorem loop_word (p : Ports w) (j : Fin 2) : p.loopAvailable ≠ p.word j := p.separate _ _ (by dsimp; omega)
theorem scratch_flag (p : Ports w) (i : Fin 3) : p.scratch ≠ p.flag i := p.separate _ _ (by dsimp; omega)
theorem scratch_available (p : Ports w) : p.scratch ≠ p.available := p.separate _ _ (by decide)
theorem scratch_loop (p : Ports w) : p.scratch ≠ p.loopAvailable := p.separate _ _ (by decide)
theorem scratch_word (p : Ports w) (j : Fin 2) : p.scratch ≠ p.word j := p.separate _ _ (by dsimp; omega)
theorem fuel_flag (p : Ports w) (i : Fin 3) : p.fuel ≠ p.flag i := p.separate _ _ (by dsimp; omega)
theorem fuel_available (p : Ports w) : p.fuel ≠ p.available := p.separate _ _ (by decide)
theorem fuel_loop (p : Ports w) : p.fuel ≠ p.loopAvailable := p.separate _ _ (by decide)
theorem fuel_word (p : Ports w) (j : Fin 2) : p.fuel ≠ p.word j := p.separate _ _ (by dsimp; omega)
theorem fuel_scratch (p : Ports w) : p.fuel ≠ p.scratch := p.separate _ _ (by decide)

def fieldPorts (p : Ports w) (i : Fin 3) (j : Fin 2) : MarkedNaturalStep.Ports w :=
  ⟨p.flag i, p.available, p.word j, p.flag_available i, p.word_flag j i, p.word_available j⟩

def loopPorts (p : Ports w) : MarkedNaturalStep.Ports w :=
  ⟨p.available, p.loopAvailable, p.scratch, p.loop_available.symm, p.scratch_available, p.scratch_loop⟩
end Ports

def Stable (p : Ports w) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work work', (∀ k, (∀ a, k ≠ p.index a) → work' k = work k) → R work → R work'

def Flags (p : Ports w) (s : State) (work : Fin (w + 1) → Tape) : Prop :=
  ∀ i, (work (p.flag i)).head = 1 ∧ (work (p.flag i)).read = Γ.ofBool (s.flags i)

def Words (p : Ports w) (s : State) (L : ℕ) (work : Fin (w + 1) → Tape) : Prop :=
  ∀ j, (work (p.word j)).HasBinaryString (s.words j) ∧ (work (p.word j)).cells 0 = Γ.start ∧
    (s.words j).length ≤ 4 * L

structure Ready (p : Ports w) (s : State) (L : ℕ) (R : (Fin (w + 1) → Tape) → Prop)
    (work : Fin (w + 1) → Tape) : Prop where
  safe : ∀ k, Parked (work k)
  flags : Flags p s work
  words : Words p s L work
  available_head : (work p.available).head = 1
  available_read : (work p.available).read = Γ.ofBool s.available
  loop_head : (work p.loopAvailable).head = 1
  scratch : Reusable L (work p.scratch)
  fuel : IsReg L (work p.fuel)
  extra : R work

def Logical (p : Ports w) (s : State) (L : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) :=
  fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s L R work

def Rest (p : Ports w) (s : State) (i : Fin 3) (j : Fin 2) (L : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape) : Prop :=
  (∀ k, k ≠ i → (work (p.flag k)).head = 1 ∧ (work (p.flag k)).read = Γ.ofBool (s.flags k)) ∧
  (∀ k, k ≠ j → (work (p.word k)).HasBinaryString (s.words k) ∧ (work (p.word k)).cells 0 = Γ.start ∧
    (s.words k).length ≤ 4 * L) ∧
  (work p.loopAvailable).head = 1 ∧ Reusable L (work p.scratch) ∧ IsReg L (work p.fuel) ∧ R work

theorem rest_stable (p : Ports w) (s : State) (i : Fin 3) (j : Fin 2) (L : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    MarkedNaturalStep.Stable (p.fieldPorts i j) (Rest p s i j L R) := by
  rintro work work' he ⟨hf, hw, hl, hs, hn, hr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hR work work' (fun k hk => he k (hk _) (hk _) (hk _)) hr⟩
  · intro k hk
    rw [he _ (p.flag_ne hk) (p.flag_available k) (p.word_flag j k).symm]
    exact hf k hk
  · intro k hk
    rw [he _ (p.word_flag k i) (p.word_available k) (p.word_ne hk)]
    exact hw k hk
  · simpa only [he _ (p.loop_flag i) p.loop_available (p.loop_word j)] using hl
  · simpa only [he _ (p.scratch_flag i) p.scratch_available (p.scratch_word j)] using hs
  · simpa only [he _ (p.fuel_flag i) p.fuel_available (p.fuel_word j)] using hn

theorem to_local (p : Ports w) (s : State) (i : Fin 3) (j : Fin 2) (L : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape) (h : Ready p s L R work) :
    MonomialPrefixStep.Ready (p.fieldPorts i j) s i j L (Rest p s i j L R) work :=
  ⟨h.safe, (h.flags i).1, h.available_head, (h.flags i).2, h.available_read,
    (h.words j).1, (h.words j).2.1, (h.words j).2.2,
    (fun k _ => h.flags k), (fun k _ => h.words k), h.loop_head, h.scratch, h.fuel, h.extra⟩

theorem from_local (p : Ports w) (s t : State) (i : Fin 3) (j : Fin 2) (L : ℕ)
    (hf : ∀ k, k ≠ i → t.flags k = s.flags k) (hw : ∀ k, k ≠ j → t.words k = s.words k)
    (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape)
    (h : MonomialPrefixStep.Ready (p.fieldPorts i j) t i j L (Rest p s i j L R) work) : Ready p t L R work := by
  obtain ⟨hs, ha, hp, hd, hv, hb, hz, hn, hflags, hwords, hl, hscratch, hfuel, hr⟩ := h
  refine ⟨hs, ?_, ?_, hp, hv, hl, hscratch, hfuel, hr⟩
  · intro k
    by_cases hk : k = i
    · subst k; exact ⟨ha, hd⟩
    · rw [hf k hk]; exact hflags k hk
  · intro k
    by_cases hk : k = j
    · subst k; exact ⟨hb, hz, hn⟩
    · rw [hw k hk]; exact hwords k hk

theorem field_flags (s : State) (i : Fin 3) (j : Fin 2) (k : Fin 3) (hk : k ≠ i) :
    (field s i j).flags k = s.flags k := by
  unfold field
  dsimp only
  split <;> simp [load, MonomialPrefixControl.read, Function.update_of_ne hk]

theorem field_words (s : State) (i : Fin 3) (j k : Fin 2) (hk : k ≠ j) :
    (field s i j).words k = s.words k := by
  unfold field
  dsimp only
  split <;> simp [load, MonomialPrefixControl.read, Function.update_of_ne hk]

theorem field_hoareTime (p : Ports w) (s : State) (i : Fin 3) (j : Fin 2) (L : ℕ)
    (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (MonomialPrefixStep.machine (p.fieldPorts i j)).HoareTime
      (Logical p s L emitted R) (Logical p (field s i j) L emitted R) (14 * L + 24) := by
  have h := MonomialPrefixStep.hoareTime (p.fieldPorts i j) s i j L hlen emitted (Rest p s i j L R)
    (rest_stable p s i j L R hR)
  exact h.consequence
    (fun _ work _ ⟨hc, hr⟩ => ⟨hc, to_local p s i j L R work hr⟩)
    (fun _ work _ ⟨hc, hr⟩ => ⟨hc, from_local p s (field s i j) i j L
      (field_flags s i j) (field_words s i j) R work hr⟩) le_rfl

theorem read_hoareTime (p : Ports w) (s : State) (i : Fin 3) (L : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (SourceBitRead.machine (p.flag i) p.available).HoareTime
      (Logical p s L emitted R) (Logical p (MonomialPrefixControl.read s i) L emitted R) 1 := by
  have h := MonomialPrefixStep.read_hoareTime (p.fieldPorts i 0) s i 0 L emitted (Rest p s i 0 L R)
    (rest_stable p s i 0 L R hR)
  exact h.consequence
    (fun _ work _ ⟨hc, hr⟩ => ⟨hc, to_local p s i 0 L R work hr⟩)
    (fun _ work _ ⟨hc, hr⟩ => ⟨hc, from_local p s (MonomialPrefixControl.read s i) i 0 L
      (fun k hk => by simp [MonomialPrefixControl.read, Function.update_of_ne hk])
      (fun _ _ => rfl) R work hr⟩) le_rfl

def Kept (p : Ports w) (s : State) (L : ℕ) (R : (Fin (w + 1) → Tape) → Prop)
    (work : Fin (w + 1) → Tape) : Prop := Flags p s work ∧ Words p s L work ∧ R work

theorem kept_stable (p : Ports w) (s : State) (L : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    MarkedNaturalStep.Stable p.loopPorts (Kept p s L R) := by
  rintro work work' he ⟨hf, hw, hr⟩
  refine ⟨?_, ?_, hR work work' (fun k hk => he k (hk _) (hk _) (hk _)) hr⟩
  · intro i
    simpa only [he _ (p.flag_available i) (p.loop_flag i).symm (p.scratch_flag i).symm] using hf i
  · intro j
    simpa only [he _ (p.word_available j) (p.loop_word j).symm (p.scratch_word j).symm] using hw j

theorem kept_fuel_stable (p : Ports w) (s : State) (L : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    MarkedNaturalLoop.FuelStable p.fuel (Kept p s L R) := by
  rintro work work' he ⟨hf, hw, hr⟩
  exact ⟨(fun i => by simpa only [he _ (p.fuel_flag i).symm] using hf i),
    (fun j => by simpa only [he _ (p.fuel_word j).symm] using hw j),
    hR work work' (fun k hk => he k (hk _)) hr⟩

theorem scratch_hoareTime (p : Ports w) (s : State) (L : ℕ) (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (NaturalRawLoad.machine p.scratch).HoareTime
      (Logical p s L emitted R) (Logical p (moveNatural s) L emitted R) (14 * L + 20) := by
  let C : (Fin (w + 1) → Tape) → Prop := fun work => Kept p s L R work ∧
    (work p.available).head = 1 ∧ (work p.available).read = Γ.ofBool s.available ∧
    (work p.loopAvailable).head = 1 ∧ IsReg L (work p.fuel)
  have hC : ∀ work work', (∀ k, k ≠ p.scratch → work' k = work k) → C work → C work' := by
    rintro work work' he ⟨⟨hf, hw, hr⟩, ha, hv, hl, hn⟩
    exact ⟨⟨(fun i => by simpa only [he _ (p.scratch_flag i).symm] using hf i),
      (fun j => by simpa only [he _ (p.scratch_word j).symm] using hw j),
      hR work work' (fun k hk => he k (hk _)) hr⟩,
      by simpa only [he _ p.scratch_available.symm] using ha,
      by simpa only [he _ p.scratch_available.symm] using hv,
      by simpa only [he _ p.scratch_loop.symm] using hl,
      by simpa only [he _ p.fuel_scratch] using hn⟩
  have h := NaturalRawTotalLoad.hoareTime L p.scratch s.before s.input emitted hlen C hC
  exact h.consequence
    (fun _ _ _ ⟨hc, hr⟩ => ⟨hc, hr.safe, hr.scratch, ⟨hr.flags, hr.words, hr.extra⟩,
      hr.available_head, hr.available_read, hr.loop_head, hr.fuel⟩)
    (fun _ _ _ ⟨hc, hs, _, _, hb, ⟨hf, hw, hr⟩, ha, hv, hl, hn⟩ =>
      ⟨hc, hs, hf, hw, ha, hv, hl, hb, hn, hr⟩) le_rfl

theorem tail_hoareTime (p : Ports w) (s : State) (L : ℕ) (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (MarkedNaturalLoop.machine p.loopPorts p.fuel).HoareTime
      (Logical p s L emitted R) (Logical p (tailRun L s) L emitted R) (MarkedNaturalLoop.timeBound L L) := by
  have h := MarkedNaturalLoop.hoareTime p.loopPorts p.fuel p.fuel_available p.fuel_loop p.fuel_scratch
    (tailState s) L L hlen emitted (Kept p s L R) (kept_stable p s L R hR) (kept_fuel_stable p s L R hR)
  exact h.consequence
    (fun _ _ _ ⟨hc, hr⟩ => ⟨⟨hc, hr.safe, hr.available_head, hr.loop_head, hr.available_read,
      hr.scratch, hr.flags, hr.words, hr.extra⟩, hr.fuel⟩)
    (fun _ _ _ ⟨⟨hc, hs, ha, hl, hv, hb, hf, hw, hr⟩, hn⟩ =>
      ⟨hc, hs, hf, hw, ha, hv, hl, hb, hn, hr⟩) le_rfl

theorem idle_hoareTime (p : Ports w) (s : State) (L : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) :
    (emitBitsTM (n := w + 1) []).HoareTime (Logical p s L emitted R) (Logical p s L emitted R) 0 :=
  (FixedOutput.hoareTime [] s.before s.input emitted (Ready p s L R)).consequence
    (fun _ _ _ ⟨hc, hr⟩ => ⟨hc, hr.safe, hr⟩)
    (fun _ _ _ ⟨hc, _, hr⟩ => by simpa only [List.append_nil, Logical] using And.intro hc hr) le_rfl

theorem branch_hoareTime (p : Ports w) (s t : State) (i : Fin 3) (L time : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (body : TM (w + 1))
    (hbody : body.HoareTime (Logical p s L emitted R) (Logical p t L emitted R) time) :
    (WorkSymbolBranch.machine Γ.one (p.flag i) body (emitBitsTM [])).HoareTime
      (Logical p s L emitted R) (Logical p (if s.flags i then t else s) L emitted R) (time + 2) := by
  cases hi : s.flags i with
  | true =>
    have h := WorkSymbolBranch.yes_hoareTime Γ.one (p.flag i) body (emitBitsTM [])
      s.before s.input emitted t.before t.input emitted (Ready p s L R) (Ready p t L R) time hbody
    apply h.consequence
    · rintro inp work out ⟨hc, hr⟩
      exact ⟨⟨hc, hr⟩, by simpa [hi, Γ.ofBool] using (hr.flags i).2⟩
    · intro inp work out hh
      simpa [hi, Logical] using hh
    · omega
  | false =>
    have h := WorkSymbolBranch.no_hoareTime Γ.one (p.flag i) body (emitBitsTM [])
      s.before s.input emitted s.before s.input emitted (Ready p s L R) (Ready p s L R)
      0 (idle_hoareTime p s L emitted R)
    apply h.consequence
    · rintro inp work out ⟨hc, hr⟩
      refine ⟨⟨hc, hr⟩, ?_⟩
      rw [(hr.flags i).2, hi]
      decide
    · intro inp work out hh
      simpa [hi, Logical] using hh
    · omega

def discard (p : Ports w) : TM (w + 1) :=
  seqTM (NaturalRawLoad.machine p.scratch) (MarkedNaturalLoop.machine p.loopPorts p.fuel)

def overflowMachine (p : Ports w) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one (p.flag 2) (discard p) (emitBitsTM [])

def thirdMachine (p : Ports w) : TM (w + 1) :=
  seqTM (SourceBitRead.machine (p.flag 2) p.available) (overflowMachine p)

def secondMachine (p : Ports w) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one (p.flag 0) (MonomialPrefixStep.machine (p.fieldPorts 1 1)) (emitBitsTM [])

def lastMachine (p : Ports w) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one (p.flag 0)
    (WorkSymbolBranch.machine Γ.one (p.flag 1) (thirdMachine p) (emitBitsTM [])) (emitBitsTM [])

def machine (p : Ports w) : TM (w + 1) :=
  seqTM (seqTM (MonomialPrefixStep.machine (p.fieldPorts 0 0)) (secondMachine p)) (lastMachine p)

def timeBound (L : ℕ) : ℕ := MarkedNaturalLoop.timeBound L L + 42 * L + 100

theorem discard_hoareTime (p : Ports w) (s : State) (L : ℕ) (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (discard p).HoareTime (Logical p s L emitted R) (Logical p (tailRun L (moveNatural s)) L emitted R)
      ((14 * L + 20) + MarkedNaturalLoop.timeBound L L + 1) := by
  have h := seqTM_hoareTime _ _ (scratch_hoareTime p s L hlen emitted R hR) (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩)
    (tail_hoareTime p (moveNatural s) L ((moveNatural_length s).trans hlen) emitted R hR)
  exact h.mono_bound (by omega)

theorem overflow_hoareTime (p : Ports w) (s : State) (L : ℕ) (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (overflowMachine p).HoareTime (Logical p s L emitted R) (Logical p (overflow L s) L emitted R)
      ((14 * L + 20) + MarkedNaturalLoop.timeBound L L + 3) :=
  branch_hoareTime p s (tailRun L (moveNatural s)) 2 L _ emitted R (discard p)
    (discard_hoareTime p s L hlen emitted R hR)

theorem third_hoareTime (p : Ports w) (s : State) (L : ℕ) (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (thirdMachine p).HoareTime (Logical p s L emitted R) (Logical p (third L s) L emitted R)
      ((14 * L + 20) + MarkedNaturalLoop.timeBound L L + 5) := by
  have h := seqTM_hoareTime _ _ (read_hoareTime p s 2 L emitted R hR) (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩)
    (overflow_hoareTime p (MonomialPrefixControl.read s 2) L ((read_length s 2).trans hlen) emitted R hR)
  exact h.mono_bound (by omega)

theorem second_hoareTime (p : Ports w) (s : State) (L : ℕ) (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (secondMachine p).HoareTime (Logical p s L emitted R) (Logical p (second s) L emitted R) (14 * L + 26) :=
  branch_hoareTime p s (field s 1 1) 0 L _ emitted R (MonomialPrefixStep.machine (p.fieldPorts 1 1))
    (field_hoareTime p s 1 1 L hlen emitted R hR)

theorem last_hoareTime (p : Ports w) (s : State) (L : ℕ) (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (lastMachine p).HoareTime (Logical p s L emitted R) (Logical p (last L s) L emitted R)
      ((14 * L + 20) + MarkedNaturalLoop.timeBound L L + 9) :=
  branch_hoareTime p s (if s.flags 1 then third L s else s) 0 L _ emitted R _
    (branch_hoareTime p s (third L s) 1 L _ emitted R _ (third_hoareTime p s L hlen emitted R hR))

theorem hoareTime (p : Ports w) (s : State) (L : ℕ) (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p).HoareTime (Logical p s L emitted R) (Logical p (parse L s) L emitted R) (timeBound L) := by
  have hfirst := field_hoareTime p s 0 0 L hlen emitted R hR
  have hsecond := second_hoareTime p (field s 0 0) L ((prefix_length s 0 0).trans hlen) emitted R hR
  have hpair := seqTM_hoareTime _ _ hfirst (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hsecond
  have hlast := last_hoareTime p (second (field s 0 0)) L
    ((second_length _).trans ((prefix_length s 0 0).trans hlen)) emitted R hR
  have h := seqTM_hoareTime _ _ hpair (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hlast
  exact h.mono_bound (by unfold timeBound; omega)

theorem encoded_hoareTime (p : Ports w) (s : State) (items : List ℕ) (suffix emitted : List Bool) (L : ℕ)
    (hlen : (MarkedNaturalControl.code items ++ suffix).length ≤ L)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p).HoareTime
      (Logical p { s with input := MarkedNaturalControl.code items ++ suffix } L emitted R)
      (Logical p (expected s items suffix) L emitted R) (timeBound L) := by
  have hcode := MarkedNaturalControl.code_length items
  have hf : items.length + 1 ≤ L := by rw [List.length_append] at hlen; omega
  simpa only [parse_code L s items suffix hf] using
    hoareTime p { s with input := MarkedNaturalControl.code items ++ suffix } L hlen emitted R hR

end JointThermoComplexity.Complexity.MonomialPrefixMachine

#print axioms JointThermoComplexity.Complexity.MonomialPrefixMachine.field_hoareTime
#print axioms JointThermoComplexity.Complexity.MonomialPrefixMachine.tail_hoareTime
#print axioms JointThermoComplexity.Complexity.MonomialPrefixMachine.hoareTime
#print axioms JointThermoComplexity.Complexity.MonomialPrefixMachine.encoded_hoareTime
