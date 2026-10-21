module
public import proofs.JointThermoComplexity.Complexity.MonomialPrefixControl
public import proofs.JointThermoComplexity.Complexity.MarkedNaturalStep

set_option autoImplicit false
@[expose] public section

/-! Exact saved-bit interface for an actual marked-field reader. The machine
is the already checked marker/load composition; this stronger frame exposes
the loaded binary word and keeps a rewound old word on the false branch.
-/

namespace JointThermoComplexity.Complexity.MonomialPrefixStep
open _root_.Complexity _root_.Complexity.TM BoxBufferState MonomialPrefixControl
open MarkedNaturalStep (Ports Stable)
open HeaderAt (Cursor)
variable {w : ℕ}

def Ready (p : Ports w) (s : State) (i : Fin 3) (j : Fin 2) (L : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape) : Prop :=
  (∀ k, Parked (work k)) ∧ (work p.active).head = 1 ∧ (work p.presence).head = 1 ∧
    (work p.active).read = Γ.ofBool (s.flags i) ∧ (work p.presence).read = Γ.ofBool s.available ∧
    (work p.buffer).HasBinaryString (s.words j) ∧ (work p.buffer).cells 0 = Γ.start ∧
    (s.words j).length ≤ 4 * L ∧ R work

theorem idle_hoareTime (p : Ports w) (s : State) (i : Fin 3) (j : Fin 2) (L : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) :
    (emitBitsTM (n := w + 1) []).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s i j L R work)
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s i j L R work) 0 :=
  (FixedOutput.hoareTime [] s.before s.input emitted (Ready p s i j L R)).consequence
    (fun _ _ _ ⟨hc, hr⟩ => ⟨hc, hr.1, hr⟩)
    (fun _ _ _ ⟨hc, _, hr⟩ => by simpa only [List.append_nil] using And.intro hc hr) le_rfl

theorem read_hoareTime (p : Ports w) (s : State) (i : Fin 3) (j : Fin 2) (L : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (SourceBitRead.machine p.active p.presence).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s i j L R work)
      (fun inp work out => Cursor (read s i).before (read s i).input emitted inp work out ∧ Ready p (read s i) i j L R work) 1 := by
  let C : (Fin (w + 1) → Tape) → Prop := fun work =>
    (work p.buffer).HasBinaryString (s.words j) ∧ (work p.buffer).cells 0 = Γ.start ∧
    (s.words j).length ≤ 4 * L ∧ R work
  have hC : ∀ work work', (∀ k, k ≠ p.active → k ≠ p.presence → work' k = work k) → C work → C work' := by
    rintro work work' he ⟨hb, hz, hl, hr⟩
    exact ⟨by simpa only [he _ p.buffer_ne_active p.buffer_ne_presence] using hb,
      by simpa only [he _ p.buffer_ne_active p.buffer_ne_presence] using hz, hl,
      hR work work' (fun k ha hp _ => he k ha hp) hr⟩
  have h := SourceBitRead.hoareTime p.active p.presence p.active_ne_presence s.before s.input emitted C hC
  exact h.consequence
    (fun _ _ _ ⟨hc, hs, ha, hp, _, _, hb, hz, hl, hr⟩ => ⟨hc, hs, ha, hp, hb, hz, hl, hr⟩)
    (fun _ _ _ ⟨hc, hs, ha, hp, hd, hv, hb, hz, hl, hr⟩ =>
      ⟨hc, hs, ha, hp, by simpa only [MonomialPrefixControl.read, Function.update_self] using hd, hv, hb, hz, hl, hr⟩) le_rfl

theorem load_hoareTime (p : Ports w) (s : State) (i : Fin 3) (j : Fin 2) (L : ℕ)
    (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (NaturalRawLoad.machine p.buffer).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s i j L R work)
      (fun inp work out => Cursor (load s j).before (load s j).input emitted inp work out ∧ Ready p (load s j) i j L R work)
      (14 * L + 20) := by
  let C : (Fin (w + 1) → Tape) → Prop := fun work => (work p.active).head = 1 ∧ (work p.presence).head = 1 ∧
    (work p.active).read = Γ.ofBool (s.flags i) ∧ (work p.presence).read = Γ.ofBool s.available ∧ R work
  have hC : ∀ work work', (∀ k, k ≠ p.buffer → work' k = work k) → C work → C work' := by
    rintro work work' he ⟨ha, hp, hd, hv, hr⟩
    exact ⟨by simpa only [he _ p.buffer_ne_active.symm] using ha,
      by simpa only [he _ p.buffer_ne_presence.symm] using hp,
      by simpa only [he _ p.buffer_ne_active.symm] using hd,
      by simpa only [he _ p.buffer_ne_presence.symm] using hv,
      hR work work' (fun k _ _ hb => he k hb) hr⟩
  have h := NaturalRawTotalLoad.hoareTime L p.buffer s.before s.input emitted hlen C hC
  apply h.consequence
  · rintro inp work out ⟨hc, hs, ha, hp, hd, hv, hb, hz, hl, hr⟩
    exact ⟨hc, hs, ⟨s.words j, hl, hb.2, hz, by rw [hb.1]; omega⟩, ha, hp, hd, hv, hr⟩
  · rintro inp work out ⟨hc, hs, hb, hz, _, ha, hp, hd, hv, hr⟩
    refine ⟨hc, hs, ha, hp, hd, hv, ?_, hz, ?_, hr⟩
    · simpa only [load, Function.update_self] using hb
    · simp only [MonomialPrefixControl.load, Function.update_self]
      have := (NaturalRawControl.bits_length s.input).trans hlen
      omega
  · exact le_rfl

theorem choice_hoareTime (p : Ports w) (s : State) (i : Fin 3) (j : Fin 2) (L : ℕ)
    (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (MarkedNaturalStep.loadChoice p).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s i j L R work)
      (fun inp work out =>
        Cursor (if s.flags i then load s j else s).before (if s.flags i then load s j else s).input emitted inp work out ∧
        Ready p (if s.flags i then load s j else s) i j L R work) (14 * L + 22) := by
  cases hf : s.flags i with
  | true =>
    have h := WorkSymbolBranch.yes_hoareTime Γ.one p.active (NaturalRawLoad.machine p.buffer) (emitBitsTM [])
      s.before s.input emitted _ _ emitted (Ready p s i j L R) (Ready p (load s j) i j L R)
      (14 * L + 20) (load_hoareTime p s i j L hlen emitted R hR)
    apply h.consequence
    · rintro inp work out hh
      exact ⟨hh, by simpa [hf, Γ.ofBool] using hh.2.2.2.2.1⟩
    · intro inp work out hh
      simpa [hf] using hh
    · omega
  | false =>
    have h := WorkSymbolBranch.no_hoareTime Γ.one p.active (NaturalRawLoad.machine p.buffer) (emitBitsTM [])
      s.before s.input emitted s.before s.input emitted (Ready p s i j L R) (Ready p s i j L R)
      0 (idle_hoareTime p s i j L emitted R)
    apply h.consequence
    · rintro inp work out hh
      refine ⟨hh, ?_⟩
      rw [hh.2.2.2.2.1, hf]
      decide
    · intro inp work out hh
      simpa [hf] using hh
    · omega

def machine (p : Ports w) : TM (w + 1) := MarkedNaturalStep.activeMachine p

theorem hoareTime (p : Ports w) (s : State) (i : Fin 3) (j : Fin 2) (L : ℕ)
    (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s i j L R work)
      (fun inp work out => Cursor (field s i j).before (field s i j).input emitted inp work out ∧
        Ready p (field s i j) i j L R work) (14 * L + 24) := by
  have hr := read_hoareTime p s i j L emitted R hR
  have hc := choice_hoareTime p (read s i) i j L ((read_length s i).trans hlen) emitted R hR
  have h := seqTM_hoareTime (SourceBitRead.machine p.active p.presence) (MarkedNaturalStep.loadChoice p) hr (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hc
  exact h.mono_bound (by omega)

end JointThermoComplexity.Complexity.MonomialPrefixStep

#print axioms JointThermoComplexity.Complexity.MonomialPrefixStep.read_hoareTime
#print axioms JointThermoComplexity.Complexity.MonomialPrefixStep.load_hoareTime
#print axioms JointThermoComplexity.Complexity.MonomialPrefixStep.hoareTime
