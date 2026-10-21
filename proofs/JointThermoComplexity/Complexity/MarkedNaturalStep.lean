module
public import proofs.JointThermoComplexity.Complexity.MarkedNaturalControl
public import proofs.JointThermoComplexity.Complexity.NaturalRawTotalLoad
public import proofs.JointThermoComplexity.Complexity.WorkSymbolBranch
public import proofs.JointThermoComplexity.Complexity.FixedOutput

set_option autoImplicit false
@[expose] public section

/-! One actual marked-natural traversal step. Inactive iterations do nothing;
an active marker controls a total raw-field load into a reusable scratch slot.
-/

namespace JointThermoComplexity.Complexity.MarkedNaturalStep
open _root_.Complexity _root_.Complexity.TM BoxBufferState MarkedNaturalControl
open HeaderAt (Cursor)
variable {w : ℕ}

structure Ports (w : ℕ) where
  active : Fin (w + 1)
  presence : Fin (w + 1)
  buffer : Fin (w + 1)
  active_ne_presence : active ≠ presence
  buffer_ne_active : buffer ≠ active
  buffer_ne_presence : buffer ≠ presence

def Stable (p : Ports w) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work work', (∀ j, j ≠ p.active → j ≠ p.presence → j ≠ p.buffer → work' j = work j) → R work → R work'

def Ready (p : Ports w) (s : State) (L : ℕ) (R : (Fin (w + 1) → Tape) → Prop)
    (work : Fin (w + 1) → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ (work p.active).head = 1 ∧ (work p.presence).head = 1 ∧
    (work p.active).read = Γ.ofBool s.active ∧ Reusable L (work p.buffer) ∧ R work

theorem idle_hoareTime (p : Ports w) (s : State) (L : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) :
    (emitBitsTM (n := w + 1) []).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s L R work)
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s L R work) 0 :=
  (FixedOutput.hoareTime [] s.before s.input emitted (Ready p s L R)).consequence
    (fun _ _ _ ⟨hc, hr⟩ => ⟨hc, hr.1, hr⟩)
    (fun _ _ _ ⟨hc, _, hr⟩ => by simpa only [List.append_nil] using And.intro hc hr) le_rfl

theorem read_hoareTime (p : Ports w) (s : State) (L : ℕ) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (SourceBitRead.machine p.active p.presence).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s L R work)
      (fun inp work out => Cursor (afterMarker s).before (afterMarker s).input emitted inp work out ∧
        Ready p (afterMarker s) L R work) 1 := by
  let C : (Fin (w + 1) → Tape) → Prop := fun work => Reusable L (work p.buffer) ∧ R work
  have hC : ∀ work work', (∀ j, j ≠ p.active → j ≠ p.presence → work' j = work j) → C work → C work' := by
    rintro work work' he ⟨hb, hr⟩
    exact ⟨by simpa only [he _ p.buffer_ne_active p.buffer_ne_presence] using hb,
      hR work work' (fun j ha hp _ => he j ha hp) hr⟩
  have h := SourceBitRead.hoareTime p.active p.presence p.active_ne_presence s.before s.input emitted C hC
  exact h.consequence
    (fun _ _ _ ⟨hc, hs, ha, hp, _, hb, hr⟩ => ⟨hc, hs, ha, hp, hb, hr⟩)
    (fun _ _ _ ⟨hc, hs, ha, hp, hd, _, hb, hr⟩ => ⟨hc, hs, ha, hp, hd, hb, hr⟩) le_rfl

theorem load_hoareTime (p : Ports w) (s : State) (L : ℕ) (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (NaturalRawLoad.machine p.buffer).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s L R work)
      (fun inp work out => Cursor (afterNatural s).before (afterNatural s).input emitted inp work out ∧
        Ready p (afterNatural s) L R work) (14 * L + 20) := by
  let C : (Fin (w + 1) → Tape) → Prop := fun work => (work p.active).head = 1 ∧ (work p.presence).head = 1 ∧
    (work p.active).read = Γ.ofBool s.active ∧ R work
  have hC : ∀ work work', (∀ j, j ≠ p.buffer → work' j = work j) → C work → C work' := by
    rintro work work' he ⟨ha, hp, hd, hr⟩
    exact ⟨by simpa only [he _ p.buffer_ne_active.symm] using ha,
      by simpa only [he _ p.buffer_ne_presence.symm] using hp,
      by simpa only [he _ p.buffer_ne_active.symm] using hd,
      hR work work' (fun j _ _ hb => he j hb) hr⟩
  have h := NaturalRawTotalLoad.hoareTime L p.buffer s.before s.input emitted hlen C hC
  exact h.consequence
    (fun _ _ _ ⟨hc, hs, ha, hp, hd, hb, hr⟩ => ⟨hc, hs, hb, ha, hp, hd, hr⟩)
    (fun _ _ _ ⟨hc, hs, _, _, hb, ha, hp, hd, hr⟩ => ⟨hc, hs, ha, hp, hd, hb, hr⟩) le_rfl

def loadChoice (p : Ports w) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one p.active (NaturalRawLoad.machine p.buffer) (emitBitsTM [])

theorem choice_hoareTime (p : Ports w) (s : State) (L : ℕ) (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (loadChoice p).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s L R work)
      (fun inp work out => Cursor (if s.active then afterNatural s else s).before (if s.active then afterNatural s else s).input
        emitted inp work out ∧ Ready p (if s.active then afterNatural s else s) L R work) (14 * L + 22) := by
  cases hactive : s.active with
  | true =>
    have h := WorkSymbolBranch.yes_hoareTime Γ.one p.active (NaturalRawLoad.machine p.buffer) (emitBitsTM [])
      s.before s.input emitted (afterNatural s).before (afterNatural s).input emitted
      (Ready p s L R) (Ready p (afterNatural s) L R) (14 * L + 20) (load_hoareTime p s L hlen emitted R hR)
    apply h.consequence
    · rintro inp work out ⟨hc, hs, ha, hp, hd, hb, hr⟩
      exact ⟨⟨hc, hs, ha, hp, hd, hb, hr⟩, by simpa [hactive, Γ.ofBool] using hd⟩
    · intro inp work out hh
      simpa [hactive] using hh
    · omega
  | false =>
    have h := WorkSymbolBranch.no_hoareTime Γ.one p.active (NaturalRawLoad.machine p.buffer) (emitBitsTM [])
      s.before s.input emitted s.before s.input emitted (Ready p s L R) (Ready p s L R) 0 (idle_hoareTime p s L emitted R)
    apply h.consequence
    · rintro inp work out ⟨hc, hs, ha, hp, hd, hb, hr⟩
      refine ⟨⟨hc, hs, ha, hp, hd, hb, hr⟩, ?_⟩
      rw [hd, hactive]
      decide
    · intro inp work out hh
      simpa [hactive] using hh
    · omega

def activeMachine (p : Ports w) : TM (w + 1) :=
  seqTM (SourceBitRead.machine p.active p.presence) (loadChoice p)

theorem active_hoareTime (p : Ports w) (s : State) (L : ℕ) (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (activeMachine p).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s L R work)
      (fun inp work out =>
        Cursor (if (afterMarker s).active then afterNatural (afterMarker s) else afterMarker s).before
          (if (afterMarker s).active then afterNatural (afterMarker s) else afterMarker s).input emitted inp work out ∧
        Ready p (if (afterMarker s).active then afterNatural (afterMarker s) else afterMarker s) L R work) (14 * L + 24) := by
  have hr := read_hoareTime p s L emitted R hR
  have hc := choice_hoareTime p (afterMarker s) L ((afterMarker_length s).trans hlen) emitted R hR
  have h := seqTM_hoareTime (SourceBitRead.machine p.active p.presence) (loadChoice p) hr (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hc
  exact h.mono_bound (by omega)

def machine (p : Ports w) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one p.active (activeMachine p) (emitBitsTM [])

theorem hoareTime (p : Ports w) (s : State) (L : ℕ) (hlen : s.input.length ≤ L) (emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Ready p s L R work)
      (fun inp work out => Cursor (step s).before (step s).input emitted inp work out ∧ Ready p (step s) L R work)
      (14 * L + 30) := by
  cases hactive : s.active with
  | true =>
    have h := WorkSymbolBranch.yes_hoareTime Γ.one p.active (activeMachine p) (emitBitsTM [])
      s.before s.input emitted _ _ emitted (Ready p s L R) _ (14 * L + 24) (active_hoareTime p s L hlen emitted R hR)
    apply h.consequence
    · rintro inp work out ⟨hc, hs, ha, hp, hd, hb, hr⟩
      exact ⟨⟨hc, hs, ha, hp, hd, hb, hr⟩, by simpa [hactive, Γ.ofBool] using hd⟩
    · intro inp work out hh
      simpa [MarkedNaturalControl.step, hactive] using hh
    · omega
  | false =>
    have h := WorkSymbolBranch.no_hoareTime Γ.one p.active (activeMachine p) (emitBitsTM [])
      s.before s.input emitted s.before s.input emitted (Ready p s L R) (Ready p s L R) 0 (idle_hoareTime p s L emitted R)
    apply h.consequence
    · rintro inp work out ⟨hc, hs, ha, hp, hd, hb, hr⟩
      refine ⟨⟨hc, hs, ha, hp, hd, hb, hr⟩, ?_⟩
      rw [hd, hactive]
      decide
    · intro inp work out hh
      simpa [MarkedNaturalControl.step, hactive] using hh
    · omega

end JointThermoComplexity.Complexity.MarkedNaturalStep

#print axioms JointThermoComplexity.Complexity.MarkedNaturalStep.read_hoareTime
#print axioms JointThermoComplexity.Complexity.MarkedNaturalStep.load_hoareTime
#print axioms JointThermoComplexity.Complexity.MarkedNaturalStep.hoareTime
