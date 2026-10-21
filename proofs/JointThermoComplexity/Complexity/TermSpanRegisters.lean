module
public import proofs.JointThermoComplexity.Complexity.TermSpanCorrect
public import proofs.JointThermoComplexity.Complexity.IntegerSkipRaw

set_option autoImplicit false
@[expose] public section

/-! Seven designated tapes, with additional tapes preserved for enclosing serializers. -/

namespace JointThermoComplexity.Complexity.TermSpanRegisters
open _root_.Complexity _root_.Complexity.TM
open HeaderAt (Cursor)
variable {n : ℕ}

def tags (n : ℕ) (i : Fin 3) : Fin (n + 7) := ⟨i.val, by omega⟩
def pending (n : ℕ) : Fin (n + 7) := ⟨3, by omega⟩
def fuel (n : ℕ) : Fin (n + 7) := ⟨4, by omega⟩
def nodeCounter (n : ℕ) : Fin (n + 7) := ⟨5, by omega⟩
def flag (n : ℕ) : Fin (n + 7) := ⟨6, by omega⟩

theorem tags_injective (n : ℕ) : Function.Injective (tags n) := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun k : Fin (n + 7) => k.val) he

theorem tags_pending (n : ℕ) (i : Fin 3) : tags n i ≠ pending n := by
  intro he; have hv := congrArg Fin.val he; change i.val = 3 at hv; omega
theorem tags_nodeCounter (n : ℕ) (i : Fin 3) : tags n i ≠ nodeCounter n := by
  intro he; have hv := congrArg Fin.val he; change i.val = 5 at hv; omega
theorem tags_flag (n : ℕ) (i : Fin 3) : tags n i ≠ flag n := by
  intro he; have hv := congrArg Fin.val he; change i.val = 6 at hv; omega
theorem fuel_tags (n : ℕ) (i : Fin 3) : fuel n ≠ tags n i := by
  intro he; have hv := congrArg Fin.val he; change 4 = i.val at hv; omega

theorem pending_nodeCounter (n : ℕ) : pending n ≠ nodeCounter n := by
  intro h; have := congrArg Fin.val h; change 3 = 5 at this; omega
theorem pending_flag (n : ℕ) : pending n ≠ flag n := by
  intro h; have := congrArg Fin.val h; change 3 = 6 at this; omega
theorem nodeCounter_flag (n : ℕ) : nodeCounter n ≠ flag n := by
  intro h; have := congrArg Fin.val h; change 5 = 6 at this; omega

def Outside (n : ℕ) (j : Fin (n + 7)) : Prop :=
  j ≠ pending n ∧ j ≠ nodeCounter n ∧ j ≠ flag n ∧ ∀ i, j ≠ tags n i

theorem fuel_outside (n : ℕ) : Outside n (fuel n) :=
  ⟨by intro h; have := congrArg Fin.val h; simp [fuel, pending] at this,
    by intro h; have := congrArg Fin.val h; simp [fuel, nodeCounter] at this,
    by intro h; have := congrArg Fin.val h; simp [fuel, flag] at this, fuel_tags n⟩

def Stable (R : (Fin (n + 7) → Tape) → Prop) : Prop :=
  ∀ work work', (∀ j, Outside n j → work' j = work j) → R work → R work'

structure Ready (count nodes : ℕ) (R : (Fin (n + 7) → Tape) → Prop) (work : Fin (n + 7) → Tape) : Prop where
  safe : ∀ j, Parked (work j)
  markers : ∀ j, (work j).cells 0 = Γ.start
  counter : IsReg count (work (pending n))
  nodeReg : IsReg nodes (work (nodeCounter n))
  tagHeads : ∀ i, (work (tags n i)).head = 1
  flagHead : (work (flag n)).head = 1
  frame : R work

def Inv (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop) (s : TermSpanControl.State) :
    _root_.Complexity.TM.TapePred (n + 7) := fun inp work out =>
  Cursor s.before s.input emitted inp work out ∧ Ready s.pending s.nodes R work

theorem reframe (old count nodes oldNodes : ℕ) (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R)
    (work work' : Fin (n + 7) → Tape) (hr : Ready old oldNodes R work)
    (he : ∀ j, Outside n j → work' j = work j) (hs : ∀ j, Parked (work' j))
    (hz : ∀ j, (work' j).cells 0 = Γ.start) (hp : IsReg count (work' (pending n)))
    (hn : IsReg nodes (work' (nodeCounter n))) (ht : ∀ i, (work' (tags n i)).head = 1)
    (hf : (work' (flag n)).head = 1) : Ready count nodes R work' :=
  ⟨hs, hz, hp, hn, ht, hf, hR work work' he hr.frame⟩

theorem seq_inv_hoareTime (a b : TM (n + 7)) (emitted : List Bool)
    (R : (Fin (n + 7) → Tape) → Prop) (s u v : TermSpanControl.State) (ta tb : ℕ)
    (ha : a.HoareTime (Inv emitted R s) (Inv emitted R u) ta)
    (hb : b.HoareTime (Inv emitted R u) (Inv emitted R v) tb) :
    (seqTM a b).HoareTime (Inv emitted R s) (Inv emitted R v) (ta + 1 + tb) :=
  seqTM_hoareTime a b ha (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hb

theorem noop_hoareTime (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop) (s : TermSpanControl.State) :
    (emitBitsTM (n := n + 7) []).HoareTime (Inv emitted R s) (Inv emitted R s) 0 := by
  have h := FixedOutput.hoareTime [] s.before s.input emitted (Ready s.pending s.nodes R)
  exact h.consequence (by rintro inp work out ⟨hc, hr⟩; exact ⟨hc, hr.safe, hr⟩)
    (by rintro inp work out ⟨hc, _, hr⟩; exact ⟨by simpa only [List.append_nil] using hc, hr⟩) le_rfl

theorem natural_hoareTime (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop) (s : TermSpanControl.State) :
    (NaturalSkip.machine (w := n + 7)).HoareTime (Inv emitted R s)
      (Inv emitted R ⟨s.before ++ PayloadControl.copied .empty s.input,
        NumericCursor.naturalRest s.input, s.pending, s.nodes⟩) (s.input.length + 1) :=
  NaturalSkipRaw.hoareTime s.before s.input emitted (fun work _ => Ready s.pending s.nodes R work)

theorem integer_hoareTime (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop) (s : TermSpanControl.State) :
    (IntegerSkipRaw.machine (w := n + 7)).HoareTime (Inv emitted R s)
      (Inv emitted R ⟨s.before ++ IntegerMachineRun.copied s.input,
        NumericCursor.integerRest s.input, s.pending, s.nodes⟩) (s.input.length + 3) :=
  IntegerSkipRaw.hoareTime s.before s.input emitted (fun work _ => Ready s.pending s.nodes R work)

theorem status_hoareTime (value : Bool) (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop)
    (hR : Stable R) (s : TermSpanControl.State) :
    (SourceTermToken.setStatus (flag n) value).HoareTime (Inv emitted R s)
      (fun inp work out => Inv emitted R s inp work out ∧ (work (flag n)).read = Γ.ofBool value) 1 := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin (n + 7) → Tape) → Prop := fun work' => ∀ j, j ≠ flag n → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ flag n → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj
    exact (he j hj).trans (hp j hj)
  obtain ⟨c, t, ht, hd, hh, hc', hs', hfh, hfv, hother⟩ :=
    SourceTermToken.setStatus_hoareTime (flag n) value s.before s.input emitted C hC
      inp work out ⟨hc, hr.safe, hr.flagHead, fun _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hp : IsReg s.pending (c.work (pending n)) := by
    rw [hother _ (by intro h; have := congrArg Fin.val h; simp [pending, flag] at this)]
    exact hr.counter
  have hn : IsReg s.nodes (c.work (nodeCounter n)) := by
    rw [hother _ (by intro h; have := congrArg Fin.val h; simp [nodeCounter, flag] at this)]
    exact hr.nodeReg
  have htags : ∀ i, (c.work (tags n i)).head = 1 := fun i => by
    rw [hother _ (tags_flag n i)]
    exact hr.tagHeads i
  have hr' := reframe s.pending s.pending s.nodes s.nodes R hR work c.work hr
    (fun j hj => hother j hj.2.2.1) hs' (fun j => (hm.2.1 j).1) hp hn htags hfh
  exact ⟨c, t, ht, hd, hh, ⟨hc', hr'⟩, hfv⟩

end JointThermoComplexity.Complexity.TermSpanRegisters

#print axioms JointThermoComplexity.Complexity.TermSpanRegisters.natural_hoareTime
#print axioms JointThermoComplexity.Complexity.TermSpanRegisters.integer_hoareTime
#print axioms JointThermoComplexity.Complexity.TermSpanRegisters.status_hoareTime
