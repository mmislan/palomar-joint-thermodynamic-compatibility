module
public import proofs.JointThermoComplexity.Complexity.RowEnergyControl

set_option autoImplicit false
@[expose] public section

/-! One actual outer-row step, retaining an active flag outside the row
reader/emitter ports. An inactive step has no source or output effect.
-/

namespace JointThermoComplexity.Complexity.RowEnergyStep
open _root_.Complexity _root_.Complexity.TM BoxBufferState RowEnergyControl
open HeaderAt (Cursor)
variable {w : ℕ}

structure Ports (w : ℕ) where
  square : RowSquareFrame.Ports w
  active : Fin (w + 1)
  active_ne_square : ∀ a, active ≠ square.index a

def Stable (p : Ports w) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work next, (∀ k, k ≠ p.active → (∀ a, k ≠ p.square.index a) → next k = work k) → R work → R next

structure Ready (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape) : Prop where
  square : RowSquareFrame.Ready p.square s.row scaleBits B W R work
  active_head : (work p.active).head = 1
  active_read : (work p.active).read = Γ.ofBool s.active

def Logical (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) :=
  fun inp work out => Cursor s.row.before s.row.input s.emitted inp work out ∧ Ready p s scaleBits B W R work

theorem idle_hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) :
    (emitBitsTM (n := w + 1) []).HoareTime (Logical p s scaleBits B W R)
      (Logical p s scaleBits B W R) 0 :=
  (FixedOutput.hoareTime [] s.row.before s.row.input s.emitted (Ready p s scaleBits B W R)).consequence
    (fun _ _ _ ⟨hc, hr⟩ => ⟨hc, hr.square.saved.safe, hr⟩)
    (fun _ _ _ ⟨hc, _, hr⟩ => by simpa only [List.append_nil, Logical] using And.intro hc hr) le_rfl

theorem read_hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (SourceBitRead.machine p.active p.square.row.available).HoareTime
      (Logical p s scaleBits B W R) (Logical p (afterMarker s) scaleBits B W R) 1 := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin (w + 1) → Tape) → Prop := fun next =>
    ∀ k, k ≠ p.active → k ≠ p.square.row.available → next k = work k
  have hC : ∀ a b, (∀ k, k ≠ p.active → k ≠ p.square.row.available → b k = a k) → C a → C b := by
    intro a b he ha k hi hv
    exact (he k hi hv).trans (ha k hi hv)
  obtain ⟨d, time, ht, hd, hh, hc', hs, ha, hv, hav, hvr, he⟩ :=
    SourceBitRead.hoareTime p.active p.square.row.available (p.active_ne_square _) s.row.before s.row.input s.emitted C hC
      inp work out ⟨hc, hr.square.saved.safe, hr.active_head, hr.square.saved.available_head, fun _ _ _ => rfl⟩
  have kept (a : Fin 25) (heq : a ≠ 21) : d.work (p.square.row.index a) = work (p.square.row.index a) :=
    he _ (p.active_ne_square _).symm (p.square.row.injective.ne heq)
  have hrow : EquationRowFrame.Ready p.square.row (afterMarker s).row B R d.work := by
    refine ⟨hs, ?_, ?_, ?_, ?_, hv, hvr, ?_, ?_, ?_,
      hR work d.work (fun k hk ha => he k hk (ha 21)) hr.square.saved.extra⟩
    · intro i
      have hi := kept (EquationRowFrame.Ports.presenceIndex i)
        (by apply Fin.ne_of_val_ne; dsimp [EquationRowFrame.Ports.presenceIndex]; omega)
      simpa only [afterMarker, EquationRowFrame.Ports.presence, hi] using hr.square.saved.presence i
    · intro i j
      have hi := kept (EquationRowFrame.Ports.slotIndex i ⟨j.val, by omega⟩)
        (by apply Fin.ne_of_val_ne; dsimp [EquationRowFrame.Ports.slotIndex]; omega)
      simpa only [afterMarker, EquationRowFrame.Ports.flag, EquationRowFrame.Ports.slot, hi] using hr.square.saved.flags i j
    · intro i j
      have hi := kept (EquationRowFrame.Ports.slotIndex i ⟨3 + j.val, by omega⟩)
        (by apply Fin.ne_of_val_ne; dsimp [EquationRowFrame.Ports.slotIndex]; omega)
      simpa only [afterMarker, EquationRowFrame.Ports.word, EquationRowFrame.Ports.slot, hi] using hr.square.saved.words i j
    · intro i
      have hi := kept (EquationRowFrame.Ports.slotIndex i 5)
        (by apply Fin.ne_of_val_ne; dsimp [EquationRowFrame.Ports.slotIndex]; omega)
      simpa only [afterMarker, EquationRowFrame.Ports.coefficient, EquationRowFrame.Ports.slot, hi] using hr.square.saved.coefficients i
    · simpa only [EquationRowFrame.Ports.loopAvailable, kept 22 (by decide)] using hr.square.saved.loop_head
    · simpa only [EquationRowFrame.Ports.scratch, kept 23 (by decide)] using hr.square.saved.scratch
    · simpa only [EquationRowFrame.Ports.fuel, kept 24 (by decide)] using hr.square.saved.fuel
  have hscale : d.work p.square.scale = work p.square.scale :=
    he _ (p.active_ne_square _).symm (RowReadSquareMachine.scale_row p.square 21)
  have hconstant : d.work p.square.constant = work p.square.constant :=
    he _ (p.active_ne_square _).symm (p.square.constant_row 21)
  have hcompare : d.work p.square.compare = work p.square.compare :=
    he _ (p.active_ne_square _).symm (p.square.compare_row 21)
  exact ⟨d, time, ht, hd, hh, hc', ⟨⟨hrow,
    by simpa only [hscale] using hr.square.scale,
    by simpa only [hscale] using hr.square.scale_zero,
    hr.square.scale_length, hr.square.word_bound,
    by simpa only [hconstant] using hr.square.constant,
    by simpa only [hcompare] using hr.square.compare_head⟩, ha, hav⟩⟩

theorem row_hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (hB : 2 ≤ B) (hlen : s.row.input.length ≤ B)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (RowReadSquareMachine.machine p.square).HoareTime
      (Logical p s scaleBits B W R) (Logical p (afterRow B scaleBits s) scaleBits B W R)
      (RowReadSquareMachine.timeBound B W) := by
  let C : (Fin (w + 1) → Tape) → Prop := fun work =>
    (work p.active).head = 1 ∧ (work p.active).read = Γ.ofBool s.active ∧ R work
  have hC : RowReadSquareMachine.Stable p.square C := by
    rintro work next he ⟨ha, hd, hr⟩
    exact ⟨by simpa only [he p.active p.active_ne_square] using ha,
      by simpa only [he p.active p.active_ne_square] using hd,
      hR work next (fun k _ hk => he k hk) hr⟩
  have h := RowReadSquareMachine.hoareTime p.square s.row scaleBits B W hB hlen s.emitted C hC
  apply h.consequence
  · rintro inp work out ⟨hc, hr⟩
    exact ⟨hc, { hr.square with saved := { hr.square.saved with extra := ⟨hr.active_head, hr.active_read, hr.square.saved.extra⟩ } }⟩
  · rintro inp work out ⟨hc, hr⟩
    rcases hr.saved.extra with ⟨ha, hd, hx⟩
    exact ⟨hc, ⟨{ hr with saved := { hr.saved with extra := hx } }, ha, hd⟩⟩
  · exact le_rfl

theorem branch_hoareTime (p : Ports w) (s t : State) (scaleBits : List Bool) (B W time : ℕ)
    (R : (Fin (w + 1) → Tape) → Prop) (body : TM (w + 1))
    (hbody : body.HoareTime (Logical p s scaleBits B W R) (Logical p t scaleBits B W R) time) :
    (WorkSymbolBranch.machine Γ.one p.active body (emitBitsTM [])).HoareTime
      (Logical p s scaleBits B W R) (Logical p (if s.active then t else s) scaleBits B W R) (time + 2) := by
  cases hi : s.active with
  | true =>
    have h := WorkSymbolBranch.yes_hoareTime Γ.one p.active body (emitBitsTM [])
      s.row.before s.row.input s.emitted t.row.before t.row.input t.emitted
      (Ready p s scaleBits B W R) (Ready p t scaleBits B W R) time hbody
    apply h.consequence
    · rintro inp work out ⟨hc, hr⟩
      exact ⟨⟨hc, hr⟩, by simpa [hi, Γ.ofBool] using hr.active_read⟩
    · intro inp work out hh
      simpa [hi, Logical] using hh
    · omega
  | false =>
    have h := WorkSymbolBranch.no_hoareTime Γ.one p.active body (emitBitsTM [])
      s.row.before s.row.input s.emitted s.row.before s.row.input s.emitted
      (Ready p s scaleBits B W R) (Ready p s scaleBits B W R) 0 (idle_hoareTime p s scaleBits B W R)
    apply h.consequence
    · rintro inp work out ⟨hc, hr⟩
      refine ⟨⟨hc, hr⟩, ?_⟩
      rw [hr.active_read, hi]
      decide
    · intro inp work out hh
      simpa [hi, Logical] using hh
    · omega

def choice (p : Ports w) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one p.active (RowReadSquareMachine.machine p.square) (emitBitsTM [])

def activeMachine (p : Ports w) : TM (w + 1) :=
  seqTM (SourceBitRead.machine p.active p.square.row.available) (choice p)

def machine (p : Ports w) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one p.active (activeMachine p) (emitBitsTM [])

def timeBound (B W : ℕ) : ℕ := RowReadSquareMachine.timeBound B W + 6

theorem active_hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (hB : 2 ≤ B) (hlen : s.row.input.length ≤ B)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (activeMachine p).HoareTime (Logical p s scaleBits B W R)
      (Logical p (if (afterMarker s).active then afterRow B scaleBits (afterMarker s) else afterMarker s) scaleBits B W R)
      (RowReadSquareMachine.timeBound B W + 4) := by
  have hr := read_hoareTime p s scaleBits B W R hR
  have hb := row_hoareTime p (afterMarker s) scaleBits B W hB ((marker_length s).trans hlen) R hR
  have hc := branch_hoareTime p (afterMarker s) (afterRow B scaleBits (afterMarker s)) scaleBits B W _ R _ hb
  have h := seqTM_hoareTime _ _ hr (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hc
  exact h.mono_bound (by omega)

theorem hoareTime (p : Ports w) (s : State) (scaleBits : List Bool) (B W : ℕ)
    (hB : 2 ≤ B) (hlen : s.row.input.length ≤ B)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p).HoareTime (Logical p s scaleBits B W R)
      (Logical p (step B scaleBits s) scaleBits B W R) (timeBound B W) := by
  exact branch_hoareTime p s
    (if (afterMarker s).active then afterRow B scaleBits (afterMarker s) else afterMarker s)
    scaleBits B W _ R _ (active_hoareTime p s scaleBits B W hB hlen R hR)

end JointThermoComplexity.Complexity.RowEnergyStep

#print axioms JointThermoComplexity.Complexity.RowEnergyStep.read_hoareTime
#print axioms JointThermoComplexity.Complexity.RowEnergyStep.row_hoareTime
#print axioms JointThermoComplexity.Complexity.RowEnergyStep.hoareTime
