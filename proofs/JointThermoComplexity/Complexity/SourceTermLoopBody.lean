module
public import proofs.JointThermoComplexity.Complexity.SourceTermLoopState
public import proofs.JointThermoComplexity.Complexity.FlagBranchNonone

set_option autoImplicit false
@[expose] public section

/-! Actual loop guards preserve rejected/completed states and advance one positive pending token. -/

namespace JointThermoComplexity.Complexity.SourceTermLoopBody
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceIndexField
open SourceTermTokenRun SourceTermLoopState
variable {n : ℕ}

def Extra (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1)) (L arity : ℕ)
    (R : (Fin (n + 1) → Tape) → Prop) (s : State) (work : Fin (n + 2) → Tape) : Prop :=
  Ready L left right arity R work ∧ IsReg s.pending (work pending.castSucc) ∧
  (∀ i, (work (ports i).castSucc).head = 1) ∧ (work (NaturalScanBuffer.flag n)).read = Γ.ofBool s.valid

def Inv (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1)) (L arity : ℕ)
    (emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop) (s : State) : _root_.Complexity.TM.TapePred (n + 2) :=
  fun inp work out => Cursor s.before s.input emitted inp work out ∧ Extra ports pending left right L arity R s work

def pendingMachine (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1)) : TM (n + 2) :=
  FlagBranch.machine pending.castSucc (SourceTermStep.machine ports pending left right) (emitBitsTM [])

def machine (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1)) : TM (n + 2) :=
  FlagBranch.machine (NaturalScanBuffer.flag n) (pendingMachine ports pending left right) (emitBitsTM [])

theorem noop_hoareTime (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1)) (L arity : ℕ)
    (emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop) (s : State) :
    (emitBitsTM (n := n + 2) []).HoareTime (Inv ports pending left right L arity emitted R s)
      (Inv ports pending left right L arity emitted R s) 0 := by
  have h := FixedOutput.hoareTime [] s.before s.input emitted (Extra ports pending left right L arity R s)
  exact h.consequence (by rintro inp work out ⟨hc, hr, hp⟩; exact ⟨hc, hr.safe, hr, hp⟩)
    (by simpa only [List.append_nil] using fun _ _ _ h => ⟨h.1, h.2.2⟩) le_rfl

theorem pending_hoareTime (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1))
    (hs : SourceTermTagRead.Separate ports left right)
    (sep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n))
    (hp : SourcePendingFrame.Separate ports pending left right) (L arity P count : ℕ) (hcount : count ≤ P)
    (ha : arity.bits.length ≤ L) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ i, j ≠ ports i) → j ≠ pending → work' j = work j) → R work → R work') :
    (pendingMachine ports pending left right).HoareTime
      (Inv ports pending left right L arity emitted R ⟨before, input, count, true⟩)
      (Inv ports pending left right L arity emitted R (step arity ⟨before, input, count, true⟩)) (32 * L + 2 * P + 83) := by
  cases count with
  | zero =>
    let s : State := ⟨before, input, 0, true⟩
    have hb := FlagBranchNonone.hoareTime pending.castSucc (SourceTermStep.machine ports pending left right) (emitBitsTM [])
      before input emitted before input emitted (Extra ports pending left right L arity R s)
      (Extra ports pending left right L arity R s) 0 (noop_hoareTime ports pending left right L arity emitted R s)
    exact hb.consequence (by
      rintro inp work out h
      refine ⟨h, ?_⟩
      have hv := h.2.2.1.read_eq
      change (work pending.castSucc).read = Γ.blank at hv
      rw [hv]
      decide) (fun _ _ _ h => h) (by omega)
  | succ v =>
    let s : State := ⟨before, input, v + 1, true⟩
    have hstep := SourceTermStep.hoareTime ports pending left right hs sep hp L arity v ha true before input emitted hlen R hR
    have hyes : (SourceTermStep.machine ports pending left right).HoareTime
        (Inv ports pending left right L arity emitted R s)
        (Inv ports pending left right L arity emitted R (step arity s)) (32 * L + 2 * v + 82) :=
      hstep.consequence (fun _ _ _ h => h) (by
        rintro inp work out ⟨hc, hr, hp, ht, hf⟩
        exact ⟨hc, hr, hp, fun i => (ht i).1, hf⟩) le_rfl
    have hb := FlagBranchRun.yes_hoareTime pending.castSucc (SourceTermStep.machine ports pending left right) (emitBitsTM [])
      before input emitted (step arity s).before (step arity s).input emitted
      (Extra ports pending left right L arity R s) (Extra ports pending left right L arity R (step arity s))
      (32 * L + 2 * v + 82) hyes
    exact hb.consequence (by
      rintro inp work out h
      refine ⟨h, ?_⟩
      have hv := h.2.2.1.read_eq
      simpa only [s, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] using hv)
      (fun _ _ _ h => h) (by omega)

theorem hoareTime (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1))
    (hs : SourceTermTagRead.Separate ports left right)
    (sep : BinaryDifferenceCursor.Separate left right (NaturalMachine.flagIndex n))
    (hp : SourcePendingFrame.Separate ports pending left right) (L arity P : ℕ) (ha : arity.bits.length ≤ L)
    (emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop) (s : State)
    (hlen : s.input.length ≤ L) (hcount : s.pending ≤ P)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ NaturalMachine.flagIndex n →
      (∀ i, j ≠ ports i) → j ≠ pending → work' j = work j) → R work → R work') :
    (machine ports pending left right).HoareTime (Inv ports pending left right L arity emitted R s)
      (Inv ports pending left right L arity emitted R (step arity s)) (32 * L + 2 * P + 84) := by
  cases s with
  | mk before input count valid =>
    cases valid with
    | false =>
      let s : State := ⟨before, input, count, false⟩
      have hb := FlagBranchRun.no_hoareTime (NaturalScanBuffer.flag n) (pendingMachine ports pending left right) (emitBitsTM [])
        before input emitted before input emitted (Extra ports pending left right L arity R s)
        (Extra ports pending left right L arity R s) 0 (noop_hoareTime ports pending left right L arity emitted R s)
      exact hb.consequence (fun _ _ _ h => ⟨h, h.2.2.2.2⟩) (fun _ _ _ h => h) (by omega)
    | true =>
      let s : State := ⟨before, input, count, true⟩
      have hpending := pending_hoareTime ports pending left right hs sep hp L arity P count hcount ha before input emitted hlen R hR
      have hb := FlagBranchRun.yes_hoareTime (NaturalScanBuffer.flag n) (pendingMachine ports pending left right) (emitBitsTM [])
        before input emitted (step arity s).before (step arity s).input emitted
        (Extra ports pending left right L arity R s) (Extra ports pending left right L arity R (step arity s))
        (32 * L + 2 * P + 83) hpending
      exact hb.consequence (fun _ _ _ h => ⟨h, h.2.2.2.2⟩) (fun _ _ _ h => h) (by omega)

end JointThermoComplexity.Complexity.SourceTermLoopBody

#print axioms JointThermoComplexity.Complexity.SourceTermLoopBody.pending_hoareTime
#print axioms JointThermoComplexity.Complexity.SourceTermLoopBody.hoareTime
