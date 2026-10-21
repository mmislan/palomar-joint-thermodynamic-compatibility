module
public import proofs.JointThermoComplexity.Complexity.LeafRowEmitter
public import proofs.JointThermoComplexity.Complexity.InputCheckpointTransition
public import proofs.JointThermoComplexity.Complexity.InputBitSkip
public import proofs.JointThermoComplexity.Complexity.RealSyntax

set_option autoImplicit false
@[expose] public section

/-! Complete leaf-node emission skips its tag, emits one raw row and restores the node cursor. -/

namespace JointThermoComplexity.Complexity.LeafLocalEquation
open _root_.Complexity _root_.Complexity.TM HeaderAt

def anchor : Fin 32 := ⟨30, by decide⟩

def Stable (R : (Fin 32 → Tape) → Prop) : Prop :=
  ∀ work work', (∀ j, j ≠ LeafRowEmitter.flag → j ≠ anchor → work' j = work j) → R work → R work'

structure Ready (v : ℕ) (R : (Fin 32 → Tape) → Prop) (work : Fin 32 → Tape) : Prop where
  rootReg : IsReg v (work LeafRowEmitter.root)
  scratchReg : IsReg 0 (work LeafRowEmitter.scratch)
  flagHead : (work LeafRowEmitter.flag).head = 1
  markers : ∀ j, j ≠ anchor → (work j).cells 0 = Γ.start
  frame : R work

theorem ready_anchor (v : ℕ) (R : (Fin 32 → Tape) → Prop) (hR : Stable R) :
    ∀ work work', (∀ j, j ≠ anchor → work' j = work j) → Ready v R work → Ready v R work' := by
  rintro work work' he hr
  exact ⟨by simpa only [he _ (by decide : LeafRowEmitter.root ≠ anchor)] using hr.rootReg,
    by simpa only [he _ (by decide : LeafRowEmitter.scratch ≠ anchor)] using hr.scratchReg,
    by simpa only [he _ (by decide : LeafRowEmitter.flag ≠ anchor)] using hr.flagHead,
    fun j hj => by simpa only [he j hj] using hr.markers j hj,
    hR work work' (fun j _ hj => he j hj) hr.frame⟩

def skip : ℕ → TM 32
  | 0 => emitBitsTM []
  | n + 1 => seqTM InputBitSkip.machine (skip n)

theorem skip_hoareTime (n : ℕ) (before input emitted : List Bool) (P : (Fin 32 → Tape) → Tape → Prop) :
    (skip n).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work out)
      (fun inp work out => Cursor (before ++ input.take n) (input.drop n) emitted inp work out ∧ P work out) (2 * n) := by
  induction n generalizing before input with
  | zero =>
    rintro inp work out ⟨hc, hp⟩
    exact ⟨⟨(emitBitsTM (n := 32) []).qhalt, inp, work, out⟩, 0, le_rfl, .zero, rfl,
      by simpa only [List.take_zero, List.drop_zero, List.append_nil] using hc, hp⟩
  | succ n ih =>
    have hb := InputBitSkip.hoareTime before input emitted P
    have ht := ih (before ++ input.take 1) (input.drop 1)
    have hseq := seqTM_hoareTime (InputBitSkip.machine (w := 32)) (skip n) hb (by
      rintro inp work out ⟨hc, hp⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hp⟩) ht
    apply hseq.consequence (fun _ _ _ h => h)
    · rintro inp work out h
      have hp : (before ++ input.take 1) ++ (input.drop 1).take n = before ++ input.take (n + 1) := by
        rw [show n + 1 = 1 + n by omega, List.take_add, List.append_assoc]
      have hd : (input.drop 1).drop n = input.drop (n + 1) := by rw [List.drop_drop, Nat.add_comm]
      simpa only [hp, hd] using h
    · omega

def forward (isVar : Bool) : TM 32 := seqTM (skip 3) (LeafRowEmitter.machine isVar)
def machine (isVar : Bool) : TM 32 := InputCheckpoint.around anchor (forward isVar)
def output (isVar : Bool) (v : ℕ) (input : List Bool) : List Bool := LeafRowEmitter.output isVar v (input.drop 3)

theorem forward_hoareTime (isVar : Bool) (v B p : ℕ) (hv : v ≤ B) (before input emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) (hR : Stable R) :
    (forward isVar).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ Ready v R work)
      (fun inp work out => Cursor ((before ++ input.take 3) ++ LeafRowEmitter.taken isVar (input.drop 3))
        (LeafRowEmitter.rest isVar (input.drop 3)) (emitted ++ output isVar v input) inp work out ∧
          (∀ j, Parked (work j)) ∧ IsReg p (work anchor) ∧ Ready v R work)
      (ReusableIndexEmitter.timeBound B + input.length + 47) := by
  let C : (Fin 32 → Tape) → Prop := fun work => IsReg p (work anchor) ∧ R work
  have hC : ∀ work work', (∀ j, j ≠ LeafRowEmitter.flag → work' j = work j) → C work → C work' := by
    rintro work work' he ⟨hp, hr⟩
    exact ⟨by simpa only [he _ (by decide : anchor ≠ LeafRowEmitter.flag)] using hp,
      hR work work' (fun j hj _ => he j hj) hr⟩
  have hs := skip_hoareTime 3 before input emitted (fun work _ => (∀ j, Parked (work j)) ∧ LeafRowEmitter.Ready v C work)
  have hl := LeafRowEmitter.hoareTime isVar v B hv (before ++ input.take 3) (input.drop 3) emitted C hC
  have hseq := seqTM_hoareTime (skip 3) (LeafRowEmitter.machine isVar) hs (by
    rintro inp work out ⟨hc, hw, hr⟩
    obtain ⟨hi, hworks, ho⟩ := hc.phase
    rw [hi, hworks, ho]
    exact ⟨hc, hw, hr⟩) hl
  apply hseq.consequence
  · rintro inp work out ⟨hc, hw, hp, hr⟩
    refine ⟨hc, hw, hr.rootReg, hr.scratchReg, hr.flagHead, ?_, hp, hr.frame⟩
    intro j
    by_cases hj : j = anchor
    · subst j
      exact hp.cell0
    · exact hr.markers j hj
  · rintro inp work out ⟨hc, hw, hr⟩
    exact ⟨hc, hw, hr.frame.1, hr.rootReg, hr.scratchReg, hr.flagHead, fun j _ => hr.markers j, hr.frame.2⟩
  · simp only [List.length_drop]
    omega

theorem hoareTime (isVar : Bool) (v B : ℕ) (hv : v ≤ B) (before input emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) (hR : Stable R) :
    (machine isVar).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work anchor) ∧ Ready v R work)
      (fun inp work out => Cursor before input (emitted ++ output isVar v input) inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work anchor) ∧ Ready v R work)
      (ReusableIndexEmitter.timeBound B + 2 * input.length + 13 * before.length + 70) := by
  let consumed := (before ++ input.take 3) ++ LeafRowEmitter.taken isVar (input.drop 3)
  let remaining := LeafRowEmitter.rest isVar (input.drop 3)
  have hsplit : consumed ++ remaining = before ++ input := by
    simp only [consumed, remaining, List.append_assoc, LeafRowEmitter.split, List.take_append_drop]
  have h := InputCheckpointTransition.hoareTime anchor (forward isVar) before input consumed remaining emitted
    (emitted ++ output isVar v input) hsplit (Ready v R) (Ready v R) (ready_anchor v R hR) (ready_anchor v R hR)
    (ReusableIndexEmitter.timeBound B + input.length + 47) (forward_hoareTime isVar v B before.length hv before input emitted R hR)
  apply h.mono_bound
  have hw := congrArg List.length hsplit
  simp only [List.length_append] at hw
  omega

theorem integer_code {n : ℕ} (z : ℤ) (hz : z.natAbs ≤ 2) (v : ℕ) (suffix : List Bool) :
    output false v ((RealSyntax.Term.int z : RealSyntax.Term n).code ++ suffix) =
      true :: RowWordCodec.polynomial (SparseInteger.sub (SparseInteger.atom (BitCodec.naturalCode v)) (SparseInteger.constant z)) := by
  have hd : ((RealSyntax.Term.int z : RealSyntax.Term n).code ++ suffix).drop 3 = BitCodec.integerCode z ++ suffix := rfl
  rw [output, hd, LeafRowEmitter.integer_output, SmallIntegerLookup.value_code z hz]
  simp [SparseInteger.sub, SparseInteger.add, SparseInteger.neg, SparseInteger.scale, SparseInteger.atom, SparseInteger.constant]

theorem variable_code {n : ℕ} (i : Fin n) (v : ℕ) (suffix : List Bool) :
    output true v ((RealSyntax.Term.var i).code ++ suffix) =
      true :: RowWordCodec.polynomial (SparseInteger.sub (SparseInteger.atom (BitCodec.naturalCode v))
        (SparseInteger.atom (BitCodec.naturalCode i.val))) := by
  have hd : ((RealSyntax.Term.var i).code ++ suffix).drop 3 = BitCodec.naturalCode i.val ++ suffix := rfl
  rw [output, hd, LeafRowEmitter.variable_output, NumericCursor.natural_copied_code]
  simp [SparseInteger.sub, SparseInteger.add, SparseInteger.neg, SparseInteger.scale, SparseInteger.atom]

end JointThermoComplexity.Complexity.LeafLocalEquation

#print axioms JointThermoComplexity.Complexity.LeafLocalEquation.hoareTime
#print axioms JointThermoComplexity.Complexity.LeafLocalEquation.integer_code
#print axioms JointThermoComplexity.Complexity.LeafLocalEquation.variable_code
