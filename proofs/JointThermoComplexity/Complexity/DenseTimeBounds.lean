module
public import proofs.JointThermoComplexity.Complexity.DenseNetworkEmitter

set_option autoImplicit false
@[expose] public section

/-! Positive polynomial majorants for the actual binary word emitter.
Only the retained structural dimensions are replaced by their raw length bounds. -/

namespace JointThermoComplexity.Complexity.DenseTimeBounds
open DenseTwoPassControl
variable {α : Type*} [Semiring α]

def q (L : α) : α := 16 * L + 3 + L * (16 * (L + 2609))
def externalBudget (n B : α) : α := 2 * (n * (98 * n + 96 * B + 114) + 3 * n + 12) + 10
def complexBudget (N B E : α) : α :=
  (N + 2) * (26 * (N + 2) + 24 * B + 100) + 100 * B + 100 * (N + 2) + 1000 + E
def rowBudget (n N B : α) : α := 3 * complexBudget N B (externalBudget n B) + 51 * B + 956
def prefixBudget (n N B : α) : α := 2 * rowBudget n N B + 1
def packetBudget (n N B : α) : α := 16 * (rowBudget n N B + 1)
def loopBudget (L n N B : α) : α := L * (123 * L + 175 + packetBudget n N B) + (L + 2)
def branchBudget (L n N B : α) : α := prefixBudget n N B + 1 + loopBudget L n N B
def extra (L : α) : α :=
  ((14 * q L + 50) + 1 + 4 * (12 * L + 10)) + 2 * branchBudget L L (16 * L) (q L) +
    ((3 * q L + 9) + 1 + 4 * (12 * L + 10) + 1 + (L + 3 + 1 + (L + 1) + 1 + 1)) +
      10000 * (17 * L + 1) + 5

theorem code0 : (BitCodec.naturalCode 0).length = 1 := by decide
theorem code1 : (BitCodec.naturalCode 1).length = 3 := by decide
theorem code2 : (BitCodec.naturalCode 2).length = 5 := by decide

theorem complex_le (right : Bool) (N B k E : ℕ) (hk : k = 1 ∨ k = 2) :
    DenseComplexCore.bound right N B k E ≤ complexBudget N B E := by
  rcases hk with rfl | rfl <;> cases right <;>
    simp only [DenseComplexCore.bound, DenseComplexCore.leftBound, DenseComplexCore.rightBound,
      DenseInternalBlocks.leftBound, DenseInternalBlocks.rightBeforeBound, DenseInternalBlocks.rightAfterBound,
      DenseInternalBlocks.zeroBound, ReusableIndicatorVector.polynomial_bound, IndicatorFixedPair.bound,
      IndicatorVectorUnit.bound, code0, code1, code2, complexBudget, Bool.false_eq_true, ↓reduceIte] <;>
    norm_num <;> ring_nf <;> omega

theorem complex_mono (N N' B E E' : ℕ) (hN : N ≤ N') (hE : E ≤ E') :
    complexBudget N B E ≤ complexBudget N' B E' := by
  have hm : (N + 2) * (26 * (N + 2) + 24 * B + 100) ≤ (N' + 2) * (26 * (N' + 2) + 24 * B + 100) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold complexBudget
  omega

theorem external_mono (n n' B : ℕ) (hn : n ≤ n') : externalBudget n B ≤ externalBudget n' B := by
  have hm : n * (98 * n + 96 * B + 114) ≤ n' * (98 * n' + 96 * B + 114) := Nat.mul_le_mul hn (by omega)
  unfold externalBudget
  omega

theorem fixed_external_le (boxed offset : Bool) (n B : ℕ) : DenseFixedPacket.externalBound boxed offset n ≤ externalBudget n B := by
  cases boxed <;> cases offset <;>
    simp only [DenseFixedPacket.externalBound, DenseFixedExternalPower.boxedBound, DenseFixedExternalPower.unboxedBound,
      DenseInternalBlocks.zeroBound, DenseFixedComplexOriginal.offsetPower, code0, code1, Bool.false_eq_true, ↓reduceIte] <;>
    unfold externalBudget <;> ring_nf <;> omega

theorem regular_external_le (boxed : Bool) (n B : ℕ) :
    (if boxed then DenseExternalPower.vectorBound n B else DenseExternalPower.unboxedBound n B) ≤ externalBudget n B := by
  cases boxed <;>
    simp only [DenseExternalPower.unboxedBound, DenseExternalPower.vectorBound, ReusablePowerVector.polynomial_bound,
      code0, externalBudget, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem regular_row_le (right : Bool) (n N B E : ℕ) (hE : E ≤ externalBudget n B) :
    DenseRowStep.timeBound right N B E ≤ rowBudget n N B := by
  have h1 := (complex_le right N B 1 E (Or.inl rfl)).trans (complex_mono N N B E (externalBudget n B) le_rfl hE)
  have h2 := (complex_le right N B 2 E (Or.inr rfl)).trans (complex_mono N N B E (externalBudget n B) le_rfl hE)
  unfold DenseRowStep.timeBound DenseRegularRecord.timeBound DenseProductBranch.timeBound rowBudget
  omega

theorem fixed_row_le (boxed right offset : Bool) (n N B : ℕ) : DenseFixedPacket.rowBound boxed right offset n N B ≤ rowBudget n N B := by
  let E := DenseFixedPacket.externalBound boxed offset n
  have hE := fixed_external_le boxed offset n B
  have h1 := (complex_le right N B 1 E (Or.inl rfl)).trans (complex_mono N N B E (externalBudget n B) le_rfl hE)
  have h2 := (complex_le right N B 2 E (Or.inr rfl)).trans (complex_mono N N B E (externalBudget n B) le_rfl hE)
  change DenseFixedRecord.timeBound right N B E + 40 * B + 80 ≤ rowBudget n N B
  unfold DenseFixedRecord.timeBound DenseProductBranch.timeBound rowBudget
  omega

theorem prefix_le (boxed right : Bool) (n N B : ℕ) : DenseFixedPacket.timeBound boxed right n N B ≤ prefixBudget n N B := by
  have h0 := fixed_row_le boxed right false n N B
  have h1 := fixed_row_le boxed right true n N B
  unfold DenseFixedPacket.timeBound prefixBudget
  omega

theorem packet_le (boxed right : Bool) (n N B : ℕ) : DensePacketChoice.timeBound boxed right n N B ≤ packetBudget n N B := by
  cases boxed with
  | false =>
    exact Nat.mul_le_mul_left 16 (Nat.add_le_add_right (regular_row_le right n N B _ (regular_external_le false n B)) 1)
  | true =>
    exact Nat.mul_le_mul_left 16 (Nat.add_le_add_right (regular_row_le right n N B _ (regular_external_le true n B)) 1)

theorem loop_le (boxed right : Bool) (L n N B : ℕ) : DenseSourceLoop.timeBound boxed right L n N B L ≤ loopBudget L n N B := by
  have hp := packet_le boxed right n N B
  have hs : DenseMarkedStep.bound boxed right L n N B + 2 ≤ 123 * L + 175 + packetBudget n N B := by
    unfold DenseMarkedStep.bound DenseLoadedPacket.timeBound DenseBankSelect.timeBound
    omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left L hs) (L + 2)

theorem branch_le (boxed right : Bool) (L n N B : ℕ) : DenseBranchPass.timeBound boxed right L n N B L ≤ branchBudget L n N B :=
  Nat.add_le_add (Nat.add_le_add_right (prefix_le boxed right n N B) 1) (loop_le boxed right L n N B)

theorem branch_mono (L n n' N N' B : ℕ) (hn : n ≤ n') (hN : N ≤ N') : branchBudget L n N B ≤ branchBudget L n' N' B := by
  have hc := complex_mono N N' B (externalBudget n B) (externalBudget n' B) hN (external_mono n n' B hn)
  have hr : rowBudget n N B ≤ rowBudget n' N' B := by unfold rowBudget; omega
  have hp : packetBudget n N B ≤ packetBudget n' N' B := by unfold packetBudget; omega
  have hm := Nat.mul_le_mul_left L (Nat.add_le_add_left hp (123 * L + 175))
  unfold branchBudget prefixBudget loopBudget
  omega

theorem internal_length : DenseNetworkSuffix.internalWord.length = 21 := by decide
theorem external_length : DenseNetworkSuffix.externalWord.length = 17 := by decide

theorem suffix_le (boxed : Bool) (n N : ℕ) : DenseNetworkSuffix.timeBound boxed n N ≤ 10000 * (n + N + 1) := by
  cases boxed <;>
    simp [DenseNetworkSuffix.timeBound, DenseNetworkSuffix.program, DenseNetworkSuffix.common,
      DenseNetworkSuffix.bound, DenseNetworkSuffix.Part.time, DenseNetworkSuffix.values,
      internal_length, external_length, DenseDimensionProgram.result, DenseDimensionProgram.external] <;> omega

def lengthBound (boxed : Bool) (L : ℕ) : ℕ := SparseDenseRescan.entryBound boxed L + extra L

theorem emitter_le (boxed : Bool) (input : List Bool) : DenseNetworkEmitter.timeBound boxed input ≤ lengthBound boxed input.length := by
  let L := input.length
  let n := arity input
  let N := total boxed input
  let B := DenseReplayControl.budget L
  have hn : n ≤ L := HeaderControl.count_le_length input
  have hN : N ≤ 16 * L := SparseDimensionEntry.rows_bound boxed input
  have hm := branch_mono L n L N (16 * L) B hn hN
  have hl := (branch_le boxed false L n N B).trans hm
  have hr := (branch_le boxed true L n N B).trans hm
  have hs : DenseNetworkSuffix.timeBound boxed n N ≤ 10000 * (17 * L + 1) := (suffix_le boxed n N).trans (by omega)
  have he : DenseNetworkEmitter.timeBound boxed input = SparseDenseRescan.entryBound boxed L + DenseLiveInitialize.timeBound L B +
      DenseBranchPass.timeBound boxed false L n N B L + DenseBranchPass.timeBound boxed true L n N B L +
        DenseTwoPassControl.restartBound L + DenseNetworkSuffix.timeBound boxed n N + 5 := by
    unfold DenseNetworkEmitter.timeBound DenseTwoPass.timeBound DenseBranchPass.entryBound DenseRescanEntry.timeBound
    simp only [L, n, N, B, arity, total]
    omega
  rw [he]
  unfold lengthBound extra DenseLiveInitialize.timeBound DenseTwoPassControl.restartBound
  change SparseDenseRescan.entryBound boxed L + ((14 * B + 50) + 1 + 4 * (12 * L + 10)) +
    DenseBranchPass.timeBound boxed false L n N B L + DenseBranchPass.timeBound boxed true L n N B L +
      ((3 * B + 9) + 1 + 4 * (12 * L + 10) + 1 + (L + 3 + 1 + (L + 1) + 1 + 1)) + DenseNetworkSuffix.timeBound boxed n N + 5 ≤
        SparseDenseRescan.entryBound boxed L + (((14 * B + 50) + 1 + 4 * (12 * L + 10)) + 2 * branchBudget L L (16 * L) B +
          ((3 * B + 9) + 1 + 4 * (12 * L + 10) + 1 + (L + 3 + 1 + (L + 1) + 1 + 1)) + 10000 * (17 * L + 1) + 5)
  omega

noncomputable def runtimePolynomial (boxed : Bool) : Polynomial ℕ := SparseDenseRescan.entryPolynomial boxed + extra Polynomial.X

theorem polynomial_eval (boxed : Bool) (L : ℕ) : (runtimePolynomial boxed).eval L = lengthBound boxed L := by
  simp [runtimePolynomial, lengthBound, extra, q, branchBudget, prefixBudget, loopBudget, packetBudget,
    rowBudget, complexBudget, externalBudget, SparseDenseRescan.entryPolynomial_eval]

end JointThermoComplexity.Complexity.DenseTimeBounds

#print axioms JointThermoComplexity.Complexity.DenseTimeBounds.emitter_le
#print axioms JointThermoComplexity.Complexity.DenseTimeBounds.polynomial_eval
