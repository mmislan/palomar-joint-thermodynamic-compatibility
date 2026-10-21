module
public import proofs.JointThermoComplexity.Complexity.FormulaStart
public import proofs.JointThermoComplexity.Complexity.NetworkSeed

set_option autoImplicit false
@[expose] public section

/-! Fresh formula preparation supplies blank working ports and the retained species and reaction counts. -/

namespace JointThermoComplexity.Complexity.NetworkFreshRegisters
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady ReactionPorts

theorem blank (m : ℕ) (work : Fin (m + 15) → Tape) (h : FreshArity.Spare (m + 7) work)
    (r : Fin (m + 15)) (hlo : 2 ≤ r.val) (hhi : r.val < 9) : work r = DimensionEntry.blankRegister := by
  let i : Fin (m + 9) := ⟨r.val, by omega⟩
  have he : (NetworkParserFree.port (m + 9) i).castSucc = r := by
    apply Fin.ext
    rfl
  rw [← he]
  exact h i hlo

theorem zeros (m L : ℕ) (work : Fin (m + 15) → Tape) (h : FreshArity.Spare (m + 7) work) :
    IsReg 0 (work (next (m + 2))) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
    Temps (m + 1) L work ∧ IsReg 0 (work (previous (m + 1))) ∧
    IsReg 0 (work (species (m + 1))) ∧ IsReg 0 (work (saved m)) := by
  have hzero : ∀ r : Fin (m + 15), 2 ≤ r.val → r.val < 9 → IsReg 0 (work r) := by
    intro r hlo hhi
    rw [blank m work h r hlo hhi]
    exact DimensionEntry.blank_register
  have hz := hzero (scratch (m + 2)) (by change (2 : ℕ) ≤ 5; omega) (by change (5 : ℕ) < 9; omega)
  have hbinary : BinaryIncrementRun.Register 0 (work (scratch (m + 2))) := by
    refine ⟨?_, hz.2.1⟩
    simpa only [Nat.zero_bits, List.replicate_zero] using CountTape.string_of_register hz
  exact ⟨hzero _ (by change (2 : ℕ) ≤ 2; omega) (by change (2 : ℕ) < 9; omega), hbinary,
    ⟨0, 0, by omega, by omega, hzero _ (by change (2 : ℕ) ≤ 3; omega) (by change (3 : ℕ) < 9; omega),
      hzero _ (by change (2 : ℕ) ≤ 4; omega) (by change (4 : ℕ) < 9; omega)⟩,
    hzero _ (by change (2 : ℕ) ≤ 6; omega) (by change (6 : ℕ) < 9; omega),
    hzero _ (by change (2 : ℕ) ≤ 7; omega) (by change (7 : ℕ) < 9; omega),
    hzero _ (by change (2 : ℕ) ≤ 8; omega) (by change (8 : ℕ) < 9; omega)⟩

end JointThermoComplexity.Complexity.NetworkFreshRegisters

#print axioms JointThermoComplexity.Complexity.NetworkFreshRegisters.zeros
