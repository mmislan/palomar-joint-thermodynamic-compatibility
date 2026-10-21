module
public import proofs.JointThermoComplexity.Complexity.RoutedNetworkParser
public import proofs.JointThermoComplexity.Complexity.DecodedDimensions
public import proofs.JointThermoComplexity.Complexity.CountOffset

set_option autoImplicit false
@[expose] public section

/-! Parser information outside its disposable copied-input tape. -/

namespace JointThermoComplexity.Complexity.ParserRegisters
open _root_.Complexity
open _root_.Complexity.TM

def Kept (n : ℕ) (input : List Bool) (work : Fin (n + 5) → Tape) : Prop :=
  (work (NetworkParser.master n)).head = 1 ∧
  (work (NetworkParser.master n)).read = Γ.ofBool (NetworkInputControl.accepted input) ∧
  NetworkScanner.Env (NetworkParser.count n 0) (NetworkParser.count n 1) (NetworkParser.count n 2)
    (DimensionHeaders.species input) (DimensionHeaders.reactions input) (DimensionHeaders.cores input) work

theorem kept_of_retained (n : ℕ) (input : List Bool) (work : Fin (n + 6) → Tape)
    (h : RoutedNetworkParser.Retained n input work) : Kept n input (CountAppend.oldWork work) :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem decoded_counts (n : ℕ) (input : List Bool) (work : Fin (n + 5) → Tape)
    (h : Kept n input work) {Q : NetworkCodec.Input} (hQ : NetworkCodec.decode input = some Q) :
    IsReg Q.speciesCount (work (NetworkParser.count n 0)) ∧
    IsReg Q.reactionCount (work (NetworkParser.count n 1)) ∧ IsReg Q.coreCount (work (NetworkParser.count n 2)) := by
  obtain ⟨hs, hr, hc⟩ := DecodedDimensions.decode_counts hQ
  simpa only [NetworkScanner.Env, hs, hr, hc] using h.2.2

theorem accepted_master (n : ℕ) (input : List Bool) (work : Fin (n + 5) → Tape)
    (h : Kept n input work) (ha : NetworkInputControl.accepted input = true) :
    (work (NetworkParser.master n)).head = 1 ∧ (work (NetworkParser.master n)).read = Γ.one := by
  exact ⟨h.1, by simpa only [ha, Γ.ofBool] using h.2.1⟩

end JointThermoComplexity.Complexity.ParserRegisters

#print axioms JointThermoComplexity.Complexity.ParserRegisters.decoded_counts
