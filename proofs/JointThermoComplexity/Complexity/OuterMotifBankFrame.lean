module
public import proofs.JointThermoComplexity.Complexity.OuterActivityBoxBankFrame
public import proofs.JointThermoComplexity.Complexity.MotifBufferMeta
public import proofs.JointThermoComplexity.Complexity.MotifDirectionFrame

set_option autoImplicit false
@[expose] public section

/-! Supplied-mask buffers and direction work preserve the actual blank production bank. -/

namespace JointThermoComplexity.Complexity.OuterMotifBankFrame
open _root_.Complexity
open _root_.Complexity.TM

theorem buffer_frame (m : ℕ) (k : Fin 3) (work work' : Fin (m + 22) → Tape)
    (hw : ∀ j, j ≠ MotifBufferPorts.buffer (m + 7) k → work' j = work j) :
    OuterFuelBank.State m work → OuterFuelBank.State m work' :=
  OuterActivityBoxBankFrame.box_frame m work work' (MotifBufferMeta.unchanged (m + 7) k work work' hw)

theorem direction_frame (m : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : MotifDirectionFrame.Unchanged (m + 7) work work') :
    OuterFuelBank.State m work → OuterFuelBank.State m work' :=
  OuterActivityBoxBankFrame.box_frame m work work' (fun j _ hacc hpower _ hsource => hw j hacc hpower hsource)

end JointThermoComplexity.Complexity.OuterMotifBankFrame

#print axioms JointThermoComplexity.Complexity.OuterMotifBankFrame.buffer_frame
#print axioms JointThermoComplexity.Complexity.OuterMotifBankFrame.direction_frame
