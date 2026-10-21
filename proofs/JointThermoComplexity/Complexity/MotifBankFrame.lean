module
public import proofs.JointThermoComplexity.Complexity.ActivityBoxBankFrame
public import proofs.JointThermoComplexity.Complexity.MotifBufferMeta
public import proofs.JointThermoComplexity.Complexity.MotifDirectionFrame

set_option autoImplicit false
@[expose] public section

/-! Supplied-mask buffers and direction work preserve the actual blank production bank. -/

namespace JointThermoComplexity.Complexity.MotifBankFrame
open _root_.Complexity
open _root_.Complexity.TM

theorem buffer_frame (m : ℕ) (k : Fin 3) (work work' : Fin (m + 20) → Tape)
    (hw : ∀ j, j ≠ MotifBufferPorts.buffer (m + 5) k → work' j = work j) :
    ProductionBank.State m work → ProductionBank.State m work' :=
  ActivityBoxBankFrame.box_frame m work work' (MotifBufferMeta.unchanged (m + 5) k work work' hw)

theorem direction_frame (m : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : MotifDirectionFrame.Unchanged (m + 5) work work') :
    ProductionBank.State m work → ProductionBank.State m work' :=
  ActivityBoxBankFrame.box_frame m work work' (fun j _ hacc hpower _ hsource => hw j hacc hpower hsource)

end JointThermoComplexity.Complexity.MotifBankFrame

#print axioms JointThermoComplexity.Complexity.MotifBankFrame.buffer_frame
#print axioms JointThermoComplexity.Complexity.MotifBankFrame.direction_frame
