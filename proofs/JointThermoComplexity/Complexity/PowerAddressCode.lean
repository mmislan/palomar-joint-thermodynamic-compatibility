module
public import proofs.JointThermoComplexity.Complexity.PowerAddressState
public import proofs.JointThermoComplexity.Complexity.BinaryPowerCode

set_option autoImplicit false
@[expose] public section

/-! Raw address serialization agrees exactly with the existing finite-variable formula codec. -/

namespace JointThermoComplexity.Complexity.PowerAddressCode
open PowerAddressState

def variableCode (address : ℕ) : List Bool := [false, false, true] ++ BitCodec.naturalCode address

def multiply (target left right : ℕ) : List Bool :=
  [false, true, false] ++ variableCode target ++ ([false, true, true] ++ variableCode left ++ variableCode right)

theorem typed_multiply {arity : ℕ} (target left right : Fin arity) :
    BinaryPowerCode.multiply target left right = multiply target.val left.val right.val := rfl

def word (s : State) : Bool → List Bool
  | false => multiply s.nextAddress s.powerAddress s.powerAddress
  | true => multiply s.nextAddress s.accumulatorAddress s.powerAddress ++
      multiply (s.nextAddress + 1) s.powerAddress s.powerAddress

def stream (s : State) : List Bool → List Bool
  | [] => []
  | bit :: rest => word s bit ++ stream (s.advance bit) rest

end JointThermoComplexity.Complexity.PowerAddressCode

#print axioms JointThermoComplexity.Complexity.PowerAddressCode.typed_multiply
