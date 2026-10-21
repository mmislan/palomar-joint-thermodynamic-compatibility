module
public import proofs.JointThermoComplexity.Complexity.SourceTermHead

set_option autoImplicit false
@[expose] public section

/-! A source-term scanner driven by a pending-node count. It never builds a
syntax tree. At most one head token is consumed per fuel step. -/

namespace JointThermoComplexity.Complexity.SourceTermScan
open RealSyntax
variable {n : ℕ}

def forestCode (ts : List (Term n)) : List Bool := ts.flatMap Term.code
def forestNodes (ts : List (Term n)) : ℕ := (ts.map Term.size).sum

@[simp] theorem forestCode_nil : forestCode ([] : List (Term n)) = [] := rfl
@[simp] theorem forestCode_cons (t : Term n) (ts : List (Term n)) : forestCode (t :: ts) = t.code ++ forestCode ts := rfl
@[simp] theorem forestNodes_nil : forestNodes ([] : List (Term n)) = 0 := rfl
@[simp] theorem forestNodes_cons (t : Term n) (ts : List (Term n)) : forestNodes (t :: ts) = t.size + forestNodes ts := rfl

def scan (n : ℕ) : ℕ → ℕ → List Bool → Option (List Bool)
  | _, 0, input => some input
  | 0, _ + 1, _ => none
  | fuel + 1, pending + 1, input => do
    let (h, rest) ← parseHead n input
    scan n fuel (pending + h.children) rest

theorem scan_empty (fuel : ℕ) (input : List Bool) : scan n fuel 0 input = some input := by cases fuel <;> rfl

theorem scan_step {fuel pending : ℕ} {input suffix : List Bool} {h : Head n}
    (hp : parseHead n input = some (h, suffix)) :
    scan n (fuel + 1) (pending + 1) input = scan n fuel (pending + h.children) suffix := by
  simp [scan, hp]

theorem forestNodes_le_code_length (ts : List (Term n)) : forestNodes ts ≤ (forestCode ts).length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [forestNodes_cons, forestCode_cons, List.length_append]
    exact Nat.add_le_add t.size_le_code_length ih

theorem pending_next_bound (pending : ℕ) (h : Head n) : pending + h.children ≤ (pending + 1) + 1 := by
  have hc := head_child_bound h
  omega

end JointThermoComplexity.Complexity.SourceTermScan

#print axioms JointThermoComplexity.Complexity.SourceTermScan.scan_step
#print axioms JointThermoComplexity.Complexity.SourceTermScan.forestNodes_le_code_length
