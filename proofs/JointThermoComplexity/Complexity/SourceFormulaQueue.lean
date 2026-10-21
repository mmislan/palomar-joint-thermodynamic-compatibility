module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaToken

set_option autoImplicit false
@[expose] public section

/-! Formula forests need only one pending-formula count; two-term leaves are already parsed. -/

namespace JointThermoComplexity.Complexity.SourceFormulaScan
open RealSyntax
variable {n : ℕ}

def nodes : Formula n → ℕ
  | .truth | .falsity | .eq _ _ | .lt _ _ => 1
  | .conj p q | .disj p q => 1 + nodes p + nodes q

def forestCode (ps : List (Formula n)) : List Bool := ps.flatMap Formula.code
def forestNodes (ps : List (Formula n)) : ℕ := (ps.map nodes).sum

@[simp] theorem forestCode_nil : forestCode ([] : List (Formula n)) = [] := rfl
@[simp] theorem forestCode_cons (p : Formula n) (ps : List (Formula n)) : forestCode (p :: ps) = p.code ++ forestCode ps := rfl
@[simp] theorem forestNodes_nil : forestNodes ([] : List (Formula n)) = 0 := rfl
@[simp] theorem forestNodes_cons (p : Formula n) (ps : List (Formula n)) : forestNodes (p :: ps) = nodes p + forestNodes ps := rfl

def rootHead : Formula n → Head n
  | .truth => .truth
  | .falsity => .falsity
  | .eq a b => .eq a b
  | .lt a b => .lt a b
  | .conj _ _ => .conj
  | .disj _ _ => .disj

def childFormulas : Formula n → List (Formula n)
  | .conj p q | .disj p q => [p, q]
  | _ => []

theorem root_decomposition (p : Formula n) (ps : List (Formula n)) :
    forestCode (p :: ps) = (rootHead p).code ++ forestCode (childFormulas p ++ ps) := by
  cases p <;> simp [rootHead, childFormulas, forestCode, Formula.code, Head.code, List.append_assoc]

theorem child_count (p : Formula n) (ps : List (Formula n)) :
    (childFormulas p ++ ps).length = ps.length + (rootHead p).children := by
  cases p <;> simp only [childFormulas, rootHead, Head.children, Head.kind, Kind.children, List.length_append,
    List.length_cons, List.length_nil] <;> omega

theorem child_nodes (p : Formula n) (ps : List (Formula n)) :
    forestNodes (childFormulas p ++ ps) + 1 = forestNodes (p :: ps) := by
  cases p <;> simp only [childFormulas, List.nil_append, List.cons_append, forestNodes_cons, nodes] <;> omega

theorem nodes_le_code_length (p : Formula n) : nodes p ≤ p.code.length := by
  induction p <;> simp_all only [nodes, Formula.code, List.length_append, List.length_cons, List.length_nil] <;> omega

theorem forestNodes_le_code_length (ps : List (Formula n)) : forestNodes ps ≤ (forestCode ps).length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [forestNodes_cons, forestCode_cons, List.length_append]
    exact Nat.add_le_add (nodes_le_code_length p) ih

def scan (arity L : ℕ) : ℕ → ℕ → List Bool → Option (List Bool)
  | _, 0, input => some input
  | 0, _ + 1, _ => none
  | fuel + 1, pending + 1, input =>
      if SourceFormulaToken.accepted arity L input then
        scan arity L fuel (pending + (classify (SourceTermToken.tagBits input)).children) (SourceFormulaToken.rest arity L input)
      else none

theorem scan_empty (L fuel : ℕ) (input : List Bool) : scan n L fuel 0 input = some input := by cases fuel <;> rfl

theorem scan_head (L fuel pending : ℕ) (head : Head n) (suffix : List Bool) (hlen : (head.code ++ suffix).length ≤ L) :
    scan n L (fuel + 1) (pending + 1) (head.code ++ suffix) = scan n L fuel (pending + head.children) suffix := by
  obtain ⟨_ht, hr, hv⟩ := SourceFormulaToken.code_result head suffix hlen
  simp only [scan, hv, ↓reduceIte, hr, classify_head, Head.children]

end JointThermoComplexity.Complexity.SourceFormulaScan

#print axioms JointThermoComplexity.Complexity.SourceFormulaScan.root_decomposition
#print axioms JointThermoComplexity.Complexity.SourceFormulaScan.scan_head
