module
public import proofs.JointThermoComplexity.Complexity.NetworkFormula
public import proofs.JointThermoComplexity.Complexity.RealCircuit
public import Mathlib.Data.Nat.Size

set_option autoImplicit false
@[expose] public section

/-!
# Serialized formula bounds

These bounds refer to the actual self-delimiting binary codes. Each gate reads
indexed variables, so its translation never expands previous circuit terms.
The deliberately loose variable-index bound is polynomial in the number of
declared variables, whose unary binder header is already part of a sentence.
-/

namespace JointThermoComplexity.Complexity.CircuitSize
open RealSyntax RealCircuit BitCodec NetworkFormula

variable {n k m d : ℕ}

theorem bits_length_le (a : ℕ) : a.bits.length ≤ a := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

theorem variable_code_length_le (i : Fin m) : (Term.var i).code.length ≤ 2 * m + 4 := by
  have h := bits_length_le i.val
  simp only [Term.code, List.length_append, List.length_cons, List.length_nil, naturalCode_length]
  omega

def integerWeight (s : Step n k) : ℕ :=
  match s with
  | .constant z => (integerCode z).length
  | _ => 0

theorem step_code_length_le (s : Step n k) (inputs : Fin n → Fin m)
    (previous : Fin k → Fin m) :
    (s.term inputs previous).code.length ≤ 4 * m + 12 + integerWeight s := by
  cases s with
  | constant z =>
    simp only [Step.term, Term.code, List.length_append, List.length_cons,
      List.length_nil, integerWeight]
    omega
  | input i =>
    have h := variable_code_length_le (inputs i)
    simpa only [Step.term, integerWeight, Nat.add_zero] using
      h.trans (by omega : 2 * m + 4 ≤ 4 * m + 12)
  | add i j =>
    have hi := variable_code_length_le (previous i)
    have hj := variable_code_length_le (previous j)
    simp only [Step.term, Term.code, List.length_append, List.length_cons,
      List.length_nil, integerWeight] at hi hj ⊢
    omega
  | mul i j =>
    have hi := variable_code_length_le (previous i)
    have hj := variable_code_length_le (previous j)
    simp only [Step.term, Term.code, List.length_append, List.length_cons,
      List.length_nil, integerWeight] at hi hj ⊢
    omega
  | neg i =>
    have hi := variable_code_length_le (previous i)
    simp only [Step.term, Term.code, List.length_append, List.length_cons,
      List.length_nil, integerWeight] at hi ⊢
    omega

def weight : {k : ℕ} → Circuit n k → ℕ
  | _, .nil => 0
  | _, .snoc c s => weight c + integerWeight s

theorem formula_code_length_le (c : Circuit n k) (inputs : Fin n → Fin m)
    (outputs : Fin k → Fin m) :
    (c.formula inputs outputs).code.length ≤ 3 + k * (6 * m + 22) + weight c := by
  induction c with
  | nil => simp [Circuit.formula, Formula.code, weight]
  | @snoc k c s ih =>
    have hp := ih (fun i => outputs i.castSucc)
    have hv := variable_code_length_le (outputs (Fin.last k))
    have hs := step_code_length_le s inputs (fun i => outputs i.castSucc)
    simp only [Circuit.formula, Formula.code, List.length_append, List.length_cons,
      List.length_nil, weight, Nat.add_mul, Nat.one_mul]
    omega

theorem conjoin_code_length_le (ps : List (Formula m)) (B : ℕ)
    (h : ∀ p ∈ ps, p.code.length ≤ B) :
    (conjoin ps).code.length ≤ 3 + ps.length * (B + 3) := by
  induction ps with
  | nil => simp [conjoin, Formula.code]
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht := ih (by intro q hq; exact h q (by simp [hq]))
    simp only [conjoin, Formula.code, List.length_append, List.length_cons,
      List.length_nil, Nat.add_mul, Nat.one_mul]
    omega

theorem allFin_code_length_le (f : Fin d → Formula m) (B : ℕ)
    (h : ∀ i, (f i).code.length ≤ B) :
    (allFin f).code.length ≤ 3 + d * (B + 3) := by
  apply (conjoin_code_length_le (List.ofFn f) B ?_).trans_eq
  · simp only [List.length_ofFn]
  · intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact h i

theorem addTerms_code_length_le (ts : List (Term m)) (B : ℕ)
    (h : ∀ t ∈ ts, t.code.length ≤ B) :
    (addTerms ts).code.length ≤ 5 + ts.length * (B + 3) := by
  induction ts with
  | nil => simp [addTerms, Term.code, integerCode, naturalCode, encodeBits]
  | cons t ts ih =>
    have ht := h t (by simp)
    have hr := ih (by intro q hq; exact h q (by simp [hq]))
    simp only [addTerms, Term.code, List.length_append, List.length_cons,
      List.length_nil, Nat.add_mul, Nat.one_mul]
    omega

theorem sumFin_code_length_le (f : Fin d → Term m) (B : ℕ)
    (h : ∀ i, (f i).code.length ≤ B) :
    (sumFin f).code.length ≤ 5 + d * (B + 3) := by
  apply (addTerms_code_length_le (List.ofFn f) B ?_).trans_eq
  · simp only [List.length_ofFn]
  · intro t ht
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact h i

end JointThermoComplexity.Complexity.CircuitSize

#print axioms JointThermoComplexity.Complexity.CircuitSize.formula_code_length_le
#print axioms JointThermoComplexity.Complexity.CircuitSize.allFin_code_length_le
#print axioms JointThermoComplexity.Complexity.CircuitSize.sumFin_code_length_le
