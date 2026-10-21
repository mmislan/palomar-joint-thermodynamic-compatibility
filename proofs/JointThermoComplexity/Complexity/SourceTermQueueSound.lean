module
public import proofs.JointThermoComplexity.Complexity.SourceTermQueue

set_option autoImplicit false
@[expose] public section

/-! A successful pending-node scan reconstructs exactly the requested forest
of well-typed terms. No AST or source-validity certificate is an input. -/

namespace JointThermoComplexity.Complexity.SourceTermScan
open RealSyntax
variable {n : ℕ}

theorem scan_sound (fuel pending : ℕ) (input suffix : List Bool)
    (hp : scan n fuel pending input = some suffix) :
    ∃ ts : List (Term n), ts.length = pending ∧ forestNodes ts ≤ fuel ∧ input = forestCode ts ++ suffix := by
  induction fuel generalizing pending input suffix with
  | zero =>
    cases pending with
    | zero =>
      have he : input = suffix := Option.some.inj hp
      exact ⟨[], rfl, Nat.le_refl 0, he⟩
    | succ pending => simp [scan] at hp
  | succ fuel ih =>
    cases pending with
    | zero =>
      have he : input = suffix := Option.some.inj hp
      exact ⟨[], rfl, Nat.zero_le _, he⟩
    | succ pending =>
      cases hh : parseHead n input with
      | none => simp [scan, hh] at hp
      | some pair =>
        obtain ⟨head, rest⟩ := pair
        have hscan : scan n fuel (pending + head.children) rest = some suffix := by simpa only [scan_step hh] using hp
        obtain ⟨ts, hcount, hnodes, hcode⟩ := ih _ _ _ hscan
        have hin := parseHead_sound hh
        cases head with
        | int z =>
          simp only [Head.children, Nat.add_zero] at hcount
          refine ⟨.int z :: ts, ?_, ?_, ?_⟩
          · simp only [List.length_cons]; omega
          · simp only [forestNodes_cons, Term.size]; omega
          · rw [hin, hcode]
            simp only [Head.code, forestCode_cons, Term.code, List.append_assoc]
        | var i =>
          simp only [Head.children, Nat.add_zero] at hcount
          refine ⟨.var i :: ts, ?_, ?_, ?_⟩
          · simp only [List.length_cons]; omega
          · simp only [forestNodes_cons, Term.size]; omega
          · rw [hin, hcode]
            simp only [Head.code, forestCode_cons, Term.code, List.append_assoc]
        | add =>
          simp only [Head.children] at hcount
          cases ts with
          | nil => simp only [List.length_nil] at hcount; omega
          | cons left ts =>
            cases ts with
            | nil => simp only [List.length_cons, List.length_nil] at hcount; omega
            | cons right ts =>
              refine ⟨.add left right :: ts, ?_, ?_, ?_⟩
              · simp only [List.length_cons] at hcount ⊢; omega
              · simp only [forestNodes_cons, Term.size] at hnodes ⊢; omega
              · rw [hin, hcode]
                simp only [Head.code, forestCode_cons, Term.code, List.append_assoc]
        | mul =>
          simp only [Head.children] at hcount
          cases ts with
          | nil => simp only [List.length_nil] at hcount; omega
          | cons left ts =>
            cases ts with
            | nil => simp only [List.length_cons, List.length_nil] at hcount; omega
            | cons right ts =>
              refine ⟨.mul left right :: ts, ?_, ?_, ?_⟩
              · simp only [List.length_cons] at hcount ⊢; omega
              · simp only [forestNodes_cons, Term.size] at hnodes ⊢; omega
              · rw [hin, hcode]
                simp only [Head.code, forestCode_cons, Term.code, List.append_assoc]
        | neg =>
          simp only [Head.children] at hcount
          cases ts with
          | nil => simp only [List.length_nil] at hcount; omega
          | cons child ts =>
            refine ⟨.neg child :: ts, ?_, ?_, ?_⟩
            · simp only [List.length_cons] at hcount ⊢; omega
            · simp only [forestNodes_cons, Term.size] at hnodes ⊢; omega
            · rw [hin, hcode]
              simp only [Head.code, forestCode_cons, Term.code, List.append_assoc]

end JointThermoComplexity.Complexity.SourceTermScan

#print axioms JointThermoComplexity.Complexity.SourceTermScan.scan_sound
