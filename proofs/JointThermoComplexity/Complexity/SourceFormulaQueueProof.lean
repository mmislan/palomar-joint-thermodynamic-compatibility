module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaQueue

set_option autoImplicit false
@[expose] public section

/-! Exact independent formula-forest semantics for the pending-formula queue. -/

namespace JointThermoComplexity.Complexity.SourceFormulaScan
open RealSyntax
variable {n : ℕ}

theorem scan_sound (L fuel pending : ℕ) (input suffix : List Bool) (hlen : input.length ≤ L)
    (hscan : scan n L fuel pending input = some suffix) :
    ∃ ps : List (Formula n), ps.length = pending ∧ forestNodes ps ≤ fuel ∧ input = forestCode ps ++ suffix := by
  induction fuel generalizing pending input with
  | zero =>
    cases pending with
    | zero =>
      have he : input = suffix := Option.some.inj hscan
      exact ⟨[], rfl, le_rfl, by simpa only [forestCode_nil, List.nil_append] using he⟩
    | succ pending => simp [scan] at hscan
  | succ fuel ih =>
    cases pending with
    | zero =>
      have he : input = suffix := Option.some.inj hscan
      exact ⟨[], rfl, Nat.zero_le _, by simpa only [forestCode_nil, List.nil_append] using he⟩
    | succ pending =>
      by_cases ha : SourceFormulaToken.accepted n L input = true
      · have hnext : scan n L fuel (pending + (classify (SourceTermToken.tagBits input)).children)
            (SourceFormulaToken.rest n L input) = some suffix := by
          simpa only [scan, ha, ↓reduceIte] using hscan
        obtain ⟨head, hcode, _ht, hchildren⟩ := SourceFormulaToken.sound n L input hlen ha
        rw [hchildren] at hnext
        have hrestlen : (SourceFormulaToken.rest n L input).length ≤ L := by
          have h := SourceFormulaToken.success_consumes n L input hlen ha
          omega
        obtain ⟨ps, hcount, hnodes, hrest⟩ := ih (pending + head.children) _ hrestlen hnext
        have leaf (p : Formula n) (hn : nodes p = 1) (hc : p.code = head.code) (hp : ps.length = pending) :
            ∃ qs : List (Formula n), qs.length = pending + 1 ∧ forestNodes qs ≤ fuel + 1 ∧ input = forestCode qs ++ suffix := by
          refine ⟨p :: ps, by simp only [List.length_cons, hp], ?_, ?_⟩
          · rw [forestNodes_cons, hn]
            omega
          · rw [hcode, hrest, ← hc, forestCode_cons]
            simp only [List.append_assoc]
        cases head with
        | truth => exact leaf .truth rfl rfl (by simpa only [Head.children, Head.kind, Kind.children, Nat.add_zero] using hcount)
        | falsity => exact leaf .falsity rfl rfl (by simpa only [Head.children, Head.kind, Kind.children, Nat.add_zero] using hcount)
        | eq a b => exact leaf (.eq a b) rfl rfl (by simpa only [Head.children, Head.kind, Kind.children, Nat.add_zero] using hcount)
        | lt a b => exact leaf (.lt a b) rfl rfl (by simpa only [Head.children, Head.kind, Kind.children, Nat.add_zero] using hcount)
        | conj =>
          simp only [Head.children, Head.kind, Kind.children] at hcount
          cases ps with
          | nil => simp at hcount
          | cons p ps =>
            cases ps with
            | nil => simp at hcount
            | cons q ps =>
              refine ⟨Formula.conj p q :: ps, ?_, ?_, ?_⟩
              · simp only [List.length_cons] at hcount ⊢
                omega
              · simp only [forestNodes_cons, nodes] at hnodes ⊢
                omega
              · rw [hcode, hrest]
                simp only [Head.code, forestCode_cons, Formula.code, List.append_assoc]
        | disj =>
          simp only [Head.children, Head.kind, Kind.children] at hcount
          cases ps with
          | nil => simp at hcount
          | cons p ps =>
            cases ps with
            | nil => simp at hcount
            | cons q ps =>
              refine ⟨Formula.disj p q :: ps, ?_, ?_, ?_⟩
              · simp only [List.length_cons] at hcount ⊢
                omega
              · simp only [forestNodes_cons, nodes] at hnodes ⊢
                omega
              · rw [hcode, hrest]
                simp only [Head.code, forestCode_cons, Formula.code, List.append_assoc]
      · simp [scan, ha] at hscan

theorem scan_complete (L fuel : ℕ) (ps : List (Formula n)) (suffix : List Bool)
    (hn : forestNodes ps ≤ fuel) (hlen : (forestCode ps ++ suffix).length ≤ L) :
    scan n L fuel ps.length (forestCode ps ++ suffix) = some suffix := by
  induction fuel generalizing ps suffix with
  | zero =>
    cases ps with
    | nil => rfl
    | cons p ps => have h := child_nodes p ps; omega
  | succ fuel ih =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      have hnodes := child_nodes p ps
      have hn' : forestNodes (childFormulas p ++ ps) ≤ fuel := by omega
      have hc : forestCode (p :: ps) ++ suffix =
          (rootHead p).code ++ (forestCode (childFormulas p ++ ps) ++ suffix) := by
        rw [root_decomposition, List.append_assoc]
      have hlen' : (forestCode (childFormulas p ++ ps) ++ suffix).length ≤ L := by
        rw [hc, List.length_append] at hlen
        omega
      have hrec := ih (childFormulas p ++ ps) suffix hn' hlen'
      rw [hc, List.length_cons, scan_head L fuel ps.length (rootHead p) _ (by simpa only [← hc] using hlen), ← child_count]
      exact hrec

theorem scan_some_iff (L fuel pending : ℕ) (input suffix : List Bool) (hlen : input.length ≤ L) :
    scan n L fuel pending input = some suffix ↔
      ∃ ps : List (Formula n), ps.length = pending ∧ forestNodes ps ≤ fuel ∧ input = forestCode ps ++ suffix := by
  constructor
  · exact scan_sound L fuel pending input suffix hlen
  · rintro ⟨ps, hc, hn, hi⟩
    rw [hi, ← hc]
    exact scan_complete L fuel ps suffix hn (by simpa only [hi] using hlen)

theorem scan_one_iff (L : ℕ) (input suffix : List Bool) (hlen : input.length ≤ L) :
    scan n L L 1 input = some suffix ↔ ∃ p : Formula n, input = p.code ++ suffix := by
  rw [scan_some_iff L L 1 input suffix hlen]
  constructor
  · rintro ⟨ps, hc, _hn, hi⟩
    cases ps with
    | nil => simp at hc
    | cons p ps =>
      have he : ps = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hc; omega)
      subst ps
      exact ⟨p, by simpa only [forestCode_cons, forestCode_nil, List.append_nil] using hi⟩
  · rintro ⟨p, hi⟩
    refine ⟨[p], rfl, ?_, ?_⟩
    · have hn := nodes_le_code_length p
      have he := congrArg List.length hi
      rw [List.length_append] at he
      simpa only [forestNodes_cons, forestNodes_nil, Nat.add_zero] using (show nodes p ≤ L by omega)
    · simpa only [forestCode_cons, forestCode_nil, List.append_nil] using hi

end JointThermoComplexity.Complexity.SourceFormulaScan

#print axioms JointThermoComplexity.Complexity.SourceFormulaScan.scan_sound
#print axioms JointThermoComplexity.Complexity.SourceFormulaScan.scan_complete
#print axioms JointThermoComplexity.Complexity.SourceFormulaScan.scan_one_iff
