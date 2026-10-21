module
public import proofs.JointThermoComplexity.Complexity.LocalEquationTemplateRun

set_option autoImplicit false
@[expose] public section

/-! Incremental word rows concatenate exactly and acquire one final outer terminator. -/

namespace JointThermoComplexity.Complexity.RowEntriesCodec
open SparseInteger

def entries : List (Poly (List Bool)) → List Bool
  | [] => []
  | p :: ps => true :: (RowWordCodec.polynomial p ++ entries ps)

theorem entries_append (ps qs : List (Poly (List Bool))) : entries (ps ++ qs) = entries ps ++ entries qs := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [entries, List.cons_append, ih, List.append_assoc]

theorem complete (ps : List (Poly (List Bool))) : entries ps ++ [false] = RowWordCodec.rows ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change (true :: (RowWordCodec.polynomial p ++ entries ps)) ++ [false] =
      true :: (RowWordCodec.polynomial p ++ RowWordCodec.rows ps)
    simp only [List.cons_append, List.append_assoc, ih]

theorem template_entries (kind : LocalEquationTemplates.Kind) (values : Fin 6 → ℕ) :
    LocalEquationTemplateRun.output kind values = entries (LocalEquationTemplates.wordRows kind values) := by
  exact List.append_cancel_right ((LocalEquationTemplateRun.output_complete kind values).trans
    (complete (LocalEquationTemplates.wordRows kind values)).symm)

theorem leaf_entries (p : Poly (List Bool)) : true :: RowWordCodec.polynomial p = entries [p] := by
  simp only [entries, List.append_nil]

end JointThermoComplexity.Complexity.RowEntriesCodec

#print axioms JointThermoComplexity.Complexity.RowEntriesCodec.complete
#print axioms JointThermoComplexity.Complexity.RowEntriesCodec.template_entries
