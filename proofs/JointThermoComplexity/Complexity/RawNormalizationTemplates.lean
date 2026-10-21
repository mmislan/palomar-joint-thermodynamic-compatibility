module
public import proofs.JointThermoComplexity.Complexity.SparseSubstitution
public import proofs.JointThermoComplexity.Complexity.NumberedTermEquations
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.OfFn

set_option autoImplicit false
@[expose] public section

/-! Exact occurrence-indexed raw normalization templates. Repeated variables,
zero coefficients and the full stored term order are retained. -/

namespace JointThermoComplexity.Complexity.RawNormalizationTemplates
open SparseInteger SparseSubstitution NumberedTermEquations
variable {V W U : Type}

theorem scale_scale (a b : ℤ) (p : Poly V) : scale a (scale b p) = scale (a * b) p := by
  simp [scale, List.map_map, Function.comp_def, mul_assoc]

theorem expand_map (f : W → Poly U) (g : V → W) (vs : List V) :
    expand f (vs.map g) = expand (fun v => f (g v)) vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.map_cons, expand, ih]

theorem relabel_expand (f : V → Poly W) (g : W → U) (vs : List V) :
    relabel g (expand f vs) = expand (fun v => relabel g (f v)) vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [expand_cons, relabel_product, ih]; rfl

theorem cube_expand_map (f : V → W) (vs : List V) :
    relabel f (expand cubeVariable vs) = expand cubeVariable (vs.map f) := by
  rw [relabel_expand, expand_map]
  rfl

theorem orthant_expand_map (f : V → W) (vs : List V) :
    relabel (Sum.map f f) (expand orthantVariable vs) = expand orthantVariable (vs.map f) := by
  rw [relabel_expand, expand_map]
  rfl

def lookup (vs : List V) (i : Fin vs.length) : V := vs[i.val]

theorem lookup_finRange (vs : List V) : (List.finRange vs.length).map (lookup vs) = vs := by
  rw [← List.ofFn_eq_map]
  exact List.ofFn_getElem

def cubeTemplate (d m : ℕ) : Poly (Fin m) := cubeTerm d (1, List.finRange m)
def orthantTemplate (m : ℕ) : Poly (Fin m ⊕ Fin m) := expand orthantVariable (List.finRange m)

theorem cubeTerm_from_template (d : ℕ) (c : ℤ) (vs : List V) :
    cubeTerm d (c, vs) = scale c (relabel (lookup vs) (cubeTemplate d vs.length)) := by
  simp only [cubeTemplate, cubeTerm, List.length_finRange, one_mul, relabel_scale,
    cube_expand_map, lookup_finRange, scale_scale]

theorem orthantTerm_from_template (c : ℤ) (vs : List V) :
    scale c (expand orthantVariable vs) =
      scale c (relabel (Sum.map (lookup vs) (lookup vs)) (orthantTemplate vs.length)) := by
  rw [orthantTemplate, orthant_expand_map, lookup_finRange]

theorem length_expand_two (f : V → Poly W) (hf : ∀ v, (f v).length = 2) (vs : List V) :
    (expand f vs).length = 2 ^ vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [expand, length_product, hf, ih, List.length_cons, pow_succ']

theorem length_cubeTemplate (d m : ℕ) : (cubeTemplate d m).length = 2 ^ m := by
  unfold cubeTemplate cubeTerm
  rw [length_scale, length_expand_two cubeVariable (fun _ => rfl), List.length_finRange]

theorem length_orthantTemplate (m : ℕ) : (orthantTemplate m).length = 2 ^ m := by
  unfold orthantTemplate
  rw [length_expand_two orthantVariable (fun _ => rfl), List.length_finRange]

end JointThermoComplexity.Complexity.RawNormalizationTemplates

#print axioms JointThermoComplexity.Complexity.RawNormalizationTemplates.cubeTemplate
#print axioms JointThermoComplexity.Complexity.RawNormalizationTemplates.cubeTerm_from_template
#print axioms JointThermoComplexity.Complexity.RawNormalizationTemplates.orthantTerm_from_template
#print axioms JointThermoComplexity.Complexity.RawNormalizationTemplates.length_cubeTemplate
