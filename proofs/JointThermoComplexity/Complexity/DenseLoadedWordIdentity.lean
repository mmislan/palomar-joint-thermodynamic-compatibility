module
public import proofs.JointThermoComplexity.Complexity.DenseCanonicalPacket

set_option autoImplicit false
@[expose] public section

/-! Canonical signed-field and occurrence decoding select exactly the ordered
normalization packet for one stored source term. -/

namespace JointThermoComplexity.Complexity.DenseLoadedWordIdentity
variable {n : ℕ}

theorem coefficient_natAbs (c : ℤ) : RationalFactorWords.coefficient (decide (c < 0)) c.natAbs = c := by
  cases c <;> simp [RationalFactorWords.coefficient]
  rw [Int.negSucc_eq]
  omega

theorem raw_word (boxed right : Bool) (N current : ℕ) (c : ℤ) (vs : List (Fin n)) (hm : vs.length ≤ 4) (suffix : List Bool) :
    DenseLoadedPacket.word boxed right n N current (SparseOffsetCode.termCode (c, vs) ++ suffix) =
      DensePacketChoice.words boxed right vs.length hm (DenseRawReady.values (vs.map Fin.val)) n N c.natAbs (decide (c < 0)) current := by
  unfold DenseLoadedPacket.word SparseOffsetCode.termCode
  simp only [List.append_assoc, SignedRawControl.magnitude_integer, SignedRawControl.negative_integer, SignedRawControl.rest_integer]
  unfold DenseBankSelect.word
  rw [OccurrenceDispatchControl.choice_code vs suffix 4 hm]
  simp only [dite_eq_left hm, DenseRawReady.rawValues, BoundedOccurrenceControl.finite_code vs suffix 4 hm]

def orthantTerm (c : ℤ) (vs : List (Fin n)) : SparseInteger.Poly (Fin (n + n)) :=
  SparseInteger.relabel finSumFinEquiv (SparseInteger.scale c (SparseSubstitution.expand SparseSubstitution.orthantVariable vs))

theorem orthantTerm_length (c : ℤ) (vs : List (Fin n)) : (orthantTerm c vs).length = 2 ^ vs.length := by
  rw [orthantTerm, SparseInteger.length_relabel, SparseInteger.length_scale]
  exact RawNormalizationTemplates.length_expand_two SparseSubstitution.orthantVariable (fun _ => rfl) vs

theorem boxed (right : Bool) (payload pre post : SparseInteger.Poly (Fin n)) (c : ℤ) (vs : List (Fin n)) (hm : vs.length ≤ 4)
    (suffix : List Bool) (hp : payload = pre ++ SparseSubstitution.cubeTerm 4 (c, vs) ++ post) :
    DenseLoadedPacket.word true right n payload.length (2 + pre.length) (SparseOffsetCode.termCode (c, vs) ++ suffix) =
      DenseCanonicalPacket.records true right ⟨n, payload⟩ (2 + pre.length) (SparseSubstitution.cubeTerm 4 (c, vs)).length := by
  rw [raw_word true right payload.length (2 + pre.length) c vs hm suffix]
  have h := DenseCanonicalPacket.boxed_cube right payload pre post vs hm c.natAbs (decide (c < 0))
    (by simpa only [coefficient_natAbs] using hp)
  simpa only [DensePacketChoice.words, ↓reduceIte, RawNormalizationTemplates.length_cubeTemplate, CountedSparseCode.cubeTerm_length] using h

theorem unboxed (right : Bool) (payload pre post : SparseInteger.Poly (Fin (n + n))) (c : ℤ) (vs : List (Fin n)) (hm : vs.length ≤ 4)
    (suffix : List Bool) (hp : payload = pre ++ orthantTerm c vs ++ post) :
    DenseLoadedPacket.word false right n payload.length (2 + pre.length) (SparseOffsetCode.termCode (c, vs) ++ suffix) =
      DenseCanonicalPacket.records false right ⟨n + n, payload⟩ (2 + pre.length) (orthantTerm c vs).length := by
  rw [raw_word false right payload.length (2 + pre.length) c vs hm suffix]
  have h := DenseCanonicalPacket.unboxed_orthant right payload pre post vs hm c.natAbs (decide (c < 0))
    (by simpa only [coefficient_natAbs, orthantTerm] using hp)
  simpa only [DensePacketChoice.words, Bool.false_eq_true, ↓reduceIte, RawNormalizationTemplates.length_orthantTemplate, orthantTerm_length] using h

theorem cube_flatMap (p : SparseInteger.Poly (Fin n)) : p.flatMap (SparseSubstitution.cubeTerm 4) = SparseSubstitution.cube 4 p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [List.flatMap_cons, SparseSubstitution.cube_cons, ih]

theorem orthant_flatMap (p : SparseInteger.Poly (Fin n)) : p.flatMap (fun a => orthantTerm a.1 a.2) =
    SparseInteger.relabel finSumFinEquiv (SparseSubstitution.orthant p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.flatMap_cons, SparseSubstitution.orthant, SparseSubstitution.substitute_cons, orthantTerm] at ih ⊢
    rw [ih]
    exact (List.map_append ..).symm

end JointThermoComplexity.Complexity.DenseLoadedWordIdentity

#print axioms JointThermoComplexity.Complexity.DenseLoadedWordIdentity.boxed
#print axioms JointThermoComplexity.Complexity.DenseLoadedWordIdentity.unboxed
