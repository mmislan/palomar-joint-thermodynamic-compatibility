module
public import proofs.JointThermoComplexity.Complexity.DenseRawPowerIdentity

set_option autoImplicit false
@[expose] public section

/-! Ordered raw packet words agree with the original record list for an exact
normalized block inside the complete stored polynomial. -/

namespace JointThermoComplexity.Complexity.DenseCanonicalPacket
variable {A B : Type} {n : ℕ}

theorem words_map (right : Bool) (N e : ℕ) (f : A → B) (gamma : B → Fin e → ℕ) (coef : B → ℤ)
    (v : ℕ) (negative : Bool) (current : ℕ) (rows : List A) :
    DensePacketControl.words right N e gamma coef v negative current (rows.map f) =
      DensePacketControl.words right N e (fun a => gamma (f a)) (fun a => coef (f a)) v negative current rows := by
  induction rows generalizing current with
  | nil => rfl
  | cons a rest ih => simp only [List.map_cons, DensePacketControl.words, ih]

theorem words_ofFn (right : Bool) (N e : ℕ) (gamma : A → Fin e → ℕ) (coef : A → ℤ) (v : ℕ) (negative : Bool)
    (rows : List A) (current : ℕ) (f : ℕ → List Bool)
    (hw : ∀ j : Fin rows.length, DenseRawRecord.word right N (DensePacketControl.index N (current + j.val)) e (gamma rows[j.val])
      (coef rows[j.val]) v negative = f (current + j.val)) :
    DensePacketControl.words right N e gamma coef v negative current rows = (List.ofFn (fun j : Fin rows.length => f (current + j.val))).flatten := by
  induction rows generalizing current with
  | nil => rfl
  | cons a rest ih =>
    have h0 : DenseRawRecord.word right N (DensePacketControl.index N current) e (gamma a) (coef a) v negative = f current := by
      simpa only [Fin.val_zero, Nat.add_zero, List.getElem_cons_zero] using hw 0
    have htail : ∀ j : Fin rest.length, DenseRawRecord.word right N (DensePacketControl.index N (current + 1 + j.val)) e (gamma rest[j.val])
        (coef rest[j.val]) v negative = f (current + 1 + j.val) := by
      intro j
      simpa only [Fin.val_succ, List.getElem_cons_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hw j.succ
    rw [DensePacketControl.words, h0, ih (current + 1) htail]
    simp only [List.ofFn_succ, List.flatten_cons, Fin.val_zero, Fin.val_succ, Nat.add_zero,
      Nat.add_left_comm, Nat.add_comm]

theorem get_middle (pre post : List A) (rows : List B) (f : B → A) (j : Fin rows.length) :
    (pre ++ rows.map f ++ post)[pre.length + j.val]'(by simp only [List.length_append, List.length_map]; omega) = f rows[j.val] := by
  have h1 : pre.length + j.val - pre.length = j.val := by omega
  simp [h1, j.isLt]

def records (boxed right : Bool) (p : SparsePolynomialCodec.PolynomialData) (current count : ℕ) : List Bool :=
  (List.ofFn (fun j : Fin count => DenseRecordCore.recordWord right (RationalPolynomialNetwork.left boxed p)
    (RationalPolynomialNetwork.right boxed p) (DensePacketControl.index p.payload.length (current + j.val)))).flatten

theorem flatten_range_add (f : ℕ → List Bool) (current a b : ℕ) :
    (List.ofFn (fun j : Fin (a + b) => f (current + j.val))).flatten =
      (List.ofFn (fun j : Fin a => f (current + j.val))).flatten ++ (List.ofFn (fun j : Fin b => f (current + a + j.val))).flatten := by
  have he : (fun j : Fin (a + b) => f (current + j.val)) =
      Fin.append (fun j : Fin a => f (current + j.val)) (fun j : Fin b => f (current + a + j.val)) := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i; rw [Fin.append_left]; rfl
    · intro i; rw [Fin.append_right]
      change f (current + (a + i.val)) = f (current + a + i.val)
      rw [Nat.add_assoc]
  rw [he, List.ofFn_fin_append, List.flatten_append]

theorem records_add (boxed right : Bool) (p : SparsePolynomialCodec.PolynomialData) (current a b : ℕ) :
    records boxed right p current (a + b) = records boxed right p current a ++ records boxed right p (current + a) b :=
  flatten_range_add (fun k => DenseRecordCore.recordWord right (RationalPolynomialNetwork.left boxed p)
    (RationalPolynomialNetwork.right boxed p) (DensePacketControl.index p.payload.length k)) current a b

def boxedBlock (c : ℤ) (vs : List (Fin n)) (rows : List (ℤ × List (Fin vs.length))) : SparseInteger.Poly (Fin n) :=
  rows.map (fun row => (c * row.1, row.2.map (RawNormalizationTemplates.lookup vs)))
def unboxedBlock (c : ℤ) (vs : List (Fin n)) (rows : List (ℤ × List (Fin vs.length ⊕ Fin vs.length))) : SparseInteger.Poly (Fin (n + n)) :=
  rows.map (fun row => (c * row.1, DenseTemplatePowerCode.signedMonomial vs row.2))

theorem boxed (right : Bool) (payload pre post : SparseInteger.Poly (Fin n)) (vs : List (Fin n)) (hm : vs.length ≤ 4)
    (rows : List (ℤ × List (Fin vs.length))) (v : ℕ) (negative : Bool)
    (hp : payload = pre ++ boxedBlock (RationalFactorWords.coefficient negative v) vs rows ++ post) :
    DensePacketControl.words right payload.length n
      (fun row : ℤ × List (Fin 4) => DenseRawExternal.boxedGamma 4 (by decide) (DenseRawReady.values (vs.map Fin.val)) row.2 n)
      Prod.fst v negative (2 + pre.length) (rows.map (fun row => (row.1, row.2.map (Fin.castLE hm)))) =
      records true right ⟨n, payload⟩ (2 + pre.length) rows.length := by
  rw [words_map]
  unfold records
  apply words_ofFn right payload.length n _ _ v negative rows (2 + pre.length)
    (fun current => DenseRecordCore.recordWord right (RationalPolynomialNetwork.left true ⟨n, payload⟩)
      (RationalPolynomialNetwork.right true ⟨n, payload⟩) (DensePacketControl.index payload.length current))
  intro j
  have hl := congrArg List.length hp
  simp only [List.length_append, boxedBlock, List.length_map] at hl
  let i : Fin payload.length := ⟨pre.length + j.val, by omega⟩
  have hx : DensePacketControl.index payload.length (2 + pre.length + j.val) = i.succ.succ := by
    apply Fin.ext
    rw [DensePacketControl.index_val _ _ (by omega)]
    change 2 + pre.length + j.val = pre.length + j.val + 1 + 1
    omega
  have hd : payload[i.val] = (RationalFactorWords.coefficient negative v * rows[j.val].1, rows[j.val].2.map (RawNormalizationTemplates.lookup vs)) := by
    simpa only [i, hp, boxedBlock] using get_middle pre post rows
      (fun row => (RationalFactorWords.coefficient negative v * row.1, row.2.map (RawNormalizationTemplates.lookup vs))) j
  rw [hx]
  exact DenseRecordWordIdentity.regular true right ⟨n, payload⟩ i _ rows[j.val].1 v negative
    (DenseRawPowerIdentity.boxed_original right ⟨n, payload⟩ i vs hm rows[j.val].2 (congrArg Prod.snd hd)) (congrArg Prod.fst hd)

theorem unboxed (right : Bool) (payload pre post : SparseInteger.Poly (Fin (n + n))) (vs : List (Fin n)) (hm : vs.length ≤ 4)
    (rows : List (ℤ × List (Fin vs.length ⊕ Fin vs.length))) (v : ℕ) (negative : Bool)
    (hp : payload = pre ++ unboxedBlock (RationalFactorWords.coefficient negative v) vs rows ++ post) :
    DensePacketControl.words right payload.length ((n + n) + 1)
      (fun row : ℤ × List (Fin 4 ⊕ Fin 4) => DenseRawExternal.unboxedGamma 4 (by decide) (DenseRawReady.values (vs.map Fin.val)) row.2 n)
      Prod.fst v negative (2 + pre.length) (rows.map (fun row => (row.1, row.2.map (Sum.map (Fin.castLE hm) (Fin.castLE hm))))) =
      records false right ⟨n + n, payload⟩ (2 + pre.length) rows.length := by
  rw [words_map]
  unfold records
  apply words_ofFn right payload.length ((n + n) + 1) _ _ v negative rows (2 + pre.length)
    (fun current => DenseRecordCore.recordWord right (RationalPolynomialNetwork.left false ⟨n + n, payload⟩)
      (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) (DensePacketControl.index payload.length current))
  intro j
  have hl := congrArg List.length hp
  simp only [List.length_append, unboxedBlock, List.length_map] at hl
  let i : Fin payload.length := ⟨pre.length + j.val, by omega⟩
  have hx : DensePacketControl.index payload.length (2 + pre.length + j.val) = i.succ.succ := by
    apply Fin.ext
    rw [DensePacketControl.index_val _ _ (by omega)]
    change 2 + pre.length + j.val = pre.length + j.val + 1 + 1
    omega
  have hd : payload[i.val] = (RationalFactorWords.coefficient negative v * rows[j.val].1, DenseTemplatePowerCode.signedMonomial vs rows[j.val].2) := by
    simpa only [i, hp, unboxedBlock] using get_middle pre post rows
      (fun row => (RationalFactorWords.coefficient negative v * row.1, DenseTemplatePowerCode.signedMonomial vs row.2)) j
  rw [hx]
  exact DenseRecordWordIdentity.regular false right ⟨n + n, payload⟩ i _ rows[j.val].1 v negative
    (DenseRawPowerIdentity.unboxed_original right payload i vs hm rows[j.val].2 (congrArg Prod.snd hd)) (congrArg Prod.fst hd)

theorem boxed_block_cube (c : ℤ) (vs : List (Fin n)) :
    boxedBlock c vs (RawNormalizationTemplates.cubeTemplate 4 vs.length) = SparseSubstitution.cubeTerm 4 (c, vs) := by
  rw [RawNormalizationTemplates.cubeTerm_from_template]
  simp [boxedBlock, SparseInteger.scale, SparseInteger.relabel, List.map_map, Function.comp_def]

theorem unboxed_block_orthant (c : ℤ) (vs : List (Fin n)) :
    unboxedBlock c vs (RawNormalizationTemplates.orthantTemplate vs.length) =
      SparseInteger.relabel finSumFinEquiv (SparseInteger.scale c (SparseSubstitution.expand SparseSubstitution.orthantVariable vs)) := by
  rw [RawNormalizationTemplates.orthantTerm_from_template]
  simp [unboxedBlock, DenseTemplatePowerCode.signedMonomial, SparseInteger.scale, SparseInteger.relabel, List.map_map, Function.comp_def]

theorem boxed_cube (right : Bool) (payload pre post : SparseInteger.Poly (Fin n)) (vs : List (Fin n)) (hm : vs.length ≤ 4)
    (v : ℕ) (negative : Bool) (hp : payload = pre ++ SparseSubstitution.cubeTerm 4 (RationalFactorWords.coefficient negative v, vs) ++ post) :
    DenseFourTemplatePacket.boxedWords right vs.length hm (DenseRawReady.values (vs.map Fin.val)) n payload.length v negative (2 + pre.length) =
      records true right ⟨n, payload⟩ (2 + pre.length) (RawNormalizationTemplates.cubeTemplate 4 vs.length).length := by
  have hp' : payload = pre ++ boxedBlock (RationalFactorWords.coefficient negative v) vs (RawNormalizationTemplates.cubeTemplate 4 vs.length) ++ post := by
    simpa only [boxed_block_cube] using hp
  exact boxed right payload pre post vs hm _ v negative hp'

theorem unboxed_orthant (right : Bool) (payload pre post : SparseInteger.Poly (Fin (n + n))) (vs : List (Fin n)) (hm : vs.length ≤ 4)
    (v : ℕ) (negative : Bool)
    (hp : payload = pre ++ SparseInteger.relabel finSumFinEquiv (SparseInteger.scale (RationalFactorWords.coefficient negative v)
      (SparseSubstitution.expand SparseSubstitution.orthantVariable vs)) ++ post) :
    DenseFourTemplatePacket.unboxedWords right vs.length hm (DenseRawReady.values (vs.map Fin.val)) n payload.length v negative (2 + pre.length) =
      records false right ⟨n + n, payload⟩ (2 + pre.length) (RawNormalizationTemplates.orthantTemplate vs.length).length := by
  have hp' : payload = pre ++ unboxedBlock (RationalFactorWords.coefficient negative v) vs (RawNormalizationTemplates.orthantTemplate vs.length) ++ post := by
    simpa only [unboxed_block_orthant] using hp
  exact unboxed right payload pre post vs hm _ v negative hp'

end JointThermoComplexity.Complexity.DenseCanonicalPacket

#print axioms JointThermoComplexity.Complexity.DenseCanonicalPacket.boxed_cube
#print axioms JointThermoComplexity.Complexity.DenseCanonicalPacket.unboxed_orthant
