module
public import proofs.JointThermoComplexity.Complexity.DenseLoadedWordIdentity

set_option autoImplicit false
@[expose] public section

/-! Ordered source traversal emits the exact consecutive normalized records.
The cursor offset remains ghost data; physical dimensions are fixed by the first pass. -/

namespace JointThermoComplexity.Complexity.DenseCanonicalSource
open CountedSparseControl DenseMarkedControl DenseCanonicalPacket
variable {n : ℕ}

theorem stopped (boxed right : Bool) (n N k : ℕ) (s : State) (hs : s.base.running = false) :
    runWords boxed right n N k s = [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [runWords, show word boxed right n N s = [] by simp only [word, hs, Bool.false_eq_true, ↓reduceIte],
      step_stopped boxed s hs, ih, List.nil_append]

theorem run_records (boxed right : Bool) (Q : SparsePolynomialCodec.PolynomialData)
    (block : (ℤ × List (Fin n)) → SparseInteger.Poly (Fin Q.arity))
    (hlen : ∀ a, (block a).length = 2 ^ a.2.length)
    (hword : ∀ pre post a suffix, a.2.length ≤ 4 →
      Q.payload = pre ++ block a ++ post →
      DenseLoadedPacket.word boxed right n Q.payload.length (2 + pre.length)
        (SparseOffsetCode.termCode a ++ suffix) =
        records boxed right Q (2 + pre.length) (block a).length)
    (source : SparseInteger.Poly (Fin n)) (hp : SparseInteger.DegreeLE 4 source)
    (pre post : SparseInteger.Poly (Fin Q.arity))
    (hdata : Q.payload = pre ++ source.flatMap block ++ post)
    (k : ℕ) (hk : source.length + 1 ≤ k) (before suffix : List Bool) (A : ℕ) :
    runWords boxed right n Q.payload.length k
      ⟨⟨true, before, SparseOffsetCode.code source ++ suffix, A⟩, pre.length⟩ =
      records boxed right Q (2 + pre.length) (source.flatMap block).length := by
  induction source generalizing pre k before A with
  | nil =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by simp only [List.length_nil] at hk; omega)
    have he : step boxed ⟨⟨true, before, [false] ++ suffix, A⟩, pre.length⟩ =
        ⟨⟨false, before ++ [false], suffix, A⟩, pre.length⟩ := rfl
    change word boxed right n Q.payload.length ⟨⟨true, before, [false] ++ suffix, A⟩, pre.length⟩ ++
      runWords boxed right n Q.payload.length k (step boxed ⟨⟨true, before, [false] ++ suffix, A⟩, pre.length⟩) = _
    rw [he, stopped boxed right n Q.payload.length k _ rfl]
    rfl
  | cons a p ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by simp only [List.length_cons] at hk; omega)
    have ha := hp a List.mem_cons_self
    have hp' : SparseInteger.DegreeLE 4 p := fun b hb => hp b (List.mem_cons_of_mem a hb)
    have hd : Q.payload = pre ++ block a ++ (p.flatMap block ++ post) := by
      simpa only [List.flatMap_cons, List.append_assoc] using hdata
    have hw := hword pre (p.flatMap block ++ post) a (SparseOffsetCode.code p ++ suffix) ha hd
    have hw' : word boxed right n Q.payload.length
        ⟨⟨true, before, SparseOffsetCode.code (a :: p) ++ suffix, A⟩, pre.length⟩ =
        records boxed right Q (2 + pre.length) (block a).length := by
      simpa only [word, SparseOffsetCode.code_cons, List.cons_append, SourceBitRead.value,
        BooleanMachine.suffix, ↓reduceIte, List.append_assoc] using hw
    have hd' : Q.payload = (pre ++ block a) ++ p.flatMap block ++ post := by
      simpa only [List.flatMap_cons, List.append_assoc] using hdata
    have hr : pre.length + 2 ^ a.2.length = (pre ++ block a).length := by
      rw [List.length_append, hlen]
    have hi := ih hp' (pre ++ block a) hd' k (by simp only [List.length_cons] at hk; omega)
      ((before ++ [true]) ++ SparseOffsetCode.termCode a) (A + SparseOffsetCode.weight boxed a)
    rw [runWords, hw', CountedSparseCode.step_cons boxed a p before suffix A pre.length ha, hr, hi]
    simpa only [List.flatMap_cons, List.length_append, Nat.add_assoc] using
      (records_add boxed right Q (2 + pre.length) (block a).length (p.flatMap block).length).symm

theorem boxed (right : Bool) (payload : SparseInteger.Poly (Fin n))
    (source : SparseInteger.Poly (Fin n)) (hp : SparseInteger.DegreeLE 4 source)
    (pre post : SparseInteger.Poly (Fin n))
    (hdata : payload = pre ++ SparseSubstitution.cube 4 source ++ post)
    (k : ℕ) (hk : source.length + 1 ≤ k) (before suffix : List Bool) (A : ℕ) :
    runWords true right n payload.length k
      ⟨⟨true, before, SparseOffsetCode.code source ++ suffix, A⟩, pre.length⟩ =
      records true right ⟨n, payload⟩ (2 + pre.length) (SparseSubstitution.cube 4 source).length := by
  simpa only [DenseLoadedWordIdentity.cube_flatMap] using
    run_records true right ⟨n, payload⟩ (SparseSubstitution.cubeTerm 4)
      (CountedSparseCode.cubeTerm_length 4)
      (fun pre post a suffix hm hd => DenseLoadedWordIdentity.boxed right payload pre post a.1 a.2 hm suffix hd)
      source hp pre post (by simpa only [DenseLoadedWordIdentity.cube_flatMap] using hdata)
      k hk before suffix A

theorem unboxed (right : Bool) (payload : SparseInteger.Poly (Fin (n + n)))
    (source : SparseInteger.Poly (Fin n)) (hp : SparseInteger.DegreeLE 4 source)
    (pre post : SparseInteger.Poly (Fin (n + n)))
    (hdata : payload = pre ++ SparseInteger.relabel finSumFinEquiv (SparseSubstitution.orthant source) ++ post)
    (k : ℕ) (hk : source.length + 1 ≤ k) (before suffix : List Bool) (A : ℕ) :
    runWords false right n payload.length k
      ⟨⟨true, before, SparseOffsetCode.code source ++ suffix, A⟩, pre.length⟩ =
      records false right ⟨n + n, payload⟩ (2 + pre.length)
        (SparseInteger.relabel finSumFinEquiv (SparseSubstitution.orthant source)).length := by
  simpa only [DenseLoadedWordIdentity.orthant_flatMap] using
    run_records false right ⟨n + n, payload⟩ (fun a => DenseLoadedWordIdentity.orthantTerm a.1 a.2)
      (fun a => DenseLoadedWordIdentity.orthantTerm_length a.1 a.2)
      (fun pre post a suffix hm hd => DenseLoadedWordIdentity.unboxed right payload pre post a.1 a.2 hm suffix hd)
      source hp pre post (by simpa only [DenseLoadedWordIdentity.orthant_flatMap] using hdata)
      k hk before suffix A

theorem canonical_runWords (boxedMode right : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (hp : SparseInteger.DegreeLE 4 p.payload) :
    runWords boxedMode right p.arity (DenseTwoPassControl.total boxedMode (SparsePolynomialCodec.code p))
      (SparsePolynomialCodec.code p).length (DenseTwoPassControl.initial boxedMode (SparsePolynomialCodec.code p)) =
      records boxedMode right (FinitePositiveCoordinates.data boxedMode p) 2
        (FinitePositiveCoordinates.data boxedMode p).payload.length := by
  rw [DenseCanonicalControl.total_code boxedMode p hp, DenseCanonicalControl.initial_code boxedMode p hp]
  have hk : p.payload.length + 1 ≤ (SparsePolynomialCodec.code p).length := by
    have hf := SparseOffsetCode.enough_fuel p.payload
    rw [SparseCountedEntry.code_eq, List.length_append]
    omega
  cases boxedMode with
  | false =>
    have h :=
      unboxed right (SparseInteger.relabel finSumFinEquiv (SparseSubstitution.orthant p.payload)) p.payload hp [] []
        (by simp only [List.nil_append, List.append_nil]) (SparsePolynomialCodec.code p).length hk
        (RealSyntax.binderCode p.arity) [] (RawOffsetBounds.offset (FinitePositiveCoordinates.data false p).payload)
    rw [List.append_nil] at h
    exact h
  | true =>
    have h :=
      boxed right (SparseSubstitution.cube 4 p.payload) p.payload hp [] []
        (by simp only [List.nil_append, List.append_nil]) (SparsePolynomialCodec.code p).length hk
        (RealSyntax.binderCode p.arity) [] (RawOffsetBounds.offset (FinitePositiveCoordinates.data true p).payload)
    rw [List.append_nil] at h
    exact h

end JointThermoComplexity.Complexity.DenseCanonicalSource

#print axioms JointThermoComplexity.Complexity.DenseCanonicalSource.run_records
#print axioms JointThermoComplexity.Complexity.DenseCanonicalSource.canonical_runWords
