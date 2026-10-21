module
public import proofs.JointThermoComplexity.Complexity.SparseInputInitialization
public import proofs.JointThermoComplexity.Complexity.SparseHeaderRouting
public import proofs.JointThermoComplexity.Complexity.CountedSparseCode
public import proofs.JointThermoComplexity.Complexity.FiniteEquationEncoding

set_option autoImplicit false
@[expose] public section

/-! Actual total input entry for the counted normalization pass. -/

namespace JointThermoComplexity.Complexity.SparseCountedEntry
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun BoxBufferState
open BinaryScaleBuffer (oldWork)
open SparseOffsetPorts

def frame (n : ℕ) (work : Fin 32 → Tape) : Prop := IsReg n (work arity)

def retained (L : ℕ) (work : Fin 33 → Tape) : Prop :=
  Register 1 (work layout.acc.castSucc) ∧ (work marker.castSucc).head = 1 ∧
    (work marker.castSucc).read = Γ.one ∧ IsReg L (work fuel.castSucc) ∧
      ∀ j, j ≠ layout.acc.castSucc → j ≠ marker.castSucc → j ≠ fuel.castSucc →
        j ≠ SparseHeaderRaw.arity → j ≠ SparseHeaderRaw.flag → j ≠ SparseHeaderRaw.sink → IsReg 0 (work j)

theorem retained_stable (L : ℕ) : SparseHeaderRaw.Stable (retained L) := by
  rintro work next he ⟨ha, hh, hv, hf, hz⟩
  exact ⟨by rw [he layout.acc.castSucc (by decide) (by decide) (by decide)]; exact ha,
    by rw [he marker.castSucc (by decide) (by decide) (by decide)]; exact hh,
    by rw [he marker.castSucc (by decide) (by decide) (by decide)]; exact hv,
    by rw [he fuel.castSucc (by decide) (by decide) (by decide)]; exact hf,
    fun j hac hmk hfu har hfl hsi => by rw [he j har hfl hsi]; exact hz j hac hmk hfu har hfl hsi⟩

def state (input : List Bool) : CountedSparseControl.State :=
  ⟨⟨true, HeaderControl.copied input, HeaderControl.suffix input, 1⟩, 0⟩

def headerEntry : TM 33 := seqTM SparseInputInitialization.machine SparseHeaderRouting.machine

def machine (boxed : Bool) : TM 33 := seqTM headerEntry (CountedSparseLoop.machine boxed)

def timeBound (L : ℕ) : ℕ := 7 * L + 33 + CountedSparseLoop.timeBound L 1 0 L

theorem frame_stable (n : ℕ) : CountedSparseLoop.Stable (frame n) := by
  intro work next he hr
  change IsReg n (next arity)
  rw [he arity (by decide) (by decide) (by decide)]
  exact hr

theorem initialize_hoareTime (input : List Bool) :
    headerEntry.HoareTime (SparseInputInitialization.Initial input)
      (fun inp work out => CountedMarkedStep.Inv input.length [] (frame (HeaderControl.count input)) (state input) inp work out ∧
        IsReg input.length (work fuel.castSucc)) (7 * input.length + 32) := by
  have hi := SparseInputInitialization.hoareTime input
  have hh := SparseHeaderRouting.hoareTime [] input [] (retained input.length) (retained_stable input.length)
  have hs := seqTM_hoareTime _ _ hi (by
    rintro inp work out ⟨hc, hsafe, hm, ha, hmh, hmr, hf, hz⟩
    obtain ⟨hinput, hwork, hout⟩ := hc.phase
    rw [hinput, hwork, hout]
    refine ⟨hc, hsafe, hm, ?_, ?_, ?_, ha, hmh, hmr, hf, ?_⟩
    · exact hz SparseHeaderRaw.arity (by decide) (by decide) (by decide)
    · exact (hz SparseHeaderRaw.flag (by decide) (by decide) (by decide)).head_eq
    · simpa only [List.replicate_zero] using CountTape.string_of_register
        (hz SparseHeaderRaw.sink (by decide) (by decide) (by decide))
    · exact fun j hac hmk hfu _ _ _ => hz j hac hmk hfu) hh
  apply hs.consequence
  · exact fun _ _ _ hp => hp
  · rintro inp work out ⟨hc, hsafe, _hm, harity, hflag, _hvalid, hscratch, hacc, hmh, hmr, hf, hz⟩
    have low (j : Fin 32) (hj : j.val ≤ 10) : IsReg 0 (work j.castSucc) := by
      have hn (k : Fin 33) (hk : 10 < k.val) : j.castSucc ≠ k := by
        intro he
        have hv := congrArg (fun x : Fin 33 => x.val) he
        change j.val = k.val at hv
        omega
      exact hz j.castSucc (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))
        (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))
    have hready : SparseOffsetLayout.Ready input.length layout (oldWork work) := by
      refine ⟨of_register (by omega) (low layout.idx (by decide)), (low layout.sign (by decide)).head_eq, ?_,
        (low layout.ending (by decide)).head_eq, hflag⟩
      intro p hmem
      have hp : p ∈ [(2, 6), (3, 7), (4, 8), (5, 9)] := hmem
      simp at hp
      have hd : p.1.val ≤ 10 := by rcases hp with rfl | rfl | rfl | rfl <;> decide
      have hm : p.2.val ≤ 10 := by rcases hp with rfl | rfl | rfl | rfl <;> decide
      exact ⟨of_register (by omega) (low p.1 hd), (low p.2 hm).head_eq⟩
    have hadj := hz layout.adjusted.castSucc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have haux := hz layout.aux.castSucc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hrows := hz rows.castSucc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hc' : Cursor (HeaderControl.copied input) (HeaderControl.suffix input) [] inp work out := by
      simpa only [List.nil_append] using hc
    have har : frame (HeaderControl.count input) (oldWork work) := harity
    exact ⟨⟨hc', hsafe, ⟨⟨hready, hadj.head_eq, hacc,
      ⟨CountTape.empty_prefix_of_zero haux, haux.cell0⟩,
      ⟨CountTape.empty_prefix_of_zero hscratch, hscratch.cell0⟩, har⟩,
      SparseInputInitialization.binary_zero hrows⟩, hmh, hmr⟩, hf⟩
  · omega

theorem hoareTime (boxed : Bool) (input : List Bool) :
    (machine boxed).HoareTime (SparseInputInitialization.Initial input)
      (fun inp work out => CountedMarkedStep.Inv input.length [] (frame (HeaderControl.count input))
        (CountedSparseControl.run boxed input.length (state input)) inp work out ∧
          IsReg input.length (work fuel.castSucc)) (timeBound input.length) := by
  have hlen : (HeaderControl.suffix input).length ≤ input.length := by
    have he := congrArg List.length (HeaderControl.consumed_and_suffix input)
    rw [List.length_append] at he
    omega
  have hp := CountedSparseLoop.hoareTime boxed input.length 1 0 input.length [] (frame (HeaderControl.count input))
    (frame_stable _) (state input) hlen (by change (1 : ℕ).bits.length ≤ 1; decide)
      (by change (0 : ℕ).bits.length ≤ 0; decide)
  have hh := initialize_hoareTime input
  have hs := seqTM_hoareTime _ _ hh (by
    rintro inp work out ⟨hi, hf⟩
    obtain ⟨hinput, hwork, hout⟩ := hi.1.phase
    rw [hinput, hwork, hout]
    exact ⟨hi, hf⟩) hp
  exact hs.mono_bound (by unfold timeBound; omega)

theorem cubic_timeBound (L : ℕ) :
    timeBound L = 3328 * L ^ 3 + 8687531 * L ^ 2 + 10897799 * L + 35 := by
  unfold timeBound
  rw [CountedSparseLoop.cubic_timeBound]
  ring1

theorem code_eq (p : SparsePolynomialCodec.PolynomialData) :
    SparsePolynomialCodec.code p = RealSyntax.binderCode p.arity ++ SparseOffsetCode.code p.payload := by
  rw [FiniteEquationEncoding.binder_unary]
  rfl

theorem count_code (p : SparsePolynomialCodec.PolynomialData) :
    HeaderControl.count (SparsePolynomialCodec.code p) = p.arity := by rw [code_eq, HeaderControl.count_code]

theorem state_code (p : SparsePolynomialCodec.PolynomialData) : state (SparsePolynomialCodec.code p) =
    ⟨⟨true, RealSyntax.binderCode p.arity, SparseOffsetCode.code p.payload, 1⟩, 0⟩ := by
  unfold state
  rw [code_eq, HeaderControl.copied_code, HeaderControl.suffix_code]

theorem canonical_hoareTime (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (hp : SparseInteger.DegreeLE 4 p.payload) :
    (machine boxed).HoareTime (SparseInputInitialization.Initial (SparsePolynomialCodec.code p))
      (fun inp work out => CountedMarkedStep.Inv (SparsePolynomialCodec.code p).length [] (frame p.arity)
        ⟨⟨false, SparsePolynomialCodec.code p, [], 1 + SparseOffsetCode.total boxed p.payload⟩,
          CountedSparseCode.rowTotal p.payload⟩ inp work out ∧ IsReg (SparsePolynomialCodec.code p).length (work fuel.castSucc))
      (timeBound (SparsePolynomialCodec.code p).length) := by
  have ht := hoareTime boxed (SparsePolynomialCodec.code p)
  have hk : p.payload.length + 1 ≤ (SparsePolynomialCodec.code p).length := by
    have hf := SparseOffsetCode.enough_fuel p.payload
    rw [code_eq, List.length_append]
    omega
  have hr := CountedSparseCode.run_code boxed p.payload hp (SparsePolynomialCodec.code p).length hk
    (RealSyntax.binderCode p.arity) [] 1 0
  simp only [List.append_nil, Nat.zero_add] at hr
  rw [count_code, state_code, hr, ← code_eq] at ht
  exact ht

end JointThermoComplexity.Complexity.SparseCountedEntry

#print axioms JointThermoComplexity.Complexity.SparseCountedEntry.hoareTime
#print axioms JointThermoComplexity.Complexity.SparseCountedEntry.cubic_timeBound
#print axioms JointThermoComplexity.Complexity.SparseCountedEntry.canonical_hoareTime
