module
public import proofs.JointThermoComplexity.Complexity.StrictOriginalSection
public import proofs.JointThermoComplexity.Complexity.GeneratedTailTime
public import proofs.JointThermoComplexity.Complexity.FiniteGeneratedTail
public import proofs.Complexitylib.Classes.P.Defs
public import proofs.Complexitylib.Models.TuringMachine.Internal

set_option autoImplicit false
@[expose] public section

/-! Actual total binary FP for the boxed and unboxed finite strict source maps.
Encoded Domain inputs yield the full finite polynomial codec exactly. -/

namespace JointThermoComplexity.Complexity.StrictSourceFP
open _root_.Complexity _root_.Complexity.TM HeaderAt
open StrictInitialComposition (arity scratch)
open EquationSystemCodec FiniteStrictData

def output (boxed : Bool) (input : List Bool) : List Bool :=
  (StrictOriginalSection.result boxed input).emitted ++ StrictGeneratedTail.word input.length (arity input)

def machine (boxed : Bool) : TM 64 := seqTM (StrictOriginalSection.machine boxed) StrictGeneratedTail.machine

def timeBound (L : ℕ) (boxed : Bool) : ℕ :=
  StrictOriginalSection.timeBound L boxed + 1 + GeneratedTailTime.budget (GeneratedTailSetup.W L L)

noncomputable def timePolynomial (boxed : Bool) : Polynomial ℕ :=
  StrictOriginalSection.timePolynomial boxed + 1 + GeneratedTailTime.timePolynomial

theorem timePolynomial_eval (L : ℕ) (boxed : Bool) : (timePolynomial boxed).eval L = timeBound L boxed := by
  simp [timePolynomial, timeBound, StrictOriginalSection.timePolynomial_eval, GeneratedTailTime.timePolynomial_eval]

theorem lead_address_eq (L n : ℕ) : StrictLeadingInitialization.leadAddress L n = GeneratedTailSetup.J L n := rfl

theorem pair_registers (a b : ℕ) (work : Fin 64 → Tape)
    (ha : BinaryIncrementRun.Register a (work 42)) (hb : BinaryIncrementRun.Register b (work 43)) :
    ∀ i, BinaryIncrementRun.Register (![a, b] i) (work (StrictLeadingInitialization.rawPorts i)) := by
  intro i
  fin_cases i
  · exact ha
  · exact hb

theorem tail_ready (L n s : ℕ) (original : List Bool) (work : Fin 64 → Tape)
    (hs : ∀ j, Parked (work j)) (hx : StrictLeadingInitialization.Extra L n s original work) :
    GeneratedEnergyStep.Ready GeneratedTailFrame.ports (GeneratedTailSetup.initialValues L n)
      (GeneratedTailFrame.Keep L n s original) work := by
  refine ⟨hs, ?_, hx.1, hx.2.2.2⟩
  change ∀ i, BinaryIncrementRun.Register (![GeneratedTailSetup.J L n, 0] i)
    (work (StrictLeadingInitialization.rawPorts i))
  rw [← lead_address_eq]
  exact pair_registers _ _ work hx.2.1 hx.2.2.1

theorem hoareTime (boxed : Bool) (input : List Bool) :
    (machine boxed).HoareTime (StrictScheduleEntry.Initial input)
      (fun inp work out => Cursor (StrictOriginalSection.result boxed input).row.before
        (StrictOriginalSection.result boxed input).row.input (output boxed input) inp work out ∧
        (∀ j, Parked (work j)) ∧ GeneratedTailFrame.Keep input.length (arity input) (scratch input) input work)
      (timeBound input.length boxed) := by
  have hi := StrictOriginalSection.hoareTime boxed input
  have ht := StrictGeneratedTail.hoareTime input.length (arity input) (scratch input) input
    (StrictOriginalSection.result boxed input).row.before (StrictOriginalSection.result boxed input).row.input
    (StrictOriginalSection.result boxed input).emitted
  have hseq := seqTM_hoareTime _ _ hi (by
    rintro inp work out ⟨⟨hc, hr⟩, _hf⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨hc, tail_ready input.length (arity input) (scratch input) input work
      hr.square.saved.safe hr.square.saved.extra⟩) ht
  apply hseq.consequence (fun _ _ _ h => h)
  · rintro inp work out ⟨hc, hr⟩
    exact ⟨hc, hr.safe, hr.extra⟩
  · have htime := GeneratedTailTime.runtime_bound input.length (arity input) (scratch input)
      (HeaderControl.count_le_length input)
    rw [GeneratedTailTime.timePolynomial_eval] at htime
    unfold timeBound
    omega

theorem machine_computesInTime (boxed : Bool) :
    (machine boxed).ComputesInTime (output boxed) (fun L => timeBound L boxed) := by
  intro input
  obtain ⟨d, t, ht, hd, hh, hc, _hs, _hk⟩ := hoareTime boxed input
    (Tape.init (input.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init []) ⟨rfl, fun _ => rfl, rfl⟩
  exact ⟨d, t, ht, hd, hh, ((FixedOutput.outAcc_iff _ _).mpr ⟨hc.tapePrefix, hc.zero⟩).hasOutput⟩

theorem output_mem_FP (boxed : Bool) : output boxed ∈ FP := by
  let P := timePolynomial boxed
  refine ⟨P.natDegree, 64, machine boxed, (fun L => timeBound L boxed), machine_computesInTime boxed, ?_⟩
  exact BigO.of_polynomial_bound P (fun L => by rw [timePolynomial_eval])

theorem encoded_hoareTime (boxed : Bool) (p : Data) (hp : FiniteEquationHardness.Domain p) :
    (machine boxed).HoareTime (StrictScheduleEntry.Initial (code p))
      (fun inp work out => Cursor (code p) [] (FiniteGeneratedTail.targetCode boxed p) inp work out ∧
        (∀ j, Parked (work j)) ∧ GeneratedTailFrame.Keep (inputLength p) p.arity (scratch (code p)) (code p) work)
      (timeBound (inputLength p) boxed) := by
  let emitted := SparseListCodec.unaryCode (variableCount p) ++
    (FiniteRowSquare.finiteEntries (FiniteStrictPrefix.lead boxed p) ++
      FiniteRowSquare.finiteEntries (FiniteRowEnergyLoop.energy p))
  have hi := StrictOriginalSection.encoded_hoareTime boxed p hp
  have ht := StrictGeneratedTail.hoareTime (inputLength p) p.arity (scratch (code p)) (code p) (code p) [] emitted
  have hseq := seqTM_hoareTime _ _ hi (by
    rintro inp work out ⟨hc, hs, hx, _hf⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨hc, tail_ready (inputLength p) p.arity (scratch (code p)) (code p) work hs hx⟩) ht
  apply hseq.consequence (fun _ _ _ h => h)
  · rintro inp work out ⟨hc, hr⟩
    exact ⟨by simpa only [emitted, FiniteGeneratedTail.code_assembly] using hc, hr.safe, hr.extra⟩
  · have hn : p.arity ≤ inputLength p := by
      rw [← FiniteStrictPrefix.header_count]
      exact HeaderControl.count_le_length (code p)
    have htime := GeneratedTailTime.runtime_bound (inputLength p) p.arity (scratch (code p)) hn
    rw [GeneratedTailTime.timePolynomial_eval] at htime
    unfold timeBound
    omega

theorem prefix_word_unique {xs ys : List Bool} {out : Tape}
    (hx : out.HasBinaryPrefix xs) (hy : out.HasBinaryPrefix ys) : xs = ys := by
  apply List.ext_getElem
  · have hxs := hx.1
    have hys := hy.1
    omega
  · intro i hi hj
    have he := (hx.2.1 i hi).symm.trans (hy.2.1 i hj)
    cases hxi : xs[i] <;> cases hyi : ys[i] <;> simp_all [Γ.ofBool]

theorem output_code (boxed : Bool) (p : Data) (hp : FiniteEquationHardness.Domain p) :
    output boxed (code p) = FiniteGeneratedTail.targetCode boxed p := by
  obtain ⟨d1, t1, _ht1, hd1, hh1, hc1, _hs1, _hx1⟩ := hoareTime boxed (code p)
    (Tape.init ((code p).map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init []) ⟨rfl, fun _ => rfl, rfl⟩
  obtain ⟨d2, t2, _ht2, hd2, hh2, hc2, _hs2, _hx2⟩ := encoded_hoareTime boxed p hp
    (Tape.init ((code p).map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init []) ⟨rfl, fun _ => rfl, rfl⟩
  have h12 := (machine boxed).reachesIn_le_halt hd1 hd2 hh2
  have h21 := (machine boxed).reachesIn_le_halt hd2 hd1 hh1
  have he : t1 = t2 := Nat.le_antisymm h12 h21
  subst t2
  have hd : d1 = d2 := TM.reachesIn_right_unique hd1 hd2
  have hout := hc2.tapePrefix
  rw [← hd] at hout
  exact prefix_word_unique hc1.tapePrefix hout

theorem boxed_code (p : Data) (hp : FiniteEquationHardness.Domain p) : output true (code p) = boundedCode p := by
  simpa only [FiniteGeneratedTail.targetCode, ↓reduceIte] using output_code true p hp

theorem unboxed_code (p : Data) (hp : FiniteEquationHardness.Domain p) : output false (code p) = allRealCode p := by
  simpa only [FiniteGeneratedTail.targetCode, Bool.false_eq_true, ↓reduceIte] using output_code false p hp

end JointThermoComplexity.Complexity.StrictSourceFP

#print axioms JointThermoComplexity.Complexity.StrictSourceFP.machine_computesInTime
#print axioms JointThermoComplexity.Complexity.StrictSourceFP.tail_ready
#print axioms JointThermoComplexity.Complexity.StrictSourceFP.output_mem_FP
#print axioms JointThermoComplexity.Complexity.StrictSourceFP.output_code
#print axioms JointThermoComplexity.Complexity.StrictSourceFP.boxed_code
#print axioms JointThermoComplexity.Complexity.StrictSourceFP.unboxed_code
