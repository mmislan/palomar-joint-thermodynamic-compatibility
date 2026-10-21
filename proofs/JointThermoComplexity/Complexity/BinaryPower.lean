module
public import proofs.JointThermoComplexity.Complexity.RealCircuit

set_option autoImplicit false
@[expose] public section

/-!
# Repeated squaring with explicit arithmetic gates

Each exponent payload bit emits one square gate and at most one multiplication
gate. The construction has a uniform semantic proof for all real bases and all
natural exponents, and an actual gate-count bound in the exponent's binary
length. This is not yet a binary Turing-machine runtime theorem.
-/

namespace JointThermoComplexity.Complexity.BinaryPower
open RealCircuit

structure State (n : ℕ) where
  size : ℕ
  circuit : Circuit n size
  accumulator : Fin size
  power : Fin size

variable {n k : ℕ}

def State.advance (s : State n) : Bool → State n
  | false =>
      ⟨s.size + 1, s.circuit.snoc (.mul s.power s.power),
        s.accumulator.castSucc, Fin.last s.size⟩
  | true =>
      let first := s.circuit.snoc (.mul s.accumulator s.power)
      ⟨s.size + 2, first.snoc (.mul s.power.castSucc s.power.castSucc),
        (Fin.last s.size).castSucc, Fin.last (s.size + 1)⟩

def State.runBits (s : State n) : List Bool → State n
  | [] => s
  | b :: bits => (s.advance b).runBits bits

def State.accValue (s : State n) (ρ : Fin n → ℝ) : ℝ :=
  s.circuit.eval ρ s.accumulator

def State.powerValue (s : State n) (ρ : Fin n → ℝ) : ℝ :=
  s.circuit.eval ρ s.power

@[simp] theorem State.advance_false_accValue (s : State n) (ρ : Fin n → ℝ) :
    (s.advance false).accValue ρ = s.accValue ρ := by
  simp [State.advance, State.accValue]

@[simp] theorem State.advance_false_powerValue (s : State n) (ρ : Fin n → ℝ) :
    (s.advance false).powerValue ρ = s.powerValue ρ * s.powerValue ρ := by
  simp [State.advance, State.powerValue, Step.eval]

@[simp] theorem State.advance_true_accValue (s : State n) (ρ : Fin n → ℝ) :
    (s.advance true).accValue ρ = s.accValue ρ * s.powerValue ρ := by
  simp [State.advance, State.accValue, State.powerValue, Step.eval]

@[simp] theorem State.advance_true_powerValue (s : State n) (ρ : Fin n → ℝ) :
    (s.advance true).powerValue ρ = s.powerValue ρ * s.powerValue ρ := by
  simp [State.advance, State.powerValue, Step.eval]

theorem State.runBits_value (s : State n) (bits : List Bool) (ρ : Fin n → ℝ) :
    (s.runBits bits).accValue ρ =
      s.accValue ρ * s.powerValue ρ ^ BitCodec.readBits bits := by
  induction bits generalizing s with
  | nil => simp [State.runBits, BitCodec.readBits]
  | cons b bits ih =>
    rw [State.runBits, ih]
    cases b
    · simp only [State.advance_false_accValue, State.advance_false_powerValue,
        BitCodec.readBits, List.foldr_cons, Nat.bit_false]
      rw [← pow_two, ← pow_mul]
    · simp only [State.advance_true_accValue, State.advance_true_powerValue,
        BitCodec.readBits, List.foldr_cons, Nat.bit_true]
      rw [← pow_two, ← pow_mul, pow_succ]
      rw [mul_assoc, mul_comm (s.powerValue ρ)]

theorem State.runBits_size_le (s : State n) (bits : List Bool) :
    (s.runBits bits).size ≤ s.size + 2 * bits.length := by
  induction bits generalizing s with
  | nil => simp [State.runBits]
  | cons b bits ih =>
    have h := ih (s.advance b)
    cases b <;> simp only [State.runBits, State.advance, List.length_cons] at * <;> omega

theorem State.size_le_advance (s : State n) (b : Bool) : s.size ≤ (s.advance b).size := by
  cases b <;> simp [State.advance]

theorem State.size_le_runBits (s : State n) (bits : List Bool) :
    s.size ≤ (s.runBits bits).size := by
  induction bits generalizing s with
  | nil => exact Nat.le_refl _
  | cons b bits ih => exact (s.size_le_advance b).trans (ih (s.advance b))

theorem State.advance_preserves (s : State n) (b : Bool) (i : Fin s.size)
    (ρ : Fin n → ℝ) :
    (s.advance b).circuit.eval ρ (Fin.castLE (s.size_le_advance b) i) =
      s.circuit.eval ρ i := by
  cases b
  · change (s.circuit.snoc (.mul s.power s.power)).eval ρ i.castSucc = _
    simp
  · change ((s.circuit.snoc (.mul s.accumulator s.power)).snoc
      (.mul s.power.castSucc s.power.castSucc)).eval ρ i.castSucc.castSucc = _
    simp

/-- Appending the power gates preserves every previously computed value. -/
theorem State.runBits_preserves (s : State n) (bits : List Bool) (i : Fin s.size)
    (ρ : Fin n → ℝ) :
    (s.runBits bits).circuit.eval ρ (Fin.castLE (s.size_le_runBits bits) i) =
      s.circuit.eval ρ i := by
  induction bits generalizing s with
  | nil => rfl
  | cons b bits ih =>
    change ((s.advance b).runBits bits).circuit.eval ρ
      (Fin.castLE ((s.advance b).size_le_runBits bits)
        (Fin.castLE (s.size_le_advance b) i)) = s.circuit.eval ρ i
    rw [ih (s.advance b)]
    exact s.advance_preserves b i ρ

def start (c : Circuit n k) (base : Fin k) : State n :=
  ⟨k + 1, c.snoc (.constant 1), Fin.last k, base.castSucc⟩

def build (c : Circuit n k) (base : Fin k) (exponent : ℕ) : State n :=
  (start c base).runBits exponent.bits

theorem build_value (c : Circuit n k) (base : Fin k) (exponent : ℕ) (ρ : Fin n → ℝ) :
    (build c base exponent).accValue ρ = (c.eval ρ base) ^ exponent := by
  unfold build
  rw [State.runBits_value]
  simp [start, State.accValue, State.powerValue, Step.eval]

theorem build_size_le (c : Circuit n k) (base : Fin k) (exponent : ℕ) :
    (build c base exponent).size ≤ k + 1 + 2 * exponent.bits.length := by
  exact State.runBits_size_le (start c base) exponent.bits

theorem build_size_ge (c : Circuit n k) (base : Fin k) (exponent : ℕ) :
    k ≤ (build c base exponent).size :=
  (Nat.le_succ k).trans (State.size_le_runBits (start c base) exponent.bits)

theorem build_preserves (c : Circuit n k) (base : Fin k) (exponent : ℕ)
    (i : Fin k) (ρ : Fin n → ℝ) :
    (build c base exponent).circuit.eval ρ
      (Fin.castLE (build_size_ge c base exponent) i) = c.eval ρ i := by
  have h := State.runBits_preserves (start c base) exponent.bits i.castSucc ρ
  have hi : Fin.castLE ((start c base).size_le_runBits exponent.bits) i.castSucc =
      Fin.castLE (build_size_ge c base exponent) i := by
    apply Fin.ext
    rfl
  rw [hi] at h
  simpa [build, start] using h

/-- The gate equations force the computed power at its emitted output index. -/
theorem formula_forces_power (c : Circuit n k) (base : Fin k) (exponent : ℕ)
    {m : ℕ} (inputs : Fin n → Fin m)
    (outputs : Fin (build c base exponent).size → Fin m) (η : Fin m → ℝ)
    (h : ((build c base exponent).circuit.formula inputs outputs).eval η) :
    η (outputs (build c base exponent).accumulator) =
      (c.eval (fun i => η (inputs i)) base) ^ exponent := by
  have hv := (build c base exponent).circuit.formula_forces_values inputs outputs η h
  have ha := congrFun hv (build c base exponent).accumulator
  exact ha.trans (build_value c base exponent (fun i => η (inputs i)))

end JointThermoComplexity.Complexity.BinaryPower

#print axioms JointThermoComplexity.Complexity.BinaryPower.build_value
#print axioms JointThermoComplexity.Complexity.BinaryPower.build_size_le
#print axioms JointThermoComplexity.Complexity.BinaryPower.build_preserves
#print axioms JointThermoComplexity.Complexity.BinaryPower.formula_forces_power
