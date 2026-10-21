module
public import proofs.JointThermoComplexity.Complexity.ReactionCircuit

set_option autoImplicit false
@[expose] public section

/-!
# One circuit for a literal network

Reaction identities are retained in input order, even when their literal data
coincide. All reaction circuits read the same activity coordinates. Appending a
reaction preserves previous outputs. The bounds count gates only; machine cost
and encoded-size theorems are separate obligations.
-/

namespace JointThermoComplexity.Complexity.NetworkCircuit
open RealCircuit ReactionCircuit

variable {n k r : ℕ}

def numeratorValue (reaction : Reaction n) (ρ : Fin n → ℝ) : ℝ :=
  reaction.difference ρ * reaction.numerator

def gateCost : List (Reaction n) → ℕ
  | [] => 0
  | reaction :: rest => reaction.gateCost + gateCost rest

structure State (n : ℕ) where
  size : ℕ
  circuit : Circuit n size
  outputs : List (Fin size)

def State.values (s : State n) (ρ : Fin n → ℝ) : List ℝ :=
  s.outputs.map (s.circuit.eval ρ)

def State.advance (s : State n) (reaction : Reaction n) : State n :=
  let next := ReactionCircuit.build s.circuit reaction
  ⟨next.size, next.circuit,
    s.outputs.map (Fin.castLE (ReactionCircuit.build_size_ge s.circuit reaction)) ++
      [next.output]⟩

theorem State.advance_values (s : State n) (reaction : Reaction n) (ρ : Fin n → ℝ) :
    (s.advance reaction).values ρ = s.values ρ ++ [numeratorValue reaction ρ] := by
  simp only [State.advance, State.values, List.map_append, List.map_map,
    List.map_cons, List.map_nil, Function.comp_def, ReactionCircuit.build_preserves]
  rw [show (ReactionCircuit.build s.circuit reaction).circuit.eval ρ
    (ReactionCircuit.build s.circuit reaction).output = numeratorValue reaction ρ from
      ReactionCircuit.build_value s.circuit reaction ρ]

theorem State.advance_length (s : State n) (reaction : Reaction n) :
    (s.advance reaction).outputs.length = s.outputs.length + 1 := by
  simp [State.advance]

theorem State.advance_size_le (s : State n) (reaction : Reaction n) :
    (s.advance reaction).size ≤ s.size + reaction.gateCost :=
  ReactionCircuit.build_size_le s.circuit reaction

def State.run (s : State n) : List (Reaction n) → State n
  | [] => s
  | reaction :: rest => (s.advance reaction).run rest

theorem State.run_values (s : State n) (reactions : List (Reaction n)) (ρ : Fin n → ℝ) :
    (s.run reactions).values ρ = s.values ρ ++ reactions.map (fun q => numeratorValue q ρ) := by
  induction reactions generalizing s with
  | nil => simp [State.run]
  | cons reaction rest ih =>
    rw [State.run, ih, State.advance_values]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]

theorem State.run_length (s : State n) (reactions : List (Reaction n)) :
    (s.run reactions).outputs.length = s.outputs.length + reactions.length := by
  induction reactions generalizing s with
  | nil => simp [State.run]
  | cons reaction rest ih =>
    rw [State.run, ih, State.advance_length]
    simp [Nat.add_assoc, Nat.add_comm]

theorem State.run_size_le (s : State n) (reactions : List (Reaction n)) :
    (s.run reactions).size ≤ s.size + gateCost reactions := by
  induction reactions generalizing s with
  | nil => simp [State.run, gateCost]
  | cons reaction rest ih =>
    have hn := s.advance_size_le reaction
    have ht := ih (s.advance reaction)
    simp only [State.run, gateCost]
    omega

def build (reactions : List (Reaction n)) : State n :=
  (⟨0, .nil, []⟩ : State n).run reactions

theorem build_values (reactions : List (Reaction n)) (ρ : Fin n → ℝ) :
    (build reactions).values ρ = reactions.map (fun q => numeratorValue q ρ) := by
  simpa [build, State.values] using State.run_values (⟨0, .nil, []⟩ : State n) reactions ρ

theorem build_length (reactions : List (Reaction n)) :
    (build reactions).outputs.length = reactions.length := by
  simpa [build] using State.run_length (⟨0, .nil, []⟩ : State n) reactions

theorem build_size_le (reactions : List (Reaction n)) :
    (build reactions).size ≤ gateCost reactions := by
  simpa [build] using State.run_size_le (⟨0, .nil, []⟩ : State n) reactions

def dense (reactions : Fin r → Reaction n) : State n := build (List.ofFn reactions)

def output (reactions : Fin r → Reaction n) (i : Fin r) : Fin (dense reactions).size :=
  (dense reactions).outputs[i.val]'(by rw [dense, build_length, List.length_ofFn]; exact i.isLt)

theorem output_value (reactions : Fin r → Reaction n) (i : Fin r) (ρ : Fin n → ℝ) :
    (dense reactions).circuit.eval ρ (output reactions i) = numeratorValue (reactions i) ρ := by
  have h := build_values (List.ofFn reactions) ρ
  have hi : i.val < (dense reactions).outputs.length := by
    rw [dense, build_length, List.length_ofFn]
    exact i.isLt
  have hv := congrArg (fun xs : List ℝ => xs[i.val]?) h
  change i.val < (build (List.ofFn reactions)).outputs.length at hi
  simp only [State.values, List.map_ofFn] at hv
  rw [List.getElem?_map, List.getElem?_eq_getElem hi] at hv
  simpa [List.getElem?_ofFn, i.isLt, output, dense] using hv

end JointThermoComplexity.Complexity.NetworkCircuit

#print axioms JointThermoComplexity.Complexity.NetworkCircuit.build_values
#print axioms JointThermoComplexity.Complexity.NetworkCircuit.build_size_le
#print axioms JointThermoComplexity.Complexity.NetworkCircuit.output_value
