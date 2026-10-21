module
public import proofs.JointThermoComplexity.Complexity.MonomialUnit
public import proofs.JointThermoComplexity.Complexity.UnaryReset

set_option autoImplicit false
@[expose] public section

/-! Initialize the unit monomial and reset the species cursor for each exponent array. -/

namespace JointThermoComplexity.Complexity.MonomialStart
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady RealCircuit CircuitSerialization PowerAddressCircuit

def machine (m : ℕ) : TM (m + 14) := seqTM (MonomialUnit.machine m) (clearWorkTM (species m))

def timeBound (L : ℕ) : ℕ := 32 * L ^ 2 + 86 * L + 60

theorem hoareTime {n k : ℕ} (m L offset arity old idx : ℕ) (ha : arity ≤ 4 * L)
    (hold : old ≤ 4 * L) (hidx : idx ≤ L) (c : Circuit n k) (inputs : Fin n → Fin arity)
    (h : offset + (k + 1) ≤ arity) (before input initial : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ previous m → j ≠ species m →
      work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input
        (initial ++ equationStream c inputs (index offset k arity (by omega))) inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 1))) ∧
        IsReg (offset + k) (work (next (m + 1))) ∧ IsReg old (work (previous m)) ∧
        Temps m L work ∧ IsReg idx (work (species m)) ∧ R work)
      (fun inp work out => Cursor before input
        (initial ++ equationStream (MonomialCircuit.start c).circuit inputs (index offset _ arity h)) inp work out ∧
        Ready m L offset (MonomialCircuit.start c) 0 R work) (timeBound L) := by
  have hu := MonomialUnit.hoareTime m L offset arity old idx ha hold c inputs h before input initial R
    (fun work work' hw hr => hR work work' (fun j hn hp _ => hw j hn hp) hr)
  have hfixed := fixed_species m L offset (MonomialCircuit.start c) R
    (fun work work' hw hr => hR work work' (fun j _ _ hj => hw j hj) hr)
  have hr := UnaryReset.hoareTime (species m) idx before input
    (initial ++ equationStream (MonomialCircuit.start c).circuit inputs (index offset _ arity h))
    (Fixed m L offset (MonomialCircuit.start c) R) hfixed
  have hseq := seqTM_hoareTime (MonomialUnit.machine m) (clearWorkTM (species m)) hu (by
    rintro inp work out ⟨hc, hs, hi, hf⟩
    obtain ⟨hip, hw, ho⟩ := hc.phase
    rw [hip, hw, ho]
    exact ⟨hc, hs, hi, hf⟩) hr
  exact hseq.consequence (fun _ _ _ hp => hp) (fun _ _ _ hp => hp) (by unfold timeBound; omega)

end JointThermoComplexity.Complexity.MonomialStart

#print axioms JointThermoComplexity.Complexity.MonomialStart.hoareTime
