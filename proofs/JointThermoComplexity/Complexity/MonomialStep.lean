module
public import proofs.JointThermoComplexity.Complexity.MonomialAdvanceReady
public import proofs.JointThermoComplexity.Complexity.UnarySuccessor

set_option autoImplicit false
@[expose] public section

/-! Each loop iteration computes the next monomial factor and advances its species address. -/

namespace JointThermoComplexity.Complexity.MonomialStep
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady CircuitSerialization PowerAddressCircuit

def machine (m : ℕ) : TM (m + 14) :=
  seqTM (MonomialAdvance.machine m) (UnarySuccessor.machine (species m))

def timeBound (L : ℕ) : ℕ := 192 * L ^ 3 + 552 * L ^ 2 + 580 * L + 222

theorem hoareTime {n : ℕ} (m L offset arity idx : ℕ) (ha : arity ≤ 4 * L) (hi : idx ≤ L)
    (s : MonomialCircuit.State n) (item : Fin n × ℕ) (inputs : Fin n → Fin arity)
    (h : offset + (s.advance item).size ≤ arity) (hlen : item.2.bits.length ≤ L) (hidx : (inputs item.1).val = idx)
    (before tail initial : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ accumulator (m + 1) →
      j ≠ power (m + 1) → j ≠ PowerBitState.flag (m + 1) → j ≠ previous m → j ≠ species m →
      work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode item.2 ++ tail)
        (initial ++ equationStream s.circuit inputs (index offset _ arity (by have hs := s.advance_size_ge item; omega))) inp work out ∧
        Ready m L offset s idx R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode item.2) tail
        (initial ++ equationStream (s.advance item).circuit inputs (index offset _ arity h)) inp work out ∧
        Ready m L offset (s.advance item) (idx + 1) R work) (timeBound L) := by
  have hstep := MonomialAdvanceReady.hoareTime m L offset arity idx ha s item inputs h hlen hidx
    before tail initial R (fun work work' hw hr => hR work work' (fun j hn ha hp hf ho _ => hw j hn ha hp hf ho) hr)
  have hfixed := fixed_species m L offset (s.advance item) R
    (fun work work' hw hr => hR work work' (fun j _ _ _ _ _ hj => hw j hj) hr)
  have hsucc := UnarySuccessor.hoareTime (species m) idx (before ++ BitCodec.naturalCode item.2) tail
    (initial ++ equationStream (s.advance item).circuit inputs (index offset _ arity h))
    (Fixed m L offset (s.advance item) R) hfixed
  have hseq := seqTM_hoareTime (MonomialAdvance.machine m) (UnarySuccessor.machine (species m)) hstep (by
    rintro inp work out ⟨hc, hs, hi, hf⟩
    obtain ⟨hip, hw, ho⟩ := hc.phase
    rw [hip, hw, ho]
    exact ⟨hc, hs, hi, hf⟩) hsucc
  exact hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
    (by unfold timeBound MonomialAdvance.timeBound; omega)

end JointThermoComplexity.Complexity.MonomialStep

#print axioms JointThermoComplexity.Complexity.MonomialStep.hoareTime
