module
public import proofs.JointThermoComplexity.Complexity.DenseRecordFrame

set_option autoImplicit false
@[expose] public section

/-! Composition at returned row boundaries yields the existing reaction codec. -/

namespace JointThermoComplexity.Complexity.DenseRecordCore
open _root_.Complexity _root_.Complexity.TM
open DenseComplexOriginal DenseRecordFrame RationalBranchData
variable {e N : ℕ}

def complexWord (right product : Bool) (L Rdata : Data (Fin e) N) (i : Fin (N + 2)) : List Bool :=
  FiniteCodec.functionCode FiniteCodec.natural (complex right product L Rdata i)
def recordWord (right : Bool) (L Rdata : Data (Fin e) N) (i : Fin (N + 2)) : List Bool :=
  (DataCodec.reaction (RationalLiteralNetwork.speciesCount e N N)).code (RationalLiteralNetwork.reaction L Rdata (index right N i))

def ReactEmits (react : TM 64) (right : Bool) (L Rdata : Data (Fin e) N) (i : Fin (N + 2))
    (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n A : ℕ) : Prop :=
  ∀ before input emitted R, DenseComplexPorts.Stable false R →
    react.HoareTime (DenseComplexFrame.Pre false m hm values n N (vertex false i).val before input emitted R)
      (DenseComplexFrame.Pre false m hm values n N (vertex false i).val before input
        (emitted ++ complexWord right false L Rdata i) R) A
def ProductEmits (product : TM 64) (right : Bool) (L Rdata : Data (Fin e) N) (i : Fin (N + 2))
    (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n P : ℕ) : Prop :=
  ∀ before input emitted R, DenseComplexPorts.Stable true R →
    product.HoareTime (DenseComplexFrame.Pre true m hm values n N (vertex true i).val before input emitted
      (DenseProductBranch.FlagFrame i R))
      (DenseComplexFrame.Pre true m hm values n N (vertex true i).val before input
        (emitted ++ complexWord right true L Rdata i) (DenseProductBranch.FlagFrame i R)) P

def machine (react product factor : TM 64) : TM 64 := seqTM (seqTM react product) factor

theorem hoareTime (react product factor : TM 64) (right : Bool) (L Rdata : Data (Fin e) N) (i : Fin (N + 2))
    (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n A P F : ℕ)
    (ha : ReactEmits react right L Rdata i m hm values n A)
    (hp : ProductEmits product right L Rdata i m hm values n P)
    (R : (Fin 64 → Tape) → Prop) (hRa : DenseComplexPorts.Stable false R) (hRp : DenseComplexPorts.Stable true R)
    (hf : ∀ before input emitted, factor.HoareTime (Pre m hm values n N i before input emitted R)
      (Pre m hm values n N i before input (emitted ++ DenseFactorCode.factor right L Rdata i) R) F)
    (before input emitted : List Bool) :
    (machine react product factor).HoareTime (Pre m hm values n N i before input emitted R)
      (Pre m hm values n N i before input (emitted ++ recordWord right L Rdata i) R) (A + P + F + 2) := by
  have h1 := (ha before input emitted (ReactR i R) (react_stable i R hRa)).consequence
    (fun inp work out h => (react_iff m hm values n N i before input emitted R inp work out).mp h)
    (fun inp work out h => (react_iff m hm values n N i before input
      (emitted ++ complexWord right false L Rdata i) R inp work out).mpr h) le_rfl
  have h2 := (hp before input (emitted ++ complexWord right false L Rdata i) (ProductR i R)
    (product_stable i R hRp)).consequence
    (fun inp work out h => (product_iff m hm values n N i before input
      (emitted ++ complexWord right false L Rdata i) R inp work out).mp h)
    (fun inp work out h => (product_iff m hm values n N i before input
      ((emitted ++ complexWord right false L Rdata i) ++ complexWord right true L Rdata i) R inp work out).mpr h) le_rfl
  have h12 := seqTM_hoareTime _ _ h1 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) h2
  have hh := seqTM_hoareTime _ _ h12 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) (hf before input ((emitted ++ complexWord right false L Rdata i) ++ complexWord right true L Rdata i))
  apply hh.consequence (fun _ _ _ h => h)
  · intro inp work out h
    change Pre m hm values n N i before input
      (emitted ++ (DataCodec.reaction (RationalLiteralNetwork.speciesCount e N N)).code
        (RationalLiteralNetwork.reaction L Rdata (index right N i))) R inp work out
    rw [DenseFactorCode.record_code]
    simpa only [complexWord, List.append_assoc] using h
  · omega

end JointThermoComplexity.Complexity.DenseRecordCore

#print axioms JointThermoComplexity.Complexity.DenseRecordCore.hoareTime
