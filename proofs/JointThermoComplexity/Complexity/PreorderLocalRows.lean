module
public import proofs.JointThermoComplexity.Complexity.SmallIntegerLookup
public import proofs.JointThermoComplexity.Complexity.PreorderLookahead
public import proofs.JointThermoComplexity.Complexity.PreorderSourceEquations

set_option autoImplicit false
@[expose] public section

/-! Local equation rows carry binary variable words, avoiding numerical expansion of source index fields. -/

namespace JointThermoComplexity.Complexity.PreorderLocalRows
open RealSyntax SparseInteger SourceCoordinateEnumeration NumberedFormulaEquations PreorderLookahead
variable {n : ℕ}

abbrev Rows := List (Poly (List Bool))
def words (ps : List (Poly ℕ)) : Rows := ps.map (relabel BitCodec.naturalCode)
def variableWord (i : ℕ) : Poly (List Bool) := atom (BitCodec.naturalCode i)

def termLocal : Term n → ℕ → List (Poly ℕ)
  | .int z, offset => [sub (atom offset) (constant z)]
  | .var i, offset => [sub (atom offset) (atom i.val)]
  | .add s _, offset => [sub (atom offset) (add (atom (offset + 1)) (atom (offset + 1 + s.size)))]
  | .mul s _, offset => [sub (atom offset) (product (atom (offset + 1)) (atom (offset + 1 + s.size)))]
  | .neg _, offset => [add (atom offset) (atom (offset + 1))]

def formulaLocal : Formula n → ℕ → List (Poly ℕ)
  | .truth, offset => [product (atom offset) (sub (atom offset) (constant 1))]
  | .falsity, offset => [atom offset]
  | .eq s _, offset => SparseCircuit.equalityActivation.map (relabel (equalityPorts offset (offset + 1) (offset + 1 + s.size)))
  | .lt s t, offset => SparseCircuit.strictSign.map (relabel (signPorts offset (offset + 1) (offset + 1 + s.size)
      (offset + 1 + s.size + t.size)))
  | .conj p _, offset => [product (atom offset) (sub (atom offset) (constant 1)),
      sub (atom (offset + 1)) (atom offset), sub (atom (offset + 1 + formulaCount p)) (atom offset)]
  | .disj p _, offset => [product (atom offset) (sub (atom offset) (constant 1)),
      sub (add (atom (offset + 1)) (atom (offset + 1 + formulaCount p))) (atom offset)]

def termRows (L offset : ℕ) (input : List Bool) : Rows :=
  if SourceTags.accepted input then
    let rest := input.drop 3
    match SourceTermToken.classify (SourceTermToken.tagBits input) with
    | .integer => [sub (variableWord offset) (constant (SmallIntegerLookup.value rest))]
    | .variable => [sub (variableWord offset) (atom (PayloadControl.copied .empty rest))]
    | .add => [sub (variableWord offset) (add (variableWord (offset + 1)) (variableWord (offset + 1 + termSize L rest)))]
    | .mul => [sub (variableWord offset) (product (variableWord (offset + 1)) (variableWord (offset + 1 + termSize L rest)))]
    | .neg => [add (variableWord offset) (variableWord (offset + 1))]
    | .invalid => []
  else []

def formulaRows (L offset : ℕ) (input : List Bool) : Rows :=
  if SourceTags.accepted input then
    let rest := input.drop 3
    match SourceFormulaScan.classify (SourceTermToken.tagBits input) with
    | .truth => [product (variableWord offset) (sub (variableWord offset) (constant 1))]
    | .falsity => [variableWord offset]
    | .eq => words (SparseCircuit.equalityActivation.map
        (relabel (equalityPorts offset (offset + 1) (offset + 1 + termSize L rest))))
    | .lt => words (SparseCircuit.strictSign.map (relabel (signPorts offset (offset + 1) (offset + 1 + termSize L rest)
        (offset + 1 + termSize L rest + termSize L (termRest L rest)))))
    | .conj => [product (variableWord offset) (sub (variableWord offset) (constant 1)),
        sub (variableWord (offset + 1)) (variableWord offset), sub (variableWord (offset + 1 + formulaSize L rest)) (variableWord offset)]
    | .disj => [product (variableWord offset) (sub (variableWord offset) (constant 1)),
        sub (add (variableWord (offset + 1)) (variableWord (offset + 1 + formulaSize L rest))) (variableWord offset)]
    | .invalid => []
  else []

attribute [local simp] NumberedTermEquations.relabel_atom NumberedTermEquations.relabel_constant
  NumberedTermEquations.relabel_sub NumberedTermEquations.relabel_add NumberedTermEquations.relabel_product

theorem term_code (L offset : ℕ) (t : Term n) (suffix : List Bool) (hlen : (t.code ++ suffix).length ≤ L)
    (hh : t.literalHeight ≤ 2) : termRows L offset (t.code ++ suffix) = words (termLocal t offset) := by
  cases t with
  | int z =>
    have hz : z.natAbs ≤ 2 := hh
    simp [termRows, termLocal, words, variableWord, Term.code, SourceTags.accepted, SourceTermToken.classify,
      SourceTermToken.tagBits, SourceBitRead.value, SmallIntegerLookup.value_code z hz]
  | var i =>
    simp [termRows, termLocal, words, variableWord, Term.code, SourceTags.accepted, SourceTermToken.classify,
      SourceTermToken.tagBits, SourceBitRead.value, NumericCursor.natural_copied_code]
  | add s t | mul s t =>
    have hb : (s.code ++ t.code ++ suffix).length ≤ L := by
      simp only [Term.code, List.length_append, List.length_cons, List.length_nil] at hlen ⊢
      omega
    have hl := (PreorderLookahead.term_code L s (t.code ++ suffix) (by simpa only [List.append_assoc] using hb)).1
    simp [termRows, termLocal, words, variableWord, Term.code, SourceTags.accepted, SourceTermToken.classify,
      SourceTermToken.tagBits, SourceBitRead.value, List.append_assoc, hl]
  | neg s =>
    simp [termRows, termLocal, words, variableWord, Term.code, SourceTags.accepted, SourceTermToken.classify,
      SourceTermToken.tagBits, SourceBitRead.value]

theorem formula_code (L offset : ℕ) (p : Formula n) (suffix : List Bool) (hlen : (p.code ++ suffix).length ≤ L) :
    formulaRows L offset (p.code ++ suffix) = words (formulaLocal p offset) := by
  cases p with
  | truth | falsity =>
    simp [formulaRows, formulaLocal, words, variableWord, Formula.code, SourceTags.accepted,
      SourceFormulaScan.classify, SourceTermToken.tagBits, SourceBitRead.value]
  | eq s t =>
    have hb : (s.code ++ t.code ++ suffix).length ≤ L := by
      simp only [Formula.code, List.length_append, List.length_cons, List.length_nil] at hlen ⊢
      omega
    have hl := (PreorderLookahead.term_code L s (t.code ++ suffix) (by simpa only [List.append_assoc] using hb)).1
    simp [formulaRows, formulaLocal, Formula.code, SourceTags.accepted, SourceFormulaScan.classify,
      SourceTermToken.tagBits, SourceBitRead.value, List.append_assoc, hl]
  | lt s t =>
    have hb : (s.code ++ t.code ++ suffix).length ≤ L := by
      simp only [Formula.code, List.length_append, List.length_cons, List.length_nil] at hlen ⊢
      omega
    have hp := PreorderLookahead.pair_code L s t suffix hb
    simp only [List.append_assoc] at hp
    simp [formulaRows, formulaLocal, Formula.code, SourceTags.accepted, SourceFormulaScan.classify,
      SourceTermToken.tagBits, SourceBitRead.value, List.append_assoc, hp.1, hp.2]
  | conj p q | disj p q =>
    have hb : (p.code ++ q.code ++ suffix).length ≤ L := by
      simp only [Formula.code, List.length_append, List.length_cons, List.length_nil] at hlen ⊢
      omega
    have hl := PreorderLookahead.formula_code L p (q.code ++ suffix) (by simpa only [List.append_assoc] using hb)
    simp [formulaRows, formulaLocal, words, variableWord, Formula.code, SourceTags.accepted, SourceFormulaScan.classify,
      SourceTermToken.tagBits, SourceBitRead.value, List.append_assoc, hl]

end JointThermoComplexity.Complexity.PreorderLocalRows

#print axioms JointThermoComplexity.Complexity.PreorderLocalRows.term_code
#print axioms JointThermoComplexity.Complexity.PreorderLocalRows.formula_code
