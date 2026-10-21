module
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.Int.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

/-!
Joint thermodynamic compatibility of two supplied autocatalytic cores.

The boxed and unboxed promise problems use one shared positive activity vector
and fixed positive rational reaction factors. The promise requires exactly two
valid signed PACs, including minimality under both species and reaction deletion.
Boxed internal and external activities lie in [1/4,1/2] and [1/2,1]; maximum side
molecularities are six and eight. Distinct indexed reactions may coincide.

The computational model below is the ordinary finite-state binary multitape
Turing model: one read-only input tape, finitely many work tapes, and an output
tape. Polynomial time bounds count transitions on every input bit string.
The existential-real language is defined independently of reaction networks.
-/

/- The Turing definitions are adapted from Samuel Schlesinger's Complexitylib,
commit43d4bb1a30bd93846eab5480bec8a37113586109, copyright2025, Apache-2.0.
The exact source attribution and license accompany the proof development. -/
namespace Complexity

/-- The four read symbols are binary zero/one, blank and the left-end marker. -/
inductive Γ where
  | zero | one | blank | start
  deriving Repr, DecidableEq
/-- A machine may write binary symbols or blank, never a new left-end marker. -/
inductive Γw where
  | zero | one | blank
  deriving Repr, DecidableEq
/-- Embed a writable symbol into the read alphabet. -/
def Γw.toΓ : Γw → Γ
  | .zero => .zero
  | .one => .one
  | .blank => .blank
instance : Coe Γw Γ where coe := Γw.toΓ
/-- Encode a Boolean as the corresponding binary tape symbol. -/
def Γ.ofBool : Bool → Γ
  | false => .zero
  | true => .one
/-- The head may move left, move right, or stay in place. -/
inductive Dir3 where
  | left | right | stay
  deriving Repr, DecidableEq

/-- One-sided infinite tape, with a natural-number head position. -/
structure Tape where
  head : ℕ
  cells : ℕ → Γ
namespace Tape
/-- Read the symbol at the current head position. -/
def read (t : Tape) : Γ := t.cells t.head
/-- Update the current cell, with writes to cell zero leaving the tape unchanged. -/
def write (t : Tape) (s : Γ) : Tape :=
  if t.head = 0 then t
  else { t with cells := Function.update t.cells t.head s }
/-- Move the head; a left move from zero remains at zero. -/
def move (t : Tape) (d : Dir3) : Tape :=
  match d with
  | .left => { t with head := t.head - 1 }
  | .right => { t with head := t.head + 1 }
  | .stay => t
/-- Write a symbol and then move the head. -/
abbrev writeAndMove (t : Tape) (s : Γ) (d : Dir3) : Tape :=
  (t.write s).move d
/-- Output occupies cells1 through its length, followed by a blank cell. -/
def HasOutput (t : Tape) (y : List Bool) : Prop :=
  (∀ (i : ℕ) (h : i < y.length), t.cells (i + 1) = Γ.ofBool (y[i]'h)) ∧
    t.cells (y.length + 1) = Γ.blank
end Tape
/-- Initialize an input string after the left-end marker, with blanks thereafter and head at
zero. -/
def Tape.init (contents : List Γ) : Tape where
  head := 0
  cells := fun i => if i = 0 then Γ.start else (contents[i - 1]?).getD Γ.blank

/-- Named input, work and output tapes prevent writing the input tape. -/
structure Cfg (n : ℕ) (Q : Type) where
  state : Q
  input : Tape
  work : Fin n → Tape
  output : Tape
namespace Cfg
/-- Initialize the input tape and empty work/output tapes in the designated start state. -/
abbrev init (qstart : Q) (x : List Bool) : Cfg n Q :=
  { state := qstart, input := Tape.init (x.map Γ.ofBool),
    work := fun _ => Tape.init [], output := Tape.init [] }
/-- A configuration is halted exactly when its state is the designated halt state. -/
abbrev isHalted (qhalt : Q) (c : Cfg n Q) : Prop := c.state = qhalt
end Cfg

/-- A deterministic finite-state machine; start markers force a right move. -/
structure TM (n : ℕ) where
  Q : Type
  [decEq : DecidableEq Q]
  [finQ : Fintype Q]
  qstart : Q
  qhalt : Q
  δ : Q → Γ → (Fin n → Γ) → Γ →
    Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3
  δ_right_of_start : ∀ (q : Q) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ),
    let (_, _, _, inDir, workDirs, outDir) := δ q iHead wHeads oHead
    (iHead = Γ.start → inDir = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
    (oHead = Γ.start → outDir = Dir3.right)
attribute [instance] TM.decEq TM.finQ
namespace TM
variable {n : ℕ}
/-- One deterministic transition; a halted configuration has no successor. -/
def step (tm : TM n) (c : Cfg n tm.Q) : Option (Cfg n tm.Q) :=
  if c.state = tm.qhalt then none
  else
    let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
      tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read
    some
      { state := q'
        input := c.input.move inDir
        work := fun i => (c.work i).writeAndMove (workWrites i) (workDirs i)
        output := c.output.writeAndMove outWrite outDir }
/-- The initial configuration of the given machine on a binary input. -/
abbrev initCfg (tm : TM n) (x : List Bool) : Cfg n tm.Q := Cfg.init tm.qstart x
/-- The configuration state equals this machine’s halt state. -/
abbrev halted (tm : TM n) (c : Cfg n tm.Q) : Prop := Cfg.isHalted tm.qhalt c
/-- Exact transition count, including the zero-step execution. -/
inductive reachesIn (tm : TM n) : ℕ → Cfg n tm.Q → Cfg n tm.Q → Prop where
  | zero : reachesIn tm 0 c c
  | step : tm.step c = some c'' → reachesIn tm t c'' c' → reachesIn tm (t + 1) c c'
/-- Total function computation, halted within T of the input length. -/
def ComputesInTime (tm : TM n) (f : List Bool → List Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x, ∃ c' t, t ≤ T x.length ∧ tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧
    c'.output.HasOutput (f x)
end TM

open Filter Asymptotics
/-- Ordinary asymptotic domination on natural-valued time bounds. -/
def BigO (f g : ℕ → ℕ) : Prop :=
  (fun n => (f n : ℝ)) =O[atTop] (fun n => (g n : ℝ))
/-- Binary functions computed by an actual multitape TM in polynomial time. -/
def FP : Set (List Bool → List Bool) :=
  {f | ∃ (d k : ℕ) (tm : TM k) (T : ℕ → ℕ),
    tm.ComputesInTime f T ∧ BigO T (· ^ d)}
end Complexity

/-! Self-delimiting binary integers: paired payload bits, canonical little-endian
Nat.bits, and signed magnitude with negative zero rejected. -/
namespace JointThermoComplexity.Complexity.BitCodec

/-- Prefix each payload bit with true and terminate the payload with false. -/
def encodeBits : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: encodeBits bs

/-- Decode the paired-bit payload and return its unused suffix; reject a truncated pair. -/
def parseBits : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: rest => some ([], rest)
  | [true] => none
  | true :: b :: rest => do
      let (payload, suffix) ← parseBits rest
      pure (b :: payload, suffix)

/-- Read a little-endian payload as a natural number. -/
def readBits (payload : List Bool) : ℕ := payload.foldr Nat.bit 0

/-- Encode the canonical little-endian binary digits of a natural number. -/
def naturalCode (n : ℕ) : List Bool := encodeBits n.bits

/-- Decode a natural number, rejecting payloads that are not its canonical binary digits. -/
def parseNatural (input : List Bool) : Option (ℕ × List Bool) := do
  let (payload, suffix) ← parseBits input
  let n := readBits payload
  if payload = n.bits then pure (n, suffix) else none

/-- Encode an integer by its sign and natural magnitude, with a unique code for zero. -/
def integerCode : ℤ → List Bool
  | .ofNat n => false :: naturalCode n
  | .negSucc n => true :: naturalCode (n + 1)

/-- Decode signed magnitude and the unused suffix; reject negative zero. -/
def parseInteger : List Bool → Option (ℤ × List Bool)
  | [] => none
  | false :: rest => do
      let (n, suffix) ← parseNatural rest
      pure (Int.ofNat n, suffix)
  | true :: rest => do
      let (n, suffix) ← parseNatural rest
      match n with
      | 0 => none
      | k + 1 => pure (Int.negSucc k, suffix)

end JointThermoComplexity.Complexity.BitCodec

/-! Existential-real syntax, its real semantics and its complete bit decoder.
All declared variables are existential; malformed or trailing data are rejected. -/
namespace JointThermoComplexity.Complexity.RealSyntax
open BitCodec
variable {n : ℕ}

/-- Real arithmetic terms with integer constants, finite variable indices, addition,
multiplication and negation. -/
inductive Term (n : ℕ) where
  | int : ℤ → Term n
  | var : Fin n → Term n
  | add : Term n → Term n → Term n
  | mul : Term n → Term n → Term n
  | neg : Term n → Term n
  deriving DecidableEq

/-- Quantifier-free real formulas using equality, strict inequality, conjunction and disjunction. -/
inductive Formula (n : ℕ) where
  | truth : Formula n
  | falsity : Formula n
  | eq : Term n → Term n → Formula n
  | lt : Term n → Term n → Formula n
  | conj : Formula n → Formula n → Formula n
  | disj : Formula n → Formula n → Formula n
  deriving DecidableEq

/-- Evaluate an arithmetic term at one assignment of all declared real variables. -/
def Term.eval (ρ : Fin n → ℝ) : Term n → ℝ
  | .int z => z
  | .var i => ρ i
  | .add s t => s.eval ρ + t.eval ρ
  | .mul s t => s.eval ρ * t.eval ρ
  | .neg t => -t.eval ρ

/-- Interpret a formula at one assignment using the ordinary real operations and relations. -/
def Formula.eval (ρ : Fin n → ℝ) : Formula n → Prop
  | .truth => True
  | .falsity => False
  | .eq s t => s.eval ρ = t.eval ρ
  | .lt s t => s.eval ρ < t.eval ρ
  | .conj p q => p.eval ρ ∧ q.eval ρ
  | .disj p q => p.eval ρ ∨ q.eval ρ

/-- Parse a tagged arithmetic term with bounded recursion fuel and range-checked variable
indices. -/
def parseTerm (n : ℕ) : ℕ → List Bool → Option (Term n × List Bool)
  | 0, _ => none
  | k + 1, input =>
    match input with
    | false :: false :: false :: rest => do
        let (z, tail) ← parseInteger rest
        pure (.int z, tail)
    | false :: false :: true :: rest => do
        let (i, tail) ← parseNatural rest
        if h : i < n then pure (.var ⟨i, h⟩, tail) else none
    | false :: true :: false :: rest => do
        let (s, rest) ← parseTerm n k rest
        let (t, tail) ← parseTerm n k rest
        pure (.add s t, tail)
    | false :: true :: true :: rest => do
        let (s, rest) ← parseTerm n k rest
        let (t, tail) ← parseTerm n k rest
        pure (.mul s t, tail)
    | true :: false :: false :: rest => do
        let (t, tail) ← parseTerm n k rest
        pure (.neg t, tail)
    | _ => none

/-- Parse a tagged formula with bounded recursion fuel, returning the unused suffix. -/
def parseFormula (n : ℕ) : ℕ → List Bool → Option (Formula n × List Bool)
  | 0, _ => none
  | k + 1, input =>
    match input with
    | false :: false :: false :: rest => some (.truth, rest)
    | false :: false :: true :: rest => some (.falsity, rest)
    | false :: true :: false :: rest => do
        let (s, rest) ← parseTerm n k rest
        let (t, tail) ← parseTerm n k rest
        pure (.eq s t, tail)
    | false :: true :: true :: rest => do
        let (s, rest) ← parseTerm n k rest
        let (t, tail) ← parseTerm n k rest
        pure (.lt s t, tail)
    | true :: false :: false :: rest => do
        let (p, rest) ← parseFormula n k rest
        let (q, tail) ← parseFormula n k rest
        pure (.conj p q, tail)
    | true :: false :: true :: rest => do
        let (p, rest) ← parseFormula n k rest
        let (q, tail) ← parseFormula n k rest
        pure (.disj p q, tail)
    | _ => none

/-- Declare n variables by n true bits followed by a false terminator. -/
def binderCode (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Read the unary variable-count header and return the remaining input. -/
def parseBinders : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, suffix) ← parseBinders rest
      pure (n + 1, suffix)

/-- An explicitly declared finite number of existential real variables and a formula over them. -/
structure Sentence where
  arity : ℕ
  formula : Formula arity
  deriving DecidableEq

/-- Some assignment of all declared real variables makes the formula true. -/
def Sentence.Satisfiable (s : Sentence) : Prop :=
  ∃ ρ : Fin s.arity → ℝ, s.formula.eval ρ

/-- Decode the declared variables and formula using input-length fuel; reject trailing data. -/
def decodeSentence (input : List Bool) : Option Sentence := do
  let (n, rest) ← parseBinders input
  let (p, suffix) ← parseFormula n rest.length rest
  if suffix = [] then pure ⟨n, p⟩ else none

/-- The bit language of well-formed existential-real sentences that have a satisfying assignment. -/
def ETR : Set (List Bool) :=
  {input | ∃ s, decodeSentence input = some s ∧ s.Satisfiable}

end JointThermoComplexity.Complexity.RealSyntax

/-! Faithful fixed-dimension codecs. Every computational field is explicit.
Only proof-valued roundtrip/soundness and inverse-law fields are admitted here;
the corresponding Solution fields have checked proofs. -/
namespace JointThermoComplexity.Complexity.FiniteCodec
open BitCodec
variable {α β : Type}

/-- A serializer/parser pair with suffix-preserving roundtrip and soundness laws. -/
structure Codec (α : Type) where
  code : α → List Bool
  parse : List Bool → Option (α × List Bool)
  roundtrip : ∀ a suffix, parse (code a ++ suffix) = some (a, suffix)
  sound : ∀ {input a suffix}, parse input = some (a, suffix) → input = code a ++ suffix

/-- The canonical self-delimiting binary natural-number codec. -/
def natural : Codec ℕ := ⟨naturalCode, parseNatural, by sorry, by sorry⟩
/-- The canonical signed binary integer codec. -/
def integer : Codec ℤ := ⟨integerCode, parseInteger, by sorry, by sorry⟩

/-- A Boolean is one bit. -/
def boolean : Codec Bool where
  code b := [b]
  parse | [] => none | b :: rest => some (b, rest)
  roundtrip := by sorry
  sound := by sorry


/-- A positive natural number uses its natural-number code; parsing rejects zero. -/
def positive : Codec {a : ℕ // 0 < a} where
  code a := naturalCode a.val
  parse input := do
    let (a, rest) ← parseNatural input
    if h : 0 < a then pure (⟨a, h⟩, rest) else none
  roundtrip := by sorry
  sound := by sorry


/-- Serialize two fields consecutively and parse them in that order. -/
def product (A : Codec α) (B : Codec β) : Codec (α × β) where
  code a := A.code a.1 ++ B.code a.2
  parse input := do
    let (a, rest) ← A.parse input
    let (b, suffix) ← B.parse rest
    pure ((a, b), suffix)
  roundtrip := by sorry
  sound := by sorry


/-- A false bit denotes none; true prefixes the code of a present value. -/
def optional (A : Codec α) : Codec (Option α) where
  code | none => [false] | some a => true :: A.code a
  parse
    | [] => none
    | false :: rest => some (none, rest)
    | true :: rest => do
        let (a, suffix) ← A.parse rest
        pure (some a, suffix)
  roundtrip := by sorry
  sound := by sorry


/-- Serialize a finite function in increasing Fin index order. -/
def functionCode (A : Codec α) : {n : ℕ} → (Fin n → α) → List Bool
  | 0, _ => []
  | _ + 1, f => A.code (f 0) ++ functionCode A (fun i => f i.succ)

/-- Read exactly n consecutive values as a function on Fin n. -/
def parseFunction (A : Codec α) : (n : ℕ) → List Bool → Option ((Fin n → α) × List Bool)
  | 0, input => some (Fin.elim0, input)
  | n + 1, input => do
      let (a, rest) ← A.parse input
      let (f, suffix) ← parseFunction A n rest
      pure (Fin.cons a f, suffix)

/-- The fixed-dimension finite-function codec with its serializer and parser laws. -/
def finiteFunction (A : Codec α) (n : ℕ) : Codec (Fin n → α) :=
  ⟨functionCode A, parseFunction A n, by sorry, by sorry⟩
end JointThermoComplexity.Complexity.FiniteCodec

/-! Literal reaction currents and one globally shared positive activity state. -/
namespace JointThermoComplexity.Complexity.ReactionCircuit
open scoped BigOperators

/-- Two literal natural stoichiometric vectors and a fixed positive integer
numerator/denominator. -/
structure Reaction (n : ℕ) where
  reactant : Fin n → ℕ
  product : Fin n → ℕ
  numerator : ℕ
  denominator : ℕ
  numerator_pos : 0 < numerator
  denominator_pos : 0 < denominator

variable {n : ℕ}

/-- Reactant activity monomial minus product activity monomial at the same state. -/
def Reaction.difference (r : Reaction n) (ρ : Fin n → ℝ) : ℝ :=
  (∏ i, ρ i ^ r.reactant i) - ∏ i, ρ i ^ r.product i

/-- The fixed positive rational factor times the difference of activity monomials. -/
noncomputable def Reaction.current (r : Reaction n) (ρ : Fin n → ℝ) : ℝ :=
  (r.numerator : ℝ) / r.denominator * r.difference ρ

end JointThermoComplexity.Complexity.ReactionCircuit

namespace JointThermoComplexity.Complexity.NetworkData
open ReactionCircuit
open scoped BigOperators

/-- A signed integer numerator and a strictly positive natural denominator. -/
structure RationalPoint where
  numerator : ℤ
  denominator : ℕ
  denominator_pos : 0 < denominator

/-- Lower and upper rational endpoints of an activity interval. -/
structure ClosedBox where
  lower : RationalPoint
  upper : RationalPoint

/-- The activity lies between the rational endpoints, expressed without division. -/
def ClosedBox.Contains (box : ClosedBox) (z : ℝ) : Prop :=
  (box.lower.numerator : ℝ) ≤ (box.lower.denominator : ℝ) * z ∧
    (box.upper.denominator : ℝ) * z ≤ (box.upper.numerator : ℝ)

/-- A supplied pair of finite species and reaction index sets. -/
structure Motif (n r : ℕ) where
  species : Finset (Fin n)
  reactions : Finset (Fin r)

/-- Explicit indexed reactions, supplied motifs, chosen reaction directions and optional activity
boxes. -/
structure Network (n r c : ℕ) where
  reactions : Fin r → Reaction n
  motifs : Fin c → Motif n r
  forward : Fin r → Bool
  boxes : Fin n → Option ClosedBox

variable {n r c : ℕ}

/-- Product multiplicity minus reactant multiplicity for the selected species. -/
def stoich (reaction : Reaction n) (s : Fin n) : ℤ :=
  (reaction.product s : ℤ) - reaction.reactant s

/-- Net production of a species using only this motif’s reactions and the given shared currents. -/
def Network.production (Q : Network n r c) (a : Fin c) (s : Fin n)
    (j : Fin r → ℝ) : ℝ :=
  ∑ i, if i ∈ (Q.motifs a).reactions then (stoich (Q.reactions i) s : ℝ) * j i else 0

/-- Strict positivity of a current in the chosen forward or reverse direction. -/
def direction (forward : Bool) (j : ℝ) : Prop := 0 < if forward then j else -j

/-- One positive activity state satisfies its boxes, each used direction and each motif’s strict
production. -/
def Network.Constraints (Q : Network n r c) (z : Fin n → ℝ) (j : Fin r → ℝ) : Prop :=
  (∀ s, 0 < z s) ∧
  (∀ s, match Q.boxes s with | none => True | some box => box.Contains (z s)) ∧
  ∀ a, (∀ i ∈ (Q.motifs a).reactions, direction (Q.forward i) (j i)) ∧
    ∀ s ∈ (Q.motifs a).species, 0 < Q.production a s j

/-- One globally shared positive activity state satisfies all constraints at its literal reaction
currents. -/
def Network.Feasible (Q : Network n r c) : Prop :=
  ∃ z, Q.Constraints z (fun i => (Q.reactions i).current z)

end JointThermoComplexity.Complexity.NetworkData

namespace JointThermoComplexity.Complexity.DataCodec
open FiniteCodec NetworkData ReactionCircuit
variable {α β : Type}

/-- Transport an explicit codec along a data equivalence without changing its encoded fields. -/
def transport (A : Codec α) (e : α ≃ β) : Codec β where
  code b := A.code (e.symm b)
  parse input := do
    let (a, suffix) ← A.parse input
    pure (e a, suffix)
  roundtrip := by sorry
  sound := by sorry


/-- Natural-number factor data with strictly positive value. -/
abbrev PositiveNatural := {a : ℕ // 0 < a}

/-- A rational datum is its signed numerator paired with a positive denominator. -/
def rationalEquiv : (ℤ × PositiveNatural) ≃ RationalPoint where
  toFun v := ⟨v.1, v.2.val, v.2.property⟩
  invFun q := (q.numerator, ⟨q.denominator, q.denominator_pos⟩)
  left_inv := by sorry
  right_inv := by sorry


/-- An interval datum is its ordered pair of rational endpoints. -/
def boxEquiv : (RationalPoint × RationalPoint) ≃ ClosedBox where
  toFun v := ⟨v.1, v.2⟩
  invFun b := (b.lower, b.upper)
  left_inv := by sorry
  right_inv := by sorry


/-- A finite set is its Boolean membership vector on all declared indices. -/
def finsetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun f := Finset.univ.filter (fun i => f i = true)
  invFun s i := decide (i ∈ s)
  left_inv := by sorry
  right_inv := by sorry


/-- A reaction is its two dense complex vectors and positive numerator/denominator pair. -/
def reactionEquiv (n : ℕ) :
    (((Fin n → ℕ) × (Fin n → ℕ)) × (PositiveNatural × PositiveNatural)) ≃ Reaction n where
  toFun v := ⟨v.1.1, v.1.2, v.2.1.val, v.2.2.val, v.2.1.property, v.2.2.property⟩
  invFun r := ((r.reactant, r.product),
    (⟨r.numerator, r.numerator_pos⟩, ⟨r.denominator, r.denominator_pos⟩))
  left_inv := by sorry
  right_inv := by sorry


/-- A motif is its species membership set paired with its reaction membership set. -/
def motifEquiv (n r : ℕ) : (Finset (Fin n) × Finset (Fin r)) ≃ Motif n r where
  toFun v := ⟨v.1, v.2⟩
  invFun a := (a.species, a.reactions)
  left_inv := by sorry
  right_inv := by sorry


/-- Network fields are ordered as reactions, motifs, directions and optional boxes. -/
def networkEquiv (n r c : ℕ) :
    (((Fin r → Reaction n) × (Fin c → Motif n r)) ×
      ((Fin r → Bool) × (Fin n → Option ClosedBox))) ≃ Network n r c where
  toFun v := ⟨v.1.1, v.1.2, v.2.1, v.2.2⟩
  invFun Q := ((Q.reactions, Q.motifs), (Q.forward, Q.boxes))
  left_inv := by sorry
  right_inv := by sorry


/-- Serialize a signed numerator followed by a positive denominator. -/
def rational : Codec RationalPoint :=
  transport (product integer positive) rationalEquiv

/-- Serialize the lower endpoint followed by the upper endpoint. -/
def box : Codec ClosedBox := transport (product rational rational) boxEquiv

/-- Serialize a finite set by its fixed-length membership vector. -/
def finset (n : ℕ) : Codec (Finset (Fin n)) :=
  transport (finiteFunction boolean n) (finsetEquiv n)

/-- Serialize both dense complexes and the fixed rational factor. -/
def reaction (n : ℕ) : Codec (Reaction n) :=
  transport (product (product (finiteFunction natural n) (finiteFunction natural n))
    (product positive positive)) (reactionEquiv n)

/-- Serialize species and reaction membership vectors at the declared dimensions. -/
def motif (n r : ℕ) : Codec (Motif n r) :=
  transport (product (finset n) (finset r)) (motifEquiv n r)

/-- Serialize all finite network fields at the declared species, reaction and core counts. -/
def network (n r c : ℕ) : Codec (Network n r c) :=
  transport (product
    (product (finiteFunction (reaction n) r) (finiteFunction (motif n r) c))
    (product (finiteFunction boolean r) (finiteFunction (optional box) n)))
    (networkEquiv n r c)

end JointThermoComplexity.Complexity.DataCodec

namespace JointThermoComplexity.Complexity.NetworkCodec
open FiniteCodec NetworkData RealSyntax

/-- Unary declared dimensions bound the number of explicitly represented entries. -/
def dimension : Codec ℕ := ⟨binderCode, parseBinders, by sorry, by sorry⟩

/-- A complete literal network together with its species, reaction and supplied-core counts. -/
structure Input where
  speciesCount : ℕ
  reactionCount : ℕ
  coreCount : ℕ
  network : Network speciesCount reactionCount coreCount

/-- Serialize the three dimension headers and then the fixed-dimension network fields. -/
def Input.code (Q : Input) : List Bool :=
  binderCode Q.speciesCount ++ binderCode Q.reactionCount ++ binderCode Q.coreCount ++
    (DataCodec.network Q.speciesCount Q.reactionCount Q.coreCount).code Q.network

/-- Read the three headers and all network fields, returning the unused suffix. -/
def parseInput (input : List Bool) : Option (Input × List Bool) := do
  let (n, tail₁) ← dimension.parse input
  let (r, tail₂) ← dimension.parse tail₁
  let (c, tail₃) ← dimension.parse tail₂
  let (Q, suffix) ← (DataCodec.network n r c).parse tail₃
  pure (⟨n, r, c, Q⟩, suffix)

/-- Decode a complete network input and reject any trailing data. -/
def decode (input : List Bool) : Option Input := do
  let (Q, suffix) ← parseInput input
  if suffix = [] then pure Q else none

/-- Well-formed literal supplied-motif inputs admitting a common state; PAC recognition is not
required. -/
def TotalFeasibility : Set (List Bool) :=
  {input | ∃ Q, decode input = some Q ∧ Q.network.Feasible}

end JointThermoComplexity.Complexity.NetworkCodec

/-! Signed PAC status is structural: a productive signed flux exists, and no
strict deletion of species or reactions remains an autocatalytic motif. -/
namespace ThermoCoreCompatibility
open scoped BigOperators

/-- A literal stoichiometric complex assigns a natural multiplicity to each species. -/
abbrev Complex (Species : Type*) := Species → ℕ

/-- Indexed reactant/product complexes and fixed positive real kinetic prefactors. -/
structure ReversibleCRN (Species Reaction : Type*) where
  reactant : Reaction → Complex Species
  product : Reaction → Complex Species
  barrier : Reaction → ℝ
  barrier_pos : ∀ r, 0 < barrier r

namespace ReversibleCRN
variable {Species Reaction : Type*}

/-- The signed stoichiometric change of a species in an indexed reaction. -/
def stoich (Q : ReversibleCRN Species Reaction) (s : Species) (r : Reaction) : ℤ :=
  (Q.product r s : ℤ) - (Q.reactant r s : ℤ)

end ReversibleCRN

variable {Species Reaction : Type*} [DecidableEq Species] [DecidableEq Reaction]

/-- A selected finite species set and a selected finite reaction set in a fixed network. -/
structure Motif (Q : ReversibleCRN Species Reaction) where
  species : Finset Species
  reactions : Finset Reaction

namespace Motif
variable {Q : ReversibleCRN Species Reaction}

/-- Both sets are nonempty, and every selected reaction meets selected species on both sides. -/
def SideIncident (C : Motif Q) : Prop :=
  C.species.Nonempty ∧ C.reactions.Nonempty ∧
    ∀ r ∈ C.reactions,
      (∃ s ∈ C.species, 0 < Q.reactant r s) ∧
      (∃ s ∈ C.species, 0 < Q.product r s)

/-- Every selected species has strictly positive net production under the same signed real flux. -/
def Productive (C : Motif Q) (v : Reaction → ℝ) : Prop :=
  ∀ s ∈ C.species,
    0 < ∑ r ∈ C.reactions, (Q.stoich s r : ℝ) * v r

/-- A side-incident motif that admits a productive signed real flux. -/
def IsAutocatalyticMotif (C : Motif Q) : Prop :=
  C.SideIncident ∧ ∃ v : Reaction → ℝ, C.Productive v

/-- Inclusion of both sets, with at least one proper species or reaction deletion. -/
def StrictSubmotif (small large : Motif Q) : Prop :=
  small.species ⊆ large.species ∧ small.reactions ⊆ large.reactions ∧
    (small.species ≠ large.species ∨ small.reactions ≠ large.reactions)

/-- An autocatalytic motif minimal under every strict species/reaction deletion. -/
def IsPAC (C : Motif Q) : Prop :=
  C.IsAutocatalyticMotif ∧
    ∀ small : Motif Q, small.StrictSubmotif C → ¬ small.IsAutocatalyticMotif

end Motif
end ThermoCoreCompatibility

namespace JointThermoComplexity.Complexity.LiteralBridge
open NetworkData
noncomputable section
variable {n r c : ℕ}

/-- Interpret the literal rational network as the preserved reversible chemical network. -/
def toCRN (Q : Network n r c) : ThermoCoreCompatibility.ReversibleCRN (Fin n) (Fin r) where
  reactant i := (Q.reactions i).reactant
  product i := (Q.reactions i).product
  barrier i := ((Q.reactions i).numerator : ℝ) / (Q.reactions i).denominator
  barrier_pos := by sorry

/-- Interpret the supplied index sets as a motif in that same chemical network. -/
def toMotif (Q : Network n r c) (a : Fin c) : ThermoCoreCompatibility.Motif (toCRN Q) where
  species := (Q.motifs a).species
  reactions := (Q.motifs a).reactions

end
end JointThermoComplexity.Complexity.LiteralBridge

/-! Existential-real complexity is ordinary binary polynomial reduction
closure of independently decoded ETR. Promise membership uses a separating
language; hardness preserves both source verdicts. -/
namespace JointThermoComplexity.Complexity.RealComplexity

/-- A decision language is a set of finite binary strings. -/
abbrev BitLanguage := Set (List Bool)

/-- A many-one reduction computed by an actual binary Turing machine in polynomial time. -/
def PolyReduces (L K : BitLanguage) : Prop :=
  ∃ f : List Bool → List Bool, f ∈ _root_.Complexity.FP ∧
    ∀ input, input ∈ L ↔ f input ∈ K

/-- The ordinary class of languages polynomial-time reducible to existential-real satisfiability. -/
def ExistsR (L : BitLanguage) : Prop := PolyReduces L RealSyntax.ETR

/-- Disjoint sets of promised YES and promised NO bit strings. -/
structure PromiseProblem where
  yes : BitLanguage
  no : BitLanguage
  disjoint : Disjoint yes no

/-- An existential-real language separates the promised YES and NO sets. -/
def PromiseProblem.Member (P : PromiseProblem) : Prop :=
  ∃ separator : BitLanguage, ExistsR separator ∧
    P.yes ⊆ separator ∧ Disjoint separator P.no

/-- One polynomial-time map sends every source YES and every source NO to the corresponding
promised set. -/
def PolyReducesToPromise (L : BitLanguage) (P : PromiseProblem) : Prop :=
  ∃ f : List Bool → List Bool, f ∈ _root_.Complexity.FP ∧
    (∀ input, input ∈ L → f input ∈ P.yes) ∧
    (∀ input, input ∉ L → f input ∈ P.no)

/-- Every existential-real language has a polynomial-time reduction preserving both promised
verdicts. -/
def PromiseProblem.Hard (P : PromiseProblem) : Prop :=
  ∀ L : BitLanguage, ExistsR L → PolyReducesToPromise L P

/-- Both separating-language membership and hardness for all existential-real languages. -/
def PromiseProblem.Complete (P : PromiseProblem) : Prop := P.Member ∧ P.Hard

end JointThermoComplexity.Complexity.RealComplexity

namespace JointThermoComplexity.Complexity.ChemicalPromiseProblem
open RealComplexity NetworkData
open scoped BigOperators

/-- The prescribed internal activity interval [1/4,1/2]. -/
def internalBox : ClosedBox := ⟨⟨1, 4, by decide⟩, ⟨1, 2, by decide⟩⟩
/-- The prescribed external activity interval [1/2,1]. -/
def externalBox : ClosedBox := ⟨⟨1, 2, by decide⟩, ⟨1, 1, by decide⟩⟩

/-- Boxed motif species use the internal interval and all other species the external interval;
unboxed inputs have no boxes. -/
def PrescribedBoxes (boxed : Bool) (Q : NetworkCodec.Input) : Prop :=
  if boxed then
    (∀ a s, s ∈ (Q.network.motifs a).species → Q.network.boxes s = some internalBox) ∧
    (∀ s, (∀ a, s ∉ (Q.network.motifs a).species) → Q.network.boxes s = some externalBox)
  else ∀ s, Q.network.boxes s = none

/-- Exactly two valid signed PACs, fixed factors in (0,2], the prescribed boxes and maximum side
molecularity six/eight. -/
def Domain (boxed : Bool) (Q : NetworkCodec.Input) : Prop :=
  Q.coreCount = 2 ∧
  (∀ a, (LiteralBridge.toMotif Q.network a).IsPAC) ∧
  (∀ r, 0 < ((Q.network.reactions r).numerator : ℝ) / (Q.network.reactions r).denominator ∧
    ((Q.network.reactions r).numerator : ℝ) / (Q.network.reactions r).denominator ≤ 2) ∧
  PrescribedBoxes boxed Q ∧
  ∀ r, (∑ s, (Q.network.reactions r).reactant s) ≤ (if boxed then 6 else 8) ∧
    (∑ s, (Q.network.reactions r).product s) ≤ (if boxed then 6 else 8)

/-- Well-formed promised networks with a globally shared feasible activity state. -/
def yes (boxed : Bool) : BitLanguage :=
  {input | ∃ Q, NetworkCodec.decode input = some Q ∧ Domain boxed Q ∧ Q.network.Feasible}

/-- Well-formed promised networks without a globally shared feasible activity state. -/
def no (boxed : Bool) : BitLanguage :=
  {input | ∃ Q, NetworkCodec.decode input = some Q ∧ Domain boxed Q ∧ ¬ Q.network.Feasible}

/-- The supplied-PAC promise problem with its explicit disjoint YES and NO sets. -/
def problem (boxed : Bool) : PromiseProblem where
  yes := yes boxed
  no := no boxed
  disjoint := by sorry


end JointThermoComplexity.Complexity.ChemicalPromiseProblem

namespace JointThermoComplexity.Complexity.ChemicalCompleteness

/-- The boxed two-supplied-PAC promise problem is existential-real complete,
with fixed factors in(0,2], the specified activity intervals and molecularity6. -/
theorem boxed_complete : (ChemicalPromiseProblem.problem true).Complete := by sorry

/-- The unboxed two-supplied-PAC promise problem is existential-real complete,
with fixed factors in(0,2] and maximum side molecularity8. -/
theorem unboxed_complete : (ChemicalPromiseProblem.problem false).Complete := by sorry

end JointThermoComplexity.Complexity.ChemicalCompleteness
