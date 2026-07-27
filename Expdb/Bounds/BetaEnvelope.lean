module

public import Expdb.Bounds.Basic
public import Expdb.ExponentialSums.ExponentSumGrowth

/-!
# Exact envelopes of affine bounds on beta

This file supplies a deliberately small executable lower-envelope calculator.
It records which input supplies each output piece and relates an affine piece
to `exponentSumGrowthExponent`.
-/

@[expose] public section

namespace Expdb.Bounds

open scoped NNReal

/-- An affine upper bound on beta over a rational interval. -/
structure BetaBound where
  domain : RatInterval
  function : RatAffine

/-- A labelled input to the envelope computation. -/
structure BetaInput where
  label : String
  bound : BetaBound

/-- A piece of a computed envelope, with the index of its source input. -/
structure EnvelopePiece where
  sourceIndex : Nat
  bound : BetaBound

/-- The result of an envelope computation. -/
structure BetaEnvelopeResult where
  pieces : List EnvelopePiece
  coversQuery : Bool

namespace BetaBound

/-- The mathematical assertion represented by an affine beta bound. -/
def Valid (b : BetaBound) : Prop :=
  ∀ α : ℝ≥0, b.domain.ContainsReal (α : ℝ) →
    Expdb.exponentSumGrowthExponent α ≤ b.function.evalReal (α : ℝ)

end BetaBound

namespace EnvelopePiece

/-- Check that a piece has the same affine function as its recorded source and
that its domain is contained in the source domain. -/
def isCertifiedBy (p : EnvelopePiece) (inputs : List BetaInput) : Bool :=
  match inputs[p.sourceIndex]? with
  | none => false
  | some source =>
      decide (p.bound.function = source.bound.function) &&
        p.bound.domain.isSubset source.bound.domain

/-- A piece passing `isCertifiedBy` inherits validity from its source input. -/
theorem valid_of_isCertifiedBy_eq_true
    {p : EnvelopePiece} {inputs : List BetaInput}
    (hinputs : ∀ source ∈ inputs, source.bound.Valid)
    (hp : p.isCertifiedBy inputs = true) :
    p.bound.Valid := by
  unfold isCertifiedBy at hp
  split at hp
  · contradiction
  · rename_i source hsource
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    rcases hp with ⟨hfunction, hdomain⟩
    intro α hα
    have hαsource :=
      RatInterval.containsReal_of_isSubset_eq_true hdomain hα
    have hvalid := hinputs source (List.mem_of_getElem? hsource) α hαsource
    simpa [hfunction] using hvalid

end EnvelopePiece

namespace BetaEnvelopeResult

/-- Check that every result piece is certified by its recorded input. -/
def isCertifiedBy (result : BetaEnvelopeResult) (inputs : List BetaInput) : Bool :=
  result.pieces.all fun p ↦ p.isCertifiedBy inputs

/-- Every piece of a certified result is a valid beta bound when all inputs are valid. -/
theorem pieces_valid_of_isCertifiedBy_eq_true
    {result : BetaEnvelopeResult} {inputs : List BetaInput}
    (hinputs : ∀ source ∈ inputs, source.bound.Valid)
    (hresult : result.isCertifiedBy inputs = true) :
    ∀ p ∈ result.pieces, p.bound.Valid := by
  intro p hp
  apply p.valid_of_isCertifiedBy_eq_true hinputs
  simpa [isCertifiedBy] using List.all_eq_true.mp hresult p hp

end BetaEnvelopeResult

namespace BetaEnvelope

def insertPoint (x : ℚ) : List ℚ → List ℚ
  | [] => [x]
  | y :: ys =>
      if x < y then x :: y :: ys
      else if x = y then y :: ys
      else y :: insertPoint x ys

def sortDedup (xs : List ℚ) : List ℚ :=
  xs.foldl (fun acc x ↦ insertPoint x acc) []

def pairIntersections : List BetaInput → List ℚ
  | [] => []
  | b :: bs =>
      bs.filterMap (fun c ↦ b.bound.function.intersection? c.bound.function) ++
        pairIntersections bs

def criticalPoints (query : RatInterval) (inputs : List BetaInput) : List ℚ :=
  sortDedup <|
    (query.lower :: query.upper ::
      inputs.flatMap fun b ↦ [b.bound.domain.lower, b.bound.domain.upper]) ++
      pairIntersections inputs
  |>.filter query.containsClosureRat

def cells : List ℚ → List RatInterval
  | [] => []
  | [x] => [RatInterval.singleton x]
  | x :: y :: rest =>
      RatInterval.singleton x ::
        (if h : x ≤ y then [RatInterval.openInterval x y h] else []) ++
        cells (y :: rest)
termination_by xs => xs.length

def betterAt (x : ℚ) (candidate current : Nat × BetaInput) : Nat × BetaInput :=
  if candidate.2.bound.function.evalRat x < current.2.bound.function.evalRat x then
    candidate
  else
    current

def chooseAt (inputs : List BetaInput) (x : ℚ) : Option (Nat × BetaInput) :=
  let active := inputs.zipIdx.filter fun b ↦ b.1.bound.domain.containsRat x
  match active with
  | [] => none
  | b :: bs =>
      some <| bs.foldl
        (fun current candidate ↦
          betterAt x (candidate.2, candidate.1) current)
        (b.2, b.1)

def pieceForCell (inputs : List BetaInput) (cell : RatInterval) :
    Option EnvelopePiece := do
  let selected ← chooseAt inputs cell.sample
  let domain ← cell.intersect? selected.2.bound.domain
  pure {
    sourceIndex := selected.1
    bound := {
      domain
      function := selected.2.bound.function
    }
  }

def mergePiece? (p q : EnvelopePiece) : Option EnvelopePiece := do
  if p.sourceIndex != q.sourceIndex || p.bound.function != q.bound.function then
    none
  else
    let domain ← p.bound.domain.mergeAdjacent? q.bound.domain
    pure { p with bound.domain := domain }

def mergePieces : List EnvelopePiece → List EnvelopePiece
  | p :: q :: rest =>
      match mergePiece? p q with
      | some merged => mergePieces (merged :: rest)
      | none => p :: mergePieces (q :: rest)
  | pieces => pieces
termination_by pieces => pieces.length

/-- Compute the exact lower envelope of the applicable input bounds on `query`.

The implementation is deterministic.  At an exact tie, the earlier input wins.
Uncovered cells are omitted and recorded by `coversQuery = false`. -/
def compute (query : RatInterval) (inputs : List BetaInput) : BetaEnvelopeResult :=
  let queryCells := (cells (criticalPoints query inputs)).filterMap (·.intersect? query)
  let rawPieces := queryCells.filterMap (pieceForCell inputs)
  {
    pieces := mergePieces rawPieces
    coversQuery := rawPieces.length == queryCells.length
  }

/-- Evaluate a computed envelope exactly at a rational point. -/
def evalRat? (result : BetaEnvelopeResult) (x : ℚ) : Option ℚ :=
  result.pieces.findSome? fun p ↦
    if p.bound.domain.containsRat x then some (p.bound.function.evalRat x) else none

/-- Render the envelope with source labels from its input list. -/
def pretty (inputs : List BetaInput) (result : BetaEnvelopeResult) : String :=
  String.intercalate "\n" <| result.pieces.map fun p ↦
    let label := (inputs[p.sourceIndex]?).map (·.label) |>.getD s!"input {p.sourceIndex}"
    let left := if p.bound.domain.lowerBoundary == .closed then "[" else "("
    let right := if p.bound.domain.upperBoundary == .closed then "]" else ")"
    s!"{label}: slope={p.bound.function.slope}, intercept={p.bound.function.intercept}, " ++
      s!"domain={left}{p.bound.domain.lower},{p.bound.domain.upper}{right}"

end BetaEnvelope

/-- Public short name for the exact beta-envelope computation. -/
abbrev computeBetaEnvelope := BetaEnvelope.compute

/-- The trivial beta bound `β(α) ≤ α` on a supplied interval. -/
def trivialBetaInput (domain : RatInterval) : BetaInput :=
  {
    label := "trivial beta bound"
    bound := {
      domain
      function := ⟨1, 0⟩
    }
  }

/-- The trivial beta input is valid, by the existing triangle-inequality bound. -/
theorem trivialBetaInput_valid (domain : RatInterval) :
    (trivialBetaInput domain).bound.Valid := by
  intro α _
  have h := Expdb.exponentSumGrowthExponent_le_iff.mpr
    (Expdb.isExponentSumBound_self α)
  simpa [trivialBetaInput, RatAffine.evalReal] using h

end Expdb.Bounds
