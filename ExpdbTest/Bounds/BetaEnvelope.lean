module

public import Expdb.Bounds
public meta import Expdb.Bounds

/-!
# Tests for exact beta envelopes
-/

set_option linter.hashCommand false
set_option linter.style.nativeDecide false

@[expose] public section

namespace ExpdbTest.Bounds.BetaEnvelope

open Expdb.Bounds

def query : RatInterval :=
  RatInterval.closed 0 (1 / 2) (by norm_num)

def trivialInput : BetaInput :=
  Expdb.Bounds.trivialBetaInput query

def classicalInput : BetaInput :=
  {
    label := "classical"
    bound := {
      domain := query
      function := ⟨1 / 2, 1 / 6⟩
    }
  }

def inputs : List BetaInput :=
  [trivialInput, classicalInput]

def result : BetaEnvelopeResult :=
  Expdb.Bounds.BetaEnvelope.compute query inputs

#guard result.coversQuery
#guard result.isCertifiedBy inputs
#guard result.pieces.length == 2
#guard result.pieces[0]?.map (·.sourceIndex) == some 0
#guard result.pieces[0]?.map (·.bound.domain.lower) == some 0
#guard result.pieces[0]?.map (·.bound.domain.upper) == some (1 / 3)
#guard result.pieces[0]?.map (·.bound.domain.upperBoundary) == some .closed
#guard result.pieces[1]?.map (·.sourceIndex) == some 1
#guard result.pieces[1]?.map (·.bound.domain.lower) == some (1 / 3)
#guard result.pieces[1]?.map (·.bound.domain.lowerBoundary) == some .open
#guard result.pieces[1]?.map (·.bound.domain.upper) == some (1 / 2)
#guard Expdb.Bounds.BetaEnvelope.evalRat? result (1 / 3) == some (1 / 3)
#guard Expdb.Bounds.BetaEnvelope.evalRat? result (1 / 2) == some (5 / 12)

def emptyResult : BetaEnvelopeResult :=
  Expdb.Bounds.BetaEnvelope.compute query []

#guard !emptyResult.coversQuery
#guard emptyResult.pieces.isEmpty

def duplicateResult : BetaEnvelopeResult :=
  Expdb.Bounds.BetaEnvelope.compute query [trivialInput, trivialInput]

#guard duplicateResult.coversQuery
#guard duplicateResult.pieces.length == 1
#guard duplicateResult.pieces[0]?.map (·.sourceIndex) == some 0

def leftOnly : BetaInput :=
  {
    label := "left"
    bound := {
      domain := RatInterval.closedOpen 0 (1 / 4) (by norm_num)
      function := ⟨1, 0⟩
    }
  }

def rightOnly : BetaInput :=
  {
    label := "right"
    bound := {
      domain := RatInterval.openClosed (1 / 4) (1 / 2) (by norm_num)
      function := ⟨1, 0⟩
    }
  }

def gapResult : BetaEnvelopeResult :=
  Expdb.Bounds.BetaEnvelope.compute query [leftOnly, rightOnly]

#guard !gapResult.coversQuery
#guard Expdb.Bounds.BetaEnvelope.evalRat? gapResult (1 / 4) == none

set_option linter.flexible false in
/-- Once the nontrivial input is proved, the certified calculation turns every
reported piece into a theorem automatically. -/
example (hclassical : classicalInput.bound.Valid) :
    ∀ p ∈ result.pieces, p.bound.Valid := by
  apply BetaEnvelopeResult.pieces_valid_of_isCertifiedBy_eq_true
    (inputs := inputs)
  · intro source hsource
    simp [inputs] at hsource
    rcases hsource with rfl | rfl
    · exact Expdb.Bounds.trivialBetaInput_valid query
    · exact hclassical
  · native_decide

end ExpdbTest.Bounds.BetaEnvelope
