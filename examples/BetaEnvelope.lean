import Expdb.Bounds

open Expdb.Bounds

def query : RatInterval :=
  RatInterval.closed 0 (1 / 2) (by norm_num)

def trivialInput : BetaInput :=
  trivialBetaInput query

def classical : BetaInput :=
  {
    label := "assumed classical beta bound"
    bound := {
      domain := query
      function := ⟨1 / 2, 1 / 6⟩
    }
  }

def result : BetaEnvelopeResult :=
  BetaEnvelope.compute query [trivialInput, classical]

#eval result.coversQuery
#eval BetaEnvelope.pretty [trivialInput, classical] result
#eval BetaEnvelope.evalRat? result (1 / 3)
#eval BetaEnvelope.evalRat? result (1 / 2)
