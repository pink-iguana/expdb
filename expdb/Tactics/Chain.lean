/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import Lean
import expdb.Transforms.VanDerCorputA
import expdb.Transforms.VanDerCorputB

/-!
# Chain Tactic for Exponent Pair Derivations

This file provides the `by_chain` tactic that automates the application of A/B transform
chains to derive exponent pairs. This reduces multi-line derivation proofs to one-liners.

## Main Declarations

* `by_chain` - Tactic to apply a chain of A/B transforms automatically

## Usage

The chain string specifies which transforms to apply in function composition order
(outermost first, i.e., the rightmost character is applied first to the starting pair).

```lean
-- Derive (2/7, 4/7) = BAAB(0, 1) in one line:
theorem example : IsExponentPair (2/7) (4/7) := by
  by_chain "BAAB" trivial_pair

-- Compare with the manual proof:
theorem example' : IsExponentPair (2/7) (4/7) := by
  have h1 := trivial_pair.ofB (by norm_num) (by norm_num)
  have h2 := h1.ofA (by norm_num) (by norm_num)
  have h3 := h2.ofA (by norm_num) (by norm_num)
  exact h3.ofB (by norm_num) (by norm_num)
```

## Implementation Notes

The tactic works by:
1. Applying each transform axiom (`vanDerCorputA`/`vanDerCorputB`) in sequence to build
   a proof term with unsimplified rational expressions
2. Using `IsExponentPair.ofA`/`IsExponentPair.ofB` with `norm_num` for the final step
   to verify that the resulting rational expressions match the goal

## References

See `LEAN.md` for the overall formalization strategy and the role of custom tactics.
-/

open Lean Elab Tactic

/-- `by_chain "chain" start` applies the chain of A/B transforms to `start` to prove the goal.

The chain string is read in function composition order: `"BAAB"` means `B(A(A(B(start))))`.
The rightmost character is applied first to the starting pair.

Each character must be `'A'` (van der Corput A-process) or `'B'` (van der Corput B-process).

**Examples**:
- `by_chain "B" trivial_pair` proves `IsExponentPair (1/2) (1/2)` (Weyl's pair)
- `by_chain "AB" trivial_pair` proves `IsExponentPair (1/6) (2/3)` (classical vdC pair)
- `by_chain "BAAB" trivial_pair` proves `IsExponentPair (2/7) (4/7)`
-/
syntax "by_chain" str term : tactic

elab_rules : tactic
  | `(tactic| by_chain $chain:str $start:term) => do
    let chainStr := chain.getString
    let chars := chainStr.data
    -- Validate the chain string
    if chars.isEmpty then
      throwError "by_chain: chain string cannot be empty"
    for c in chars do
      if c != 'A' && c != 'B' then
        throwError "by_chain: invalid character '{c}' in chain string; expected only 'A' or 'B'"
    -- Apply transforms right-to-left (rightmost character is applied first)
    let steps := chars.reverse
    -- For a single-step chain, use ofA/ofB directly with norm_num
    if steps.length == 1 then
      match steps.head! with
      | 'A' =>
        evalTactic (← `(tactic|
          exact IsExponentPair.ofA $start (by norm_num) (by norm_num)))
      | 'B' =>
        evalTactic (← `(tactic|
          exact IsExponentPair.ofB $start (by norm_num) (by norm_num)))
      | _ => unreachable!
      return
    -- For multi-step chains:
    -- Step 1: Introduce the starting proof as a local hypothesis
    let h₀ := mkIdent `_by_chain_0
    evalTactic (← `(tactic| have $h₀ := $start))
    -- Step 2: Apply intermediate transforms using axioms directly.
    -- Each step builds on the previous, with Lean inferring k and l from the hypothesis type.
    -- Loop covers steps[0] through steps[n-2]; the final step[n-1] is handled in Step 3.
    let mut prev := h₀
    for i in [:steps.length - 1] do
      let next := mkIdent (Name.mkSimple s!"_by_chain_{i + 1}")
      match steps[i]! with
      | 'A' =>
        evalTactic (← `(tactic| have $next := vanDerCorputA _ _ $prev))
      | 'B' =>
        evalTactic (← `(tactic| have $next := vanDerCorputB _ _ $prev))
      | _ => unreachable!
      prev := next
    -- Step 3: Apply the final transform using ofA/ofB with norm_num.
    -- The ofA/ofB helpers introduce equality obligations (k' = ..., l' = ...)
    -- that norm_num discharges by evaluating the rational arithmetic.
    match steps.getLast! with
    | 'A' =>
      evalTactic (← `(tactic|
        exact IsExponentPair.ofA $prev (by norm_num) (by norm_num)))
    | 'B' =>
      evalTactic (← `(tactic|
        exact IsExponentPair.ofB $prev (by norm_num) (by norm_num)))
    | _ => unreachable!
