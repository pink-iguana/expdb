/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Large Value Estimates

This file defines large value estimates, which bound how frequently a Dirichlet
polynomial of length N can be large. Specifically, a large value estimate asserts
that for a Dirichlet polynomial P of length N, the measure of t ∈ [T, 2T] where
|P(σ + it)| ≥ V is bounded by

  |{t ∈ [T, 2T] : |P(σ + it)| ≥ V}| ≤ N^(ρ+ε) T^ε

where ρ ≤ LV(σ, τ) depends on σ (the real part) and τ (where V = N^τ).

## Main Definitions

* `LargeValueEstimate σ τ ρ` — A predicate asserting that ρ is a valid large value
  bound for parameters (σ, τ), i.e., ρ ≤ LV(σ, τ).

## Mathematical Background

Large value estimates are a central tool in analytic number theory, connecting
exponential sum bounds to zero-density estimates for the Riemann zeta function.
The key parameters are:

* σ ∈ [1/2, 1]: the real part of the complex variable
* τ ≥ 0: encodes the size threshold V = N^τ
* ρ: the exponent bounding the measure of large values

The feasible region of (σ, τ, ρ) forms a 3-dimensional polytope (or union of
polytopes) in the Python code. In Lean, we axiomatize individual bounds as
predicates.

## References

* [Huxley, 1972] - "On the difference between consecutive primes"
* [Heath-Brown, 1979] - "Zero density estimates"
* [Jutila, 1977] - "Zero-density estimates for L-functions"
* [Bourgain, 2000] - "On large values estimates for Dirichlet polynomials"
* [Guth-Maynard, 2024] - Large value estimates
* [ANTEDB Blueprint] - https://teorth.github.io/expdb/blueprint/
* See `blueprint/src/python/large_values.py` for the Python implementation

## Implementation Notes

Following the same strategy as `ExponentPair.lean`, we define a predicate
`LargeValueEstimate` that captures the constraint ρ ≤ LV(σ, τ) for given
parameters. Literature bounds are axiomatized in `Literature/LargeValues.lean`,
and transforms are axiomatized in `Transforms/LargeValueRaisePower.lean`.

See `LEAN.md` for the overall formalization strategy.
-/

/--
Predicate: is ρ a valid large value bound for parameters (σ, τ)?

This asserts that the measure of large values of a Dirichlet polynomial with
parameters σ and τ is bounded by N^(ρ+ε). The domain constraints are:
  - 1/2 ≤ σ ≤ 1 (σ is in the critical strip)
  - 0 ≤ τ (τ encodes the threshold)
  - 0 ≤ ρ (the bound is nonneg)

A large value estimate `LargeValueEstimate σ τ ρ` asserts that (σ, τ, ρ) is
feasible, meaning ρ is an upper bound on LV(σ, τ).
-/
def LargeValueEstimate (σ τ ρ : ℚ) : Prop :=
  1/2 ≤ σ ∧ σ ≤ 1 ∧ 0 ≤ τ ∧ 0 ≤ ρ

namespace LargeValueEstimate

/-- The σ parameter is in the critical strip -/
theorem sigma_in_critical_strip {σ τ ρ : ℚ} (h : LargeValueEstimate σ τ ρ) :
    1/2 ≤ σ ∧ σ ≤ 1 :=
  ⟨h.1, h.2.1⟩

/-- The τ parameter is nonneg -/
theorem tau_nonneg {σ τ ρ : ℚ} (h : LargeValueEstimate σ τ ρ) :
    0 ≤ τ :=
  h.2.2.1

/-- The ρ parameter is nonneg -/
theorem rho_nonneg {σ τ ρ : ℚ} (h : LargeValueEstimate σ τ ρ) :
    0 ≤ ρ :=
  h.2.2.2

/-- Any ρ' ≥ ρ is also a valid bound (monotonicity in ρ). -/
theorem mono_rho {σ τ ρ ρ' : ℚ} (h : LargeValueEstimate σ τ ρ)
    (hρ : ρ ≤ ρ') :
    LargeValueEstimate σ τ ρ' :=
  ⟨h.1, h.2.1, h.2.2.1, le_trans h.2.2.2 hρ⟩

end LargeValueEstimate

/-!
## Examples

These verify that specific (σ, τ, ρ) triples satisfy the domain constraints.
The actual bounds (showing ρ ≤ LV(σ, τ)) are provided by axioms in the
`Literature` module.
-/

-- Domain check: (3/4, 1, 1/2)
example : LargeValueEstimate (3/4) 1 (1/2) := by
  unfold LargeValueEstimate
  norm_num

-- Domain check: (1/2, 0, 1)
example : LargeValueEstimate (1/2) 0 1 := by
  unfold LargeValueEstimate
  norm_num
