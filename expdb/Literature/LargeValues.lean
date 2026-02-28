/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import expdb.Basic.LargeValueEstimate

/-!
# Literature Large Value Estimates

This file contains large value estimates from the literature, axiomatized as
propositions in Lean. These mirror the `literature.py` functions
`add_huxley_large_values_estimate`, `add_heath_brown_large_values_estimate`, etc.

## Main Results

* `large_value_L2_bound` — The L² mean value theorem: ρ ≤ max(2 − 2σ, 1 − 2σ + τ)
* `large_value_huxley_bound` — Huxley's estimate: ρ ≤ max(2 − 2σ, 4 − 6σ + τ)
* `large_value_heath_brown_bound` — Heath-Brown's estimate: ρ ≤ max(2 − 2σ, 10 − 13σ + τ)

## Implementation Notes

In the Python code (`large_values.py`), each literature estimate is represented as
a 3D region of feasible (σ, τ, ρ) triples. In Lean, we axiomatize each bound as
a proposition: given that σ and τ are in the domain and ρ equals the stated bound,
then `LargeValueEstimate σ τ ρ` holds.

Each axiom corresponds to a single linear upper bound on ρ from the Python code.
The "max" structure (taking the maximum of several linear bounds) is represented
by providing separate axioms for each branch of the maximum.

## References

* [Huxley, 1972] - "On the difference between consecutive primes"
* [Heath-Brown, 1979] - "Zero density estimates for the Riemann zeta function"
* [Jutila, 1977] - "Zero-density estimates for L-functions"
* [Bourgain, 2000] - "On large values estimates for Dirichlet polynomials"
* [Guth-Maynard, 2024] - Large value estimates
-/

/-!
## L² Mean Value Theorem (Classical)

The classical L² mean value theorem gives:
  LV(σ, τ) ≤ max(2 − 2σ, 1 − 2σ + τ)

This is the most basic large value estimate and holds for all σ ∈ [1/2, 1]
and τ ≥ 0.

**Python equivalent**: `large_value_estimate_L2` in `large_values.py`
  `classical_LV_estimate([[2, -2, 0], [1, -2, 1]])`
-/

/--
The L² mean value theorem, first branch: ρ ≤ 2 − 2σ.

This bound is independent of τ and represents the baseline large value estimate.
The domain constraint 0 ≤ 2 − 2σ is satisfied when σ ≤ 1.
-/
axiom large_value_L2_branch1 (σ τ : ℚ)
    (hσ₁ : 1/2 ≤ σ) (hσ₂ : σ ≤ 1) (hτ : 0 ≤ τ) (hρ : 0 ≤ 2 - 2 * σ) :
    LargeValueEstimate σ τ (2 - 2 * σ)

/--
The L² mean value theorem, second branch: ρ ≤ 1 − 2σ + τ.

This bound depends linearly on τ and dominates the first branch when τ is large
relative to 1 − σ.
-/
axiom large_value_L2_branch2 (σ τ : ℚ)
    (hσ₁ : 1/2 ≤ σ) (hσ₂ : σ ≤ 1) (hτ : 0 ≤ τ) (hρ : 0 ≤ 1 - 2 * σ + τ) :
    LargeValueEstimate σ τ (1 - 2 * σ + τ)

/-!
## Huxley's Large Value Estimate

Huxley's large value theorem gives:
  LV(σ, τ) ≤ max(2 − 2σ, 4 − 6σ + τ)

**Python equivalent**: `add_huxley_large_values_estimate` in `literature.py`
  `literature_bound_LV_max([[2, -2, 0], [4, -6, 1]], ...)`

**Reference**: Huxley (1972), "On the difference between consecutive primes"
-/

/--
Huxley's large value theorem, second branch: ρ ≤ 4 − 6σ + τ.

(The first branch ρ ≤ 2 − 2σ is already captured by `large_value_L2_branch1`.)
-/
axiom large_value_huxley (σ τ : ℚ)
    (hσ₁ : 1/2 ≤ σ) (hσ₂ : σ ≤ 1) (hτ : 0 ≤ τ) (hρ : 0 ≤ 4 - 6 * σ + τ) :
    LargeValueEstimate σ τ (4 - 6 * σ + τ)

/-!
## Heath-Brown's Large Value Estimate

Heath-Brown's large value theorem gives:
  LV(σ, τ) ≤ max(2 − 2σ, 10 − 13σ + τ)

**Python equivalent**: `add_heath_brown_large_values_estimate` in `literature.py`
  `literature_bound_LV_max([[2, -2, 0], [10, -13, 1]], ...)`

**Reference**: Heath-Brown (1979), "Zero density estimates for the Riemann zeta function"
-/

/--
Heath-Brown's large value theorem, second branch: ρ ≤ 10 − 13σ + τ.

(The first branch ρ ≤ 2 − 2σ is already captured by `large_value_L2_branch1`.)
-/
axiom large_value_heath_brown (σ τ : ℚ)
    (hσ₁ : 1/2 ≤ σ) (hσ₂ : σ ≤ 1) (hτ : 0 ≤ τ) (hρ : 0 ≤ 10 - 13 * σ + τ) :
    LargeValueEstimate σ τ (10 - 13 * σ + τ)

/-!
## Guth-Maynard Large Value Estimate

Guth and Maynard's large value theorem gives:
  LV(σ, τ) ≤ max(2 − 2σ, 18/5 − 4σ, τ + 12/5 − 4σ)

**Python equivalent**: `add_guth_maynard_large_values_estimate` in `literature.py`
  `literature_bound_LV_max([[2, -2, 0], [18/5, -4, 0], [12/5, -4, 1]], ...)`

**Reference**: Guth-Maynard (2024)
-/

/--
Guth-Maynard large value theorem, second branch: ρ ≤ 18/5 − 4σ.

(The first branch ρ ≤ 2 − 2σ is already captured by `large_value_L2_branch1`.)
-/
axiom large_value_guth_maynard_branch2 (σ τ : ℚ)
    (hσ₁ : 1/2 ≤ σ) (hσ₂ : σ ≤ 1) (hτ : 0 ≤ τ) (hρ : 0 ≤ 18/5 - 4 * σ) :
    LargeValueEstimate σ τ (18/5 - 4 * σ)

/--
Guth-Maynard large value theorem, third branch: ρ ≤ τ + 12/5 − 4σ.
-/
axiom large_value_guth_maynard_branch3 (σ τ : ℚ)
    (hσ₁ : 1/2 ≤ σ) (hσ₂ : σ ≤ 1) (hτ : 0 ≤ τ) (hρ : 0 ≤ τ + 12/5 - 4 * σ) :
    LargeValueEstimate σ τ (τ + 12/5 - 4 * σ)

/-!
## Numerical Verification

These examples verify that specific literature bounds satisfy the domain constraints.
-/

/-- The L² bound at σ = 3/4, τ = 1 gives ρ = 1/2 -/
example : LargeValueEstimate (3/4) 1 (1/2) :=
  large_value_L2_branch1 (3/4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The L² bound at σ = 1/2, τ = 0 gives ρ = 1 -/
example : LargeValueEstimate (1/2) 0 1 :=
  large_value_L2_branch1 (1/2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Huxley's bound at σ = 3/4, τ = 2 gives ρ = 4 − 6·(3/4) + 2 = 3/2 -/
example : LargeValueEstimate (3/4) 2 (3/2) :=
  large_value_huxley (3/4) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The L² second branch at σ = 1/2, τ = 1 gives ρ = 1 -/
example : LargeValueEstimate (1/2) 1 1 :=
  large_value_L2_branch2 (1/2) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-!
## Future Additions

As the formalization progresses, additional literature bounds will be added:
* Jutila (1977) — family of estimates parameterized by k
* Bourgain (2000) — optimized large value estimate with piecewise bounds
* Guth-Maynard (2024) — second family of estimates parameterized by k
-/
