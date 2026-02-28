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
# Zero Density Estimates

This file defines zero density estimates for the Riemann zeta function.
A zero density estimate bounds the number N(σ, T) of zeros of ζ(s) in the
rectangle σ ≤ Re(s) ≤ 1, |Im(s)| ≤ T, in the form:

  N(σ, T) ≤ T^{A(1-σ) + o(1)}   as T → ∞

where A = A(σ) is the zero density exponent.

## Main Definitions

* `IsZeroDensityBound A σ` - Predicate asserting that A is a valid upper bound
  on the zero density exponent at σ
* `ZeroDensityEstimate` - A structure bundling A and σ with proof obligations

## Implementation Notes

This follows the same axiomatization strategy as `IsExponentPair`: the predicate
captures geometric/domain constraints, while the actual analytic content comes
from literature axioms in `expdb.Literature.ZeroDensityClassical` and transform
axioms in `expdb.Transforms.ExponentPairToZeroDensity`.

The definition mirrors the Python class `Zero_Density_Estimate` in
`blueprint/src/python/zero_density_estimate.py`.

## References

* [Ingham, 1940] - "On the estimation of N(σ,T)"
* [Huxley, 1972] - Zero density estimates for primes
* [Heath-Brown, 1979] - Zero density estimates for ζ(s) and L-functions
* [ANTEDB Blueprint] - https://teorth.github.io/expdb/blueprint/
-/

/--
A zero density bound `IsZeroDensityBound A σ` asserts that the zero density
exponent at σ is at most A. That is:

  N(σ, T) ≤ T^{A(1-σ) + o(1)}

where N(σ, T) counts the zeros of ζ(s) with Re(s) ≥ σ and |Im(s)| ≤ T.

The geometric constraints are:
- A ≥ 0 (the density bound is non-negative)
- 1/2 ≤ σ ≤ 1 (zeros lie in the critical strip)

The actual density bounds (specific values of A at specific σ) come from
literature axioms and transforms, analogous to how `IsExponentPair` values
come from literature axioms.
-/
def IsZeroDensityBound (A σ : ℚ) : Prop :=
  0 ≤ A ∧ 1/2 ≤ σ ∧ σ ≤ 1

/--
A `ZeroDensityEstimate` bundles a bound value A and a point σ with
proof that the bound satisfies the geometric constraints.

This is the bundled version of `IsZeroDensityBound`, analogous to
`ExponentPair` being the bundled version of `IsExponentPair`.
-/
structure ZeroDensityEstimate where
  A : ℚ
  σ : ℚ
  A_nonneg : 0 ≤ A
  σ_ge_half : 1/2 ≤ σ
  σ_le_one : σ ≤ 1

namespace ZeroDensityEstimate

/-- Convert a `ZeroDensityEstimate` structure to the `IsZeroDensityBound` predicate -/
theorem isZeroDensityBound_of_zeroDensityEstimate (e : ZeroDensityEstimate) :
    IsZeroDensityBound e.A e.σ :=
  ⟨e.A_nonneg, e.σ_ge_half, e.σ_le_one⟩

/-- Helper: create a `ZeroDensityEstimate` from rationals with a proof -/
def mk' (A σ : ℚ) (h : IsZeroDensityBound A σ) : ZeroDensityEstimate :=
  ⟨A, σ, h.1, h.2.1, h.2.2⟩

end ZeroDensityEstimate

namespace IsZeroDensityBound

/-- Monotonicity: if A is a valid zero density bound and A ≤ A', then A' is
    also a valid bound. Larger A gives a weaker (but still valid) estimate. -/
theorem mono {A A' σ : ℚ} (h : IsZeroDensityBound A σ) (hle : A ≤ A') :
    IsZeroDensityBound A' σ :=
  ⟨le_trans h.1 hle, h.2.1, h.2.2⟩

/-- The sigma value lies in [1/2, 1]. -/
theorem sigma_bounds {A σ : ℚ} (h : IsZeroDensityBound A σ) : 1/2 ≤ σ ∧ σ ≤ 1 :=
  ⟨h.2.1, h.2.2⟩

/-- The bound A is non-negative. -/
theorem bound_nonneg {A σ : ℚ} (h : IsZeroDensityBound A σ) : 0 ≤ A :=
  h.1

end IsZeroDensityBound

/-!
## Examples

These verify that specific (A, σ) pairs satisfy the geometric constraints.
-/

-- Ingham's bound at σ = 3/4: A ≤ 3/(2 - 3/4) = 12/5
example : IsZeroDensityBound (12/5) (3/4) := by
  unfold IsZeroDensityBound
  norm_num

-- The density hypothesis bound A = 2 at σ = 3/4
example : IsZeroDensityBound 2 (3/4) := by
  unfold IsZeroDensityBound
  norm_num

-- Bourgain's bound A = 2 at σ = 25/32
example : IsZeroDensityBound 2 (25/32) := by
  unfold IsZeroDensityBound
  norm_num
