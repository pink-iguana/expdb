/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import expdb.Basic.ZeroDensityEstimate

/-!
# Classical Zero Density Estimates

This file contains the classical zero density estimates from the literature,
axiomatized following the same approach as `Literature/Classical.lean` for
exponent pairs.

These estimates bound the zero density exponent A(σ) in the estimate
  N(σ, T) ≤ T^{A(σ)(1-σ) + o(1)}
where N(σ, T) counts zeros of ζ(s) with Re(s) ≥ σ, |Im(s)| ≤ T.

## Main Results

* `carlson_zero_density` - Carlson (1921): A(σ) ≤ 4σ
* `ingham_zero_density` - Ingham (1940): A(σ) ≤ 3/(2-σ)
* `huxley_zero_density` - Huxley (1972): A(σ) ≤ 3/(3σ-1)
* `heathbrown_zero_density` - Heath-Brown (1979): A(σ) ≤ 4/(4σ-1) for σ ∈ [25/28, 1]
* `bourgain_zero_density` - Bourgain (2000): A(σ) ≤ 2 for σ ∈ [25/32, 1]
* `guth_maynard_zero_density` - Guth-Maynard (2024): A(σ) ≤ 15/(3+5σ)

## Implementation Notes

These are axiomatized as universally quantified statements over σ (with appropriate
domain restrictions), mirroring the Python code in `literature.py` Chapter 11.
Each axiom gives A(σ) as a rational function of σ on an interval.

The axiomatization strategy mirrors `literature.py`: results are recorded with their
references but not re-proved from first principles.

## References

* [Carlson, 1921] - "Über die Nullstellen der Dirichletschen Reihen"
* [Ingham, 1940] - "On the estimation of N(σ,T)"
* [Huxley, 1972] - "On the difference between consecutive primes"
* [Heath-Brown, 1979] - "Zero Density Estimates for the Riemann Zeta-Function"
* [Bourgain, 2000] - "On large values estimates for Dirichlet polynomials"
* [Guth-Maynard, 2024] - "New large value estimates for Dirichlet polynomials"
-/

/--
Carlson's zero density estimate (1921): A(σ) ≤ 4σ for σ ∈ [1/2, 1].

This is the first non-trivial zero density result. At σ = 1/2, it gives
A ≤ 2, matching the density hypothesis. At σ = 1, it gives A ≤ 4.

**Reference**: Carlson (1921), "Über die Nullstellen der Dirichletschen Reihen
und der Riemannschen ζ-Funktion"
-/
axiom carlson_zero_density (σ : ℚ) (hσ₀ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) :
    IsZeroDensityBound (4 * σ) σ

/--
Ingham's zero density estimate (1940): A(σ) ≤ 3/(2-σ) for σ ∈ [1/2, 1).

This is one of the most important classical results. It improves on Carlson's
estimate for σ close to 1. At σ = 1/2, it gives A ≤ 2. It was a major
breakthrough in understanding the distribution of zeta zeros.

Note: The denominator 2-σ is positive for σ < 2, so the bound is well-defined
on [1/2, 1). At σ = 1, we take the limit A → 3.

**Reference**: Ingham (1940), "On the estimation of N(σ,T)"
-/
axiom ingham_zero_density (σ : ℚ) (hσ₀ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1)
    (hσ₂ : σ < 2) :
    IsZeroDensityBound (3 / (2 - σ)) σ

/--
Huxley's zero density estimate (1972): A(σ) ≤ 3/(3σ-1) for σ ∈ (1/2, 1].

This improves on Ingham's estimate for σ close to 1.
At σ = 1, A ≤ 3/2. At σ = 3/4, A ≤ 3/(9/4 - 1) = 3/(5/4) = 12/5.

Note: The denominator 3σ-1 is positive for σ > 1/3.

**Reference**: Huxley (1972), "On the difference between consecutive primes",
Invent. Math. 15, pages 164--170
-/
axiom huxley_zero_density (σ : ℚ) (hσ₀ : 1/2 < σ) (hσ₁ : σ ≤ 1) :
    IsZeroDensityBound (3 / (3 * σ - 1)) σ

/--
Heath-Brown's zero density estimate (1979): A(σ) ≤ 4/(4σ-1) for σ ∈ [25/28, 1].

This is one of the strongest estimates near σ = 1.
At σ = 25/28, A ≤ 4/(100/28 - 1) = 4/(72/28) = 112/72 = 14/9.

**Reference**: Heath-Brown (1979), "Zero Density Estimates for the Riemann
Zeta-Function and Dirichlet L-Functions", J. Lond. Math. Soc. s2-19, 221--232
-/
axiom heathbrown_zero_density (σ : ℚ) (hσ₀ : 25/28 ≤ σ) (hσ₁ : σ ≤ 1) :
    IsZeroDensityBound (4 / (4 * σ - 1)) σ

/--
Bourgain's zero density estimate (2000): A(σ) ≤ 2 for σ ∈ [25/32, 1].

This establishes the density hypothesis (A(σ) ≤ 2) for σ ≥ 25/32,
a significant achievement towards proving the full density hypothesis.

**Reference**: Bourgain (2000), "On large values estimates for Dirichlet
polynomials and the density hypothesis for the Riemann zeta function",
Internat. Math. Res. Notices, no. 3, pages 133--146
-/
axiom bourgain_zero_density (σ : ℚ) (hσ₀ : 25/32 ≤ σ) (hσ₁ : σ ≤ 1) :
    IsZeroDensityBound 2 σ

/--
Guth-Maynard zero density estimate (2024): A(σ) ≤ 15/(3+5σ) for σ ∈ [1/2, 1].

This is a breakthrough result using new large value estimates for Dirichlet
polynomials. At σ = 1/2, it gives A ≤ 15/(11/2) = 30/11 ≈ 2.727.
At σ = 1, it gives A ≤ 15/8 = 1.875.

**Reference**: Guth-Maynard (2024), "New large value estimates for Dirichlet
polynomials"
-/
axiom guth_maynard_zero_density (σ : ℚ) (hσ₀ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) :
    IsZeroDensityBound (15 / (3 + 5 * σ)) σ

/-!
## Numerical Verifications

These verify that specific evaluations of the bounds satisfy the geometric
constraints of `IsZeroDensityBound`.
-/

-- Carlson at σ = 3/4: A ≤ 4 · 3/4 = 3
example : IsZeroDensityBound 3 (3/4) := by unfold IsZeroDensityBound; norm_num

-- Ingham at σ = 3/4: A ≤ 3/(2-3/4) = 12/5
example : IsZeroDensityBound (12/5) (3/4) := by unfold IsZeroDensityBound; norm_num

-- Heath-Brown at σ = 25/28: A ≤ 4/(100/28-1) = 14/9
example : IsZeroDensityBound (14/9) (25/28) := by unfold IsZeroDensityBound; norm_num

-- Bourgain at σ = 25/32: A ≤ 2
example : IsZeroDensityBound 2 (25/32) := by unfold IsZeroDensityBound; norm_num

-- Guth-Maynard at σ = 1/2: A ≤ 30/11
example : IsZeroDensityBound (30/11) (1/2) := by unfold IsZeroDensityBound; norm_num

/-!
## Future Additions

As the formalization progresses, additional zero density estimates will be added:
* Montgomery (1971): A(σ) ≤ 1600(1-σ)^{1/2}
* Ivić (1979, 1980, 1984): Various estimates
* Jutila (1982): Estimates near the critical line
* Conrey (1989): Improved estimates
* Pintz (2023): Near σ = 1

These will be added following the same axiomatization pattern.
-/
