/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import expdb.Basic.LargeValueEstimate

/-!
# Large Value Estimate: Raise to Power Transform

The raise-to-power transform is a fundamental operation on large value estimates.
Given a large value estimate LV(σ, τ) ≤ ρ and a positive rational k, we obtain:
  LV(σ, k·τ) ≤ k·ρ

This corresponds to raising the Dirichlet polynomial to the k-th power, which
scales both the threshold parameter τ and the measure bound ρ by the factor k.

## Main Results

* `large_value_raise_to_power` — The raise-to-power transform axiom

## Implementation Notes

This axiom mirrors the `raise_to_power_hypothesis` function in the Python code
(`large_values.py`), which creates a `Large_Value_Estimate_Transform` that
scales the region by `[1, k, k]` in (σ, τ, ρ) space.

In the Python code, this transform is applied to existing large value estimates
to produce new estimates with scaled parameters. In Lean, we axiomatize this
as a theorem relating the original and scaled parameters.

## References

* Classical result in analytic number theory
* See `blueprint/src/python/large_values.py`, function `raise_to_power_hypothesis`
-/

/--
Raise-to-power transform for large value estimates.

If LV(σ, τ) ≤ ρ is a valid large value estimate and k > 0, then
LV(σ, k·τ) ≤ k·ρ is also a valid large value estimate.

This corresponds to raising the Dirichlet polynomial to the k-th power.

**Python equivalent**: `raise_to_power_hypothesis(k)` in `large_values.py`,
which creates a transform scaling (σ, τ, ρ) by [1, k, k].

**Reference**: Classical; see e.g. the discussion in the ANTEDB blueprint.
-/
axiom large_value_raise_to_power (σ τ ρ k : ℚ)
    (h : LargeValueEstimate σ τ ρ) (hk : 0 < k) :
    LargeValueEstimate σ (k * τ) (k * ρ)

namespace LargeValueEstimate

/-- Helper: apply the raise-to-power transform and simplify.
    Given `LargeValueEstimate σ τ ρ`, produce `LargeValueEstimate σ τ' ρ'`
    where `τ' = k * τ` and `ρ' = k * ρ`, with equalities discharged by
    the caller (typically via `norm_num`). -/
theorem ofRaisePower {σ τ ρ k τ' ρ' : ℚ}
    (h : LargeValueEstimate σ τ ρ) (hk : 0 < k)
    (hτ : τ' = k * τ) (hρ : ρ' = k * ρ) :
    LargeValueEstimate σ τ' ρ' := by
  rw [hτ, hρ]; exact large_value_raise_to_power σ τ ρ k h hk

end LargeValueEstimate

/-!
## Properties and Examples
-/

namespace LargeValueRaisePower

/--
Raising to the power k = 1 is the identity (the parameters are unchanged).

This is a sanity check: scaling by 1 should give back the same estimate.
-/
example {σ τ ρ : ℚ} (h : LargeValueEstimate σ τ ρ) :
    LargeValueEstimate σ τ ρ :=
  h.ofRaisePower (by norm_num : (0:ℚ) < 1) (by ring) (by ring)

/--
Raising to the power k = 2 doubles both τ and ρ.

Example: if LV(3/4, 1) ≤ 1/2, then LV(3/4, 2) ≤ 1.
-/
example (h : LargeValueEstimate (3/4) 1 (1/2)) :
    LargeValueEstimate (3/4) 2 1 :=
  h.ofRaisePower (by norm_num : (0:ℚ) < 2) (by norm_num) (by norm_num)

end LargeValueRaisePower

/-!
## Future Work

* Axiomatize additional transforms that connect large value estimates to
  other exponent types (e.g., zero density estimates)
* Formalize the Huxley subdivision transform
* Connect large value estimates to exponent pairs via the ANTEDB derivation chains
-/
