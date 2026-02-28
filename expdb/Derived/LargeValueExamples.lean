/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import expdb.Literature.LargeValues
import expdb.Transforms.LargeValueRaisePower

/-!
# Derived Large Value Estimates - Examples

This file contains examples of large value estimates derived from literature
results by applying transforms. Each theorem corresponds to a derivation
chain that can be computed by the Python code in `blueprint/src/python/`.

These examples serve the same purposes as `Derived/Examples.lean`:
1. Demonstrate the Lean formalization of large value estimates in action
2. Validate that Python derivations can be translated to Lean proofs
3. Provide a test suite for the formalization
4. Showcase the proof patterns

## Main Results

We prove several derived large value estimates:
* Raise-to-power applied to L² bounds
* Specific numerical instances at particular (σ, τ) values
* Comparison of different literature bounds at the same point

## References

These derivations match those in the ANTEDB Python code. See:
* `blueprint/src/python/large_values.py` - Large value estimate classes
* `blueprint/src/python/literature.py` - Literature axioms
-/

/-!
## Instantiations of Literature Bounds

These theorems instantiate the literature axioms at specific rational points,
demonstrating that the bounds give concrete numerical results.
-/

/--
The L² bound at σ = 3/4: ρ ≤ 2 − 2·(3/4) = 1/2.

This is the first branch of the L² mean value theorem, evaluated at σ = 3/4.
The bound is independent of τ.
-/
theorem large_value_at_3_4_branch1 (τ : ℚ) (hτ : 0 ≤ τ) :
    LargeValueEstimate (3/4) τ (1/2) :=
  large_value_L2_branch1 (3/4) τ (by norm_num) (by norm_num) hτ (by norm_num)

/--
The L² second branch at σ = 3/4, τ = 1: ρ ≤ 1 − 2·(3/4) + 1 = 1/2.

At this point, both branches of the L² estimate give the same value.
-/
theorem large_value_at_3_4_L2_branch2 :
    LargeValueEstimate (3/4) 1 (1/2) :=
  large_value_L2_branch2 (3/4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/--
Huxley's bound at σ = 3/4, τ = 2: ρ ≤ 4 − 6·(3/4) + 2 = 3/2.
-/
theorem large_value_huxley_at_3_4_tau_2 :
    LargeValueEstimate (3/4) 2 (3/2) :=
  large_value_huxley (3/4) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/--
Heath-Brown's bound at σ = 5/6, τ = 1: ρ ≤ 10 − 13·(5/6) + 1 = 1/6.
-/
theorem large_value_heath_brown_at_5_6 :
    LargeValueEstimate (5/6) 1 (1/6) :=
  large_value_heath_brown (5/6) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-!
## Raise-to-Power Derivations

These theorems demonstrate the raise-to-power transform applied to literature bounds.
-/

/--
Applying the raise-to-power transform with k = 2 to the L² bound at σ = 3/4:
If LV(3/4, τ) ≤ 1/2, then LV(3/4, 2τ) ≤ 1.

This demonstrates composing a literature axiom with a transform.
-/
theorem large_value_L2_raised_k2 (τ : ℚ) (hτ : 0 ≤ τ) :
    LargeValueEstimate (3/4) (2 * τ) 1 :=
  (large_value_at_3_4_branch1 τ hτ).ofRaisePower (by norm_num : (0:ℚ) < 2)
    (by ring) (by norm_num)

/--
Chain derivation: L² bound at σ = 3/4, τ = 1, raised to power k = 3.

Step 1: L²(3/4, 1) gives ρ ≤ 1/2
Step 2: Raise to power 3: LV(3/4, 3) ≤ 3/2

This matches the pattern in the Python code where `raise_to_power_hypothesis(3)`
is applied to an existing large value estimate.
-/
theorem large_value_L2_raised_k3_example :
    LargeValueEstimate (3/4) 3 (3/2) := by
  have h1 : LargeValueEstimate (3/4) 1 (1/2) :=
    large_value_L2_branch1 (3/4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h1.ofRaisePower (by norm_num : (0:ℚ) < 3) (by norm_num) (by norm_num)

/--
Guth-Maynard bound at σ = 3/4: ρ ≤ 18/5 − 4·(3/4) = 18/5 − 3 = 3/5.

The second branch of the Guth-Maynard estimate, which is independent of τ.
-/
theorem large_value_guth_maynard_at_3_4 (τ : ℚ) (hτ : 0 ≤ τ) :
    LargeValueEstimate (3/4) τ (3/5) :=
  large_value_guth_maynard_branch2 (3/4) τ (by norm_num) (by norm_num) hτ (by norm_num)

/--
Guth-Maynard third branch at σ = 3/4, τ = 1: ρ ≤ 1 + 12/5 − 4·(3/4) = 17/5 − 3 = 2/5.

For this particular (σ, τ), the third branch gives a better bound than the second.
-/
theorem large_value_guth_maynard_branch3_at_3_4 :
    LargeValueEstimate (3/4) 1 (2/5) :=
  large_value_guth_maynard_branch3 (3/4) 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-!
## Future Work

As the formalization progresses, this file will be expanded with:

1. **More instantiations**: Evaluating all literature bounds at key rational points
2. **Transform chains**: Composing multiple transforms (raise-to-power, subdivision)
3. **Comparison proofs**: Formally showing which bound dominates in which region
4. **Connection to zero density**: Derivations that connect large value estimates
   to zero density estimates via the transforms in `zero_density_estimate.py`
-/
