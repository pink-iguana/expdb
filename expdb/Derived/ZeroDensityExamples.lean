/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import expdb.Literature.Classical
import expdb.Literature.ZeroDensityClassical
import expdb.Transforms.VanDerCorputA
import expdb.Transforms.VanDerCorputB
import expdb.Transforms.ExponentPairToZeroDensity

/-!
# Derived Zero Density Estimates - Examples

This file contains examples of zero density estimates derived from literature
results and exponent pairs by applying transforms. Each theorem corresponds to
a derivation that can be computed by the Python code in
`blueprint/src/python/zero_density_estimate.py`.

These examples serve multiple purposes:
1. Demonstrate the zero density formalization in action
2. Validate that Python derivations can be translated to Lean proofs
3. Showcase the derivation chains connecting exponent pairs to zero density

## Main Results

We demonstrate several derivation patterns:
* Direct instantiation of classical zero density axioms at specific σ values
* Application of Ivić's transform to known exponent pairs
* Chains combining A/B transforms with Ivić's EP→ZD transform

## References

* `blueprint/src/python/zero_density_estimate.py` - Python implementation
* `blueprint/src/python/literature.py` - Chapter 11: zero density estimates
-/

/-!
## Direct Instantiation of Classical Bounds

These show specific evaluations of the classical zero density axioms.
-/

/--
Carlson's bound at σ = 3/4: A(3/4) ≤ 4 · 3/4 = 3.

This is a direct instantiation of Carlson's 1921 zero density theorem.
-/
theorem carlson_at_3_4 : IsZeroDensityBound 3 (3/4) :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/--
Carlson's bound at σ = 1/2: A(1/2) ≤ 4 · 1/2 = 2.

At the critical line, Carlson's bound gives A = 2, matching the density hypothesis.
-/
theorem carlson_at_1_2 : IsZeroDensityBound 2 (1/2) :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/--
Ingham's bound at σ = 3/4: A(3/4) ≤ 3/(2-3/4) = 3/(5/4) = 12/5.

This improves on Carlson's A = 3 at σ = 3/4.
-/
theorem ingham_at_3_4 : IsZeroDensityBound (12/5) (3/4) :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/--
Ingham's bound at σ = 1/2: A(1/2) ≤ 3/(2-1/2) = 3/(3/2) = 2.

At the critical line, Ingham's bound also gives A = 2.
-/
theorem ingham_at_1_2 : IsZeroDensityBound 2 (1/2) :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/--
Heath-Brown's bound at σ = 15/16: A(15/16) ≤ 4/(4·15/16-1) = 4/(60/16-1) = 4/(44/16) = 16/11.
-/
theorem heathbrown_at_15_16 : IsZeroDensityBound (16/11) (15/16) :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/--
Bourgain's density hypothesis for σ = 7/8: A(7/8) ≤ 2.

Since 7/8 = 28/32 ≥ 25/32, Bourgain's 2000 result applies.
-/
theorem bourgain_density_at_7_8 : IsZeroDensityBound 2 (7/8) :=
  bourgain_zero_density (7/8) (by norm_num) (by norm_num)

/--
Guth-Maynard bound at σ = 1/2: A(1/2) ≤ 15/(3+5/2) = 15/(11/2) = 30/11.

While not as strong as Ingham or Carlson at σ = 1/2, the Guth-Maynard bound
is stronger for σ closer to 1.
-/
theorem guth_maynard_at_1_2 : IsZeroDensityBound (30/11) (1/2) :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/--
Guth-Maynard bound at σ = 3/4: A(3/4) ≤ 15/(3+15/4) = 15/(27/4) = 60/27 = 20/9.
-/
theorem guth_maynard_at_3_4 : IsZeroDensityBound (20/9) (3/4) :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/-!
## Exponent Pair to Zero Density Chains

These derive zero density bounds from exponent pairs using the Ivić transform.
-/

/--
Ivić's transform applied to the classical pair (1/6, 2/3) at σ = 5/6.

Chain: Classical EP (1/6, 2/3) → via Ivić (m=2) → A(5/6) ≤ 3/(2·5/6) = 9/5

Lower bound verification: (12 + 18·1/6 + 22·2/3) / (16 + 22·1/6 + 26·2/3)
= (12 + 3 + 44/3) / (16 + 11/3 + 52/3) = (89/3) / (111/3) = 89/111 ≈ 0.802
Since σ = 5/6 ≈ 0.833 > 89/111 ≈ 0.802, the bound is valid.
-/
theorem ivic_from_classical_vdc_at_5_6 : IsZeroDensityBound (9/5) (5/6) :=
  classical_vdc_pair.toZeroDensityIvic (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/--
Ivić's transform applied to Weyl's pair (1/2, 1/2) at σ = 9/10.

Chain: Weyl EP (1/2, 1/2) → via Ivić (m=2) → A(9/10) ≤ 3/(2·9/10) = 5/3

Lower bound: (12 + 9 + 11) / (16 + 11 + 13) = 32/40 = 4/5
Since σ = 9/10 > 4/5, the bound is valid.
-/
theorem ivic_from_weyl_at_9_10 : IsZeroDensityBound (5/3) (9/10) :=
  weyl_pair.toZeroDensityIvic (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/--
Ivić's transform applied directly to the trivial pair (0, 1) at σ = 6/7.

Chain: Trivial EP (0, 1) → via Ivić (m=2) → A(6/7) ≤ 3/(2·6/7) = 7/4

Lower bound for (0, 1): (12 + 0 + 22) / (16 + 0 + 26) = 34/42 = 17/21 ≈ 0.810
Since σ = 6/7 ≈ 0.857 > 17/21 ≈ 0.810, the bound is valid.
-/
theorem ivic_from_trivial_at_6_7 : IsZeroDensityBound (7/4) (6/7) :=
  trivial_pair.toZeroDensityIvic (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-!
## Combined Transform Chains

These combine A/B transforms on exponent pairs with the Ivić EP→ZD transform,
demonstrating the full derivation chain from basic exponent pairs to zero density bounds.
-/

/--
Chain: Weyl → A → Ivić zero density.

(1/2, 1/2) →A→ (1/6, 2/3) → Ivić(m=2) → A(5/6) ≤ 9/5

This derives the same bound as `ivic_from_classical_vdc_at_5_6` but starting
from Weyl's pair, showing the full dependency tree.
-/
theorem zd_chain_weyl_A_ivic : IsZeroDensityBound (9/5) (5/6) := by
  -- First derive (1/6, 2/3) = A(1/2, 1/2)
  have h1 : IsExponentPair (1/6) (2/3) := weyl_pair.ofA (by norm_num) (by norm_num)
  -- Then apply Ivić's EP→ZD transform
  exact h1.toZeroDensityIvic (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/--
Chain: Trivial → B → A → Ivić zero density.

(0, 1) →B→ (1/2, 1/2) →A→ (1/6, 2/3) → Ivić(m=2) → A(5/6) ≤ 9/5

This derives the zero density bound starting from the trivial pair,
demonstrating the full dependency tree computed by the Python code.

```
- [Derived zero density estimate A ≤ 9/5 at σ = 5/6]. Follows from:
  - [Ivić EP→ZD transform (m=2)]
  - [Derived exponent pair (1/6, 2/3)]. Follows from:
    - [van der Corput A transform]
    - [Derived exponent pair (1/2, 1/2)]. Follows from:
      - [van der Corput B transform]
      - [Trivial exponent pair (0, 1)]
```
-/
theorem zd_chain_trivial_BA_ivic : IsZeroDensityBound (9/5) (5/6) := by
  -- (0, 1) →B→ (1/2, 1/2)
  have h1 : IsExponentPair (1/2) (1/2) := trivial_pair.ofB (by norm_num) (by norm_num)
  -- (1/2, 1/2) →A→ (1/6, 2/3)
  have h2 : IsExponentPair (1/6) (2/3) := h1.ofA (by norm_num) (by norm_num)
  -- Apply Ivić's transform at σ = 5/6
  exact h2.toZeroDensityIvic (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/--
Chain: Classical → A → Ivić zero density.

(1/6, 2/3) →A→ (1/14, 11/14) → Ivić(m=2) → A(σ) ≤ 3/(2σ)

Lower bound for (1/14, 11/14): (12 + 18/14 + 22·11/14) / (16 + 22/14 + 26·11/14)
= (214/7) / 38 = 107/133 ≈ 0.804

At σ = 6/7 ≈ 0.857 > 107/133: A(6/7) ≤ 3/(12/7) = 7/4
-/
theorem zd_chain_classical_A_ivic : IsZeroDensityBound (7/4) (6/7) := by
  -- (1/6, 2/3) →A→ (1/14, 11/14)
  have h1 : IsExponentPair (1/14) (11/14) :=
    classical_vdc_pair.ofA (by norm_num) (by norm_num)
  -- Apply Ivić's transform at σ = 6/7
  exact h1.toZeroDensityIvic (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/--
Monotonicity example: improving a bound.

If we know A(3/4) ≤ 12/5 from Ingham, then certainly A(3/4) ≤ 3
(a weaker but sometimes more convenient bound).
-/
theorem ingham_weakened_at_3_4 : IsZeroDensityBound 3 (3/4) :=
  ingham_at_3_4.mono (by norm_num)

/-!
## Future Work

As the formalization progresses, this file will be expanded with:

1. **More derived bounds**: Using additional exponent pairs from `derived.py`
2. **Bourgain EP→ZD examples**: Once appropriate exponent pairs with k ≤ 1/5 are derived
3. **Comparison theorems**: Showing which bounds are tighter at various σ values
4. **Systematic derivations**: Matching all derivations in `zero_density_estimate.py`
5. **Convex combinations**: Using convexity to derive additional bounds
-/
