/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import expdb.Basic.ExponentPair
import expdb.Transforms.VanDerCorputA
import expdb.Transforms.VanDerCorputB

/-!
# Heath-Brown Exponent Pairs

This file contains exponent pairs from the work of D.R. Heath-Brown, particularly
the parametric family from his 2017 paper on new exponent pairs.

## Main Results

* `heathBrown_pair_m3` - The Heath-Brown pair (1/10, 23/30) for m=3
* `heathBrown_pair_m4` - The Heath-Brown pair (1/27, 31/36) for m=4
* `heathBrown_pair_m5` - The Heath-Brown pair (1/56, 127/140) for m=5

## Implementation Notes

These results are axiomatized following the approach in the Python codebase
(`blueprint/src/python/literature.py`). The pairs come from the parametric family
  k = 2/((m-1)²(m+2)), l = 1 - (3m-2)/(m(m-1)(m+2))
for integers m ≥ 3.

## References

* [Heath-Brown, 2017] - "New exponent pairs"
* Graham-Kolesnik (1991) - For the general framework of exponent pairs
-/

/--
The Heath-Brown exponent pair (1/10, 23/30) for m=3.

From the parametric family k = 2/((m-1)²(m+2)), l = 1 - (3m-2)/(m(m-1)(m+2)):
  k = 2/(2²·5) = 2/20 = 1/10
  l = 1 - 7/(3·2·5) = 1 - 7/30 = 23/30

The pair satisfies the geometric constraints:
- 0 ≤ 1/10 ≤ 1/2
- 1/2 ≤ 23/30 ≤ 1
- 1/10 + 23/30 = 26/30 = 13/15 ≤ 1

**Reference**: Heath-Brown (2017), "New exponent pairs"
-/
axiom heathBrown_pair_m3 : IsExponentPair (1/10) (23/30)

/-- Numerical verification that the Heath-Brown m=3 pair lies in the triangle. -/
example : IsExponentPair (1/10) (23/30) := by
  unfold IsExponentPair; norm_num

/--
The Heath-Brown exponent pair (1/27, 31/36) for m=4.

From the parametric family:
  k = 2/(3²·6) = 2/54 = 1/27
  l = 1 - 10/(4·3·6) = 1 - 10/72 = 62/72 = 31/36

**Reference**: Heath-Brown (2017), "New exponent pairs"
-/
axiom heathBrown_pair_m4 : IsExponentPair (1/27) (31/36)

/-- Numerical verification that the Heath-Brown m=4 pair lies in the triangle. -/
example : IsExponentPair (1/27) (31/36) := by
  unfold IsExponentPair; norm_num

/--
The Heath-Brown exponent pair (1/56, 127/140) for m=5.

From the parametric family:
  k = 2/(4²·7) = 2/112 = 1/56
  l = 1 - 13/(5·4·7) = 1 - 13/140 = 127/140

**Reference**: Heath-Brown (2017), "New exponent pairs"
-/
axiom heathBrown_pair_m5 : IsExponentPair (1/56) (127/140)

/-- Numerical verification that the Heath-Brown m=5 pair lies in the triangle. -/
example : IsExponentPair (1/56) (127/140) := by
  unfold IsExponentPair; norm_num

/-!
## Derived Pairs from Heath-Brown

The Heath-Brown pairs generate new exponent pairs when combined with the
A and B transforms.
-/

/--
B(1/10, 23/30): applying the B-process to the Heath-Brown m=3 pair.

Computation: B(1/10, 23/30) = (23/30 - 1/2, 1/10 + 1/2) = (8/30, 6/10) = (4/15, 3/5)
-/
theorem heathBrown_m3_B : IsExponentPair (4/15) (3/5) :=
  heathBrown_pair_m3.ofB (by norm_num) (by norm_num)

/--
A(1/10, 23/30): applying the A-process to the Heath-Brown m=3 pair.

Computation: A(1/10, 23/30) = ((1/10)/(2·(1/10)+2), (23/30)/(2·(1/10)+2) + 1/2)
           = ((1/10)/(11/5), (23/30)/(11/5) + 1/2)
           = (1/22, 23/66 + 1/2) = (1/22, 28/33)
-/
theorem heathBrown_m3_A : IsExponentPair (1/22) (28/33) :=
  heathBrown_pair_m3.ofA (by norm_num) (by norm_num)
