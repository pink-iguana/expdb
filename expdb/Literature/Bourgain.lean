/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import expdb.Basic.ExponentPair
import expdb.Transforms.VanDerCorputA
import expdb.Transforms.VanDerCorputB

/-!
# Bourgain Exponent Pairs

This file contains exponent pairs from the work of Jean Bourgain and collaborators,
particularly the breakthrough result using decoupling techniques.

## Main Results

* `bourgain_pair` - The Bourgain (2017) exponent pair (13/84, 55/84)

## Implementation Notes

These results are axiomatized following the approach in the Python codebase
(`blueprint/src/python/literature.py`).

## References

* [Bourgain, 2017] - "Decoupling, exponential sums and the Riemann zeta function"
  (J. Amer. Math. Soc. 30 (2017), 205-224)
-/

/--
The Bourgain exponent pair (13/84, 55/84) from decoupling theory.

This is one of the best known exponent pairs, obtained through Bourgain's
work on decoupling inequalities. It lies on the symmetry line l = k + 1/2,
since 55/84 - 13/84 = 42/84 = 1/2.

The pair satisfies the geometric constraints:
- 0 ≤ 13/84 ≤ 1/2
- 1/2 ≤ 55/84 ≤ 1
- 13/84 + 55/84 = 68/84 = 17/21 ≤ 1

**Reference**: Bourgain (2017), "Decoupling, exponential sums and the Riemann
zeta function", J. Amer. Math. Soc. 30, 205-224
-/
axiom bourgain_pair : IsExponentPair (13/84) (55/84)

/--
Numerical verification that the Bourgain pair lies in the exponent pair triangle.
-/
example : IsExponentPair (13/84) (55/84) := by
  unfold IsExponentPair; norm_num

/-!
## Derived Pairs from Bourgain

The Bourgain pair generates new exponent pairs when combined with the
A and B transforms. Some useful derived pairs:
-/

/--
A(13/84, 55/84): applying the A-process to the Bourgain pair.

Computation: A(13/84, 55/84) = (13/84)/(2·(13/84)+2), (55/84)/(2·(13/84)+2)+1/2)
           = (13/84)/(97/42), (55/84)/(97/42)+1/2)
           = (13/194, 55/194 + 1/2)
           = (13/194, 152/194)
           = (13/194, 76/97)
-/
theorem bourgain_A : IsExponentPair (13/194) (76/97) :=
  bourgain_pair.ofA (by norm_num) (by norm_num)

/--
B(13/84, 55/84): applying the B-process to the Bourgain pair.

Since 55/84 - 13/84 = 1/2, the B-transform maps the Bourgain pair to itself:
B(13/84, 55/84) = (55/84 - 1/2, 13/84 + 1/2) = (13/84, 55/84)

This is because the Bourgain pair lies on the symmetry line l = k + 1/2,
which is the set of fixed points of the B-process.
-/
theorem bourgain_B_fixed : IsExponentPair (13/84) (55/84) :=
  bourgain_pair.ofB (by norm_num) (by norm_num)
