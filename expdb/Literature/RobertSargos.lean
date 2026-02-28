/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import expdb.Basic.ExponentPair
import expdb.Transforms.VanDerCorputA
import expdb.Transforms.VanDerCorputB

/-!
# Robert-Sargos Exponent Pairs

This file contains exponent pairs from the work of O. Robert and P. Sargos,
particularly those arising from k-th derivative tests for exponential sums.

## Main Results

* `robert_pair_2002` - (1/13, 10/13) from 4th derivative test
* `sargos_pair_2003a` - (1/204, 197/204)
* `robert_pair_2002a` - (1/360, 44/45)
* `robertSargos_pair_2001` - (1/649, 640/649)
* `robert_pair_2002b` - (1/615, 202/205)
* `robert_pair_2002c` - (1/915, 181/183)

## Implementation Notes

These results are axiomatized following the approach in the Python codebase
(`blueprint/src/python/literature.py`). The pairs arise from higher-order
derivative tests, which give exponent pairs with very small k and l close to 1.
These are particularly useful for applications to the Riemann zeta function.

## References

* [Robert-Sargos, 2001] - "Un théorème de moyenne pour les sommes d'exponentielles"
* [Robert, 2002] - "Fourth derivative test for exponential sums"
* [Sargos, 2003] - "An analog of van der Corput's A₅-process"
* [Robert, 2002b] - "On van der Corput's k-th derivative test for exponential sums"
-/

/--
The Robert (2002) exponent pair (1/13, 10/13) from the 4th derivative test.

This pair has the notable property that k + l = 11/13 < 1, giving
a significant gap from the boundary k + l = 1 of the triangle.

**Reference**: Robert (2002), "Fourth derivative test for exponential sums"
-/
axiom robert_pair_2002 : IsExponentPair (1/13) (10/13)

/-- Numerical verification. -/
example : IsExponentPair (1/13) (10/13) := by
  unfold IsExponentPair; norm_num

/--
The Sargos (2003) exponent pair (1/204, 197/204).

From an analog of van der Corput's A₅-process.

**Reference**: Sargos (2003), "An analog of van der Corput's A₅-process"
-/
axiom sargos_pair_2003a : IsExponentPair (1/204) (197/204)

/-- Numerical verification. -/
example : IsExponentPair (1/204) (197/204) := by
  unfold IsExponentPair; norm_num

/--
The Robert (2002) exponent pair (1/360, 44/45).

This is 1 - 8/360 = 352/360 = 44/45 for the l coordinate.

**Reference**: Robert (2002)
-/
axiom robert_pair_2002a : IsExponentPair (1/360) (44/45)

/-- Numerical verification. -/
example : IsExponentPair (1/360) (44/45) := by
  unfold IsExponentPair; norm_num

/--
The Robert-Sargos (2001) exponent pair (1/649, 640/649).

**Reference**: Robert-Sargos (2001), "Un théorème de moyenne pour les
sommes d'exponentielles"
-/
axiom robertSargos_pair_2001 : IsExponentPair (1/649) (640/649)

/-- Numerical verification. -/
example : IsExponentPair (1/649) (640/649) := by
  unfold IsExponentPair; norm_num

/--
The Robert (2002b) exponent pair (1/615, 202/205).

This is 1 - 9/615 = 606/615 = 202/205 for the l coordinate.

**Reference**: Robert (2002b), "On van der Corput's k-th derivative test
for exponential sums"
-/
axiom robert_pair_2002b : IsExponentPair (1/615) (202/205)

/-- Numerical verification. -/
example : IsExponentPair (1/615) (202/205) := by
  unfold IsExponentPair; norm_num

/--
The Robert (2002b) exponent pair (1/915, 181/183).

This is 1 - 10/915 = 905/915 = 181/183 for the l coordinate.

**Reference**: Robert (2002b), "On van der Corput's k-th derivative test
for exponential sums"
-/
axiom robert_pair_2002c : IsExponentPair (1/915) (181/183)

/-- Numerical verification. -/
example : IsExponentPair (1/915) (181/183) := by
  unfold IsExponentPair; norm_num

/-!
## Derived Pairs from Robert-Sargos

These pairs have very small k, so the A-process yields pairs with even smaller k,
while the B-process swaps coordinates.
-/

/--
B(1/13, 10/13): applying the B-process to the Robert 2002 pair.

Computation: B(1/13, 10/13) = (10/13 - 1/2, 1/13 + 1/2) = (7/26, 15/26)
-/
theorem robert_2002_B : IsExponentPair (7/26) (15/26) :=
  robert_pair_2002.ofB (by norm_num) (by norm_num)

/--
A(1/13, 10/13): applying the A-process to the Robert 2002 pair.

Computation: A(1/13, 10/13) = ((1/13)/(2/13+2), (10/13)/(2/13+2) + 1/2)
           = ((1/13)/(28/13), (10/13)/(28/13) + 1/2)
           = (1/28, 10/28 + 1/2) = (1/28, 6/7)
-/
theorem robert_2002_A : IsExponentPair (1/28) (6/7) :=
  robert_pair_2002.ofA (by norm_num) (by norm_num)
