/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import expdb.Basic.ExponentPair
import expdb.Transforms.VanDerCorputA
import expdb.Transforms.VanDerCorputB

/-!
# Huxley-School Exponent Pairs

This file contains exponent pairs from the work of M.N. Huxley and collaborators,
particularly those arising from the Bombieri-Iwaniec method applied to exponential
sums. This includes results by Huxley, Watt, and Huxley-Kolesnik.

## Main Results

### Pairs on the symmetry line l = k + 1/2

* `huxley_pair_1988` - (9/56, 37/56)
* `watt_pair_1989` - (89/560, 369/560)
* `huxley_pair_1991` - (17/108, 71/108)
* `huxley_pair_1993` - (89/570, 187/285)
* `huxley_pair_2005` - (32/205, 269/410)

### Pairs off the symmetry line

* `huxleyWatt_pair_1990` - (2/13, 35/52)
* `huxley_pair_1996` - (6299/43860, 29507/43860)

## Implementation Notes

These results are axiomatized following the approach in the Python codebase
(`blueprint/src/python/literature.py`). All pairs on the symmetry line satisfy
l = k + 1/2, which means they are fixed points of the B-process.

## References

* [Huxley, 1988] - "Exponential sums and lattice points"
* [Watt, 1989] - "Exponential sums and the Riemann Zeta Function II"
* [Huxley-Watt, 1990] - "Exponential sums and the Riemann zeta function"
* [Huxley-Kolesnik, 1991] - "Exponential Sums and the Riemann Zeta Function III"
* [Huxley, 1993] - "Exponential sums and the Riemann Zeta Function IV"
* [Huxley, 1996] - "Area, Lattice Points and Exponential Sums"
* [Huxley, 2005] - "Exponential sums and the Riemann Zeta Function V"
-/

/-!
## Pairs on the Symmetry Line l = k + 1/2

These pairs all satisfy l = k + 1/2, which means the B-process maps them to
themselves: B(k, k+1/2) = (k+1/2-1/2, k+1/2) = (k, k+1/2).
-/

/--
The Huxley (1988) exponent pair (9/56, 37/56).

This pair lies on the symmetry line: 37/56 - 9/56 = 28/56 = 1/2.

**Reference**: Huxley (1988), "Exponential sums and lattice points"
-/
axiom huxley_pair_1988 : IsExponentPair (9/56) (37/56)

/-- Numerical verification. -/
example : IsExponentPair (9/56) (37/56) := by
  unfold IsExponentPair; norm_num

/--
The Watt (1989) exponent pair (89/560, 369/560).

This pair lies on the symmetry line: 369/560 - 89/560 = 280/560 = 1/2.

**Reference**: Watt (1989), "Exponential sums and the Riemann Zeta Function II"
-/
axiom watt_pair_1989 : IsExponentPair (89/560) (369/560)

/-- Numerical verification. -/
example : IsExponentPair (89/560) (369/560) := by
  unfold IsExponentPair; norm_num

/--
The Huxley-Kolesnik (1991) exponent pair (17/108, 71/108).

This pair lies on the symmetry line: 71/108 - 17/108 = 54/108 = 1/2.

**Reference**: Huxley-Kolesnik (1991), "Exponential Sums and the Riemann Zeta
Function III"
-/
axiom huxley_pair_1991 : IsExponentPair (17/108) (71/108)

/-- Numerical verification. -/
example : IsExponentPair (17/108) (71/108) := by
  unfold IsExponentPair; norm_num

/--
The Huxley (1993) exponent pair (89/570, 187/285).

This pair lies on the symmetry line: 187/285 - 89/570 = 374/570 - 89/570 = 285/570 = 1/2.

**Reference**: Huxley (1993), "Exponential sums and the Riemann Zeta Function IV"
-/
axiom huxley_pair_1993 : IsExponentPair (89/570) (187/285)

/-- Numerical verification. -/
example : IsExponentPair (89/570) (187/285) := by
  unfold IsExponentPair; norm_num

/--
The Huxley (2005) exponent pair (32/205, 269/410).

This pair lies on the symmetry line: 269/410 - 32/205 = 269/410 - 64/410 = 205/410 = 1/2.

**Reference**: Huxley (2005), "Exponential sums and the Riemann Zeta Function V"
-/
axiom huxley_pair_2005 : IsExponentPair (32/205) (269/410)

/-- Numerical verification. -/
example : IsExponentPair (32/205) (269/410) := by
  unfold IsExponentPair; norm_num

/-!
## Pairs Off the Symmetry Line

These pairs satisfy l > k + 1/2 and arise from the Bombieri-Iwaniec method.
-/

/--
The Huxley-Watt (1990) exponent pair (2/13, 35/52).

This pair satisfies l > k + 1/2: 35/52 - 2/13 = 35/52 - 8/52 = 27/52 > 1/2.

**Reference**: Huxley-Watt (1990), "Exponential sums and the Riemann zeta function"
-/
axiom huxleyWatt_pair_1990 : IsExponentPair (2/13) (35/52)

/-- Numerical verification. -/
example : IsExponentPair (2/13) (35/52) := by
  unfold IsExponentPair; norm_num

/--
The Huxley (1996) exponent pair (6299/43860, 29507/43860).

This is from the detailed analysis in "Area, Lattice Points and Exponential Sums",
Table 17.1.

**Reference**: Huxley (1996), "Area, Lattice Points and Exponential Sums"
-/
axiom huxley_pair_1996 : IsExponentPair (6299/43860) (29507/43860)

/-- Numerical verification. -/
example : IsExponentPair (6299/43860) (29507/43860) := by
  unfold IsExponentPair; norm_num

/-!
## Derived Pairs from Huxley

The Huxley pairs generate new exponent pairs when combined with the A and B transforms.
Note that pairs on the symmetry line l = k + 1/2 are fixed by B, so only A produces
new results from those pairs.
-/

/--
A(9/56, 37/56): applying the A-process to the Huxley 1988 pair.

Computation: A(9/56, 37/56) = ((9/56)/(2·(9/56)+2), (37/56)/(2·(9/56)+2) + 1/2)
           = ((9/56)/(65/28), (37/56)/(65/28) + 1/2)
           = (9/130, 37/130 + 1/2) = (9/130, 51/65)
-/
theorem huxley_1988_A : IsExponentPair (9/130) (51/65) :=
  huxley_pair_1988.ofA (by norm_num) (by norm_num)

/--
B(2/13, 35/52): applying the B-process to the Huxley-Watt 1990 pair.

Computation: B(2/13, 35/52) = (35/52 - 1/2, 2/13 + 1/2) = (9/52, 17/26)
-/
theorem huxleyWatt_1990_B : IsExponentPair (9/52) (17/26) :=
  huxleyWatt_pair_1990.ofB (by norm_num) (by norm_num)
