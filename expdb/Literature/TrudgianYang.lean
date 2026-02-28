/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import expdb.Basic.ExponentPair
import expdb.Transforms.VanDerCorputA
import expdb.Transforms.VanDerCorputB

/-!
# Trudgian-Yang Exponent Pairs

This file contains exponent pairs from the recent work of Trudgian and Yang (2025),
which introduces new exponent pairs using systematic optimization methods.

## Main Results

* `trudgianYang_pair_1` - (4742/38463, 35731/51284)
* `trudgianYang_pair_2` - (18/199, 593/796)
* `trudgianYang_pair_3` - (2779/38033, 58699/76066)
* `trudgianYang_pair_4` - (715/10238, 7955/10238)

## Implementation Notes

These results are axiomatized following the approach in the Python codebase
(`blueprint/src/python/literature.py`).

## References

* [Trudgian-Yang, 2025] - T. Tao, T. Trudgian, A. Yang, "New exponent pairs,
  zero density estimates, and zero additive energy estimates: a systematic approach"
-/

/--
The Trudgian-Yang (2025) exponent pair (4742/38463, 35731/51284).

**Reference**: Trudgian-Yang (2025)
-/
axiom trudgianYang_pair_1 : IsExponentPair (4742/38463) (35731/51284)

/-- Numerical verification. -/
example : IsExponentPair (4742/38463) (35731/51284) := by
  unfold IsExponentPair; norm_num

/--
The Trudgian-Yang (2025) exponent pair (18/199, 593/796).

This is the cleanest Trudgian-Yang pair in terms of denominator size.

**Reference**: Trudgian-Yang (2025)
-/
axiom trudgianYang_pair_2 : IsExponentPair (18/199) (593/796)

/-- Numerical verification. -/
example : IsExponentPair (18/199) (593/796) := by
  unfold IsExponentPair; norm_num

/--
The Trudgian-Yang (2025) exponent pair (2779/38033, 58699/76066).

**Reference**: Trudgian-Yang (2025)
-/
axiom trudgianYang_pair_3 : IsExponentPair (2779/38033) (58699/76066)

/-- Numerical verification. -/
example : IsExponentPair (2779/38033) (58699/76066) := by
  unfold IsExponentPair; norm_num

/--
The Trudgian-Yang (2025) exponent pair (715/10238, 7955/10238).

**Reference**: Trudgian-Yang (2025)
-/
axiom trudgianYang_pair_4 : IsExponentPair (715/10238) (7955/10238)

/-- Numerical verification. -/
example : IsExponentPair (715/10238) (7955/10238) := by
  unfold IsExponentPair; norm_num

/-!
## Derived Pairs from Trudgian-Yang

The Trudgian-Yang pairs generate new exponent pairs when combined with transforms.
-/

/--
B(18/199, 593/796): applying the B-process to the cleanest Trudgian-Yang pair.

Computation: B(18/199, 593/796) = (593/796 - 1/2, 18/199 + 1/2)
           = (195/796, 235/398)
-/
theorem trudgianYang_pair_2_B : IsExponentPair (195/796) (235/398) :=
  trudgianYang_pair_2.ofB (by norm_num) (by norm_num)
