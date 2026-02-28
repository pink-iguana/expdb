/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import expdb.Basic.ExponentPair

/-!
# Classical Exponent Pairs

This file contains the classical exponent pairs from the literature, particularly
those derived from the foundational work of Weyl and van der Corput in the 1920s.

## Main Results

* `trivial_pair` - The trivial exponent pair (0, 1)
* `weyl_pair` - The Weyl exponent pair (1/2, 1/2)
* `classical_vdc_pair` - The classical van der Corput pair (1/6, 2/3)

## Implementation Notes

These results are currently axiomatized, following the approach in the Python
codebase where literature results are taken as given. Future work may formalize
the underlying exponential sum estimates, but this is not necessary for the
initial formalization goals (see `LEAN.md`).

The axiomatization strategy mirrors the `literature.py` module in the Python code,
where results are recorded with their references but not re-proved.

## References

* [Weyl, 1916] - "Über die Gleichverteilung von Zahlen mod Eins"
* [van der Corput, 1920s] - Original exponent pair work
* [Graham-Kolesnik, 1991] - "van der Corput's Method of Exponential Sums", Section 2.2
-/

/--
The trivial exponent pair (0, 1).

This follows from the triangle inequality: for any exponential sum S(N),
  |S(N)| ≤ N^(0+ε) + N^(1+ε) = O(N)
which is trivially true since S(N) is a sum of O(N) terms.

**Reference**: Folklore; appears in all textbooks on exponential sums.
-/
axiom trivial_pair : IsExponentPair 0 1

/--
The Weyl exponent pair (1/2, 1/2).

This is the famous result of Hermann Weyl on equidistribution and exponential sums
over polynomial sequences. It gives the bound
  |∑ₙ e^(2πi f(n))| ≤ N^(1/2+ε)
for polynomials f of degree ≥ 2.

**Reference**: Weyl (1916), "Über die Gleichverteilung von Zahlen mod Eins"
-/
axiom weyl_pair : IsExponentPair (1/2) (1/2)

/--
The classical van der Corput exponent pair (1/6, 2/3).

This is derived by applying Weyl differencing (the A-process) to the trivial pair,
giving (0, 1) → (0, 1/2), and then applying the B-process to get (1/6, 2/3).
More precisely: BA^2(0,1) = (1/6, 2/3).

This pair is optimal for certain exponential sums over smooth functions and
represents a fundamental improvement over Weyl's estimate in many applications.

**Reference**: van der Corput (1920s); See Graham-Kolesnik (1991), Theorem 2.2
-/
axiom classical_vdc_pair : IsExponentPair (1/6) (2/3)

/-!
## Future Additions

As the formalization progresses, additional classical pairs will be added:
* (1/5, 37/50) - Heath-Brown (1979)
* (53/342, 55/114) - Huxley (1996)
* (13/84, 55/84) - Bourgain (2017)

These will be added to separate files (`HeathBrown.lean`, `Huxley.lean`, `Bourgain.lean`)
to maintain organization and make references clear.
-/
