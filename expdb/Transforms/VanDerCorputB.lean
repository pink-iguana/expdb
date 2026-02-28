/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import expdb.Basic.ExponentPair

/-!
# Van der Corput B-Process

The van der Corput B-process (or B-transform) is the second fundamental operation on
exponent pairs. It transforms an exponent pair (k, l) into a new exponent pair
  (l - 1/2, k + 1/2)

This transformation is more mysterious than the A-process and corresponds to a "duality"
or "transposition" in the theory of exponential sums. It swaps and shifts the coordinates
in a way that preserves the underlying exponential sum bounds.

## Main Results

* `vanDerCorputB` - The B-process transformation theorem

## Implementation Notes

Like the A-process, this is currently axiomatized. The B-process is arguably deeper
than the A-process and its proof requires more sophisticated techniques in exponential
sum theory. Full formalization is a long-term goal.

## References

* [van der Corput, 1920s] - Original work
* [Graham-Kolesnik, 1991] - "van der Corput's Method of Exponential Sums", Section 2.4
* [Huxley, 1996] - "Area, Lattice Points, and Exponential Sums", Chapter 5
-/

/--
Van der Corput B-process: transforms (k, l) to (l - 1/2, k + 1/2).

Given an exponent pair (k, l), applying the B-process yields a new exponent pair
by swapping and shifting the coordinates. This operation has a profound geometric
and analytic interpretation.

**Geometric interpretation**: The B-process is an affine transformation that maps
the exponent pair triangle to itself. It has special properties with respect to
the geometry of the triangle:
* It swaps the vertices (0, 1) ↔ (1/2, 1/2)
* The vertex (0, 1/2) maps to (-1/2, 1/2), outside the triangle
* Combined with A, generates a dense set of points in the triangle

**Analytic interpretation**: Corresponds to a duality in exponential sum estimates,
relating bounds for different types of sums.

**Example**: B(0, 1) = (1/2, 1/2), Weyl's pair.

**Reference**: Graham-Kolesnik (1991), Theorem 2.4
-/
axiom vanDerCorputB (k l : ℚ) (h : IsExponentPair k l) :
    IsExponentPair (l - 1/2) (k + 1/2)

namespace IsExponentPair

/-- Apply the B-process and simplify: given `IsExponentPair k l`, produce
    `IsExponentPair k' l'` where `k' = l - 1/2` and `l' = k + 1/2`,
    with the equalities discharged by the caller (typically via `norm_num`). -/
theorem ofB {k l k' l' : ℚ} (h : IsExponentPair k l)
    (hk : k' = l - 1/2) (hl : l' = k + 1/2) :
    IsExponentPair k' l' := by
  rw [hk, hl]; exact vanDerCorputB k l h

end IsExponentPair

/-!
## Properties and Examples
-/

namespace VanDerCorputB

/--
The B-process preserves the geometric constraints on exponent pairs.
-/
theorem preserves_triangle (k l : ℚ) (h : IsExponentPair k l) :
    let k' := l - 1/2
    let l' := k + 1/2
    0 ≤ k' ∧ k' ≤ 1/2 ∧ 1/2 ≤ l' ∧ l' ≤ 1 ∧ k' + l' ≤ 1 :=
  vanDerCorputB k l h

/--
Applying B to the trivial pair (0, 1) gives Weyl's pair (1/2, 1/2).

Proof: B(0, 1) = (1 - 1/2, 0 + 1/2) = (1/2, 1/2)

This is a fundamental relationship showing how Weyl's estimate follows from
the trivial bound by applying the B-process.
-/
example (h : IsExponentPair 0 1) : IsExponentPair (1/2) (1/2) :=
  h.ofB (by norm_num) (by norm_num)

/--
The B-process is an involution on the classical pairs:
B(1/2, 1/2) = (0, 1), mapping Weyl's pair back to the trivial pair.

More generally, B²(k, l) = (k, l) whenever both (k, l) and B(k, l) are
in the exponent pair triangle.
-/
example (hk : IsExponentPair (1/2) (1/2)) : IsExponentPair 0 1 :=
  hk.ofB (by norm_num) (by norm_num)

/--
The B-process is an involution: applying B twice gives back the original pair.
This follows from the arithmetic identity (k+1/2)-1/2 = k and (l-1/2)+1/2 = l.
-/
theorem vanDerCorputB_involution {k l : ℚ} (_h : IsExponentPair k l) :
    (k + 1/2 : ℚ) - 1/2 = k ∧ (l - 1/2 : ℚ) + 1/2 = l := by
  constructor <;> ring

end VanDerCorputB

/-!
## Relationship Between A and B

The A and B processes do not commute, and their commutator generates interesting
structure in the exponent pair theory. The classical van der Corput pair (1/6, 2/3)
can be derived as BA(1/2, 1/2) or as various other combinations.

These relationships will be explored in `expdb.Derived.Examples`.
-/
