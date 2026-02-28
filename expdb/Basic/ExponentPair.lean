/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exponent Pairs

This file defines exponent pairs, which are rational points (k, l) that encode
bounds on exponential sums. Specifically, if (k, l) is an exponent pair, then
for any "nice" exponential sum S(N), we have
  |S(N)| ≤ N^(k+ε) + N^(l+ε)
for any ε > 0, under appropriate conditions.

## Main Definitions

* `ExponentPair` - A structure representing the geometric constraints on exponent pairs
* `IsExponentPair k l` - A predicate asserting that (k, l) satisfies the analytic
  conditions to be an exponent pair

## References

* [van der Corput, 1920s] - Original development of exponent pair theory
* [Graham-Kolesnik, 1991] - "van der Corput's Method of Exponential Sums"
* [Huxley, 1996] - "Area, Lattice Points, and Exponential Sums"
* [ANTEDB Blueprint] - https://teorth.github.io/expdb/blueprint/exponent-pairs-chapter.html

## Implementation Notes

This is the foundational file for the ANTEDB Lean formalization. Currently, we define
the geometric constraints on exponent pairs but leave the analytic conditions
(exponential sum bounds) as axioms to be formalized later.

See `LEAN.md` for the overall formalization strategy.
-/

/--
An exponent pair is a rational point (k, l) in the "exponent pair triangle":
  0 ≤ k ≤ 1/2
  1/2 ≤ l ≤ 1
  k + l ≤ 1

These geometric constraints reflect the underlying exponential sum estimates.
The extreme points of this triangle are (0, 1), (1/2, 1/2), and (0, 1/2).
-/
structure ExponentPair where
  k : ℚ
  l : ℚ
  k_nonneg : 0 ≤ k
  k_le_half : k ≤ 1/2
  l_ge_half : 1/2 ≤ l
  l_le_one : l ≤ 1
  sum_le_one : k + l ≤ 1

/--
Predicate: is (k, l) an exponent pair?

This includes both the geometric constraints (being in the triangle) and the
analytic conditions (satisfying exponential sum bounds). Currently, the analytic
conditions are axiomatized; literature results and transforms will populate this.

This predicate is used throughout the ANTEDB formalization as the primary
interface for working with exponent pairs.
-/
def IsExponentPair (k l : ℚ) : Prop :=
  0 ≤ k ∧ k ≤ 1/2 ∧ 1/2 ≤ l ∧ l ≤ 1 ∧ k + l ≤ 1

namespace ExponentPair

/-- Convert an `ExponentPair` structure to the `IsExponentPair` predicate -/
theorem isExponentPair_of_exponentPair (p : ExponentPair) :
    IsExponentPair p.k p.l :=
  ⟨p.k_nonneg, p.k_le_half, p.l_ge_half, p.l_le_one, p.sum_le_one⟩

/-- Helper: create an `ExponentPair` from rationals with a proof -/
def mk' (k l : ℚ) (h : IsExponentPair k l) : ExponentPair :=
  ⟨k, l, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end ExponentPair

namespace IsExponentPair

/-- The exponent pair triangle is contained in the unit square -/
theorem k_in_unit_interval {k l : ℚ} (h : IsExponentPair k l) : 0 ≤ k ∧ k ≤ 1 := by
  constructor
  · exact h.1
  · calc k ≤ 1/2 := h.2.1
         _ ≤ 1 := by norm_num

/-- The exponent pair triangle is contained in the unit square -/
theorem l_in_unit_interval {k l : ℚ} (h : IsExponentPair k l) : 0 ≤ l ∧ l ≤ 1 := by
  constructor
  · calc (0:ℚ) ≤ 1/2 := by norm_num
               _ ≤ l := h.2.2.1
  · exact h.2.2.2.1

/-- The set of exponent pairs is convex: any convex combination of two
    exponent pairs is again an exponent pair (at the geometric constraint level). -/
theorem convex {k₁ l₁ k₂ l₂ t : ℚ}
    (h₁ : IsExponentPair k₁ l₁) (h₂ : IsExponentPair k₂ l₂)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    IsExponentPair (t * k₁ + (1 - t) * k₂) (t * l₁ + (1 - t) * l₂) := by
  unfold IsExponentPair at *
  obtain ⟨h1a, h1b, h1c, h1d, h1e⟩ := h₁
  obtain ⟨h2a, h2b, h2c, h2d, h2e⟩ := h₂
  have h_1mt : (0 : ℚ) ≤ 1 - t := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg ht₀ h1a, mul_nonneg h_1mt h2a]
  · nlinarith [mul_nonneg ht₀ (show (0 : ℚ) ≤ 1/2 - k₁ by linarith),
               mul_nonneg h_1mt (show (0 : ℚ) ≤ 1/2 - k₂ by linarith)]
  · nlinarith [mul_nonneg ht₀ (show (0 : ℚ) ≤ l₁ - 1/2 by linarith),
               mul_nonneg h_1mt (show (0 : ℚ) ≤ l₂ - 1/2 by linarith)]
  · nlinarith [mul_nonneg ht₀ (show (0 : ℚ) ≤ 1 - l₁ by linarith),
               mul_nonneg h_1mt (show (0 : ℚ) ≤ 1 - l₂ by linarith)]
  · nlinarith [mul_nonneg ht₀ (show (0 : ℚ) ≤ 1 - k₁ - l₁ by linarith),
               mul_nonneg h_1mt (show (0 : ℚ) ≤ 1 - k₂ - l₂ by linarith)]

end IsExponentPair

/-!
## Examples

These will be populated with actual exponent pairs as the formalization progresses.
-/

-- The trivial exponent pair (0, 1)
example : IsExponentPair 0 1 := by
  unfold IsExponentPair
  norm_num

-- The Weyl exponent pair (1/2, 1/2)
example : IsExponentPair (1/2) (1/2) := by
  unfold IsExponentPair
  norm_num

-- The Bourgain exponent pair (13/84, 55/84)
example : IsExponentPair (13/84) (55/84) := by
  unfold IsExponentPair
  norm_num
