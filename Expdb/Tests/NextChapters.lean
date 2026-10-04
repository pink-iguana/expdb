module

import Expdb.LargeValues.Exponents
import Expdb.Zeta.GrowthRight
import Expdb.Zeta.PowerRemainder

/-! Boundary checks for the definitions in the chapters following exponent pairs. -/

open Expdb

noncomputable section

-- Nonintegral scales retain both integer endpoints in the real dyadic interval.
example : dyadicIndices (3 / 2) = Finset.Icc 2 3 := by
  have hceil : ⌈(3 / 2 : ℝ)⌉₊ = 2 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  norm_num [dyadicIndices, hceil, Nat.floor_eq_iff]

example : dyadicIndices 2 = {2, 3, 4} := by
  norm_num [dyadicIndices]
  decide

-- The separation convention allows distance exactly one, including interval endpoints.
example : IsOneSeparated ({0, 1} : Finset ℝ) := by
  intro x y hxy
  have hx := x.property
  have hy := y.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact False.elim (hxy (Subtype.ext (hx.trans hy.symm)))
  · simp [hx, hy]
  · simp [hx, hy]
  · exact False.elim (hxy (Subtype.ext (hx.trans hy.symm)))

-- Zero coefficients are permitted when the observation set is empty, even at small T.
example : IsZetaLargeValuePattern (3 / 2) (1 / 2) 10 (fun _ => 0) (1 / 2) ∅ :=
  isZetaLargeValuePattern_zero_empty (by norm_num) (by norm_num) (by norm_num)

-- Both endpoints of the blueprint's sigma range are covered at the tau = 0 boundary.
example : largeValueExponent 1 0 = 0 :=
  largeValueExponent_zero (by norm_num)

example : largeValueExponent (1 / 2) 0 = 0 :=
  largeValueExponent_zero (by norm_num)

-- The extended-real API retains a genuinely negative-infinite exponent.
example {σ τ : ℝ} (h : ∀ ρ : ℝ, IsZetaLargeValueBound σ τ ρ) :
    zetaLargeValueExponent σ τ = ⊥ := zetaLargeValueExponent_eq_bot_iff.mpr h

-- Right-of-strip finiteness is certified without additional hypotheses.
example : zetaGrowthExponent 2 = 0 := zetaGrowthExponent_eq_zero_of_one_lt (by norm_num)

-- The epsilon formulation treats both signs of the height.
example {σ b : ℝ} (h : IsZetaGrowthBound σ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, C ≤ |t| →
      ‖zetaOnVertical σ (-t)‖ ≤ C * |t| ^ (b + ε) := by
  obtain ⟨C, hC, hb⟩ := h ε hε
  exact ⟨C, hC, fun t ht => by simpa using hb (-t) (by simpa using ht)⟩

-- Symmetry agrees with the literal blueprint expression, including sigma = 1.
example (t : ℝ) :
    ‖riemannZeta (1 - (t : ℂ) * Complex.I)‖ =
      ‖riemannZeta (1 + (t : ℂ) * Complex.I)‖ := by
  simpa [zetaOnVertical, sub_eq_add_neg] using norm_zetaOnVertical_neg 1 t

-- A conventional positive-height Big-O estimate yields an actual exponent bound.
open Filter in
example {σ b : ℝ} (hσ : 1 < σ)
    (h : (fun t : ℝ => zetaOnVertical σ t) =O[atTop] (fun t => t ^ b)) :
    zetaGrowthExponent σ ≤ b :=
  (zetaGrowthExponent_le_iff_of_one_lt hσ).mpr (isZetaGrowthBound_of_isBigO h)

-- Higher-order remainders converge even on lines left of the critical strip.
example (t : ℝ) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => (EulerMaclaurin.saw 3 x : ℂ) *
        (x : ℂ) ^ (-(-1 + (t : ℂ) * Complex.I) - 3)) (Set.Ioi 1) := by
  simpa using integrableOn_zetaPowerRemainder (k := 3) (s := -1 + (t : ℂ) * Complex.I)
    (by decide) (by norm_num)

example (t : ℝ) :
    ‖zetaPowerRemainder 3 (-1 + (t : ℂ) * Complex.I)‖ ≤ EulerMaclaurin.sawBound 3 := by
  have hb := norm_zetaPowerRemainder_le (k := 3) (s := -1 + (t : ℂ) * Complex.I)
    (by norm_num)
  norm_num at hb
  exact hb

example : DifferentiableAt ℂ (zetaPowerRemainder 3) (-1) :=
  differentiableAt_zetaPowerRemainder (by decide) (by norm_num)
