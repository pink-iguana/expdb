module

import Expdb.LargeValues.Exponents
import Expdb.Zeta.GrowthRight

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
  le_antisymm (largeValueExponent_le_tau (by norm_num) (by norm_num))
    (largeValueExponent_nonneg (by norm_num) (by norm_num))

example : largeValueExponent (1 / 2) 0 = 0 :=
  le_antisymm (largeValueExponent_le_tau (by norm_num) (by norm_num))
    (largeValueExponent_nonneg (by norm_num) (by norm_num))

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
