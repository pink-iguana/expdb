module

public import Expdb.Zeta.Growth
public import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Zeta growth to the right of the critical strip

Absolute convergence of the zeta and Möbius Dirichlet series gives uniform upper
and positive lower bounds on every vertical line with real part greater than one.
These certify that `μ(σ) = 0` for `σ > 1`. The endpoint `σ = 1` requires separate analysis.
-/

@[expose] public section

open Filter Topology
open scoped Expdb ArithmeticFunction.Moebius

noncomputable section

namespace Expdb

private def majorant (σ : ℝ) : ℝ := ∑' n : ℕ, ‖LSeries.term 1 (σ : ℂ) n‖

private theorem norm_lSeries_le_majorant {σ : ℝ} (hσ : 1 < σ)
    {f : ℕ → ℂ} (hf : ∀ n ≠ 0, ‖f n‖ ≤ 1) {s : ℂ} (hs : s.re = σ) :
    ‖LSeries f s‖ ≤ majorant σ := by
  have hsum : Summable (fun n => ‖LSeries.term 1 (σ : ℂ) n‖) :=
    (LSeriesSummable_of_bounded_of_one_lt_real (f := 1) (m := 1) (by simp) hσ).norm
  apply tsum_of_norm_bounded hsum.hasSum
  intro n
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hs, Complex.ofReal_re]
  split_ifs with hn
  · rfl
  · simp only [Pi.one_apply, norm_one]
    exact div_le_div_of_nonneg_right (hf n hn) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private theorem one_le_majorant {σ : ℝ} (hσ : 1 < σ) : 1 ≤ majorant σ := by
  have hsum : Summable (fun n => ‖LSeries.term 1 (σ : ℂ) n‖) :=
    (LSeriesSummable_of_bounded_of_one_lt_real (f := 1) (m := 1) (by simp) hσ).norm
  have h := hsum.le_tsum 1 (fun n _ => norm_nonneg _)
  simpa [majorant, LSeries.term] using h

/-- For each `σ > 1`, the norm of zeta is bounded above and bounded away from zero,
uniformly in the height `t`. -/
theorem zetaAt_bounds_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t : ℝ,
      1 / B ≤ ‖zetaAt σ t‖ ∧ ‖zetaAt σ t‖ ≤ B := by
  refine ⟨majorant σ, one_le_majorant hσ, fun t => ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hs : s.re = σ := by simp [s]
  have hsr : 1 < s.re := hs ▸ hσ
  have hu : ‖zetaAt σ t‖ ≤ majorant σ := by
    rw [zetaAt, ← LSeries_one_eq_riemannZeta hsr]
    exact norm_lSeries_le_majorant hσ (by simp) hs
  have hm : ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤ majorant σ := by
    apply norm_lSeries_le_majorant hσ _ hs
    intro n _
    norm_cast
    exact ArithmeticFunction.abs_moebius_le_one
  have hmul : zetaAt σ t *
      LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s = 1 := by
    simpa [zetaAt, LSeries_one_eq_riemannZeta hsr] using
      LSeries_one_mul_Lseries_moebius hsr
  have hnorm : ‖zetaAt σ t‖ *
      ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hmul
  refine ⟨?_, hu⟩
  apply (div_le_iff₀ (zero_lt_one.trans_le (one_le_majorant hσ))).mpr
  have hh := mul_le_mul_of_nonneg_left hm (norm_nonneg (zetaAt σ t))
  linarith

/-- Zero is an admissible exponent on every line with `σ > 1`. -/
theorem isZetaGrowthBound_zero_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    IsZetaGrowthBound σ 0 := by
  obtain ⟨B, hB, hb⟩ := zetaAt_bounds_of_one_lt hσ
  apply isZetaGrowthBound_iff_forall_pos.mpr
  intro ε hε
  refine ⟨B, zero_lt_one.trans_le hB, fun t ht => ?_⟩
  simpa only [zero_add] using (hb t).2.trans
    (le_mul_of_one_le_right (zero_lt_one.trans_le hB).le (Real.one_le_rpow (hB.trans ht) hε.le))

/-- Positive uniform lower bounds exclude negative admissible exponents for `σ > 1`. -/
theorem IsZetaGrowthBound.nonneg_of_one_lt {σ b : ℝ} (h : IsZetaGrowthBound σ b)
    (hσ : 1 < σ) : 0 ≤ b := by
  obtain ⟨B, hB, hb⟩ := zetaAt_bounds_of_one_lt hσ
  let t : VariableObject ℝ := fun i => (i : ℝ) + 1
  have ht : ∀ i, 1 ≤ |t i| := by
    intro i
    have hnonneg : 0 ≤ t i := by dsimp [t]; positivity
    rw [abs_of_nonneg hnonneg]
    dsimp [t]
    linarith [Nat.cast_nonneg (α := ℝ) i]
  have htop : t.IsUnbounded := by
    unfold VariableObject.IsUnbounded
    simp only [Real.norm_eq_abs]
    apply tendsto_atTop_mono (fun i : ℕ => show (i : ℝ) ≤ |t i| by
      dsimp [t]; rw [abs_of_nonneg (by positivity)]; linarith)
    exact tendsto_natCast_atTop_atTop
  have habstop : VariableObject.IsUnbounded (fun i => |t i|) := by
    simpa [VariableObject.IsUnbounded, Real.norm_eq_abs] using htop
  apply exponent_le_of_isPowerBounded_of_eventually_norm_ge_rpow
    ht habstop (h t ht htop) (one_div_pos.mpr (zero_lt_one.trans_le hB))
  exact Eventually.of_forall fun i => by simpa using (hb (t i)).1

/-- The set of admissible zeta growth exponents is nonempty for `σ > 1`. -/
theorem zetaGrowthBounds_nonempty_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    (zetaGrowthBounds σ).Nonempty := ⟨0, isZetaGrowthBound_zero_of_one_lt hσ⟩

/-- The set of admissible zeta growth exponents is bounded below by zero for `σ > 1`. -/
theorem zetaGrowthBounds_bddBelow_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    BddBelow (zetaGrowthBounds σ) := ⟨0, fun _ hb => hb.nonneg_of_one_lt hσ⟩

/-- The zeta growth exponent is zero for `σ > 1` (the open part of `zeta-grow-triv`). -/
theorem zetaGrowthExponent_eq_zero_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    zetaGrowthExponent σ = 0 := by
  apply le_antisymm
  · exact (zetaGrowthExponent_le_iff (zetaGrowthBounds_nonempty_of_one_lt hσ)
      (zetaGrowthBounds_bddBelow_of_one_lt hσ)).mpr (isZetaGrowthBound_zero_of_one_lt hσ)
  · exact (isZetaGrowthBound_zetaGrowthExponent
      (zetaGrowthBounds_nonempty_of_one_lt hσ)).nonneg_of_one_lt hσ

end Expdb
