module

public import Expdb.Mathlib.EulerMaclaurin
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Bounds for the Euler–Maclaurin power remainder

The arbitrary-order summation formula produces a periodic Bernoulli function times
a derivative of `x ↦ x^(-s)`. This module bounds the resulting power integral on
`(1,∞)` using the existing Bernoulli bound and the elementary improper power integral.

The integral has not yet been identified with the remainder in a continuation formula
for `riemannZeta`; that identification is a separate analytic prerequisite.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open Expdb.EulerMaclaurin

noncomputable section

namespace Expdb

/-- The power integral occurring in an order-`k` Euler–Maclaurin zeta remainder. -/
def zetaPowerRemainder (k : ℕ) (s : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 1, (saw k x : ℂ) * (x : ℂ) ^ (-s - (k : ℂ))

private theorem continuous_saw {k : ℕ} (hk : k ≠ 1) : Continuous (saw k) := by
  unfold saw
  exact continuous_const.mul ((periodizedBernoulli.continuous hk).comp continuous_quotient_mk')

private theorem norm_powerRemainderIntegrand_le (k : ℕ) (s : ℂ) {x : ℝ} (hx : 1 < x) :
    ‖(saw k x : ℂ) * (x : ℂ) ^ (-s - (k : ℂ))‖ ≤
      sawBound k * x ^ (-s.re - (k : ℝ)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hx)]
  simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
  exact mul_le_mul_of_nonneg_right (abs_saw_le k x) (Real.rpow_nonneg (by linarith) _)

/-- The remainder integrand is genuinely integrable when `re(s)+k>1`.
Orders other than one have a continuous periodic Bernoulli function. -/
theorem integrableOn_zetaPowerRemainder {k : ℕ} (hk : k ≠ 1) {s : ℂ}
    (hs : 1 < s.re + (k : ℝ)) :
    IntegrableOn (fun x : ℝ => (saw k x : ℂ) * (x : ℂ) ^ (-s - (k : ℂ))) (Ioi 1) := by
  have hc : ContinuousOn (fun x : ℝ => (saw k x : ℂ) * (x : ℂ) ^ (-s - (k : ℂ))) (Ioi 1) := by
    apply (Complex.continuous_ofReal.comp (continuous_saw hk)).continuousOn.mul
    apply Complex.continuous_ofReal.continuousOn.cpow_const
    intro x hx
    simp [Complex.mem_slitPlane_iff, show 0 < x from zero_lt_one.trans hx]
  have hg : IntegrableOn (fun x : ℝ => sawBound k * x ^ (-s.re - (k : ℝ))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  apply hg.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_powerRemainderIntegrand_le k s hx

/-- An explicit bound for the power remainder; its constant depends only on the
real part of `s` and the summation order, not on the imaginary part. -/
theorem norm_zetaPowerRemainder_le {k : ℕ} {s : ℂ} (hs : 1 < s.re + (k : ℝ)) :
    ‖zetaPowerRemainder k s‖ ≤ sawBound k / (s.re + (k : ℝ) - 1) := by
  have hg : IntegrableOn (fun x : ℝ => sawBound k * x ^ (-s.re - (k : ℝ))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have hb := norm_integral_le_of_norm_le hg (show ∀ᵐ x : ℝ ∂volume.restrict (Ioi 1),
      ‖(saw k x : ℂ) * (x : ℂ) ^ (-s - (k : ℂ))‖ ≤
        sawBound k * x ^ (-s.re - (k : ℝ)) from by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_powerRemainderIntegrand_le k s hx)
  change ‖zetaPowerRemainder k s‖ ≤ _ at hb
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
    Real.one_rpow] at hb
  rw [show -s.re - (k : ℝ) + 1 = -(s.re + (k : ℝ) - 1) by ring,
    div_neg, neg_div, neg_neg] at hb
  simpa only [mul_one_div] using hb

private def truncatedSaw (k : ℕ) : ℝ → ℂ :=
  (Ioi 1).indicator (fun x => (saw k x : ℂ))

private theorem zetaPowerRemainder_eq_mellin (k : ℕ) (s : ℂ) :
    zetaPowerRemainder k s = mellin (truncatedSaw k) (1 - s - (k : ℂ)) := by
  unfold mellin
  have hfun : (fun x : ℝ => (x : ℂ) ^ (1 - s - (k : ℂ) - 1) • truncatedSaw k x) =
      (Ioi 1).indicator (fun x : ℝ => (saw k x : ℂ) * (x : ℂ) ^ (-s - (k : ℂ))) := by
    funext x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp only [truncatedSaw, indicator_of_mem hx, smul_eq_mul,
        show 1 - s - (k : ℂ) - 1 = -s - (k : ℂ) by ring, mul_comm]
    · simp [truncatedSaw, hx]
  rw [hfun, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi]
  norm_num [zetaPowerRemainder]

/-- The power remainder is holomorphic on its half-plane of convergence. This uses
Mathlib's dominated differentiation theorem for Mellin transforms. -/
theorem differentiableAt_zetaPowerRemainder {k : ℕ} (hk : k ≠ 1) {s : ℂ}
    (hs : 1 < s.re + (k : ℝ)) : DifferentiableAt ℂ (zetaPowerRemainder k) s := by
  let z : ℂ := 1 - s - (k : ℂ)
  have hloc : LocallyIntegrableOn (truncatedSaw k) (Ioi 0) :=
    (((Complex.continuous_ofReal.comp (continuous_saw hk)).locallyIntegrable).indicator
      measurableSet_Ioi).locallyIntegrableOn _
  have htop : truncatedSaw k =O[atTop] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    apply Asymptotics.IsBigO.of_bound (sawBound k)
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simpa [truncatedSaw, hx, Real.norm_eq_abs] using abs_saw_le k x
    · simp [truncatedSaw, hx]
  have hbot : truncatedSaw k =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(z.re - 1))) := by
    apply Asymptotics.IsBigO.of_bound 0
    have hsmall0 : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), x < 1 :=
      Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
    have hsmall : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < 1 :=
      hsmall0.filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall] with x hx
    simp [truncatedSaw, not_lt_of_ge hx.le]
  have hdiff : DifferentiableAt ℂ (mellin (truncatedSaw k)) z :=
    mellin_differentiableAt_of_isBigO_rpow hloc htop
      (by change 1 - s.re - (k : ℝ) < 0; linarith)
      hbot (by linarith)
  have heq : zetaPowerRemainder k = fun w : ℂ =>
      mellin (truncatedSaw k) (1 - w - (k : ℂ)) :=
    funext (zetaPowerRemainder_eq_mellin k)
  rw [heq]
  change DifferentiableAt ℂ
    ((mellin (truncatedSaw k)) ∘ fun w : ℂ => 1 - w - (k : ℂ)) s
  exact hdiff.comp s ((differentiableAt_id.const_sub (1 : ℂ)).sub_const (k : ℂ))

/-- The Euler–Maclaurin power remainder is analytic throughout its open half-plane
of absolute convergence. -/
theorem analyticOn_zetaPowerRemainder {k : ℕ} (hk : k ≠ 1) :
    AnalyticOnNhd ℂ (zetaPowerRemainder k) {s : ℂ | 1 < s.re + (k : ℝ)} := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    exact (differentiableAt_zetaPowerRemainder hk hs).differentiableWithinAt
  · exact isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)

end Expdb
