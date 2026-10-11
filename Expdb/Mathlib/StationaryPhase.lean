module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Fourier.PoissonSummation

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Quantitative quadratic stationary phase

Adapted from `lean/OAI/Dynamics/ThreeTorus/StationaryPhase.lean` and
`lean/OAI/MeasureTheory/Falconer/Fourier/SchwartzFourierMomentBounds.lean` in
[OpenAI Math](https://github.com/openai/math) at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, licensed under Apache-2.0 (see the root LICENSE).

Adaptations for Expdb: retained the quadratic identity, quantitative remainder,
and Fourier moment estimate. Imports were narrowed, and namespaces and proofs
were updated for the current Mathlib API.
-/

@[expose] public section

namespace Expdb.StationaryPhase

noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real ContDiff ComplexConjugate

private theorem quadratic_gaussian_pairing (f : 𝓢(ℝ, ℂ)) {b : ℂ} (hb : 0 < b.re) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2)) =
      (1 / b ^ (1 / 2 : ℂ)) * (∫ ξ : ℝ, (𝓕⁻ f) ξ *
        Complex.exp (-Real.pi / b * ξ ^ 2)) := by
  have hi : Integrable (fun x : ℝ => Complex.exp (-Real.pi * b * x ^ 2)) := by
    have hb' : 0 < ((Real.pi : ℂ) * b).re := by
      simpa only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] using mul_pos Real.pi_pos hb
    simpa only [neg_mul, mul_zero, zero_mul, add_zero] using
      integrable_cexp_quadratic hb' 0 0
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) (μ := volume) (ν := volume) Real.continuous_fourierChar continuous_inner
      (𝓕⁻ f).integrable hi
  have hinv : (𝓕 ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) = (f : ℝ → ℂ) := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  have h' : (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2)) =
      ∫ x : ℝ, (𝓕⁻ f) x * (𝓕 fun y : ℝ => Complex.exp (-Real.pi * b * y ^ 2)) x := by
    rw [flip_innerₗ] at h
    change (∫ x : ℝ, (𝓕 ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x •
      Complex.exp (-Real.pi * b * x ^ 2)) = _ at h
    simpa only [hinv, smul_eq_mul] using! h
  rw [h', fourier_gaussian_pi hb, ← integral_const_mul]
  congr 1
  ext x
  ring

private theorem norm_quadratic_exp_le_one {b : ℂ} (hb : 0 ≤ b.re) (x : ℝ) :
    ‖Complex.exp (-(Real.pi : ℂ) * b * x ^ 2)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have he : (-(Real.pi : ℂ) * b * (x : ℂ) ^ 2).re = -Real.pi * b.re * x ^ 2 := by
    simp [mul_re, mul_im, pow_two]
  rw [he]
  have := mul_nonneg (mul_nonneg Real.pi_pos.le hb) (sq_nonneg x)
  linarith

/-- The Gaussian identity extends to the imaginary boundary after pairing with
an integrable Schwartz amplitude. This uses dominated convergence, never a
non-absolutely convergent Bochner integral for a bare Fresnel kernel. -/
private theorem quadratic_boundary_pairing (f : 𝓢(ℝ, ℂ)) {b : ℂ}
    (hb : 0 ≤ b.re) (hbslit : b ∈ Complex.slitPlane) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2)) =
      (1 / b ^ (1 / 2 : ℂ)) * (∫ ξ : ℝ, (𝓕⁻ f) ξ *
        Complex.exp (-Real.pi / b * ξ ^ 2)) := by
  have hb0 : b ≠ 0 := Complex.slitPlane_ne_zero hbslit
  have hparam : Tendsto (fun ε : ℝ => b + (ε : ℂ)) (𝓝[>] 0) (𝓝 b) := by
    have hcast : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [add_zero] using hcast.const_add b
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hre : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < (b + (ε : ℂ)).re := by
    filter_upwards [heps] with ε hε
    simp only [add_re, ofReal_re]
    linarith
  have hleft : Tendsto (fun ε : ℝ => ∫ x : ℝ,
      f x * Complex.exp (-Real.pi * (b + (ε : ℂ)) * x ^ 2)) (𝓝[>] 0)
        (𝓝 (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * x ^ 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
      ?_ ?_ f.integrable.norm ?_
    · exact Eventually.of_forall (fun ε => by apply Continuous.aestronglyMeasurable; fun_prop)
    · filter_upwards [hre] with ε hε
      filter_upwards [] with x
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (norm_quadratic_exp_le_one hε.le x)
        (norm_nonneg (f x))).trans_eq (mul_one _)
    · filter_upwards [] with x
      exact tendsto_const_nhds.mul (((hparam.const_mul _).mul_const _).cexp)
  have hintegral : Tendsto (fun ε : ℝ => ∫ x : ℝ,
      (𝓕⁻ f) x * Complex.exp (-Real.pi / (b + (ε : ℂ)) * x ^ 2)) (𝓝[>] 0)
        (𝓝 (∫ x : ℝ, (𝓕⁻ f) x * Complex.exp (-Real.pi / b * x ^ 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖(𝓕⁻ f) x‖)
      ?_ ?_ (𝓕⁻ f).integrable.norm ?_
    · exact Eventually.of_forall (fun ε => by apply Continuous.aestronglyMeasurable; fun_prop)
    · filter_upwards [hre] with ε hε
      filter_upwards [] with x
      rw [norm_mul, div_eq_mul_inv]
      have hb' : 0 ≤ (b + (ε : ℂ))⁻¹.re := by
        rw [Complex.inv_re]
        exact div_nonneg hε.le (Complex.normSq_nonneg _)
      exact (mul_le_mul_of_nonneg_left (norm_quadratic_exp_le_one hb' x)
        (norm_nonneg ((𝓕⁻ f) x))).trans_eq (mul_one _)
    · filter_upwards [] with x
      exact tendsto_const_nhds.mul (((tendsto_const_nhds.div hparam hb0).mul_const _).cexp)
  have hpow : Tendsto (fun ε : ℝ => 1 / (b + (ε : ℂ)) ^ (1 / 2 : ℂ))
      (𝓝[>] 0) (𝓝 (1 / b ^ (1 / 2 : ℂ))) := by
    apply tendsto_const_nhds.div
    · exact (continuousAt_cpow_const hbslit).tendsto.comp hparam
    · exact cpow_ne_zero_iff.mpr (Or.inl hb0)
  have hr := hpow.mul hintegral
  have hright := hr.congr' (hre.mono (fun ε hε => (quadratic_gaussian_pairing f hε).symm))
  exact tendsto_nhds_unique hleft hright

private theorem cpow_pos_mul {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ((t : ℂ) * z) ^ w = (t : ℂ) ^ w * z ^ w := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr ht.ne') hz),
    Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne'),
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul ht hz,
    ← Complex.ofReal_log ht.le, add_mul, Complex.exp_add]

private theorem quadratic_factor {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t : ℂ) / ((t : ℂ) * (-I)) ^ (1 / 2 : ℂ) =
      Complex.exp ((Real.pi : ℂ) / 4 * I) := by
  have hs : (Real.sqrt t : ℂ) = (t : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ht.le]
    norm_num
  rw [cpow_pos_mul ht (neg_ne_zero.mpr I_ne_zero), hs, div_mul_eq_div_div,
    div_self (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr ht.ne'))),
    Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero), Complex.log_neg_I,
    one_div, ← Complex.exp_neg]
  congr 1
  ring

private theorem integral_fourierInv (f : 𝓢(ℝ, ℂ)) : (∫ x : ℝ, (𝓕⁻ f) x) = f 0 := by
  have he : (𝓕 ((𝓕⁻ f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) 0 = f 0 := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  simpa [Real.fourier_eq] using he

lemma quadratic_stationary_identity (f : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t : ℂ) * (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) =
      Complex.exp ((Real.pi : ℂ) / 4 * I) *
        (∫ ξ : ℝ, (𝓕⁻ f) ξ * Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ))) := by
  have hb : 0 ≤ ((t : ℂ) * (-I)).re := by simp
  have hslit : (t : ℂ) * (-I) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simpa using ht.ne'
  have he := quadratic_boundary_pairing f hb hslit
  have hleft : ∀ x : ℝ, Complex.exp (-(Real.pi : ℂ) * ((t : ℂ) * (-I)) * x^2) =
      Complex.exp (I * (Real.pi * t * x^2 : ℝ)) := by
    intro x
    congr 1
    push_cast
    ring
  have hright : ∀ x : ℝ, Complex.exp (-(Real.pi : ℂ) / ((t : ℂ) * (-I)) * x^2) =
      Complex.exp (I * (-Real.pi / t * x^2 : ℝ)) := by
    intro x
    congr 1
    push_cast
    field_simp
    simp [I_sq]
    ring
  simp only [hleft, hright] at he
  rw [he, ← mul_assoc, ← div_eq_mul_one_div, quadratic_factor ht]

lemma quadratic_stationary_error (f : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 < t) :
    ‖(Real.sqrt t : ℂ) * (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x^2 : ℝ))) -
      Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0‖ ≤
        (Real.pi / t) * (∫ ξ : ℝ, ξ^2 * ‖(𝓕⁻ f) ξ‖) := by
  rw [quadratic_stationary_identity f ht, ← mul_sub, norm_mul]
  have hnorm : ‖Complex.exp ((Real.pi : ℂ) / 4 * I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hnorm, one_mul, ← integral_fourierInv f]
  have hi : Integrable (fun ξ : ℝ => (𝓕⁻ f) ξ *
      Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ))) := by
    apply ((𝓕⁻ f).integrable (μ := volume)).mul_bdd
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · filter_upwards [] with ξ
      have he : ‖Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ))‖ = 1 := by
        rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
      exact he.le
  rw [← integral_sub hi (𝓕⁻ f).integrable]
  have hd : Integrable (fun ξ : ℝ => ξ^2 * ‖(𝓕⁻ f) ξ‖) := by
    have hh := (𝓕⁻ f).integrable_pow_mul volume 2
    simpa only [Real.norm_eq_abs, sq_abs] using hh
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hd.const_mul (Real.pi / t))
  filter_upwards [] with ξ
  have heq : (𝓕⁻ f) ξ * Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - (𝓕⁻ f) ξ =
      (𝓕⁻ f) ξ * (Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - 1) := by ring
  rw [heq, norm_mul]
  have he := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -Real.pi / t * ξ^2)
  have he' : ‖Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - 1‖ ≤
      Real.pi / t * ξ^2 := by
    convert he using 1
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_of_pos Real.pi_pos,
      abs_of_pos ht, abs_of_nonneg (sq_nonneg ξ)]
  calc
    ‖(𝓕⁻ f) ξ‖ * ‖Complex.exp (I * (-Real.pi / t * ξ^2 : ℝ)) - 1‖ ≤
        ‖(𝓕⁻ f) ξ‖ * (Real.pi / t * ξ^2) :=
      mul_le_mul_of_nonneg_left he' (norm_nonneg _)
    _ = _ := by ring


private theorem schwartz_iteratedDeriv_integrable (φ : 𝓢(ℝ, ℂ)) (n : ℕ) :
    Integrable (iteratedDeriv n (φ : ℝ → ℂ)) := by
  apply (φ.integrable_pow_mul_iteratedFDeriv volume 0 n).mono'
    ((φ.smooth ⊤).continuous_iteratedDeriv n
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).aestronglyMeasurable
  filter_upwards with x
  simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv]

/-- The L¹ norm of a derivative, normalized by the Fourier derivative factor. -/
noncomputable def fourierDerivativeL1 (φ : 𝓢(ℝ, ℂ)) (n : ℕ) : ℝ :=
  (∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖)/(2*Real.pi)^n

theorem fourierDerivativeL1_nonneg (φ : 𝓢(ℝ, ℂ)) (n : ℕ) : 0 ≤ fourierDerivativeL1 φ n := by
  unfold fourierDerivativeL1
  exact div_nonneg (integral_nonneg (fun _ => norm_nonneg _)) (by positivity)

private theorem schwartz_fourier_weighted_pointwise (φ : 𝓢(ℝ, ℂ)) (n : ℕ) (ξ : ℝ) :
    ‖ξ‖^n * ‖𝓕 φ ξ‖ ≤ fourierDerivativeL1 φ n := by
  have he := congrFun (Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (φ.smooth ⊤)
    (fun k _ => schwartz_iteratedDeriv_integrable φ k) (n := n) (by simp)) ξ
  have hh := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (iteratedDeriv n (φ : ℝ → ℂ)) ξ
  have hh' : ‖𝓕 (iteratedDeriv n (φ : ℝ → ℂ)) ξ‖ ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    simpa using! hh
  rw [he] at hh'
  simp only [norm_smul,norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one] at hh'
  have hh'' : (2*Real.pi)^n * (‖ξ‖^n*‖𝓕 φ ξ‖) ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    convert hh' using 1
    simp only [mul_pow,Real.norm_eq_abs,SchwartzMap.fourier_coe]
    ring
  exact (le_div_iff₀ (by positivity : 0 < (2*Real.pi)^n)).mpr (by simpa [mul_comm] using hh'')

/-- An `n`th Fourier moment is bounded by the `n`th and `(n + 2)`nd derivative norms. -/
theorem schwartz_fourier_moment_bound (φ : 𝓢(ℝ, ℂ)) (n : ℕ) :
    (∫ ξ : ℝ, ‖ξ‖^n*‖𝓕 φ ξ‖) ≤
      (fourierDerivativeL1 φ n + fourierDerivativeL1 φ (n+2)) *
        ∫ ξ : ℝ, (1+ξ^2)⁻¹ := by
  have hi : Integrable (fun ξ : ℝ => ‖ξ‖^n*‖𝓕 φ ξ‖) := (𝓕 φ).integrable_pow_mul volume n
  rw [← integral_const_mul]
  apply integral_mono hi (integrable_inv_one_add_sq.const_mul _) _
  intro ξ
  have h₀ := schwartz_fourier_weighted_pointwise φ n ξ
  have h₂ := schwartz_fourier_weighted_pointwise φ (n+2) ξ
  have hp : 0 < 1+ξ^2 := by positivity
  dsimp only
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hp).mpr
  have he : ‖ξ‖^(n+2)*‖𝓕 φ ξ‖ = (‖ξ‖^n*‖𝓕 φ ξ‖)*ξ^2 := by
    rw [pow_add,Real.norm_eq_abs,sq_abs]
    ring
  rw [he] at h₂
  nlinarith


/-- The inverse Fourier transform has the same even weighted moment as the
Fourier transform. This is the moment needed by the quadratic remainder. -/
lemma integral_sq_norm_fourierInv (f : 𝓢(ℝ, ℂ)) :
    (∫ ξ : ℝ, ξ ^ 2 * ‖(𝓕⁻ f) ξ‖) = ∫ ξ : ℝ, ξ ^ 2 * ‖(𝓕 f) ξ‖ := by
  have h := MeasureTheory.integral_neg_eq_self
    (fun ξ : ℝ => ξ ^ 2 * ‖(𝓕 f) ξ‖) volume
  simpa only [Real.fourierInv_eq_fourier_neg, SchwartzMap.fourierInv_coe,
    SchwartzMap.fourier_coe, neg_sq] using h

/-- A quantitative remainder controlled by ordinary derivative norms of the
amplitude. Uniform bounds for these norms give a uniform `t⁻³ᐟ²` remainder. -/
lemma quadratic_stationary_error_of_derivative_bounds (f : 𝓢(ℝ, ℂ))
    {t B₂ B₄ : ℝ} (ht : 0 < t)
    (h₂ : fourierDerivativeL1 f 2 ≤ B₂) (h₄ : fourierDerivativeL1 f 4 ≤ B₄) :
    ‖(∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x ^ 2 : ℝ))) -
        Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0 / (Real.sqrt t : ℂ)‖ ≤
      (Real.pi * ((B₂ + B₄) * ∫ ξ : ℝ, (1 + ξ ^ 2)⁻¹)) /
        (t * Real.sqrt t) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hm := schwartz_fourier_moment_bound f 2
  simp only [Real.norm_eq_abs, sq_abs] at hm
  have hmoment : (∫ ξ : ℝ, ξ ^ 2 * ‖(𝓕⁻ f) ξ‖) ≤
      (B₂ + B₄) * ∫ ξ : ℝ, (1 + ξ ^ 2)⁻¹ := by
    rw [integral_sq_norm_fourierInv]
    exact hm.trans (mul_le_mul_of_nonneg_right (add_le_add h₂ h₄)
      (integral_nonneg (fun _ => by positivity)))
  have he := (quadratic_stationary_error f ht).trans
    (mul_le_mul_of_nonneg_left hmoment (by positivity))
  have hfactor :
      (Real.sqrt t : ℂ) *
          ((∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x ^ 2 : ℝ))) -
            Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0 / (Real.sqrt t : ℂ)) =
        (Real.sqrt t : ℂ) *
            (∫ x : ℝ, f x * Complex.exp (I * (Real.pi * t * x ^ 2 : ℝ))) -
          Complex.exp ((Real.pi : ℂ) / 4 * I) * f 0 := by
    have hs0 : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    field_simp
  rw [← hfactor, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le] at he
  calc
    _ ≤ ((Real.pi / t) *
        ((B₂ + B₄) * ∫ ξ : ℝ, (1 + ξ ^ 2)⁻¹)) / Real.sqrt t :=
      (le_div_iff₀ hs).2 (by simpa only [mul_comm] using he)
    _ = _ := by ring


/-- The negative-curvature version of the derivative-controlled remainder.
Model phases have negative second derivative, so this is the sign used in the
B-process. It follows by conjugation, with the same amplitude bounds. -/
lemma quadratic_stationary_error_negative_of_derivative_bounds (f : 𝓢(ℝ, ℂ))
    {t B₂ B₄ : ℝ} (ht : 0 < t)
    (h₂ : fourierDerivativeL1 f 2 ≤ B₂) (h₄ : fourierDerivativeL1 f 4 ≤ B₄) :
    ‖(∫ x : ℝ, f x * Complex.exp (-I * (Real.pi * t * x ^ 2 : ℝ))) -
        Complex.exp (-(Real.pi : ℂ) / 4 * I) * f 0 / (Real.sqrt t : ℂ)‖ ≤
      (Real.pi * ((B₂ + B₄) * ∫ ξ : ℝ, (1 + ξ ^ 2)⁻¹)) /
        (t * Real.sqrt t) := by
  let g : 𝓢(ℝ, ℂ) := SchwartzMap.postcompCLM (𝕜 := ℝ)
    Complex.conjCLE.toContinuousLinearMap f
  have hg (x : ℝ) : g x = conj (f x) := rfl
  have hderiv (k : ℕ) (x : ℝ) :
      iteratedDeriv k (g : ℝ → ℂ) x = conj (iteratedDeriv k (f : ℝ → ℂ) x) := by
    change iteratedFDeriv ℝ k (Complex.conjCLE ∘ (f : ℝ → ℂ)) x (fun _ => 1) = _
    rw [Complex.conjCLE.iteratedFDeriv_comp_left]
    rfl
  have hL1 (k : ℕ) : fourierDerivativeL1 g k = fourierDerivativeL1 f k := by
    unfold fourierDerivativeL1
    simp only [hderiv, Complex.norm_conj]
  have he := quadratic_stationary_error_of_derivative_bounds g ht
    (by simpa only [hL1] using h₂) (by simpa only [hL1] using h₄)
  have hphase (a : ℝ) : conj (Complex.exp (-I * (a : ℂ))) =
      Complex.exp (I * (a : ℂ)) := by
    rw [← Complex.exp_conj]
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, neg_neg]
  have hmain : conj (Complex.exp (-(Real.pi : ℂ) / 4 * I)) =
      Complex.exp ((Real.pi : ℂ) / 4 * I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_div₀, map_neg, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  have hconj :
      conj ((∫ x : ℝ, f x * Complex.exp (-I * (Real.pi * t * x ^ 2 : ℝ))) -
        Complex.exp (-(Real.pi : ℂ) / 4 * I) * f 0 / (Real.sqrt t : ℂ)) =
      (∫ x : ℝ, g x * Complex.exp (I * (Real.pi * t * x ^ 2 : ℝ))) -
        Complex.exp ((Real.pi : ℂ) / 4 * I) * g 0 / (Real.sqrt t : ℂ) := by
    rw [map_sub, ← integral_conj, map_div₀, map_mul, hmain, Complex.conj_ofReal]
    simp only [map_mul, hphase, hg]
  rw [← Complex.norm_conj, hconj]
  exact he

end
end Expdb.StationaryPhase
