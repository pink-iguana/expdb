import expdb.basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

open MeasureTheory Real Complex Filter Topology BigOperators
open scoped FourierTransform SchwartzMap ContDiff

noncomputable section

/-!
# Lemma 3.1 (L² Integral Estimate)
Based exactly on the handwritten proof:
  ∫_I |∑ aᵣ e(ξᵣ t)|² dt = (T + O(N)) ∑|aᵣ|²

Proof structure:
  Goal 1: WLOG ∑|aᵣ|² = 1
  Goal 2: ∫_ℝ |∑ aᵣ e(ξᵣ t)|² |ψ̂((t-t₀)/N)|² dt = N  [eq 3.1]
  Goal 3: ∫_J |∑ aᵣ e(ξᵣ t)|² dt ≪ N for |J| = N       [eq 3.2]
  Goal 4: ∫_I F = T - ∫_ℝ F·E  (Fubini identity)
  Goal 5: E(t) ≪ (1 + dist(t,∂I)/N)^{-10}
  Goal 6: ∫_ℝ F·E ≪ N  (dyadic decomposition)
  Goal 7: Assembly → Lemma 3.1
-/
-- ============================================================
-- A fixed smooth bump ψ, supported on [-1/4, 1/4], with L²-norm 1.
-- ============================================================

private def rawBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

private def rawL2 : ℝ := ∫ x : ℝ, (rawBump x) ^ 2

private lemma rawL2_pos : 0 < rawL2 := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := 0)
  · simpa using ((rawBump.contDiff (n := ⊤)).continuous.pow 2)
  · apply ((rawBump.contDiff (n := ⊤)).continuous.pow 2).integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact rawBump.hasCompactSupport.isCompact
    simpa only [Function.support_pow rawBump (by norm_num : 2 ≠ 0)] using
      (subset_tsupport (rawBump : ℝ → ℝ))
  · intro x
    positivity
  · have hzero : (rawBump : ℝ → ℝ) 0 = 1 := by
      apply rawBump.one_of_mem_closedBall
      simp [rawBump, Metric.mem_closedBall]
    simp [hzero]

def ψ (x : ℝ) : ℝ := rawBump x / Real.sqrt rawL2

lemma psi_smooth : ContDiff ℝ ∞ ψ := by
  simpa [ψ] using (rawBump.contDiff (n := ⊤)).div_const (Real.sqrt rawL2)

lemma psi_hasCompactSupport : HasCompactSupport ψ := by
  apply HasCompactSupport.of_support_subset_isCompact rawBump.hasCompactSupport.isCompact
  intro x hx
  apply subset_tsupport rawBump
  simp only [Function.mem_support] at hx ⊢
  intro hzero
  apply hx
  simp [ψ, hzero]

lemma psi_supp (x : ℝ) (hx : ψ x ≠ 0) : |x| ≤ 1 / 4 := by
  have hraw : (rawBump : ℝ → ℝ) x ≠ 0 := by
    intro hzero
    apply hx
    simp [ψ, hzero]
  have hmem : x ∈ Metric.ball (0 : ℝ) rawBump.rOut := by
    rw [← rawBump.support_eq]
    exact hraw
  have : |x| < 1 / 4 := by
    simpa [rawBump, Metric.mem_ball, Real.dist_eq] using hmem
  exact this.le

lemma psi_nonneg (x : ℝ) : 0 ≤ ψ x :=
  div_nonneg (rawBump.nonneg' x) (Real.sqrt_nonneg rawL2)

lemma psi_l2norm : ∫ x : ℝ, (ψ x) ^ 2 = 1 := by
  rw [show (fun x : ℝ => (ψ x) ^ 2) = fun x => (rawBump x) ^ 2 / rawL2 by
        funext x
        simp only [ψ, div_pow]
        rw [Real.sq_sqrt rawL2_pos.le]]
  rw [integral_div]
  exact div_self (ne_of_gt rawL2_pos)

-- ψ̂(u) = ∫_ℝ ψ(x) e(-xu) dx
def psiHat (u : ℝ) : ℂ :=
  ∫ x : ℝ, (ψ x : ℂ) * e (-(x * u))

-- ψ is integrable
lemma psi_integrable : Integrable ψ :=
  psi_smooth.continuous.integrable_of_hasCompactSupport psi_hasCompactSupport

-- ∫ ψ > 0  (from proof: "ψ(t) ≥ 0 and ‖ψ‖_{L²} = 1 so ψ ≢ 0")
lemma psi_integral_pos : 0 < ∫ x : ℝ, ψ x := by
  have hne : ∃ x, ψ x ≠ 0 := by
    by_contra h
    push_neg at h
    have hsquare : ∫ x : ℝ, (ψ x) ^ 2 = 0 := by
      calc
        ∫ x : ℝ, (ψ x) ^ 2
            = ∫ x : ℝ, (0 : ℝ) ^ 2 := by
              congr 1
              ext x
              rw [h x]
        _ = 0 := by simp
    linarith [psi_l2norm, hsquare]

  obtain ⟨x, hx⟩ := hne
  exact integral_pos_of_integrable_nonneg_nonzero
    psi_smooth.continuous psi_integrable psi_nonneg hx

-- ============================================================
-- GOAL 1: WLOG ∑|aᵣ|² = 1
-- "Let M = ∑|aᵣ|², let Aᵣ = aᵣ/M^{1/2} → ∑|Aᵣ|² = 1"
-- ============================================================

lemma goal1 {R : ℕ} (a : Fin R → ℂ) (M : ℝ) (hM : M = ∑ r, ‖a r‖ ^ 2)
    (hpos : 0 < M) :
    ∑ r, ‖(fun r => a r / (Real.sqrt M : ℂ)) r‖ ^ 2 = 1 := by
  simp_rw [norm_div]
  simp only [norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg M)]
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  rw [← hM, Real.sq_sqrt hpos.le]
  exact div_self (ne_of_gt hpos)

/-- The exponential sum occurring in the $L^2$ integral estimate. -/
def expSum {ι : Type*} [Fintype ι] (a : ι → ℂ) (ξ : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ r, a r * e (ξ r * t)

/-- The squared modulus of `expSum`. -/
def expSumSq {ι : Type*} [Fintype ι] (a : ι → ℂ) (ξ : ι → ℝ) (t : ℝ) : ℝ :=
  ‖expSum a ξ t‖ ^ 2

-- ============================================================
-- Plancherel: ‖ψ̂‖_{L²} = ‖ψ‖_{L²} = 1
-- From proof: "∑|aᵣ|² ∫|ψ̂((t-t₀)/N)|² dt, let u=(t-t₀)/N
--             = N ∫|ψ̂(u)|² du = N  (by Plancherel, ‖ψ‖=1)"
-- ============================================================

private lemma psi_complex_hasCompactSupport : HasCompactSupport (fun x : ℝ => (ψ x : ℂ)) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := -1 / 4) (b := 1 / 4)) (by
      intro x hx
      simp only [Function.mem_support] at hx
      have h := psi_supp x (by exact_mod_cast hx)
      simp only [Set.mem_Icc, abs_le] at h ⊢
      simpa only [neg_div] using h)

private lemma psi_complex_smooth : ContDiff ℝ ∞ (fun x : ℝ => (ψ x : ℂ)) := by
  simpa only [ContinuousLinearMap.coe_comp', Function.comp_apply, Complex.ofRealCLM_apply] using
    (Complex.ofRealCLM.contDiff (n := ∞)).comp psi_smooth

private def psiSchwartz : 𝓢(ℝ, ℂ) :=
  psi_complex_hasCompactSupport.toSchwartzMap psi_complex_smooth

private lemma psiHat_eq_fourier : psiHat = 𝓕 (psiSchwartz : ℝ → ℂ) := by
  funext u
  rw [Real.fourier_real_eq]
  simp [psiSchwartz, psiHat, e, Circle.smul_def, Real.fourierChar_apply]
  apply integral_congr_ae
  filter_upwards with x
  ring

lemma psiHat_l2 : ∫ u : ℝ, ‖psiHat u‖ ^ 2 = 1 := by
  simp_rw [psiHat_eq_fourier]
  rw [← SchwartzMap.fourier_coe, SchwartzMap.integral_norm_sq_fourier]
  simpa [psiSchwartz, Real.norm_eq_abs, abs_of_nonneg (psi_nonneg _)] using psi_l2norm

-- ============================================================
-- ψ̂ is rapidly decaying
-- From proof (Goal 5 Step 1):
-- "ψ̂(u) = 1/(2πiu) ψ̂'(u), repeat k times → |ψ̂(u)| ≪ Cₖ/(1+|u|)ᵏ"
-- ============================================================

lemma psiHat_decay (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, ‖psiHat u‖ ≤ C * (1 + |u|) ^ (-(K : ℝ)) := by
  let g : 𝓢(ℝ, ℂ) := 𝓕 psiSchwartz
  have hfourier : ∀ u : ℝ, psiHat u = g u := by
    intro u
    exact congr_fun psiHat_eq_fourier u
  let c : ℝ := 2 ^ K * (Finset.Iic (K, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
  refine ⟨|c| + 1, by positivity, ?_⟩
  intro u
  have hweight : (1 + |u|) ^ K * ‖psiHat u‖ ≤ c := by
    have hw := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (K, 0)) (k := K) (n := 0) le_rfl le_rfl g u
    rw [norm_iteratedFDeriv_zero, ← hfourier u] at hw
    simpa [c, Real.norm_eq_abs] using hw
  have hbase : 0 < 1 + |u| := by positivity
  have hpow : 0 < (1 + |u|) ^ K := by positivity
  have hrpow : (1 + |u|) ^ (-(K : ℝ)) = ((1 + |u|) ^ K)⁻¹ := by
    rw [← Real.rpow_natCast, Real.rpow_neg hbase.le]
  rw [hrpow, ← div_eq_mul_inv]
  apply (le_div_iff₀ hpow).2
  calc
    ‖psiHat u‖ * (1 + |u|) ^ K =
        (1 + |u|) ^ K * ‖psiHat u‖ := by ring
    _ ≤ c := hweight
    _ ≤ |c| + 1 := by linarith [le_abs_self c]

-- ============================================================
-- ψ̂ has positive lower bound near 0
-- From proof (Goal 3 Step 2):
-- "ψ̂ is continuous, ψ̂(0) = ∫ψ > 0, choose ε = ψ̂(0)/2
--  → ψ̂(u) > ψ̂(0)/2 for |u| < δ → |ψ̂(u)|² ≥ c·1_{[-δ/2,δ/2]}(u)"
-- ============================================================

lemma psiHat_lower_bound :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧
    ∀ u : ℝ, |u| ≤ δ → c ≤ ‖psiHat u‖ ^ 2 := by
  have hcts : Continuous psiHat := by
    rw [psiHat_eq_fourier]
    exact (𝓕 psiSchwartz).continuous
  have hpsi0_eq : (psiHat 0).re = ∫ x : ℝ, ψ x := by
    simp only [psiHat, mul_zero, neg_zero, e_zero, mul_one]
    have hψc : Integrable (fun x : ℝ => (ψ x : ℂ)) := psi_integrable.ofReal
    simpa using (integral_re hψc).symm
  have hpsi0 : 0 < (psiHat 0).re := by
    rw [hpsi0_eq]
    exact psi_integral_pos
  have hpos : 0 < ‖psiHat 0‖ := by
    rw [norm_pos_iff]
    intro hzero
    have : (psiHat 0).re = 0 := by rw [hzero]; rfl
    linarith
  set v₀ := ‖psiHat 0‖
  obtain ⟨δ, hδ, hball⟩ :=
    (Metric.continuousAt_iff.mp hcts.continuousAt) (v₀ / 2) (by linarith)
  refine ⟨(v₀ / 2) ^ 2, δ / 2, by positivity, by positivity, ?_⟩
  intro u hu
  have hdist : dist (psiHat u) (psiHat 0) < v₀ / 2 := by
    apply hball
    rw [Real.dist_eq]
    simp only [sub_zero]
    exact lt_of_le_of_lt hu (by linarith)
  have hbound : v₀ - ‖psiHat u‖ < v₀ / 2 := by
    calc
      v₀ - ‖psiHat u‖ = ‖psiHat 0‖ - ‖psiHat u‖ := rfl
      _ ≤ ‖psiHat 0 - psiHat u‖ := norm_sub_norm_le _ _
      _ = dist (psiHat u) (psiHat 0) := by
        rw [dist_eq_norm_sub, norm_sub_rev]
      _ < v₀ / 2 := hdist
  have hball' : v₀ / 2 < ‖psiHat u‖ := by linarith
  nlinarith [norm_nonneg (psiHat u)]

-- ============================================================
-- GOAL 2: ∫_ℝ F(t) |ψ̂((t-t₀)/N)|² dt = N   [equation (3.1)]
--
-- Apply Plancherel once to the sum of translates
--   G(x) = ∑ᵣ aᵣe(ξᵣt₀)ψ(x + Nξᵣ).
-- Its Fourier transform is the weighted exponential sum after t=t₀+Nu,
-- while the translates of ψ form an orthonormal family by separation.
-- ============================================================

-- Package translates of the concrete bump as Schwartz functions.
private def psiShift (w : ℝ) : 𝓢(ℝ, ℂ) := by
  let f : ℝ → ℂ := fun x => (ψ (x + w) : ℂ)
  have hcomp : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := -w - 1 / 4) (b := -w + 1 / 4))
    intro x hx
    change (ψ (x + w) : ℂ) ≠ 0 at hx
    have hx' : ψ (x + w) ≠ 0 := by exact_mod_cast hx
    have h := abs_le.mp (psi_supp (x + w) hx')
    constructor <;> linarith
  have hsmooth : ContDiff ℝ ∞ f := by
    simpa only [f, Function.comp_apply] using
      psi_complex_smooth.comp (contDiff_id.add contDiff_const)
  exact hcomp.toSchwartzMap hsmooth

private lemma psiShift_apply (w x : ℝ) : psiShift w x = ψ (x + w) := rfl

private lemma fourier_psiShift (w u : ℝ) :
    (𝓕 (psiShift w : ℝ → ℂ)) u = e (w * u) * psiHat u := by
  have hcoe : (psiShift w : ℝ → ℂ) = fun x : ℝ => (ψ (x + w) : ℂ) := by
    ext x
    exact_mod_cast psiShift_apply w x
  rw [hcoe, Real.fourier_real_eq]
  have hpsi : psiHat u = ∫ x : ℝ, e (-(x * u)) * (ψ x : ℂ) := by
    simp only [psiHat]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hpsi]
  have ht := congr_fun
    (Fourier.fourierIntegral_comp_add_right 𝐞 volume (fun x : ℝ => (ψ x : ℂ)) w) u
  simpa [Fourier.fourierIntegral_def, Circle.smul_def, e, Real.fourierChar_apply] using ht

private lemma psiShift_inner_eq_zero {v w : ℝ} (hvw : 1 ≤ |v - w|) :
    ∫ x : ℝ, inner ℂ (psiShift v x) (psiShift w x) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with x
  by_cases hxv : ψ (x + v) = 0
  · simp [psiShift_apply, hxv]
  by_cases hxw : ψ (x + w) = 0
  · simp [psiShift_apply, hxw]
  exfalso
  have hv := psi_supp (x + v) hxv
  have hw := psi_supp (x + w) hxw
  have hbound : |v - w| ≤ 1 / 2 := by
    calc
      |v - w| = |(x + v) - (x + w)| := by ring_nf
      _ ≤ |x + v| + |x + w| := abs_sub _ _
      _ ≤ 1 / 4 + 1 / 4 := by linarith
      _ = 1 / 2 := by norm_num
  linarith

private lemma psiShift_inner_self (w : ℝ) :
    ∫ x : ℝ, inner ℂ (psiShift w x) (psiShift w x) = 1 := by
  calc
    ∫ x : ℝ, inner ℂ (psiShift w x) (psiShift w x) =
        ∫ x : ℝ, (((ψ (x + w)) ^ 2 : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards with x
          simp [psiShift_apply, abs_of_nonneg (psi_nonneg _)]
    _ = ((∫ x : ℝ, (ψ (x + w)) ^ 2 : ℝ) : ℂ) := integral_ofReal
    _ = ((∫ x : ℝ, (ψ x) ^ 2 : ℝ) : ℂ) := by
      rw [integral_add_right_eq_self (fun x : ℝ => (ψ x) ^ 2) w]
    _ = 1 := by rw [psi_l2norm]; norm_num

private lemma psiShift_orthonormal {R : ℕ} (ξ : Fin R → ℝ) (N : ℝ) (hN : 0 < N)
    (hsep : IsSeparatedFamily (1 / N) ξ) :
    Orthonormal ℂ (fun r => (psiShift (N * ξ r)).toLp 2) := by
  rw [orthonormal_iff_ite]
  intro r s
  rw [SchwartzMap.inner_toL2_toL2_eq
    (psiShift (N * ξ r)) (psiShift (N * ξ s)) volume]
  by_cases hrs : r = s
  · subst s
    rw [if_pos rfl, psiShift_inner_self]
  · rw [if_neg hrs]
    apply psiShift_inner_eq_zero
    rw [show N * ξ r - N * ξ s = N * (ξ r - ξ s) by ring, abs_mul, abs_of_pos hN]
    calc
      1 = N * (1 / N) := by field_simp
      _ ≤ N * |ξ r - ξ s| := mul_le_mul_of_nonneg_left (hsep r s hrs) hN.le

theorem goal2 {R : ℕ} (a : Fin R → ℂ) (ξ : Fin R → ℝ)
    (N : ℝ) (hN : 0 < N) (t₀ : ℝ)
    (hnorm : ∑ r, ‖a r‖ ^ 2 = 1)
    (hsep : IsSeparatedFamily (1 / N) ξ) :
    ∫ t : ℝ, expSumSq a ξ t * ‖psiHat ((t - t₀) / N)‖ ^ 2 = N := by
  let c : Fin R → ℂ := fun r => a r * e (ξ r * t₀)
  let G : 𝓢(ℝ, ℂ) := ∑ r, c r • psiShift (N * ξ r)
  have hfourier (u : ℝ) :
      (𝓕 G : 𝓢(ℝ, ℂ)) u = expSum a ξ (t₀ + N * u) * psiHat u := by
    change (SchwartzMap.fourierTransformCLM ℂ
      (∑ r, c r • psiShift (N * ξ r))) u = _
    rw [map_sum]
    simp_rw [map_smul]
    have hsum_apply (s : Finset (Fin R)) (f : Fin R → 𝓢(ℝ, ℂ)) :
        (∑ r ∈ s, f r) u = ∑ r ∈ s, f r u := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert r s hrs ih =>
          simp [Finset.sum_insert, hrs, SchwartzMap.add_apply, ih]
    rw [hsum_apply Finset.univ]
    simp_rw [SchwartzMap.smul_apply, smul_eq_mul]
    have hshift (r : Fin R) :
        SchwartzMap.fourierTransformCLM ℂ (psiShift (N * ξ r)) u =
          e ((N * ξ r) * u) * psiHat u := by
      rw [SchwartzMap.fourierTransformCLM_apply]
      rw [SchwartzMap.fourier_coe]
      exact fourier_psiShift (N * ξ r) u
    simp_rw [hshift]
    rw [show (∑ r, c r * (e ((N * ξ r) * u) * psiHat u)) =
        (∑ r, c r * e ((N * ξ r) * u)) * psiHat u by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      ring]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    simp only [c]
    calc
      a r * e (ξ r * t₀) * e ((N * ξ r) * u) =
          a r * (e (ξ r * t₀) * e ((N * ξ r) * u)) := by ring
      _ = a r * e (ξ r * (t₀ + N * u)) := by
        rw [← e_add]
        congr 2
        ring
  have hG_toLp :
      G.toLp 2 = ∑ r, c r • (psiShift (N * ξ r)).toLp 2 := by
    change SchwartzMap.toLpCLM ℂ ℂ 2 volume G = _
    simp [G]
  have hG_norm : ‖G.toLp 2‖ ^ 2 = 1 := by
    have horth := (psiShift_orthonormal ξ N hN hsep).inner_sum c c Finset.univ
    have hc_norm : ∑ r, ‖c r‖ ^ 2 = 1 := by
      simpa only [c, norm_mul, norm_e, mul_one] using hnorm
    have hsum_norm :
        ‖∑ r, c r • (psiShift (N * ξ r)).toLp 2‖ ^ 2 = ∑ r, ‖c r‖ ^ 2 := by
      calc
        ‖∑ r, c r • (psiShift (N * ξ r)).toLp 2‖ ^ 2 =
            (inner ℂ (∑ r, c r • (psiShift (N * ξ r)).toLp 2)
              (∑ r, c r • (psiShift (N * ξ r)).toLp 2)).re :=
                by
                  exact norm_sq_eq_re_inner (𝕜 := ℂ)
                    (∑ r, c r • (psiShift (N * ξ r)).toLp 2)
        _ = (∑ r, (starRingEnd ℂ) (c r) * c r).re := congrArg Complex.re horth
        _ = ∑ r, ‖c r‖ ^ 2 := by
          rw [Complex.re_sum]
          apply Finset.sum_congr rfl
          intro r _
          rw [Complex.conj_mul']
          rw [← Complex.ofReal_pow, Complex.ofReal_re]
    rw [hG_toLp, hsum_norm, hc_norm]
  have hG_inner : inner ℂ (G.toLp 2) (G.toLp 2) = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    simpa only [Complex.ofReal_pow, Complex.ofReal_one] using
      congrArg (fun x : ℝ => (x : ℂ)) hG_norm
  have hG_l2 : ∫ x : ℝ, ‖G x‖ ^ 2 = 1 := by
    have hinner_integral : ∫ x : ℝ, inner ℂ (G x) (G x) = 1 := by
      rw [← SchwartzMap.inner_toL2_toL2_eq G G volume]
      exact hG_inner
    apply Complex.ofRealLI.injective
    simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using hinner_integral
  let H : ℝ → ℝ := fun u => ‖(𝓕 G : 𝓢(ℝ, ℂ)) u‖ ^ 2
  have hrewrite : (fun t : ℝ =>
      expSumSq a ξ t * ‖psiHat ((t - t₀) / N)‖ ^ 2) =
      fun t => H ((1 / N) * t + (-t₀ / N)) := by
    funext t
    rw [show (1 / N) * t + -t₀ / N = (t - t₀) / N by
      field_simp
      ring]
    have hu : t₀ + N * ((t - t₀) / N) = t := by
      field_simp
      ring
    simp only [H, hfourier, hu, expSumSq, norm_mul, mul_pow]
  rw [hrewrite]
  let K : ℝ → ℝ := fun x => H (x + (-t₀ / N))
  change ∫ t : ℝ, K ((1 / N) * t) = N
  rw [Measure.integral_comp_mul_left K (1 / N)]
  rw [show (∫ y : ℝ, K y) = ∫ y : ℝ, H y by
    exact integral_add_right_eq_self H (-t₀ / N)]
  rw [show (∫ y : ℝ, H y) = 1 by
    simpa only [H] using (SchwartzMap.integral_norm_sq_fourier G).trans hG_l2]
  simp [abs_of_pos hN]

-- ============================================================
-- GOAL 3: ∫_J |∑ aᵣ e(ξᵣ t)|² dt ≪ N for |J| = N  [eq (3.2)]
--
-- Enlarge the smoothing scale from N to M ≍ψ N so that the whole normalized
-- interval lies in the neighbourhood where |ψ̂|² has a positive lower bound.
-- Goal 2 at scale M then gives c·∫_J F ≤ M ≪ψ N.
-- ============================================================

theorem goal3 {R : ℕ} (a : Fin R → ℂ) (ξ : Fin R → ℝ)
    (N : ℝ) (hN : 0 < N)
    (hnorm : ∑ r, ‖a r‖ ^ 2 = 1)
    (hsep : IsSeparatedFamily (1 / N) ξ)
    (a₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
    ∫ t in Set.Icc a₀ (a₀ + N), expSumSq a ξ t ≤ C * N := by
  obtain ⟨c, δ, hc, hδ, hlb⟩ := psiHat_lower_bound
  -- Enlarge the smoothing scale so that the whole interval lies in the
  -- neighbourhood on which `psiHat_lower_bound` applies.
  set M := N * (1 + 1 / δ)
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hNM : N ≤ M := by
    have hinvδ : 0 ≤ 1 / δ := by positivity
    dsimp [M]
    nlinarith
  have hsepM : IsSeparatedFamily (1 / M) ξ := by
    intro r s hrs
    apply le_trans _ (hsep r s hrs)
    apply (div_le_div_iff₀ hM hN).2
    simpa using hNM
  set t₀ := a₀ + N / 2
  have h2 := goal2 a ξ M hM t₀ hnorm hsepM
  have hlb_J : ∀ t ∈ Set.Icc a₀ (a₀ + N),
      c ≤ ‖psiHat ((t - t₀) / M)‖ ^ 2 := by
    intro t ht
    apply hlb
    rw [abs_div, abs_of_pos hM]
    apply (div_le_iff₀ hM).2
    have habs : |t - t₀| ≤ N / 2 := by
      rw [abs_le]
      constructor <;> simp only [t₀] <;> linarith [ht.1, ht.2]
    apply habs.trans
    have hscale : δ * M = δ * N + N := by
      dsimp [M]
      field_simp
    rw [hscale]
    nlinarith
  have hFcont : Continuous (expSumSq a ξ) := by
    unfold expSumSq expSum e
    fun_prop
  have hweighted : Integrable (fun t : ℝ =>
      expSumSq a ξ t * ‖psiHat ((t - t₀) / M)‖ ^ 2) := by
    by_contra h
    rw [integral_undef h] at h2
    linarith
  refine ⟨(1 + 1 / δ) / c, by positivity, ?_⟩
  have hFub : c * ∫ t in Set.Icc a₀ (a₀ + N), expSumSq a ξ t ≤ M := by
    calc c * ∫ t in Set.Icc a₀ (a₀ + N), expSumSq a ξ t
        = ∫ t in Set.Icc a₀ (a₀ + N), c * expSumSq a ξ t :=
            (integral_const_mul _ _).symm
      _ ≤ ∫ t in Set.Icc a₀ (a₀ + N),
            expSumSq a ξ t * ‖psiHat ((t - t₀) / M)‖ ^ 2 := by
          apply setIntegral_mono_on
          · exact (continuous_const.mul hFcont).integrableOn_Icc
          · exact hweighted.integrableOn
          · exact measurableSet_Icc
          · intro t ht
            calc
              c * expSumSq a ξ t = expSumSq a ξ t * c := by ring
              _ ≤ expSumSq a ξ t * ‖psiHat ((t - t₀) / M)‖ ^ 2 :=
                mul_le_mul_of_nonneg_left (hlb_J t ht) (sq_nonneg _)
      _ ≤ ∫ t : ℝ, expSumSq a ξ t * ‖psiHat ((t - t₀) / M)‖ ^ 2 :=
          setIntegral_le_integral hweighted (ae_of_all _ fun t =>
            mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = M := h2
  rw [show (1 + 1 / δ) / c * N = M / c by
    dsimp [M]
    ring]
  apply (le_div_iff₀ hc).2
  nlinarith

-- ============================================================
-- GOAL 4: ∫_I F = T - ∫_ℝ F·E  (Fubini identity)
--
-- From handwritten proof:
--   By (3.1): ∫_ℝ F|ψ̂((t-t₀)/N)|² dt = N
--   Integrate over t₀ ∈ I: ∫_I N dt₀ = NT
--   By Fubini: NT = ∫_I ∫_ℝ F|ψ̂|² dt dt₀ = ∫_ℝ F(∫_I |ψ̂|² dt₀) dt
--   Rearrange: ∫_I F = T - ∫_ℝ F·(1/N ∫_I |ψ̂|² dt₀ - 1_I) dt
-- ============================================================

-- E(t) = 1/N ∫_I |ψ̂((t-t₀)/N)|² dt₀ - 1_I(t)
def kernelE (N : ℝ) (a₀ b₀ : ℝ) (t : ℝ) : ℝ :=
  (1 / N) * (∫ t₀ in Set.Icc a₀ b₀, ‖psiHat ((t - t₀) / N)‖ ^ 2) -
  Set.indicator (Set.Icc a₀ b₀) (fun _ => (1 : ℝ)) t

theorem goal4 {R : ℕ} (a : Fin R → ℂ) (ξ : Fin R → ℝ)
    (N : ℝ) (hN : 0 < N)
    (hnorm : ∑ r, ‖a r‖ ^ 2 = 1)
    (hsep : IsSeparatedFamily (1 / N) ξ)
    (a₀ b₀ : ℝ) (T : ℝ) (hT : T = b₀ - a₀) (hab : a₀ ≤ b₀) :
    ∫ t in Set.Icc a₀ b₀, expSumSq a ξ t =
    T - ∫ t : ℝ, expSumSq a ξ t * kernelE N a₀ b₀ t := by
  let F : ℝ → ℝ := expSumSq a ξ
  let K : ℝ → ℝ → ℝ := fun t₀ t => ‖psiHat ((t - t₀) / N)‖ ^ 2
  let H : ℝ × ℝ → ℝ := fun p => F p.2 * K p.1 p.2
  have hF_nonneg : ∀ t, 0 ≤ F t := fun t => sq_nonneg _
  have hK_nonneg : ∀ t₀ t, 0 ≤ K t₀ t := fun t₀ t => sq_nonneg _
  have hH_nonneg : ∀ p, 0 ≤ H p := fun p =>
    mul_nonneg (hF_nonneg p.2) (hK_nonneg p.1 p.2)
  have hF_cont : Continuous F := by
    dsimp [F]
    unfold expSumSq expSum e
    fun_prop
  have hpsiHat_cont : Continuous psiHat := by
    rw [psiHat_eq_fourier]
    exact (𝓕 psiSchwartz).continuous
  have hK_cont : Continuous (fun p : ℝ × ℝ => K p.1 p.2) := by
    exact ((hpsiHat_cont.comp
      ((continuous_snd.sub continuous_fst).div_const N)).norm.pow 2)
  have hH_cont : Continuous H :=
    (hF_cont.comp continuous_snd).mul hK_cont
  -- From (3.1): ∫_ℝ F(t)|ψ̂((t-t₀)/N)|² dt = N for each t₀.
  have h31 : ∀ t₀ : ℝ,
      ∫ t : ℝ, H (t₀, t) = N := by
    intro t₀
    simpa only [H, F, K] using goal2 a ξ N hN t₀ hnorm hsep
  have hslice : ∀ t₀ : ℝ, Integrable (fun t => H (t₀, t)) := by
    intro t₀
    by_contra h
    have hzero := h31 t₀
    rw [integral_undef h] at hzero
    linarith
  -- The product-space integrability follows from the already evaluated slices.
  have hH_int : Integrable H ((volume.restrict (Set.Icc a₀ b₀)).prod volume) := by
    apply (integrable_prod_iff hH_cont.aestronglyMeasurable).2
    constructor
    · exact ae_of_all _ hslice
    · have hmarginal : (fun t₀ : ℝ => ∫ t : ℝ, ‖H (t₀, t)‖) = fun _ => N := by
        funext t₀
        rw [show (fun t : ℝ => ‖H (t₀, t)‖) = fun t => H (t₀, t) by
          funext t
          exact Real.norm_of_nonneg (hH_nonneg (t₀, t))]
        exact h31 t₀
      rw [hmarginal]
      exact integrableOn_const measure_Icc_lt_top.ne
  -- Integrate the constant marginal over t₀ ∈ I.
  have hNT : ∫ _ in Set.Icc a₀ b₀, N = N * T := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le hab, smul_eq_mul, hT]
    ring
  -- Fubini, with the interval restriction built into the first measure.
  have hswap :
      (∫ t₀ in Set.Icc a₀ b₀, ∫ t : ℝ, H (t₀, t)) =
      ∫ t : ℝ, ∫ t₀ in Set.Icc a₀ b₀, H (t₀, t) := by
    exact integral_integral_swap hH_int
  have hFubini : ∫ t : ℝ, F t * (∫ t₀ in Set.Icc a₀ b₀, K t₀ t) = N * T := by
    calc
      ∫ t : ℝ, F t * (∫ t₀ in Set.Icc a₀ b₀, K t₀ t) =
          ∫ t : ℝ, ∫ t₀ in Set.Icc a₀ b₀, H (t₀, t) := by
            congr 1
            ext t
            change F t * (∫ t₀ in Set.Icc a₀ b₀, K t₀ t) =
              ∫ t₀ in Set.Icc a₀ b₀, F t * K t₀ t
            rw [integral_const_mul]
      _ = ∫ t₀ in Set.Icc a₀ b₀, ∫ t : ℝ, H (t₀, t) := hswap.symm
      _ = ∫ _ in Set.Icc a₀ b₀, N := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t₀ _
        exact h31 t₀
      _ = N * T := hNT
  have hFK_int : Integrable (fun t : ℝ => F t *
      (∫ t₀ in Set.Icc a₀ b₀, K t₀ t)) := by
    have hmarginal := hH_int.integral_prod_right
    apply hmarginal.congr
    apply ae_of_all
    intro t
    change (∫ t₀ in Set.Icc a₀ b₀, F t * K t₀ t) =
      F t * (∫ t₀ in Set.Icc a₀ b₀, K t₀ t)
    rw [integral_const_mul]
  have hFI_int : Integrable ((Set.Icc a₀ b₀).indicator F) :=
    hF_cont.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hexpand : (fun t : ℝ => expSumSq a ξ t * kernelE N a₀ b₀ t) =
      fun t => (1 / N) * (F t * (∫ t₀ in Set.Icc a₀ b₀, K t₀ t)) -
        (Set.Icc a₀ b₀).indicator F t := by
    funext t
    simp only [kernelE, F, K]
    by_cases ht : t ∈ Set.Icc a₀ b₀
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      ring
  rw [hexpand, integral_sub (hFK_int.const_mul _) hFI_int,
    integral_const_mul, hFubini, integral_indicator measurableSet_Icc]
  field_simp
  ring

-- ============================================================
-- GOAL 5: E(t) ≪ (1 + dist(t,∂I)/N)^{-10}
--
--   Step 1: ψ̂ rapidly decaying (IBP)
--   Step 2: 1/N ∫_I |ψ̂((t-t₀)/N)|² dt₀ = ∫_{I_t} |ψ̂(u)|² du
--           where I_t = [(t-b₀)/N, (t-a₀)/N]
--   Step 3 (t ∈ I): 0 ∈ I_t, so = 1 - ∫_{ℝ\I_t} |ψ̂|² ≪ (1+d_t)^{-10}
--   Step 4 (t ∉ I): 0 ∉ I_t, so = ∫_{I_t} |ψ̂|² ≪ (1+d_t)^{-10}
-- ============================================================

theorem goal5 (N : ℝ) (hN : 0 < N)
    (a₀ b₀ : ℝ) (hab : a₀ ≤ b₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    |kernelE N a₀ b₀ t| ≤
    C * (1 + min (|t - a₀| / N) (|t - b₀| / N)) ^ (-(10 : ℝ)) := by
  obtain ⟨C_d, hC_d, hdecay⟩ := psiHat_decay 12
  refine ⟨C_d ^ 2 * 8, by positivity, ?_⟩
  intro t
have hint : Integrable (fun u => ‖psiHat u‖ ^ 2) := by
    apply Integrable.mono (f := fun u => C_d * (1 + |u|)^(-(12:ℝ)))
    · apply Integrable.const_mul
      exact integrable_rpow_neg (by norm_num)
    · apply ae_of_all; intro u
      exact hdecay u
  have hint2 : Integrable (fun u => (1 + |u|)^(-(12:ℝ))) := by
    apply integrable_rpow_neg_abs (by norm_num : (1:ℝ) < 12)
  -- Step 2: Substitution u = (t-t₀)/N
  -- 1/N ∫_I |ψ̂((t-t₀)/N)|² dt₀ = ∫_{I_t} |ψ̂(u)|² du
  have hsubst : (1 / N) * ∫ t₀ in Set.Icc a₀ b₀,
      ‖psiHat ((t - t₀) / N)‖ ^ 2 =
      ∫ u in Set.Icc ((t - b₀) / N) ((t - a₀) / N),
        ‖psiHat u‖ ^ 2 := by
    rw [one_div, ← intervalIntegral.integral_comp_sub_left
      (fun u => ‖psiHat u‖ ^ 2) t]
    simp [Set.uIcc_of_le (div_le_div_of_nonneg_right (by linarith) hN)]
    congr 1 <;> [field_simp; field_simp; ring]
  -- Tail bound: ∫_{|u|≥d} |ψ̂|² ≤ 2C²/(11(1+d)^{11}) ≪ (1+d)^{-10}
  have htail : ∀ d : ℝ, 0 ≤ d →
      ∫ u in {u : ℝ | d ≤ |u|}, ‖psiHat u‖ ^ 2 ≤
      C_d ^ 2 * 8 * (1 + d) ^ (-(10 : ℝ)) := by
    intro d hd
    calc ∫ u in {u | d ≤ |u|}, ‖psiHat u‖ ^ 2
        ≤ C_d ^ 2 * ∫ u in {u | d ≤ |u|}, (1 + |u|) ^ (-(12 : ℝ)) := by
          apply set_integral_mono_ae
          · exact hint
          · exact (Integrable.const_mul hint2_)
          · apply ae_of_all; intro u
            have := hdecay u
            nlinarith [norm_nonneg (psiHat u), sq_nonneg (‖psiHat u‖)]
      -- ∫_{|u|≥d} (1+|u|)^{-12} du = 2/(11(1+d)^{11})
      _ ≤ C_d ^ 2 * (8 * (1 + d) ^ (-(10 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hcalc : ∫ u in Set.Ici d, (1 + u) ^ (-(12 : ℝ)) =
              (1/11) * (1 + d) ^ (-(11 : ℝ)) := by
            simp [MeasureTheory.integral_Ici_rpow_of_lt (by norm_num : -(12:ℝ) < -1)]
            ring
          calc ∫ u in {u : ℝ | d ≤ |u|}, (1 + |u|) ^ (-(12 : ℝ))
              ≤ 2 * ∫ u in Set.Ici d, (1 + u) ^ (-(12 : ℝ)) := by
                rw [show {u : ℝ | d ≤ |u|} = Set.Ici d ∪ Set.Iic (-d) from by
                  ext u; simp [abs_le, le_abs]]
                rw [integral_union (by simp; intro a h1 h2; linarith)
                  measurableSet_Ici]
                · have hsym : ∫ u in Set.Iic (-d), (1 + |u|) ^ (-(12 : ℝ)) =
                      ∫ u in Set.Ici d, (1 + u) ^ (-(12 : ℝ)) := by
                    rw [← integral_comp_neg (f := fun u => (1 + |u|)^(-(12:ℝ)))]
                    simp [abs_neg]
                    congr 1; ext u
                    rw [show Set.Ici d = {u | d ≤ u} from rfl]
                    simp [abs_of_nonneg]
                  rw [show (∫ u in Set.Ici d, (1 + |u|)^(-(12:ℝ))) =
                      ∫ u in Set.Ici d, (1+u)^(-(12:ℝ)) from by
                    congr 1; ext u
                    congr 2; exact abs_of_nonneg (le_trans hd (Set.mem_Ici.mp ‹_›))]
                  linarith [integral_nonneg (fun u => by positivity)]
                · sorry; · sorry
            _ = 2 * (1/11) * (1+d)^(-(11:ℝ)) := by rw [hcalc]; ring
            _ ≤ 8 * (1+d)^(-(10:ℝ)) := by
                have h1d : 1 + d ≥ 1 := by linarith
                nlinarith [Real.rpow_le_rpow_of_exponent_ge h1d
                  (by norm_num : -(11:ℝ) ≤ -(10:ℝ))]
      _ = C_d ^ 2 * 8 * (1 + d) ^ (-(10 : ℝ)) := by ring
  -- Set d_t = dist(t, ∂I)/N
  set d_t := min (|t - a₀| / N) (|t - b₀| / N)
  -- Case analysis: t ∈ I or t ∉ I
  by_cases htI : t ∈ Set.Icc a₀ b₀
  · -- STEP 3: t ∈ I → 0 ∈ I_t
    -- |E(t)| = |∫_{ℝ\I_t} |ψ̂|²| ≤ ∫_{|u|≥d_t} |ψ̂|²
    have hind : Set.indicator (Set.Icc a₀ b₀) (fun _ => (1:ℝ)) t = 1 :=
      Set.indicator_of_mem htI _
    simp only [kernelE, hind, hsubst]
    -- 0 ∈ I_t because t ∈ [a₀,b₀]
    have h0_in : (0:ℝ) ∈ Set.Icc ((t-b₀)/N) ((t-a₀)/N) := by
      constructor
      · apply div_nonpos_of_nonpos_of_nonneg <;> linarith [htI.2]
      · apply div_nonneg <;> linarith [htI.1]
    -- ∫_{I_t} = ∫_ℝ - ∫_{ℝ\I_t} = 1 - ∫_{ℝ\I_t}
    rw [psiHat_l2.symm]
    rw [← integral_add_compl measurableSet_Icc (by sorry)]
    simp only [add_sub_cancel_left]
    rw [abs_neg]
    calc |∫ u in (Set.Icc _ _)ᶜ, ‖psiHat u‖^2|
        ≤ ∫ u in (Set.Icc _ _)ᶜ, ‖psiHat u‖^2 :=
          le_abs_self _
      _ ≤ ∫ u in {u | d_t ≤ |u|}, ‖psiHat u‖^2 := by
          apply set_integral_mono_set
          · exact fun u => sq_nonneg _
          -- ℝ\I_t ⊆ {|u| ≥ d_t} because 0 ∈ I_t
          · apply ae_of_all; intro u hu
            simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hu
            simp only [Set.mem_setOf_eq]
            -- Geometric argument: since 0 ∈ I_t, u outside I_t means |u| ≥ d_t
            cases hu with
            | inl h =>
              rw [abs_of_nonpos (le_of_lt h)]
              simp [d_t]; constructor
              · linarith [h, h0_in.1]
              · linarith [h, (t - b₀)/N |>.neg_le_abs]
            | inr h =>
              rw [abs_of_pos h]
              simp [d_t]; constructor
              · linarith [h0_in.2]
              · linarith [h, le_abs_self ((t-b₀)/N)]
      _ ≤ C_d^2 * 8 * (1 + d_t)^(-(10:ℝ)) :=
          htail d_t (by simp [d_t]; positivity)
  · -- STEP 4: t ∉ I → 0 ∉ I_t
    have hind : Set.indicator (Set.Icc a₀ b₀) (fun _ => (1:ℝ)) t = 0 :=
      Set.indicator_of_not_mem htI _
    simp only [kernelE, hind, hsubst, sub_zero]
    rw [abs_of_nonneg (integral_nonneg (fun u => sq_nonneg _))]
    -- 0 ∉ I_t because t ∉ [a₀,b₀]
    have h0_out : (0:ℝ) ∉ Set.Icc ((t-b₀)/N) ((t-a₀)/N) := by
      simp only [Set.mem_Icc, not_and_or, not_le]
      cases Set.not_mem_Icc.mp htI with
      | inl h => right; apply div_pos_of_neg_of_neg <;> linarith
      | inr h => left; apply div_neg_of_pos_of_neg <;> linarith
    calc ∫ u in Set.Icc ((t-b₀)/N) ((t-a₀)/N), ‖psiHat u‖^2
        ≤ ∫ u in {u | d_t ≤ |u|}, ‖psiHat u‖^2 := by
          apply set_integral_mono_set
          · exact fun u => sq_nonneg _
          -- I_t ⊆ {|u| ≥ d_t} because 0 ∉ I_t
          · apply ae_of_all; intro u hu
            simp only [Set.mem_setOf_eq]
            simp only [Set.mem_Icc] at hu
            -- Geometric: 0 ∉ I_t → I_t entirely on one side → |u| ≥ d_t
            cases Set.not_mem_Icc.mp h0_out with
            | inl h =>
              -- I_t is entirely negative
              rw [abs_of_nonpos (le_trans hu.2 (le_of_lt h))]
              simp [d_t]
              constructor
              · linarith [hu.1]
              · linarith [hu.2, h]
            | inr h =>
              -- I_t is entirely positive
              rw [abs_of_nonneg (le_trans (le_of_lt (lt_of_not_le h)) hu.1)]
              simp [d_t]
              constructor
              · linarith [hu.1, h]
              · linarith [hu.2]
      _ ≤ C_d^2 * 8 * (1 + d_t)^(-(10:ℝ)) :=
          htail d_t (by simp [d_t]; positivity)

-- ============================================================
-- GOAL 6: ∫_ℝ F·E ≪ N  (dyadic decomposition)
--
-- From handwritten proof:
--   Case 1 (N ≪ T): divide I into J_k with |J_k| = N
--     Layer ℓ: J with dist(J,∂I) ~ 2^ℓN, contains ~2^ℓ intervals
--     |E(t)| ≪ (2^ℓ)^{-10}  (by Goal 5)
--     ∫_J F ≤ CN  (by Goal 3 = eq 3.2)
--     Sum: ∑_ℓ 2^ℓ · CN · 2^{-10ℓ} = CN ∑ 2^{-9ℓ} ≪ N
--   Cases B,C (outside I): same method
--   Case 2 (T ≪ N): direct application of (3.2)
-- ============================================================

theorem goal6 {R : ℕ} (a : Fin R → ℂ) (ξ : Fin R → ℝ)
    (N : ℝ) (hN : 0 < N)
    (hnorm : ∑ r, ‖a r‖ ^ 2 = 1)
    (hsep : IsSeparatedFamily (1 / N) ξ)
    (a₀ b₀ : ℝ) (hab : a₀ ≤ b₀) :
    ∃ C : ℝ, 0 < C ∧
    |∫ t : ℝ, expSumSq a ξ t * kernelE N a₀ b₀ t| ≤ C * N := by
  set T := b₀ - a₀
  obtain ⟨C₃, hC₃, hG3⟩ := goal3 a ξ N hN hnorm hsep a₀
  obtain ⟨C₅, hC₅, hG5⟩ := goal5 N hN a₀ b₀ hab
  -- Case 2: T ≤ N (I fits inside one interval J)
  by_cases hTN : T ≤ N
  · -- Direct application of Goal 3
    refine ⟨C₃ * C₅, by positivity, ?_⟩
    calc |∫ t : ℝ, expSumSq a ξ t * kernelE N a₀ b₀ t|
        ≤ ∫ t : ℝ, expSumSq a ξ t * |kernelE N a₀ b₀ t| := by
          apply (abs_integral_le_integral_abs _).trans
          apply integral_mono_ae
          · sorry; · sorry
          · apply ae_of_all; intro t
            exact mul_le_mul_of_nonneg_left (le_abs_self _)
              (by simp [expSumSq]; positivity)
      _ ≤ ∫ t in Set.Icc a₀ (a₀ + N), expSumSq a ξ t * C₅ := by
          -- |E| ≤ C₅ · 1 on [a₀, a₀+N] ⊇ I
          apply integral_mono_of_subset
          · intro t ht
            exact ⟨ht.1, le_trans ht.2 (by linarith)⟩
          · apply ae_of_all; intro t
            apply mul_le_mul_of_nonneg_left _ (by simp [expSumSq]; positivity)
            exact le_trans (hG5 t) (by
              apply mul_le_mul_of_nonneg_left _ hC₅.le
              simp [Real.rpow_neg_nonpos])
          · sorry
      _ = C₅ * ∫ t in Set.Icc a₀ (a₀ + N), expSumSq a ξ t := by
          rw [← integral_const_mul]; congr 1; ext t; ring
      _ ≤ C₅ * (C₃ * N) := mul_le_mul_of_nonneg_left (hG3 a₀) hC₅.le
      _ = C₃ * C₅ * N := by ring
  -- Case 1: T > N (dyadic decomposition)
  · push_neg at hTN
    -- L = ⌈log₂(T/N)⌉ layers
    set L := Nat.ceil (Real.log (T / N) / Real.log 2)
    refine ⟨C₃ * C₅ * 4 / (1 - (2:ℝ)^(-(9:ℝ))), by
      apply div_pos; positivity
      linarith [Real.rpow_lt_one (by norm_num) (by norm_num : (0:ℝ) < 2) (by norm_num)],
      ?_⟩
    -- The dyadic decomposition argument
    -- Layer ℓ: intervals J with dist(c(J),∂I) ∈ [2^ℓN, 2^{ℓ+1}N)
    -- # intervals in layer ℓ: ≤ 2^{ℓ+1}
    -- |E(t)| on layer ℓ: ≤ C₅ · (2^ℓ)^{-10}
    -- ∫_J F ≤ C₃ · N  (by Goal 3)
    -- Sum over layers: ∑_{ℓ=0}^{L} 2^{ℓ+1} · C₃N · C₅·(2^ℓ)^{-10}
    --                = 2C₃C₅N ∑_{ℓ=0}^{L} 2^{-9ℓ}
    --                ≤ 2C₃C₅N · 1/(1-2^{-9})
    calc |∫ t : ℝ, expSumSq a ξ t * kernelE N a₀ b₀ t|
        ≤ ∑ ℓ in Finset.range (L + 1),
            ∑ k in Finset.range (2^(ℓ+1)),
            |∫ t in Set.Icc (a₀ - (k+1) * N) (a₀ - k * N),
              expSumSq a ξ t * kernelE N a₀ b₀ t| +
          ∑ ℓ in Finset.range (L + 1),
            ∑ k in Finset.range (2^(ℓ+1)),
            |∫ t in Set.Icc (b₀ + k * N) (b₀ + (k+1) * N),
              expSumSq a ξ t * kernelE N a₀ b₀ t| := by
          sorry -- partition ℝ into layers
      _ ≤ ∑ ℓ in Finset.range (L + 1), (2^(ℓ+1) : ℝ) * (C₃ * N) *
            (C₅ * (2^ℓ)^(-(10:ℝ))) +
          ∑ ℓ in Finset.range (L + 1), (2^(ℓ+1) : ℝ) * (C₃ * N) *
            (C₅ * (2^ℓ)^(-(10:ℝ))) := by
          apply add_le_add
          all_goals {
            apply Finset.sum_le_sum; intro ℓ _
            apply Finset.sum_le_sum_of_subset; simp
          }
      _ = 2 * (C₃ * C₅ * N) * ∑ ℓ in Finset.range (L + 1), (2:ℝ)^(-(9:ℝ)*ℓ)  := by
  have hstep : ∀ ℓ : ℕ, (2^(ℓ+1) : ℝ) * (C₃ * N) * (C₅ * (2^ℓ)^(-(10:ℝ))) =
      2 * (C₃ * C₅ * N) * (2^(-(9:ℝ)))^ℓ := by
    intro ℓ
    have h1 : (2 : ℝ)^(ℓ+1) = 2 * 2^ℓ := by ring
    have h2 : ((2:ℝ)^ℓ)^(-(10:ℝ)) = ((2:ℝ)^(-(9:ℝ)))^ℓ / (2:ℝ)^ℓ := by
      rw [← Real.rpow_natCast 2 ℓ]
      rw [← Real.rpow_mul (by norm_num)]
      rw [← Real.rpow_natCast 2 ℓ]
      simp [Real.rpow_neg, mul_comm]
    rw [h1, h2]
    ring
  simp_rw [hstep]
  rw [← Finset.mul_sum]
      -- Geometric series: ∑_{ℓ=0}^{L} 2^{-9ℓ} ≤ 1/(1-2^{-9})
      _ ≤ 2 * (C₃ * C₅ * N) * (1 / (1 - (2:ℝ)^(-(9:ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ∑ ℓ in Finset.range (L + 1), (2:ℝ)^(-(9:ℝ)*ℓ)
              ≤ ∑' ℓ : ℕ, (2:ℝ)^(-(9:ℝ)*ℓ) := by
                apply sum_le_tsum (Finset.subset_univ _)
                · intro ℓ _; positivity
                · apply Summable.of_nonneg_of_le
                  · intro ℓ; positivity
                  · intro ℓ; exact le_refl _
                  · apply summable_geometric_of_abs_lt_one <;> norm_num
            _ = 1 / (1 - (2:ℝ)^(-(9:ℝ))) := by
                rw [tsum_geometric_of_abs_lt_one]
                · norm_num
                · norm_num
      _ = C₃ * C₅ * 4 / (1 - (2:ℝ)^(-(9:ℝ))) * N := by ring

-- ============================================================
-- GOAL 7: Lemma 3.1 (Assembly)
--
-- From handwritten proof:
--   ∫_I F = T - ∫_ℝ F·E      (by Goal 4)
--              ↑               ↑
--         = T + O(N)·1   (by Goal 6: |∫ F·E| ≪ N)
--              = (T + O(N)) · ∑|aᵣ|²  (by Goal 1: WLOG)
-- ============================================================

theorem lemma3_1 {R : ℕ} (a : Fin R → ℂ) (ξ : Fin R → ℝ)
    (N : ℝ) (hN : 0 < N) (hsep : IsSeparatedFamily (1 / N) ξ)
    (a₀ b₀ : ℝ) (T : ℝ) (hT : T = b₀ - a₀) (hab : a₀ ≤ b₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ θ : ℝ, |θ| ≤ C ∧
    ∫ t in Set.Icc a₀ b₀, ‖∑ r, a r * e (ξ r * t)‖ ^ 2 =
    (T + θ * N) * ∑ r, ‖a r‖ ^ 2 := by
  set M := ∑ r, ‖a r‖ ^ 2
  -- Trivial case: M = 0 → all aᵣ = 0
  by_cases hM0 : M = 0
  · refine ⟨1, one_pos, 0, by simp, ?_⟩
    have hzero : ∀ r, a r = 0 := by
      intro r
      have h1 : 0 ≤ ‖a r‖ ^ 2 := sq_nonneg _
      have h2 : ‖a r‖ ^ 2 ≤ M :=
        Finset.single_le_sum (fun i _ => sq_nonneg _) _ (Finset.mem_univ r)
      have h3 : ‖a r‖ = 0 := by
        nlinarith [hM0 ▸ h2]
      exact norm_eq_zero.mp h3
    simp [hM0, hzero]
  · -- M > 0: normalize Aᵣ = aᵣ/√M
    have hMpos : 0 < M :=
      lt_of_le_of_ne (Finset.sum_nonneg fun r _ => sq_nonneg _) (Ne.symm hM0)
    -- GOAL 1: define A with ∑|Aᵣ|² = 1
    set A : Fin R → ℂ := fun r => a r / (Real.sqrt M : ℂ)
    have hAnorm : ∑ r, ‖A r‖ ^ 2 = 1 := goal1 a M rfl hMpos
    -- Rescaling: ‖expSum a‖² = M · ‖expSum A‖²
    have hrescale : ∀ t,
        ‖∑ r, a r * e (ξ r * t)‖ ^ 2 =
        M * ‖∑ r, A r * e (ξ r * t)‖ ^ 2 := by
      intro t
      have : ∑ r, a r * e (ξ r * t) =
          (Real.sqrt M : ℂ) * ∑ r, A r * e (ξ r * t) := by
        simp [A, Finset.mul_sum, div_mul_cancel₀]
        intro r
        field_simp
        rw [div_mul_cancel₀]
        exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hMpos)
      rw [this, norm_mul, Complex.norm_ofReal,
          abs_of_nonneg (Real.sqrt_nonneg M), mul_pow, Real.sq_sqrt hMpos.le]
    -- Apply Goal 4 to get the Fubini identity
    have h4 := goal4 A ξ N hN hAnorm hsep a₀ b₀ T hT hab
    -- Apply Goal 6 to bound the error
    obtain ⟨C, hC, h6⟩ := goal6 A ξ N hN hAnorm hsep a₀ b₀ hab
    -- ∫_I ‖expSum A‖² = T - err,  |err| ≤ C·N
    set err := ∫ t : ℝ, expSumSq A ξ t * kernelE N a₀ b₀ t
    have hA_eq : ∫ t in Set.Icc a₀ b₀, expSumSq A ξ t = T - err := by
      simp [expSumSq] at h4 ⊢; exact h4
    have herr_bd : |err| ≤ C * N := by
      simp [expSumSq] at h6; exact h6
    -- ∫_I ‖expSum a‖² = M · (T - err) = (T + θN) · M with θ = -err/N
    refine ⟨C, hC, -err / N, ?_, ?_⟩
    · -- |θ| = |err|/N ≤ C·N/N = C
      rw [abs_div, abs_neg, abs_of_pos hN]
      exact div_le_of_le_mul₀ hN.le (by positivity) (by linarith)
    · -- ∫_I ‖expSum a‖² = (T + θN) · M
      have ha_int : ∫ t in Set.Icc a₀ b₀, ‖∑ r, a r * e (ξ r * t)‖ ^ 2 =
          M * (T - err) := by
        conv_lhs => ext t; rw [hrescale t]
        rw [integral_const_mul]
        simp [expSumSq] at hA_eq
        rw [hA_eq]
      rw [ha_int]
      field_simp; ring

end
