module

public import Expdb.ExponentialSums.UpperSemicontinuity
public import Expdb.ExponentialSums.Differencing

import Mathlib.Topology.Sequences
import Mathlib.Data.Nat.Log

/-!
# The van der Corput A-process for growth exponents

The blueprint proof selects a logarithmic range of shifts, normalizes its difference
phase, and applies the defining bound for β. Below the cutoff `N²/T`, the existing
formula `β(x) = x - 1` for `x > 1` supplies the small-shift cancellation estimate.
-/

@[expose] public section

open Filter Topology
open scoped Expdb NNReal

noncomputable section

namespace Expdb

/-- Dyadic pigeonholing costs only the number of logarithmic ranges. Each range
contains at most its lower endpoint's number of shifts. -/
private lemma exists_shift_dyadic_bound (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j)
    {H : ℕ} (hH : 1 ≤ H) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ H ∧
      (∑ k ∈ Finset.Ico 1 H, C k) ≤ (Nat.log 2 H + 1 : ℕ) * ((j : ℝ) * C j) := by
  classical
  by_cases hH1 : H = 1
  · refine ⟨1, le_rfl, by omega, ?_⟩
    simp only [hH1, Finset.Ico_self, Finset.sum_empty]
    exact mul_nonneg (Nat.cast_nonneg _) (by simpa using hC 1)
  let J := Finset.Ico 1 H
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image J (fun k ↦ (k : ℝ) * C k)
    ⟨1, by simp [J]; omega⟩
  let M : ℝ := (j : ℝ) * C j
  have hM : 0 ≤ M := mul_nonneg (Nat.cast_nonneg _) (hC j)
  have hbin : ∀ k : ℕ, (∑ n ∈ J with Nat.log 2 n = k, C n) ≤ M := by
    intro k
    let B := J.filter (fun n ↦ Nat.log 2 n = k)
    have hB : B ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := by
      intro n hn
      obtain ⟨hnJ, hnlog⟩ := Finset.mem_filter.1 hn
      have hnpos : n ≠ 0 := by have := (Finset.mem_Ico.1 hnJ).1; omega
      rw [Finset.mem_Ico]
      constructor
      · simpa [hnlog] using Nat.pow_log_le_self 2 hnpos
      · simpa [hnlog] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
    have hcard : (B.card : ℝ) ≤ (2 : ℝ) ^ k := by
      have hc := Finset.card_le_card hB
      rw [Nat.card_Ico, pow_succ] at hc
      have hc' : B.card ≤ 2 ^ k := by omega
      exact_mod_cast hc'
    have hpow : (0 : ℝ) < 2 ^ k := by positivity
    have hentry : ∀ n ∈ B, C n ≤ M / (2 : ℝ) ^ k := by
      intro n hn
      have hnJ := (Finset.mem_filter.1 hn).1
      have hlower : (2 : ℝ) ^ k ≤ n := by exact_mod_cast (Finset.mem_Ico.1 (hB hn)).1
      apply (le_div_iff₀ hpow).2
      calc
        C n * 2 ^ k ≤ (n : ℝ) * C n := by nlinarith [hC n]
        _ ≤ M := hmax n hnJ
    calc
      _ ≤ ∑ _n ∈ B, M / (2 : ℝ) ^ k := Finset.sum_le_sum hentry
      _ = (B.card : ℝ) * (M / (2 : ℝ) ^ k) := by simp
      _ ≤ (2 : ℝ) ^ k * (M / (2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_right hcard (div_nonneg hM hpow.le)
      _ = M := by field_simp
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := J) (t := Finset.range (Nat.log 2 H + 1)) (g := Nat.log 2)
    (fun n hn ↦ Finset.mem_range.2 (by
      exact Nat.lt_succ_of_le (Nat.log_mono_right (Finset.mem_Ico.1 hn).2.le))) C
  refine ⟨j, (Finset.mem_Ico.1 hj).1, (Finset.mem_Ico.1 hj).2.le, ?_⟩
  calc
    _ = ∑ k ∈ Finset.range (Nat.log 2 H + 1), ∑ n ∈ J with Nat.log 2 n = k, C n :=
      hfiber.symm
    _ ≤ ∑ _k ∈ Finset.range (Nat.log 2 H + 1), M :=
      Finset.sum_le_sum fun k _ ↦ hbin k
    _ = _ := by simp [M]

private lemma isPowerBounded_dyadic_range_count {H : VariableObject ℕ}
    {T : VariableObject ℝ} {h : ℝ} (hh : 0 ≤ h)
    (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hHT : IsPowerAsymptotic (fun i ↦ (H i : ℝ)) T h) :
    IsPowerBounded (fun i ↦ ((Nat.log 2 (H i) + 1 : ℕ) : ℝ)) T 0 := by
  apply (isPowerBounded_iff_forall_pos _ T 0 hT hTunbounded).2
  intro ε hε
  let η : ℝ := ε / (h + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper := hHT.eventually_between (Filter.Eventually.of_forall hT) zero_lt_one
  refine Asymptotics.IsBigO.of_bound (1 / (η * Real.log 2) + 1) ?_
  filter_upwards [hupper] with i hi
  have hpow : (H i : ℝ) ^ η ≤ T i ^ ε := by
    calc
      _ ≤ (T i ^ (h + 1)) ^ η :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hi.2 hη.le
      _ = T i ^ ε := by
        rw [← Real.rpow_mul (zero_le_one.trans (hT i))]
        congr 1
        dsimp [η]
        field_simp
  have hlog : Real.log (H i) ≤ T i ^ ε / η :=
    (Real.log_natCast_le_rpow_div (H i) hη).trans
      (div_le_div_of_nonneg_right hpow hη.le)
  have hnatlog : (Nat.log 2 (H i) : ℝ) ≤ Real.log (H i) / Real.log 2 := by
    simpa [Real.logb] using Real.natLog_le_logb (H i) 2
  have hnatbound := hnatlog.trans (div_le_div_of_nonneg_right hlog hlog2.le)
  have hone : 1 ≤ T i ^ ε := Real.one_le_rpow (hT i) hε.le
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg
    (Real.rpow_nonneg (zero_le_one.trans (hT i)) _), zero_add, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ T i ^ ε / η / Real.log 2 + T i ^ ε := add_le_add hnatbound hone
    _ = _ := by ring

private lemma correlation_isPowerBounded
    {α h' σ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hh' : 0 ≤ h') (hh'α : h' < α)
    (hσ : 0 < σ) {N T : VariableObject ℝ}
    {F : VariableFunction (VariableObject.fixed ℝ) ℝ} {a b j : VariableObject ℕ}
    (hN : ∀ i, 1 ≤ N i) (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α)
    (hjT : IsPowerAsymptotic (fun i ↦ (j i : ℝ)) T h') (hj : ∀ i, 0 < j i)
    (hF : IsModelPhaseFunctionWith F σ)
    (hab : ∀ i, N i ≤ (a i : ℝ) ∧ (b i : ℝ) ≤ 2 * N i ∧ a i ≤ b i) :
    IsPowerBounded (fun i ↦ correlationSumAt (F i) (T i) (N i) (a i) (b i) (j i)) T
      ((1 + h' - α) * exponentSumGrowthExponent (α / (1 + h' - α)).toNNReal) := by
  let J : VariableObject ℝ := fun i ↦ (j i : ℝ)
  let κ : ℝ := 1 + h' - α
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hNpos : ∀ i, 0 < N i := fun i ↦ zero_lt_one.trans_le (hN i)
  have hJpos : ∀ i, 0 < J i := fun i ↦ by dsimp [J]; exact_mod_cast hj i
  have hTtop := (VariableObject.isUnbounded_iff_tendsto_atTop
    (fun i ↦ zero_le_one.trans (hT i))).1 hTunbounded
  have hNtop := hNT.tendsto_atTop_of_pos hα hT hTunbounded
  have hratio : Tendsto (J / N) atTop (𝓝 0) :=
    (hjT.div hNT hT).tendsto_zero_of_neg (by linarith) hT hTunbounded
  let r : VariableObject ℝ := fun i ↦ min (J i / N i) (1 / 2)
  have hr : ∀ i, 0 < r i := fun i ↦ lt_min (div_pos (hJpos i) (hNpos i)) (by norm_num)
  have hr1 : ∀ i, r i < 1 := fun i ↦ (min_le_right _ _).trans_lt (by norm_num)
  have hrzero : Tendsto r atTop (𝓝 0) := by
    simpa [r] using hratio.min (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)))
  have hsmall : ∀ᶠ i in atTop, J i / N i < 1 / 2 :=
    hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  let G : VariableFunction (VariableObject.fixed ℝ) ℝ :=
    fun i ↦ differencePhase (F i) σ (r i)
  have hG : IsModelPhaseFunctionWith G (σ + 1) := hF.differencePhase hσ hr hr1 hrzero
  let M : VariableObject ℝ := N - J
  have hMN : Tendsto (M / N) atTop (𝓝 1) := by
    have heq : M / N = fun i ↦ 1 - J i / N i := by
      ext i
      dsimp [M]
      field_simp [(hNpos i).ne']
    rw [heq]
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
      atTop (𝓝 1)).sub hratio
  have hMT : IsPowerAsymptotic M T α := by
    have hprod := (isPowerAsymptotic_zero_of_tendsto_one hMN hT hTunbounded).mul hNT hT
    convert hprod using 1
    · ext i
      dsimp
      field_simp [(hNpos i).ne']
    · simp
  let S : VariableObject ℝ := fun i ↦ σ * T i * J i / N i
  have hσT : IsPowerAsymptotic (fun _ : ℕ ↦ σ) T 0 :=
    isPowerAsymptotic_zero_of_tendsto_pos hσ tendsto_const_nhds hT hTunbounded
  have hST : IsPowerAsymptotic S T κ := by
    change IsPowerAsymptotic (((fun _ : ℕ ↦ σ) * T * (fun i ↦ (j i : ℝ))) / N) T κ
    simpa [κ] using
      ((hσT.mul (isPowerAsymptotic_self T) hT).mul hjT hT).div hNT hT
  have hStop : Tendsto S atTop atTop := hST.tendsto_atTop_of_pos hκ hT hTunbounded
  have hMS : IsPowerAsymptotic M S (α / κ) := hMT.change_base hST hκ hT
  have hακ : 0 ≤ α / κ := (div_pos hα hκ).le
  have hsetup : ∀ᶠ i in atTop, 1 ≤ M i ∧ 1 ≤ S i ∧
      M i ≤ ((a i - j i : ℕ) : ℝ) ∧ ((b i - 2 * j i : ℕ) : ℝ) ≤ 2 * M i := by
    filter_upwards [hsmall, hNtop.eventually (eventually_ge_atTop 2),
      hStop.eventually (eventually_ge_atTop 1)] with i hi hiN hiS
    have hjN : 2 * J i < N i := by
      have := (div_lt_iff₀ (hNpos i)).1 hi
      linarith
    have hja : j i ≤ a i := by
      have : J i ≤ (a i : ℝ) := by linarith [hJpos i, (hab i).1]
      dsimp [J] at this
      exact_mod_cast this
    have hjb : 2 * j i ≤ b i := by
      have : 2 * J i ≤ (b i : ℝ) := hjN.le.trans
        ((hab i).1.trans (by exact_mod_cast (hab i).2.2))
      dsimp [J] at this
      exact_mod_cast this
    dsimp [M]
    rw [Nat.cast_sub hja, Nat.cast_sub hjb, Nat.cast_mul, Nat.cast_ofNat]
    exact ⟨by linarith, hiS, by linarith [(hab i).1], by linarith [(hab i).2.1]⟩
  have hbound := IsExponentSumBound.isPowerBounded_of_eventually_setup
    (isExponentSumBound_exponentSumGrowthExponent (α / κ).toNNReal)
    (by linarith : 0 < σ + 1) hStop
    (by simpa [Real.coe_toNNReal _ hακ] using hMS) hG hsetup
  have hbase := hbound.change_base hST hT
  obtain ⟨e, he, hO⟩ := hbase
  obtain ⟨C, hCpos, hC⟩ := hO.exists_pos
  refine ⟨e, he, Asymptotics.IsBigO.of_bound C ?_⟩
  filter_upwards [hC.bound, hsmall, hsetup] with i hiO hiSmall hiSetup
  have hja : j i ≤ a i := by
    have : (j i : ℝ) ≤ (a i : ℝ) := by
      have := (div_lt_iff₀ (hNpos i)).1 hiSmall
      dsimp [J] at this
      linarith [(hab i).1, hN i]
    exact_mod_cast this
  have hjb : 2 * j i ≤ b i := by
    have hjN : 2 * J i < N i := by
      have := (div_lt_iff₀ (hNpos i)).1 hiSmall
      linarith
    have : (2 : ℝ) * (j i : ℝ) ≤ (b i : ℝ) := hjN.le.trans
      ((hab i).1.trans (by exact_mod_cast (hab i).2.2))
    exact_mod_cast this
  have heq := norm_correlationSumAt_eq_differencePhase (F i) (T := T i) hσ.ne' (hNpos i).ne'
    (hj i).ne' (by dsimp [M] at hiSetup; linarith [hiSetup.1] : N i - (j i : ℝ) ≠ 0)
    hja hjb
  rw [heq]
  have hrEq : r i = J i / N i := min_eq_left hiSmall.le
  simpa [exponentialSum_apply, G, hrEq, S, M, J] using hiO

private lemma weighted_correlation_isPowerBounded
    {α h σ γ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hh : 0 < h) (hhα : h < α)
    (hσ : 0 < σ) {N T : VariableObject ℝ}
    {F : VariableFunction (VariableObject.fixed ℝ) ℝ} {a b j H : VariableObject ℕ}
    (hN : ∀ i, 1 ≤ N i) (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α)
    (hHT : IsPowerAsymptotic (fun i ↦ (H i : ℝ)) T h)
    (hj : ∀ i, 0 < j i) (hjH : ∀ i, j i ≤ H i)
    (hF : IsModelPhaseFunctionWith F σ)
    (hab : ∀ i, N i ≤ (a i : ℝ) ∧ (b i : ℝ) ≤ 2 * N i ∧ a i ≤ b i)
    (hγ : ∀ h' ∈ Set.Icc 0 h,
      h' + (1 + h' - α) * exponentSumGrowthExponent (α / (1 + h' - α)).toNNReal ≤ γ) :
    IsPowerBounded (fun i ↦ (j i : ℝ) *
      ‖correlationSumAt (F i) (T i) (N i) (a i) (b i) (j i)‖) T γ := by
  apply isPowerBounded_of_subsequences hT hTunbounded
  intro φ hφ
  have hTφ : ∀ i, 1 ≤ T (φ i) := fun i ↦ hT _
  have hTtop := (VariableObject.isUnbounded_iff_tendsto_atTop
    (fun i ↦ zero_le_one.trans (hT i))).1 hTunbounded
  have hTgt : ∀ᶠ i in atTop, 1 < T (φ i) :=
    (hTtop.comp hφ.tendsto_atTop).eventually (eventually_gt_atTop 1)
  have hlogH := (hHT.comp_tendsto hφ.tendsto_atTop).tendsto_logb hTgt
  let e : ℕ → ℝ := fun i ↦ Real.logb (T (φ i)) (j (φ i))
  have hcompact : ∀ᶠ i in atTop, e i ∈ Set.Icc 0 (h + 1) := by
    filter_upwards [hTgt, hlogH.eventually (gt_mem_nhds (by linarith : h < h + 1))]
      with i hiT hiH
    have hjpos : (0 : ℝ) < j (φ i) := by exact_mod_cast hj _
    have hlogle : e i ≤ Real.logb (T (φ i)) (H (φ i)) :=
      Real.logb_le_logb_of_le hiT hjpos (by exact_mod_cast hjH _)
    refine ⟨?_, hlogle.trans hiH.le⟩
    exact Real.logb_nonneg hiT (by exact_mod_cast hj _)
  obtain ⟨h', hh'mem, ψ, hψ, he⟩ := isCompact_Icc.tendsto_subseq' hcompact.frequently
  have hTgt' := hψ.tendsto_atTop.eventually hTgt
  have hh'h : h' ≤ h := by
    apply le_of_tendsto_of_tendsto he (hlogH.comp hψ.tendsto_atTop)
    filter_upwards [hTgt'] with i hi
    change Real.logb (T (φ (ψ i))) (j (φ (ψ i))) ≤
      Real.logb (T (φ (ψ i))) (H (φ (ψ i)))
    exact Real.logb_le_logb_of_le hi (by exact_mod_cast hj (φ (ψ i)))
      (by exact_mod_cast hjH (φ (ψ i)))
  have hjpower : IsPowerAsymptotic (fun i ↦ (j (φ (ψ i)) : ℝ))
      (fun i ↦ T (φ (ψ i))) h' :=
    isPowerAsymptotic_of_logb_tendsto hTgt'
      (Filter.Eventually.of_forall fun i ↦ by exact_mod_cast hj (φ (ψ i))) he
  have hT' : ∀ i, 1 ≤ T (φ (ψ i)) := fun i ↦ hT _
  have hT'unbounded : VariableObject.IsUnbounded (fun i ↦ T (φ (ψ i))) :=
    (VariableObject.isUnbounded_iff_tendsto_atTop
      (fun i ↦ zero_le_one.trans (hT' i))).2
      ((hTtop.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop)
  have hcorrelation := correlation_isPowerBounded hα hα1 hh'mem.1
    (hh'h.trans_lt hhα) hσ (fun i ↦ hN _) hT' hT'unbounded
    ((hNT.comp_tendsto hφ.tendsto_atTop).comp_tendsto hψ.tendsto_atTop)
    hjpower (fun i ↦ hj _) ((hF.comp_tendsto hφ.tendsto_atTop).comp_tendsto hψ.tendsto_atTop)
    (fun i ↦ hab _)
  refine ⟨ψ, hψ, ?_⟩
  exact (hjpower.isPowerBounded.mul hcorrelation.norm hT').mono
    (Filter.Eventually.of_forall hT') (hγ h' ⟨hh'mem.1, hh'h⟩)

private lemma exponentialSum_A_bound
    {α h B σ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hh : 0 < h) (hhα : h < α)
    (hσ : 0 < σ) (hdiag : 2 * α - h ≤ 2 * B)
    (hcorr : ∀ h' ∈ Set.Icc (2 * α - 1) h,
      (1 + h' - α) * exponentSumGrowthExponent (α / (1 + h' - α)).toNNReal + h' ≤
        2 * B - α + h)
    {N T : VariableObject ℝ} {F : VariableFunction (VariableObject.fixed ℝ) ℝ}
    {a b : VariableObject ℕ}
    (hN : ∀ i, 1 ≤ N i) (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T α) (hF : IsModelPhaseFunctionWith F σ)
    (hab : ∀ i, N i ≤ (a i : ℝ) ∧ (b i : ℝ) ≤ 2 * N i ∧ a i ≤ b i) :
    IsPowerBounded (exponentialSum F T N a b) T B := by
  let H := floorRpow T h
  have hHpos : ∀ i, 0 < H i := floorRpow_pos T h
  have hHT := isPowerAsymptotic_floorRpow hh hT hTunbounded
  have hHNzero := (hHT.div hNT hT).tendsto_zero_of_neg (by linarith) hT hTunbounded
  have hHN : ∀ᶠ i in atTop, (H i : ℝ) ≤ N i := by
    have hsmall := hHNzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hsmall] with i hi
    exact ((div_lt_one (zero_lt_one.trans_le (hN i))).1 hi).le
  have hselect := fun i ↦ exists_shift_dyadic_bound
    (fun j ↦ ‖correlationSumAt (F i) (T i) (N i) (a i) (b i) j‖)
    (fun j ↦ norm_nonneg _) (Nat.one_le_iff_ne_zero.2 (hHpos i).ne')
  choose j hj hjH hdyadic using hselect
  let γ : ℝ := 2 * B - α + h
  have hγ : α ≤ γ := by dsimp [γ]; linarith
  have hγbound : ∀ h' ∈ Set.Icc 0 h,
      h' + (1 + h' - α) * exponentSumGrowthExponent (α / (1 + h' - α)).toNNReal ≤ γ := by
    intro h' hh'
    by_cases hlarge : 2 * α - 1 ≤ h'
    · simpa [γ, add_comm] using hcorr h' ⟨hlarge, hh'.2⟩
    · have hκ : 0 < 1 + h' - α := by linarith [hh'.1]
      have hxpos : 0 ≤ α / (1 + h' - α) := (div_pos hα hκ).le
      have hxgt : (1 : ℝ≥0) < (α / (1 + h' - α)).toNNReal := by
        change (1 : ℝ) < ((α / (1 + h' - α)).toNNReal : ℝ)
        rw [Real.coe_toNNReal _ hxpos]
        apply (lt_div_iff₀ hκ).2
        linarith
      rw [exponentSumGrowthExponent_eq_sub_one hxgt, Real.coe_toNNReal _ hxpos]
      have heq : h' + (1 + h' - α) * (α / (1 + h' - α) - 1) = 2 * α - 1 := by
        field_simp
        ring
      rw [heq]
      linarith
  let W : VariableObject ℝ := fun i ↦ (j i : ℝ) *
    ‖correlationSumAt (F i) (T i) (N i) (a i) (b i) (j i)‖
  have hW : IsPowerBounded W T γ := weighted_correlation_isPowerBounded hα hα1 hh hhα hσ
    hN hT hTunbounded hNT hHT (fun i ↦ lt_of_lt_of_le Nat.zero_lt_one (hj i)) hjH hF hab hγbound
  let K : VariableObject ℝ := fun i ↦ ((Nat.log 2 (H i) + 1 : ℕ) : ℝ)
  have hK : IsPowerBounded K T 0 := isPowerBounded_dyadic_range_count hh.le hT hTunbounded hHT
  have hKW : IsPowerBounded (K * W) T γ := by simpa using hK.mul hW hT
  have hsum : IsPowerBounded (N + K * W) T γ := by
    simpa [max_eq_right hγ] using hNT.isPowerBounded.add hKW hT
  have hratio : IsPowerAsymptotic (N / fun i ↦ (H i : ℝ)) T (α - h) := hNT.div hHT hT
  have hout := hratio.isPowerBounded.mul hsum hT
  have hconst : IsPowerBounded (fun _ : ℕ ↦ (6 : ℝ)) T 0 :=
    (isPowerAsymptotic_zero_of_tendsto_pos (by norm_num : (0 : ℝ) < 6)
      tendsto_const_nhds hT hTunbounded).isPowerBounded
  let Y : VariableObject ℝ := fun i ↦ 6 * N i / H i * (N i + K i * W i)
  have hY : IsPowerBounded Y T (2 * B) := by
    convert hconst.mul hout hT using 1
    · ext i
      dsimp [Y]
      ring
    · dsimp [γ]
      ring
  have hsq : IsPowerBounded (fun i ↦ ‖exponentialSum F T N a b i‖ ^ 2) T (2 * B) := by
    apply hY.of_norm_le
    filter_upwards [hHN] with i hi
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ 6 * N i / H i * (N i +
          ∑ k ∈ Finset.Ico 1 (H i), ‖correlationSumAt (F i) (T i) (N i) (a i) (b i) k‖) :=
        norm_exponentialSumAt_sq_le_correlations (F i) (T i) (hN i) (hab i).1
          (hab i).2.1 (hj i |>.trans (hjH i)) hi
      _ ≤ Y i := by
        dsimp [Y, K, W]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (hdyadic i))
          (div_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans (hN i)))
            (Nat.cast_nonneg _))
  exact hsq.of_norm_sq hT hTunbounded

/-- A strengthened growth-bound form of the blueprint A-process, valid for `0 < α < 1`.
The finite differencing estimate has no `H²` error, so the `2h` term in the blueprint
inequality is unnecessary here. The supremum formulation follows by bounding each
correlation exponent by the chosen upper bound. -/
theorem isExponentSumBound_of_vanDerCorputA {α : ℝ≥0} {h B : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hh : 0 < h) (hhα : h < (α : ℝ))
    (hdiag : 2 * (α : ℝ) - h ≤ 2 * B)
    (hcorr : ∀ h' ∈ Set.Icc (2 * (α : ℝ) - 1) h,
      (1 + h' - α) * exponentSumGrowthExponent ((α : ℝ) / (1 + h' - α)).toNNReal + h' ≤
        2 * B - α + h) : IsExponentSumBound α B := by
  intro N T F a b hN hT hTunbounded hNT hF hab
  obtain ⟨σ, hσ, hFσ⟩ := hF.exists_with
  let a' : VariableObject ℕ := fun i ↦ if a i ≤ b i then a i else ⌈N i⌉₊
  let b' : VariableObject ℕ := fun i ↦ if a i ≤ b i then b i else ⌈N i⌉₊
  have hab' : ∀ i, N i ≤ (a' i : ℝ) ∧ (b' i : ℝ) ≤ 2 * N i ∧ a' i ≤ b' i := by
    intro i
    dsimp [a', b']
    split_ifs with hi
    · exact ⟨(hab i).1, (hab i).2, hi⟩
    · refine ⟨Nat.le_ceil _, ?_, le_rfl⟩
      exact (Nat.ceil_lt_add_one (zero_le_one.trans (hN i))).le.trans (by linarith [hN i])
  have hbound := exponentialSum_A_bound (by exact_mod_cast hα) (by exact_mod_cast hα1)
    hh hhα hσ hdiag hcorr hN hT hTunbounded hNT hFσ hab'
  obtain ⟨e, he, hO⟩ := hbound
  refine ⟨e, he, (Asymptotics.IsBigO.of_bound 1 ?_).trans hO⟩
  filter_upwards [] with i
  by_cases hi : a i ≤ b i
  · simp [exponentialSum, a', b', hi]
  · simp [exponentialSum, a', b', hi, exponentialSumAt_of_lt (by omega : b i < a i)]

end Expdb
