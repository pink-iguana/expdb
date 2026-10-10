module

public import Expdb.ExponentialSums.ExponentSumGrowth
import Expdb.Fourier.Completion

/-!
# Full-interval bounds via finite Fourier completion

Below scale one, completing an interval only adds an infinitesimal linear term to the
model phase. Selecting a maximizing Fourier twist supplies the needed uniformity directly
from the variable-phase definition, with no smoothing or Fourier-integral tail estimates.
-/

@[expose] public section
open Filter Topology
open scoped Expdb FourierTransform NNReal
noncomputable section
namespace Expdb

private lemma completion_factor_bound {α : ℝ≥0} {N T : VariableObject ℝ}
    (hN : ∀ i, 1 ≤ N i) (hT : ∀ i, 1 ≤ T i) (hTunbounded : T.IsUnbounded)
    (hNT : IsPowerAsymptotic N T (α : ℝ)) :
    IsPowerBounded (fun i ↦ 3 + 2 * Real.log (⌊2 * N i⌋₊ + 1 : ℕ)) T 0 := by
  apply (isPowerBounded_iff_forall_pos _ T 0 hT hTunbounded).2
  intro ε hε
  let A : ℝ := 3 + 2 * Real.log 3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C : ℝ := A + 2 * ((α : ℝ) + 1) / ε
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hNT.eventually_between (Eventually.of_forall hT)
    (by norm_num : (0 : ℝ) < 1)] with i hi
  have hqpos : (0 : ℝ) < (⌊2 * N i⌋₊ + 1 : ℕ) := by positivity
  have hqone : (1 : ℝ) ≤ (⌊2 * N i⌋₊ + 1 : ℕ) := by exact_mod_cast (Nat.le_add_left 1 _)
  have hq : ((⌊2 * N i⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * N i := by
    have hf := Nat.floor_le (by linarith [hN i] : 0 ≤ 2 * N i)
    push_cast
    linarith [hN i]
  have hscale : 3 * N i ≤ 3 * T i ^ ((α : ℝ) + 1) := by linarith [hi.2]
  have hlog : Real.log (⌊2 * N i⌋₊ + 1 : ℕ) ≤
      Real.log 3 + ((α : ℝ) + 1) * Real.log (T i) := by
    have htpos : 0 < T i := zero_lt_one.trans_le (hT i)
    have h := Real.log_le_log hqpos (hq.trans hscale)
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos htpos _).ne', Real.log_rpow htpos] at h
    exact h
  have hpow : 1 ≤ T i ^ ε := Real.one_le_rpow (hT i) hε.le
  have hlogpow := Real.log_le_rpow_div (zero_le_one.trans (hT i)) hε
  have hL : 0 ≤ 3 + 2 * Real.log (⌊2 * N i⌋₊ + 1 : ℕ) := by
    positivity
  simp only [Real.norm_eq_abs, zero_add, abs_of_nonneg hL,
    abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans (hT i)) ε)]
  have hm := mul_le_mul_of_nonneg_left hlogpow (by positivity : 0 ≤ 2 * ((α : ℝ) + 1))
  have hApow := mul_le_mul_of_nonneg_left hpow hA
  dsimp [C, A] at hApow ⊢
  ring_nf at hm hApow hlog ⊢
  nlinarith

/-- Below scale one, finite Fourier completion turns full-interval bounds into
arbitrary-interval bounds. This also includes scale zero. -/
theorem IsFullIntervalExponentSumBound.of_lt_one {α : ℝ≥0} {β : ℝ}
    (hbound : IsFullIntervalExponentSumBound α β) (hα : α < 1) :
    IsExponentSumBound α β := by
  intro N T F a b hN hT hTunbounded hNT hF hab
  let q (i : ℕ) : ℕ := ⌊2 * N i⌋₊ + 1
  have hq (i : ℕ) : 0 < q i := by dsimp [q]; omega
  have hcomplete (i : ℕ) := exists_norm_sum_Icc_le_log_mul_twist (hq i)
    (Nat.ceil_le.mpr (hab i).1) (Nat.le_floor (hab i).2)
    (by dsimp [q]; omega : ⌊2 * N i⌋₊ < q i)
    (fun n ↦ (𝐞 (T i * F i ((n : ℝ) / N i)) : ℂ))
  let r : VariableObject ℝ := fun i ↦ (hcomplete i).choose
  have hr (i : ℕ) : 0 ≤ r i ∧ r i ≤ 1 :=
    ⟨(hcomplete i).choose_spec.1, (hcomplete i).choose_spec.2.1⟩
  let c : VariableObject ℝ := fun i ↦ -(r i * (N i / T i))
  have hratio := (hNT.div (isPowerAsymptotic_self T) hT).tendsto_zero_of_neg
    (by
      have : (α : ℝ) < 1 := by exact_mod_cast hα
      linarith) hT hTunbounded
  have hc : c.IsInfinitesimal := by
    apply squeeze_zero' (g := fun i ↦ N i / T i)
    · exact Eventually.of_forall fun i ↦ norm_nonneg _
    · apply Eventually.of_forall
      intro i
      have hratio0 : 0 ≤ N i / T i :=
        div_nonneg (zero_le_one.trans (hN i)) (zero_le_one.trans (hT i))
      simp only [c, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hr i).1,
        abs_of_nonneg hratio0]
      exact mul_le_of_le_one_left hratio0 (hr i).2
    · exact hratio
  obtain ⟨σ, hσ, hFσ⟩ := hF.exists_with
  let G : VariableFunction (VariableObject.fixed ℝ) ℝ := fun i u ↦ F i u + c i * u
  have hG : IsModelPhaseFunction G := (hFσ.add_infinitesimal_linear hc).isModelPhaseFunction hσ
  have hfull := hbound N T G hN hT hTunbounded hNT hG
  have hfactor := completion_factor_bound hN hT hTunbounded hNT
  have hproduct := hfactor.mul hfull.norm hT
  apply IsPowerBounded.of_norm_le (by simpa using hproduct)
  apply Eventually.of_forall
  intro i
  have he : ∑ n ∈ Finset.Icc ⌈N i⌉₊ ⌊2 * N i⌋₊,
      (𝐞 (T i * F i ((n : ℝ) / N i)) : ℂ) * (𝐞 (-(r i * n)) : ℂ) =
      exponentialSum G T N (fun i ↦ ⌈N i⌉₊) (fun i ↦ ⌊2 * N i⌋₊) i := by
    simp only [exponentialSum, exponentialSumAt, oscillatory, G, c]
    apply Finset.sum_congr rfl
    intro n _
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 2
    have hNne : N i ≠ 0 := (zero_lt_one.trans_le (hN i)).ne'
    have hTne : T i ≠ 0 := (zero_lt_one.trans_le (hT i)).ne'
    field_simp [hNne, hTne]
  have hi := (hcomplete i).choose_spec.2.2
  rw [he] at hi
  simpa [exponentialSum, exponentialSumAt, oscillatory, q] using hi

end Expdb
