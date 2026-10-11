module

public import Expdb.ExponentialSums.PhaseFunctions
public import Expdb.Mathlib.SmoothExtension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp

/-!
# Controlled extension of phase errors

The B-process needs phases on a larger interval than `[1, 2]`. This bridge uses
Borel jet realization and gluing to extend a smooth error exactly, with a bound
for any prescribed finite number of derivatives. The constant is independent
of the error function and of its uncontrolled higher derivatives.
-/

@[expose] public section

namespace Expdb

open Set
open scoped ContDiff Topology
noncomputable section

private lemma iteratedDerivWithin_eq_of_restriction
    {f g : ℝ → ℝ} {s t : Set ℝ} (hst : s ⊆ t)
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hg : ContDiffOn ℝ ∞ g t) (heq : EqOn g f s) {x : ℝ} (hx : x ∈ s) (k : ℕ) :
    iteratedDerivWithin k g t x = iteratedDerivWithin k f s x := by
  have hsub := iteratedFDerivWithin_subset hst hs ht
    (hg.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)) : ContDiffOn ℝ k g t) hx
  have hderiv : iteratedDerivWithin k g s x = iteratedDerivWithin k g t x := by
    simp only [iteratedDerivWithin, hsub]
  rw [← hderiv]
  exact iteratedDerivWithin_congr heq hx

/-- A smooth error on the phase interval extends exactly to any larger compact
interval, with finite derivative bounds uniform over the original error. -/
theorem exists_phaseError_extension (P : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ f : ℝ → ℝ,
      ContDiffOn ℝ ∞ f phaseInterval →
      (∀ k ≤ P, ∀ x ∈ phaseInterval, ‖iteratedDerivWithin k f phaseInterval x‖ ≤ δ) →
      ∀ l u : ℝ, l < 1 → 2 < u →
      ∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc l u) ∧ EqOn g f phaseInterval ∧
        ∀ k ≤ P, ∀ x ∈ Icc l u, ‖iteratedDerivWithin k g (Icc l u) x‖ ≤ C * δ := by
  obtain ⟨C, hC, hrealize⟩ :=
    SmoothExtension.exists_contDiff_iteratedDeriv_eq_with_small_bound (F := ℝ) P
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro δ hδ f hf hbound l u hl hu
  have hf' : ContDiffOn ℝ ∞ f (Icc 1 2) := hf
  obtain ⟨L, hL, hLj, hLb⟩ := hrealize δ hδ
    (fun k => iteratedDerivWithin k f phaseInterval 1)
    (fun k hk => hbound k hk 1 (by norm_num [phaseInterval]))
  obtain ⟨R, hR, hRj, hRb⟩ := hrealize δ hδ
    (fun k => iteratedDerivWithin k f phaseInterval 2)
    (fun k hk => hbound k hk 2 (by norm_num [phaseInterval]))
  let fL : ℝ → ℝ := fun x => L (x - 1)
  let fR : ℝ → ℝ := fun x => R (x - 2)
  have hfL : ContDiff ℝ ∞ fL := hL.comp (contDiff_id.sub contDiff_const)
  have hfR : ContDiff ℝ ∞ fR := hR.comp (contDiff_id.sub contDiff_const)
  have hLderiv (k : ℕ) (x : ℝ) : iteratedDeriv k fL x = iteratedDeriv k L (x - 1) :=
    congrFun (iteratedDeriv_comp_sub_const k L 1) x
  have hRderiv (k : ℕ) (x : ℝ) : iteratedDeriv k fR x = iteratedDeriv k R (x - 2) :=
    congrFun (iteratedDeriv_comp_sub_const k R 2) x
  have hLzero : fL 1 = f 1 := by
    simpa [fL, iteratedDeriv_zero, iteratedDerivWithin_zero] using hLj 0
  have hRzero : fR 2 = f 2 := by
    simpa [fR, iteratedDeriv_zero, iteratedDerivWithin_zero] using hRj 0
  let g₁ : ℝ → ℝ := fun x => if x ≤ 1 then fL x else f x
  have hg₁ : ContDiffOn ℝ ∞ g₁ (Icc l 2) := by
    apply SmoothExtension.contDiffOn_Icc_ite_of_jet_match hl (by norm_num)
      hfL.contDiffOn hf'
    intro k
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hl)
      (hfL.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
        ⟨hl.le, le_rfl⟩, hLderiv, sub_self, hLj]
    rfl
  have hg₁eq : EqOn g₁ f phaseInterval := by
    intro x hx
    dsimp [g₁]
    split_ifs with h
    · have : x = 1 := le_antisymm h hx.1
      subst x
      exact hLzero
    · rfl
  have hsub : phaseInterval ⊆ Icc l 2 := fun x hx => ⟨hl.le.trans hx.1, hx.2⟩
  let g : ℝ → ℝ := fun x => if x ≤ 2 then g₁ x else fR x
  have hg : ContDiffOn ℝ ∞ g (Icc l u) := by
    apply SmoothExtension.contDiffOn_Icc_ite_of_jet_match (by linarith) hu
      hg₁ hfR.contDiffOn
    intro k
    rw [iteratedDerivWithin_eq_of_restriction hsub uniqueDiffOn_phaseInterval
      (uniqueDiffOn_Icc (by linarith)) hg₁ hg₁eq (by norm_num [phaseInterval]) k]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hu)
      (hfR.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
        ⟨le_rfl, hu.le⟩, hRderiv, sub_self, hRj]
  have hgeq : EqOn g f phaseInterval := by
    intro x hx
    exact (if_pos hx.2).trans (hg₁eq hx)
  have hgLeq : EqOn g fL (Icc l 1) := by
    intro x hx
    dsimp [g, g₁]
    rw [if_pos (hx.2.trans (by norm_num)), if_pos hx.2]
  have hgReq : EqOn g fR (Icc 2 u) := by
    intro x hx
    dsimp [g]
    split_ifs with h
    · have : x = 2 := le_antisymm h hx.1
      subst x
      exact (hg₁eq (by norm_num [phaseInterval])).trans hRzero.symm
    · rfl
  have hJ : UniqueDiffOn ℝ (Icc l u) := uniqueDiffOn_Icc (by linarith)
  have hleftSub : Icc l 1 ⊆ Icc l u := fun y hy => ⟨hy.1, by linarith [hy.2]⟩
  have hrightSub : Icc 2 u ⊆ Icc l u := fun y hy => ⟨by linarith [hy.1], hy.2⟩
  have hmiddleSub : phaseInterval ⊆ Icc l u :=
    fun y hy => ⟨hl.le.trans hy.1, hy.2.trans hu.le⟩
  refine ⟨g, hg, hgeq, ?_⟩
  intro k hk x hx
  by_cases hleft : x ≤ 1
  · have hxL : x ∈ Icc l 1 := ⟨hx.1, hleft⟩
    rw [iteratedDerivWithin_eq_of_restriction
      hleftSub
      (uniqueDiffOn_Icc hl) hJ hg hgLeq hxL k,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hl)
        (hfL.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt hxL, hLderiv]
    exact (hLb k hk _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le)
  · by_cases hright : 2 ≤ x
    · have hxR : x ∈ Icc 2 u := ⟨hright, hx.2⟩
      rw [iteratedDerivWithin_eq_of_restriction
        hrightSub
        (uniqueDiffOn_Icc hu) hJ hg hgReq hxR k,
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hu)
          (hfR.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt hxR, hRderiv]
      exact (hRb k hk _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le)
    · have hxF : x ∈ phaseInterval := ⟨(lt_of_not_ge hleft).le, (lt_of_not_ge hright).le⟩
      rw [iteratedDerivWithin_eq_of_restriction
        hmiddleSub
        uniqueDiffOn_phaseInterval hJ hg hgeq hxF k]
      exact (hbound k hk x hxF).trans (by
        simpa using mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C) hδ.le)

/-- A primitive of the reference derivative on the positive half-line. -/
def modelPhasePrimitive (σ : ℝ) (x : ℝ) : ℝ :=
  if σ = 1 then Real.log x else x ^ (1 - σ) / (1 - σ)

private lemma hasDerivAt_modelPhasePrimitive (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (modelPhasePrimitive σ) (modelPhase σ x) x := by
  change HasDerivAt (fun y => if σ = 1 then Real.log y else y ^ (1 - σ) / (1 - σ))
    (modelPhase σ x) x
  by_cases hσ : σ = 1
  · subst σ
    simpa [modelPhasePrimitive, modelPhase, Real.rpow_neg_one] using Real.hasDerivAt_log hx.ne'
  · have h := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hx.ne')).div_const (1 - σ)
    have hd : (1 - σ) * x ^ (1 - σ - 1) / (1 - σ) = x ^ (-σ) := by
      have hs : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
      rw [show 1 - σ - 1 = -σ by ring, mul_div_cancel_left₀ _ hs]
    simpa only [modelPhasePrimitive, if_neg hσ, modelPhase, hd] using h

private lemma contDiffOn_modelPhasePrimitive (σ : ℝ) {s : Set ℝ}
    (hs : ∀ x ∈ s, 0 < x) : ContDiffOn ℝ ∞ (modelPhasePrimitive σ) s := by
  intro x hx
  change ContDiffWithinAt ℝ ∞
    (fun y => if σ = 1 then Real.log y else y ^ (1 - σ) / (1 - σ)) s x
  by_cases hσ : σ = 1
  · simp only [hσ]
    exact (Real.contDiffAt_log.mpr (hs x hx).ne').contDiffWithinAt
  · simp only [if_neg hσ]
    exact ((Real.contDiffAt_rpow_const_of_ne (hs x hx).ne').div_const _).contDiffWithinAt

private lemma iteratedDerivWithin_modelPhasePrimitive (σ : ℝ) {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hpos : ∀ x ∈ s, 0 < x) (p : ℕ) {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin (p + 1) (modelPhasePrimitive σ) s x =
      iteratedDerivWithin p (modelPhase σ) s x := by
  rw [iteratedDerivWithin_succ']
  apply iteratedDerivWithin_congr (s := s) _ hx
  intro y hy
  exact (hasDerivAt_modelPhasePrimitive σ (hpos y hy)).hasDerivWithinAt.derivWithin
    (hs.uniqueDiffWithinAt hy)

/-- An approximate model phase extends exactly to any larger positive compact
interval. The model derivative errors remain uniformly small through the same
order; the constant is independent of the phase and of its higher derivatives. -/
theorem exists_approximateModelPhase_extension (P : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ (σ : ℝ) (F : ℝ → ℝ),
      IsApproximateModelPhaseFunction F σ P δ →
      ∀ l u : ℝ, 0 < l → l < 1 → 2 < u →
      ∃ G : ℝ → ℝ, ContDiffOn ℝ ∞ G (Icc l u) ∧ EqOn G F phaseInterval ∧
        ∀ p ≤ P, ∀ x ∈ Icc l u,
          ‖iteratedDerivWithin (p + 1) G (Icc l u) x -
            iteratedDerivWithin p (modelPhase σ) (Icc l u) x‖ ≤ C * δ := by
  obtain ⟨C, hC, hextend⟩ := exists_phaseError_extension (P + 1)
  refine ⟨C, hC, ?_⟩
  intro δ hδ σ F hF l u hl0 hl hu
  have hpos : ∀ x ∈ phaseInterval, 0 < x := fun x hx => zero_lt_one.trans_le hx.1
  have hQ := contDiffOn_modelPhasePrimitive σ hpos
  let c : ℝ := F 1 - modelPhasePrimitive σ 1
  let Q : ℝ → ℝ := fun x => c + modelPhasePrimitive σ x
  let f : ℝ → ℝ := fun x => F x - Q x
  have hQc : ContDiffOn ℝ ∞ Q phaseInterval := contDiffOn_const.add hQ
  have hf : ContDiffOn ℝ ∞ f phaseInterval := hF.1.sub hQc
  have hf0 : f 1 = 0 := by dsimp [f, Q, c]; ring
  have herror (p : ℕ) {x : ℝ} (hx : x ∈ phaseInterval) :
      iteratedDerivWithin (p + 1) f phaseInterval x = modelPhaseErrorAt F σ p x := by
    change iteratedDerivWithin (p + 1) (F - Q) phaseInterval x = _
    rw [iteratedDerivWithin_sub hx uniqueDiffOn_phaseInterval
      ((hF.1.of_le (by exact_mod_cast (le_top : ((p + 1) : ℕ∞) ≤ ⊤))) x hx)
      ((hQc.of_le (by exact_mod_cast (le_top : ((p + 1) : ℕ∞) ≤ ⊤))) x hx)]
    change iteratedDerivWithin (p + 1) F phaseInterval x -
      iteratedDerivWithin (p + 1) (fun x => c + modelPhasePrimitive σ x) phaseInterval x = _
    rw [iteratedDerivWithin_const_add (by omega),
      iteratedDerivWithin_modelPhasePrimitive σ uniqueDiffOn_phaseInterval hpos p hx]
    rfl
  have hfirst : ∀ x ∈ phaseInterval, ‖derivWithin f phaseInterval x‖ ≤ δ := by
    intro x hx
    have h := hF.2 0 (by omega) ⟨x, hx⟩
    rw [← herror 0 hx] at h
    simpa only [Nat.zero_add, iteratedDerivWithin_one] using h
  have hb : ∀ k ≤ P + 1, ∀ x ∈ phaseInterval,
      ‖iteratedDerivWithin k f phaseInterval x‖ ≤ δ := by
    intro k hk x hx
    cases k with
    | zero =>
      have h := (convex_Icc (1 : ℝ) 2).norm_image_sub_le_of_norm_derivWithin_le
        (hf.differentiableOn (by simp)) hfirst
        (show (1 : ℝ) ∈ phaseInterval by norm_num [phaseInterval]) hx
      have hnorm : ‖x - 1‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (sub_nonneg.2 hx.1)]
        linarith [hx.2]
      simp only [hf0, sub_zero] at h
      exact h.trans (by simpa using mul_le_mul_of_nonneg_left hnorm hδ.le)
    | succ p =>
      rw [herror p hx]
      exact hF.2 p (by omega) ⟨x, hx⟩
  obtain ⟨g, hg, hgeq, hgb⟩ := hextend δ hδ f hf hb l u hl hu
  let G : ℝ → ℝ := fun x => g x + Q x
  have hposJ : ∀ x ∈ Icc l u, 0 < x := fun x hx => hl0.trans_le hx.1
  have hQJ : ContDiffOn ℝ ∞ Q (Icc l u) :=
    contDiffOn_const.add (contDiffOn_modelPhasePrimitive σ hposJ)
  refine ⟨G, hg.add hQJ, ?_, ?_⟩
  · intro x hx
    dsimp [G]
    rw [hgeq hx]
    dsimp [f]
    ring
  · intro p hp x hx
    have hJ := uniqueDiffOn_Icc (show l < u by linarith)
    rw [iteratedDerivWithin_fun_add hx hJ
      ((hg.of_le (by exact_mod_cast (le_top : ((p + 1) : ℕ∞) ≤ ⊤))) x hx)
      ((hQJ.of_le (by exact_mod_cast (le_top : ((p + 1) : ℕ∞) ≤ ⊤))) x hx)]
    change ‖iteratedDerivWithin (p + 1) g (Icc l u) x +
      iteratedDerivWithin (p + 1) (fun x => c + modelPhasePrimitive σ x) (Icc l u) x - _‖ ≤ _
    rw [iteratedDerivWithin_const_add (by omega),
      iteratedDerivWithin_modelPhasePrimitive σ hJ hposJ p hx, add_sub_cancel_right]
    exact hgb (p + 1) (by omega) x hx


private theorem exists_global_smooth_restriction (l u : ℝ) (hl : 0 < l) (hlu : l < u)
    (g : ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g (Icc (l / 2) (2 * u))) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ EqOn G g (Icc l u) := by
  let χ : ContDiffBump ((l + u) / 2 : ℝ) :=
    ⟨(u - l) / 2 + l / 8, (u - l) / 2 + l / 4, by linarith, by linarith⟩
  let G : ℝ → ℝ := fun x => χ x * g x
  have hsupport : tsupport (χ : ℝ → ℝ) ⊆ Ioo (l / 2) (2 * u) := by
    intro x hx
    rw [χ.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    change -((u - l) / 2 + l / 4) ≤ x - (l + u) / 2 ∧
      x - (l + u) / 2 ≤ (u - l) / 2 + l / 4 at hx
    constructor <;> linarith [hx.1, hx.2]
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport (χ : ℝ → ℝ)
    · have hm := hsupport hx
      exact χ.contDiffAt.mul (hg.contDiffAt
        (Icc_mem_nhds hm.1 hm.2))
    · have he : G =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        have hz := notMem_tsupport_iff_eventuallyEq.mp hx
        filter_upwards [hz] with y hy
        simp [G, hy]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨G, hG, ?_⟩
  intro x hx
  have hχ : χ x = 1 := by
    apply χ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    change -((u - l) / 2 + l / 8) ≤ x - (l + u) / 2 ∧
      x - (l + u) / 2 ≤ (u - l) / 2 + l / 8
    constructor <;> linarith [hx.1, hx.2]
  simp [G, hχ]

/-- The controlled extension can be chosen globally smooth. This allows the
ordinary-derivative normal-form machinery to be applied on a larger positive
interval, without imposing any conditions on the original phase outside `[1,2]`. -/
theorem exists_global_approximateModelPhase_extension (P : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ σ : ℝ, ∀ F : ℝ → ℝ,
      IsApproximateModelPhaseFunction F σ P δ →
      ∀ l u : ℝ, 0 < l → l < 1 → 2 < u →
      ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ EqOn G F phaseInterval ∧
        ∀ p ≤ P, ∀ x ∈ Icc l u,
          ‖iteratedDeriv (p + 1) G x - iteratedDeriv p (modelPhase σ) x‖ ≤ C * δ := by
  obtain ⟨C, hC, hext⟩ := exists_approximateModelPhase_extension P
  refine ⟨C, hC, ?_⟩
  intro δ hδ σ F hF l u hl0 hl hu
  have hlu : l < u := by linarith
  obtain ⟨g, hg, heq, hb⟩ := hext δ hδ σ F hF (l / 2) (2 * u)
    (by positivity) (by linarith) (by linarith)
  obtain ⟨G, hG, hGg⟩ := exists_global_smooth_restriction l u hl0 hlu g hg
  have hJ : UniqueDiffOn ℝ (Icc l u) := uniqueDiffOn_Icc hlu
  have hK : UniqueDiffOn ℝ (Icc (l / 2) (2 * u)) := uniqueDiffOn_Icc (by linarith)
  have hJK : Icc l u ⊆ Icc (l / 2) (2 * u) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hmodel : ContDiffOn ℝ ∞ (modelPhase σ) (Icc (l / 2) (2 * u)) := by
    intro x hx
    exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (show 0 < x by linarith
      [hx.1]))).contDiffWithinAt
  refine ⟨G, hG, ?_, ?_⟩
  · intro x hx
    exact (hGg ⟨hl.le.trans hx.1, hx.2.trans hu.le⟩).trans (heq hx)
  · intro p hp x hx
    have hphase := iteratedDerivWithin_eq_of_restriction hJK hJ hK hg hGg.symm hx (p + 1)
    have hreference := iteratedDerivWithin_eq_of_restriction hJK hJ hK hmodel
      (fun _ _ => rfl) hx p
    have hGa : ContDiffAt ℝ (p + 1) G x := hG.contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl (p + 1))
    have hma : ContDiffAt ℝ p (modelPhase σ) x :=
      Real.contDiffAt_rpow_const_of_ne (ne_of_gt (hl0.trans_le hx.1))
    rw [iteratedDerivWithin_eq_iteratedDeriv hJ hGa hx] at hphase
    rw [iteratedDerivWithin_eq_iteratedDeriv hJ hma hx] at hreference
    rw [← hphase, ← hreference]
    exact hb p hp x (hJK hx)

end
end Expdb
