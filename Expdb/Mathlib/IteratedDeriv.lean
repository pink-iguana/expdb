module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Supplementary lemmas for iterated derivatives

This file contains chain rules that are useful in the exponential-sums development but are not
currently available in Mathlib in the required two-set form. It also contains restriction
and compact-support bounds for iterated derivatives.
-/

@[expose] public section

namespace Expdb

open scoped ContDiff

/-- Iterated derivatives of a function precomposed with an affine map. Unlike Mathlib's
`iteratedDerivWithin_comp_const_smul`, the domain and codomain sets may be different. -/
theorem iteratedDerivWithin_comp_affine_of_mapsTo
    {f : ℝ → ℝ} {s t : Set ℝ} {x c d : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n f t) (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hx : x ∈ s) (hst : Set.MapsTo (fun y ↦ c * y + d) s t) :
    iteratedDerivWithin n (fun y ↦ f (c * y + d)) s x =
      c ^ n * iteratedDerivWithin n f t (c * x + d) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      have hcx : c * x + d ∈ t := hst hx
      have heq : Set.EqOn
          (iteratedDerivWithin n (fun y ↦ f (c * y + d)) s)
          (fun y ↦ c ^ n * iteratedDerivWithin n f t (c * y + d)) s :=
        fun y hy ↦ ih hf.of_succ hy
      have houter : DifferentiableWithinAt ℝ (iteratedDerivWithin n f t) t (c * x + d) :=
        hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) ht _ hcx
      have haffine : HasDerivWithinAt (fun y : ℝ ↦ c * y + d) c s x := by
        simpa using (((hasDerivAt_id x).const_mul c).add_const d |>.hasDerivWithinAt)
      have hcomp : DifferentiableWithinAt ℝ
          (fun y ↦ iteratedDerivWithin n f t (c * y + d)) s x := by
        change DifferentiableWithinAt ℝ
          ((iteratedDerivWithin n f t) ∘ fun y ↦ c * y + d) s x
        exact houter.comp x haffine.differentiableWithinAt hst
      rw [iteratedDerivWithin_succ, derivWithin_congr heq (ih hf.of_succ hx),
        derivWithin_const_mul _ hcomp, iteratedDerivWithin_succ,
        ← Function.comp_def, derivWithin.scomp x houter
          haffine.differentiableWithinAt hst]
      rw [haffine.derivWithin (hs.uniqueDiffWithinAt hx)]
      simp only [pow_succ]
      ring

/-- Iterated derivatives agree under restriction to a smaller set on which the functions agree. -/
theorem iteratedDerivWithin_eq_of_restriction
    {f g : ℝ → ℝ} {s t : Set ℝ} (hst : s ⊆ t)
    (hs : UniqueDiffOn ℝ s) (ht : UniqueDiffOn ℝ t)
    (hg : ContDiffOn ℝ ∞ g t) (heq : Set.EqOn g f s) {x : ℝ} (hx : x ∈ s) (k : ℕ) :
    iteratedDerivWithin k g t x = iteratedDerivWithin k f s x := by
  have hsub := iteratedFDerivWithin_subset hst hs ht
    (hg.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)) : ContDiffOn ℝ k g t) hx
  have hderiv : iteratedDerivWithin k g s x = iteratedDerivWithin k g t x := by
    simp only [iteratedDerivWithin, hsub]
  rw [← hderiv]
  exact iteratedDerivWithin_congr heq hx

/-- Every derivative of a compactly supported smooth function is bounded. -/
theorem exists_bound_iteratedDeriv_of_hasCompactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (k : ℕ) :
    ∃ C, ∀ x, ‖iteratedDeriv k f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := Continuous.bounded_above_of_compact_support
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)) (hc.iteratedFDeriv (𝕜 := ℝ) k)
  refine ⟨C, fun x ↦ ?_⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hC x

end Expdb
