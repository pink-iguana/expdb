/-
Copyright (c) 2026 Expdb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Expdb contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Ring

/-!
# The quadratic factor of a phase near a stationary point

Mathlib's integral Taylor theorem factors a phase minus its tangent as a
quadratic polynomial times an averaged second derivative. This representation
includes the stationary point itself, where dividing by `(x - v)²` would be
singular. It is the starting point for the B-process change of variables.
-/

@[expose] public section
namespace Expdb

open MeasureTheory
open scoped ContDiff
noncomputable section

/-- Twice the averaged second derivative along the segment from `v` to `x`. -/
def phaseQuadraticFactor (F : ℝ → ℝ) (v x : ℝ) : ℝ :=
  2 * ∫ t : ℝ in 0..1, (1 - t) * iteratedDeriv 2 F (v + t * (x - v))

/-- The phase minus its tangent has an exact quadratic factor, including at
`x = v`. Only twice continuous differentiability along the segment is needed. -/
theorem phase_sub_tangent_eq_quadraticFactor (F : ℝ → ℝ) (v x : ℝ)
    (hF : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 F (v + t * (x - v))) :
    F x - F v - deriv F v * (x - v) =
      (x - v) ^ 2 * phaseQuadraticFactor F v x / 2 := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv
    (n := 1) (x := v) (y := x - v) hF
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_zero, pow_one, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, iteratedDeriv_zero,
    iteratedDeriv_one, smul_eq_mul, one_mul, Nat.reduceAdd] at h
  rw [show v + (x - v) = x by ring] at h
  have he : (∫ t : ℝ in 0..1,
      (1 - t) * ((x - v) ^ 2 * iteratedDeriv 2 F (v + t * (x - v)))) =
      (x - v) ^ 2 * ∫ t : ℝ in 0..1,
        (1 - t) * iteratedDeriv 2 F (v + t * (x - v)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  rw [he] at h
  dsimp [phaseQuadraticFactor]
  linarith

private lemma integral_one_sub : (∫ t : ℝ in 0..1, 1 - t) = 1 / 2 := by
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ))
    (g := fun t : ℝ => t) intervalIntegrable_const
    (continuous_id.intervalIntegrable _ _), intervalIntegral.integral_const, integral_id]
  norm_num

/-- At the stationary point the factor is the second derivative itself. -/
@[simp] theorem phaseQuadraticFactor_self (F : ℝ → ℝ) (v : ℝ) :
    phaseQuadraticFactor F v v = iteratedDeriv 2 F v := by
  simp only [phaseQuadraticFactor, sub_self, mul_zero, add_zero]
  rw [intervalIntegral.integral_mul_const]
  rw [integral_one_sub]
  ring

/-- Bounds on curvature along the segment also bound the quadratic factor.
In particular, positive curvature keeps its square root away from zero. -/
theorem phaseQuadraticFactor_bounds (F : ℝ → ℝ) (v x : ℝ) {c C : ℝ}
    (hcontinuous : ContinuousOn (fun t : ℝ => iteratedDeriv 2 F (v + t * (x - v)))
      (Set.Icc 0 1))
    (hlower : ∀ t ∈ Set.Icc (0 : ℝ) 1, c ≤ iteratedDeriv 2 F (v + t * (x - v)))
    (hupper : ∀ t ∈ Set.Icc (0 : ℝ) 1, iteratedDeriv 2 F (v + t * (x - v)) ≤ C) :
    c ≤ phaseQuadraticFactor F v x ∧ phaseQuadraticFactor F v x ≤ C := by
  have hi : IntervalIntegrable
      (fun t : ℝ => (1 - t) * iteratedDeriv 2 F (v + t * (x - v))) volume 0 1 := by
    have hc : ContinuousOn (fun t : ℝ => (1 - t) *
        iteratedDeriv 2 F (v + t * (x - v))) (Set.Icc 0 1) :=
      (continuous_const.sub continuous_id).continuousOn.mul hcontinuous
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hc
  have hconst (a : ℝ) : (∫ t : ℝ in 0..1, (1 - t) * a) = a / 2 := by
    rw [intervalIntegral.integral_mul_const]
    rw [integral_one_sub]
    ring
  have hl := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
    ((by fun_prop : Continuous (fun t : ℝ => (1 - t) * c)).intervalIntegrable 0 1) hi
    (fun t ht => mul_le_mul_of_nonneg_left (hlower t ht) (sub_nonneg.2 ht.2))
  have hu := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num) hi
    ((by fun_prop : Continuous (fun t : ℝ => (1 - t) * C)).intervalIntegrable 0 1)
    (fun t ht => mul_le_mul_of_nonneg_left (hupper t ht) (sub_nonneg.2 ht.2))
  rw [hconst] at hl hu
  dsimp [phaseQuadraticFactor]
  constructor <;> linarith

end
end Expdb
