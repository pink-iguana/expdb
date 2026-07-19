import expdb.Basic.Definitions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Project-specific asymptotic notation

This module formalizes the infinitesimal comparison relation and underspill principle from
Chapter 2 of the ANTEDB blueprint. The notation `X ≤o Y` is available after
`open scoped Expdb`.
-/

open Filter Topology

namespace Expdb

/-- `X ≤ Y + o(1)` in the strict sense that the error is bounded by a sequence tending to zero. -/
def IsLEUpToInfinitesimal (X Y : ℕ → ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
    ∀ᶠ i in atTop, X i ≤ Y i + ε i

/-- Project-specific notation for comparison up to an infinitesimal error. -/
scoped[Expdb] notation X " ≤o " Y => IsLEUpToInfinitesimal X Y

open scoped Expdb

/-- **Underspill principle.** The relation `X ≤ Y + o(1)` holds if and only if it continues to
hold after adding every fixed positive error to `Y`. -/
theorem underspill (X Y : ℕ → ℝ) :
    (X ≤o Y) ↔
    (∀ ε : ℝ, ε > 0 → X ≤o (fun i => Y i + ε)) := by
  constructor
  · intro ⟨εseq, hεseq_inf, hεseq_bound⟩ ε hε
    refine ⟨εseq, hεseq_inf, ?_⟩
    filter_upwards [hεseq_bound] with i hi
    linarith
  · intro h
    have key : ∀ c : ℝ, c > 0 → ∀ᶠ i in atTop, X i - Y i < c := by
      intro c hc
      have hc2 : c / 2 > 0 := by linarith
      obtain ⟨dseq, hdseq_inf, hdseq_bound⟩ := h (c / 2) hc2
      rw [Metric.tendsto_nhds] at hdseq_inf
      have hdseq_small := hdseq_inf (c / 2) hc2
      filter_upwards [hdseq_bound, hdseq_small] with i hi_bound hi_small
      rw [Real.dist_eq] at hi_small
      have hi_small' : |dseq i| < c / 2 := by simpa only [sub_zero] using hi_small
      have hdseq_lt : dseq i < c / 2 := lt_of_abs_lt hi_small'
      linarith
    refine ⟨fun i => max (X i - Y i) 0, ?_, Filter.Eventually.of_forall fun i => ?_⟩
    · rw [Metric.tendsto_nhds]
      intro δ hδ
      filter_upwards [key δ hδ] with i hi
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_right _ _)]
      exact max_lt hi hδ
    · have hi : X i - Y i ≤ max (X i - Y i) 0 := le_max_left _ _
      linarith

end Expdb
