module

public import Expdb.ExponentialSums.UpperSemicontinuity

/-!
# Bounds for exponential sum growth exponents

This module records the classical transformations of the exponential sum growth exponent from
the blueprint's Exponential sum growth exponents chapter (`beta-chapter`).
-/

@[expose] public section

open Filter
open scoped Expdb NNReal

noncomputable section

namespace Expdb

/-! ## Bound data -/

/-- The assertion that `f` is an upper bound for `β` on `s`. -/
def IsExponentSumGrowthBoundOn (s : Set ℝ≥0) (f : ℝ≥0 → ℝ) : Prop :=
  ∀ ⦃α⦄, α ∈ s → exponentSumGrowthExponent α ≤ f α

/-- Exact rational data for an affine upper bound on `β` over a closed interval. -/
structure AffineBetaBound where
  /-- The slope of the affine function. -/
  slope : ℚ
  /-- The constant term of the affine function. -/
  intercept : ℚ
  /-- The lower endpoint of the interval. -/
  lower : ℚ
  /-- The upper endpoint of the interval. -/
  upper : ℚ
  deriving DecidableEq, Repr

namespace AffineBetaBound

/-- Evaluate the affine function associated to `b`. -/
def eval (b : AffineBetaBound) (α : ℝ) : ℝ := b.slope * α + b.intercept

/-- The assertion that an affine bound is valid on its stated interval. -/
def IsValid (b : AffineBetaBound) : Prop :=
  ∀ α : ℝ≥0, (b.lower : ℝ) ≤ α → (α : ℝ) ≤ b.upper →
    exponentSumGrowthExponent α ≤ b.eval α

end AffineBetaBound

/-- Extend the exponential sum growth exponent to real inputs by truncating negative inputs to
zero. -/
def exponentSumGrowthExponentReal (α : ℝ) : ℝ :=
  exponentSumGrowthExponent α.toNNReal

/-- On nonnegative inputs, the real extension of `β` agrees with `β`. -/
@[simp] theorem exponentSumGrowthExponentReal_of_nonneg {α : ℝ} (hα : 0 ≤ α) :
    exponentSumGrowthExponentReal α = exponentSumGrowthExponent ⟨α, hα⟩ := by
  unfold exponentSumGrowthExponentReal
  apply congrArg exponentSumGrowthExponent
  apply NNReal.eq
  rw [Real.coe_toNNReal _ hα]
  rfl

/-! ## Classical transformations -/

/-- The van der Corput `A`-process for `β` (blueprint Lemma `vdca-beta`). -/
theorem vanDerCorputA_exponentSumGrowthExponent
    (α : ℝ≥0) (h : ℝ) (hα : α ≤ 2 / 3) (hh : 0 ≤ h) :
    2 * exponentSumGrowthExponent α ≤
      max (max (2 * (α : ℝ) - h) (2 * h))
        ((α : ℝ) - h + sSup
          ((fun h' : ℝ ↦
            (h' + 1 - α) *
                exponentSumGrowthExponentReal ((α : ℝ) / (h' + 1 - α)) + h') ''
            Set.Icc (2 * (α : ℝ) - 1) h)) := by
  sorry

/-- The van der Corput inequality for `β` (blueprint Proposition `beta-vdc`). -/
theorem exponentSumGrowthExponent_le_vanDerCorput
    (α : ℝ≥0) (k : ℕ) (hk : 2 ≤ k) (hα : 0 < α) :
    exponentSumGrowthExponent α ≤
      max ((α : ℝ) + (1 - k * (α : ℝ)) / ((2 : ℝ) ^ k - 2))
        ((1 - 2 ^ (2 - (k : ℤ))) * (α : ℝ) -
          (1 - (α : ℝ)) / ((2 : ℝ) ^ k - 2)) := by
  sorry

/-- The exponential sum growth exponent at one is `1 / 2`. -/
@[simp] theorem exponentSumGrowthExponent_one :
    exponentSumGrowthExponent 1 = 1 / 2 := by
  apply le_antisymm
  · have h := exponentSumGrowthExponent_le_vanDerCorput 1 2 (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  · exact (exponentSumGrowthExponent_mem_Icc (α := 1) (by norm_num)).1

/-- The optimized van der Corput inequality (blueprint Corollary `vdc-opt`). -/
theorem exponentSumGrowthExponent_le_vanDerCorput_sInf
    (α : ℝ≥0) (hα : 0 < α) :
    exponentSumGrowthExponent α ≤
      sInf {x : ℝ | ∃ k : ℕ, 2 ≤ k ∧
        x = (α : ℝ) + (1 - k * (α : ℝ)) / ((2 : ℝ) ^ k - 2)} := by
  sorry

/-! ## Full dyadic intervals -/

/-- The exponential sum bound obtained by testing only the full interval `[N, 2N]`. -/
def IsFullIntervalExponentSumBound (α : ℝ≥0) (β : ℝ) : Prop :=
  ∀ (N T : VariableObject ℝ)
    (F : VariableFunction (VariableObject.fixed ℝ) ℝ),
    (∀ i, 1 ≤ N i) →
    (∀ i, 1 ≤ T i) →
    T.IsUnbounded →
    IsPowerAsymptotic N T (α : ℝ) →
    IsModelPhaseFunction F →
    IsPowerBounded
      (exponentialSum F T N (fun i ↦ ⌈N i⌉₊) (fun i ↦ ⌊2 * N i⌋₊)) T β

/-- Arbitrary subintervals may be replaced by the full interval in the definition of `β`
(blueprint Lemma `interval-set`). -/
theorem isExponentSumBound_iff_fullInterval {α : ℝ≥0} {β : ℝ} :
    IsExponentSumBound α β ↔ IsFullIntervalExponentSumBound α β := by
  sorry

/-- Characterization of `β` using only full dyadic intervals. -/
theorem exponentSumGrowthExponent_le_iff_fullInterval {α : ℝ≥0} {β : ℝ} :
    exponentSumGrowthExponent α ≤ β ↔ IsFullIntervalExponentSumBound α β := by
  rw [exponentSumGrowthExponent_le_iff, isExponentSumBound_iff_fullInterval]

/-! ## Reflection -/

/-- Reflection for the exponential sum growth exponent (blueprint Lemma `beta-reflect`). -/
theorem exponentSumGrowthExponent_reflection
    (α : ℝ≥0) (hα : 0 < α) (hα' : α < 1) :
    exponentSumGrowthExponent (1 - α) =
      1 / 2 - (α : ℝ) + exponentSumGrowthExponent α := by
  sorry

end Expdb

end
