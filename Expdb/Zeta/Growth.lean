module

public import Expdb.Basic.PowerAsymptotics
public import Expdb.Basic.AutomaticUniformity
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Zeta growth exponents

This module defines admissible zeta growth exponents and their infimum `μ(σ)` from the
blueprint definition `zeta-grow-def`. It proves that the explicit epsilon bounds are
equivalent to bounds along every unbounded sequence of heights.

The infimum is admissible when the candidate set is nonempty. When the set is also
bounded below, the infimum is its least element.
-/

@[expose] public section

open Filter Topology
open scoped Expdb

noncomputable section

namespace Expdb

/-- The Riemann zeta function evaluated at `σ + it`. -/
def zetaAt (σ t : ℝ) : ℂ := riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)

/-- Reflection of the height conjugates zeta, by its real Dirichlet coefficients. -/
theorem zetaAt_neg (σ t : ℝ) :
    zetaAt σ (-t) = star (zetaAt σ t) := by
  simpa [zetaAt, map_add, map_mul] using
    riemannZeta_conj ((σ : ℂ) + (t : ℂ) * Complex.I)

/-- Zeta has the same norm at positive and negative heights. -/
@[simp] theorem norm_zetaAt_neg (σ t : ℝ) :
    ‖zetaAt σ (-t)‖ = ‖zetaAt σ t‖ := by
  rw [zetaAt_neg, norm_star]

/-- Admissible zeta growth exponent (`zeta-grow-def`): for each positive epsilon,
one constant controls both the threshold and the bound, for both signs of the height. -/
def IsZetaGrowthBound (σ b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, C ≤ |t| → ‖zetaAt σ t‖ ≤ C * |t| ^ (b + ε)

/-- The candidate set for the zeta growth exponent. -/
def zetaGrowthBounds (σ : ℝ) : Set ℝ := {b | IsZetaGrowthBound σ b}

/-- The real infimum `μ(σ)` from `zeta-grow-def`. It is the least admissible exponent
when the candidate set is nonempty and bounded below. -/
def zetaGrowthExponent (σ : ℝ) : ℝ := sInf (zetaGrowthBounds σ)

@[simp] theorem mem_zetaGrowthBounds {σ b : ℝ} :
    b ∈ zetaGrowthBounds σ ↔ IsZetaGrowthBound σ b := Iff.rfl

/-- A witness constant can always be enlarged to at least one. -/
theorem IsZetaGrowthBound.exists_constant_ge_one {σ b : ℝ} (h : IsZetaGrowthBound σ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, C ≤ |t| →
      ‖zetaAt σ t‖ ≤ C * |t| ^ (b + ε) := by
  obtain ⟨C, _, hC⟩ := h ε hε
  refine ⟨max C 1, le_max_right _ _, fun t ht => ?_⟩
  exact (hC t ((le_max_left _ _).trans ht)).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _))

/-- Increasing an admissible exponent preserves admissibility. -/
theorem IsZetaGrowthBound.mono {σ b c : ℝ} (h : IsZetaGrowthBound σ b)
    (hbc : b ≤ c) : IsZetaGrowthBound σ c := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h.exists_constant_ge_one hε
  refine ⟨C, zero_lt_one.trans_le hC, fun t ht => ?_⟩
  exact (hb t ht).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (hC.trans ht) (by linarith)) (by linarith))

/-- Underspill for admissible zeta growth exponents. -/
theorem isZetaGrowthBound_of_forall_gt {σ b : ℝ}
    (h : ∀ c : ℝ, b < c → IsZetaGrowthBound σ c) : IsZetaGrowthBound σ b := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h (b + ε / 2) (by linarith) (ε / 2) (by linarith)
  refine ⟨C, hC, ?_⟩
  simpa only [show b + ε / 2 + ε / 2 = b + ε by ring] using hb

/-- The set of admissible zeta growth exponents is closed, as asserted after
`zeta-grow-def`. -/
theorem isClosed_zetaGrowthBounds (σ : ℝ) : IsClosed (zetaGrowthBounds σ) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro b hb
  have hnot : ¬ IsZetaGrowthBound σ b := hb
  have hbad : ∃ c : ℝ, b < c ∧ ¬ IsZetaGrowthBound σ c := by
    by_contra h
    push Not at h
    exact hnot (isZetaGrowthBound_of_forall_gt h)
  obtain ⟨c, hbc, hc⟩ := hbad
  apply Filter.mem_of_superset (Iio_mem_nhds hbc)
  intro x hx
  exact fun h => hc (h.mono hx.le)

/-- It suffices to prove the explicit growth bounds at positive heights. Conjugation
symmetry supplies the negative heights, including the line `σ = 1`. -/
theorem isZetaGrowthBound_iff_positive_height {σ b : ℝ} :
    IsZetaGrowthBound σ b ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
        ∀ t : ℝ, C ≤ t → ‖zetaAt σ t‖ ≤ C * t ^ (b + ε) := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hb⟩ := h ε hε
    exact ⟨C, hC, fun t ht => by
      simpa [abs_of_pos (hC.trans_le ht)] using
        hb t (by simpa [abs_of_pos (hC.trans_le ht)] using ht)⟩
  · intro h ε hε
    obtain ⟨C, hC, hb⟩ := h ε hε
    refine ⟨C, hC, fun t ht => ?_⟩
    by_cases ht0 : 0 ≤ t
    · simpa [abs_of_nonneg ht0] using hb t (by simpa [abs_of_nonneg ht0] using ht)
    · have htneg : t < 0 := lt_of_not_ge ht0
      simpa [abs_of_neg htneg] using hb (-t) (by simpa [abs_of_neg htneg] using ht)

/-- The infimum is admissible when the candidate set is nonempty. -/
theorem isZetaGrowthBound_zetaGrowthExponent {σ : ℝ}
    (hne : (zetaGrowthBounds σ).Nonempty) :
    IsZetaGrowthBound σ (zetaGrowthExponent σ) := by
  apply isZetaGrowthBound_of_forall_gt
  intro c hc
  obtain ⟨b, hb, hbc⟩ := exists_lt_of_csInf_lt hne hc
  exact hb.mono hbc.le

/-- For a nonempty candidate set bounded below, `μ(σ) ≤ b` if and only if `b` is admissible. -/
theorem zetaGrowthExponent_le_iff {σ b : ℝ}
    (hne : (zetaGrowthBounds σ).Nonempty) (hbd : BddBelow (zetaGrowthBounds σ)) :
    zetaGrowthExponent σ ≤ b ↔ IsZetaGrowthBound σ b := by
  constructor
  · exact fun h => (isZetaGrowthBound_zetaGrowthExponent hne).mono h
  · exact fun h => csInf_le hbd h

/-- The infimum is the least admissible exponent when the candidate set is nonempty
and bounded below. -/
theorem isLeast_zetaGrowthExponent {σ : ℝ}
    (hne : (zetaGrowthBounds σ).Nonempty) (hbd : BddBelow (zetaGrowthBounds σ)) :
    IsLeast (zetaGrowthBounds σ) (zetaGrowthExponent σ) :=
  ⟨isZetaGrowthBound_zetaGrowthExponent hne,
    fun _ h => (zetaGrowthExponent_le_iff hne hbd).mpr h⟩

/-- Sequence formulation of the blueprint's unbounded-height growth bound. -/
def IsZetaGrowthBoundSequential (σ b : ℝ) : Prop :=
  ∀ t : VariableObject ℝ, (∀ i, 1 ≤ |t i|) → t.IsUnbounded →
    IsPowerBounded (fun i => zetaAt σ (t i)) (fun i => |t i|) b

/-- Explicit bounds imply bounds along every unbounded sequence of heights. -/
theorem IsZetaGrowthBound.toSequential {σ b : ℝ} (h : IsZetaGrowthBound σ b) :
    IsZetaGrowthBoundSequential σ b := by
  intro t ht htop
  have habstop : VariableObject.IsUnbounded (fun i => |t i|) := by
    simpa [VariableObject.IsUnbounded, Real.norm_eq_abs] using htop
  apply (isPowerBounded_iff_forall_pos _ _ b ht habstop).2
  intro ε hε
  obtain ⟨C, _, hC⟩ := h ε hε
  apply Asymptotics.IsBigO.of_bound C
  have hlarge : ∀ᶠ i in atTop, C ≤ |t i| :=
    (tendsto_atTop.1 htop) C
  filter_upwards [hlarge] with i hi
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hC (t i) hi

/-- Full-tail automatic uniformity turns sequence bounds back into explicit bounds. -/
theorem IsZetaGrowthBoundSequential.toExplicit {σ b : ℝ}
    (h : IsZetaGrowthBoundSequential σ b) : IsZetaGrowthBound σ b := by
  intro ε hε
  let E : VariableObject (Set ℝ) := fun i => {t | (i : ℝ) + 1 ≤ |t|}
  have hE : ∀ i, (E i).Nonempty := by
    intro i
    refine ⟨(i : ℝ) + 1, ?_⟩
    simp [E, abs_of_nonneg (by positivity : 0 ≤ (i : ℝ) + 1)]
  let f : VariableFunction (fun i => E i) ℝ := fun _ t =>
    ‖zetaAt σ t‖ / |(t : ℝ)| ^ (b + ε)
  have hf : f.IsChoicewiseBounded := by
    intro t
    have ht : ∀ i, 1 ≤ |(t i : ℝ)| := fun i => by
      have hi := (t i).property
      dsimp [E] at hi
      linarith [Nat.cast_nonneg (α := ℝ) i]
    have htop : VariableObject.IsUnbounded (fun i => (t i : ℝ)) := by
      unfold VariableObject.IsUnbounded
      simp only [Real.norm_eq_abs]
      apply tendsto_atTop_mono (fun i : ℕ => show (i : ℝ) ≤ |(t i : ℝ)| by
        have hi := (t i).property
        dsimp [E] at hi
        linarith)
      exact tendsto_natCast_atTop_atTop
    have habstop : VariableObject.IsUnbounded (fun i => |(t i : ℝ)|) := by
      simpa [VariableObject.IsUnbounded, Real.norm_eq_abs] using htop
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp
      ((isPowerBounded_iff_forall_pos _ _ b ht habstop).1 (h _ ht htop) ε hε)
    refine ⟨C, ?_⟩
    filter_upwards [hC] with i hi
    have hpos : 0 < |(t i : ℝ)| ^ (b + ε) :=
      Real.rpow_pos_of_pos (zero_lt_one.trans_le (ht i)) _
    simpa [f, Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg _),
      abs_of_pos hpos, div_le_iff₀ hpos] using hi
  obtain ⟨C, hC⟩ := (VariableFunction.isChoicewiseBounded_iff_eventually_uniform E hE f).1 hf
  obtain ⟨i, hi⟩ := eventually_atTop.mp hC
  let D : ℝ := max (max C 1) ((i : ℝ) + 1)
  have hD1 : 1 ≤ D := (le_max_right C 1).trans (le_max_left _ _)
  refine ⟨D, zero_lt_one.trans_le hD1, fun t ht => ?_⟩
  have hti : t ∈ E i := (le_max_right _ _).trans ht
  have hbound := hi i le_rfl ⟨t, hti⟩
  have hpos : 0 < |t| ^ (b + ε) := Real.rpow_pos_of_pos (zero_lt_one.trans_le (hD1.trans ht)) _
  have hratio : ‖zetaAt σ t‖ / |t| ^ (b + ε) ≤ C := by
    simpa [f, Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg _),
      abs_of_pos hpos] using hbound
  exact ((div_le_iff₀ hpos).mp hratio).trans
    (mul_le_mul_of_nonneg_right ((le_max_left C 1).trans (le_max_left _ _)) hpos.le)

/-- Compatibility of the blueprint's two growth-bound formulations. -/
theorem isZetaGrowthBound_iff_sequential {σ b : ℝ} :
    IsZetaGrowthBound σ b ↔ IsZetaGrowthBoundSequential σ b :=
  ⟨IsZetaGrowthBound.toSequential, IsZetaGrowthBoundSequential.toExplicit⟩

/-- The bound holds along every unbounded height sequence, without any restriction
on its initial values (in particular, the sequence may initially meet the pole). -/
theorem IsZetaGrowthBound.isPowerBounded {σ b : ℝ} (h : IsZetaGrowthBound σ b)
    (t : VariableObject ℝ) (ht : t.IsUnbounded) :
    IsPowerBounded (fun i => zetaAt σ (t i)) (fun i => |t i|) b := by
  let t' : VariableObject ℝ := fun i => if 1 ≤ |t i| then t i else 1
  have ht' : ∀ i, 1 ≤ |t' i| := by
    intro i
    dsimp [t']
    split_ifs with hi
    · exact hi
    · norm_num
  have heq : t' =ᶠ[atTop] t := by
    have hlarge : ∀ᶠ i in atTop, 1 ≤ |t i| := (tendsto_atTop.1 ht) 1
    filter_upwards [hlarge] with i hi
    simp [t', hi]
  have hunbounded : t'.IsUnbounded := by
    unfold VariableObject.IsUnbounded at *
    exact (tendsto_congr' (heq.mono fun i hi => congrArg norm hi)).mpr ht
  obtain ⟨exponent, hexponent, hb⟩ := h.toSequential t' ht' hunbounded
  refine ⟨exponent, hexponent, hb.congr' ?_ ?_⟩
  · exact heq.mono fun i hi => by simp only [hi]
  · exact heq.mono fun i hi => by simp only [hi]

/-- An ordinary polynomial upper bound at positive heights supplies an admissible
growth exponent. Conjugation then covers negative heights as well. -/
theorem isZetaGrowthBound_of_isBigO {σ b : ℝ}
    (h : (fun t : ℝ => zetaAt σ t) =O[atTop] (fun t => t ^ b)) :
    IsZetaGrowthBound σ b := by
  apply isZetaGrowthBound_iff_positive_height.mpr
  intro ε hε
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨R, hR⟩ := eventually_atTop.mp hC
  let D := max (max C 1) R
  have hD1 : 1 ≤ D := (le_max_right C 1).trans (le_max_left _ _)
  refine ⟨D, zero_lt_one.trans_le hD1, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := hD1.trans ht
  have hb := hR t ((le_max_right _ _).trans ht)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans ht1) _)] at hb
  calc
    ‖zetaAt σ t‖ ≤ C * t ^ b := hb
    _ ≤ D * t ^ b := mul_le_mul_of_nonneg_right
      ((le_max_left C 1).trans (le_max_left _ _))
      (Real.rpow_nonneg (zero_le_one.trans ht1) _)
    _ ≤ D * t ^ (b + ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (zero_le_one.trans hD1)

/-- A polynomial lower bound along just one unbounded height sequence bounds every
candidate exponent from below. -/
theorem IsZetaGrowthBound.exponent_ge_of_lower_bound {σ b a c : ℝ}
    (h : IsZetaGrowthBound σ b) (t : VariableObject ℝ)
    (ht : ∀ i, 1 ≤ |t i|) (htop : t.IsUnbounded) (hc : 0 < c)
    (hlower : ∀ᶠ i in atTop, c * |t i| ^ a ≤ ‖zetaAt σ (t i)‖) : a ≤ b := by
  have habstop : VariableObject.IsUnbounded (fun i => |t i|) := by
    simpa [VariableObject.IsUnbounded, Real.norm_eq_abs] using htop
  exact exponent_le_of_isPowerBounded_of_eventually_norm_ge_rpow ht habstop
    (h.isPowerBounded t htop) hc hlower

end Expdb
