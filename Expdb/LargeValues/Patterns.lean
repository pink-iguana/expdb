module

public import Expdb.Basic.Definitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite large value patterns

Finite objects from `large-pattern-def`. The scale `N` remains real; only the summation
indices are natural numbers. Both coefficient and observation intervals are closed.
-/

@[expose] public section

noncomputable section

namespace Expdb

/-- The natural-number interval from `⌈N⌉₊` to `⌊2 * N⌋₊`. For `N ≥ 0`, these are
exactly the natural numbers in the real interval `[N, 2N]`. -/
def dyadicIndices (N : ℝ) : Finset ℕ := Finset.Icc ⌈N⌉₊ ⌊2 * N⌋₊

@[simp] theorem mem_dyadicIndices {N : ℝ} (hN : 0 ≤ N) {n : ℕ} :
    n ∈ dyadicIndices N ↔ N ≤ n ∧ (n : ℝ) ≤ 2 * N := by
  have h2N : 0 ≤ 2 * N := by positivity
  simp only [dyadicIndices, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff h2N]

/-- The Dirichlet polynomial `∑ n ∈ dyadicIndices N, a n * n^(-it)`. -/
def dirichletPolynomial (N : ℝ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ dyadicIndices N, a n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)

/-- A large value pattern from `large-pattern-def`: `N > 1`, `T, V > 0`, the coefficients
are bounded by one on `[N, 2N]`, and `W` is a finite one-separated subset of `[u, u + T]`
where the Dirichlet polynomial has norm at least `V`. -/
def IsLargeValuePattern (N T V : ℝ) (a : ℕ → ℂ) (u : ℝ) (W : Finset ℝ) : Prop :=
  1 < N ∧ 0 < T ∧ 0 < V ∧
    (∀ n ∈ dyadicIndices N, ‖a n‖ ≤ 1) ∧
    (∀ t ∈ W, t ∈ Set.Icc u (u + T)) ∧
    IsOneSeparated W ∧
    ∀ t ∈ W, V ≤ ‖dirichletPolynomial N a t‖

/-- A zeta large value pattern from `large-pattern-def`: a large value pattern with
`u = T` and coefficients equal on `[N, 2N]` to the indicator of a closed subinterval.
The coefficient interval may be empty. -/
def IsZetaLargeValuePattern (N T V : ℝ) (a : ℕ → ℂ) (u : ℝ)
    (W : Finset ℝ) : Prop :=
  IsLargeValuePattern N T V a u W ∧ u = T ∧
    ∃ l r : ℝ, Set.Icc l r ⊆ Set.Icc N (2 * N) ∧
      ∀ n ∈ dyadicIndices N, a n = Set.indicator (Set.Icc l r) (fun _ : ℝ => (1 : ℂ)) n

/-- Every zeta pattern is a general large value pattern. -/
theorem IsZetaLargeValuePattern.toIsLargeValuePattern
    {N T V u : ℝ} {a : ℕ → ℂ} {W : Finset ℝ}
    (h : IsZetaLargeValuePattern N T V a u W) :
    IsLargeValuePattern N T V a u W := h.1

/-- The polynomial only depends on coefficients in the summation interval. -/
theorem dirichletPolynomial_congr {N : ℝ} {a b : ℕ → ℂ}
    (h : ∀ n ∈ dyadicIndices N, a n = b n) (t : ℝ) :
    dirichletPolynomial N a t = dirichletPolynomial N b t := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [h n hn]

/-- Changing unused coefficients does not change whether a tuple is a pattern. -/
theorem isLargeValuePattern_congr {N T V u : ℝ} {a b : ℕ → ℂ} {W : Finset ℝ}
    (h : ∀ n ∈ dyadicIndices N, a n = b n) :
    IsLargeValuePattern N T V a u W ↔ IsLargeValuePattern N T V b u W := by
  unfold IsLargeValuePattern
  simp_rw [dirichletPolynomial_congr h]
  have hc : (∀ n ∈ dyadicIndices N, ‖a n‖ ≤ 1) ↔
      (∀ n ∈ dyadicIndices N, ‖b n‖ ≤ 1) := by
    constructor <;> intro hb n hn <;> simpa [h n hn] using hb n hn
  rw [hc]

@[simp] theorem isOneSeparated_empty : IsOneSeparated (∅ : Finset ℝ) := by
  intro i j hij
  exact False.elim (Finset.notMem_empty _ i.property)

/-- An empty observation set satisfies every observation condition. -/
@[simp] theorem isLargeValuePattern_empty {N T V u : ℝ} {a : ℕ → ℂ} :
    IsLargeValuePattern N T V a u ∅ ↔
      1 < N ∧ 0 < T ∧ 0 < V ∧ ∀ n ∈ dyadicIndices N, ‖a n‖ ≤ 1 := by
  simp [IsLargeValuePattern]

/-- Zeta patterns, too, only depend on coefficients in the dyadic summation interval. -/
theorem isZetaLargeValuePattern_congr {N T V u : ℝ} {a b : ℕ → ℂ} {W : Finset ℝ}
    (h : ∀ n ∈ dyadicIndices N, a n = b n) :
    IsZetaLargeValuePattern N T V a u W ↔ IsZetaLargeValuePattern N T V b u W := by
  unfold IsZetaLargeValuePattern
  rw [isLargeValuePattern_congr h]
  have hc : (∃ l r : ℝ, Set.Icc l r ⊆ Set.Icc N (2 * N) ∧
      ∀ n ∈ dyadicIndices N, a n = Set.indicator (Set.Icc l r) (fun _ : ℝ => (1 : ℂ)) n) ↔
      (∃ l r : ℝ, Set.Icc l r ⊆ Set.Icc N (2 * N) ∧
      ∀ n ∈ dyadicIndices N, b n = Set.indicator (Set.Icc l r) (fun _ : ℝ => (1 : ℂ)) n) := by
    constructor
    · rintro ⟨l, r, hlr, ha⟩
      exact ⟨l, r, hlr, fun n hn => (h n hn).symm.trans (ha n hn)⟩
    · rintro ⟨l, r, hlr, hb⟩
      exact ⟨l, r, hlr, fun n hn => (h n hn).trans (hb n hn)⟩
  rw [hc]

/-- An empty coefficient interval and empty observation set give a zeta pattern. -/
theorem isZetaLargeValuePattern_zero_empty {N T V : ℝ}
    (hN : 1 < N) (hT : 0 < T) (hV : 0 < V) :
    IsZetaLargeValuePattern N T V (fun _ => 0) T ∅ := by
  refine ⟨isLargeValuePattern_empty.mpr ⟨hN, hT, hV, by simp⟩, rfl, 1, 0, ?_, ?_⟩
  · simp
  · simp

/-- A one-separated finite set in a closed interval of length `T` has at most `T+1` points. -/
theorem card_le_length_add_one {W : Finset ℝ} {u T : ℝ}
    (hT : 0 ≤ T) (hW : ∀ t ∈ W, t ∈ Set.Icc u (u + T))
    (hsep : IsOneSeparated W) : (W.card : ℝ) ≤ T + 1 := by
  classical
  let f : ℝ → ℕ := fun t => ⌊t - u⌋₊
  have hmem : ∀ t ∈ W, f t ∈ Finset.range (⌊T⌋₊ + 1) := by
    intro t ht
    have ht' := hW t ht
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_mono (by linarith [ht'.2])
  have hinj : Set.InjOn f (↑W : Set ℝ) := by
    intro x hx y hy heq
    by_contra hne
    have hdist : 1 ≤ dist x y := hsep (i := ⟨x, hx⟩) (j := ⟨y, hy⟩)
      (by intro h; exact hne (congrArg Subtype.val h))
    have hx' := hW x hx
    have hy' := hW y hy
    have hxf := Nat.floor_le (show 0 ≤ x - u by linarith [hx'.1])
    have hyf := Nat.floor_le (show 0 ≤ y - u by linarith [hy'.1])
    have hxl := Nat.lt_floor_add_one (x - u)
    have hyl := Nat.lt_floor_add_one (y - u)
    have heq' : (⌊x - u⌋₊ : ℝ) = (⌊y - u⌋₊ : ℝ) := congrArg Nat.cast heq
    rw [Real.dist_eq] at hdist
    have habs : |x - y| < 1 := by rw [abs_lt]; constructor <;> linarith
    exact (not_lt_of_ge hdist) habs
  have hcard := Finset.card_le_card_of_injOn f hmem hinj
  have hcard' : (W.card : ℝ) ≤ (⌊T⌋₊ : ℝ) + 1 := by
    exact_mod_cast (by simpa using hcard : W.card ≤ ⌊T⌋₊ + 1)
  exact hcard'.trans (by linarith [Nat.floor_le hT])

end Expdb
