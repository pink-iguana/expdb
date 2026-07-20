import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Sequences

/-!
# ANTEDB Blueprint — Chapter 2: Basic notation

This file defines the project-specific notions used in Chapter 2. When a blueprint convention
already has a standard Mathlib representation, prefer using that representation directly:
-the notation `e(θ)` is `𝐞 θ` after `open scoped FourierTransform`; it is coerced from
  `Circle` to `ℂ` when the surrounding expression requires a complex number;
-indicator functions are written using `Set.indicator`;
-suprema and infima, including those of empty sets, use Mathlib's `sSup` and `sInf`;
-finite cardinalities use `Finset.card`;
-standard asymptotic relations use Mathlib's `Asymptotics` API.

The blueprint also uses non-standard objects indexed by some ambient
parameter. Their asymptotic properties can be expressed using Mathlib's filter API:
-a bounded variable `X` satisfies
 `∃ C : ℝ, ∀ᶠ i in atTop, ‖X i‖ ≤ C`;
-an unbounded variable `X` satisfies
 `Tendsto (fun i => ‖X i‖) atTop atTop`;
-an infinitesimal variable `X` satisfies
 `Tendsto X atTop (nhds 0)`.

If these conditions recur sufficiently often in later chapters, they may be given the
project-specific names `IsBoundedVariable`, `IsUnboundedVariable`, and
`IsInfinitesimalVariable`.

New declarations are introduced here only when the notion used by the blueprint is genuinely
project-specific or differs from the corresponding Mathlib notion.
-/

open Filter Topology Real

-- ===========================================================
--  Separated families and sets
-- ===========================================================

/-- A family in a pseudo-metric space is `δ`-separated when distinct indices have values at
least `δ` apart. This uses a non-strict inequality, unlike `Metric.IsSeparated`. -/
def IsSeparatedFamily {ι α : Type*} [PseudoMetricSpace α] (δ : ℝ) (x : ι → α) : Prop :=
  Pairwise fun i j => δ ≤ dist (x i) (x j)

/-- λ-Separated Sets: distance between distinct elements is at least λ -/
def IsLambdaSeparated {α : Type*} [PseudoMetricSpace α] (lam : ℝ) (W : Finset α) : Prop :=
  IsSeparatedFamily lam fun t : W => (t : α)

/-- 1-Separated Sets: distance between distinct elements is at least 1. -/
abbrev IsOneSeparated {α : Type*} [PseudoMetricSpace α] (W : Finset α) : Prop :=
  IsLambdaSeparated 1 W

-- ===========================================================
-- Bounded families
-- ===========================================================

/-- A family in a normed type is `C`-bounded when every value has norm at most `C`. -/
def IsBoundedFamily {ι β : Type*} [Norm β] (C : ℝ) (a : ι → β) : Prop :=
  ∀ i, ‖a i‖ ≤ C

/-- A family in a normed type is 1-bounded. -/
abbrev IsOneBounded {ι β : Type*} [Norm β] (a : ι → β) : Prop :=
  IsBoundedFamily 1 a

-- ===========================================================
-- Asymptotic Notation
-- ===========================================================

/-- The one-sided asymptotic relation `X ≤ Y + o(1)` from the blueprint.

It holds when there is a real error sequence tending to zero such that
`X i ≤ Y i + err i` eventually. Equivalently, for every fixed `δ > 0`, one eventually has
`X i ≤ Y i + δ`.

This does not assert that `X - Y` tends to zero; it only requires the positive part of `X - Y`
to tend to zero. -/
def EventuallyLeUpToInfinitesimal (X Y : ℕ → ℝ) : Prop :=
  ∃ err : ℕ → ℝ, Tendsto err atTop (nhds 0) ∧
    ∀ᶠ i in atTop, X i ≤ Y i + err i

/-- `X ≤o Y` denotes the complete blueprint expression `X ≤ Y + o(1)`; it is not the
little-o relation `X = o(Y)`. -/
notation X " ≤o " Y => EventuallyLeUpToInfinitesimal X Y

/-- The relation `X ≤ Y + o(1)` is equivalent to `X i ≤ Y i + δ` eventually for every fixed
positive `δ`. -/
theorem eventuallyLeUpToInfinitesimal_iff_forall_pos (X Y : ℕ → ℝ) :
    (X ≤o Y) ↔
    ∀ δ : ℝ, 0 < δ → ∀ᶠ i in atTop, X i ≤ Y i + δ := by
  constructor
  · rintro ⟨err, herr, hXY⟩ δ hδ
    rw [Metric.tendsto_nhds] at herr
    have herr_small := herr δ hδ
    filter_upwards [hXY, herr_small] with i hi hierr
    rw [Real.dist_eq, sub_zero] at hierr
    have herr_lt : err i < δ := lt_of_le_of_lt (le_abs_self _) hierr
    linarith
  · intro h
    refine ⟨fun i => max (X i - Y i) 0, ?_, Filter.Eventually.of_forall fun i => ?_⟩
    · rw [Metric.tendsto_nhds]
      intro δ hδ
      have hδ2 : 0 < δ / 2 := by linarith
      filter_upwards [h (δ / 2) hδ2] with i hi
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_right _ _)]
      exact max_lt (by linarith) hδ
    · have hi : X i - Y i ≤ max (X i - Y i) 0 := le_max_left _ _
      linarith

-- ============================================================
--  Auxiliary lemmas for subsequence extraction
-- ============================================================

/-- From a property holding arbitrarily late, extract a strictly
    increasing sequence on which it holds. -/
private lemma extract_strictMono_subseq {P : ℕ → Prop}
    (h : ∀ j, ∃ i ≥ j, P i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) := by
  have step : ∀ prev, ∃ i > prev, P i :=
    fun prev => let ⟨i, hi, hP⟩ := h (prev + 1); ⟨i, by omega, hP⟩
  let φ : ℕ → ℕ :=
    fun n => n.rec (h 0).choose (fun _ prev => (step prev).choose)
  exact ⟨φ, strictMono_nat_of_lt_succ fun n => (step (φ n)).choose_spec.1,
         fun n => n.casesOn (h 0).choose_spec.2
                             (fun _ => (step (φ _)).choose_spec.2)⟩

/-- Extract a strictly increasing φ and bad elements x(n) ∈ E(φ n)
    with |f(φ n)(x n)| > n.  Used in the proof of Proposition 2.1(i). -/
private lemma extract_bad_seq_i
    (E : ℕ → Set ℝ) (f : ∀ i, E i → ℂ)
    (bad : ∀ j, ∃ i ≥ j, ∃ x : E i, (j : ℝ) < ‖f i x‖):
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ x : ∀ n, E (φ n), ∀ n, n < ‖f (φ n) (x n)‖ := by
  have step : ∀ (n prev : ℕ), ∃ i > prev, ∃ x : E i, (n : ℝ) < ‖f i x‖ :=
    fun n prev => by
      obtain ⟨i, hi, x, hx⟩ := bad (max (prev + 1) n)
      exact ⟨i, by have := le_max_left (prev+1) n; omega,
             x, lt_of_le_of_lt (by exact_mod_cast le_max_right (prev+1) n) hx⟩
  let data : ℕ → Σ i, E i :=
    fun n => n.rec ⟨(step 0 0).choose, (step 0 0).choose_spec.2.choose⟩
      fun n p => ⟨(step (n+1) p.1).choose, (step (n+1) p.1).choose_spec.2.choose⟩
  exact ⟨fun n => (data n).1,
         strictMono_nat_of_lt_succ fun n => (step (n+1) (data n).1).choose_spec.1,
         fun n => (data n).2,
         fun n => n.casesOn (step 0 0).choose_spec.2.choose_spec
                             (fun _ => (step _ _).choose_spec.2.choose_spec)⟩

/-- For a fixed threshold ε, extract a strictly increasing φ and bad elements
    x(n) ∈ E(φ n) with |f(φ n)(x n)| > ε. Used in Proposition 2.1(ii). -/
private lemma extract_bad_seq_ii
    (E : ℕ → Set ℝ) (f : ∀ i, E i → ℂ)
    {ε : ℝ}
    (bad : ∀ j, ∃ i ≥ j, ∃ x : E i, ε < ‖f i x‖) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ x : ∀ n, E (φ n), ∀ n, ε < ‖f (φ n) (x n)‖ := by
  obtain ⟨φ, hφ, hbad⟩ := extract_strictMono_subseq
    (P := fun i => ∃ x : E i, ε < ‖f i x‖) bad
  choose x hx using hbad
  exact ⟨φ, hφ, x, hx⟩

/-- Build a strictly increasing threshold sequence φ such that
    |f(φ n)(x)| ≤ 1/(n+1) for all x ∈ E(φ n). -/
private lemma build_increasing_thresholds
    (E : ℕ → Set ℝ) (f : ∀ i, E i → ℂ)
    (scale : ∀ n : ℕ, 0 < n → ∃ i_n, ∀ i ≥ i_n, ∀ x : E i,
             ‖f i x‖ ≤ 1/n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∀ n, ∀ x : E (φ n), ‖f (φ n) x‖ ≤ 1/(n+1) := by
  choose i_seq hi_seq using fun n => scale (n+1) (Nat.succ_pos n)
  let φ : ℕ → ℕ :=
    fun n => n.rec (i_seq 0) (fun k p => max (i_seq (k+1)) (p+1))
  refine ⟨φ, strictMono_nat_of_lt_succ fun n =>
           Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _),
         fun n x => ?_⟩
  have hge : φ n ≥ i_seq n := by
    cases n with
    | zero => exact le_refl _
    | succ n => exact le_max_left _ _
  have hb := hi_seq n (φ n) hge x
  rwa [Nat.cast_add, Nat.cast_one] at hb

-- ===========================================================
-- Underspill Principle
-- ===========================================================

/-- **Underspill principle.** The relation `X ≤ Y + o(1)` holds if and only if
`X ≤ Y + ε + o(1)` for every fixed `ε > 0`. -/
theorem underspill (X Y : ℕ → ℝ) :
    (X ≤o Y) ↔
    (∀ ε : ℝ, ε > 0 → X ≤o (fun i => Y i + ε)) := by
  constructor
  · intro h ε hε
    apply (eventuallyLeUpToInfinitesimal_iff_forall_pos X (fun i => Y i + ε)).2
    intro δ hδ
    filter_upwards [(eventuallyLeUpToInfinitesimal_iff_forall_pos X Y).1 h δ hδ] with i hi
    linarith
  · intro h
    apply (eventuallyLeUpToInfinitesimal_iff_forall_pos X Y).2
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have hbound := (eventuallyLeUpToInfinitesimal_iff_forall_pos
      X (fun i => Y i + ε / 2)).1 (h (ε / 2) hε2) (ε / 2) hε2
    filter_upwards [hbound] with i hi
    linarith

-- ============================================================
-- Pointwise-bounded and pointwise-infinitesimal functions
-- ============================================================

/-- f is pointwise O(1): for every variable sequence (x_i) ∈ E_i,
    the values (f_i(x_i)) are eventually bounded. -/
def IsPointwiseBounded (E : ℕ → Set ℝ) (f : ∀ i, E i → ℂ) : Prop :=
  ∀ x : ∀ i, E i, ∃ C : ℝ, ∀ᶠ i in atTop, ‖f i (x i)‖ ≤ C

/-- f is pointwise o(1): for every variable sequence (x_i) ∈ E_i,
    the values (f_i(x_i)) tend to 0. -/
def IsPointwiseInfinitesimal (E : ℕ → Set ℝ) (f : ∀ i, E i → ℂ) : Prop :=
  ∀ x : ∀ i, E i, Tendsto (fun i => ‖f i (x i)‖) atTop (nhds 0)

-- ============================================================
-- Proposition 2.1 — Automatic uniformity
-- ============================================================

private noncomputable def extend_subsequence
    (E : ℕ → Set ℝ) (hE : ∀ i, (E i).Nonempty)
    (φ : ℕ → ℕ) (x : ∀ n, E (φ n)) : ∀ j, E j := by
  classical
  exact fun j =>
    if h : ∃ n, φ n = j then
      (show E (φ h.choose) = E j by rw [h.choose_spec]) ▸ x h.choose
    else ⟨(hE j).choose, (hE j).choose_spec⟩

open Classical in
private lemma norm_extend_subsequence_apply
    {E : ℕ → Set ℝ} (hE : ∀ i, (E i).Nonempty)
    {f : ∀ i, E i → ℂ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (x : ∀ n, E (φ n)) (m : ℕ) :
    ‖f (φ m) (extend_subsequence E hE φ x (φ m))‖ = ‖f (φ m) (x m)‖ := by
  simp only [extend_subsequence]
  split_ifs with h
  · have hm : h.choose = m := hφ.injective h.choose_spec
    have hx : x h.choose ≍ x m := by rw [hm]
    apply congrArg
    apply congrArg
    apply eq_of_heq
    exact rec_heq_of_heq _ hx
  · exact absurd ⟨m, rfl⟩ h

/-- **Proposition 2.1(i) — Automatic uniform bound.**
    If f(x) = O(1) for every variable x ∈ E, then after passing to a
    subsequence there exists a *fixed* C with |f(x)| ≤ C for all x ∈ E. -/
theorem automatic_uniformity_i
    (E : ℕ → Set ℝ) (hE : ∀ i, (E i).Nonempty)
    (f : ∀ i, E i → ℂ)
    (hf : IsPointwiseBounded E f) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ C : ℝ, ∀ i, ∀ x : E (φ i),
    ‖f (φ i) x‖ ≤ C := by
  have h_eventual :
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x : E (φ i), ‖f (φ i) x‖ ≤ C := by
    by_contra h_fail
    push_neg at h_fail
    -- Build a bad sequence: for each j find i ≥ j and x with |f i x| > j
    have bad : ∀ j, ∃ i ≥ j, ∃ x : E i, (j:ℝ) < ‖f i x‖ := fun j => by
      rcases Filter.frequently_atTop.mp (h_fail id strictMono_id j) j with ⟨i, hi, x, hx⟩
      exact ⟨i, hi, x, hx⟩
    obtain ⟨φ, hφ, x_bad, hx_bad⟩ := extract_bad_seq_i E f bad
    let y : ∀ j, E j := extend_subsequence E hE φ x_bad
    -- Apply pointwise bound to y
    obtain ⟨C_y, hC_y⟩ := hf y
    rw [Filter.eventually_atTop] at hC_y
    obtain ⟨j₀, hj₀⟩ := hC_y
    obtain ⟨n₁, hn₁⟩ := exists_nat_gt C_y
    -- Find m with φ(m) ≥ j₀ and m > n₁
    obtain ⟨m, hm_ge, hm_large⟩ : ∃ m, φ m ≥ j₀ ∧ m > n₁ := by
      obtain ⟨m, hm⟩ := (hφ.tendsto_atTop).eventually (eventually_ge_atTop j₀) |>.exists
      exact ⟨max m (n₁+1), le_trans hm (hφ.monotone (le_max_left _ _)), by omega⟩
    -- Derive contradiction
    have heq := norm_extend_subsequence_apply hE (f := f) hφ x_bad m
    linarith [hj₀ (φ m) hm_ge,
              hx_bad m,
              show C_y < (m:ℝ) from
              lt_trans hn₁ (by exact_mod_cast hm_large),
              heq ▸ hj₀ (φ m) hm_ge]
  obtain ⟨φ, hφ, C, hC⟩ := h_eventual
  rw [Filter.eventually_atTop] at hC
  obtain ⟨N, hN⟩ := hC
  refine ⟨fun n => φ (n + N), ?_, C, ?_⟩
  · intro m n hmn
    exact hφ (Nat.add_lt_add_right hmn N)
  · intro n x
    exact hN (n + N) (by omega) x

/-- **Proposition 2.1(ii) — Automatic uniform infinitesimal.**
    If f(x) = o(1) for every variable x ∈ E, then after passing to a
    subsequence there exists an *infinitesimal* c with |f(x)| ≤ c for all x ∈ E. -/
theorem automatic_uniformity_ii
    (E : ℕ → Set ℝ) (hE : ∀ i, (E i).Nonempty)
    (f : ∀ i, E i → ℂ)
    (hf : IsPointwiseInfinitesimal E f) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ c : ℕ → ℝ, Tendsto c atTop (nhds 0) ∧
    ∀ i, ∀ x : E (φ i),
    ‖f (φ i) x‖ ≤ c i := by
  -- Step 1: for each n ≥ 1, the bound 1/n eventually holds uniformly
  have scale : ∀ n : ℕ, 0 < n → ∃ i_n, ∀ i ≥ i_n, ∀ x : E i,
      ‖f i x‖ ≤ 1/n := by
    intro n hn
    by_contra h_fail; push_neg at h_fail
    have bad : ∀ j, ∃ i ≥ j, ∃ x : E i, (1:ℝ)/n < ‖f i x‖ :=
      fun j => by obtain ⟨i, hi, x, hx⟩ := h_fail j; exact ⟨i, hi, x, hx⟩
    obtain ⟨φ, hφ, x_bad, hx_bad⟩ :=
      extract_bad_seq_ii E f bad
    let y : ∀ j, E j := extend_subsequence E hE φ x_bad
    have hfy := hf y
    rw [Metric.tendsto_atTop] at hfy
    obtain ⟨N₀, hN₀⟩ := hfy (1/(2*n)) (by positivity)
    obtain ⟨m, hm⟩ := (hφ.tendsto_atTop).eventually (eventually_ge_atTop N₀) |>.exists
    have heq := norm_extend_subsequence_apply hE (f := f) hφ x_bad m
    have h1 : ‖f (φ m) (y (φ m))‖ < 1/(2*n) := by
      have := hN₀ (φ m) hm
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    linarith [hx_bad m, heq ▸ h1,
              show (1:ℝ)/(2*n) < 1/n by
                have hn : (0 : ℝ) < n := by positivity
                exact one_div_lt_one_div_of_lt hn (by nlinarith)]
  -- Step 2: build strictly increasing thresholds and conclude
  obtain ⟨φ, hφ, hφ_bd⟩ := build_increasing_thresholds E f scale
  refine ⟨φ, hφ, fun n => 1/(↑n+1), ?_, hφ_bd⟩
  exact tendsto_one_div_add_atTop_nhds_zero_nat
