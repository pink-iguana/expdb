module

import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Derivative bounds and convergence along sequences

`SeqClose` records convergence of the difference of two real sequences and eventual boundedness
of the comparison sequence. `DerivativesClose` applies this relation to derivatives through a
specified order at varying points; `PositiveDerivativesClose` omits the function values.

The product, composition, square-root and inverse rules propagate these bounds and convergence.
They are used by the dual phase construction and the stationary-phase amplitude estimates.
-/

@[expose] public section

namespace Expdb

open Filter Topology
open scoped ContDiff

noncomputable section

/-! ## Close sequences -/

/-- The real sequence `u` is asymptotically equal to the eventually bounded sequence `v`. -/
def SeqClose (u v : ℕ → ℝ) : Prop :=
  Tendsto (fun i ↦ u i - v i) atTop (𝓝 0) ∧
    IsBoundedUnder (· ≤ ·) atTop (fun i ↦ ‖v i‖)

namespace SeqClose

variable {u v u₁ v₁ u₂ v₂ : ℕ → ℝ}

theorem bdd_left (h : SeqClose u v) : IsBoundedUnder (· ≤ ·) atTop (fun i ↦ ‖u i‖) := by
  apply (Asymptotics.isBigO_one_iff ℝ).1
  have hdiff := ((Asymptotics.isLittleO_one_iff ℝ).2 h.1).isBigO
  exact (hdiff.add ((Asymptotics.isBigO_one_iff ℝ).2 h.2)).congr_left fun i ↦ sub_add_cancel _ _

theorem symm (h : SeqClose u v) : SeqClose v u :=
  ⟨by simpa using h.1.neg, h.bdd_left⟩

theorem trans (h₁ : SeqClose u v) (h₂ : SeqClose v u₁) : SeqClose u u₁ :=
  ⟨by simpa using h₁.1.add h₂.1, h₂.2⟩

theorem const (c : ℝ) : SeqClose (fun _ ↦ c) (fun _ ↦ c) :=
  ⟨by simp,
    isBoundedUnder_const⟩

theorem of_bound {C : ℝ} (hb : ∀ᶠ i in atTop, ‖u i‖ ≤ C) : SeqClose u u :=
  ⟨by simp,
    ⟨C, by simpa using hb⟩⟩

theorem exists_bound (h : SeqClose u v) : ∃ C, ∀ᶠ i in atTop, ‖u i‖ ≤ C := by
  obtain ⟨C, hC⟩ := h.bdd_left
  exact ⟨C, by simpa using hC⟩

theorem congr_left {w : ℕ → ℝ} (h : SeqClose u v) (he : ∀ᶠ i in atTop, u i = w i) :
    SeqClose w v := by
  refine ⟨h.1.congr' ?_, h.2⟩
  filter_upwards [he] with i hi
  rw [hi]

theorem congr_right {w : ℕ → ℝ} (h : SeqClose u v) (he : ∀ᶠ i in atTop, v i = w i) :
    SeqClose u w := by
  refine ⟨h.1.congr' ?_, ?_⟩
  · filter_upwards [he] with i hi
    rw [hi]
  · obtain ⟨C, hC⟩ := h.2
    refine ⟨C, ?_⟩
    simp only [eventually_map] at hC ⊢
    filter_upwards [hC, he] with i h1 h2
    rwa [← h2]

theorem add (h₁ : SeqClose u₁ v₁) (h₂ : SeqClose u₂ v₂) :
    SeqClose (fun i ↦ u₁ i + u₂ i) (fun i ↦ v₁ i + v₂ i) := by
  refine ⟨?_, ?_⟩
  · have := h₁.1.add h₂.1
    simp only [add_zero] at this
    refine this.congr fun i ↦ ?_
    ring
  · exact (Asymptotics.isBigO_one_iff ℝ).1 (((Asymptotics.isBigO_one_iff ℝ).2 h₁.2).add
    ((Asymptotics.isBigO_one_iff ℝ).2 h₂.2))

theorem neg (h : SeqClose u v) : SeqClose (fun i ↦ -u i) (fun i ↦ -v i) := by
  refine ⟨?_, ?_⟩
  · have := h.1.neg
    simp only [neg_zero] at this
    refine this.congr fun i ↦ ?_
    ring
  · simpa using h.2

theorem sub (h₁ : SeqClose u₁ v₁) (h₂ : SeqClose u₂ v₂) :
    SeqClose (fun i ↦ u₁ i - u₂ i) (fun i ↦ v₁ i - v₂ i) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

theorem mul (h₁ : SeqClose u₁ v₁) (h₂ : SeqClose u₂ v₂) :
    SeqClose (fun i ↦ u₁ i * u₂ i) (fun i ↦ v₁ i * v₂ i) := by
  refine ⟨?_, ?_⟩
  · have ha := h₁.1.zero_mul_isBoundedUnder_le h₂.bdd_left
    have hb := h₂.1.zero_mul_isBoundedUnder_le h₁.2
    have := ha.add hb
    simp only [add_zero] at this
    refine this.congr fun i ↦ ?_
    ring
  · apply (Asymptotics.isBigO_one_iff ℝ).1
    simpa only [one_mul] using ((Asymptotics.isBigO_one_iff ℝ).2 h₁.2).mul
      ((Asymptotics.isBigO_one_iff ℝ).2 h₂.2)

theorem const_mul (c : ℝ) (h : SeqClose u v) :
    SeqClose (fun i ↦ c * u i) (fun i ↦ c * v i) :=
  (const c).mul h

theorem sum {ι : Type*} (s : Finset ι) {U V : ι → ℕ → ℝ}
    (h : ∀ k ∈ s, SeqClose (U k) (V k)) :
    SeqClose (fun i ↦ ∑ k ∈ s, U k i) (fun i ↦ ∑ k ∈ s, V k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun k hk ↦ h k (Finset.mem_insert_of_mem hk))

/-- Reciprocals of sequences bounded away from zero are close. -/
theorem inv (h : SeqClose u v) {c : ℝ} (hc : 0 < c) (hv : ∀ᶠ i in atTop, c ≤ ‖v i‖) :
    SeqClose (fun i ↦ (u i)⁻¹) (fun i ↦ (v i)⁻¹) := by
  have hu : ∀ᶠ i in atTop, c / 2 ≤ ‖u i‖ := by
    have hsmall : ∀ᶠ i in atTop, ‖u i - v i‖ ≤ c / 2 :=
      h.1.norm.eventually (Iic_mem_nhds (by simpa using half_pos hc))
    filter_upwards [hsmall, hv] with i h1 h2
    have : ‖v i‖ ≤ ‖u i‖ + ‖u i - v i‖ := by
      calc ‖v i‖ = ‖u i - (u i - v i)‖ := by ring_nf
        _ ≤ ‖u i‖ + ‖u i - v i‖ := norm_sub_le _ _
    linarith
  have hvinv : IsBoundedUnder (· ≤ ·) atTop (fun i ↦ ‖(v i)⁻¹‖) := by
    refine ⟨c⁻¹, ?_⟩
    simp only [eventually_map]
    filter_upwards [hv] with i hi
    rw [norm_inv]
    exact inv_anti₀ hc hi
  have huinv : IsBoundedUnder (· ≤ ·) atTop (fun i ↦ ‖(u i)⁻¹‖) := by
    refine ⟨(c / 2)⁻¹, ?_⟩
    simp only [eventually_map]
    filter_upwards [hu] with i hi
    rw [norm_inv]
    exact inv_anti₀ (half_pos hc) hi
  refine ⟨?_, hvinv⟩
  have hprod : IsBoundedUnder (· ≤ ·) atTop (fun i ↦ ‖(u i)⁻¹ * (v i)⁻¹‖) := by
    apply (Asymptotics.isBigO_one_iff ℝ).1
    simpa only [one_mul] using ((Asymptotics.isBigO_one_iff ℝ).2 huinv).mul
      ((Asymptotics.isBigO_one_iff ℝ).2 hvinv)
  have hneg : Tendsto (fun i ↦ -(u i - v i)) atTop (𝓝 0) := by simpa using h.1.neg
  have := hneg.zero_mul_isBoundedUnder_le hprod
  refine this.congr' ?_
  filter_upwards [hu, hv] with i h1 h2
  have hu0 : u i ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (half_pos hc) h1)
  have hv0 : v i ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hc h2)
  field_simp
  ring

end SeqClose

/-! ## Derivative bounds and convergence -/

/-- Derivative differences tend to zero through order `n` at two sequences of points,
and the comparison derivatives are eventually bounded. -/
def DerivativesClose (f g : ℕ → ℝ → ℝ) (x y : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ k ≤ n, SeqClose (fun i ↦ iteratedDeriv k (f i) (x i))
    (fun i ↦ iteratedDeriv k (g i) (y i))

/-- Derivative differences of orders `1` through `n` tend to zero at two sequences of points,
and the comparison derivatives are eventually bounded. -/
def PositiveDerivativesClose (f g : ℕ → ℝ → ℝ) (x y : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ n → SeqClose (fun i ↦ iteratedDeriv k (f i) (x i))
    (fun i ↦ iteratedDeriv k (g i) (y i))

theorem DerivativesClose.mono {f g : ℕ → ℝ → ℝ} {x y : ℕ → ℝ} {m n : ℕ}
    (h : DerivativesClose f g x y n) (hmn : m ≤ n) : DerivativesClose f g x y m :=
  fun k hk ↦ h k (hk.trans hmn)

theorem DerivativesClose.positiveDerivativesClose {f g : ℕ → ℝ → ℝ} {x y : ℕ → ℝ} {n : ℕ}
    (h : DerivativesClose f g x y n) : PositiveDerivativesClose f g x y n :=
  fun k _ hk ↦ h k hk

theorem PositiveDerivativesClose.mono {f g : ℕ → ℝ → ℝ} {x y : ℕ → ℝ} {m n : ℕ}
    (h : PositiveDerivativesClose f g x y n) (hmn : m ≤ n) : PositiveDerivativesClose f g x y m :=
  fun k hk1 hk ↦ h k hk1 (hk.trans hmn)

/-- Differentiation shifts the orders in `DerivativesClose`. -/
theorem DerivativesClose.shift {f g : ℕ → ℝ → ℝ} {x y : ℕ → ℝ} {n : ℕ}
    (h : DerivativesClose f g x y (n + 1)) :
    DerivativesClose (fun i ↦ deriv (f i)) (fun i ↦ deriv (g i)) x y n := by
  intro k hk
  simpa only [← iteratedDeriv_succ'] using h (k + 1) (by omega)

/-- Differentiation converts positive-order bounds and convergence to `DerivativesClose`. -/
theorem PositiveDerivativesClose.shift {f g : ℕ → ℝ → ℝ} {x y : ℕ → ℝ} {n : ℕ}
    (h : PositiveDerivativesClose f g x y (n + 1)) :
    DerivativesClose (fun i ↦ deriv (f i)) (fun i ↦ deriv (g i)) x y n := by
  intro k hk
  simpa only [← iteratedDeriv_succ'] using h (k + 1) (by omega) (by omega)

/-- Combine convergence and boundedness of the values with those of the derivatives. -/
theorem DerivativesClose.unshift {f g : ℕ → ℝ → ℝ} {x y : ℕ → ℝ} {n : ℕ}
    (h0 : SeqClose (fun i ↦ f i (x i)) (fun i ↦ g i (y i)))
    (h : DerivativesClose (fun i ↦ deriv (f i)) (fun i ↦ deriv (g i)) x y n) :
    DerivativesClose f g x y (n + 1) := by
  intro k hk
  rcases k with _ | k
  · simpa using h0
  · simpa only [iteratedDeriv_succ'] using h k (by omega)

/-- Products preserve derivative bounds and convergence. -/
theorem DerivativesClose.mul {f g f' g' : ℕ → ℝ → ℝ} {x y : ℕ → ℝ} {n : ℕ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hf' : ∀ i, ContDiff ℝ ∞ (f' i)) (hg' : ∀ i, ContDiff ℝ ∞ (g' i))
    (h₁ : DerivativesClose f f' x y n) (h₂ : DerivativesClose g g' x y n) :
    DerivativesClose (fun i z ↦ f i z * g i z) (fun i z ↦ f' i z * g' i z) x y n := by
  intro k hk
  simp only [iteratedDeriv_fun_mul ((hf _).contDiffAt.of_le (by exact_mod_cast le_top))
    ((hg _).contDiffAt.of_le (by exact_mod_cast le_top)), iteratedDeriv_fun_mul
    ((hf' _).contDiffAt.of_le (by exact_mod_cast le_top))
    ((hg' _).contDiffAt.of_le (by exact_mod_cast le_top))]
  apply SeqClose.sum
  intro m hm
  have hm' := Finset.mem_range.1 hm
  exact ((SeqClose.const _).mul (h₁ m (by omega))).mul (h₂ (k - m) (by omega))

/-- The derivative of a composition, differentiated `j` more times. -/
private theorem iteratedDeriv_succ_comp {g f : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (j : ℕ) (x : ℝ) :
    iteratedDeriv (j + 1) (g ∘ f) x =
      ∑ m ∈ Finset.range (j + 1), (j.choose m : ℝ) *
        iteratedDeriv m (deriv g ∘ f) x * iteratedDeriv (j - m + 1) f x := by
  have hd : deriv (g ∘ f) = fun y ↦ (deriv g ∘ f) y * deriv f y := by
    funext y
    exact deriv_comp y ((hg.differentiable (by simp)) _) ((hf.differentiable (by simp)) _)
  rw [iteratedDeriv_succ', hd,
    iteratedDeriv_fun_mul
      (((hg.deriv' (n := ∞)).comp hf).contDiffAt.of_le (by exact_mod_cast le_top))
      ((hf.deriv' (n := ∞)).contDiffAt.of_le (by exact_mod_cast le_top))]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [← iteratedDeriv_succ']

/-- The chain rule for derivative bounds and convergence. -/
theorem DerivativesClose.comp {n : ℕ} :
    ∀ {g g' f f' : ℕ → ℝ → ℝ} {x x' : ℕ → ℝ},
    (∀ i, ContDiff ℝ ∞ (g i)) → (∀ i, ContDiff ℝ ∞ (g' i)) →
    (∀ i, ContDiff ℝ ∞ (f i)) → (∀ i, ContDiff ℝ ∞ (f' i)) →
    DerivativesClose g g' (fun i ↦ f i (x i)) (fun i ↦ f' i (x' i)) n →
    PositiveDerivativesClose f f' x x' n →
    DerivativesClose (fun i ↦ g i ∘ f i) (fun i ↦ g' i ∘ f' i) x x' n := by
  induction n with
  | zero =>
    intro g g' f f' x x' _ _ _ _ hg _ k hk
    obtain rfl : k = 0 := by omega
    simpa using hg 0 le_rfl
  | succ n ih =>
    intro g g' f f' x x' hgs hg's hfs hf's hg hf k hk
    rcases k with _ | j
    · simpa using hg 0 (by omega)
    · have hIH := ih (g := fun i ↦ deriv (g i)) (g' := fun i ↦ deriv (g' i))
        (fun i ↦ (hgs i).deriv' (n := ∞)) (fun i ↦ (hg's i).deriv' (n := ∞))
        hfs hf's hg.shift (hf.mono (by omega))
      simp only [iteratedDeriv_succ_comp (hgs _) (hfs _),
        iteratedDeriv_succ_comp (hg's _) (hf's _)]
      apply SeqClose.sum
      intro m hm
      have hm' := Finset.mem_range.1 hm
      exact ((SeqClose.const _).mul (hIH m (by omega))).mul
        (hf (j - m + 1) (by omega) (by omega))

/-- If `u * a = b`, derivative bounds and convergence for `a` and `b` imply them for `u`,
provided `a` stays away from zero. -/
theorem DerivativesClose.of_mul_eq {u u' a a' b b' : ℕ → ℝ → ℝ} {x x' : ℕ → ℝ} {n : ℕ}
    (hu : ∀ i, ContDiff ℝ ∞ (u i)) (hu' : ∀ i, ContDiff ℝ ∞ (u' i))
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (ha' : ∀ i, ContDiff ℝ ∞ (a' i))
    (heq : ∀ i y, u i y * a i y = b i y) (heq' : ∀ i y, u' i y * a' i y = b' i y)
    (haj : DerivativesClose a a' x x' n) (hbj : DerivativesClose b b' x x' n)
    {c : ℝ} (hc : 0 < c) (hlow : ∀ᶠ i in atTop, c ≤ ‖a' i (x' i)‖) :
    DerivativesClose u u' x x' n := by
  have hclose : SeqClose (fun i ↦ a i (x i)) (fun i ↦ a' i (x' i)) := by
    simpa using haj 0 (Nat.zero_le _)
  have hainv : SeqClose (fun i ↦ (a i (x i))⁻¹) (fun i ↦ (a' i (x' i))⁻¹) :=
    hclose.inv hc hlow
  have ha0 : ∀ᶠ i in atTop, a i (x i) ≠ 0 ∧ a' i (x' i) ≠ 0 := by
    have hsmall : ∀ᶠ i in atTop, ‖a i (x i) - a' i (x' i)‖ ≤ c / 2 :=
      hclose.1.norm.eventually (Iic_mem_nhds (by simpa using half_pos hc))
    filter_upwards [hsmall, hlow] with i h1 h2
    constructor
    · intro h0
      rw [h0, zero_sub, norm_neg] at h1
      linarith
    · intro h0
      rw [h0, norm_zero] at h2
      linarith
  -- Solve the Leibniz identity for the top derivative of `u`.
  have hformula : ∀ (v A B : ℝ → ℝ), ContDiff ℝ ∞ v → ContDiff ℝ ∞ A →
      (∀ y, v y * A y = B y) → ∀ k z, A z ≠ 0 →
      iteratedDeriv k v z = (iteratedDeriv k B z -
        ∑ m ∈ Finset.range k, (k.choose m : ℝ) * iteratedDeriv m v z *
          iteratedDeriv (k - m) A z) * (A z)⁻¹ := by
    intro v A B hv hA hvAB k z hz
    have hB : B = fun y ↦ v y * A y := funext fun y ↦ (hvAB y).symm
    rw [hB, iteratedDeriv_fun_mul ((hv).contDiffAt.of_le (by exact_mod_cast le_top))
      ((hA).contDiffAt.of_le (by exact_mod_cast le_top)), Finset.sum_range_succ]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, iteratedDeriv_zero]
    field_simp
    ring
  have key : ∀ k ≤ n, SeqClose (fun i ↦ iteratedDeriv k (u i) (x i))
      (fun i ↦ iteratedDeriv k (u' i) (x' i)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have hsum : SeqClose
          (fun i ↦ ∑ m ∈ Finset.range k, (k.choose m : ℝ) * iteratedDeriv m (u i) (x i) *
            iteratedDeriv (k - m) (a i) (x i))
          (fun i ↦ ∑ m ∈ Finset.range k, (k.choose m : ℝ) *
            iteratedDeriv m (u' i) (x' i) * iteratedDeriv (k - m) (a' i) (x' i)) := by
        apply SeqClose.sum
        intro m hm
        have hm' := Finset.mem_range.1 hm
        exact ((SeqClose.const _).mul (ih m hm' (by omega))).mul (haj (k - m) (by omega))
      have hexpr := ((hbj k hk).sub hsum).mul hainv
      refine (hexpr.congr_left ?_).congr_right ?_
      · filter_upwards [ha0] with i hi
        exact (hformula (u i) (a i) (b i) (hu i) (ha i) (heq i) k (x i) hi.1).symm
      · filter_upwards [ha0] with i hi
        exact (hformula (u' i) (a' i) (b' i) (hu' i) (ha' i) (heq' i) k (x' i) hi.2).symm
  exact key

/-- Nonnegative square roots preserve derivative bounds and convergence when they stay
away from zero. -/
theorem DerivativesClose.of_mul_self_eq {s s' h h' : ℕ → ℝ → ℝ} {x x' : ℕ → ℝ} {n : ℕ}
    (hs : ∀ i, ContDiff ℝ ∞ (s i)) (hs' : ∀ i, ContDiff ℝ ∞ (s' i))
    (hpos : ∀ i y, 0 ≤ s i y) (hpos' : ∀ i y, 0 ≤ s' i y)
    (heq : ∀ i y, s i y * s i y = h i y) (heq' : ∀ i y, s' i y * s' i y = h' i y)
    (hhj : DerivativesClose h h' x x' n)
    {c : ℝ} (hc : 0 < c) (hlow : ∀ᶠ i in atTop, c ≤ s' i (x' i)) :
    DerivativesClose s s' x x' n := by
  have hh0 : SeqClose (fun i ↦ h i (x i)) (fun i ↦ h' i (x' i)) := by
    simpa using hhj 0 (Nat.zero_le _)
  have h0 : SeqClose (fun i ↦ s i (x i)) (fun i ↦ s' i (x' i)) := by
    have hbd : IsBoundedUnder (· ≤ ·) atTop (fun i ↦ ‖s' i (x' i)‖) := by
      obtain ⟨C, hC⟩ := hh0.2
      refine ⟨C + 1, ?_⟩
      simp only [eventually_map] at hC ⊢
      filter_upwards [hC] with i hi
      rw [← heq'] at hi
      rw [Real.norm_of_nonneg (hpos' _ _)]
      rw [Real.norm_of_nonneg (mul_self_nonneg _)] at hi
      nlinarith [hpos' i (x' i)]
    refine ⟨?_, hbd⟩
    have hq : IsBoundedUnder (· ≤ ·) atTop
        (fun i ↦ ‖(s i (x i) + s' i (x' i))⁻¹‖) := by
      refine ⟨c⁻¹, ?_⟩
      simp only [eventually_map]
      filter_upwards [hlow] with i hi
      rw [norm_inv, Real.norm_of_nonneg (add_nonneg (hpos _ _) (hpos' _ _))]
      exact inv_anti₀ hc (by linarith [hpos i (x i)])
    have := hh0.1.zero_mul_isBoundedUnder_le hq
    refine this.congr' ?_
    filter_upwards [hlow] with i hi
    have hne : s i (x i) + s' i (x' i) ≠ 0 := by linarith [hpos i (x i)]
    rw [← heq, ← heq']
    field_simp
    ring
  have hs0 : SeqClose (fun i ↦ (2 * s i (x i))⁻¹) (fun i ↦ (2 * s' i (x' i))⁻¹) := by
    refine (h0.const_mul 2).inv (by positivity : (0 : ℝ) < 2 * c) ?_
    filter_upwards [hlow] with i hi
    rw [Real.norm_of_nonneg (by linarith [hpos' i (x' i)])]
    linarith
  have hlowl : ∀ᶠ i in atTop, s i (x i) ≠ 0 := by
    have hsmall : ∀ᶠ i in atTop, ‖s i (x i) - s' i (x' i)‖ ≤ c / 2 :=
      h0.1.norm.eventually (Iic_mem_nhds (by simpa using half_pos hc))
    filter_upwards [hsmall, hlow] with i h1 h2 h3
    rw [h3, zero_sub, norm_neg, Real.norm_of_nonneg (hpos' _ _)] at h1
    linarith
  have hlowr : ∀ᶠ i in atTop, s' i (x' i) ≠ 0 := by
    filter_upwards [hlow] with i hi h0
    rw [h0] at hi
    linarith
  have hformula : ∀ (v H : ℝ → ℝ), ContDiff ℝ ∞ v → (∀ y, v y * v y = H y) →
      ∀ k z, v z ≠ 0 →
      iteratedDeriv (k + 1) v z = (iteratedDeriv (k + 1) H z -
        ∑ m ∈ Finset.range k, ((k + 1).choose (m + 1) : ℝ) * iteratedDeriv (m + 1) v z *
          iteratedDeriv (k + 1 - (m + 1)) v z) * (2 * v z)⁻¹ := by
    intro v H hv hvH k z hz
    have hH : H = fun y ↦ v y * v y := funext fun y ↦ (hvH y).symm
    rw [hH, iteratedDeriv_fun_mul ((hv).contDiffAt.of_le (by exact_mod_cast le_top))
      ((hv).contDiffAt.of_le (by exact_mod_cast le_top)), Finset.sum_range_succ',
      Finset.sum_range_succ]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, iteratedDeriv_zero,
      Nat.choose_zero_right, Nat.sub_zero]
    field_simp
    ring
  have key : ∀ k ≤ n, SeqClose (fun i ↦ iteratedDeriv k (s i) (x i))
      (fun i ↦ iteratedDeriv k (s' i) (x' i)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases k with _ | k
      · simpa using h0
      · have hsum : SeqClose
            (fun i ↦ ∑ m ∈ Finset.range k, ((k + 1).choose (m + 1) : ℝ) *
              iteratedDeriv (m + 1) (s i) (x i) * iteratedDeriv (k + 1 - (m + 1)) (s i) (x i))
            (fun i ↦ ∑ m ∈ Finset.range k, ((k + 1).choose (m + 1) : ℝ) *
              iteratedDeriv (m + 1) (s' i) (x' i) *
                iteratedDeriv (k + 1 - (m + 1)) (s' i) (x' i)) := by
          apply SeqClose.sum
          intro m hm
          have hm' := Finset.mem_range.1 hm
          exact ((SeqClose.const _).mul (ih (m + 1) (by omega) (by omega))).mul
            (ih (k + 1 - (m + 1)) (by omega) (by omega))
        have hexpr := ((hhj (k + 1) hk).sub hsum).mul hs0
        refine (hexpr.congr_left ?_).congr_right ?_
        · filter_upwards [hlowl] with i hi
          exact (hformula (s i) (h i) (hs i) (heq i) k (x i) hi).symm
        · filter_upwards [hlowr] with i hi
          exact (hformula (s' i) (h' i) (hs' i) (heq' i) k (x' i) hi).symm
  exact key

/-- If `Y ∘ X = id`, bounds and convergence of the derivatives of `X` through order `n + 1`
follow from those of its values and of the derivatives of `Y'` through order `n` at the images. -/
theorem DerivativesClose.inverse {X X' Y Y' : ℕ → ℝ → ℝ} {x x' : ℕ → ℝ} {n : ℕ}
    (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hX' : ∀ i, ContDiff ℝ ∞ (X' i))
    (hY : ∀ i, ContDiff ℝ ∞ (Y i)) (hY' : ∀ i, ContDiff ℝ ∞ (Y' i))
    (hinv : ∀ i y, Y i (X i y) = y) (hinv' : ∀ i y, Y' i (X' i y) = y)
    (hYj : DerivativesClose (fun i ↦ deriv (Y i)) (fun i ↦ deriv (Y' i))
      (fun i ↦ X i (x i)) (fun i ↦ X' i (x' i)) n)
    (h0 : SeqClose (fun i ↦ X i (x i)) (fun i ↦ X' i (x' i)))
    {c : ℝ} (hc : 0 < c) (hlow : ∀ᶠ i in atTop, c ≤ ‖deriv (Y' i) (X' i (x' i))‖) :
    DerivativesClose X X' x x' (n + 1) := by
  have hprod : ∀ (X₀ Y₀ : ℝ → ℝ), ContDiff ℝ ∞ X₀ → ContDiff ℝ ∞ Y₀ →
      (∀ y, Y₀ (X₀ y) = y) → ∀ y, deriv X₀ y * (deriv Y₀ ∘ X₀) y = 1 := by
    intro X₀ Y₀ hX₀ hY₀ hinv₀ y
    have hcomp : deriv (Y₀ ∘ X₀) y = 1 := by
      have : Y₀ ∘ X₀ = id := funext hinv₀
      rw [this, deriv_id]
    rw [deriv_comp y ((hY₀.differentiable (by simp)) _) ((hX₀.differentiable (by simp)) _)]
      at hcomp
    simpa [mul_comm] using hcomp
  have step : ∀ m ≤ n, DerivativesClose X X' x x' m → DerivativesClose X X' x x' (m + 1) := by
    intro m hm hXm
    have hcomp := DerivativesClose.comp (g := fun i ↦ deriv (Y i)) (g' := fun i ↦ deriv (Y' i))
      (fun i ↦ (hY i).deriv' (n := ∞)) (fun i ↦ (hY' i).deriv' (n := ∞))
      hX hX' (hYj.mono hm) hXm.positiveDerivativesClose
    have hu := DerivativesClose.of_mul_eq (u := fun i ↦ deriv (X i)) (u' := fun i ↦ deriv (X' i))
      (b := fun _ _ ↦ 1) (b' := fun _ _ ↦ 1)
      (fun i ↦ (hX i).deriv' (n := ∞)) (fun i ↦ (hX' i).deriv' (n := ∞))
      (fun i ↦ ((hY i).deriv' (n := ∞)).comp (hX i))
      (fun i ↦ ((hY' i).deriv' (n := ∞)).comp (hX' i))
      (fun i y ↦ hprod (X i) (Y i) (hX i) (hY i) (hinv i) y)
      (fun i y ↦ hprod (X' i) (Y' i) (hX' i) (hY' i) (hinv' i) y)
      hcomp (by
        intro k _
        rcases k with _ | k
        · exact SeqClose.const 1
        · simpa [iteratedDeriv_succ'] using SeqClose.const 0) hc hlow
    exact DerivativesClose.unshift h0 hu
  have : ∀ m ≤ n + 1, DerivativesClose X X' x x' m := by
    intro m
    induction m with
    | zero =>
      intro _ k hk
      obtain rfl : k = 0 := by omega
      simpa using h0
    | succ m ih => intro hm; exact step m (by omega) (ih (by omega))
  exact this (n + 1) le_rfl

end

end Expdb
