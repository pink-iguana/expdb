module

public import Expdb.ExponentialSums.ExponentSumGrowthBounds

/-!
# Exponent pairs

This module formalizes the blueprint's Exponent pairs chapter (`exponent-pairs-chapter`).

It defines exponent pairs and the van der Corput transforms, proves duality with the exponential
sum growth exponent, and shows that the set of exponent pairs is closed and convex.
-/

@[expose] public section

open Filter Topology
open scoped Expdb FourierTransform NNReal

noncomputable section

namespace Expdb

/-! ## Definition -/

/-- The analytic exponent-pair bound with the blueprint's subsequence convention made
explicit: every subsequence has a further subsequence on which the variable exponents
converge to the fixed parameters `k` and `ℓ`. All data use the same composed index map.
`isExponentPairBound_iff_forall_pos` recovers the epsilon estimates on arbitrary scales. -/
def IsExponentPairBound (k l : ℝ) : Prop :=
  ∀ (N T : VariableObject ℝ)
    (F : VariableFunction (VariableObject.fixed ℝ) ℝ)
    (a b : VariableObject ℕ),
    (∀ i, 1 ≤ N i) →
    (∀ i, N i ≤ T i) →
    IsModelPhaseFunction F →
    (∀ i, IsDyadicSubinterval (N i) (a i) (b i)) →
    ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∃ k' l' : VariableObject ℝ,
          k' =o VariableObject.fixed k ∧ l' =o VariableObject.fixed l ∧
          Asymptotics.IsBigO atTop
            (fun j ↦ exponentialSum F T N a b (φ (ψ j)))
            (fun j ↦ (T (φ (ψ j)) / N (φ (ψ j))) ^ k' j * N (φ (ψ j)) ^ l' j)

/-- The blueprint's Definition `exp-pair-def`: `(k, ℓ)` is an exponent pair if it lies in the
triangle `{0 ≤ k ≤ 1/2 ≤ ℓ ≤ 1, k + ℓ ≤ 1}` and satisfies the exponential sum bound
`IsExponentPairBound`. -/
def IsExponentPair (k l : ℝ) : Prop :=
  (0 ≤ k ∧ k ≤ 1 / 2 ∧ 1 / 2 ≤ l ∧ l ≤ 1 ∧ k + l ≤ 1) ∧ IsExponentPairBound k l

/-! ## The triangle constraints -/

/-- The first coordinate of an exponent pair is nonnegative. -/
theorem IsExponentPair.k_nonneg {k l : ℝ} (h : IsExponentPair k l) : 0 ≤ k := h.1.1

/-- The first coordinate of an exponent pair is at most `1 / 2`. -/
theorem IsExponentPair.k_le_half {k l : ℝ} (h : IsExponentPair k l) : k ≤ 1 / 2 := h.1.2.1

/-- The second coordinate of an exponent pair is at least `1 / 2`. -/
theorem IsExponentPair.half_le_l {k l : ℝ} (h : IsExponentPair k l) : 1 / 2 ≤ l := h.1.2.2.1

/-- The second coordinate of an exponent pair is at most `1`. -/
theorem IsExponentPair.l_le_one {k l : ℝ} (h : IsExponentPair k l) : l ≤ 1 := h.1.2.2.2.1

/-- The coordinates of an exponent pair sum to at most `1`. -/
theorem IsExponentPair.add_le_one {k l : ℝ} (h : IsExponentPair k l) : k + l ≤ 1 :=
  h.1.2.2.2.2

/-- The first coordinate of an exponent pair does not exceed the second. -/
theorem IsExponentPair.k_le_l {k l : ℝ} (h : IsExponentPair k l) : k ≤ l :=
  h.k_le_half.trans h.half_le_l

/-- An exponent pair satisfies the exponential sum bound. -/
theorem IsExponentPair.bound {k l : ℝ} (h : IsExponentPair k l) : IsExponentPairBound k l :=
  h.2

/-! ## Subsequences -/

/-- Being a model phase function is inherited by subsequences. -/
theorem IsModelPhaseFunction.comp_strictMono
    {F : VariableFunction (VariableObject.fixed ℝ) ℝ}
    (hF : IsModelPhaseFunction F) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsModelPhaseFunction (fun i ↦ F (φ i)) := by
  classical
  obtain ⟨hphase, σ, hσ, herror⟩ := hF
  refine ⟨fun i ↦ hphase (φ i), σ, hσ, ?_⟩
  intro p y
  set x : ∀ i, (VariableObject.fixed phaseInterval) i := fun j ↦
    if h : ∃ i, φ i = j then y h.choose
      else ⟨1, by simp [phaseInterval]⟩ with hxdef
  have hx : ∀ i, x (φ i) = y i := by
    intro i
    have h : ∃ i', φ i' = φ i := ⟨i, rfl⟩
    simp only [hxdef, dif_pos h]
    congr 1
    exact hφ.injective h.choose_spec
  have hlimit := (herror p x).comp hφ.tendsto_atTop
  refine hlimit.congr fun i ↦ ?_
  simp only [Function.comp_apply, hx i]
  rfl

/-- An exponential sum over an interval inside `[N, 2N]` has at most `3N` unit-sized terms. -/
theorem norm_exponentialSum_le_three_mul
    (F : VariableFunction (VariableObject.fixed ℝ) ℝ)
    (T N : VariableObject ℝ) (a b : VariableObject ℕ)
    (hN : ∀ i, 1 ≤ N i)
    (hab : ∀ i, IsDyadicSubinterval (N i) (a i) (b i))
    (i : ℕ) :
    ‖exponentialSum F T N a b i‖ ≤ 3 * N i := by
  have h := norm_exponentialSumAt_le_add_one (F i) (T i) (N i) (a i) (b i)
  have h2 := (hab i).2
  have h3 := hN i
  simpa [exponentialSum] using h.trans (by linarith)

private theorem exponentPairMajorant_shift (N T k l δ : ℝ) (hN : 0 < N) (hT : 0 < T) :
    (T / N) ^ (k + δ) * N ^ (l + δ) =
      ((T / N) ^ k * N ^ l) * T ^ δ := by
  rw [Real.rpow_add (div_pos hT hN), Real.rpow_add hN]
  calc
    (T / N) ^ k * (T / N) ^ δ * (N ^ l * N ^ δ) =
        ((T / N) ^ k * N ^ l) * ((T / N) ^ δ * N ^ δ) := by ring
    _ = ((T / N) ^ k * N ^ l) * T ^ δ := by
      rw [← Real.mul_rpow (div_pos hT hN).le hN.le, div_mul_cancel₀ T hN.ne']

/-- Vanishing exponent losses imply every fixed positive loss, without a growth
assumption on the heights. -/
private theorem exponentPairBound_isBigO
    (S : VariableObject ℂ) (N T : VariableObject ℝ) (k l : ℝ)
    (hN : ∀ i, 1 ≤ N i) (hNT : ∀ i, N i ≤ T i)
    (hS : ∃ k' l' : VariableObject ℝ,
      k' =o VariableObject.fixed k ∧ l' =o VariableObject.fixed l ∧
      Asymptotics.IsBigO atTop S (fun i ↦ (T i / N i) ^ k' i * N i ^ l' i)) :
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO atTop S
      (fun i ↦ (T i / N i) ^ (k + ε) * N i ^ (l + ε)) := by
  have hNpos : ∀ i, 0 < N i := fun i ↦ zero_lt_one.trans_le (hN i)
  have hT : ∀ i, 1 ≤ T i := fun i ↦ (hN i).trans (hNT i)
  have hTpos : ∀ i, 0 < T i := fun i ↦ zero_lt_one.trans_le (hT i)
  have hdiv : ∀ i, 1 ≤ T i / N i := fun i ↦ (le_div_iff₀ (hNpos i)).mpr (by simpa using hNT i)
  obtain ⟨k', l', hk', hl', hbound⟩ := hS
  intro ε hε
  have hk := (isEqUpToInfinitesimal_iff_forall_pos k' (VariableObject.fixed k)).mp hk' ε hε
  have hl := (isEqUpToInfinitesimal_iff_forall_pos l' (VariableObject.fixed l)).mp hl' ε hε
  refine hbound.trans (Asymptotics.IsBigO.of_bound 1 ?_)
  filter_upwards [hk, hl] with i hki hli
  simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (div_pos (hTpos i) (hNpos i)).le _) (Real.rpow_nonneg (hNpos i).le _)),
    one_mul]
  rw [Real.norm_eq_abs] at hki hli
  apply mul_le_mul
    (Real.rpow_le_rpow_of_exponent_le (hdiv i) (by
      dsimp [VariableObject.fixed] at hki; linarith [le_abs_self (k' i - k)]))
    (Real.rpow_le_rpow_of_exponent_le (hN i) (by
      dsimp [VariableObject.fixed] at hli; linarith [le_abs_self (l' i - l)]))
    (Real.rpow_nonneg (hNpos i).le _) (Real.rpow_nonneg (div_pos (hTpos i) (hNpos i)).le _)

/-- On divergent heights, vanishing exponent losses are equivalent to every fixed
positive exponent loss. The two variable exponents need not have the same error. -/
private theorem exponentPairBound_iff_forall_pos
    (S : VariableObject ℂ) (N T : VariableObject ℝ) (k l : ℝ)
    (hN : ∀ i, 1 ≤ N i) (hNT : ∀ i, N i ≤ T i) (hTunbounded : T.IsUnbounded) :
    (∃ k' l' : VariableObject ℝ,
      k' =o VariableObject.fixed k ∧ l' =o VariableObject.fixed l ∧
      Asymptotics.IsBigO atTop S (fun i ↦ (T i / N i) ^ k' i * N i ^ l' i)) ↔
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO atTop S
      (fun i ↦ (T i / N i) ^ (k + ε) * N i ^ (l + ε)) := by
  have hNpos : ∀ i, 0 < N i := fun i ↦ zero_lt_one.trans_le (hN i)
  have hT : ∀ i, 1 ≤ T i := fun i ↦ (hN i).trans (hNT i)
  have hTpos : ∀ i, 0 < T i := fun i ↦ zero_lt_one.trans_le (hT i)
  constructor
  · intro hS
    exact exponentPairBound_isBigO S N T k l hN hNT hS
  · intro hS
    let B : VariableObject ℝ := fun i ↦ (T i / N i) ^ k * N i ^ l
    have hBpos : ∀ i, 0 < B i := fun i ↦ mul_pos
      (Real.rpow_pos_of_pos (div_pos (hTpos i) (hNpos i)) _) (Real.rpow_pos_of_pos (hNpos i) _)
    let X : VariableObject ℝ := fun i ↦ ‖S i‖ / B i
    have hX : IsPowerBounded X T 0 := by
      apply (isPowerBounded_iff_forall_pos X T 0 hT hTunbounded).mpr
      intro ε hε
      obtain ⟨C, hCpos, hC⟩ := (hS ε hε).exists_pos
      refine Asymptotics.IsBigO.of_bound C ?_
      filter_upwards [hC.bound] with i hi
      have hshift := exponentPairMajorant_shift (N i) (T i) k l ε (hNpos i) (hTpos i)
      simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (Real.rpow_nonneg (div_pos (hTpos i) (hNpos i)).le _)
        (Real.rpow_nonneg (hNpos i).le _))] at hi
      simp only [X, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (hBpos i).le),
        zero_add, abs_of_nonneg (Real.rpow_nonneg (hTpos i).le _)]
      apply (div_le_iff₀ (hBpos i)).mpr
      rw [hshift] at hi
      dsimp [B]
      nlinarith [hi]
    obtain ⟨δ, hδ, hbound⟩ := hX
    refine ⟨fun i ↦ k + δ i, fun i ↦ l + δ i, ?_, ?_, ?_⟩
    · rw [isEqUpToInfinitesimal_iff_tendsto_sub] at hδ ⊢
      simpa [VariableObject.fixed] using hδ
    · rw [isEqUpToInfinitesimal_iff_tendsto_sub] at hδ ⊢
      simpa [VariableObject.fixed] using hδ
    · obtain ⟨C, hCpos, hC⟩ := hbound.exists_pos
      refine Asymptotics.IsBigO.of_bound C ?_
      filter_upwards [hC.bound] with i hi
      simp only [X, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (hBpos i).le),
        abs_of_nonneg (Real.rpow_nonneg (hTpos i).le _)] at hi
      simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (Real.rpow_nonneg (div_pos (hTpos i) (hNpos i)).le _) (Real.rpow_nonneg (hNpos i).le _))]
      rw [exponentPairMajorant_shift (N i) (T i) k l (δ i) (hNpos i) (hTpos i)]
      have := (div_le_iff₀ (hBpos i)).mp hi
      dsimp [B] at this
      nlinarith [this]

/-- The subsequence formulation of the vanishing-exponent bound is equivalent to epsilon
bounds on all scale sequences, including bounded or oscillating heights. -/
theorem isExponentPairBound_iff_forall_pos {k l : ℝ} :
    IsExponentPairBound k l ↔
    ∀ (N T : VariableObject ℝ)
      (F : VariableFunction (VariableObject.fixed ℝ) ℝ) (a b : VariableObject ℕ),
      (∀ i, 1 ≤ N i) → (∀ i, N i ≤ T i) → IsModelPhaseFunction F →
      (∀ i, IsDyadicSubinterval (N i) (a i) (b i)) →
      ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO atTop (exponentialSum F T N a b)
        (fun i ↦ (T i / N i) ^ (k + ε) * N i ^ (l + ε)) := by
  constructor
  · intro h N T F a b hN hNT hF hab ε hε
    by_contra hO
    have hfreq : ∀ n : ℕ, ∃ᶠ i in atTop,
        (n : ℝ) * ‖(T i / N i) ^ (k + ε) * N i ^ (l + ε)‖ <
          ‖exponentialSum F T N a b i‖ := by
      intro n
      rw [Asymptotics.isBigO_iff] at hO
      push Not at hO
      simpa using hO n
    obtain ⟨φ, hφ, hφprop⟩ := extraction_forall_of_frequently hfreq
    obtain ⟨ψ, hψ, k', l', hk', hl', hbound⟩ := h N T F a b hN hNT hF hab φ hφ
    have hsubε := exponentPairBound_isBigO
      (fun j ↦ exponentialSum F T N a b (φ (ψ j)))
      (N ∘ φ ∘ ψ) (T ∘ φ ∘ ψ) k l (fun j ↦ hN _) (fun j ↦ hNT _)
      ⟨k', l', hk', hl', hbound⟩ ε hε
    obtain ⟨C, hCpos, hC⟩ := hsubε.exists_pos
    have hcontra : ∀ᶠ j : ℕ in atTop, (ψ j : ℝ) < C := by
      filter_upwards [hC.bound] with j hj
      have hf := hφprop (ψ j)
      have hNpos : 0 < N (φ (ψ j)) := zero_lt_one.trans_le (hN _)
      have hTpos : 0 < T (φ (ψ j)) := hNpos.trans_le (hNT _)
      have hRpos : 0 < ‖(T (φ (ψ j)) / N (φ (ψ j))) ^ (k + ε) *
          N (φ (ψ j)) ^ (l + ε)‖ := by
        exact norm_pos_iff.mpr (mul_pos
          (Real.rpow_pos_of_pos (div_pos hTpos hNpos) _)
          (Real.rpow_pos_of_pos hNpos _)).ne'
      change ‖exponentialSum F T N a b (φ (ψ j))‖ ≤
        C * ‖(T (φ (ψ j)) / N (φ (ψ j))) ^ (k + ε) *
          N (φ (ψ j)) ^ (l + ε)‖ at hj
      exact lt_of_mul_lt_mul_right (hf.trans_le hj) hRpos.le
    have hlarge : ∀ᶠ j : ℕ in atTop, C ≤ (ψ j : ℝ) :=
      (tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop).eventually (eventually_ge_atTop C)
    obtain ⟨j, hj, hjC⟩ := (hcontra.and hlarge).exists
    exact (not_lt_of_ge hjC) hj
  · intro h N T F a b hN hNT hF hab φ hφ
    have hNpos : ∀ i, 0 < N i := fun i ↦ zero_lt_one.trans_le (hN i)
    have hT : ∀ i, 1 ≤ T i := fun i ↦ (hN i).trans (hNT i)
    have hTpos : ∀ i, 0 < T i := fun i ↦ zero_lt_one.trans_le (hT i)
    let B : VariableObject ℝ := fun i ↦ (T i / N i) ^ k * N i ^ l
    have hBpos : ∀ i, 0 < B i := fun i ↦ mul_pos
      (Real.rpow_pos_of_pos (div_pos (hTpos i) (hNpos i)) _) (Real.rpow_pos_of_pos (hNpos i) _)
    let X : VariableObject ℝ := fun i ↦ ‖exponentialSum F T N a b i‖ / B i
    have hXbound : ∀ i, X i ≤ 3 * T i ^ (1 + |k| + |l|) := by
      intro i
      have hdiv1 : 1 ≤ T i / N i := (le_div_iff₀ (hNpos i)).mpr (by simpa using hNT i)
      have hdivT : T i / N i ≤ T i := by
        apply (div_le_iff₀ (hNpos i)).mpr
        nlinarith [hN i, hTpos i]
      have hkbound : (T i / N i) ^ (-k) ≤ T i ^ |k| :=
        (Real.rpow_le_rpow_of_exponent_le hdiv1 (neg_le_abs k)).trans
          (Real.rpow_le_rpow (div_pos (hTpos i) (hNpos i)).le hdivT (abs_nonneg k))
      have hlbound : N i ^ (-l) ≤ T i ^ |l| :=
        (Real.rpow_le_rpow_of_exponent_le (hN i) (neg_le_abs l)).trans
          (Real.rpow_le_rpow (hNpos i).le (hNT i) (abs_nonneg l))
      have hSbound : ‖exponentialSum F T N a b i‖ ≤ 3 * T i :=
        (norm_exponentialSum_le_three_mul F T N a b hN hab i).trans (by linarith [hNT i])
      have hinv : (B i)⁻¹ = (T i / N i) ^ (-k) * N i ^ (-l) := by
        dsimp [B]
        rw [mul_inv_rev, Real.rpow_neg (div_pos (hTpos i) (hNpos i)).le,
          Real.rpow_neg (hNpos i).le]
        ring
      calc
        X i = ‖exponentialSum F T N a b i‖ *
            ((T i / N i) ^ (-k) * N i ^ (-l)) := by
          dsimp [X]
          rw [div_eq_mul_inv, hinv]
        _ ≤ (3 * T i) * (T i ^ |k| * T i ^ |l|) := by
          exact mul_le_mul hSbound
            (mul_le_mul hkbound hlbound (Real.rpow_nonneg (hNpos i).le _)
              (Real.rpow_nonneg (hTpos i).le _))
            (mul_nonneg (Real.rpow_nonneg (div_pos (hTpos i) (hNpos i)).le _)
              (Real.rpow_nonneg (hNpos i).le _)) (mul_nonneg (by norm_num) (hTpos i).le)
        _ = 3 * T i ^ (1 + |k| + |l|) := by
          rw [Real.rpow_add (hTpos i), Real.rpow_add (hTpos i), Real.rpow_one]
          ring
    by_cases htop : Tendsto (T ∘ φ) atTop atTop
    · refine ⟨id, strictMono_id, ?_⟩
      have hTunbounded : VariableObject.IsUnbounded (T ∘ φ) :=
        (VariableObject.isUnbounded_iff_tendsto_atTop
          (fun j ↦ (hTpos (φ j)).le)).mpr htop
      apply (exponentPairBound_iff_forall_pos
        (fun j ↦ exponentialSum F T N a b (φ j)) (N ∘ φ) (T ∘ φ) k l
        (fun j ↦ hN _) (fun j ↦ hNT _) hTunbounded).mpr
      intro ε hε
      exact (h N T F a b hN hNT hF hab ε hε).comp_tendsto hφ.tendsto_atTop
    · have hfreq : ∃ M : ℝ, ∃ᶠ j in atTop, T (φ j) < M := by
        simpa only [Filter.tendsto_atTop, not_forall, Filter.not_eventually, not_le,
          Function.comp_apply]
          using htop
      obtain ⟨M, hM⟩ := hfreq
      obtain ⟨ψ, hψ, hψbound⟩ := extraction_of_frequently_atTop hM
      refine ⟨ψ, hψ, VariableObject.fixed k, VariableObject.fixed l,
        IsEqUpToInfinitesimal.refl _, IsEqUpToInfinitesimal.refl _, ?_⟩
      let Q : ℝ := max M 1
      have hMQ : M ≤ Q := le_max_left _ _
      refine Asymptotics.IsBigO.of_bound (3 * Q ^ (1 + |k| + |l|)) ?_
      filter_upwards [] with j
      have hsmall : T (φ (ψ j)) ≤ Q := (hψbound j).le.trans hMQ
      have hb := Real.rpow_le_rpow (hTpos (φ (ψ j))).le hsmall
        (show 0 ≤ 1 + |k| + |l| by positivity)
      have hx : X (φ (ψ j)) ≤ 3 * Q ^ (1 + |k| + |l|) :=
        (hXbound _).trans (mul_le_mul_of_nonneg_left hb (by norm_num))
      have hS := (div_le_iff₀ (hBpos (φ (ψ j)))).mp hx
      simpa only [B, VariableObject.fixed, Real.norm_eq_abs,
        abs_of_pos (hBpos (φ (ψ j)))] using hS

/-! ## Consequences of the exponential sum bound -/

/-- The exponential sum bound may be applied when `N ≤ T` only holds eventually. -/
theorem IsExponentPairBound.isBigO_of_eventually_le
    {k l : ℝ} (h : IsExponentPairBound k l) {N T : VariableObject ℝ}
    {F : VariableFunction (VariableObject.fixed ℝ) ℝ} {a b : VariableObject ℕ}
    (hN : ∀ i, 1 ≤ N i) (hT : ∀ i, 1 ≤ T i) (hNT : ∀ᶠ i in atTop, N i ≤ T i)
    (hF : IsModelPhaseFunction F)
    (hab : ∀ i, IsDyadicSubinterval (N i) (a i) (b i))
    {ε : ℝ} (hε : 0 < ε) :
    Asymptotics.IsBigO atTop (exponentialSum F T N a b)
      (fun i ↦ (T i / N i) ^ (k + ε) * N i ^ (l + ε)) := by
  classical
  set N' : VariableObject ℝ := fun i ↦ if N i ≤ T i then N i else T i with hN'def
  set a' : VariableObject ℕ := fun i ↦ if N i ≤ T i then a i else ⌈T i⌉₊ with ha'def
  set b' : VariableObject ℕ := fun i ↦ if N i ≤ T i then b i else 0 with hb'def
  have hN'1 : ∀ i, 1 ≤ N' i := by
    intro i
    by_cases hi : N i ≤ T i <;> simp [hN'def, hi, hN i, hT i]
  have hN'T : ∀ i, N' i ≤ T i := by
    intro i
    by_cases hi : N i ≤ T i <;> simp [hN'def, hi]
  have hab' : ∀ i, IsDyadicSubinterval (N' i) (a' i) (b' i) := by
    intro i
    by_cases hi : N i ≤ T i
    · simpa [hN'def, ha'def, hb'def, hi] using hab i
    · refine ⟨?_, ?_⟩
      · simpa [hN'def, ha'def, hi] using Nat.le_ceil (T i)
      · have := hT i
        simp only [hN'def, hb'def, hi, if_false, Nat.cast_zero]
        linarith
  have hmain := isExponentPairBound_iff_forall_pos.mp h N' T F a' b' hN'1 hN'T hF hab' ε hε
  refine hmain.congr' ?_ ?_ <;> filter_upwards [hNT] with i hi
  · simp [exponentialSum, hN'def, ha'def, hb'def, hi]
  · simp [hN'def, hi]

/-! ## Duality with the exponential sum growth exponent -/

/-- Half of the blueprint's Lemma `beta-duality`: an exponent pair gives the linear bound
`β(α) ≤ k + (ℓ - k) α`, here in the range `α < 1`. -/
theorem IsExponentPairBound.isExponentSumBound
    {k l : ℝ} (h : IsExponentPairBound k l) (hkl : k ≤ l)
    {α : ℝ≥0} (hα : (α : ℝ) < 1) :
    IsExponentSumBound α (k + (l - k) * α) := by
  intro N T F a b hN hT hTunbounded hNT hF hab
  refine (isPowerBounded_iff_forall_pos _ T _ hT hTunbounded).2 ?_
  intro ε hε
  have hlk : 0 ≤ l - k := by linarith
  set δ : ℝ := min ((1 - (α : ℝ)) / 2) (ε / (2 * (l - k + 1))) with hδdef
  have hδpos : 0 < δ := by
    refine lt_min (by linarith) ?_
    have : 0 < 2 * (l - k + 1) := by linarith
    positivity
  have hδ1 : (α : ℝ) + δ ≤ 1 := by
    have := min_le_left ((1 - (α : ℝ)) / 2) (ε / (2 * (l - k + 1)))
    rw [← hδdef] at this
    linarith
  have hδ2 : δ * (l - k) ≤ ε / 2 := by
    have hd := min_le_right ((1 - (α : ℝ)) / 2) (ε / (2 * (l - k + 1)))
    rw [← hδdef, le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (l - k + 1))] at hd
    nlinarith [hδpos.le]
  have hbetween := hNT.eventually_between (Filter.Eventually.of_forall hT) hδpos
  have hNTle : ∀ᶠ i in atTop, N i ≤ T i := by
    filter_upwards [hbetween] with i hi
    calc N i ≤ T i ^ ((α : ℝ) + δ) := hi.2
      _ ≤ T i ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (hT i) hδ1
      _ = T i := Real.rpow_one _
  have hbig := h.isBigO_of_eventually_le hN hT hNTle hF hab
    (ε := ε / 2) (by linarith)
  refine hbig.trans (Asymptotics.IsBigO.of_bound 1 ?_)
  filter_upwards [hbetween] with i hi
  have hT0 : (0 : ℝ) < T i := lt_of_lt_of_le zero_lt_one (hT i)
  have hN0 : (0 : ℝ) < N i := lt_of_lt_of_le zero_lt_one (hN i)
  have hsplit : (T i / N i) ^ (k + ε / 2) * N i ^ (l + ε / 2) =
      T i ^ (k + ε / 2) * N i ^ (l - k) := by
    rw [Real.div_rpow hT0.le hN0.le, div_mul_eq_mul_div, mul_div_assoc,
      ← Real.rpow_sub hN0, show l + ε / 2 - (k + ε / 2) = l - k by ring]
  have hNpow : N i ^ (l - k) ≤ T i ^ (((α : ℝ) + δ) * (l - k)) := by
    calc N i ^ (l - k) ≤ (T i ^ ((α : ℝ) + δ)) ^ (l - k) :=
          Real.rpow_le_rpow hN0.le hi.2 hlk
      _ = T i ^ (((α : ℝ) + δ) * (l - k)) := by
          rw [← Real.rpow_mul hT0.le]
  have hfinal : T i ^ (k + ε / 2) * N i ^ (l - k) ≤
      T i ^ (k + (l - k) * (α : ℝ) + ε) := by
    calc T i ^ (k + ε / 2) * N i ^ (l - k)
        ≤ T i ^ (k + ε / 2) * T i ^ (((α : ℝ) + δ) * (l - k)) := by
          gcongr
      _ = T i ^ (k + ε / 2 + ((α : ℝ) + δ) * (l - k)) := by
          rw [← Real.rpow_add hT0]
      _ ≤ T i ^ (k + (l - k) * (α : ℝ) + ε) := by
          apply Real.rpow_le_rpow_of_exponent_le (hT i)
          nlinarith [hδ2]
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (T i / N i) ^ (k + ε / 2) * N i ^ (l + ε / 2)),
    abs_of_nonneg (Real.rpow_nonneg hT0.le _), hsplit]
  exact hfinal

/-- An exponent pair gives the linear bound `β(α) ≤ k + (ℓ - k) α` on `[0, 1]`. -/
theorem IsExponentPair.exponentSumGrowthExponent_le
    {k l : ℝ} (h : IsExponentPair k l) {α : ℝ≥0} (hα : α ≤ 1) :
    exponentSumGrowthExponent α ≤ k + (l - k) * α := by
  have hkl : k ≤ l := h.k_le_l
  have hα' : (α : ℝ) ≤ 1 := by exact_mod_cast hα
  rcases lt_or_eq_of_le hα' with hlt | heq
  · exact exponentSumGrowthExponent_le_iff.2 (h.bound.isExponentSumBound hkl hlt)
  · have hαone : α = 1 := by exact_mod_cast heq
    subst hαone
    rw [NNReal.coe_one, mul_one]
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    set ε' : ℝ := min ε (1 / 2) with hε'def
    have hε'pos : 0 < ε' := lt_min hε (by norm_num)
    have hε'le : ε' ≤ ε := min_le_left _ _
    have hε'half : ε' ≤ 1 / 2 := min_le_right _ _
    set α' : ℝ≥0 := ⟨1 - ε', by linarith⟩ with hα'def
    have hcoe : (α' : ℝ) = 1 - ε' := rfl
    have hle : α' ≤ 1 := by
      rw [← NNReal.coe_le_coe, hcoe, NNReal.coe_one]
      linarith
    have h1 := exponentSumGrowthExponent_le_add_sub hle
    have h2 : exponentSumGrowthExponent α' ≤ k + (l - k) * (α' : ℝ) :=
      exponentSumGrowthExponent_le_iff.2
        (h.bound.isExponentSumBound hkl (by rw [hcoe]; linarith))
    rw [NNReal.coe_one] at h1
    rw [hcoe] at h2
    nlinarith [sub_nonneg.2 hkl]

/-- The converse half of the blueprint's Lemma `beta-duality`: the linear bound
`β(α) ≤ k + (ℓ - k) α` on `[0, 1]` implies the exponential sum bound. -/
theorem isExponentPairBound_of_forall_exponentSumGrowthExponent_le
    {k l : ℝ} (hk : 0 ≤ k) (hkl : k ≤ l)
    (hβ : ∀ α : ℝ≥0, α ≤ 1 → exponentSumGrowthExponent α ≤ k + (l - k) * α) :
    IsExponentPairBound k l := by
  apply isExponentPairBound_iff_forall_pos.mpr
  intro N T F a b hN hNT hF hab ε hε
  by_contra hO
  have hT1 : ∀ i, 1 ≤ T i := fun i ↦ (hN i).trans (hNT i)
  have hlk : 0 ≤ l - k := by linarith
  set R : VariableObject ℝ := fun i ↦ (T i / N i) ^ (k + ε) * N i ^ (l + ε) with hRdef
  have hRsplit : ∀ i, R i = T i ^ (k + ε) * N i ^ (l - k) := by
    intro i
    have hT0 : (0 : ℝ) < T i := lt_of_lt_of_le zero_lt_one (hT1 i)
    have hN0 : (0 : ℝ) < N i := lt_of_lt_of_le zero_lt_one (hN i)
    simp only [hRdef]
    rw [Real.div_rpow hT0.le hN0.le, div_mul_eq_mul_div, mul_div_assoc,
      ← Real.rpow_sub hN0, show l + ε - (k + ε) = l - k by ring]
  have hR1 : ∀ i, 1 ≤ R i := by
    intro i
    rw [hRsplit i]
    have h1 : (1 : ℝ) ≤ T i ^ (k + ε) :=
      Real.one_le_rpow (hT1 i) (by linarith)
    have h2 : (1 : ℝ) ≤ N i ^ (l - k) := Real.one_le_rpow (hN i) hlk
    nlinarith
  -- Extract a subsequence along which the claimed bound fails badly.
  have hfreq : ∀ n : ℕ, ∃ᶠ i in atTop,
      (n : ℝ) * ‖R i‖ < ‖exponentialSum F T N a b i‖ := by
    intro n
    rw [Asymptotics.isBigO_iff] at hO
    push Not at hO
    simpa using hO n
  obtain ⟨φ, hφ, hφprop⟩ := extraction_forall_of_frequently hfreq
  -- The scales along this subsequence tend to infinity.
  have hNlarge : ∀ j : ℕ, (j : ℝ) ≤ 3 * N (φ j) := by
    intro j
    have h1 := hφprop j
    have h2 : (1 : ℝ) ≤ ‖R (φ j)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hR1 (φ j)])]
      exact hR1 (φ j)
    have h3 : ‖exponentialSum F T N a b (φ j)‖ ≤ 3 * N (φ j) :=
      norm_exponentialSum_le_three_mul F T N a b hN hab (φ j)
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have hNtop : Tendsto (fun j ↦ N (φ j)) atTop atTop := by
    have hdiv : Tendsto (fun j : ℕ ↦ (j : ℝ) / 3) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
    refine tendsto_atTop_mono (fun j ↦ ?_) hdiv
    exact (div_le_iff₀ (show (0:ℝ) < 3 by norm_num)).2 (by linarith [hNlarge j])
  have hTtop : Tendsto (fun j ↦ T (φ j)) atTop atTop :=
    tendsto_atTop_mono (fun j ↦ hNT (φ j)) hNtop
  -- Pass to a further subsequence on which the scale exponent converges.
  set x : ℕ → ℝ := fun j ↦ max 0 (min 1 (Real.logb (T (φ j)) (N (φ j)))) with hxdef
  have hxmem : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    refine ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  obtain ⟨α0, hα0mem, ψ, hψ, hlimit⟩ := isCompact_Icc.tendsto_subseq hxmem
  set φ2 : ℕ → ℕ := fun j ↦ φ (ψ j) with hφ2def
  have hφ2 : StrictMono φ2 := hφ.comp hψ
  set N₂ : VariableObject ℝ := fun j ↦ N (φ2 j) with hN₂def
  set T₂ : VariableObject ℝ := fun j ↦ T (φ2 j) with hT₂def
  set F₂ : VariableFunction (VariableObject.fixed ℝ) ℝ := fun j ↦ F (φ2 j) with hF₂def
  set a₂ : VariableObject ℕ := fun j ↦ a (φ2 j) with ha₂def
  set b₂ : VariableObject ℕ := fun j ↦ b (φ2 j) with hb₂def
  have hN₂1 : ∀ j, 1 ≤ N₂ j := fun j ↦ hN _
  have hT₂1 : ∀ j, 1 ≤ T₂ j := fun j ↦ hT1 _
  have hT₂top : Tendsto T₂ atTop atTop := hTtop.comp hψ.tendsto_atTop
  have hT₂unbounded : T₂.IsUnbounded :=
    (VariableObject.isUnbounded_iff_tendsto_atTop
      (fun j ↦ zero_le_one.trans (hT₂1 j))).2 hT₂top
  have hT₂gt : ∀ᶠ j in atTop, 1 < T₂ j := hT₂top.eventually (eventually_gt_atTop 1)
  have hlogb : Tendsto (fun j ↦ Real.logb (T₂ j) (N₂ j)) atTop (𝓝 α0) := by
    refine hlimit.congr' ?_
    filter_upwards [hT₂gt] with j hj
    have hlogT : 0 < Real.log (T₂ j) := Real.log_pos hj
    have hlogN : 0 ≤ Real.log (N₂ j) := Real.log_nonneg (hN₂1 j)
    have hle : Real.log (N₂ j) ≤ Real.log (T₂ j) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one (hN₂1 j)) (hNT _)
    have h0 : 0 ≤ Real.logb (T₂ j) (N₂ j) := by
      rw [Real.logb]; positivity
    have h1 : Real.logb (T₂ j) (N₂ j) ≤ 1 := by
      rw [Real.logb, div_le_one hlogT]; exact hle
    simp only [Function.comp_apply, hxdef]
    change max 0 (min 1 (Real.logb (T₂ j) (N₂ j))) = Real.logb (T₂ j) (N₂ j)
    rw [min_eq_right h1, max_eq_right h0]
  have hpa : IsPowerAsymptotic N₂ T₂ α0 :=
    isPowerAsymptotic_of_logb_tendsto hT₂gt
      (Filter.Eventually.of_forall fun j ↦ lt_of_lt_of_le zero_lt_one (hN₂1 j)) hlogb
  set αnn : ℝ≥0 := ⟨α0, hα0mem.1⟩ with hαnndef
  have hαnncoe : (αnn : ℝ) = α0 := rfl
  have hαnnle : αnn ≤ 1 := by
    rw [← NNReal.coe_le_coe, hαnncoe, NNReal.coe_one]
    exact hα0mem.2
  have hsumbound : IsExponentSumBound αnn (k + (l - k) * α0) :=
    exponentSumGrowthExponent_le_iff.1 (hβ αnn hαnnle)
  have hpb := hsumbound N₂ T₂ F₂ a₂ b₂ hN₂1 hT₂1 hT₂unbounded hpa
    (hF.comp_strictMono hφ2) (fun j ↦ hab _)
  obtain ⟨C, hCpos, hCbound⟩ :=
    ((isPowerBounded_iff_forall_pos _ T₂ _ hT₂1 hT₂unbounded).1 hpb
      (ε / 4) (by linarith)).exists_pos
  -- Bound the majorant below along the subsequence.
  set δ : ℝ := ε / (2 * (l - k + 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    have : 0 < 2 * (l - k + 1) := by linarith
    positivity
  have hδ2 : δ * (l - k) ≤ ε / 2 := by
    rw [hδdef]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num : (0:ℝ) < 2)]
    nlinarith
  have hbetween := hpa.eventually_between
    (Filter.Eventually.of_forall hT₂1) hδpos
  have hcontra : ∀ᶠ j in atTop, ((ψ j : ℝ)) < C := by
    filter_upwards [hbetween, hCbound.bound, hT₂gt] with j hj hCj hTj
    have hT0 : (0 : ℝ) < T₂ j := lt_trans zero_lt_one hTj
    have hRlow : T₂ j ^ (k + (l - k) * α0 + ε / 2) ≤ R (φ2 j) := by
      rw [hRsplit]
      calc T₂ j ^ (k + (l - k) * α0 + ε / 2)
          ≤ T₂ j ^ (k + ε + (α0 - δ) * (l - k)) := by
            apply Real.rpow_le_rpow_of_exponent_le hTj.le
            nlinarith
        _ = T₂ j ^ (k + ε) * T₂ j ^ ((α0 - δ) * (l - k)) := by
            rw [← Real.rpow_add hT0]
        _ = T₂ j ^ (k + ε) * (T₂ j ^ (α0 - δ)) ^ (l - k) := by
            rw [← Real.rpow_mul hT0.le]
        _ ≤ T₂ j ^ (k + ε) * N₂ j ^ (l - k) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _) hj.1 hlk)
              (Real.rpow_nonneg hT0.le _)
    have hSj : ‖exponentialSum F T N a b (φ2 j)‖ ≤ C * T₂ j ^ (k + (l - k) * α0 + ε / 4) := by
      have := hCj
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans (hT₂1 j)) _)] at this
      exact this
    have hlow := hφprop (ψ j)
    have hRnorm : ‖R (φ2 j)‖ = R (φ2 j) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hR1 (φ2 j)])]
    rw [hRnorm] at hlow
    have hmono : T₂ j ^ (k + (l - k) * α0 + ε / 4) ≤
        T₂ j ^ (k + (l - k) * α0 + ε / 2) :=
      Real.rpow_le_rpow_of_exponent_le hTj.le (by linarith)
    have hpos : (0 : ℝ) < T₂ j ^ (k + (l - k) * α0 + ε / 2) :=
      Real.rpow_pos_of_pos hT0 _
    have hkey : (ψ j : ℝ) * T₂ j ^ (k + (l - k) * α0 + ε / 2) <
        C * T₂ j ^ (k + (l - k) * α0 + ε / 2) := by
      calc (ψ j : ℝ) * T₂ j ^ (k + (l - k) * α0 + ε / 2)
          ≤ (ψ j : ℝ) * R (φ2 j) := by
            have : (0 : ℝ) ≤ (ψ j : ℝ) := Nat.cast_nonneg _
            exact mul_le_mul_of_nonneg_left hRlow this
        _ < ‖exponentialSum F T N a b (φ2 j)‖ := hlow
        _ ≤ C * T₂ j ^ (k + (l - k) * α0 + ε / 4) := hSj
        _ ≤ C * T₂ j ^ (k + (l - k) * α0 + ε / 2) := by
            exact mul_le_mul_of_nonneg_left hmono hCpos.le
    exact lt_of_mul_lt_mul_right (by linarith [hkey]) hpos.le
  obtain ⟨j, hj1, hj2⟩ := ((hcontra.and (eventually_ge_atTop ⌈C⌉₊)).exists)
  have : (C : ℝ) ≤ (j : ℝ) := le_trans (Nat.le_ceil C) (by exact_mod_cast hj2)
  have hψj : (j : ℝ) ≤ (ψ j : ℝ) := by exact_mod_cast hψ.le_apply
  linarith

/-- **Duality between exponent pairs and `β`** (blueprint Lemma `beta-duality`). A point
`(k, ℓ)` of the triangle `{0 ≤ k ≤ 1/2 ≤ ℓ ≤ 1, k + ℓ ≤ 1}` is an exponent pair if and only if
`β(α) ≤ k + (ℓ - k) α` for all `0 ≤ α ≤ 1`. -/
theorem isExponentPair_iff_forall_exponentSumGrowthExponent_le
    {k l : ℝ} (htriangle : 0 ≤ k ∧ k ≤ 1 / 2 ∧ 1 / 2 ≤ l ∧ l ≤ 1 ∧ k + l ≤ 1) :
    IsExponentPair k l ↔
      ∀ α : ℝ≥0, α ≤ 1 → exponentSumGrowthExponent α ≤ k + (l - k) * α := by
  obtain ⟨hk, hk2, hl2, hl1, hkl⟩ := htriangle
  refine ⟨fun h _ hα ↦ h.exponentSumGrowthExponent_le hα, fun hβ ↦
    ⟨⟨hk, hk2, hl2, hl1, hkl⟩,
      isExponentPairBound_of_forall_exponentSumGrowthExponent_le hk
        (hk2.trans hl2) hβ⟩⟩

/-! ## The set of exponent pairs -/

/-- The set of exponent pairs, as a subset of the plane. -/
def exponentPairs : Set (ℝ × ℝ) := {p | IsExponentPair p.1 p.2}

/-- Membership in the set of exponent pairs. -/
@[simp] theorem mem_exponentPairs {p : ℝ × ℝ} :
    p ∈ exponentPairs ↔ IsExponentPair p.1 p.2 := Iff.rfl

/-- The set of exponent pairs is the intersection of the triangle with the half-planes coming
from the linear bounds on `β`. -/
theorem exponentPairs_eq_inter :
    exponentPairs =
      ({p : ℝ × ℝ | 0 ≤ p.1} ∩ {p : ℝ × ℝ | p.1 ≤ 1 / 2} ∩ {p : ℝ × ℝ | 1 / 2 ≤ p.2} ∩
        {p : ℝ × ℝ | p.2 ≤ 1} ∩ {p : ℝ × ℝ | p.1 + p.2 ≤ 1}) ∩
        ⋂ α : {α : ℝ≥0 // α ≤ 1},
          {p : ℝ × ℝ | exponentSumGrowthExponent α ≤ p.1 + (p.2 - p.1) * ((α : ℝ≥0) : ℝ)} := by
  ext p
  simp only [mem_exponentPairs, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro hp
    exact ⟨⟨⟨⟨⟨hp.k_nonneg, hp.k_le_half⟩, hp.half_le_l⟩, hp.l_le_one⟩, hp.add_le_one⟩,
      fun α ↦ hp.exponentSumGrowthExponent_le α.2⟩
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    exact (isExponentPair_iff_forall_exponentSumGrowthExponent_le
      ⟨h1, h2, h3, h4, h5⟩).2 fun α hα ↦ h6 ⟨α, hα⟩

/-- The set of exponent pairs is closed (blueprint Corollary `exp-pair-closed`). -/
theorem isClosed_exponentPairs : IsClosed exponentPairs := by
  rw [exponentPairs_eq_inter]
  refine IsClosed.inter ?_ (isClosed_iInter fun α ↦ ?_)
  · exact ((((isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_fst continuous_const)).inter
      (isClosed_le continuous_const continuous_snd)).inter
      (isClosed_le continuous_snd continuous_const)).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const)
  · exact isClosed_le continuous_const
      (continuous_fst.add ((continuous_snd.sub continuous_fst).mul continuous_const))

/-- The set of exponent pairs is convex (blueprint Corollary `exp-pair-closed`). -/
theorem convex_exponentPairs : Convex ℝ exponentPairs := by
  have hfst : IsLinearMap ℝ (fun p : ℝ × ℝ ↦ p.1) := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have hsnd : IsLinearMap ℝ (fun p : ℝ × ℝ ↦ p.2) := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  have hadd : IsLinearMap ℝ (fun p : ℝ × ℝ ↦ p.1 + p.2) :=
    ⟨fun p q ↦ by simp [Prod.fst_add, Prod.snd_add]; ring,
      fun c p ↦ by simp [Prod.smul_def]; ring⟩
  have hlin : ∀ t : ℝ, IsLinearMap ℝ (fun p : ℝ × ℝ ↦ p.1 + (p.2 - p.1) * t) := fun t ↦
    ⟨fun p q ↦ by simp [Prod.fst_add, Prod.snd_add]; ring,
      fun c p ↦ by simp [Prod.smul_def]; ring⟩
  rw [exponentPairs_eq_inter]
  refine Convex.inter ?_ (convex_iInter fun α ↦ ?_)
  · exact ((((convex_halfSpace_ge hfst 0).inter
      (convex_halfSpace_le hfst (1 / 2))).inter
      (convex_halfSpace_ge hsnd (1 / 2))).inter
      (convex_halfSpace_le hsnd 1)).inter
      (convex_halfSpace_le hadd 1)
  · exact convex_halfSpace_ge (hlin ((α : ℝ≥0) : ℝ)) (exponentSumGrowthExponent α)

/-! ## The van der Corput transforms -/

/-- The van der Corput `A`-transform `A(k, ℓ) = (k / (2k + 2), ℓ / (2k + 2) + 1/2)`. -/
def vanDerCorputA (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 / (2 * p.1 + 2), p.2 / (2 * p.1 + 2) + 1 / 2)

/-- The van der Corput `B`-transform `B(k, ℓ) = (ℓ - 1/2, k + 1/2)`. -/
def vanDerCorputB (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2 - 1 / 2, p.1 + 1 / 2)

/-- The first coordinate of the van der Corput `A`-transform. -/
@[simp] theorem vanDerCorputA_fst (k l : ℝ) :
    (vanDerCorputA (k, l)).1 = k / (2 * k + 2) := rfl

/-- The second coordinate of the van der Corput `A`-transform. -/
@[simp] theorem vanDerCorputA_snd (k l : ℝ) :
    (vanDerCorputA (k, l)).2 = l / (2 * k + 2) + 1 / 2 := rfl

/-- The first coordinate of the van der Corput `B`-transform. -/
@[simp] theorem vanDerCorputB_fst (k l : ℝ) : (vanDerCorputB (k, l)).1 = l - 1 / 2 := rfl

/-- The second coordinate of the van der Corput `B`-transform. -/
@[simp] theorem vanDerCorputB_snd (k l : ℝ) : (vanDerCorputB (k, l)).2 = k + 1 / 2 := rfl

/-- The van der Corput `A`-transform maps the exponent pair triangle into itself. -/
theorem vanDerCorputA_mem_triangle {k l : ℝ}
    (htriangle : 0 ≤ k ∧ k ≤ 1 / 2 ∧ 1 / 2 ≤ l ∧ l ≤ 1 ∧ k + l ≤ 1) :
    0 ≤ (vanDerCorputA (k, l)).1 ∧ (vanDerCorputA (k, l)).1 ≤ 1 / 2 ∧
      1 / 2 ≤ (vanDerCorputA (k, l)).2 ∧ (vanDerCorputA (k, l)).2 ≤ 1 ∧
      (vanDerCorputA (k, l)).1 + (vanDerCorputA (k, l)).2 ≤ 1 := by
  obtain ⟨hk, hk2, hl2, hl1, hkl⟩ := htriangle
  have hpos : (0 : ℝ) < 2 * k + 2 := by linarith
  have hl0 : (0 : ℝ) ≤ l := by linarith
  have hhalf : l / (2 * k + 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hpos]; linarith
  have hsum : k / (2 * k + 2) + l / (2 * k + 2) = (k + l) / (2 * k + 2) := by ring
  have hsum' : (k + l) / (2 * k + 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hpos]; linarith
  simp only [vanDerCorputA_fst, vanDerCorputA_snd]
  have hl0' : (0 : ℝ) ≤ l / (2 * k + 2) := by positivity
  refine ⟨by positivity, ?_, by linarith, by linarith, by linarith⟩
  rw [div_le_iff₀ hpos]; linarith

/-- The van der Corput `B`-transform maps the exponent pair triangle into itself. -/
theorem vanDerCorputB_mem_triangle {k l : ℝ}
    (htriangle : 0 ≤ k ∧ k ≤ 1 / 2 ∧ 1 / 2 ≤ l ∧ l ≤ 1 ∧ k + l ≤ 1) :
    0 ≤ (vanDerCorputB (k, l)).1 ∧ (vanDerCorputB (k, l)).1 ≤ 1 / 2 ∧
      1 / 2 ≤ (vanDerCorputB (k, l)).2 ∧ (vanDerCorputB (k, l)).2 ≤ 1 ∧
      (vanDerCorputB (k, l)).1 + (vanDerCorputB (k, l)).2 ≤ 1 := by
  obtain ⟨hk, hk2, hl2, hl1, hkl⟩ := htriangle
  refine ⟨by simp; linarith, by simp; linarith, by simp; linarith, by simp; linarith, ?_⟩
  simp only [vanDerCorputB_fst, vanDerCorputB_snd]
  linarith

/-! ## Trivial exponent pairs -/

/-- `(0, 1)` is an exponent pair (blueprint Proposition `exp-pair-trivial`). -/
theorem isExponentPair_zero_one : IsExponentPair 0 1 := by
  refine (isExponentPair_iff_forall_exponentSumGrowthExponent_le (by norm_num)).2 ?_
  intro α _
  simpa using exponentSumGrowthExponent_le_self α

/-- The pair `(1/2, 1/2)` is an exponent pair as soon as `β(α) ≤ 1/2` holds on the upper half
`[1/2, 1]` of the scale range; on the lower half the trivial bound `β(α) ≤ α` suffices. -/
theorem isExponentPair_half_half_of_exponentSumGrowthExponent_le_half
    (hβ : ∀ α : ℝ≥0, 1 / 2 ≤ (α : ℝ) → α ≤ 1 → exponentSumGrowthExponent α ≤ 1 / 2) :
    IsExponentPair (1 / 2) (1 / 2) := by
  refine (isExponentPair_iff_forall_exponentSumGrowthExponent_le (by norm_num)).2 ?_
  intro α hα
  simp only [sub_self, zero_mul, add_zero]
  rcases le_or_gt ((α : ℝ)) (1 / 2) with h | h
  · exact (exponentSumGrowthExponent_le_self α).trans h
  · exact hβ α h.le hα

/-- `(1/2, 1/2)` is an exponent pair (blueprint Proposition `exp-pair-trivial`). -/
theorem isExponentPair_half_half : IsExponentPair (1 / 2) (1 / 2) := by
  apply isExponentPair_half_half_of_exponentSumGrowthExponent_le_half
  intro α hhalf hα
  by_cases hαone : α = 1
  · subst α
    simp
  have hαlt : α < 1 := lt_of_le_of_ne hα hαone
  let γ : ℝ≥0 := 1 - α
  have hγpos : 0 < γ := tsub_pos_of_lt hαlt
  have hαpos : 0 < α := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  have hγlt : γ < 1 := tsub_lt_self (by norm_num) hαpos
  have href := exponentSumGrowthExponent_reflection γ hγpos hγlt
  have hγα : 1 - γ = α := tsub_tsub_cancel_of_le hα
  rw [hγα] at href
  rw [href]
  linarith [exponentSumGrowthExponent_le_self γ]

end Expdb
