module

public import Expdb.LargeValues.Patterns
public import Expdb.Basic.PowerAsymptotics
public import Mathlib.Data.EReal.Basic

/-!
# Large value exponents

Sequence-based admissibility from `lv-def` and `lvz-def`. The zeta exponent takes values
in `EReal`: an empty asymptotic regime can have exponent `−∞`.
-/

@[expose] public section

open Filter Topology
open scoped Expdb

noncomputable section

namespace Expdb

/-- The universal cardinality bound for general patterns (`lv-def`). -/
def IsLargeValueBound (σ τ ρ : ℝ) : Prop :=
  ∀ (N T V : VariableObject ℝ) (a : VariableObject (ℕ → ℂ))
    (u : VariableObject ℝ) (W : VariableObject (Finset ℝ)),
    (∀ i, IsLargeValuePattern (N i) (T i) (V i) (a i) (u i) (W i)) →
    N.IsUnbounded → IsPowerAsymptotic T N τ → IsPowerAsymptotic V N σ →
    IsPowerBounded (fun i => ((W i).card : ℝ)) N ρ

/-- The universal cardinality bound for zeta patterns (`lvz-def`). -/
def IsZetaLargeValueBound (σ τ ρ : ℝ) : Prop :=
  ∀ (N T V : VariableObject ℝ) (a : VariableObject (ℕ → ℂ))
    (u : VariableObject ℝ) (W : VariableObject (Finset ℝ)),
    (∀ i, IsZetaLargeValuePattern (N i) (T i) (V i) (a i) (u i) (W i)) →
    N.IsUnbounded → IsPowerAsymptotic T N τ → IsPowerAsymptotic V N σ →
    IsPowerBounded (fun i => ((W i).card : ℝ)) N ρ

/-- Candidate exponents for general large values. -/
def largeValueBounds (σ τ : ℝ) : Set ℝ := {ρ | IsLargeValueBound σ τ ρ}

/-- Candidate exponents for zeta large values. -/
def zetaLargeValueBounds (σ τ : ℝ) : Set ℝ := {ρ | IsZetaLargeValueBound σ τ ρ}

/-- The real infimum defining `LV(σ,τ)` (`lv-def`). Its least-bound interpretation is
asserted on the blueprint domain `1/2 ≤ σ ≤ 1`, `0 ≤ τ`. -/
def largeValueExponent (σ τ : ℝ) : ℝ := sInf (largeValueBounds σ τ)

/-- The extended-real infimum defining `LVζ(σ,τ)` (`lvz-def`). -/
def zetaLargeValueExponent (σ τ : ℝ) : EReal :=
  sInf ((fun ρ : ℝ => (ρ : EReal)) '' zetaLargeValueBounds σ τ)

@[simp] theorem mem_largeValueBounds {σ τ ρ : ℝ} :
    ρ ∈ largeValueBounds σ τ ↔ IsLargeValueBound σ τ ρ := Iff.rfl

@[simp] theorem mem_zetaLargeValueBounds {σ τ ρ : ℝ} :
    ρ ∈ zetaLargeValueBounds σ τ ↔ IsZetaLargeValueBound σ τ ρ := Iff.rfl

/-- A general bound also bounds zeta patterns. -/
theorem IsLargeValueBound.toZeta {σ τ ρ : ℝ} (h : IsLargeValueBound σ τ ρ) :
    IsZetaLargeValueBound σ τ ρ := by
  intro N T V a u W hp hN hT hV
  exact h N T V a u W (fun i => (hp i).1) hN hT hV

/-- Admissibility is upward closed in the cardinality exponent. -/
theorem IsLargeValueBound.mono {σ τ ρ ρ' : ℝ} (h : IsLargeValueBound σ τ ρ)
    (hle : ρ ≤ ρ') : IsLargeValueBound σ τ ρ' := by
  intro N T V a u W hp hN hT hV
  exact (h N T V a u W hp hN hT hV).mono
    (Eventually.of_forall fun i => (hp i).1.le) hle

/-- Zeta admissibility is upward closed in the cardinality exponent. -/
theorem IsZetaLargeValueBound.mono {σ τ ρ ρ' : ℝ} (h : IsZetaLargeValueBound σ τ ρ)
    (hle : ρ ≤ ρ') : IsZetaLargeValueBound σ τ ρ' := by
  intro N T V a u W hp hN hT hV
  exact (h N T V a u W hp hN hT hV).mono
    (Eventually.of_forall fun i => (hp i).1.1.le) hle

/-- The observation interval supplies the trivial exponent `τ`. -/
theorem isLargeValueBound_tau (σ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsLargeValueBound σ τ τ := by
  intro N T V a u W hp hN hT _
  have hN1 : ∀ i, 1 ≤ N i := fun i => (hp i).1.le
  apply (isPowerBounded_iff_forall_pos _ N τ hN1 hN).2
  intro ε hε
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [hT.eventually_between (Eventually.of_forall hN1) hε] with i hi
  have hcard := card_le_length_add_one (hp i).2.1.le
    (hp i).2.2.2.2.1 (hp i).2.2.2.2.2.1
  have hpow : 1 ≤ N i ^ (τ + ε) := Real.one_le_rpow (hN1 i) (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hN1 i]) _)]
  linarith [hi.2]

/-- Candidates approach any limiting admissible exponent from above. -/
theorem isLargeValueBound_of_forall_gt {σ τ ρ : ℝ}
    (h : ∀ ρ', ρ < ρ' → IsLargeValueBound σ τ ρ') : IsLargeValueBound σ τ ρ := by
  intro N T V a u W hp hN hT hV
  exact IsPowerBounded.of_forall_gt (fun i => (hp i).1.le) hN
    (fun ρ' hρ' => h ρ' hρ' N T V a u W hp hN hT hV)

/-- Underspill for zeta cardinality exponents. -/
theorem isZetaLargeValueBound_of_forall_gt {σ τ ρ : ℝ}
    (h : ∀ ρ', ρ < ρ' → IsZetaLargeValueBound σ τ ρ') : IsZetaLargeValueBound σ τ ρ := by
  intro N T V a u W hp hN hT hV
  exact IsPowerBounded.of_forall_gt (fun i => (hp i).1.1.le) hN
    (fun ρ' hρ' => h ρ' hρ' N T V a u W hp hN hT hV)

/-- General candidate sets are closed without restrictions on the scale parameters. -/
theorem isClosed_largeValueBounds (σ τ : ℝ) : IsClosed (largeValueBounds σ τ) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro ρ hρ
  have hnot : ¬ IsLargeValueBound σ τ ρ := hρ
  have hbad : ∃ ρ' : ℝ, ρ < ρ' ∧ ¬ IsLargeValueBound σ τ ρ' := by
    by_contra h
    push Not at h
    exact hnot (isLargeValueBound_of_forall_gt h)
  obtain ⟨ρ', hlt, hb⟩ := hbad
  apply Filter.mem_of_superset (Iio_mem_nhds hlt)
  intro x hx
  exact fun h => hb (h.mono hx.le)

/-- Zeta candidate sets are closed, including regimes with exponent `−∞`. -/
theorem isClosed_zetaLargeValueBounds (σ τ : ℝ) :
    IsClosed (zetaLargeValueBounds σ τ) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro ρ hρ
  have hnot : ¬ IsZetaLargeValueBound σ τ ρ := hρ
  have hbad : ∃ ρ' : ℝ, ρ < ρ' ∧ ¬ IsZetaLargeValueBound σ τ ρ' := by
    by_contra h
    push Not at h
    exact hnot (isZetaLargeValueBound_of_forall_gt h)
  obtain ⟨ρ', hlt, hb⟩ := hbad
  apply Filter.mem_of_superset (Iio_mem_nhds hlt)
  intro x hx
  exact fun h => hb (h.mono hx.le)

/-- A real zeta candidate bounds the extended-real infimum. -/
theorem zetaLargeValueExponent_le_of_bound {σ τ ρ : ℝ}
    (h : IsZetaLargeValueBound σ τ ρ) : zetaLargeValueExponent σ τ ≤ (ρ : EReal) :=
  sInf_le ⟨ρ, h, rfl⟩

/-- The extended-real definition has exactly the intended real upper bounds. -/
theorem zetaLargeValueExponent_le_iff {σ τ ρ : ℝ} :
    zetaLargeValueExponent σ τ ≤ (ρ : EReal) ↔ IsZetaLargeValueBound σ τ ρ := by
  constructor
  · intro h
    apply isZetaLargeValueBound_of_forall_gt
    intro ρ' hρ'
    have hinf : zetaLargeValueExponent σ τ < (ρ' : EReal) :=
      h.trans_lt (EReal.coe_lt_coe_iff.mpr hρ')
    obtain ⟨b, hb, hblt⟩ := (sInf_lt_iff).mp hinf
    obtain ⟨β, hβ, rfl⟩ := hb
    exact hβ.mono (EReal.coe_lt_coe_iff.mp hblt).le
  · exact zetaLargeValueExponent_le_of_bound

/-- Zeta large value exponents are finite above on the intended domain. -/
theorem zetaLargeValueExponent_le_tau (σ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    zetaLargeValueExponent σ τ ≤ (τ : EReal) :=
  zetaLargeValueExponent_le_of_bound (isLargeValueBound_tau σ hτ).toZeta

/-- There is no `+∞` zeta exponent when `τ ≥ 0`. -/
theorem zetaLargeValueExponent_ne_top (σ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    zetaLargeValueExponent σ τ ≠ ⊤ :=
  (lt_of_le_of_lt (zetaLargeValueExponent_le_tau σ hτ) (EReal.coe_lt_top τ)).ne

/-- The exponent is `−∞` exactly when every real exponent is admissible. -/
theorem zetaLargeValueExponent_eq_bot_iff {σ τ : ℝ} :
    zetaLargeValueExponent σ τ = ⊥ ↔ ∀ ρ : ℝ, IsZetaLargeValueBound σ τ ρ := by
  constructor
  · intro h ρ
    apply zetaLargeValueExponent_le_iff.mp
    rw [h]
    exact bot_le
  · intro h
    apply eq_bot_iff.mpr
    by_contra hnot
    obtain ⟨ρ, hρ⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
    exact (not_lt_of_ge (zetaLargeValueExponent_le_of_bound (h ρ))) hρ.2

/-- Singleton patterns at height zero rule out negative general exponents. -/
theorem IsLargeValueBound.nonneg {σ τ ρ : ℝ} (hσ : σ ≤ 1)
    (h : IsLargeValueBound σ τ ρ) : 0 ≤ ρ := by
  classical
  let N : VariableObject ℝ := fun i => (i : ℝ) + 2
  let T : VariableObject ℝ := fun i => N i ^ τ
  let V : VariableObject ℝ := fun i => N i ^ σ
  have hN : ∀ i, 1 < N i := by intro i; dsimp [N]; linarith [Nat.cast_nonneg (α := ℝ) i]
  have hNtop : Tendsto N atTop atTop := by
    apply tendsto_atTop_mono (fun i : ℕ => show (i : ℝ) ≤ N i by dsimp [N]; linarith)
    exact tendsto_natCast_atTop_atTop
  have hNunbounded : N.IsUnbounded :=
    (VariableObject.isUnbounded_iff_tendsto_atTop (fun i => (hN i).le.trans' zero_le_one)).2 hNtop
  have hp : ∀ i, IsLargeValuePattern (N i) (T i) (V i) (fun _ => 1) 0 {0} := by
    intro i
    have hN0 : 0 < N i := zero_lt_one.trans (hN i)
    refine ⟨hN i, Real.rpow_pos_of_pos hN0 _, Real.rpow_pos_of_pos hN0 _,
      ?_, ?_, ?_, ?_⟩
    · intro n hn; simp
    · intro t ht
      simp only [Finset.mem_singleton] at ht
      subst t
      simp [T, (Real.rpow_pos_of_pos hN0 τ).le]
    · intro x y hxy
      have hx : (x : ℝ) = 0 := Finset.mem_singleton.mp x.property
      have hy : (y : ℝ) = 0 := Finset.mem_singleton.mp y.property
      exact False.elim (hxy (Subtype.ext (hx.trans hy.symm)))
    · intro t ht
      simp only [Finset.mem_singleton] at ht
      subst t
      have hind : dyadicIndices (N i) = Finset.Icc (i + 2) (2 * (i + 2)) := by
        unfold dyadicIndices N
        have hcast : (i : ℝ) + 2 = ((i + 2 : ℕ) : ℝ) := by push_cast; ring
        rw [hcast, show 2 * ((i + 2 : ℕ) : ℝ) = ((2 * (i + 2) : ℕ) : ℝ) by push_cast; ring]
        simp only [Nat.ceil_natCast, Nat.floor_natCast]
      have hpoly : ‖dirichletPolynomial (N i) (fun _ => 1) 0‖ = (i : ℝ) + 3 := by
        simp [dirichletPolynomial, hind, Nat.card_Icc]
        norm_cast
        omega
      rw [hpoly]
      have hV : V i ≤ N i := by
        dsimp [V]
        simpa using Real.rpow_le_rpow_of_exponent_le (hN i).le hσ
      dsimp [N] at hV
      linarith
  have hT : IsPowerAsymptotic T N τ :=
    ⟨VariableObject.fixed τ, IsEqUpToInfinitesimal.refl _, Eventually.of_forall fun _ => rfl⟩
  have hV : IsPowerAsymptotic V N σ :=
    ⟨VariableObject.fixed σ, IsEqUpToInfinitesimal.refl _, Eventually.of_forall fun _ => rfl⟩
  have hb := h N T V (fun _ _ => 1) (fun _ => 0) (fun _ => {0}) hp hNunbounded hT hV
  apply exponent_le_of_isPowerBounded_of_eventually_norm_ge_rpow
    (fun i => (hN i).le) hNunbounded hb zero_lt_one
  exact Eventually.of_forall fun i => by simp

/-- General candidate sets are nonempty when `τ ≥ 0`. -/
theorem largeValueBounds_nonempty (σ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    (largeValueBounds σ τ).Nonempty := ⟨τ, isLargeValueBound_tau σ hτ⟩

/-- General candidate exponents have a lower bound on the blueprint domain. -/
theorem largeValueBounds_bddBelow {σ : ℝ} (hσ : σ ≤ 1) (τ : ℝ) :
    BddBelow (largeValueBounds σ τ) := ⟨0, fun _ h => h.nonneg hσ⟩

/-- The infimum is an admissible general exponent. -/
theorem isLargeValueBound_largeValueExponent {σ τ : ℝ} (_hσ : σ ≤ 1) (hτ : 0 ≤ τ) :
    IsLargeValueBound σ τ (largeValueExponent σ τ) := by
  apply isLargeValueBound_of_forall_gt
  intro ρ hρ
  obtain ⟨β, hβ, hβρ⟩ := exists_lt_of_csInf_lt (largeValueBounds_nonempty σ hτ) hρ
  exact hβ.mono hβρ.le

/-- The defining least-bound characterisation of `LV`. -/
theorem largeValueExponent_le_iff {σ τ ρ : ℝ} (hσ : σ ≤ 1) (hτ : 0 ≤ τ) :
    largeValueExponent σ τ ≤ ρ ↔ IsLargeValueBound σ τ ρ := by
  constructor
  · exact fun h => (isLargeValueBound_largeValueExponent hσ hτ).mono h
  · exact fun h => csInf_le (largeValueBounds_bddBelow hσ τ) h

/-- The general exponent is the least candidate. -/
theorem isLeast_largeValueExponent {σ τ : ℝ} (hσ : σ ≤ 1) (hτ : 0 ≤ τ) :
    IsLeast (largeValueBounds σ τ) (largeValueExponent σ τ) :=
  ⟨isLargeValueBound_largeValueExponent hσ hτ,
    fun _ h => (largeValueExponent_le_iff hσ hτ).mpr h⟩

/-- The trivial upper bound for the real general exponent. -/
theorem largeValueExponent_le_tau {σ τ : ℝ} (hσ : σ ≤ 1) (hτ : 0 ≤ τ) :
    largeValueExponent σ τ ≤ τ :=
  (largeValueExponent_le_iff hσ hτ).mpr (isLargeValueBound_tau σ hτ)

/-- General large value exponents are nonnegative. -/
theorem largeValueExponent_nonneg {σ τ : ℝ} (hσ : σ ≤ 1) (hτ : 0 ≤ τ) :
    0 ≤ largeValueExponent σ τ := (isLargeValueBound_largeValueExponent hσ hτ).nonneg hσ

/-- At scale exponent zero, general large value exponents vanish (`lv-basic`, part iii). -/
@[simp] theorem largeValueExponent_zero {σ : ℝ} (hσ : σ ≤ 1) :
    largeValueExponent σ 0 = 0 :=
  le_antisymm (largeValueExponent_le_tau hσ le_rfl) (largeValueExponent_nonneg hσ le_rfl)

/-- Specialising coefficients can only improve the large value exponent. -/
theorem zetaLargeValueExponent_le_largeValueExponent {σ τ : ℝ}
    (hσ : σ ≤ 1) (hτ : 0 ≤ τ) :
    zetaLargeValueExponent σ τ ≤ (largeValueExponent σ τ : EReal) :=
  zetaLargeValueExponent_le_of_bound (isLargeValueBound_largeValueExponent hσ hτ).toZeta

end Expdb
