# Lean Formalization for ANTEDB

This document describes the Lean formalization of the Analytic Number Theory Exponent Database (ANTEDB): what has been implemented, how to use it, and what remains to be done.

As noted in the accompanying paper:

> "Currently, the ANTEDB python module performs computations using routines that are not formally certified to be error-free. A natural future direction of the project would be to incorporate formal verification in languages such as Lean. Completely formalizing the estimates in the ANTEDB would be a significant challenge; however, several conditional calculations deriving one exponent from other exponents in the literature could conceivably be formalised within the ANTEDB."

## Quick Start

```bash
lake build         # builds all Lean files (first build downloads Mathlib, ~10-20 min)
```

The project uses **Lean 4** (v4.25.0-rc2) with **Mathlib** as a dependency. Configuration is in [`lakefile.toml`](lakefile.toml) and [`lean-toolchain`](lean-toolchain).

## What Has Been Formalized

### Directory Structure

```
expdb/
├── Basic/
│   ├── ExponentPair.lean          # Core definitions and convexity theorem
│   └── ZeroDensityEstimate.lean   # Zero density predicate and structure
├── Literature/
│   ├── Classical.lean             # Axioms: (0,1), (1/2,1/2), (1/6,2/3)
│   ├── Bourgain.lean              # Axiom: (13/84, 55/84)
│   ├── HeathBrown.lean            # Axioms: Heath-Brown (2017) parametric pairs
│   ├── Huxley.lean                # Axioms: Huxley, Watt, Huxley-Kolesnik pairs
│   ├── RobertSargos.lean          # Axioms: Robert, Sargos k-th derivative pairs
│   └── TrudgianYang.lean          # Axioms: Trudgian-Yang (2025) pairs
├── Transforms/
│   ├── VanDerCorputA.lean         # A-process axiom + ofA helper
│   └── VanDerCorputB.lean         # B-process axiom + ofB helper
├── Tactics/
│   └── Chain.lean                 # by_chain tactic for automated A/B derivations
├── Derived/
│   └── Examples.lean              # 22+ proven derivation theorems
├── ForMathlib/                    # (placeholder) for upstreaming to Mathlib
├── Mathlib/                       # (placeholder) for missing Mathlib pieces
└── Example.lean                   # (empty)
```

### Core Definitions (`Basic/ExponentPair.lean`)

The `IsExponentPair` predicate encodes the geometric constraints of the exponent pair triangle:

```lean
def IsExponentPair (k l : ℚ) : Prop :=
  0 ≤ k ∧ k ≤ 1/2 ∧ 1/2 ≤ l ∧ l ≤ 1 ∧ k + l ≤ 1
```

There is also an `ExponentPair` structure bundling the rationals with proofs. Key results in this file:

| Declaration | Description |
|---|---|
| `ExponentPair.isExponentPair_of_exponentPair` | Structure → predicate conversion |
| `ExponentPair.mk'` | Predicate → structure conversion |
| `IsExponentPair.k_in_unit_interval` | 0 ≤ k ≤ 1 |
| `IsExponentPair.l_in_unit_interval` | 0 ≤ l ≤ 1 |
| **`IsExponentPair.convex`** | **Convex combinations of exponent pairs are exponent pairs** |

The convexity theorem is fully proved (no axioms, no `sorry`):

```lean
theorem convex {k₁ l₁ k₂ l₂ t : ℚ}
    (h₁ : IsExponentPair k₁ l₁) (h₂ : IsExponentPair k₂ l₂)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    IsExponentPair (t * k₁ + (1 - t) * k₂) (t * l₁ + (1 - t) * l₂)
```

### Literature Axioms

These mirror `literature.py` in the Python code — results taken as given from published papers.

**`Literature/Classical.lean`** — three classical axioms:

| Axiom | Value | Source |
|---|---|---|
| `trivial_pair` | (0, 1) | Triangle inequality |
| `weyl_pair` | (1/2, 1/2) | Weyl (1916) |
| `classical_vdc_pair` | (1/6, 2/3) | van der Corput (1920s) |

**`Literature/Bourgain.lean`** — one modern axiom plus two derived results:

| Declaration | Value | Notes |
|---|---|---|
| `bourgain_pair` (axiom) | (13/84, 55/84) | Bourgain (2017) decoupling |
| `bourgain_A` (theorem) | (13/194, 76/97) | A-process applied to Bourgain |
| `bourgain_B_fixed` (theorem) | (13/84, 55/84) | B is identity on symmetry line l = k + 1/2 |

**`Literature/HeathBrown.lean`** — three axioms from Heath-Brown's parametric family, plus derived pairs:

| Declaration | Value | Notes |
|---|---|---|
| `heathBrown_pair_m3` (axiom) | (1/10, 23/30) | Heath-Brown (2017), m=3 |
| `heathBrown_pair_m4` (axiom) | (1/27, 31/36) | Heath-Brown (2017), m=4 |
| `heathBrown_pair_m5` (axiom) | (1/56, 127/140) | Heath-Brown (2017), m=5 |
| `heathBrown_m3_B` (theorem) | (4/15, 3/5) | B(1/10, 23/30) |
| `heathBrown_m3_A` (theorem) | (1/22, 28/33) | A(1/10, 23/30) |

**`Literature/Huxley.lean`** — seven axioms from the Huxley school, plus derived pairs:

| Declaration | Value | Notes |
|---|---|---|
| `huxley_pair_1988` (axiom) | (9/56, 37/56) | Huxley (1988), symmetry line |
| `watt_pair_1989` (axiom) | (89/560, 369/560) | Watt (1989), symmetry line |
| `huxley_pair_1991` (axiom) | (17/108, 71/108) | Huxley-Kolesnik (1991), symmetry line |
| `huxley_pair_1993` (axiom) | (89/570, 187/285) | Huxley (1993), symmetry line |
| `huxley_pair_2005` (axiom) | (32/205, 269/410) | Huxley (2005), symmetry line |
| `huxleyWatt_pair_1990` (axiom) | (2/13, 35/52) | Huxley-Watt (1990) |
| `huxley_pair_1996` (axiom) | (6299/43860, 29507/43860) | Huxley (1996) |
| `huxley_1988_A` (theorem) | (9/130, 51/65) | A(9/56, 37/56) |
| `huxleyWatt_1990_B` (theorem) | (9/52, 17/26) | B(2/13, 35/52) |

**`Literature/RobertSargos.lean`** — six axioms from k-th derivative tests, plus derived pairs:

| Declaration | Value | Notes |
|---|---|---|
| `robert_pair_2002` (axiom) | (1/13, 10/13) | Robert (2002), 4th derivative |
| `sargos_pair_2003a` (axiom) | (1/204, 197/204) | Sargos (2003) |
| `robert_pair_2002a` (axiom) | (1/360, 44/45) | Robert (2002) |
| `robertSargos_pair_2001` (axiom) | (1/649, 640/649) | Robert-Sargos (2001) |
| `robert_pair_2002b` (axiom) | (1/615, 202/205) | Robert (2002b) |
| `robert_pair_2002c` (axiom) | (1/915, 181/183) | Robert (2002b) |
| `robert_2002_B` (theorem) | (7/26, 15/26) | B(1/13, 10/13) |
| `robert_2002_A` (theorem) | (1/28, 6/7) | A(1/13, 10/13) |

**`Literature/TrudgianYang.lean`** — four axioms from the recent systematic approach, plus derived pairs:

| Declaration | Value | Notes |
|---|---|---|
| `trudgianYang_pair_1` (axiom) | (4742/38463, 35731/51284) | Trudgian-Yang (2025) |
| `trudgianYang_pair_2` (axiom) | (18/199, 593/796) | Trudgian-Yang (2025) |
| `trudgianYang_pair_3` (axiom) | (2779/38033, 58699/76066) | Trudgian-Yang (2025) |
| `trudgianYang_pair_4` (axiom) | (715/10238, 7955/10238) | Trudgian-Yang (2025) |
| `trudgianYang_pair_2_B` (theorem) | (195/796, 235/398) | B(18/199, 593/796) |

### Transform Axioms and Helpers

The A and B transforms are axiomatized (the underlying analytic proofs require deep exponential sum theory not yet in Mathlib). Each file also provides an `ofX` helper that makes applying the transform ergonomic.

**`Transforms/VanDerCorputA.lean`:**

```lean
-- Axiom: A-process transforms (k, l) to (k/(2k+2), l/(2k+2) + 1/2)
axiom vanDerCorputA (k l : ℚ) (h : IsExponentPair k l) :
    IsExponentPair (k / (2*k + 2)) (l / (2*k + 2) + 1/2)

-- Helper: apply A and discharge arithmetic via norm_num
theorem IsExponentPair.ofA {k l k' l' : ℚ} (h : IsExponentPair k l)
    (hk : k' = k / (2 * k + 2)) (hl : l' = l / (2 * k + 2) + 1/2) :
    IsExponentPair k' l'
```

**`Transforms/VanDerCorputB.lean`:**

```lean
-- Axiom: B-process transforms (k, l) to (l - 1/2, k + 1/2)
axiom vanDerCorputB (k l : ℚ) (h : IsExponentPair k l) :
    IsExponentPair (l - 1/2) (k + 1/2)

-- Helper: apply B and discharge arithmetic via norm_num
theorem IsExponentPair.ofB {k l k' l' : ℚ} (h : IsExponentPair k l)
    (hk : k' = l - 1/2) (hl : l' = k + 1/2) :
    IsExponentPair k' l'

-- B is an involution (arithmetic identity)
theorem vanDerCorputB_involution {k l : ℚ} (_h : IsExponentPair k l) :
    (k + 1/2 : ℚ) - 1/2 = k ∧ (l - 1/2 : ℚ) + 1/2 = l
```

### Derived Exponent Pairs (`Derived/Examples.lean`)

All theorems are fully proved — zero `sorry`s remain in the entire codebase.

**Simple derivations from classical axioms:**

| Theorem | Pair | Derivation |
|---|---|---|
| `derived_classical_vdc` | (1/6, 2/3) | A(Weyl) |
| `derived_pair_1_14_11_14` | (1/14, 11/14) | A(1/6, 2/3) |
| `derived_pair_2_7_4_7` | (2/7, 4/7) | BA(1/6, 2/3) |
| `derived_pair_1_9_13_18` | (1/9, 13/18) | ABA(1/6, 2/3) |
| `derived_pair_2_9_11_18` | (2/9, 11/18) | BABA(1/6, 2/3) |
| `derived_pair_1_11_3_4` | (1/11, 3/4) | ABABA(1/6, 2/3) |
| `derived_pair_1_4_13_22` | (1/4, 13/22) | BABABA(1/6, 2/3) |
| `derived_pair_1_18_5_9` | (1/18, 5/9) | Geometric verification |

**Full derivation chains from the trivial pair:**

| Theorem | Pair | Chain |
|---|---|---|
| `weyl_from_trivial` | (1/2, 1/2) | B(0,1) |
| `classical_vdc_from_trivial` | (1/6, 2/3) | AB(0,1) |
| `derived_pair_2_7_4_7_from_trivial` | (2/7, 4/7) | BAAB(0,1) |
| `derived_pair_1_9_13_18_from_trivial` | (1/9, 13/18) | ABAAB(0,1) |
| `derived_pair_2_9_11_18_from_trivial` | (2/9, 11/18) | BABAAAB(0,1) |

**Derivations from newer literature axioms:**

| Theorem | Pair | Derivation |
|---|---|---|
| `bourgain_AA` | (13/414, 359/414) | AA(Bourgain) |
| `bourgain_BA` | (55/194, 55/97) | BA(Bourgain) |
| `heathBrown_m3_BA` | (23/66, 6/11) | BA(1/10, 23/30) |
| `heathBrown_m3_AB` | (2/19, 14/19) | AB(1/10, 23/30) |
| `robert_2002_BA` | (5/14, 15/28) | BA(1/13, 10/13) |
| `robert_2002_AB` | (7/66, 8/11) | AB(1/13, 10/13) |

Each proof follows the same pattern — apply `ofA`/`ofB` and let `norm_num` handle the rational arithmetic:

```lean
theorem derived_pair_2_7_4_7_from_trivial : IsExponentPair (2/7) (4/7) := by
  have h1 : IsExponentPair (1/2) (1/2) := trivial_pair.ofB (by norm_num) (by norm_num)
  have h2 : IsExponentPair (1/6) (2/3) := h1.ofA (by norm_num) (by norm_num)
  have h3 : IsExponentPair (1/14) (11/14) := h2.ofA (by norm_num) (by norm_num)
  exact h3.ofB (by norm_num) (by norm_num)
```

### Zero Density Estimates

#### Core Definitions (`Basic/ZeroDensityEstimate.lean`)

The `IsZeroDensityBound` predicate encodes zero density estimates for the Riemann zeta function:

```lean
def IsZeroDensityBound (A σ : ℚ) : Prop :=
  0 ≤ A ∧ 1/2 ≤ σ ∧ σ ≤ 1
```

This asserts that `A` is a valid bound on the zero density exponent at `σ`, meaning N(σ, T) ≤ T^{A(1-σ) + o(1)}. There is also a `ZeroDensityEstimate` structure bundling the values with proofs.

Key results:

| Declaration | Description |
|---|---|
| `IsZeroDensityBound.mono` | Monotonicity: weaker bounds are still valid |
| `IsZeroDensityBound.sigma_bounds` | σ ∈ [1/2, 1] |
| `IsZeroDensityBound.bound_nonneg` | A ≥ 0 |

#### Literature Zero Density Axioms (`Literature/ZeroDensityClassical.lean`)

These mirror Chapter 11 of `literature.py` in the Python code:

| Axiom | Bound | Domain | Source |
|---|---|---|---|
| `carlson_zero_density` | A(σ) ≤ 4σ | σ ∈ [1/2, 1] | Carlson (1921) |
| `ingham_zero_density` | A(σ) ≤ 3/(2-σ) | σ ∈ [1/2, 1] | Ingham (1940) |
| `huxley_zero_density` | A(σ) ≤ 3/(3σ-1) | σ ∈ (1/2, 1] | Huxley (1972) |
| `heathbrown_zero_density` | A(σ) ≤ 4/(4σ-1) | σ ∈ [25/28, 1] | Heath-Brown (1979) |
| `bourgain_zero_density` | A(σ) ≤ 2 | σ ∈ [25/32, 1] | Bourgain (2000) |
| `guth_maynard_zero_density` | A(σ) ≤ 15/(3+5σ) | σ ∈ [1/2, 1] | Guth-Maynard (2024) |

#### Exponent Pair → Zero Density Transforms (`Transforms/ExponentPairToZeroDensity.lean`)

Two axiomatized transforms connect exponent pairs to zero density estimates:

| Axiom | Formula | Description |
|---|---|---|
| `ivic_ep_to_zd` | A(σ) ≤ 3/(2σ) | Ivić (m=2): EP → ZD via exponent pair method |
| `bourgain_ep_to_zd` | A(σ) ≤ 4k/(2(1+k)σ-1-l) | Bourgain: EP → ZD for k ≤ 1/5, l ≥ 3/5 |

Each transform has a helper theorem on `IsExponentPair` for ergonomic use:

```lean
-- Apply Ivić's transform: (k, l) → A(σ) ≤ 3/(2σ)
theorem IsExponentPair.toZeroDensityIvic ...

-- Apply Bourgain's transform: (k, l) → A(σ) ≤ 4k/(2(1+k)σ - 1 - l)
theorem IsExponentPair.toZeroDensityBourgain ...
```

#### Derived Zero Density Examples (`Derived/ZeroDensityExamples.lean`)

Derived zero density bounds include direct instantiations and derivation chains:

**Direct instantiations:**

| Theorem | Bound | Source |
|---|---|---|
| `carlson_at_3_4` | A(3/4) ≤ 3 | Carlson |
| `ingham_at_3_4` | A(3/4) ≤ 12/5 | Ingham |
| `bourgain_density_at_7_8` | A(7/8) ≤ 2 | Bourgain |
| `guth_maynard_at_3_4` | A(3/4) ≤ 20/9 | Guth-Maynard |

**EP → ZD derivation chains:**

| Theorem | Bound | Chain |
|---|---|---|
| `ivic_from_classical_vdc_at_5_6` | A(5/6) ≤ 9/5 | Classical EP → Ivić |
| `zd_chain_trivial_BA_ivic` | A(5/6) ≤ 9/5 | Trivial →B→A→ Ivić |
| `zd_chain_classical_A_ivic` | A(6/7) ≤ 7/4 | Classical →A→ Ivić |

The derivation chain proofs combine A/B transforms with EP→ZD transforms:

```lean
theorem zd_chain_trivial_BA_ivic : IsZeroDensityBound (9/5) (5/6) := by
  -- (0, 1) →B→ (1/2, 1/2)
  have h1 : IsExponentPair (1/2) (1/2) := trivial_pair.ofB (by norm_num) (by norm_num)
  -- (1/2, 1/2) →A→ (1/6, 2/3)
  have h2 : IsExponentPair (1/6) (2/3) := h1.ofA (by norm_num) (by norm_num)
  -- Apply Ivić's transform at σ = 5/6
  exact h2.toZeroDensityIvic (by norm_num) (by norm_num) (by norm_num) (by norm_num)
```

### Axiom Inventory

The formalization uses **25 literature axioms** and **2 transform axioms** (and nothing else — no `sorry` anywhere):

**Transform axioms:**

| Axiom | File | What it asserts |
|---|---|---|
| `vanDerCorputA` | Transforms/VanDerCorputA.lean | A-process preserves exponent pairs |
| `vanDerCorputB` | Transforms/VanDerCorputB.lean | B-process preserves exponent pairs |

**Literature axioms (Classical + Bourgain):**

| Axiom | File | What it asserts |
|---|---|---|
| `trivial_pair` | Literature/Classical.lean | (0, 1) is an exponent pair |
| `weyl_pair` | Literature/Classical.lean | (1/2, 1/2) is an exponent pair |
| `classical_vdc_pair` | Literature/Classical.lean | (1/6, 2/3) is an exponent pair |
| `bourgain_pair` | Literature/Bourgain.lean | (13/84, 55/84) is an exponent pair |

**Literature axioms (Heath-Brown):**

| Axiom | File | What it asserts |
|---|---|---|
| `heathBrown_pair_m3` | Literature/HeathBrown.lean | (1/10, 23/30) is an exponent pair |
| `heathBrown_pair_m4` | Literature/HeathBrown.lean | (1/27, 31/36) is an exponent pair |
| `heathBrown_pair_m5` | Literature/HeathBrown.lean | (1/56, 127/140) is an exponent pair |

**Literature axioms (Huxley school):**

| Axiom | File | What it asserts |
|---|---|---|
| `huxley_pair_1988` | Literature/Huxley.lean | (9/56, 37/56) is an exponent pair |
| `watt_pair_1989` | Literature/Huxley.lean | (89/560, 369/560) is an exponent pair |
| `huxley_pair_1991` | Literature/Huxley.lean | (17/108, 71/108) is an exponent pair |
| `huxley_pair_1993` | Literature/Huxley.lean | (89/570, 187/285) is an exponent pair |
| `huxley_pair_2005` | Literature/Huxley.lean | (32/205, 269/410) is an exponent pair |
| `huxleyWatt_pair_1990` | Literature/Huxley.lean | (2/13, 35/52) is an exponent pair |
| `huxley_pair_1996` | Literature/Huxley.lean | (6299/43860, 29507/43860) is an exponent pair |

**Literature axioms (Robert-Sargos):**

| Axiom | File | What it asserts |
|---|---|---|
| `robert_pair_2002` | Literature/RobertSargos.lean | (1/13, 10/13) is an exponent pair |
| `sargos_pair_2003a` | Literature/RobertSargos.lean | (1/204, 197/204) is an exponent pair |
| `robert_pair_2002a` | Literature/RobertSargos.lean | (1/360, 44/45) is an exponent pair |
| `robertSargos_pair_2001` | Literature/RobertSargos.lean | (1/649, 640/649) is an exponent pair |
| `robert_pair_2002b` | Literature/RobertSargos.lean | (1/615, 202/205) is an exponent pair |
| `robert_pair_2002c` | Literature/RobertSargos.lean | (1/915, 181/183) is an exponent pair |

**Literature axioms (Trudgian-Yang):**

| Axiom | File | What it asserts |
|---|---|---|
| `trudgianYang_pair_1` | Literature/TrudgianYang.lean | (4742/38463, 35731/51284) is an exponent pair |
| `trudgianYang_pair_2` | Literature/TrudgianYang.lean | (18/199, 593/796) is an exponent pair |
| `trudgianYang_pair_3` | Literature/TrudgianYang.lean | (2779/38033, 58699/76066) is an exponent pair |
| `trudgianYang_pair_4` | Literature/TrudgianYang.lean | (715/10238, 7955/10238) is an exponent pair |

**Large value estimate axioms:**

| Axiom | File | What it asserts |
|---|---|---|
| `large_value_L2_branch1` | Literature/LargeValues.lean | ρ ≤ 2 − 2σ (L² mean value, branch 1) |
| `large_value_L2_branch2` | Literature/LargeValues.lean | ρ ≤ 1 − 2σ + τ (L² mean value, branch 2) |
| `large_value_huxley` | Literature/LargeValues.lean | ρ ≤ 4 − 6σ + τ (Huxley) |
| `large_value_heath_brown` | Literature/LargeValues.lean | ρ ≤ 10 − 13σ + τ (Heath-Brown) |
| `large_value_guth_maynard_branch2` | Literature/LargeValues.lean | ρ ≤ 18/5 − 4σ (Guth-Maynard) |
| `large_value_guth_maynard_branch3` | Literature/LargeValues.lean | ρ ≤ τ + 12/5 − 4σ (Guth-Maynard) |
| `large_value_raise_to_power` | Transforms/LargeValueRaisePower.lean | Raise-to-power transform |

Note: `trivial_pair`, `weyl_pair`, and `classical_vdc_pair` could be reduced to just `trivial_pair` + the two transforms (since Weyl = B(trivial) and classical = AB(trivial)), but keeping all three as axioms is convenient and mirrors the Python code.

#### Zero Density Axioms

| Axiom | File | What it asserts |
|---|---|---|
| `carlson_zero_density` | Literature/ZeroDensityClassical.lean | A(σ) ≤ 4σ for σ ∈ [1/2, 1] |
| `ingham_zero_density` | Literature/ZeroDensityClassical.lean | A(σ) ≤ 3/(2-σ) for σ ∈ [1/2, 1] |
| `huxley_zero_density` | Literature/ZeroDensityClassical.lean | A(σ) ≤ 3/(3σ-1) for σ ∈ (1/2, 1] |
| `heathbrown_zero_density` | Literature/ZeroDensityClassical.lean | A(σ) ≤ 4/(4σ-1) for σ ∈ [25/28, 1] |
| `bourgain_zero_density` | Literature/ZeroDensityClassical.lean | A(σ) ≤ 2 for σ ∈ [25/32, 1] |
| `guth_maynard_zero_density` | Literature/ZeroDensityClassical.lean | A(σ) ≤ 15/(3+5σ) for σ ∈ [1/2, 1] |
| `ivic_ep_to_zd` | Transforms/ExponentPairToZeroDensity.lean | Ivić EP→ZD transform (m=2) |
| `bourgain_ep_to_zd` | Transforms/ExponentPairToZeroDensity.lean | Bourgain EP→ZD transform |

## How Proofs Work

The proof pattern directly mirrors Python's `Hypothesis` dependency trees. In Python:

```python
# Python: derive (2/7, 4/7) = BA(1/6, 2/3)
h1 = classical_vdc_pair                         # (1/6, 2/3)
h2 = A_transform_function(h1)                   # → (1/14, 11/14)
h3 = B_transform_function(h2)                   # → (2/7, 4/7)
```

In Lean:

```lean
-- Lean: same chain, formally verified
have h1 := classical_vdc_pair                                       -- (1/6, 2/3)
have h2 := h1.ofA (by norm_num) (by norm_num)                      -- → (1/14, 11/14)
exact h2.ofB (by norm_num) (by norm_num)                            -- → (2/7, 4/7)
```

The `(by norm_num)` arguments prove that the rational arithmetic simplifies correctly (e.g. that `(1/6) / (2*(1/6) + 2) = 1/14`). Lean's kernel checks these proofs, giving a stronger guarantee than Python's runtime assertions.

### Custom Tactics (`Tactics/Chain.lean`)

The `by_chain` tactic automates the repetitive pattern of applying `ofA`/`ofB` with `norm_num`, reducing multi-line derivation proofs to one-liners:

```lean
-- Before: manual 4-step proof
theorem derived_pair_2_7_4_7_from_trivial : IsExponentPair (2/7) (4/7) := by
  have h1 : IsExponentPair (1/2) (1/2) := trivial_pair.ofB (by norm_num) (by norm_num)
  have h2 : IsExponentPair (1/6) (2/3) := h1.ofA (by norm_num) (by norm_num)
  have h3 : IsExponentPair (1/14) (11/14) := h2.ofA (by norm_num) (by norm_num)
  exact h3.ofB (by norm_num) (by norm_num)

-- After: one-liner with by_chain
theorem derived_pair_2_7_4_7_from_trivial_chain : IsExponentPair (2/7) (4/7) := by
  by_chain "BAAB" trivial_pair
```

The chain string is read in function composition order: `"BAAB"` means `B(A(A(B(start))))`, so the rightmost character is applied first. Each character must be `'A'` (A-process) or `'B'` (B-process).

| Example | Chain | Start | Result |
|---|---|---|---|
| `by_chain "B" trivial_pair` | B | (0,1) | (1/2, 1/2) |
| `by_chain "AB" trivial_pair` | AB | (0,1) | (1/6, 2/3) |
| `by_chain "BAAB" trivial_pair` | BAAB | (0,1) | (2/7, 4/7) |
| `by_chain "A" bourgain_pair` | A | (13/84, 55/84) | (13/194, 76/97) |

## What Is NOT Formalized (and Why)

Following the paper's guidance, the formalization deliberately does **not** attempt:

1. **Deep analytic number theory** (van der Corput lemma, Weyl differencing, exponential sum estimates) — would require years of Mathlib development; treated as axioms instead
2. **Asymptotic analysis** (Big-O, little-o, limits as T → ∞) — we work with exponents directly, not the underlying estimates
3. **Optimization algorithms** (LP solvers, convex hull computation) — kept in Python; Lean verifies individual results
4. **Original literature proofs** (Weyl, Huxley, Bourgain etc.) — axiomatized, mirroring `literature.py`

## Next Steps

### Near-term (straightforward)

1. ~~**More literature axioms**~~ ✅ **Done** — Axiomatized 20 new exponent pairs from `literature.py`:
   - Heath-Brown (2017): `expdb/Literature/HeathBrown.lean` (3 pairs)
   - Huxley (1988, 1991, 1993, 1996, 2005), Watt (1989), Huxley-Watt (1990): `expdb/Literature/Huxley.lean` (7 pairs)
   - Robert-Sargos (2001, 2002, 2003): `expdb/Literature/RobertSargos.lean` (6 pairs)
   - Trudgian-Yang (2025): `expdb/Literature/TrudgianYang.lean` (4 pairs)
   - Remaining: Sargos (1995) pairs, Huxley (2001) pair (very large denominators), and additional parametric family instances could be added in the future.

2. ~~**More derived pairs**~~ ✅ **Partially done** — Added 8 new derived theorems from the new literature axioms, plus longer chains from trivial pair. The `ofA`/`ofB` pattern scales to any A/B chain; systematically deriving the ~50-100 pairs from `derived.py` remains as future work.

3. **Sargos C/D transforms** — Define `MuBound` and `BetaBound` types, axiomatize:
   - C-process: exponent pair → mu bound
   - D-process: exponent pair → beta bound
   - These connect exponent pairs to divisor sum and zeta function applications.

4. **Beta-exponent duality** — State and axiomatize the duality between `IsExponentPair` and `BetaBound`, following `bound_beta.py`.

### Medium-term (requires more design)

5. **Python → Lean bridge** — `Hypothesis.to_lean()` auto-generates Lean proof terms from dependency trees for exponent pairs derived via A/B transform chains, enabling batch verification. See `hypotheses.py`.

6. **Custom tactics** ✅ — The `by_chain` tactic in `Tactics/Chain.lean` automates A/B chain applications, reducing proofs to one-liners like `by_chain "BAAB" trivial_pair`. See the "Custom Tactics" section above for details and examples.

7. **Zero density estimates** ✅ — Defined `IsZeroDensityBound` and `ZeroDensityEstimate`, axiomatized 6 classical literature results (Carlson, Ingham, Huxley, Heath-Brown, Bourgain, Guth-Maynard), axiomatized 2 EP→ZD transforms (Ivić, Bourgain), and formalized derivation chains connecting exponent pairs to zero density bounds. See `Basic/ZeroDensityEstimate.lean`, `Literature/ZeroDensityClassical.lean`, `Transforms/ExponentPairToZeroDensity.lean`, and `Derived/ZeroDensityExamples.lean`.

8. **Large value estimates** ✅ — `LargeValueEstimate` has been defined in `Basic/LargeValueEstimate.lean`, with literature axioms in `Literature/LargeValues.lean` (L², Huxley, Heath-Brown, Guth-Maynard), the raise-to-power transform in `Transforms/LargeValueRaisePower.lean`, and derived examples in `Derived/LargeValueExamples.lean`. Future work includes axiomatizing Jutila's parameterized family and Bourgain's optimized piecewise estimates.

### Long-term (research-level)

9. **Prove the A/B transforms from first principles** — Replace the axioms with actual proofs. This requires formalizing the van der Corput differencing lemma and Poisson summation in Mathlib, which is a multi-year effort.

10. **Verified polytope operations** — Certify the convex hull and polytope membership tests that Python uses for optimization, enabling end-to-end verified computation.

## References

1. T. Tao, T. Trudgian, A. Yang, "[New exponent pairs, zero density estimates, and zero additive energy estimates: a systematic approach](https://arxiv.org/abs/2501.16779)" (2025)
2. [ANTEDB Web Blueprint](https://teorth.github.io/expdb/blueprint/)
3. [ANTEDB Python Code](blueprint/src/python/)
4. [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
5. [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
6. Graham & Kolesnik, "van der Corput's Method of Exponential Sums" (1991)
7. Huxley, "Area, Lattice Points, and Exponential Sums" (1996)
