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
│   └── ExponentPair.lean          # Core definitions and convexity theorem
├── Literature/
│   ├── Classical.lean             # Axioms: (0,1), (1/2,1/2), (1/6,2/3)
│   └── Bourgain.lean              # Axiom: (13/84, 55/84)
├── Transforms/
│   ├── VanDerCorputA.lean         # A-process axiom + ofA helper
│   └── VanDerCorputB.lean         # B-process axiom + ofB helper
├── Derived/
│   └── Examples.lean              # 14 proven derivation theorems
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

All 14 theorems are fully proved — zero `sorry`s remain in the entire codebase.

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

Each proof follows the same pattern — apply `ofA`/`ofB` and let `norm_num` handle the rational arithmetic:

```lean
theorem derived_pair_2_7_4_7_from_trivial : IsExponentPair (2/7) (4/7) := by
  have h1 : IsExponentPair (1/2) (1/2) := trivial_pair.ofB (by norm_num) (by norm_num)
  have h2 : IsExponentPair (1/6) (2/3) := h1.ofA (by norm_num) (by norm_num)
  have h3 : IsExponentPair (1/14) (11/14) := h2.ofA (by norm_num) (by norm_num)
  exact h3.ofB (by norm_num) (by norm_num)
```

### Axiom Inventory

The formalization uses exactly **5 axioms** (and nothing else — no `sorry` anywhere):

| Axiom | File | What it asserts |
|---|---|---|
| `trivial_pair` | Literature/Classical.lean | (0, 1) is an exponent pair |
| `weyl_pair` | Literature/Classical.lean | (1/2, 1/2) is an exponent pair |
| `classical_vdc_pair` | Literature/Classical.lean | (1/6, 2/3) is an exponent pair |
| `bourgain_pair` | Literature/Bourgain.lean | (13/84, 55/84) is an exponent pair |
| `vanDerCorputA` | Transforms/VanDerCorputA.lean | A-process preserves exponent pairs |
| `vanDerCorputB` | Transforms/VanDerCorputB.lean | B-process preserves exponent pairs |

Note: `trivial_pair`, `weyl_pair`, and `classical_vdc_pair` could be reduced to just `trivial_pair` + the two transforms (since Weyl = B(trivial) and classical = AB(trivial)), but keeping all three as axioms is convenient and mirrors the Python code.

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

## What Is NOT Formalized (and Why)

Following the paper's guidance, the formalization deliberately does **not** attempt:

1. **Deep analytic number theory** (van der Corput lemma, Weyl differencing, exponential sum estimates) — would require years of Mathlib development; treated as axioms instead
2. **Asymptotic analysis** (Big-O, little-o, limits as T → ∞) — we work with exponents directly, not the underlying estimates
3. **Optimization algorithms** (LP solvers, convex hull computation) — kept in Python; Lean verifies individual results
4. **Original literature proofs** (Weyl, Huxley, Bourgain etc.) — axiomatized, mirroring `literature.py`

## Next Steps

### Near-term (straightforward)

1. **More literature axioms** — Axiomatize the ~25 exponent pairs from `literature.py`:
   - Heath-Brown (1979): `expdb/Literature/HeathBrown.lean`
   - Huxley (1988, 1993, 1996, 2005): `expdb/Literature/Huxley.lean`
   - Robert-Sargos (2001, 2002, 2003): `expdb/Literature/RobertSargos.lean`
   - Trudgian-Yang (2025): `expdb/Literature/TrudgianYang.lean`

2. **More derived pairs** — The `ofA`/`ofB` pattern scales to any A/B chain. Systematically derive the ~50-100 pairs that Python computes in `derived.py`.

3. **Sargos C/D transforms** — Define `MuBound` and `BetaBound` types, axiomatize:
   - C-process: exponent pair → mu bound
   - D-process: exponent pair → beta bound
   - These connect exponent pairs to divisor sum and zeta function applications.

4. **Beta-exponent duality** — State and axiomatize the duality between `IsExponentPair` and `BetaBound`, following `bound_beta.py`.

### Medium-term (requires more design)

5. **Python → Lean bridge** — `Hypothesis.to_lean()` auto-generates Lean proof terms from dependency trees for exponent pairs derived via A/B transform chains, enabling batch verification. See `hypotheses.py`.

6. **Custom tactics** — Build `apply_chain` or similar tactics to automate A/B chain applications, reducing proofs to one-liners like `exact by_chain "BAAB" trivial_pair`.

7. **Zero density estimates** — Define `ZeroDensityEstimate` and axiomatize key results from `zero_density_estimate.py`, then formalize the derivation chains that connect zero density to exponent pairs.

8. **Large value estimates** — Define `LargeValueEstimate` following `large_values.py` and axiomatize the transforms that connect these to other exponents.

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
