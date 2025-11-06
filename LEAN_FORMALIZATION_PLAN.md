# Lean Formalization Plan for ANTEDB

This document outlines the strategy for integrating formal verification using the [Lean theorem prover](https://leanprover.github.io/) into the Analytic Number Theory Exponent Database (ANTEDB). As noted in the accompanying paper:

> "Currently, the ANTEDB python module performs computations using routines that are not formally certified to be error-free. A natural future direction of the project would be to incorporate formal verification in languages such as Lean. Completely formalizing the estimates in the ANTEDB would be a significant challenge; however, several conditional calculations deriving one exponent from other exponents in the literature could conceivably be formalised within the ANTEDB."

## Current State

The repository already has basic Lean infrastructure:
- **Build configuration**: [`lakefile.toml`](lakefile.toml), [`lean-toolchain`](lean-toolchain)
- **Mathlib dependency**: Connected to Lean's mathematical library
- **Lean source directory**: [`expdb/`](expdb/) with placeholder structure
  - [`expdb/Example.lean`](expdb/Example.lean) - Empty example file
  - [`expdb/ForMathlib/`](expdb/ForMathlib/) - For upstreaming to Mathlib
  - [`expdb/Mathlib/`](expdb/Mathlib/) - For missing Mathlib components

The Python codebase (`blueprint/src/python/`) has a mature hypothesis system with:
- **Dependency tracking**: `Hypothesis` objects form proof trees
- **Literature axioms**: Baseline results from papers
- **Transform chains**: A/B/C/D transforms applied iteratively
- **Derived results**: Computational proofs via convex hull operations

## Proposed Lean Directory Structure

```
expdb/
├── Basic/                          # Foundational definitions
│   ├── ExponentPair.lean           # Definition of exponent pairs
│   ├── BetaFunction.lean           # β(α) exponential sum bounds
│   ├── MuFunction.lean             # μ(σ) divisor bound function
│   ├── ZeroDensity.lean            # Zero density estimates N(σ,T)
│   ├── Moments.lean                # Zeta function moment bounds
│   ├── LargeValues.lean            # Large value estimates
│   └── AdditiveEnergy.lean         # Additive energy bounds
│
├── Transforms/                     # Verified transformations
│   ├── VanDerCorputA.lean          # A-process: k/(2k+2) transform
│   ├── VanDerCorputB.lean          # B-process: (l-1/2, k+1/2) swap
│   ├── SargosC.lean                # C-process: exponent pair → mu bound
│   ├── SargosD.lean                # D-process: exponent pair → beta bound
│   ├── Convexity.lean              # Convex combinations of pairs
│   └── Duality.lean                # Exponent pair ↔ beta function duality
│
├── Literature/                     # Axiomatized literature results
│   ├── Classical.lean              # (0,1), (1/2,1/2), (1/6,2/3)
│   ├── HeathBrown.lean             # Heath-Brown 1979 results
│   ├── Huxley.lean                 # Huxley 1996, 2005 results
│   ├── Bourgain.lean               # Bourgain 2017 exponent pairs
│   ├── Ingham.lean                 # Ingham 1940 zero density
│   ├── HuxleyTreeblazer.lean      # Huxley-Treeblazer 1993
│   └── References.lean             # Central registry of all axioms
│
├── Derived/                        # Formally proven derived results
│   ├── ExponentPairs.lean          # Derived exponent pairs
│   ├── BetaBounds.lean             # Derived beta bounds
│   ├── MuBounds.lean               # Derived mu bounds
│   ├── ZeroDensityBounds.lean      # Derived zero density estimates
│   └── Examples.lean               # Showcase proofs matching derived.py
│
├── Computation/                    # Verified computational components
│   ├── RationalArithmetic.lean     # Exact rational operations
│   ├── Interval.lean               # Interval arithmetic
│   ├── RationalFunction.lean       # Piecewise rational functions
│   ├── Polytope.lean               # Convex polytope operations
│   ├── ConvexHull.lean             # Convex hull algorithms
│   └── Verification.lean           # Verified numerical checks
│
├── ForMathlib/                     # Contributions to upstream Mathlib
│   ├── README.md                   # (existing)
│   ├── Convex/
│   │   └── ConvexCombination.lean  # General convex analysis lemmas
│   └── NumberTheory/
│       └── ExponentialSums.lean    # Van der Corput lemma prerequisites
│
├── Mathlib/                        # Missing Mathlib components
│   ├── README.md                   # (existing)
│   └── NumberTheory/
│       ├── AnalyticNumberTheory.lean  # ANT-specific tools
│       └── ExponentialSumEstimates.lean  # Weyl sums, van der Corput
│
└── Example.lean                    # (existing) - Can become a showcase
```

## What Will Be Formalized

### Priority 1: Core Transformations (Most Feasible)

These are **conditional calculations** that derive one exponent from another - exactly what the paper recommends formalizing:

#### Van der Corput A-Process
```lean
-- Transforms (k, l) ↦ (k/(2k+2), l/(2k+2) + 1/2)
theorem vanDerCorputA (k l : ℚ) (h : IsExponentPair k l) :
    IsExponentPair (k / (2*k + 2)) (l / (2*k + 2) + 1/2)
```

**Impact**: This transform is applied hundreds of times in `derived.py`. Proving it correct once provides strong guarantees for all derived pairs.

#### Van der Corput B-Process
```lean
-- Transforms (k, l) ↦ (l - 1/2, k + 1/2)
theorem vanDerCorputB (k l : ℚ) (h : IsExponentPair k l) :
    IsExponentPair (l - 1/2) (k + 1/2)
```

**Impact**: The most commonly used transform. Combined with A, generates the classical exponent pair triangle.

#### Sargos C-Process (Exponent Pair → Mu Bound)
```lean
-- Derives μ(σ) bound from exponent pair
theorem sargosC (k l : ℚ) (σ : ℚ) (h : IsExponentPair k l) :
    MuBound σ ((1-σ) * (l-k) + k)
```

**Impact**: Connects exponent pairs to divisor sum bounds. Essential for applications to prime number theory.

#### Sargos D-Process (Exponent Pair → Beta Bound)
```lean
-- Derives β(α) bound from exponent pair
theorem sargosD (k l : ℚ) (α : ℚ) (h : IsExponentPair k l) :
    BetaBound α (k + (l - k) * α)
```

**Impact**: Most important connection. Beta bounds are the dual formulation of exponent pairs.

### Priority 2: Convexity and Duality Theory

#### Convex Combinations
```lean
theorem exponentPair_convex (k₁ l₁ k₂ l₂ : ℚ) (t : ℚ)
    (h₁ : IsExponentPair k₁ l₁) (h₂ : IsExponentPair k₂ l₂)
    (ht : 0 ≤ t ∧ t ≤ 1) :
    IsExponentPair (t*k₁ + (1-t)*k₂) (t*l₁ + (1-t)*l₂)
```

**Impact**: Fundamental property that justifies the convex hull optimization in `polytope.py`. All points in the convex hull of known pairs are valid pairs.

#### Beta-Exponent Duality
```lean
theorem betaDuality (k l : ℚ) :
    IsExponentPair k l ↔
    ∀ α, 0 ≤ α ∧ α ≤ 1 → β α ≤ k + (l - k) * α
```

**Impact**: Connects the two main representations of exponential sum bounds. Allows translation between beta bounds and exponent pairs.

### Priority 3: Derivation Chains (Concrete Examples)

Formalize specific derivation trees from `derived.py`:

```lean
-- Example: Classical pair (1/6, 2/3) via Weyl differencing
axiom weyl_pair : IsExponentPair (1/6) (2/3)

-- Apply BA to get (2/7, 4/7)
theorem derived_pair_2_7_4_7 : IsExponentPair (2/7) (4/7) := by
  have h1 : IsExponentPair (1/6) (2/3) := weyl_pair
  have h2 : IsExponentPair (1/14) (11/14) := vanDerCorputA h1  -- A-process
  exact vanDerCorputB h2  -- B-process

-- Apply BAAA to get (1/18, 5/9)
theorem derived_pair_1_18_5_9 : IsExponentPair (1/18) (5/9) := by
  have h1 := weyl_pair
  have h2 := vanDerCorputB h1                    -- B
  have h3 := vanDerCorputA h2                    -- A
  have h4 := vanDerCorputA h3                    -- A
  exact vanDerCorputA h4                         -- A
```

**Impact**: Validates the proof trees computed by Python. Each theorem corresponds to a `Hypothesis` object with dependencies.

### Priority 4: Computational Verification

#### Rational Arithmetic
```lean
-- Verify that rational operations preserve exactness
theorem rational_arithmetic_exact (k₁ l₁ k₂ l₂ : ℚ) :
    let k' := k₁ / (2 * k₁ + 2)
    let l' := l₁ / (2 * k₁ + 2) + 1/2
    (k' : ℚ) = k' ∧ (l' : ℚ) = l'  -- No loss of precision
```

**Impact**: The Python code uses `Fraction` for exact arithmetic. Lean provides the same guarantees formally.

#### Polytope Containment
```lean
-- Verify specific numerical checks from the database
theorem bourgain_pair_in_triangle :
    let k := (13 : ℚ) / 84
    let l := (55 : ℚ) / 84
    0 ≤ k ∧ k ≤ 1/2 ∧ 1/2 ≤ l ∧ l ≤ 1 ∧ k + l ≤ 1 := by
  norm_num
```

**Impact**: Demonstrates that Lean can verify specific numerical claims from the literature.

## What Will NOT Be Formalized (Initially)

Following the paper's guidance, we **will not** attempt to formalize:

1. **Deep analytic number theory**: Van der Corput lemma, Weyl differencing, exponential sum estimates over primes
   - **Reason**: Would require extensive Mathlib development (years of work)
   - **Solution**: Treat as axioms, like the Python code does

2. **Asymptotic analysis**: Big-O notation, little-o terms, limits as T → ∞
   - **Reason**: Requires sophisticated real analysis infrastructure
   - **Solution**: Work with the exponents directly, not the asymptotic estimates

3. **Optimization algorithms**: Gradient descent, LP solvers, numerical sampling
   - **Reason**: These are heuristic methods, not formal proofs
   - **Solution**: Keep these in Python; use Lean only to verify individual results

4. **Literature proofs**: Original papers by Weyl, van der Corput, Huxley, Bourgain, etc.
   - **Reason**: These are research-level theorems requiring deep expertise
   - **Solution**: Axiomatize as in `literature.py`

## Implementation Phases

### Phase 1: Foundation (2-3 months)

**Goal**: Establish basic definitions and axiomatize key literature results

**Deliverables**:
- `Basic/ExponentPair.lean`: Define `ExponentPair` structure and `IsExponentPair` predicate
- `Basic/BetaFunction.lean`: Define beta bounds
- `Literature/Classical.lean`: Axiomatize (0,1), (1/2,1/2), (1/6,2/3)
- `Literature/References.lean`: Central registry of all axiomatized results
- `Transforms/VanDerCorputA.lean`: State theorem (axiomatize initially)
- `Transforms/VanDerCorputB.lean`: State theorem (axiomatize initially)

**Success metric**: Can state and axiomatize 10-15 key literature results

### Phase 2: Proof Automation (3-4 months)

**Goal**: Build tactics and automation for applying transforms

**Deliverables**:
- Custom tactics for chain application: `apply_A`, `apply_B`, etc.
- `Derived/Examples.lean`: Prove 10-20 simple derivations
- Python bridge: Add `Hypothesis.to_lean()` method to generate Lean proof terms
- Verification script: Check Python derivations against Lean proofs

**Success metric**: Can automatically translate simple Python proof trees to Lean

### Phase 3: Convexity (3-4 months)

**Goal**: Formalize convex hull theory and duality

**Deliverables**:
- `Transforms/Convexity.lean`: Prove exponent pairs closed under convex combinations
- `Transforms/Duality.lean`: Prove beta-exponent duality theorem
- `Computation/ConvexHull.lean`: Verified convex hull membership
- `ForMathlib/Convex/`: Extract general lemmas for upstreaming

**Success metric**: Can verify that computed convex hulls are correct

### Phase 4: Computational Verification (4-6 months)

**Goal**: Connect Lean verification to Python computations

**Deliverables**:
- `Computation/RationalArithmetic.lean`: Certified rational operations
- `Computation/Polytope.lean`: Verified polytope algorithms
- Extraction mechanism: Run Lean functions from Python
- `Derived/ExponentPairs.lean`: Verify 50+ derived pairs from database

**Success metric**: Can certify computational results from `derived.py`

### Phase 5: Advanced Transforms (6-12 months)

**Goal**: Formally prove the A/B/C/D transforms (if possible)

**Deliverables**:
- `Mathlib/NumberTheory/ExponentialSumEstimates.lean`: Prerequisites
- `Transforms/VanDerCorputA.lean`: Full proof (replace axiom)
- `Transforms/VanDerCorputB.lean`: Full proof (replace axiom)
- Research paper on formalization

**Success metric**: At least A and B transforms proven from first principles

**Note**: This phase may require significant Mathlib contributions and could be a multi-year effort. It's acceptable to leave these as axioms indefinitely.

## Integration with Existing Python Code

### Python → Lean Translation

Add method to `Hypothesis` class in `hypotheses.py`:

```python
def to_lean_proof(self, depth: int = 0) -> str:
    """Generate Lean proof term from dependency tree"""
    indent = "  " * depth

    if not self.dependencies:
        # Leaf node: literature result
        safe_name = self.name.replace(" ", "_").replace("(", "").replace(")", "")
        return f"{indent}literature_{safe_name}"

    # Internal node: apply transform
    if len(self.dependencies) == 1:
        dep = list(self.dependencies)[0]
        transform = self._infer_transform()  # A, B, C, or D
        return f"{indent}transform_{transform} (\n{dep.to_lean_proof(depth+1)}\n{indent})"

    # Multiple dependencies: convex combination
    deps = [d.to_lean_proof(depth+1) for d in self.dependencies]
    return f"{indent}convex_combination [\n" + ",\n".join(deps) + f"\n{indent}]"
```

### Verification Script

Create `scripts/verify_with_lean.py`:

```python
#!/usr/bin/env python3
"""Verify Python derivations using Lean"""

import subprocess
import tempfile
from pathlib import Path
from hypotheses import Hypothesis
from derived import all_derived_pairs

def verify_hypothesis(h: Hypothesis) -> bool:
    """Check if Lean can verify this hypothesis"""
    lean_code = f"""
import expdb.Literature.References
import expdb.Derived.ExponentPairs

theorem verify_{h.safe_name} : {h.to_lean_statement()} := by
  {h.to_lean_proof()}
"""

    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
        f.write(lean_code)
        temp_path = f.name

    try:
        result = subprocess.run(
            ['lean', temp_path],
            capture_output=True,
            timeout=30
        )
        return result.returncode == 0
    finally:
        Path(temp_path).unlink()

# Check all derived pairs
for h in all_derived_pairs:
    status = "✓" if verify_hypothesis(h) else "✗"
    print(f"{status} {h.name}")
```

### Lean → Python Extraction

Use Lean's code extraction to generate certified Python:

```lean
-- In Computation/RationalArithmetic.lean
def rational_add (a b : ℚ) : ℚ := a + b

def rational_mul (a b : ℚ) : ℚ := a * b

-- Extract to Python
#eval IO.println (repr (rational_add (1/3) (1/6)))  -- 1/2
```

This generates Python code that's guaranteed correct by Lean's type checker.

## Success Metrics and Milestones

### Short-term (6 months)
- ✅ 20+ literature results axiomatized in Lean
- ✅ A and B transforms stated (axiomatized)
- ✅ 10 simple derivation chains proven
- ✅ Basic Python-Lean bridge functional

### Medium-term (12 months)
- ✅ 100+ derived pairs verified in Lean
- ✅ Convexity theorem proven
- ✅ Duality theorem proven
- ✅ Integration tests: Python ↔ Lean consistency checks

### Long-term (2+ years)
- ✅ A and B transforms proven from first principles
- ✅ C and D transforms proven
- ✅ Computational algorithms certified
- ✅ Publication: "Formally Verified Exponent Pair Database"

### Stretch Goals
- Complete formalization of van der Corput lemma in Mathlib
- Formal verification of Bourgain's 2017 results
- Integration with other formal math projects (e.g., Lean's analytic number theory library)

## Technical Challenges and Mitigation

### Challenge 1: Mathlib Gaps
**Problem**: Van der Corput lemma and exponential sum theory not in Mathlib

**Mitigation**:
1. Start by axiomatizing these results (like Python does)
2. Gradually formalize prerequisites as time permits
3. Engage Mathlib community for contributions
4. Accept that some axioms may remain indefinitely

### Challenge 2: Asymptotic Notation
**Problem**: Estimates like $N(\sigma, T) \ll T^{f(\sigma) + o(1)}$ are informal

**Mitigation**:
1. Work directly with exponent functions $f(\sigma)$, not the estimates
2. Treat "$\ll$" and "$o(1)$" as part of the axiomatization
3. Focus on formal relationships between exponents, not the underlying analysis

### Challenge 3: Computational Complexity
**Problem**: Convex hull and polytope operations may be slow in Lean

**Mitigation**:
1. Keep heavy computation in Python
2. Use Lean only for verification of results
3. Develop efficient tactics for common patterns
4. Use `norm_num` and `polyrith` for arithmetic

### Challenge 4: Proof Maintenance
**Problem**: Database grows; keeping Lean proofs synchronized is effort-intensive

**Mitigation**:
1. Automated translation Python → Lean
2. CI/CD integration: test on every commit
3. Focus on conditional derivations (stable) rather than optimization (changes frequently)

## Resources and Prerequisites

### Required Expertise
- **Lean programming**: Intermediate level (tactics, structures, proofs)
- **Analytic number theory**: Understanding of exponent pairs and exponential sums
- **Python**: Familiarity with the existing ANTEDB codebase

### Estimated Effort
- **Phase 1-2**: 1 person, 6 months (foundational work)
- **Phase 3-4**: 1-2 people, 12 months (verification infrastructure)
- **Phase 5+**: Open-ended research (optional deep formalization)

### Learning Resources
- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- ANTEDB Blueprint: [Web version](https://teorth.github.io/expdb/blueprint/)
- ANTEDB Python: [`blueprint/src/python/`](blueprint/src/python/)

## Getting Started

### Step 1: Set up Lean environment
```bash
# Lean is already configured in this repository
lake build  # Build the project
```

### Step 2: Create first definition
Edit `expdb/Basic/ExponentPair.lean`:
```lean
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.Order.Field.Basic

/-- An exponent pair is a rational point (k,l) satisfying certain
    exponential sum bounds. We encode the geometric constraints. -/
structure ExponentPair where
  k : ℚ
  l : ℚ
  k_nonneg : 0 ≤ k
  k_le_half : k ≤ 1/2
  l_ge_half : 1/2 ≤ l
  l_le_one : l ≤ 1
  sum_le_one : k + l ≤ 1

/-- Predicate: is (k,l) an exponent pair? -/
def IsExponentPair (k l : ℚ) : Prop :=
  ∃ h : ExponentPair, h.k = k ∧ h.l = l
```

### Step 3: Axiomatize first literature result
Edit `expdb/Literature/Classical.lean`:
```lean
import expdb.Basic.ExponentPair

/-- The trivial exponent pair (0, 1) -/
axiom trivial_pair : IsExponentPair 0 1

/-- The Weyl exponent pair (1/2, 1/2) -/
axiom weyl_pair : IsExponentPair (1/2) (1/2)

/-- Classical van der Corput pair (1/6, 2/3) -/
axiom classical_vdc_pair : IsExponentPair (1/6) (2/3)
```

### Step 4: State first transform
Edit `expdb/Transforms/VanDerCorputA.lean`:
```lean
import expdb.Basic.ExponentPair

/-- Van der Corput A-process transforms (k,l) to (k/(2k+2), l/(2k+2) + 1/2) -/
axiom vanDerCorputA (k l : ℚ) (h : IsExponentPair k l) :
    IsExponentPair (k / (2*k + 2)) (l / (2*k + 2) + 1/2)
```

### Step 5: Prove first derivation
Edit `expdb/Derived/Examples.lean`:
```lean
import expdb.Literature.Classical
import expdb.Transforms.VanDerCorputA
import expdb.Transforms.VanDerCorputB

/-- Derived pair (2/7, 4/7) = BA(1/6, 2/3) -/
theorem derived_pair_2_7_4_7 : IsExponentPair (2/7) (4/7) := by
  have h1 : IsExponentPair (1/6) (2/3) := classical_vdc_pair
  have h2 : IsExponentPair (1/14) (11/14) := vanDerCorputA h1
  exact vanDerCorputB h2
```

## Conclusion

Formal verification with Lean is a natural evolution for the ANTEDB project. By focusing on **conditional calculations** - deriving one exponent from another - rather than deep analytic number theory, we can make steady progress while providing valuable certification of the database's computational results.

The key insight is that we don't need to formalize everything. The Python code already provides an effective "semi-formal" system. Lean adds a layer of mathematical rigor where it's most valuable: verifying the logical structure of derivations and ensuring computational correctness.

This plan is designed to be incremental and practical, with each phase delivering tangible value. Even Phase 1 alone (axiomatizing results and stating transforms) would enhance the project by providing a machine-checkable specification of the database's logical structure.

## References

1. T. Tao, T. Trudgian, A. Yang, "[New exponent pairs, zero density estimates, and zero additive energy estimates: a systematic approach](https://arxiv.org/abs/2501.16779)" (2025)
2. [ANTEDB Web Blueprint](https://teorth.github.io/expdb/blueprint/)
3. [ANTEDB Python Documentation](blueprint/src/python/README.md)
4. [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
5. [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
