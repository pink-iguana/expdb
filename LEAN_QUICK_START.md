# Quick Start Guide - Lean Formalization

This guide helps you get started with the Lean formalization of ANTEDB.

## Prerequisites

- Basic familiarity with Lean 4 (see [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/))
- Understanding of exponent pairs (see [ANTEDB Blueprint](https://teorth.github.io/expdb/blueprint/exponent-pairs-chapter.html))
- Python knowledge helpful but not required

## Installation

### 1. Install Lean 4 and Lake
```bash
# Install elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Restart your shell or run:
source ~/.profile  # or ~/.bash_profile or ~/.zshrc

# Verify installation
lean --version
lake --version
```

### 2. Build the Project
```bash
cd /path/to/expdb
lake build
```

This will download Mathlib and build all dependencies. First build may take 10-20 minutes.

## Understanding the Codebase

### File Structure
```
expdb/
├── Basic/ExponentPair.lean        # Core definitions
├── Literature/Classical.lean      # Axiomatized results
├── Transforms/
│   ├── VanDerCorputA.lean         # A-process
│   └── VanDerCorputB.lean         # B-process
└── Derived/Examples.lean          # Proven derivations
```

### Key Concepts

#### 1. `IsExponentPair` Predicate
```lean
def IsExponentPair (k l : ℚ) : Prop :=
  0 ≤ k ∧ k ≤ 1/2 ∧ 1/2 ≤ l ∧ l ≤ 1 ∧ k + l ≤ 1
```
This is the main interface for working with exponent pairs.

#### 2. Literature Axioms
```lean
axiom trivial_pair : IsExponentPair 0 1
axiom weyl_pair : IsExponentPair (1/2) (1/2)
axiom classical_vdc_pair : IsExponentPair (1/6) (2/3)
```
We don't prove these - they're taken from the literature.

#### 3. Transforms
```lean
axiom vanDerCorputA (k l : ℚ) (h : IsExponentPair k l) :
    IsExponentPair (k / (2*k + 2)) (l / (2*k + 2) + 1/2)

axiom vanDerCorputB (k l : ℚ) (h : IsExponentPair k l) :
    IsExponentPair (l - 1/2) (k + 1/2)
```
These are also axiomatized for now.

## Your First Proof

Let's prove that (2/7, 4/7) is an exponent pair.

### Step 1: Open the File
Open `expdb/Derived/Examples.lean` in VS Code with the Lean 4 extension.

### Step 2: Write the Theorem Statement
```lean
theorem my_first_derived_pair : IsExponentPair (2/7) (4/7) := by
  sorry
```

### Step 3: Build the Proof Step-by-Step
The derivation is: BA(1/6, 2/3) = (2/7, 4/7)

```lean
theorem my_first_derived_pair : IsExponentPair (2/7) (4/7) := by
  -- Start with classical pair (1/6, 2/3)
  have h1 : IsExponentPair (1/6) (2/3) := classical_vdc_pair

  -- Apply A-transform: (1/6, 2/3) → (1/14, 11/14)
  have h2 : IsExponentPair (1/14) (11/14) := by
    convert vanDerCorputA (1/6) (2/3) h1 using 1
    constructor <;> norm_num

  -- Apply B-transform: (1/14, 11/14) → (2/7, 4/7)
  convert vanDerCorputB (1/14) (11/14) h2 using 1
  constructor <;> norm_num
```

### Step 4: Check Your Proof
- Save the file (Ctrl+S)
- Look for the green checkmark in VS Code
- If you see errors, hover over them for details

## Common Patterns

### Pattern 1: Apply Transform with Arithmetic Check
```lean
have h_new : IsExponentPair k' l' := by
  convert vanDerCorputA k l h_old using 1
  constructor <;> norm_num
```
- `convert` applies the theorem and generates arithmetic goals
- `norm_num` solves rational arithmetic automatically
- `constructor <;>` applies `constructor` to all goals

### Pattern 2: Chain Multiple Transforms
```lean
have h1 := classical_vdc_pair          -- (1/6, 2/3)
have h2 := vanDerCorputA _ _ h1        -- Apply A
have h3 := vanDerCorputA _ _ h2        -- Apply A again
have h4 := vanDerCorputB _ _ h3        -- Apply B
exact h4                                -- This is our goal
```
Lean can infer the `k l` arguments from context (use `_`).

### Pattern 3: From Literature Axiom
```lean
theorem my_result : IsExponentPair k l := by
  have h := some_literature_result
  -- ... apply transforms to h
  exact result
```

## Exercises

Try proving these derived pairs:

### Exercise 1: One Transform
Prove that (1/14, 11/14) = A(1/6, 2/3)
```lean
theorem exercise_1 : IsExponentPair (1/14) (11/14) := by
  sorry
```

### Exercise 2: Weyl from Trivial
Prove that (1/2, 1/2) = B(0, 1)
```lean
theorem exercise_2 : IsExponentPair (1/2) (1/2) := by
  sorry
```

### Exercise 3: Longer Chain
Prove that (1/6, 2/3) = BA(1/2, 1/2)
```lean
theorem exercise_3 : IsExponentPair (1/6) (2/3) := by
  sorry
```

### Exercise 4: From Trivial (Challenge)
Prove (2/7, 4/7) starting only from `trivial_pair`
```lean
theorem exercise_4 : IsExponentPair (2/7) (4/7) := by
  sorry
```

<details>
<summary>Solutions</summary>

```lean
-- Exercise 1
theorem exercise_1 : IsExponentPair (1/14) (11/14) := by
  have h := classical_vdc_pair
  convert vanDerCorputA (1/6) (2/3) h using 1
  constructor <;> norm_num

-- Exercise 2
theorem exercise_2 : IsExponentPair (1/2) (1/2) := by
  have h := trivial_pair
  convert vanDerCorputB 0 1 h using 1
  constructor <;> norm_num

-- Exercise 3
theorem exercise_3 : IsExponentPair (1/6) (2/3) := by
  have h1 := weyl_pair
  have h2 : IsExponentPair (1/6) (5/6) := by
    convert vanDerCorputA (1/2) (1/2) h1 using 1
    constructor <;> norm_num
  convert vanDerCorputB (1/6) (5/6) h2 using 1
  constructor <;> norm_num

-- Exercise 4: See derived_pair_2_7_4_7_from_trivial in Examples.lean
```

</details>

## Connecting to Python

Every theorem you prove corresponds to a Python `Hypothesis`:

### Python Side
```python
from exponent_pair import *

# Find proof of (2/7, 4/7)
h = best_proof_of_exponent_pair(frac(2,7), frac(4,7))
h.recursively_list_proofs()
```

Output:
```
- [Derived exponent pair (2/7, 4/7)]. Follows from:
  - [van der Corput B transform]
  - [Derived exponent pair (1/14, 11/14)]. Follows from:
    - [van der Corput A transform]
    - [Derived exponent pair (1/6, 2/3)]
```

### Lean Side
```lean
theorem derived_pair_2_7_4_7 : IsExponentPair (2/7) (4/7) := by
  have h1 := classical_vdc_pair           -- (1/6, 2/3)
  have h2 := vanDerCorputA _ _ h1         -- A transform
  exact vanDerCorputB _ _ h2              -- B transform
```

The structure matches! Python's dependency tree = Lean's proof tree.

## Next Steps

1. **Work through exercises** - Get comfortable with the proof patterns
2. **Add more literature results** - Axiomatize Heath-Brown, Huxley, Bourgain
3. **Prove more derived pairs** - Match results from `derived.py`
4. **Create tactics** - Automate common patterns
5. **Write verification scripts** - Check Python ↔ Lean consistency

## Resources

### Lean Learning
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)

### ANTEDB Resources
- [Blueprint](https://teorth.github.io/expdb/blueprint/)
- [Python Code](https://github.com/teorth/expdb/tree/main/blueprint/src/python)
- [Formalization Plan](LEAN_FORMALIZATION_PLAN.md)

### Exponent Pair Theory
- Graham & Kolesnik, "van der Corput's Method of Exponential Sums" (1991)
- Huxley, "Area, Lattice Points, and Exponential Sums" (1996)
- [Blueprint: Exponent Pairs Chapter](https://teorth.github.io/expdb/blueprint/exponent-pairs-chapter.html)

## Getting Help

- **File issues**: Use GitHub issues for bugs or questions
- **Join discussions**: ANTEDB has an active community
- **Lean community**: Ask on Zulip for Lean-specific questions

## Tips for Success

1. **Start small**: Prove one derived pair at a time
2. **Use `sorry`**: Leave gaps and fill them in later
3. **Check arithmetic**: Use `#eval` to verify rational computations
4. **Read examples**: `expdb/Derived/Examples.lean` has working patterns
5. **Match Python**: Use Python code as a guide for proof structure

Happy formalizing! 🎉
