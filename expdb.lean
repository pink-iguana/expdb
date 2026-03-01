/-
Copyright (c) 2025 ANTEDB Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ANTEDB Contributors
-/

-- Basic definitions
import expdb.Basic.ExponentPair
import expdb.Basic.LargeValueEstimate
import expdb.Basic.ZeroDensityEstimate

-- Literature results (axiomatized)
import expdb.Literature.Classical
import expdb.Literature.Bourgain
import expdb.Literature.HeathBrown
import expdb.Literature.Huxley
import expdb.Literature.RobertSargos
import expdb.Literature.TrudgianYang
import expdb.Literature.ZeroDensityClassical
import expdb.Literature.LargeValues

-- Transforms
import expdb.Transforms.VanDerCorputA
import expdb.Transforms.VanDerCorputB
import expdb.Transforms.ExponentPairToZeroDensity
import expdb.Transforms.LargeValueRaisePower

-- Tactics
import expdb.Tactics.Chain

-- Derived results
import expdb.Derived.Examples
import expdb.Derived.ZeroDensityExamples
import expdb.Derived.LargeValueExamples

-- Original example file
import expdb.Example

/-!
# Analytic Number Theory Exponent Database - Lean Formalization

This is the main entry point for the Lean formalization of the ANTEDB project.

## Project Overview

The Analytic Number Theory Exponent Database (ANTEDB) systematically records theorems
about exponents in analytic number theory, including:
- Exponent pairs for exponential sum bounds
- Zero-density estimates for the Riemann zeta function
- Beta and mu functions for various number-theoretic problems
- Relationships and transformations between these exponents

This Lean formalization provides machine-checked proofs of derivations within the
database, focusing on **conditional calculations** that derive one exponent from
another through formal transformations.

## Organization

The formalization is organized into several modules:

### Basic Definitions (`expdb.Basic`)
- `ExponentPair` - Core definition of exponent pairs
- `ZeroDensityEstimate` - Zero density estimates
- `LargeValueEstimate` - Large value estimates

### Literature Results (`expdb.Literature`)
- `Classical` - Classical exponent pairs (Weyl, van der Corput)
- `Bourgain` - Bourgain's exponent pairs
- `HeathBrown` - Heath-Brown's results
- `Huxley` - Huxley's results
- `RobertSargos` - Robert and Sargos k-th derivative pairs
- `TrudgianYang` - Trudgian-Yang (2025) pairs
- `ZeroDensityClassical` - Classical zero density estimates
- `LargeValues` - Large value estimate axioms

### Transforms (`expdb.Transforms`)
- `VanDerCorputA` - A-process transformation
- `VanDerCorputB` - B-process transformation
- `ExponentPairToZeroDensity` - EP → ZD transforms (Ivić, Bourgain)
- `LargeValueRaisePower` - Raise-to-power transform for LV estimates

### Tactics (`expdb.Tactics`)
- `Chain` - `by_chain` tactic for automated A/B derivations

### Derived Results (`expdb.Derived`)
- `Examples` - Derived exponent pair proofs
- `ZeroDensityExamples` - Derived zero density estimates
- `LargeValueExamples` - Derived large value estimates

## Getting Started

See `LEAN.md` for the overall strategy and implementation phases.

To start exploring:
1. Look at `expdb.Basic.ExponentPair` for the core definitions
2. See `expdb.Literature.Classical` for axiomatized literature results
3. Check `expdb.Derived.Examples` for example proofs

## References

- [ANTEDB Web Blueprint](https://teorth.github.io/expdb/blueprint/)
- [ANTEDB Python Code](https://github.com/teorth/expdb/tree/main/blueprint/src/python)
- [Lean Formalization](LEAN.md)
- T. Tao, T. Trudgian, A. Yang, "New exponent pairs, zero density estimates, and
  zero additive energy estimates: a systematic approach" (2025)
-/
