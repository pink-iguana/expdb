# Mathlib

This folder contains `.lean` files with declarations missing from existing Mathlib developments.

## Planned Structure

As the Lean formalization progresses (see [LEAN.md](../../LEAN.md)), this directory will contain:

- `NumberTheory/AnalyticNumberTheory.lean` - Analytic number theory-specific tools and definitions
- `NumberTheory/ExponentialSumEstimates.lean` - Weyl sums, van der Corput lemma, and related exponential sum estimates

These files contain specialized results that are needed for the ANTEDB formalization but may not yet be suitable for upstreaming to Mathlib. Once these mature and gain broader applicability, they may be moved to `ForMathlib/` for eventual contribution to the main Mathlib library.
