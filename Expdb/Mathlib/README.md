# Mathlib

This folder contains `.lean` files with declarations missing from existing Mathlib developments.

The B-process development uses the following selected Apache-2.0 extracts. Each
source file records the pinned revision and the modifications made for Expdb.
The upstream license texts were checked and are identical to the root `LICENSE`.

| File | Upstream source | Extracted results |
| --- | --- | --- |
| `StationaryPhase.lean` | [OpenAI Math](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI) | Quadratic stationary phase with a quantitative remainder; Fourier moment bound |
| `NonstationaryPhase.lean` | [prime-minor-arcs-2-15](https://github.com/jconorgrogan/prime-minor-arcs-2-15/blob/f369f267b4dcfebf010c8e7baa2c9602e2960eba/Proof/MRTNonstationaryPhaseTwoIBP.lean) | Two integrations by parts with explicit derivative budgets |
| `SmoothExtension.lean` | [DifferentialGeometry](https://github.com/qinz1yang/differential-geometry/tree/fd2f07fba4c6c102ba626c59153ad98da8f0d442/DifferentialGeometry/Analysis/Calculus/SmoothExtension) | Borel jet realization and closed-interval gluing, strengthened here with uniform finite-order bounds |

The applicable DifferentialGeometry NOTICE attribution is preserved in
`SmoothExtension.lean`. None of the selected files imports upstream project
modules: their dependencies are Mathlib. The model-phase extension bridge lives
in `Expdb/ExponentialSums/PhaseExtension.lean`.
