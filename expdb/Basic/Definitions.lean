import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Basic definitions

This module contains the definitions mentioned in Chapter 2 of the ANTEDB blueprint.

Indicator functions, suprema and infima, finite cardinalities, and standard asymptotic relations
use their existing Mathlib definitions and notation. When the blueprint uses `e(θ)`,
we use Mathlib's `𝐞 θ` after `open scoped FourierTransform`.
-/

namespace Expdb

/-- A family in a pseudo-metric space is `δ`-separated when distinct indices have values at
least `δ` apart. This uses a non-strict inequality, unlike `Metric.IsSeparated`. -/
def IsSeparatedFamily {ι α : Type*} [PseudoMetricSpace α] (δ : ℝ) (x : ι → α) : Prop :=
  Pairwise fun i j => δ ≤ dist (x i) (x j)

/-- A finite set is `δ`-separated when distinct elements are at least `δ` apart. -/
def IsSeparated {α : Type*} [PseudoMetricSpace α] (δ : ℝ) (W : Finset α) : Prop :=
  IsSeparatedFamily δ fun t : W => (t : α)

/-- A finite set is `1`-separated. -/
abbrev IsOneSeparated {α : Type*} [PseudoMetricSpace α] (W : Finset α) : Prop :=
  IsSeparated 1 W

/-- A family in a normed type is `C`-bounded when every value has norm at most `C`. -/
def IsBoundedFamily {ι β : Type*} [Norm β] (C : ℝ) (a : ι → β) : Prop :=
  ∀ i, ‖a i‖ ≤ C

/-- A family in a normed type is `1`-bounded. -/
abbrev IsOneBounded {ι β : Type*} [Norm β] (a : ι → β) : Prop :=
  IsBoundedFamily 1 a

end Expdb
