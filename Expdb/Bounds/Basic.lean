module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Real.Basic

import Mathlib.Tactic

/-!
# Exact one-dimensional affine data

Small executable types used by the bound calculators.  The computational
representation uses rational numbers; `ContainsReal` and `evalReal` provide the
bridge to theorem statements over the reals.
-/

@[expose] public section

namespace Expdb.Bounds

/-- Whether an endpoint belongs to an interval. -/
inductive Boundary where
  | open
  | closed
  deriving DecidableEq, Repr, BEq

@[simp] theorem Boundary.open_ne_closed : Boundary.open ≠ Boundary.closed := by decide

@[simp] theorem Boundary.closed_ne_open : Boundary.closed ≠ Boundary.open := by decide

/-- A finite rational interval.  Degenerate intervals are allowed in the type;
`IsEmpty` detects the three empty degenerate variants. -/
structure RatInterval where
  lower : ℚ
  upper : ℚ
  lowerBoundary : Boundary
  upperBoundary : Boundary
  lower_le_upper : lower ≤ upper

namespace RatInterval

/-- Construct an interval after checking that its endpoints are ordered. -/
def ofEndpoints? (lower upper : ℚ) (lowerBoundary upperBoundary : Boundary) :
    Option RatInterval :=
  if h : lower ≤ upper then
    some ⟨lower, upper, lowerBoundary, upperBoundary, h⟩
  else
    none

/-- A closed interval. -/
def closed (lower upper : ℚ) (h : lower ≤ upper) : RatInterval :=
  ⟨lower, upper, .closed, .closed, h⟩

/-- An open interval. -/
def openInterval (lower upper : ℚ) (h : lower ≤ upper) : RatInterval :=
  ⟨lower, upper, .open, .open, h⟩

/-- A closed-open interval. -/
def closedOpen (lower upper : ℚ) (h : lower ≤ upper) : RatInterval :=
  ⟨lower, upper, .closed, .open, h⟩

/-- An open-closed interval. -/
def openClosed (lower upper : ℚ) (h : lower ≤ upper) : RatInterval :=
  ⟨lower, upper, .open, .closed, h⟩

/-- A singleton interval. -/
def singleton (x : ℚ) : RatInterval :=
  closed x x le_rfl

/-- Whether the interval is empty. -/
def isEmpty (I : RatInterval) : Bool :=
  I.lower == I.upper &&
    (I.lowerBoundary == .open || I.upperBoundary == .open)

/-- Exact membership of a rational point. -/
def containsRat (I : RatInterval) (x : ℚ) : Bool :=
  (if I.lowerBoundary == .closed then I.lower ≤ x else I.lower < x) &&
    (if I.upperBoundary == .closed then x ≤ I.upper else x < I.upper)

/-- Membership of a real point in the represented interval. -/
def ContainsReal (I : RatInterval) (x : ℝ) : Prop :=
  (if I.lowerBoundary = .closed then (I.lower : ℝ) ≤ x else (I.lower : ℝ) < x) ∧
    (if I.upperBoundary = .closed then x ≤ (I.upper : ℝ) else x < (I.upper : ℝ))

/-- A decidable endpoint characterization of interval containment. -/
def IsSubset (I J : RatInterval) : Prop :=
  (I.lower = I.upper ∧
      (I.lowerBoundary = .open ∨ I.upperBoundary = .open)) ∨
    ((J.lower < I.lower ∨
        (J.lower = I.lower ∧
          (I.lowerBoundary = .open ∨ J.lowerBoundary = .closed))) ∧
      (I.upper < J.upper ∨
        (I.upper = J.upper ∧
          (I.upperBoundary = .open ∨ J.upperBoundary = .closed))))

/-- Executable interval-containment check. -/
def isSubset (I J : RatInterval) : Bool :=
  @decide (I.IsSubset J) (by unfold IsSubset; infer_instance)

/-- The endpoint containment check implies semantic containment over the reals. -/
theorem containsReal_of_isSubset {I J : RatInterval} (hIJ : I.IsSubset J)
    {x : ℝ} (hx : I.ContainsReal x) : J.ContainsReal x := by
  rcases I with ⟨il, iu, ilb, iub, hiu⟩
  rcases J with ⟨jl, ju, jlb, jub, hju⟩
  simp only [IsSubset, ContainsReal] at hIJ hx ⊢
  rcases hIJ with hEmpty | ⟨hlower, hupper⟩
  · rcases hEmpty with ⟨heq, hopen⟩
    have hxLower := hx.1
    have hxUpper := hx.2
    have heqR : (il : ℝ) = (iu : ℝ) := congrArg ((↑·) : ℚ → ℝ) heq
    cases ilb <;> cases iub <;>
      simp at hopen hxLower hxUpper <;>
      linarith
  · constructor
    · have hxLower := hx.1
      cases jlb with
      | «open» =>
          rcases hlower with hlower | ⟨heq, hboundary⟩
          · have hlowerR : (jl : ℝ) < (il : ℝ) := by exact_mod_cast hlower
            cases ilb <;> simp at hxLower ⊢ <;> linarith
          · have hilb : ilb = .open := hboundary.resolve_right Boundary.open_ne_closed
            subst ilb
            simpa using (congrArg ((↑·) : ℚ → ℝ) heq).trans_lt hxLower
      | «closed» =>
          have hle : jl ≤ il := by
            rcases hlower with hlower | ⟨heq, _⟩
            · exact le_of_lt hlower
            · exact le_of_eq heq
          have hleR : (jl : ℝ) ≤ (il : ℝ) := by exact_mod_cast hle
          cases ilb <;> simp at hxLower ⊢ <;> linarith
    · have hxUpper := hx.2
      cases jub with
      | «open» =>
          rcases hupper with hupper | ⟨heq, hboundary⟩
          · have hupperR : (iu : ℝ) < (ju : ℝ) := by exact_mod_cast hupper
            cases iub <;> simp at hxUpper ⊢ <;> linarith
          · have hiub : iub = .open := hboundary.resolve_right Boundary.open_ne_closed
            subst iub
            simpa using hxUpper.trans_eq (congrArg ((↑·) : ℚ → ℝ) heq)
      | «closed» =>
          have hle : iu ≤ ju := by
            rcases hupper with hupper | ⟨heq, _⟩
            · exact le_of_lt hupper
            · exact le_of_eq heq
          have hleR : (iu : ℝ) ≤ (ju : ℝ) := by exact_mod_cast hle
          cases iub <;> simp at hxUpper ⊢ <;> linarith

/-- Boolean interval containment is sound. -/
theorem containsReal_of_isSubset_eq_true {I J : RatInterval}
    (hIJ : I.isSubset J = true) {x : ℝ} (hx : I.ContainsReal x) :
    J.ContainsReal x := by
  apply containsReal_of_isSubset ?_ hx
  let inst : Decidable (I.IsSubset J) := by unfold IsSubset; infer_instance
  exact @of_decide_eq_true (I.IsSubset J) inst hIJ

/-- Membership in the closure of the represented interval. -/
def containsClosureRat (I : RatInterval) (x : ℚ) : Bool :=
  I.lower ≤ x && x ≤ I.upper

/-- The intersection of two intervals, or `none` when it is empty. -/
def intersect? (I J : RatInterval) : Option RatInterval := do
  let lower := max I.lower J.lower
  let upper := min I.upper J.upper
  let lowerBoundary :=
    if I.lower < J.lower then J.lowerBoundary
    else if J.lower < I.lower then I.lowerBoundary
    else if I.lowerBoundary == .closed && J.lowerBoundary == .closed then
      .closed
    else
      .open
  let upperBoundary :=
    if I.upper < J.upper then I.upperBoundary
    else if J.upper < I.upper then J.upperBoundary
    else if I.upperBoundary == .closed && J.upperBoundary == .closed then
      .closed
    else
      .open
  let K ← ofEndpoints? lower upper lowerBoundary upperBoundary
  if K.isEmpty then none else some K

/-- A rational representative point.  The result lies in every nonempty interval. -/
def sample (I : RatInterval) : ℚ :=
  if I.lower = I.upper then I.lower else (I.lower + I.upper) / 2

/-- Merge adjacent intervals when their union is again an interval. -/
def mergeAdjacent? (I J : RatInterval) : Option RatInterval :=
  if I.upper = J.lower then
    if I.upperBoundary == .closed || J.lowerBoundary == .closed then
      ofEndpoints? I.lower J.upper I.lowerBoundary J.upperBoundary
    else
      none
  else
    none

end RatInterval

/-- An affine function with rational slope and intercept. -/
structure RatAffine where
  slope : ℚ
  intercept : ℚ
  deriving DecidableEq, Repr, BEq

namespace RatAffine

/-- Exact rational evaluation. -/
def evalRat (f : RatAffine) (x : ℚ) : ℚ :=
  f.slope * x + f.intercept

/-- Evaluation after embedding the coefficients into the reals. -/
def evalReal (f : RatAffine) (x : ℝ) : ℝ :=
  (f.slope : ℝ) * x + (f.intercept : ℝ)

/-- The intersection abscissa of two nonparallel affine functions. -/
def intersection? (f g : RatAffine) : Option ℚ :=
  if f.slope = g.slope then none
  else some ((g.intercept - f.intercept) / (f.slope - g.slope))

end RatAffine

end Expdb.Bounds
