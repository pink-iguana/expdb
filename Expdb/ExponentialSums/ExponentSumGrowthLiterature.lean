module

public import Expdb.ExponentialSums.ExponentSumGrowthBounds

/-!
# Literature bounds for exponential sum growth exponents

This module records the bounds for the exponential sum growth exponent in the known bounds
section of the blueprint's Exponential sum growth exponents chapter (`beta-chapter`).
-/

@[expose] public section

open scoped NNReal

noncomputable section

namespace Expdb

/-! ## Bounds from 1989 to 1995 -/

/-- The 1989 Watt bound (blueprint Theorem `beta-Watt`). -/
theorem exponentSumGrowthExponent_le_watt_1989
    (α : ℝ≥0) (hα : 3 / 7 ≤ α) (hα' : α ≤ 1 / 2) :
    exponentSumGrowthExponent α ≤ 89 / 560 + (α : ℝ) / 2 := by
  sorry

/-- The 1991 Huxley--Kolesnik bound (blueprint Theorem `beta-HK2`). -/
theorem exponentSumGrowthExponent_le_huxleyKolesnik_1991
    (α : ℝ≥0) (hα : 2 / 5 ≤ α) (hα' : α ≤ 1 / 2) :
    exponentSumGrowthExponent α ≤
      max (max ((1 + 8 * (α : ℝ)) / 22) ((11 + 112 * (α : ℝ)) / 158))
        ((1 + 17 * (α : ℝ)) / 22) := by
  sorry

/-- The 1993 Huxley bound (blueprint Theorem `beta-Huxley-4`). -/
theorem exponentSumGrowthExponent_le_huxley_1993 (α : ℝ≥0) :
    (α ≤ 49 / 114 →
      exponentSumGrowthExponent α ≤
        max (13 / 60 + 7 / 20 * (α : ℝ)) (11 / 120 + 13 / 20 * (α : ℝ))) ∧
    (49 / 114 ≤ α → α ≤ 1 / 2 →
      exponentSumGrowthExponent α ≤ 89 / 570 + (α : ℝ) / 2) := by
  sorry

/-- The first range of the 1993 Huxley bound. -/
theorem exponentSumGrowthExponent_le_huxley_1993_low
    (α : ℝ≥0) (hα : α ≤ 49 / 114) :
    exponentSumGrowthExponent α ≤
      max (13 / 60 + 7 / 20 * (α : ℝ)) (11 / 120 + 13 / 20 * (α : ℝ)) :=
  (exponentSumGrowthExponent_le_huxley_1993 α).1 hα

/-- The second range of the 1993 Huxley bound. -/
theorem exponentSumGrowthExponent_le_huxley_1993_high
    (α : ℝ≥0) (hα : 49 / 114 ≤ α) (hα' : α ≤ 1 / 2) :
    exponentSumGrowthExponent α ≤ 89 / 570 + (α : ℝ) / 2 :=
  (exponentSumGrowthExponent_le_huxley_1993 α).2 hα hα'

/-- The second 1993 Huxley bound (blueprint Theorem `beta-Huxley-4a`). -/
theorem exponentSumGrowthExponent_le_huxley_1993_second
    (α : ℝ≥0) (hα : α ≤ 1) :
    (α ≤ 87 / 275 →
      exponentSumGrowthExponent α ≤ (13 + 94 * (α : ℝ)) / 146) ∧
    (87 / 275 ≤ α → α ≤ 423 / 1295 →
      exponentSumGrowthExponent α ≤ (11 + 191 * (α : ℝ)) / 244) ∧
    (423 / 1295 ≤ α → α ≤ 227 / 601 →
      exponentSumGrowthExponent α ≤ (89 + 908 * (α : ℝ)) / 1282) ∧
    (227 / 601 ≤ α → α ≤ 12 / 31 →
      exponentSumGrowthExponent α ≤ (29 + 173 * (α : ℝ)) / 280) ∧
    (12 / 31 ≤ α →
      exponentSumGrowthExponent α ≤ (4 + 103 * (α : ℝ)) / 128) := by
  sorry

/-- The first range of the second 1993 Huxley bound. -/
theorem exponentSumGrowthExponent_le_huxley_1993_second_part_one
    (α : ℝ≥0) (hα : α ≤ 1) (hα' : α ≤ 87 / 275) :
    exponentSumGrowthExponent α ≤ (13 + 94 * (α : ℝ)) / 146 :=
  (exponentSumGrowthExponent_le_huxley_1993_second α hα).1 hα'

/-- The second range of the second 1993 Huxley bound. -/
theorem exponentSumGrowthExponent_le_huxley_1993_second_part_two
    (α : ℝ≥0) (hα : α ≤ 1) (hα' : 87 / 275 ≤ α)
    (hα'' : α ≤ 423 / 1295) :
    exponentSumGrowthExponent α ≤ (11 + 191 * (α : ℝ)) / 244 :=
  (exponentSumGrowthExponent_le_huxley_1993_second α hα).2.1 hα' hα''

/-- The third range of the second 1993 Huxley bound. -/
theorem exponentSumGrowthExponent_le_huxley_1993_second_part_three
    (α : ℝ≥0) (hα : α ≤ 1) (hα' : 423 / 1295 ≤ α)
    (hα'' : α ≤ 227 / 601) :
    exponentSumGrowthExponent α ≤ (89 + 908 * (α : ℝ)) / 1282 :=
  (exponentSumGrowthExponent_le_huxley_1993_second α hα).2.2.1 hα' hα''

/-- The fourth range of the second 1993 Huxley bound. -/
theorem exponentSumGrowthExponent_le_huxley_1993_second_part_four
    (α : ℝ≥0) (hα : α ≤ 1) (hα' : 227 / 601 ≤ α)
    (hα'' : α ≤ 12 / 31) :
    exponentSumGrowthExponent α ≤ (29 + 173 * (α : ℝ)) / 280 :=
  (exponentSumGrowthExponent_le_huxley_1993_second α hα).2.2.2.1 hα' hα''

/-- The fifth range of the second 1993 Huxley bound. -/
theorem exponentSumGrowthExponent_le_huxley_1993_second_part_five
    (α : ℝ≥0) (hα : α ≤ 1) (hα' : 12 / 31 ≤ α) :
    exponentSumGrowthExponent α ≤ (4 + 103 * (α : ℝ)) / 128 :=
  (exponentSumGrowthExponent_le_huxley_1993_second α hα).2.2.2.2 hα'

/-- The two 1995 Sargos bounds (blueprint Theorem `sargos_1995`). -/
theorem exponentSumGrowthExponent_le_sargos_1995
    (α : ℝ≥0) (hα : α ≤ 1) :
    (exponentSumGrowthExponent α ≤
      max (max (max ((α : ℝ) + 3 * (1 - 4 * α) / 40) (7 * α / 8))
        ((α : ℝ) / 3 - (1 - 4 * α) / 6)) 0) ∧
    (exponentSumGrowthExponent α ≤
      max (max (max ((α : ℝ) + (1 - 4 * α) / 14) (5 * α / 6))
        ((α : ℝ) / 3 - (1 - 4 * α) / 6)) 0) := by
  sorry

/-- The first 1995 Sargos bound. -/
theorem exponentSumGrowthExponent_le_sargos_1995_first
    (α : ℝ≥0) (hα : α ≤ 1) :
    exponentSumGrowthExponent α ≤
      max (max (max ((α : ℝ) + 3 * (1 - 4 * α) / 40) (7 * α / 8))
        ((α : ℝ) / 3 - (1 - 4 * α) / 6)) 0 :=
  (exponentSumGrowthExponent_le_sargos_1995 α hα).1

/-- The second 1995 Sargos bound. -/
theorem exponentSumGrowthExponent_le_sargos_1995_second
    (α : ℝ≥0) (hα : α ≤ 1) :
    exponentSumGrowthExponent α ≤
      max (max (max ((α : ℝ) + (1 - 4 * α) / 14) (5 * α / 6))
        ((α : ℝ) / 3 - (1 - 4 * α) / 6)) 0 :=
  (exponentSumGrowthExponent_le_sargos_1995 α hα).2

/-! ## Huxley's tables -/

/-- The affine bounds in Huxley's Table 17.1. -/
def huxleyTable17_1 : List AffineBetaBound :=
  [⟨39 / 60, 4 / 60, 7 / 12, 517 / 873⟩,
   ⟨42 / 120, 29 / 120, 65 / 114, 7 / 12⟩,
   ⟨285 / 570, 89 / 570, 49 / 114, 65 / 114⟩,
   ⟨78 / 120, 11 / 120, 5 / 12, 49 / 114⟩,
   ⟨21 / 60, 13 / 60, 356 / 873, 5 / 12⟩,
   ⟨103 / 128, 4 / 128, 12 / 31, 356 / 873⟩,
   ⟨173 / 280, 29 / 280, 227 / 601, 12 / 31⟩,
   ⟨908 / 1282, 89 / 1282, 423 / 1295, 227 / 601⟩,
   ⟨191 / 244, 11 / 244, 87 / 275, 423 / 1295⟩,
   ⟨94 / 146, 13 / 146, 1424 / 4747, 87 / 275⟩,
   ⟨235 / 264, 4 / 264, 120 / 419, 1424 / 4747⟩,
   ⟨1351 / 1614, 49 / 1614, 967 / 3428, 120 / 419⟩,
   ⟨464 / 600, 29 / 600, 199 / 716, 967 / 3428⟩,
   ⟨2243 / 2706, 89 / 2706, 19 / 74, 199 / 716⟩,
   ⟨428 / 492, 11 / 492, 161 / 646, 19 / 74⟩,
   ⟨253 / 318, 13 / 318, 2848 / 12173, 161 / 646⟩]

/-- The affine bounds in Huxley's Table 19.2. -/
def huxleyTable19_2 : List AffineBetaBound :=
  [⟨285 / 570, 89 / 570, 106822 / 246639, 139817 / 246639⟩,
   ⟨17972 / 27290, 2387 / 27290, 675 / 1574, 106822 / 246639⟩,
   ⟨19177 / 29855, 2819 / 29855, 699371 / 1647930, 675 / 1574⟩,
   ⟨88442 / 134680, 11897 / 134680, 156527 / 370694, 699371 / 1647930⟩,
   ⟨897 / 1345, 113 / 1345, 263 / 638, 156527 / 370694⟩,
   ⟨3624 / 5530, 491 / 5530, 143 / 349, 263 / 638⟩,
   ⟨1053 / 2800, 569 / 2800, 307 / 761, 143 / 349⟩,
   ⟨2484 / 6410, 1273 / 6410, 68682 / 171139, 307 / 761⟩,
   ⟨103 / 128, 4 / 128, 12 / 31, 68682 / 171139⟩,
   ⟨173 / 280, 29 / 280, 227 / 601, 12 / 31⟩]

/-- The bounds in Huxley's Tables 17.1 and 19.2 are valid (blueprint Theorem
`huxley-table`). -/
theorem huxleyTables_valid :
    AffineBetaBound.AllValid (huxleyTable17_1 ++ huxleyTable19_2) := by
  sorry

/-- Each affine bound in Huxley's Table 17.1 is valid. -/
theorem huxleyTable17_1_valid {b : AffineBetaBound}
    (hb : b ∈ huxleyTable17_1) : b.IsValid :=
  huxleyTables_valid.isValid (List.mem_append.mpr (Or.inl hb))

/-- Each affine bound in Huxley's Table 19.2 is valid. -/
theorem huxleyTable19_2_valid {b : AffineBetaBound}
    (hb : b ∈ huxleyTable19_2) : b.IsValid :=
  huxleyTables_valid.isValid (List.mem_append.mpr (Or.inr hb))

/-! ## Bounds from 2001 onwards -/

/-- The 2001 Huxley--Kolesnik bound (blueprint Theorem `beta-HK`). -/
theorem exponentSumGrowthExponent_le_huxleyKolesnik_2001
    (α : ℝ≥0) (hα : 2 / 5 ≤ α) (hα' : α ≤ 1 / 2) :
    exponentSumGrowthExponent α ≤
      max (max (7 / 80 + 79 / 120 * (α : ℝ))
        (3 / 32 + 103 / 160 * (α : ℝ)))
        (9 / 40 + 13 / 40 * (α : ℝ)) := by
  sorry

/-- The 2002 Robert--Sargos bound (blueprint Theorem `beta-RS`). -/
theorem exponentSumGrowthExponent_le_robertSargos_2002
    (α : ℝ≥0) (hα : 0 < α) :
    exponentSumGrowthExponent α ≤
      max ((α : ℝ) + (1 - 4 * α) / 13) (-7 * (1 - 4 * α) / 13) := by
  sorry

/-- The two 2003 Sargos bounds (blueprint Theorem `sargos-bound`). -/
theorem exponentSumGrowthExponent_le_sargos_2003
    (α : ℝ≥0) (hα : 0 < α) :
    (exponentSumGrowthExponent α ≤
      max ((α : ℝ) + (1 - 8 * α) / 204) (-95 * (1 - 8 * α) / 204)) ∧
    (exponentSumGrowthExponent α ≤
      max ((α : ℝ) + 7 * (1 - 9 * α) / 2640)
        (-1001 * (1 - 9 * α) / 2640)) := by
  sorry

/-- The first 2003 Sargos bound. -/
theorem exponentSumGrowthExponent_le_sargos_2003_first
    (α : ℝ≥0) (hα : 0 < α) :
    exponentSumGrowthExponent α ≤
      max ((α : ℝ) + (1 - 8 * α) / 204) (-95 * (1 - 8 * α) / 204) :=
  (exponentSumGrowthExponent_le_sargos_2003 α hα).1

/-- The second 2003 Sargos bound. -/
theorem exponentSumGrowthExponent_le_sargos_2003_second
    (α : ℝ≥0) (hα : 0 < α) :
    exponentSumGrowthExponent α ≤
      max ((α : ℝ) + 7 * (1 - 9 * α) / 2640)
        (-1001 * (1 - 9 * α) / 2640) :=
  (exponentSumGrowthExponent_le_sargos_2003 α hα).2

/-- The 2005 Huxley bound (blueprint Theorem `beta-Huxley-5`). -/
theorem exponentSumGrowthExponent_le_huxley_2005
    (α : ℝ≥0) (hα : 1 / 3 ≤ α) (hα' : α ≤ 1 / 2) :
    exponentSumGrowthExponent α ≤
      max ((37 + 59 * (α : ℝ)) / 170) ((63 + 449 * (α : ℝ)) / 690) := by
  sorry

/-- The first 2016 Robert bound (blueprint Theorem `beta-R`). -/
theorem exponentSumGrowthExponent_le_robert_2016
    (α : ℝ≥0) (hα : 0 < α) (hα' : α ≤ 3 / 7) :
    exponentSumGrowthExponent α ≤
      max ((α : ℝ) + (1 - 4 * α) / 12) (11 * α / 12) := by
  sorry

/-- The second 2016 Robert bound (blueprint Theorem `beta-R2`). -/
theorem exponentSumGrowthExponent_le_robert_2016_second
    (α : ℝ≥0) (k : ℕ) (hk : 4 ≤ k)
    (hα : -(1 - k * (α : ℝ)) * (k - 1) / (2 * k - 3) ≤ α) :
    exponentSumGrowthExponent α ≤
      (α : ℝ) + max ((1 - k * (α : ℝ)) / (2 * (k - 1) * (k - 2)))
        (-1 / (2 * (k - 1) * (k - 2))) := by
  sorry

/-- The 2017 Heath--Brown bound (blueprint Theorem `beta-HB`). -/
theorem exponentSumGrowthExponent_le_heathBrown_2017
    (α : ℝ≥0) (k : ℕ) (hα : 0 < α) (hk : 3 ≤ k) :
    exponentSumGrowthExponent α ≤
      (α : ℝ) + max (max ((1 - k * (α : ℝ)) / (k * (k - 1)))
        (-(α : ℝ) / (k * (k - 1))))
        (-2 * (α : ℝ) / (k * (k - 1)) -
          2 * (1 - k * (α : ℝ)) / (k ^ 2 * (k - 1))) := by
  sorry

/-- The 2017 Bourgain bound (blueprint Theorem `beta-Bourgain`). -/
theorem exponentSumGrowthExponent_le_bourgain_2017 (α : ℝ≥0) :
    (1 / 3 < α → α ≤ 5 / 12 →
      exponentSumGrowthExponent α ≤ 2 / 9 + (α : ℝ) / 3) ∧
    (5 / 12 < α → α ≤ 3 / 7 →
      exponentSumGrowthExponent α ≤ 1 / 12 + 2 * (α : ℝ) / 3) ∧
    (3 / 7 < α → α ≤ 1 / 2 →
      exponentSumGrowthExponent α ≤ 13 / 84 + (α : ℝ) / 2) := by
  sorry

/-- The first range of the 2017 Bourgain bound. -/
theorem exponentSumGrowthExponent_le_bourgain_2017_first
    (α : ℝ≥0) (hα : 1 / 3 < α) (hα' : α ≤ 5 / 12) :
    exponentSumGrowthExponent α ≤ 2 / 9 + (α : ℝ) / 3 :=
  (exponentSumGrowthExponent_le_bourgain_2017 α).1 hα hα'

/-- The second range of the 2017 Bourgain bound. -/
theorem exponentSumGrowthExponent_le_bourgain_2017_second
    (α : ℝ≥0) (hα : 5 / 12 < α) (hα' : α ≤ 3 / 7) :
    exponentSumGrowthExponent α ≤ 1 / 12 + 2 * (α : ℝ) / 3 :=
  (exponentSumGrowthExponent_le_bourgain_2017 α).2.1 hα hα'

/-- The third range of the 2017 Bourgain bound. -/
theorem exponentSumGrowthExponent_le_bourgain_2017_third
    (α : ℝ≥0) (hα : 3 / 7 < α) (hα' : α ≤ 1 / 2) :
    exponentSumGrowthExponent α ≤ 13 / 84 + (α : ℝ) / 2 :=
  (exponentSumGrowthExponent_le_bourgain_2017 α).2.2 hα hα'

/-- The 2020 Heath--Brown bound (blueprint Theorem `beta-hb-2020`). -/
theorem exponentSumGrowthExponent_le_heathBrown_2020
    (α : ℝ≥0) (hα : 1 ≤ 4 * (α : ℝ) - 1) (hα' : 4 * (α : ℝ) - 1 ≤ 2) :
    exponentSumGrowthExponent α ≤
      max ((α : ℝ) * (1 - (4 * α - 1) / (4 * (4 * α - 1) + 8)))
        (8 * α / 9) := by
  sorry

/-! ## Combined bound -/

/-- The affine pieces in the combined bound of Trudgian and Yang. -/
def combinedBetaBounds : List AffineBetaBound :=
  [⟨346 / 414, 13 / 414, 0, 2848 / 12173⟩,
   ⟨253 / 318, 13 / 318, 2848 / 12173, 161 / 646⟩,
   ⟨107 / 123, 11 / 492, 161 / 646, 19 / 74⟩,
   ⟨2243 / 2706, 89 / 2706, 19 / 74, 199 / 716⟩,
   ⟨58 / 75, 29 / 600, 199 / 716, 967 / 3428⟩,
   ⟨1351 / 1614, 49 / 1614, 967 / 3428, 120 / 419⟩,
   ⟨235 / 264, 1 / 66, 120 / 419, 1328 / 4447⟩,
   ⟨139 / 194, 13 / 194, 1328 / 4447, 104 / 343⟩,
   ⟨47 / 73, 13 / 146, 104 / 343, 87 / 275⟩,
   ⟨191 / 244, 11 / 244, 87 / 275, 423 / 1295⟩,
   ⟨454 / 641, 89 / 1282, 423 / 1295, 227 / 601⟩,
   ⟨173 / 280, 29 / 280, 227 / 601, 12 / 31⟩,
   ⟨103 / 128, 1 / 32, 12 / 31, 1508 / 3825⟩,
   ⟨521 / 796, 18 / 199, 1508 / 3825, 62831 / 155153⟩,
   ⟨1053 / 2800, 569 / 2800, 62831 / 155153, 143 / 349⟩,
   ⟨1812 / 2765, 491 / 5530, 143 / 349, 263 / 638⟩,
   ⟨897 / 1345, 113 / 1345, 263 / 638, 1673 / 4038⟩,
   ⟨1 / 3, 2 / 9, 1673 / 4038, 5 / 12⟩,
   ⟨2 / 3, 1 / 12, 5 / 12, 3 / 7⟩,
   ⟨1 / 2, 13 / 84, 3 / 7, 1 / 2⟩]

/-- Every affine piece in `combinedBetaBounds` is valid (blueprint Theorem
`combined-bound`). -/
theorem combinedBetaBounds_valid :
    AffineBetaBound.AllValid combinedBetaBounds := by
  sorry

/-- Extract a valid affine piece from `combinedBetaBounds`. -/
theorem combinedBetaBound_valid {b : AffineBetaBound}
    (hb : b ∈ combinedBetaBounds) : b.IsValid :=
  combinedBetaBounds_valid.isValid hb

end Expdb

end
