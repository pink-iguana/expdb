"""
Test the Hypothesis.to_lean() method for generating Lean 4 proofs.

This test constructs minimal Hypothesis objects directly, avoiding
the full literature import chain (which requires optional C library
dependencies like pycddlib).
"""

from fractions import Fraction as frac

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from hypotheses import Hypothesis
from reference import Reference


# Minimal Exp_pair stand-in that mirrors exponent_pair.Exp_pair
class Exp_pair:
    def __init__(self, k, l):
        self.k = k
        self.l = l
    def __repr__(self):
        return f"The exponent pair ({self.k}, {self.l})"


def _make_exp_pair_hyp(name, k, l, ref, deps=None):
    """Helper to build an exponent pair Hypothesis."""
    h = Hypothesis(name, "Exponent pair", Exp_pair(k, l), "proof", ref)
    if deps:
        h.dependencies = deps
    return h


def _make_transform_hyp(name):
    """Helper to build an exponent pair transform Hypothesis."""
    return Hypothesis(name, "Exponent pair transform", None, "proof",
                      Reference.make("test", 2024))


def _A_transform(input_hyp, A_hyp):
    """Apply the A-process: (k, l) -> (k/(2k+2), l/(2k+2) + 1/2)."""
    k, l = input_hyp.data.k, input_hyp.data.l
    new_k = k / (2 * k + 2)
    new_l = frac(1, 2) + l / (2 * k + 2)
    return _make_exp_pair_hyp(
        f"Derived exponent pair ({new_k}, {new_l})",
        new_k, new_l,
        Reference.derived(2024),
        deps={input_hyp, A_hyp},
    )


def _B_transform(input_hyp, B_hyp):
    """Apply the B-process: (k, l) -> (l - 1/2, k + 1/2)."""
    k, l = input_hyp.data.k, input_hyp.data.l
    new_k = l - frac(1, 2)
    new_l = k + frac(1, 2)
    return _make_exp_pair_hyp(
        f"Derived exponent pair ({new_k}, {new_l})",
        new_k, new_l,
        Reference.derived(2024),
        deps={input_hyp, B_hyp},
    )


# ---- Fixtures ----

A_transform_hyp = _make_transform_hyp("van der Corput A transform")
B_transform_hyp = _make_transform_hyp("van der Corput B transform")

trivial = _make_exp_pair_hyp(
    "Trivial exponent pair (0, 1)", frac(0), frac(1), Reference.trivial()
)
bourgain = _make_exp_pair_hyp(
    "Bourgain exponent pair", frac(13, 84), frac(55, 84),
    Reference.make("Bourgain", 2017),
)


# ---- Tests ----

def test_format_frac():
    assert Hypothesis._lean_format_frac(frac(0)) == "0"
    assert Hypothesis._lean_format_frac(frac(1)) == "1"
    assert Hypothesis._lean_format_frac(frac(1, 2)) == "(1/2)"
    assert Hypothesis._lean_format_frac(frac(2, 3)) == "(2/3)"
    assert Hypothesis._lean_format_frac(frac(13, 84)) == "(13/84)"


def test_auto_name():
    assert Hypothesis._lean_auto_name(frac(2, 7), frac(4, 7)) == "derived_pair_2_7_4_7"
    assert Hypothesis._lean_auto_name(frac(0), frac(1)) == "derived_pair_0_1"
    assert Hypothesis._lean_auto_name(frac(1, 2), frac(1, 2)) == "derived_pair_1_2_1_2"


def test_trivial_pair():
    lean = trivial.to_lean()
    assert "theorem derived_pair_0_1 : IsExponentPair 0 1 :=" in lean
    assert "trivial_pair" in lean


def test_single_B_transform():
    """B(trivial) = (1/2, 1/2) — single-step, term-mode proof."""
    weyl = _B_transform(trivial, B_transform_hyp)
    lean = weyl.to_lean()
    assert "IsExponentPair (1/2) (1/2)" in lean
    assert "trivial_pair.ofB (by norm_num) (by norm_num)" in lean
    assert ":= by" not in lean


def test_single_A_transform_from_bourgain():
    """A(bourgain) — single step from known axiom."""
    a_bourgain = _A_transform(bourgain, A_transform_hyp)
    lean = a_bourgain.to_lean("bourgain_A")
    assert "theorem bourgain_A" in lean
    assert "bourgain_pair.ofA (by norm_num) (by norm_num)" in lean


def test_two_step_AB():
    """AB(trivial) = (1/6, 2/3) — two-step, tactic-mode proof."""
    weyl = _B_transform(trivial, B_transform_hyp)
    vdc = _A_transform(weyl, A_transform_hyp)
    lean = vdc.to_lean()
    assert "IsExponentPair (1/6) (2/3) := by" in lean
    assert "have h1 : IsExponentPair (1/2) (1/2) := trivial_pair.ofB" in lean
    assert "exact h1.ofA (by norm_num) (by norm_num)" in lean


def test_four_step_BAAB():
    """BAAB(trivial) = (2/7, 4/7) — matches Examples.lean."""
    step1 = _B_transform(trivial, B_transform_hyp)
    step2 = _A_transform(step1, A_transform_hyp)
    step3 = _A_transform(step2, A_transform_hyp)
    step4 = _B_transform(step3, B_transform_hyp)

    lean = step4.to_lean("derived_pair_2_7_4_7_from_trivial")
    assert "theorem derived_pair_2_7_4_7_from_trivial" in lean
    assert "IsExponentPair (2/7) (4/7) := by" in lean
    assert "have h1 : IsExponentPair (1/2) (1/2) := trivial_pair.ofB" in lean
    assert "have h2 : IsExponentPair (1/6) (2/3) := h1.ofA" in lean
    assert "have h3 : IsExponentPair (1/14) (11/14) := h2.ofA" in lean
    assert "exact h3.ofB (by norm_num) (by norm_num)" in lean


def test_five_step_ABAAB():
    """ABAAB(trivial) = (1/9, 13/18) — matches Examples.lean."""
    step1 = _B_transform(trivial, B_transform_hyp)
    step2 = _A_transform(step1, A_transform_hyp)
    step3 = _A_transform(step2, A_transform_hyp)
    step4 = _B_transform(step3, B_transform_hyp)
    step5 = _A_transform(step4, A_transform_hyp)

    lean = step5.to_lean("derived_pair_1_9_13_18_from_trivial")
    assert "theorem derived_pair_1_9_13_18_from_trivial" in lean
    assert "IsExponentPair (1/9) (13/18) := by" in lean
    assert "have h4 : IsExponentPair (2/7) (4/7)" in lean
    assert "exact h4.ofA (by norm_num) (by norm_num)" in lean


def test_custom_theorem_name():
    weyl = _B_transform(trivial, B_transform_hyp)
    lean = weyl.to_lean("weyl_from_trivial")
    assert "theorem weyl_from_trivial" in lean


def test_error_non_exponent_pair():
    try:
        A_transform_hyp.to_lean()
        assert False, "Expected ValueError"
    except ValueError as e:
        assert "Exponent pair" in str(e)


def test_unknown_literature_pair():
    """Unknown pair generates a TODO comment with placeholder axiom."""
    unknown = _make_exp_pair_hyp(
        "Test pair", frac(7, 99), frac(88, 99), Reference.make("Test", 2024)
    )
    lean = unknown.to_lean()
    assert "TODO" in lean
    assert "IsExponentPair (7/99) (8/9)" in lean


def test_convexity_proof_base_case():
    """A hypothesis with multiple exponent pair deps stops the chain."""
    dep1 = _make_exp_pair_hyp("p1", frac(0), frac(1), Reference.trivial())
    dep2 = _make_exp_pair_hyp("p2", frac(1, 2), frac(1, 2), Reference.trivial())
    dep3 = _make_exp_pair_hyp("p3", frac(1, 6), frac(2, 3), Reference.trivial())

    convex = _make_exp_pair_hyp(
        "Convex pair", frac(1, 4), frac(3, 4), Reference.derived(2024),
        deps={dep1, dep2, dep3},
    )
    lean = convex.to_lean()
    assert "TODO" in lean
    assert "IsExponentPair (1/4) (3/4)" in lean


def test_bourgain_axiom():
    """Known literature axiom maps to its Lean name."""
    lean = bourgain.to_lean()
    assert "bourgain_pair" in lean
    assert "IsExponentPair (13/84) (55/84)" in lean


def run_lean_bridge_tests():
    test_format_frac()
    test_auto_name()
    test_trivial_pair()
    test_single_B_transform()
    test_single_A_transform_from_bourgain()
    test_two_step_AB()
    test_four_step_BAAB()
    test_five_step_ABAAB()
    test_custom_theorem_name()
    test_error_non_exponent_pair()
    test_unknown_literature_pair()
    test_convexity_proof_base_case()
    test_bourgain_axiom()


if __name__ == "__main__":
    run_lean_bridge_tests()
    print("All Lean bridge test cases passed.")
