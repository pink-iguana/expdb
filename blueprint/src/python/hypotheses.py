from fractions import Fraction
from typing import Optional

# Basic code for handling hypotheses in the exponent database.  The code here is
# intended to be as flexible and general as possible, anticipating that different
# types of hypotheses will be manipulated in different ways.

########################################################################################
# A Hypothesis is a mathematical assertion that was in the literature, conjectured,
# or derived from other hypotheses.
# It consists of some data (under the 'data' attribute) together with metadata.
# More precisely, it contains the following information:
#
# - name : the short name of the hypothesis, e.g., 'Bourgain bound on \mu(1/2)'
# - hypothesis_type : the type of the hypothesis.  Current supported types:
#    - 'Upper bound on beta'
#    - 'Exponent pair'
#    - 'Exponent pair transform'
#    - 'Upper bound on mu'
#    - 'Large value estimate'
#    - 'Zeta large value estimate'
#    - 'Zero density estimate'
#    - 'Zero density energy estimate'
#    - 'Large value energy region'
#    - 'Large value energy region transform'
# - description : a longer description of the hypothesis, e.g., 'The bound
#       $\mu(1/2) \leq 13/84$'.  Defaults to the description of the underlying data.
# - citation : a reference to where the hypothesis was discovered/proven/conjectured,
#       e.g., 'A paper of Bourgain'.  Use 'Derived' if the hypothesis was generated
#       by the exponent database as a consequence of other existing hypotheses.
# - proof : a human-readable proof of the hypothesis.  (If from the literature,
#       the proof will simply cite the literature.  If a conjecture, states the
#       hypothesis as a conjecture).
# - data : the function or class that computes whatever the hypothesis is., e.g.
#       Bound_mu(1/2, 13/84).  The type of `data` depends on `hypothesis_type`
# - year : the year in which the result was established.  Use 'Derived' if the
#       hypothesis is derived within the database, 'Conjectured' if it is a
#       conjecture rather than a proven result, or 'Classical' if it is too standard
#       to assign a year to.
# - dependencies : the set of hypotheses that the current hypothesis directly
#       depends on (defaults to the empty set).

# Lean code generation is available via the `to_lean()` method.

class Hypothesis:
    def __init__(self, name, hypothesis_type, data, proof, reference):
        self.name = name
        self.hypothesis_type = hypothesis_type
        self.description = data.__repr__()
        self.proof = proof
        self.data = data
        self.reference = reference
        self.dependencies = set()

    # By default, just returns the name of the hypothesis.
    def __repr__(self):
        return self.name

    # Returns the name and description.
    def desc(self):
        return f"{self.name} ({self.description})"

    # Returns the name, description, human-readable proof of the hypothesis.
    def desc_with_proof(self):
        return f"{self.name}: {self.description}.  {self.proof}."

    # Adds a single hypothesis to the set of dependencies.
    def add_dependency(self, fact):
        self.dependencies.add(fact)

    # internal method to add all dependencies of a hypothesis to a Hypothesis_Set
    def add_recursive_dependencies(self, dependency_set):
        dependency_set.add_hypotheses(self.dependencies)
        for subhypothesis in list(self.dependencies):
            subhypothesis.add_recursive_dependencies(dependency_set)

    # Returns the set of all hypotheses that the current hypothesis depends on, recursively.
    def recursive_dependencies(self):
        dependency_set = Hypothesis_Set()
        self.add_recursive_dependencies(dependency_set)
        return dependency_set

    def recursively_list_proofs(self, indentation=0):
        if len(self.dependencies) > 0:
            print(
                "\t" * indentation
                + f"- [{self}]  i.e. {self.data}. {self.proof}. Dependencies:"
            )
            for d in self.dependencies:
                d.recursively_list_proofs(indentation + 1)
        else:
            print("\t" * indentation + f"- [{self}]  i.e. {self.data}. {self.proof}.")

    # Returns True if the hypothesis is of the given type and was established by the given year.
    def is_match(self, hypothesis_type="Any", year="Any"):
        if hypothesis_type == "Any" or hypothesis_type == self.hypothesis_type:
            if (
                year == "Any"
                or self.reference.label == "Derived"
                or self.reference.label == "Classical"
            ):
                return True
            if self.reference.label == "Conjectured":
                return False
            if (
                self.reference.year() != "Unknown date"
                and self.reference.year() <= year
            ):
                return True
        return False

    def proof_complexity(self) -> int:
        """
        Returns the complexity of the proof of this hypothesis. The proof 
        complexity is the total number of Hypothesis objects 
        in the dependency tree of a Hypothesis (including itself). 

        Returns
        -------
        int 
            The proof complexity of this hypothesis.
        """
        return sum(h.proof_complexity() for h in self.dependencies) + 1

    def proof_depth(self) -> int:
        """
        Returns the height of the dependency-tree representation of this 
        hypothesis (including the root and leaves).

        Returns
        -------
        int 
            The maximum depth of the tree that represents the dependency 
            structure of this hypothesis. 
        """
        return 1 + max(d.proof_depth() for d in self.dependencies)

    def proof_date(self) -> int:
        """
        Returns the date of the last dependency, or -1 if unknown. This is the 
        date as of which the result is "effectively proved", even if 
        it does not appear anywhere in the literature as a claimed result.

        Returns 
        -------
        int 
            The year of the latest dependency of this hypothesis, or -1 if unknown.
        """
        year = self.reference.year()
        if year == "Unknown date":
            year = -1
        return max([year] + [h.proof_date() for h in self.dependencies])

    # Lean code generation --------------------------------------------------------

    # Known Lean axiom names for exponent pairs, keyed by (k, l).
    # Extend this dictionary when new axioms are added to the Lean formalization.
    _LEAN_EXPONENT_PAIR_AXIOMS = {
        (Fraction(0), Fraction(1)): "trivial_pair",
        (Fraction(1, 2), Fraction(1, 2)): "weyl_pair",
        (Fraction(1, 6), Fraction(2, 3)): "classical_vdc_pair",
        (Fraction(13, 84), Fraction(55, 84)): "bourgain_pair",
    }

    @staticmethod
    def _lean_format_frac(f):
        """Format a Fraction as a Lean rational literal."""
        f = Fraction(f)
        if f.denominator == 1:
            return str(f.numerator)
        return f"({f.numerator}/{f.denominator})"

    @staticmethod
    def _lean_auto_name(k, l):
        """Generate a Lean theorem name from exponent pair values."""
        k, l = Fraction(k), Fraction(l)
        def part(f):
            if f.denominator == 1:
                return str(f.numerator)
            return f"{f.numerator}_{f.denominator}"
        return f"derived_pair_{part(k)}_{part(l)}"

    def _lean_linearize_proof(self):
        """
        Walk the dependency tree and return a linearized proof chain.

        Returns a list of (hypothesis, lean_ref, transform) tuples where:
        - The first element is the base axiom with lean_ref set to its Lean
          name (or None if unknown) and transform=None.
        - Subsequent elements are derived steps with lean_ref=None and
          transform='A' or 'B'.

        The chain follows van der Corput A/B transforms. If a non-A/B step
        is encountered (e.g. convexity), the chain stops and treats that
        node as a base case.
        """
        steps = []
        current = self

        while True:
            key = (Fraction(current.data.k), Fraction(current.data.l))

            # Leaf node: no dependencies
            if not current.dependencies:
                lean_ref = Hypothesis._LEAN_EXPONENT_PAIR_AXIOMS.get(key)
                steps.append((current, lean_ref, None))
                break

            # Find an A/B transform and the input exponent pair
            transform = None
            input_hyp = None
            for dep in current.dependencies:
                if dep.hypothesis_type == "Exponent pair transform":
                    if dep.name == "van der Corput A transform":
                        transform = "A"
                    elif dep.name == "van der Corput B transform":
                        transform = "B"
                elif dep.hypothesis_type == "Exponent pair":
                    input_hyp = dep

            if transform and input_hyp:
                steps.append((current, None, transform))
                current = input_hyp
            else:
                # Not a simple A/B chain step (convexity, other transforms)
                lean_ref = Hypothesis._LEAN_EXPONENT_PAIR_AXIOMS.get(key)
                steps.append((current, lean_ref, None))
                break

        steps.reverse()
        return steps

    def to_lean(self, theorem_name=None):
        """
        Generate a Lean 4 theorem proving this exponent pair from its
        dependency tree.

        Currently supports hypotheses of type 'Exponent pair' whose proofs
        consist of chains of van der Corput A and B transforms applied to
        known literature axioms. Convexity-based proofs and other transform
        types are partially supported: the chain is traced as far as
        possible, and any unsupported base case is flagged with a TODO
        comment.

        Parameters
        ----------
        theorem_name : str, optional
            Name for the generated Lean theorem. If not provided, a name is
            auto-generated from the exponent pair values.

        Returns
        -------
        str
            A string containing a valid Lean 4 theorem statement and proof.

        Raises
        ------
        ValueError
            If the hypothesis type is not 'Exponent pair'.

        Examples
        --------
        >>> from literature import *
        >>> A = literature.find_hypothesis(keywords="van der Corput A transform")
        >>> B = literature.find_hypothesis(keywords="van der Corput B transform")
        >>> pair = B.data.transform(trivial_exp_pair)
        >>> pair = A.data.transform(pair)
        >>> print(pair.to_lean())
        theorem derived_pair_1_6_2_3 : IsExponentPair (1/6) (2/3) := by
          have h1 : IsExponentPair (1/2) (1/2) := trivial_pair.ofB (by norm_num) (by norm_num)
          exact h1.ofA (by norm_num) (by norm_num)
        """
        if self.hypothesis_type != "Exponent pair":
            raise ValueError(
                f"to_lean() currently only supports 'Exponent pair' hypotheses, "
                f"got '{self.hypothesis_type}'"
            )

        fmt = Hypothesis._lean_format_frac
        steps = self._lean_linearize_proof()

        k_str = fmt(self.data.k)
        l_str = fmt(self.data.l)
        name = theorem_name or Hypothesis._lean_auto_name(self.data.k, self.data.l)

        base_hyp, base_ref, _ = steps[0]

        # Handle missing axiom reference
        if base_ref is None:
            bk = fmt(base_hyp.data.k)
            bl = fmt(base_hyp.data.l)
            placeholder = Hypothesis._lean_auto_name(base_hyp.data.k, base_hyp.data.l)
            comment = (
                f"-- TODO: The following axiom is needed but not yet in the Lean "
                f"formalization.\n"
                f"-- axiom {placeholder} : IsExponentPair {bk} {bl}\n"
            )
            base_ref = placeholder
        else:
            comment = ""

        # Single element: just the axiom itself
        if len(steps) == 1:
            return (
                f"{comment}theorem {name} : IsExponentPair {k_str} {l_str} :=\n"
                f"  {base_ref}"
            )

        # Two elements: single transform, use term-mode proof
        if len(steps) == 2:
            _, _, transform = steps[1]
            return (
                f"{comment}theorem {name} : IsExponentPair {k_str} {l_str} :=\n"
                f"  {base_ref}.of{transform} (by norm_num) (by norm_num)"
            )

        # Three or more: tactic-mode proof with have chain
        lines = [
            f"{comment}theorem {name} : IsExponentPair {k_str} {l_str} := by"
        ]
        for i in range(1, len(steps)):
            hyp, _, transform = steps[i]
            prev_ref = base_ref if i == 1 else f"h{i - 1}"
            hk = fmt(hyp.data.k)
            hl = fmt(hyp.data.l)

            if i < len(steps) - 1:
                lines.append(
                    f"  have h{i} : IsExponentPair {hk} {hl} := "
                    f"{prev_ref}.of{transform} (by norm_num) (by norm_num)"
                )
            else:
                lines.append(
                    f"  exact {prev_ref}.of{transform} (by norm_num) (by norm_num)"
                )

        return "\n".join(lines)


########################################################################################
# A Hypothesis_Set is, as the name suggests, a set of hypotheses.  This will be an input parameter in various exponent calculation routines in the database, which seek to answer questions like "What is the best zero-density bound known for sigma = 3/4 assuming [a given list of hypotheses]"

# In the future, we can allow lists of hypotheses to store precomputed data to speed up calculations.  For instance, if the list of hypotheses contains exponent pairs, we can permit the list to store the convex hull of these pairs.  A routine that wants to compute this convex hull can first look to see if the convex hull has already been computed, and use it if available, otherwise it will compute it and store it in the list.  This way, such computations only need to be performed once.

# Similarly, we can develop methods to self-improve lists of hypotheses.  For instance, if a list of hypotheses contains exponent pairs, we can create methods to discover all zeta function moment bounds that can be derived from those pairs, add those to the list of hypotheses, and remove duplicate or redundant hypotheses in the combined list.


class Hypothesis_Set:
    def __init__(self, hypotheses=set()):
        self.hypotheses = set()
        self.add_hypotheses(hypotheses)
        self.data = {}
        self.data_valid = False  # set to false whenever data needs to be recomputed

    def __repr__(self):
        return f'Set of {len(self.hypotheses)} hypotheses: [{",".join(h.name for h in self.hypotheses)}]'

    # Shallow copy, the hypothesis objects are not cloned
    def __copy__(self):
        copy = Hypothesis_Set(self.hypotheses)
        copy.data = self.data
        copy.data_valid = self.data_valid
        return copy

    def __iter__(self):
        return self.hypotheses.__iter__()

    def __next__(self):
        return self.hypotheses.__next__()

    def __len__(self):
        return len(self.hypotheses)

    def to_list(self):
        return list(self.hypotheses)

    def list_proofs(self):
        for hypothesis in self:
            print(hypothesis.desc_with_proof())

    # Adds a single hypothesis to the hypothesis set.
    # If invalidate_data is true, then the precomputed, cached data (e.g. a convex hull)
    # is invalidated and will be recomputed at the next proof function call. In certain
    # cases calls of this function are guaranteed to not require recomputation of cached
    # data (e.g. in prove_mu_bound where we insert a valid bound on \mu(\sigma) derived
    # from other bounds; such a bound is guaranteed to not enlarge the precomputed convex
    # hull)
    def add_hypothesis(self, hypothesis, invalidate_data=True):
        self.hypotheses.add(hypothesis)
        if invalidate_data:
            self.data_valid = False

    # Adds a set or list of hypotheses, an individual hypothesis, or a Hypothesis_Set
    def add_hypotheses(self, new_hypotheses, invalidate_data=True):
        if isinstance(new_hypotheses, Hypothesis):
            self.add_hypothesis(new_hypotheses, invalidate_data)
        elif isinstance(new_hypotheses, Hypothesis_Set):
            self.add_hypotheses(new_hypotheses.hypotheses, invalidate_data)
        elif isinstance(new_hypotheses, list):
            self.add_hypotheses(set(new_hypotheses), invalidate_data)
        else:
            self.hypotheses.update(new_hypotheses)
            if invalidate_data:
                self.data_valid = False

    # return all hypotheses of a given type, and (optionally) up to a given year.  Note: is now returning a Hypothesis_Set rather than a list
    def list_hypotheses(self, hypothesis_type="Any", year="Any"):
        return [
            hypothesis
            for hypothesis in self
            if hypothesis.is_match(hypothesis_type, year)
        ]

    
    def find_hypothesis(
        self, hypothesis_type="Any", data="Any", name="Any", keywords="Any", year="Any"
    ) -> Optional[Hypothesis]:
        """
        Returns the first instance of a Hypothesis in the set that matches the 
        specified requirements.

        Parameters
        ----------
        hypothesis_type : str, optional
            The type of the hypothesis, e.g. "Exponent pair" (default is "Any").
        data : str or object, optional
            The data that the hypothesis contains, e.g. an object of type Exp_pair
            (default is "Any").
        name : str, optional
            The full name of the hypothesis, e.g. "Jutila large value theorem with k = 3"
            (default is "Any").
        keywords : str, optional
            A comma-separated list of keywords to search for in the name of the 
            hypothesis (default is "Any").
        year : str or int, optional
            The year of the hypothesis (default is "Any").
        
        Returns
        -------
        Hypothesis or None
            The first hypothesis that matches all conditions, or None if no such 
            hypothesis exists. 
        """
        for h in self:
            if hypothesis_type == "Any" or h.hypothesis_type == hypothesis_type:
                if data == "Any" or h.data == data:
                    if name == "Any" or h.name == name:
                        if keywords == "Any" or all(
                            k.strip() in h.name for k in keywords.split(",")
                        ):
                            if year == "Any" or h.reference.year() == year:
                                return h
        print("ERROR: No matching hypothesis found")
        return None
