
def formula_to_nnf(formula):
    """
    Takes a formula and returns an equivalent formula in negation normal form (nnf).
    """
    
    def _other_andor(andor):
        return '∧' if andor == '∨' else '∨'

    match formula:
        # Every formula is either an atom, conjunction, disjunction, or negation.
        case str():
            # Atoms are already in nnf.
            return formula
        case (φ, andor, ψ) if andor in {'∧', '∨'}:
            # Assuming formula_to_nnf works for subformulae, the following is equivalent to the original formula and is in nnf.
            return (formula_to_nnf(φ), andor, formula_to_nnf(ψ))
        case ('¬', _):
            match formula:
                # Every negation is a negated atom, negated conjunction, negated disjunction, or negated negation.
                case ('¬', str()):
                    # Negated atoms are already in nnf.
                    return formula
                case ('¬', (φ, andor, ψ)) if andor in {'∧', '∨'}:
                    # If formula_to_nnf works for the negations of the subformulae, the following is equivalent to the original formulae by DeMorgan's and is in nnf.
                    return (formula_to_nnf(('¬', φ)), _other_andor(andor), formula_to_nnf(('¬', ψ)))
                case ('¬', ('¬', φ)):
                    # If formula_to_nnf works for the subformula of the subformula then the following is equivalent to the original formula by double negation and is in nnf.
                    return formula_to_nnf(φ)
                case _:
                    assert False
        case _:
            assert False
        # Correctness follows by induction on the number of symbols in the formula.

def nnf_to_nested_sets(nnf_formula):
    """
    In the nested sets representation, an formula is represented as either a literal or a set of formulae that are represented as nested sets.  Sets at even level (including 0) are either conjunctive or disjunctive, the sets at odd level are the other thing.  The representation is slightly ambiguous as it does not fix which level parity is conjunctive and which is disjunctive, but this can be resolved by specifying externally whether level 0 is conjunctive or disjunctive.  The terms “evenjunction” and “oddjunction” may be used at points in this codebase to generically refer to the kind of junction represented by even and odd leveled sets, respectively without assuming which of these is conjunctive and which is disjunctive.
    
    Note that here we use frozenset because ordinary sets are unhashable and cannot themselves be members of sets in Python.

    For example, ((P ∧ Q) ∨ ((R ∨ S) ∧ (T ∧ U))) is represented as:
        {{P, Q}, {{R, S}, T, U}}
    with the outermost set set being disjunctive.
    
    Similarly, ((P ∨ P) ∧ Q) is represented by {{P}, Q} with the outermost set being conjunctive.

    This function takes an nnf expresion and returns an equivalent nested sets representation together with a 1 if the outermost set is conjunctive, a -1 is disjunctive, and 0 if literal.

    """
    formula = nnf_formula

    match formula:
        # Every nnf formula is either a literal, or a junction of nnf formulae.
        case ('¬', a) | a if isinstance(a, str):
            # Given a literal, `nnf_to_nested_sets` works trivially.
            return formula, 0
        case (φ, andor, ψ) if andor in {'∧', '∨'}:
            # Now, consider a junction and suppose `nnf_to_nested_sets` works correctly for both juncts.  We need to show that the set that is returned, with the junction type indicator, correctly represents the nnf formula.

            # This junction type indicator returned is clearly correct.
            junction_type = 1 if andor == '∧' else -1 
            
            # By virtue of this, the set we return represents the same type of junction at the top level as the junction received.

            φ_nested_sets, φ_junction_type = nnf_to_nested_sets(φ)
            ψ_nested_sets, ψ_junction_type = nnf_to_nested_sets(ψ)
            # `nnf_to_nested_sets` returns, along with the junct type, a set exactly that which is either a junct of `formula` that cannot be “merged” with the top level set (i.e. is a literal or a junction of different junction type), or is an element of the nested sets representation of a junct of `formula` that can be “merged” with the top level set (i.e. is a junction of the same junction type).
            return ((
                    φ_nested_sets if φ_junction_type == junction_type else frozenset({φ_nested_sets})
                ).union(
                    ψ_nested_sets if ψ_junction_type == junction_type else frozenset({ψ_nested_sets})
            ), junction_type)
    # Correctness follows by induction on the height of the formula.

def _s(*args):
    """
    Helper function that acts as a concise constructor for constructing a frozenset from zero or more items-to-be.
    """
    return frozenset(args)

def _sb(iterator):
    """
    Helper function that acts as a concise constructor for constructing a frozenset from an iterator of items-to-be.
    """
    return frozenset(iterator)

def nested_sets_to_jnf(nested_sets):
    """
    Takes a nested sets representation of a formula (without the junction type indicator) and flattens it into an junctive normal form that is equivalent to the original (under the same junction type as the original).  In nested_sets_to_jnf, we use the term “node” we mean either a literal or a set in a nested sets representation.  A junctive normal form is a nested sets representation where the level 0 node is a set, all level 1 nodes are sets, and all level 2 nodes are literals.
    """

    def is_literal(node):
        return isinstance(node, str) or isinstance(node, tuple)
    
    def is_set(node):
        return not is_literal(node)
    
    if is_literal(nested_sets):
        # A singleton evenjunction of a singleton oddjunction of a literal is equivalent to the original literal and has two levels.
        return _s(_s(nested_sets))
    
    level_0_set = nested_sets

    def find_level_2_set(level_0_set):
        """
        Given a level 0 set, returns a level 2 set if it exists; returns None otherwise.
        """

        # The level 1 sets are the sets in the level 0 set.
        for level_1_node in level_0_set:
            if is_set(level_1_node):
                # The level 2 sets are the sets in the level 1 sets.
                for level_2_node in level_1_node:
                    if is_set(level_2_node):
                        return level_2_node
        # If we reach this point, there is no level 2 set so we return None.
        return None

    level_2_set = find_level_2_set(level_0_set)

    if level_2_set is None:
        # nested_set has at most two levels.
        # enclosing a literal in a singleton maintains equivalence.
        # doing this for every level 1 literal results in an equivalent nested set representation where the level 0 node is a set, every level 1 node is a set, and every level 2 node is a literal.
        ret = _sb(_s(level_1_node) if is_literal(level_1_node) else level_1_node for level_1_node in level_0_set)
        return ret

    if len(level_0_set) == 1:
        level_1_set = next(iter(level_0_set))
        rest_of_level_1_set = level_1_set - _s(level_2_set)

        recurrendum = _sb(_s(*(_s(e2) if is_literal(e2) else e2), *rest_of_level_1_set) for e2 in level_2_set)

        # The recurrendum is related to the original nested sets by the following transformation:
        #       {{{a…, {bⱼ…}…}, c…}}
        #   ▷ {{aᵢ, c…}…, {bⱼ…, c…}…}
        # Here, a… is 0 or more literals aᵢ, {bⱼ…}… are sets of 0 or more nodes bⱼₖ, and c… is 0 or more nodes.
        # The original formula (at this point in the code) is known to fit the form of the starting point of the transformation because it has a single level 1 node, its level 1 node is a set, and it has at least one level 2 set in the level 1 set.
        
        # The transformation results in an equivalent nested sets representation by the following:
        # {{{a…, {bⱼ…}…}, c…}}
        # ≡ E(O(E(a…, O(bⱼ…)…), c…)) where E and O are evenjunction and oddjunction respectively;
        # ≡ O(E(a…, O(bⱼ…)…), c…) since the outer evenjunction had one operand;
        # ≡ E(O(aᵢ, c…)…, O(O(bⱼ…), c…)…) by distribution of the outer oddjunction over the evenjunction;
        # ≡ E(O(aᵢ, c…)…, O(bⱼ…, c…)…) by combining the nested oddjunctions;
        # ≡ {{aᵢ, c…}…, {bⱼ…, c…}…} by translating back into nested sets.

        # For a more concrete example of this line of reasoning:
        # {{{a₁, a₂, {b₁₁, b₁₂}, {b₂₁, b₂₂}}, c₁, c₂}} where a₁, a₂ are literals and the rest are nodes;
        # ≡ E(O(E(a₁, a₂, O(b₁₁, b₁₂), O(b₂₁, b₂₂)), c₁, c₂)) where E and O are evenjunction and oddjunction respectively;
        # ≡ O(E(a₁, a₂, O(b₁₁, b₁₂), O(b₂₁, b₂₂)), c₁, c₂) since the outer evenjunction had one operand;
        # ≡ E(O(a₁, c₁, c₂), O(a₂, c₁, c₂), O(O(b₁₁, b₁₂), c₁, c₂), O(O(b₂₁, b₂₂), c₁, c₂))) by distribution of the outer oddjunction over the evenjunction;
        # ≡ E(O(a₁, c₁, c₂), O(a₂, c₁, c₂), O(b₁₁, b₁₂, c₁, c₂), O(b₂₁, b₂₂, c₁, c₂))) by combining the nested oddjunctions;
        # ≡ {{{a₁, c₁, c₂}, {a₂, c₁, c₂}, {b₁₁, b₁₂, c₁, c₂}, {b₂₁, b₂₂, c₁, c₂}}} by translating back into nested sets.

        # Assuming nested_sets_to_jnf works for the recurrendum, this is correct.
        return nested_sets_to_jnf(recurrendum)

    # level_0_set is of the form {{aᵢ…}…} where there are at least two {aᵢ…} and each {aᵢ…} is a set of nodes.  Assuming nested_sets_to_jnf works on each {{aᵢ…}}:
    # {{aᵢ…}…} ≡ ∪({{aᵢ…}}…) ≡ ∪(nested_sets_to_jnf({{aᵢ…}})…)
    # and the latter is in jnf.
    ret = _s().union(*(nested_sets_to_jnf(_s(level_1_set)) for level_1_set in level_0_set))
    assert find_level_2_set(ret) is None
    
    # This function always recurs either on a set with strictly lower depth, or the same depth but strictly fewer elements.  Thus, correctness follows by induction.

    return ret

def formula_to_cnf(formula):
    """
    Takes a formula and returns a cnf nested sets representation equivalent to that formula.
    """

    # `nested_sets` is equivalent to `formula` under the junction type `junction_type`.
    nested_sets, junction_type = nnf_to_nested_sets(formula_to_nnf(formula))
    # If `junction_type` is conjunction, then `nested_sets_to_jnf(nested_sets)` is a conjunctive normal form of `formula`.  If `junction_type` is not conjunction, then it is either disjunction or literal.  If `junction_type` is disjunction, then {`nested_sets`} is equivalent under conjunction to `nested_sets` under disjunction, and `nested_sets_to_jnf({nested_sets})` is a conjunctive normal form of `formula`.  Otherwise, `formula` is a literal, {`nested_sets`} is equivalent under conjunction to `formula`, and so `nested_sets_to_jnf({nested_sets}) is a conjunctive normal form of `formula`.
    return nested_sets_to_jnf(nested_sets if junction_type == 1 else _s(nested_sets))


def literal_complement(literal):
    """
    Given an literal (an atom or negated atom), returns the literal that is equivalent to the literal's negation.
    """
    return ('¬', literal) if isinstance(literal, str) else literal[1]

def resolve(clause, other):
    """
    Given a clause `clause` and another clause `other`, returns the result of the resolution inference rule applied to the two clauses if resolution is applicable, or None if not.  Resolution is applicable if there is some literal L in `clause` whose complement is in `other`.  The result of resolution would then be a new clause that is the set of literals in `clause` except for L unioned with the set of literals in `other` except for the complement of L.
    """
    # It is straightforward to see that this code maps directly to the specification.
    for literal in clause:
        if literal_complement(literal) in other:
            return (clause - _s(literal)).union(other - _s(literal_complement(literal)))
    return None

from collections import deque
def is_cnf_unsatisfiable(cnf_formula):
    """
    Takes a cnf formula as a depth two nested set and, using resolution, returns True if unsatisfiable and False otherwise.
    """

    # We take for granted that if `cnf_formula` is inconsistent, then the empty clause is obtainable through some sequence of resolutions.  This was proven in J. A. Robinson's 1965 paper “A Machine-Oriented Logic Based on the Resolution Principle”, accessible at https://dl.acm.org/doi/10.1145/321250.321253.

    # let closure(`cnf_formula`) denote the closure of `cnf_formula` under resolution, and let one_step(`tried`) denote the set of clauses that can be obtained by a single resolution step between some pair of clauses in `tried`.

    # Loop invariants (for the outer while loop:
    # • one_step(`tried`) ⊆ `to_try_set` ∪ `tried`.
    # • `to_try_set` = `set(to_try_deque)`
    # • `len(to_try_deque)` = `len(to_try_set)`.
    # • `cnf_formula` ⊆ `to_try_set` ∪ `tried`.
    # • `to_try_set` ∪ `tried` ⊆ closure(`cnf_formula`)
    # • `tried` = n_steps(`cnf_formula`, while_itr)


    # The loop invariants are trivially satisfied before entering the while loop.
    tried = set()
    to_try_set = set(cnf_formula)
    to_try_deque = deque(cnf_formula)

    while len(to_try_deque) > 0:
        # Assume while loop's invariants for induction.
        clause = to_try_deque.popleft()
        to_try_set.remove(clause)
        # • `to_try_set′` = `set(to_try_deque′)`
        # • `len(to_try_deque′)` = `len(to_try_set′)`.

        if len(clause) == 0:
            return True
        tried.add(clause)
        # • `cnf_formula` ⊆ `to_try_set′` ∪ `tried′`.
        # • `tried′` ∪ `to_try_set′` ⊆ closure(`cnf_formula`)
        # • `cnf_formula` ⊆ `to_try_set′` ∪ `tried′`.
        # for_itr := 0
        # Invariants for for loop:
        # • one_step(`tried′`) ⊆ `to_try_set′` ∪ `tried′` ∪ {`resolve`(`clause`, other) : other ∈ `tried′`[for_itr:] ∧ `resolve`(`clause`, other) ≠ `None`} where `tried′`[for_itr:] denotes all elements from for_itr and beyond, indexing from 0, in an enumeration of the elements of `tried` that has as a prefix the sequence of elements through which the for loop will eventually end up iterating.
        # • `to_try_set′` = `set(to_try_deque′)`.
        # • `len(to_try_deque′)` = `len(to_try_set′)`.
        # • `to_try_set′` ∪ `tried′` ⊆ closure(`cnf_formula`).
        # • `cnf_formula` ⊆ `to_try_set′` ∪ `tried′`.
        # These are currently all satisfied.
        for other in tried: # `other` ∈ `tried′`
            # Assume for loop's invariants for induction.
            # for_itr := for_itr + 1
            # `clause`, `other` ∈ closure(`cnf_formula`).
            resolved = resolve(clause, other)
            # `resolved` = `None` or `resolved` ∈ closure(`cnf_formula`).
            if resolved is not None and resolved not in tried and resolved not in to_try_set:
                # `resolved` ∈ closure(`cnf_formula`).
                # `resolved` ∉ `tried′` ∪ `to_try_set′`.
                to_try_set.add(resolved)
                to_try_deque.append(resolved)
                # • one_step(`tried′`) ⊆ `to_try_set′′` ∪ `tried′` ∪ {`resolve`(`clause`, other) : other ∈ `tried′`[for_itr′:] ∧ `resolve`(`clause`, other) ≠ `None`}
                # • `to_try_set′′` = `set(to_try_deque′′)`.
                # • `len(to_try_deque′′)` = `len(to_try_set′′)`.
                # • `to_try_set′′` ∪ `tried′` ⊆ closure(`cnf_formula`).
                # • `cnf_formula` ⊆ `to_try_set′′` ∪ `tried′`.
            # else:
                # All for loop invariants are preserved.
        # All for loop invariants still hold.
        # Since for_itr′ = `len(tried′)`, we have one_step(`tried′`) ⊆ `to_try_set′′` ∪ `tried′`.
        # We hence have all our while loop invariants preserved.

    # We conclude by noting that `set(to_try_deque)` = `to_try_set` = ø.  Since `cnf_formula` ⊆ `to_try_set` ∪ `tried`, we have `cnf_formula` ⊆ `tried`.  However, we also have one_step(`tried`) ⊆ `to_try_set` ∪ `tried` = `tried`, so `tried` is closed under resolution.  We can get more here.  Since `cnf_formula` ⊆ `tried`, we have closure(`cnf_formula`) ⊆ `tried`.  On the other hand, `tried` ⊆ closure(`cnf_formula`), so `tried` = closure(`cnf_formula`).  

    # If `cnf_formula` were unsatisfiable, then by Robinson 1965 we would have ø ∈ closure(`cnf_formula`) = `tried`.  But, we can see from the conditional return in the while loop that ø ∉ `tried`. By contrapositive, `cnf_formula` is satisfiable.

    return False # not unsatisfiable

    # `is_cnf_unsatisfiable` always terminates because each iteration of the while loop (if True isn't returned) adds a clause into `to_try_set`, each clause added to `to_try_set` is not already in `to_try_set` ∪ `tried`, once a clause is added to `to_try_set` it stays in `to_try_set` ∪ `tried`, we have `to_try_set` ∪ `tried` ⊆ closure(`cnf_formula`), and closure(`cnf_formula`) is finite because every clause in closure(`cnf_formula`) is a set of literals formed from atoms that occur in `cnf_formula`, and there are only finitely many such sets of literals because there are only finitely many `atoms` that occur in `cnf_formula`.  All this means that the while loop can only go for finitely many iterations.

def is_formula_tautology(formula):
    return is_cnf_unsatisfiable(formula_to_cnf(('¬', formula)))


## IO stuff

def _parse(tokens, idx):
    ast = []
    assert tokens[idx] == '('
    while True:
        idx += 1
        t = tokens[idx]
        match t:
            case ')':
                return tuple(ast), idx
            case '(':
                subparsed, idx = _parse(tokens, idx)
                ast.append(subparsed)
            case a:
                ast.append(a)


def ensure_formula(ast):
    if isinstance(ast, str):
        return ast
    match ast:
        case (φ, andor, ψ) if andor in ('∧', '∨'):
            return (ensure_formula(φ), andor, ensure_formula(ψ))
        case ('¬', φ):
            return ('¬', ensure_formula(φ))
        case _:
            assert False

def parse(s):
    """
    Parses strings to formulae if the string is well-formed according to the following syntax, and errors otherwise.

    Syntax:
        Formula ::= Atom | ComplexFormula
        Atom ::= ⟨string without whitespace or parentheses⟩
        ComplexFormula ::= '(' '¬' Formula ')' | '(' Formula '∧' Formula ')' | '(' Formula '∨' Formula ')'
    """
    tokens = s.replace('(', ' ( ').replace(')', ' ) ').split()
    ast, idx = _parse(tokens, 0)
    assert idx == len(tokens) - 1
    return ensure_formula(ast)

def frozen_set_to_str(frozen_set):
    if not isinstance(frozen_set, (frozenset, set)):
        return str(frozen_set)
    return "{" + ", ".join(frozen_set_to_str(el) for el in frozen_set) + "}"

def print_frozen_set(frozen_set):
    print(frozen_set_to_str(frozen_set))

## Testing stuff

def eval_formula_on_tvs(formula, tvs):
    """
    Takes a formula and a truth assignment and returns the truth value of that formula for that truth assignment.  The truth assignment is taken as a dictionary from atoms to their truth values in the assignment.
    """
    match formula:
        case str():
            return tvs[formula]
        case (φ, '∧', ψ):
            return eval_formula_on_tvs(φ, tvs) and eval_formula_on_tvs(ψ, tvs)
        case (φ, '∨', ψ):
            return eval_formula_on_tvs(φ, tvs) or eval_formula_on_tvs(ψ, tvs)
        case ('¬', φ):
            return not eval_formula_on_tvs(φ, tvs)
        case _:
            assert False

def formula_get_atoms(formula):
    """
    Gets the set of atoms that appear in the formula.
    """
    match formula:
        case str():
            return _s(formula)
        case (φ, andor, ψ) if andor in {'∧', '∨'}:
            return formula_get_atoms(φ).union(formula_get_atoms(ψ))
        case ('¬', φ):
            return formula_get_atoms(φ)

def get_truth_assignments(n):
    """
    Takes nonnegative integer n and returns an iterator through the sequences of n booleans startingfrom all false and progressing as one would count in binary in big endian.  For example, the truth assignments for atoms P, Q, and R would go:

    P Q R
    —————
    F F F
    F F T
    F T F
    F T T
    T F F
    T F T
    T T F
    T T T
    """

    if n == 0:
        yield tuple()
    else:
        for assignment in get_truth_assignments(n - 1):
            yield assignment + (False,)
            yield assignment + (True,)

def make_tt_for_formula(formula, atom_ordering):
    """
    Takes a formula and a sequence of the atom_ordering in the formula (which must contain exactly the atoms in the formula with no duplicates) and returns an iterator through the truth value of the formula corresponding with the order of assignments specified by get_truth_assignments.  
    """
    atom_set = formula_get_atoms(formula)
    assert _sb(atom_ordering) == atom_set and len(atom_ordering) == len(atom_set)

    for assignment in get_truth_assignments(len(atom_ordering)):
        yield eval_formula_on_tvs(formula, {atom_ordering[i] : assignment[i] for i in range(len(atom_ordering))})


def eval_cnf_on_tvs(cnf, tvs):
    """
    Takes a cnf formula (as a nested set of depth two) and a truth assignment and returns the truth value of that formula for that truth assignment.  The truth assignment is taken as a dictionary from atoms to their truth values in the assignment.
    """
    return all(any(tvs[literal] if isinstance(literal, str) else not tvs[literal[1]] for literal in clause) for clause in cnf)

def jnf_get_atoms(jnf):
    """
    Gets the set of atoms that appear in a given (con/dis)junctive normal form formula, taken as a nested set of depth 2.
    """
    return _s().union(*(_sb(el if isinstance(el, str) else el[1] for el in el) for el in jnf))

def make_tt_for_cnf(cnf, atom_ordering):
    """
    Takes a cnf formula (represented as a nested set of depth 2) and a sequence of the atom_ordering in the formula (which must contain exactly the atoms in the formula with no duplicates) and returns an iterator through the truth value of the formula corresponding with the order of assignments specified by get_truth_assignments.
    """
    atom_set = jnf_get_atoms(cnf)
    assert _sb(atom_ordering) == atom_set and len(atom_ordering) == len(atom_set)

    for assignment in get_truth_assignments(len(atom_ordering)):
        yield eval_cnf_on_tvs(cnf, {atom_ordering[i] : assignment[i] for i in range(len(atom_ordering))})


import random
def random_formula_of_depth_at_most(d, atoms):
    if d == 0:
        return random.choice(atoms)
    continuing_probability = 0.8
    φ = random_formula_of_depth_at_most(d - 1 if random.random() < continuing_probability else 0, atoms)
    ψ = random_formula_of_depth_at_most(d - 1 if random.random() < continuing_probability else 0, atoms)
    return ((φ, '∧', ψ), (φ, '∨', ψ), ('¬', φ))[random.randrange(3)]


def run_tests():

    assert is_formula_tautology(parse("((¬ (((¬ P) ∨ Q) ∧ P)) ∨ Q)")) # modus ponens
    assert is_formula_tautology(parse("((¬ (((¬ P) ∨ Q) ∧ ((¬ Q) ∨ R))) ∨ ((¬ P) ∨ R))")) # hypothetical syllogism
    assert parse("((P ∧ S) ∧ (Q ∨ (R ∧ T)))") == (('P', '∧', 'S'), '∧', ('Q', '∨', ('R', '∧', 'T')))
    assert parse("(¬ P)") == ('¬', 'P')
    assert formula_to_nnf(parse("(¬ (¬ P))")) == 'P'
    assert formula_to_nnf(parse("(¬ ((¬ P) ∨ (¬ Q)))")) == parse("(P ∧ Q)")
    assert formula_to_nnf(parse("(¬ (P ∧ (¬ Q)))")) == parse("((¬ P) ∨ Q)")
    assert nnf_to_nested_sets(parse("((P ∧ Q) ∨ ((R ∨ S) ∧ (T ∧ U)))")) == (_s(_s('P', 'Q'), _s(_s('R', 'S'), 'T', 'U')), -1)
    assert formula_get_atoms(parse("((P ∧ S) ∧ (Ϙ ∨ (P ∧ T)))")) == _s('P', 'S', 'Ϙ', 'T')
    assert tuple(get_truth_assignments(3)) == ((False, False, False), (False, False, True), (False, True, False), (False, True, True), (True, False, False), (True, False, True), (True, True, False), (True, True, True))
    assert tuple(make_tt_for_formula(parse('(¬ (P ∧ (¬ Q)))'), ('P', 'Q'))) == (True, True, False, True)
    assert tuple(make_tt_for_formula(parse('((¬ P) ∨ Q)'), ('P', 'Q'))) == (True, True, False, True)
    assert tuple(make_tt_for_formula(parse('(Q ∨ (¬ (P ∨ R)))'), ('P', 'Q', 'R'))) == (True, False, True, True, False, False, True, True)
    assert jnf_get_atoms(_s(_s('P', ('¬', 'R')), _s('T', ('¬', 'π')))) == _s('P', 'R', 'T', 'π')

    def test_cnf_conversion(formula):
        atom_ordering = tuple(formula_get_atoms(formula))
        # print(tuple(make_tt_for_cnf(formula_to_cnf(formula), atom_ordering)))
        # print(tuple(make_tt_for_formula(formula, atom_ordering)))
        assert tuple(make_tt_for_cnf(formula_to_cnf(formula), atom_ordering)) == tuple(make_tt_for_formula(formula, atom_ordering))

    test_cnf_conversion(parse("(P ∧ Q)"))
    test_cnf_conversion(parse("((¬ ((¬ P) ∧ Q)) ∨ ((¬ (R ∨ S)) ∧ (¬ (T ∧ (¬ U)))))"))
    test_cnf_conversion(parse("(((¬ ((P ∧ (¬ Q)) ∨ (R ∧ S))) ∧ ((T ∨ (¬ U)) ∧ ((¬ V) ∨ ((W ∧ X) ∧ (¬ Y))))) ∨ ((¬ (P ∨ Q)) ∧ ((¬ R) ∨ ((S ∧ (¬ T)) ∧ (U ∨ (¬ (V ∧ W)))))))"))
    test_cnf_conversion(parse("(((¬ P) ∧ (W ∨ (¬ R))) ∨ ((S ∧ (¬ U)) ∧ ((¬ U) ∨ ((V ∧ W) ∨ ((¬ X) ∧ (Q ∨ (¬ P)))))))"))

    def test_resolution(formula):
        is_taut = all(make_tt_for_formula(formula, tuple(formula_get_atoms(formula))))
        assert is_taut == is_formula_tautology(formula)
        return is_taut

    for i in range(100):
        test_cnf_conversion(random_formula_of_depth_at_most(3, ('P', 'Q', 'R', 'S', 'T')))

    for i in range(100):
        test_cnf_conversion(random_formula_of_depth_at_most(6, ('P', 'Q', 'R', 'S', 'T')))

    N = 10000
    taut_count = 0
    for i in range(N):
        was_taut = test_resolution(random_formula_of_depth_at_most(4, ('P', 'Q', 'R')))
        taut_count += was_taut
    assert taut_count / N > 0.06 # if there are no tautologies then we're not testing much.

    N = 500
    taut_count = 0
    for i in range(N):
        was_taut = test_resolution(random_formula_of_depth_at_most(5, ('P', 'Q', 'R', 'S', 'T')))
        taut_count += was_taut
    assert taut_count / N > 0.03

import argparse

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-t', action='store_true')
    parser.add_argument('-f')        

    try:
        args = parser.parse_args()
    except SystemExit:
        print("Usage: python3 atp.py [-t] [-f <file with formula to check>].")
        exit(1)
    
    if not (args.t or args.f):
        print("Must specify at least -t or -f.")
        exit(1)
    
    if args.t:
        run_tests()
        print("Tests passed")
        
    if args.f:
        with open(args.f) as file:
            contents = file.read()
            print("Tautology" if is_formula_tautology(parse(contents)) else "Not a tautology")

if __name__ == '__main__':
    main()