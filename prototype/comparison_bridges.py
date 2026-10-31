"""Exact toy algebra for two-star bridges and three-point extraction.

This is not an end-to-end proof system or a security estimator. Oracle replies
must already have been checked against the same frozen protocol prefix. The
matrix tests below validate returned kernel certificates; they do not establish
uniform-matrix hardness. Only small explicitly enumerated challenge sets are
supported by the sampler. Integer kernel vectors are never reduced modulo q.
"""

from dataclasses import dataclass
from fractions import Fraction
from .quadratic_fold import Ring


def _positive_integer(value, name, *, zero=False):
    if type(value) is not int or value < (0 if zero else 1):
        raise ValueError(f"invalid {name}")
    return value


def _element(ring, value):
    if len(value) != ring.N or any(type(c) is not int for c in value):
        raise ValueError("invalid integer ring element")
    return tuple(value)


def integer_mul(ring, left, right):
    """Product in Z[X]/(X^N+1), without reduction modulo q."""
    left, right = _element(ring, left), _element(ring, right)
    result = [0] * ring.N
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[(i + j) % ring.N] += (1 if i + j < ring.N else -1) * a * b
    return tuple(result)


def _integer_sub(left, right):
    if len(left) != len(right):
        raise ValueError("integer dimension mismatch")
    return tuple(a - b for a, b in zip(left, right))


def _vector_sub(left, right):
    if len(left) != len(right):
        raise ValueError("witness dimension mismatch")
    return tuple(_integer_sub(a, b) for a, b in zip(left, right))


def _integer_scale(ring, scalar, vector):
    return tuple(integer_mul(ring, scalar, entry) for entry in vector)


def _product(ring, values):
    result = (1,) + (0,) * (ring.N - 1)
    for value in values:
        result = integer_mul(ring, result, value)
    return result


def infinity_norm(vector):
    return max((abs(c) for entry in vector for c in entry), default=0)


def operator_norm(element):
    """Exact induced infinity norm of negacyclic integer multiplication."""
    return sum(abs(c) for c in element)


def _canonical_vector(ring, vector):
    if not vector:
        raise ValueError("empty witness")
    return tuple(ring.elt(_element(ring, entry)) for entry in vector)


def _lift_vector(ring, vector):
    return tuple(ring.centered(entry) for entry in vector)


def matrix_vector(ring, matrix, vector):
    """Mod-q image of a vector, also accepting integer coefficient lifts."""
    result = []
    for row in matrix:
        if len(row) != len(vector):
            raise ValueError("matrix/witness dimension mismatch")
        value = ring.elt(0)
        for coefficient, entry in zip(row, vector):
            value = ring.add(value, ring.mul(_element(ring, coefficient),
                                             _element(ring, entry)))
        result.append(value)
    return tuple(result)


@dataclass(frozen=True)
class ComparisonBounds:
    rho: int
    fresh: int
    legacy: int
    oriented: int
    short_tuple: int
    three_point: int


def comparison_bounds(k, T, G):
    """Bounds for actual integer witnesses; three_point covers both stages.

    Its short_tuple bound uses scalar-bit sources and challenge coefficient
    bound one. When G>=k and T>=1, three_point equals fresh=8*T*G.
    """
    _positive_integer(k, "arity")
    _positive_integer(T, "challenge operator bound")
    _positive_integer(G, "target bound", zero=True)
    rho = (2 * T) ** k
    fresh = 8 * T * G
    return ComparisonBounds(rho, fresh, 2 * (k + 1) * G * rho**2,
                            2 * (k + 1) * G * rho, 2 * (G + k),
                            max(fresh, 2 * (G + k)))


def _ceil_log2_fraction(value):
    # Exact rounding, including dyadic boundaries; no floating logarithms.
    n, d = value.numerator, value.denominator
    exponent = max(0, n.bit_length() - d.bit_length())
    while (d << exponent) < n:
        exponent += 1
    while exponent and (d << (exponent - 1)) >= n:
        exponent -= 1
    return exponent


def sampling_parameters(k, eta=None, *, three_point=False, legacy=False):
    """Return cap R and the proved weighted expected-cost multiplier Q.

    Preferred: R=1, no eta, Q2=1+2k or Q3=1+9k/2. Timeout is included in
    the singleton/doubleton-fiber failure mass. The superseded eta-based
    analysis requires an explicit legacy=True switch.
    """
    _positive_integer(k, "arity")
    if not legacy:
        if eta is not None:
            raise ValueError("eta belongs only to the legacy sampler analysis")
        Q = Fraction(2 + 9 * k, 2) if three_point else Fraction(1 + 2 * k)
        return 1, (Q.numerator if Q.denominator == 1 else Q)
    if not isinstance(eta, (int, Fraction)) or isinstance(eta, bool):
        raise ValueError("eta must be an exact rational")
    eta = Fraction(eta)
    if not 0 < eta < 1:
        raise ValueError("eta must lie in (0,1)")
    R = _ceil_log2_fraction(Fraction((2 if three_point else 1) * k) / eta) + 1
    Q = 1 + k * ((2 + 2 * R) if three_point else (2 + R))
    return R, Q


@dataclass(frozen=True)
class StarRecord:
    y: tuple
    y_lifts: tuple
    anchor: tuple
    anchor_lift: tuple
    old: tuple
    fresh: tuple
    slacks: tuple
    numerators: tuple
    T: int
    G: int


def make_star_record(ring, y, anchor, branches, *, T, G):
    """Extract openings, preserving signed integer challenge/numerator lifts.

    Centered challenge representatives are the designated representatives in
    this prototype. The caller validates the original target commitments and
    relation; this function checks dimensions, units and the numerical bounds.
    """
    comparison_bounds(len(y), T, G)
    if len(branches) != len(y):
        raise ValueError("incomplete star")
    y = tuple(ring.elt(_element(ring, c)) for c in y)
    y_lifts = tuple(ring.centered(c) for c in y)
    if any(operator_norm(c) > T for c in y_lifts):
        raise ValueError("challenge exceeds T")
    anchor = _canonical_vector(ring, anchor)
    anchor_lift = _lift_vector(ring, anchor)
    if infinity_norm(anchor_lift) > G:
        raise ValueError("target exceeds G")
    fresh, slacks, numerators = [], [], []
    for j, (challenge, opening) in enumerate(branches):
        challenge = ring.elt(_element(ring, challenge))
        challenge_lift = ring.centered(challenge)
        if operator_norm(challenge_lift) > T:
            raise ValueError("challenge exceeds T")
        opening = _canonical_vector(ring, opening)
        opening_lift = _lift_vector(ring, opening)
        if len(opening) != len(anchor):
            raise ValueError("witness dimension mismatch")
        if infinity_norm(opening_lift) > G:
            raise ValueError("target exceeds G")
        slack = _integer_sub(y_lifts[j], challenge_lift)
        inverse = ring.inv(ring.elt(slack))
        numerator = _vector_sub(anchor_lift, opening_lift)
        fresh.append(ring.scale(inverse, numerator))
        slacks.append(slack)
        numerators.append(numerator)
    old = anchor
    for challenge, opening in zip(y, fresh):
        old = ring.vsub(old, ring.scale(challenge, opening))
    return StarRecord(y, y_lifts, anchor, anchor_lift, old, tuple(fresh),
                      tuple(slacks), tuple(numerators), T, G)


@dataclass(frozen=True)
class KernelCertificate:
    branch: str
    coordinate: object
    vector: tuple
    bound: int
    norm: int


def _certificate(ring, matrix, projection, vector, bound, branch, coordinate):
    norm = infinity_norm(vector)
    if norm > bound:
        raise ArithmeticError("integer kernel vector exceeds proved bound")
    if not any(c % ring.q for entry in vector for c in entry):
        raise ValueError("kernel vector is zero modulo q")
    if any(any(entry) for entry in matrix_vector(ring, matrix, vector)):
        raise ValueError("not a kernel vector for the supplied matrix")
    if any(any(entry) for entry in matrix_vector(ring, projection, vector)):
        raise ValueError("projection commitments do not match")
    return KernelCertificate(branch, coordinate, vector, bound, norm)


def _same_commitment(ring, matrix, projection, left, right):
    return (matrix_vector(ring, matrix, left) == matrix_vector(ring, matrix, right)
            and matrix_vector(ring, projection, left) ==
            matrix_vector(ring, projection, right))


def compare_stars(ring, matrix, left, right, *, projection=()):
    """Fresh collision first; otherwise use the integer oriented old bridge.

    Returns None only when the complete extracted tuples coincide. The matrix
    and optional projection are checked on all input openings before comparing.
    """
    if (len(left.y), left.T, left.G) != (len(right.y), right.T, right.G):
        raise ValueError("incompatible star parameters")
    if len(left.anchor) != len(right.anchor):
        raise ValueError("witness dimension mismatch")
    for a, b in zip((left.old,) + left.fresh, (right.old,) + right.fresh):
        if not _same_commitment(ring, matrix, projection, a, b):
            raise ValueError("stars do not open the same input commitments")
    bounds = comparison_bounds(len(left.y), left.T, left.G)
    for j, (a, b) in enumerate(zip(left.fresh, right.fresh)):
        if a != b:
            z = _vector_sub(_integer_scale(ring, right.slacks[j], left.numerators[j]),
                            _integer_scale(ring, left.slacks[j], right.numerators[j]))
            return _certificate(ring, matrix, projection, z, bounds.fresh, "fresh", j)
    if left.old == right.old:
        return None
    common = _product(ring, left.slacks)
    z = _integer_scale(ring, common, _vector_sub(left.anchor_lift, right.anchor_lift))
    for j, numerator in enumerate(left.numerators):
        # Exact product of the other slacks: not integer or modular division.
        others = _product(ring, left.slacks[:j] + left.slacks[j + 1:])
        delta_y = _integer_sub(left.y_lifts[j], right.y_lifts[j])
        z = _vector_sub(z, _integer_scale(ring, integer_mul(ring, delta_y, others),
                                         numerator))
    return _certificate(ring, matrix, projection, z, bounds.oriented,
                        "old_oriented", None)


def validate_strong_challenges(ring, challenges):
    """Exhaustive toy-set validation, including fork-to-fork unit differences."""
    values = tuple(ring.elt(_element(ring, c)) for c in challenges)
    if len(values) < 3 or len(set(values)) != len(values):
        raise ValueError("need at least three distinct ring challenges")
    for j, c in enumerate(values):
        for previous in values[:j]:
            try:
                ring.inv(ring.sub(c, previous))
            except ValueError as exc:
                raise ValueError("challenge difference is not a unit") from exc
    return values


@dataclass(frozen=True)
class ThreePointSample:
    y: tuple
    center: object
    branches: tuple


@dataclass(frozen=True)
class SamplingStats:
    oracle_calls: int
    fork_trials: int
    initial_draws: int


def sample_three_point_star(ring, challenges, k, oracle, rng, R=1):
    """Return (complete sample, stats), (kernel, stats), or (None, stats).

    R=1 is the preferred cap=M algorithm; a larger R is retained only for
    the archived eta-based analysis. The caller
    must actually reset the oracle to the same frozen snapshot and random-tape
    entry on every call; this Python callback wrapper cannot enforce replay.
    The oracle returns an already checked target reply, a KernelCertificate,
    or None. A kernel at the center or either fork is absorbing: return it
    immediately. The caller is responsible for validating its actual same-A
    kernel and radius; this wrapper recognizes the type, not its validity.
    Stats
    count skipped/repeated-challenge trials separately from oracle invocations.
    Exhaustive validation of the explicit challenge set is additional toy cost.
    """
    _positive_integer(k, "arity")
    _positive_integer(R, "cap multiplier")
    challenges = validate_strong_challenges(ring, challenges)
    y = tuple(rng.choice(challenges) for _ in range(k))
    center = oracle(y)
    calls, trials = 1, 0
    if isinstance(center, KernelCertificate):
        return center, SamplingStats(calls, trials, k)
    if center is None:
        return None, SamplingStats(calls, trials, k)
    branches = []
    for j in range(k):
        selected = []
        excluded = {y[j]}
        for _ in range(2):
            for _ in range(len(challenges) * R):
                trials += 1
                candidate = rng.choice(challenges)
                if candidate in excluded:
                    continue
                other = list(y)
                other[j] = candidate
                reply = oracle(tuple(other))
                calls += 1
                if isinstance(reply, KernelCertificate):
                    return reply, SamplingStats(calls, trials, k)
                if reply is not None:
                    selected.append((candidate, reply))
                    excluded.add(candidate)
                    break
            else:
                return None, SamplingStats(calls, trials, k)
        branches.append(tuple(selected))
    return ThreePointSample(y, center, tuple(branches)), SamplingStats(calls, trials, k)


def _error_from_slots(ring, constant, linear, mixed, y):
    k = len(y)
    if len(linear) != k or len(mixed) != k * (k - 1) // 2:
        raise ValueError("incorrect frozen error coefficient slots")
    result = ring.elt(_element(ring, constant))
    for coefficient, challenge in zip(linear, y):
        result = ring.add(result, ring.mul(coefficient, challenge))
    index = 0
    for i in range(k):
        for j in range(i + 1, k):
            result = ring.add(result, ring.mul(mixed[index], ring.mul(y[i], y[j])))
            index += 1
    return result


@dataclass(frozen=True)
class ThreePointAnalysis:
    first_star: StarRecord
    collision: object
    square_coefficients: tuple


def analyze_three_point_star(ring, matrix, sample, phi, constant, linear, mixed,
                             *, T, G, projection=()):
    """Check actual targets, line consistency and fresh square coefficients.

    Original C_old and C_j are not supplied here: the caller must already
    check each target opening against those actual frozen commitments. The
    matrix checks here only compare the supplied extracted openings.
    phi must be the supplied homogeneous quadratic compressed relation. Its
    degree is an external construction fact; finite tests cannot certify an
    arbitrary callable's polynomial degree. Error slots are restricted here to
    the protocol's constant, linear and distinct-coordinate mixed terms.
    """
    k = len(sample.y)
    if len(sample.branches) != k or any(len(pair) != 2 for pair in sample.branches):
        raise ValueError("incomplete three-point star")
    first = make_star_record(ring, sample.y, sample.center,
                             tuple(pair[0] for pair in sample.branches), T=T, G=G)
    second = make_star_record(ring, sample.y, sample.center,
                              tuple(pair[1] for pair in sample.branches), T=T, G=G)
    error = lambda y: _error_from_slots(ring, constant, linear, mixed, y)
    if ring.elt(phi(first.anchor)) != error(first.y):
        raise ValueError("center fails the target relation")
    squares = []
    for j, pair in enumerate(sample.branches):
        validate_strong_challenges(ring, (first.y[j], pair[0][0], pair[1][0]))
        for challenge, witness in pair:
            y_other = list(first.y)
            y_other[j] = ring.elt(challenge)
            if ring.elt(phi(_canonical_vector(ring, witness))) != error(tuple(y_other)):
                raise ValueError("fork fails the target relation")
        a, b = first.fresh[j], second.fresh[j]
        if not _same_commitment(ring, matrix, projection, a, b):
            raise ValueError("forks do not open the same source commitment")
        if a != b:
            z = _vector_sub(_integer_scale(ring, second.slacks[j], first.numerators[j]),
                            _integer_scale(ring, first.slacks[j], second.numerators[j]))
            certificate = _certificate(ring, matrix, projection, z, 8 * T * G,
                                       "three_point_line", j)
            return ThreePointAnalysis(first, certificate, ())
        # Polynomial at c: phi(base+c*a)-error(y_-j,c). Check its actual
        # constant, linear and square coefficients, not just a boolean flag.
        base = ring.vsub(first.anchor, ring.scale(first.y[j], a))
        g_base, g_a = ring.elt(phi(base)), ring.elt(phi(a))
        cross = ring.sub(ring.sub(ring.elt(phi(ring.vadd(base, a))), g_base), g_a)
        y_zero, y_one = list(first.y), list(first.y)
        y_zero[j], y_one[j] = ring.elt(0), ring.elt(1)
        e_zero = error(tuple(y_zero))
        coefficients = (ring.sub(g_base, e_zero),
                        ring.sub(cross, ring.sub(error(tuple(y_one)), e_zero)), g_a)
        if any(any(coefficient) for coefficient in coefficients):
            raise ValueError("three-point quadratic coefficient identity failed")
        squares.append(g_a)
    return ThreePointAnalysis(first, None, tuple(squares))
