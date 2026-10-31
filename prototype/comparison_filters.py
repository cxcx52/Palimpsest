"""Independent-trial comparison with concrete Palimpsest kernel bridges.

The retry rule is the author's CauchyFold independent-trial comparison lemma.
This module implements a local extractor component, not an end-to-end prover.
Each raw trial must reset the SAME frozen adversary prefix and use independent
extractor coins. It returns None, a validated KernelCertificate, or a checked
record. Validation of the actual source/target relation belongs to the caller.
The retry loop is deliberately EPT, with no undocumented finite retry limit.
"""

from .comparison_bridges import (
    KernelCertificate, _certificate, _integer_scale, _lift_vector,
    _same_commitment, _vector_sub, comparison_bounds, infinity_norm,
)


def compare_on_failure(raw_trial, valid, compare):
    """Return a valid FIRST record, a kernel, or failure.

    `compare(a,b)` must return a checked kernel when compatibility keys differ,
    and None when they agree. For a bad first key v with raw mass p_v <= theta,
    total good-or-kernel mass is at least s-theta. Expected raw work is at most
    twice its unconditional mean, even if a trial's output and cost correlate.
    This does NOT return a valid second record: doing so would destroy the
    first-record domination used by the next comparison gate's root bound.
    """
    first = raw_trial()
    if first is None or isinstance(first, KernelCertificate):
        return first
    if valid(first):
        return first
    while True:
        second = raw_trial()
        if second is not None:
            break
    if isinstance(second, KernelCertificate):
        return second
    return compare(first, second)


def _check_pair(ring, matrix, projection, left, right):
    if (len(left.y), left.T, left.G) != (len(right.y), right.T, right.G):
        raise ValueError("incompatible star parameters")
    if len(left.anchor) != len(right.anchor):
        raise ValueError("witness dimension mismatch")
    for a, b in zip((left.old,) + left.fresh, (right.old,) + right.fresh):
        if not _same_commitment(ring, matrix, projection, a, b):
            raise ValueError("records do not open the same frozen commitments")


def compare_fresh(ring, matrix, left, right, *, projection=()):
    """Compatibility is the fresh tuple ONLY; old openings may be wide."""
    _check_pair(ring, matrix, projection, left, right)
    for j, (a, b) in enumerate(zip(left.fresh, right.fresh)):
        if a != b:
            z = _vector_sub(
                _integer_scale(ring, right.slacks[j], left.numerators[j]),
                _integer_scale(ring, left.slacks[j], right.numerators[j]))
            return _certificate(ring, matrix, projection, z, 8 * left.T * left.G,
                                "independent_fresh", j)
    return None


def compare_short_tuples(ring, matrix, left, right, *, projection=()):
    """After fresh bit tightening, compare FULL tuples by short differences.

    Same-old/different-fresh records are incompatible. Omitting this case is
    invalid for the fixed-full-tuple root bound used by the old-relation gate.
    """
    _check_pair(ring, matrix, projection, left, right)
    bits = (ring.elt(0), ring.elt(1))
    for record in (left, right):
        if any(entry not in bits for source in record.fresh for entry in source):
            raise ValueError("short comparison requires scalar-bit fresh openings")
        if any(abs(c) > 1 for y in record.y_lifts for c in y):
            raise ValueError("short comparison requires coefficient bound one")
        if infinity_norm(_lift_vector(ring, record.old)) > record.G + len(record.y):
            raise ValueError("old opening exceeds the short bound")
    bound = comparison_bounds(len(left.y), left.T, left.G).short_tuple
    for j, (a, b) in enumerate(zip((left.old,) + left.fresh,
                                   (right.old,) + right.fresh)):
        if a != b:
            z = _vector_sub(_lift_vector(ring, a), _lift_vector(ring, b))
            return _certificate(ring, matrix, projection, z, bound,
                                "independent_short_tuple", j)
    return None
