"""Local weak-anchor and rank-star components, not an end-to-end extractor.

Callers check each target reply against the ACTUAL frozen input commitments,
error slots, relation, radius and checkpoint. They restore the same adversary
snapshot and suffix tape for every y-query in one raw trial. Independent raw
strong/weak trials restore that checkpoint with fresh independent continuation
coins. This module cannot enforce callback replay or certify polynomial degree.

KernelCertificate callbacks must already validate the same A, integer vector,
nonzero residue and permitted radius. A dataclass/type check is not validation.
"""
from dataclasses import dataclass
from .comparison_bridges import (
    KernelCertificate, StarRecord, ThreePointSample, _certificate,
    _integer_scale, _vector_sub, infinity_norm,
)
from .comparison_filters import compare_fresh


@dataclass(frozen=True)
class AnchorStats:
    strong_calls: int
    weak_calls: int
    weak_loops: int
    branch: str


def extract_with_weak_anchor(strong_trial, weak_trial, *, fresh_valid,
                             tighten, old_valid, compare_fresh_only,
                             compare_full):
    """Return (first strong record / checked kernel / None, AnchorStats).

    `tighten(first)` verifies deterministic bit tightening and short-old
    reconstruction after full-f validation; it returns None, never a substitute
    record. Both comparison callbacks return only a kernel or None. They compare
    the same frozen source/old commitments; weak has no semantic-validity promise.

    There is at most ONE unbounded weak retry loop per invocation. Its two entry
    branches are mutually exclusive and use the identical weak_trial distribution.
    The raw-work bound mu_S+mu_W additionally needs a_S <= s_W and independent
    raw trials. These are proof/caller contracts, not inferable from callbacks.
    The full-f/old predicates must be actual checks, not verifier acceptance bits.
    """
    first = strong_trial()
    if first is None or isinstance(first, KernelCertificate):
        return first, AnchorStats(1, 0, 0, 'strong_terminal')
    if not fresh_valid(first):
        comparison, branch = compare_fresh_only, 'fresh_bad'
    else:
        if tighten(first) is not None:
            raise ValueError('tighten must retain the first record and return None')
        if old_valid(first):
            return first, AnchorStats(1, 0, 0, 'valid_first')
        comparison, branch = compare_full, 'old_bad'
    calls = 0
    while True:
        calls += 1
        anchor = weak_trial()
        if anchor is not None:
            break
    if isinstance(anchor, KernelCertificate):
        return anchor, AnchorStats(1, calls, 1, branch)
    result = comparison(first, anchor)
    if result is not None and not isinstance(result, KernelCertificate):
        raise ValueError('comparison may return only failure or a checked kernel')
    return result, AnchorStats(1, calls, 1, branch)


def _shape(record):
    if not isinstance(record, StarRecord):
        raise ValueError('a checked StarRecord is required')
    k, m = len(record.y), len(record.anchor)
    if not k or not m or any(len(v) != k for v in
                            (record.y_lifts, record.fresh, record.slacks,
                             record.numerators)):
        raise ValueError('incomplete star record')
    if len(record.old) != m or len(record.anchor_lift) != m:
        raise ValueError('witness dimension mismatch')
    if any(len(v) != m for v in record.fresh + record.numerators):
        raise ValueError('witness dimension mismatch')


def short_old_lift(ring, record):
    """Construct the TRUE integer old opening after scalar-bit tightening.

    The actual fresh validity proof and input commitments are caller obligations.
    This checks the local bit, lift, residue and shortness invariants explicitly.
    It does not replace the weak numerators by modular/centered differences.
    """
    _shape(record)
    bits = (ring.elt(0), ring.elt(1))
    if any(w not in bits for source in record.fresh for w in source):
        raise ValueError('short old requires scalar-bit fresh openings')
    if any(abs(c) > 1 for y in record.y_lifts for c in y):
        raise ValueError('short old requires challenge coefficient bound one')
    if any(ring.elt(y) != residue for y, residue in
           zip(record.y_lifts, record.y)):
        raise ValueError('challenge lift does not match residue')
    if any(ring.elt(v) != residue for v, residue in
           zip(record.anchor_lift, record.anchor)):
        raise ValueError('anchor lift does not match residue')
    if infinity_norm(record.anchor_lift) > record.G:
        raise ValueError('anchor exceeds target bound')
    old = record.anchor_lift
    for y, source in zip(record.y_lifts, record.fresh):
        integer_bits = tuple((int(w == bits[1]),) + (0,) * (ring.N - 1)
                             for w in source)
        old = _vector_sub(old, _integer_scale(ring, y, integer_bits))
    if tuple(ring.elt(v) for v in old) != record.old:
        raise ValueError('reconstructed old does not match residue')
    if infinity_norm(old) > record.G + len(record.y):
        raise ValueError('reconstructed old exceeds short bound')
    return old


def compare_full_with_weak(ring, matrix, strong, weak, *, projection=()):
    """FULL-tuple comparison with a two-point, possibly nonbit weak anchor.

    Strong fresh validity/tightening must already hold. First compare fresh
    residues using the 8TG numerator bridge. Only equality transfers bitness to
    weak; then construct both integer old openings and use their short difference.
    Never send a nonbit weak record directly to the old short-tuple comparator.
    """
    _shape(strong)
    _shape(weak)
    strong_old = short_old_lift(ring, strong)
    collision = compare_fresh(ring, matrix, strong, weak, projection=projection)
    if collision is not None:
        return collision
    weak_old = short_old_lift(ring, weak)
    if strong.old == weak.old:
        return None
    z = _vector_sub(strong_old, weak_old)
    return _certificate(ring, matrix, projection, z,
                        2 * (strong.G + len(strong.y)),
                        'weak_anchor_short_old', 0)


def _size(domain):
    size = domain.size
    if type(size) is not int or size < 1:
        raise ValueError('domain.size must be a positive integer')
    return size


def _draw(draw_below, bound):
    rank = draw_below(bound)
    if type(rank) is not int or not 0 <= rank < bound:
        raise ValueError('draw_below returned an invalid rank')
    return rank


def sample_excluding(domain, excluded_ranks, draw_below):
    """Uniformly draw (rank, unrank(rank)) outside a small rank exclusion set.

    Requires a bijective domain.unrank and a uniform draw_below. Never enumerate
    the M-element domain and never reject repeatedly to avoid excluded points.
    Internal bit-rejection proposals inside draw_below are additional caller cost.
    """
    size = _size(domain)
    excluded = set(excluded_ranks)
    if any(type(v) is not int or not 0 <= v < size for v in excluded):
        raise ValueError('invalid excluded rank')
    if len(excluded) == size:
        raise ValueError('no unexcluded challenge')
    rank = _draw(draw_below, size - len(excluded))
    for skipped in sorted(excluded):
        if rank >= skipped:
            rank += 1
    return rank, domain.unrank(rank)


@dataclass(frozen=True)
class RankStarSample:
    y: tuple
    center: object
    branches: tuple
    center_ranks: tuple
    branch_ranks: tuple

    def as_three_point(self):
        if any(len(pair) != 2 for pair in self.branches):
            raise ValueError('not a three-point sample')
        return ThreePointSample(self.y, self.center, self.branches)


@dataclass(frozen=True)
class RankSamplingStats:
    oracle_calls: int
    fork_trials: int
    rank_draws: int
    excluded_draws: int
    stop_coin_draws: int
    initial_draws: int
    mode: str
    points: int


def sample_rank_star(domain, k, oracle, streams, *, points=3, mode='cap_m'):
    """Two/three-point rank-domain sampler with absorbing checked kernels.

    domain exposes size and bijective unrank; e.g. FixedWeightChallenges. Its
    pairwise unit-difference property and coefficient/operator bounds must have
    been established externally. No exponentially large domain is enumerated.

    streams((j, stage, channel)) returns a persistent uniform draw_below callable;
    stage=0 is the center, then 1/2 are first/second forks. channel is 'rank' or
    'stop'. Streams at different addresses are independent. All first forks are
    completed before any second fork, so the coupled two-point sampler is a
    literal first-phase prefix of a successful three-point sampler. Actual raw
    S/W trials MUST use independent stream families; this coupling is analytical.

    cap_m: each stage has M draws from the FULL domain; excluded ranks count as
    trials but skip the oracle, exactly the old cap=M semantics.
    random_stop: query uniformly outside r existing successful points; after an
    oracle FAILURE only, stop independently with probability r/M. Failed queries
    are not excluded. There is no hidden retry cap. Kernel/record returns precede
    the stop coin. This is a separate optional algorithm, not cap=M relabelled.

    The caller validates replies and resets the same snapshot/suffix tape at each
    oracle call. Stats count rank-interface calls, not the bit-level rejection
    proposals inside a uniform integer sampler; charge those separately.
    """
    size = _size(domain)
    if type(k) is not int or k < 1 or type(points) is not int or points not in (2, 3):
        raise ValueError('positive arity and two or three points required')
    if size < points:
        raise ValueError('domain too small for distinct points')
    if mode not in ('cap_m', 'random_stop'):
        raise ValueError('unknown sampling mode')
    ranks, values = [], []
    for j in range(k):
        rank = _draw(streams((j, 0, 'rank')), size)
        ranks.append(rank)
        values.append(domain.unrank(rank))
    calls, trials, draws, skipped, stops = 1, 0, k, 0, 0
    center = oracle(tuple(values))

    def finish(result):
        return result, RankSamplingStats(calls, trials, draws, skipped, stops,
                                        k, mode, points)

    if center is None or isinstance(center, KernelCertificate):
        return finish(center)
    branches, fork_ranks = [[] for _ in range(k)], [[] for _ in range(k)]
    for stage in range(1, points):
        for j in range(k):
            excluded = {ranks[j], *fork_ranks[j]}
            chooser = streams((j, stage, 'rank'))
            stopper = streams((j, stage, 'stop')) if mode == 'random_stop' else None
            used = 0
            while mode == 'random_stop' or used < size:
                used += 1
                trials += 1
                draws += 1
                if mode == 'cap_m':
                    rank = _draw(chooser, size)
                    if rank in excluded:
                        skipped += 1
                        continue
                    value = domain.unrank(rank)
                else:
                    rank, value = sample_excluding(domain, excluded, chooser)
                other = list(values)
                other[j] = value
                reply = oracle(tuple(other))
                calls += 1
                if isinstance(reply, KernelCertificate):
                    return finish(reply)
                if reply is not None:
                    branches[j].append((value, reply))
                    fork_ranks[j].append(rank)
                    break
                if mode == 'random_stop':
                    stops += 1
                    if _draw(stopper, size) < len(excluded):
                        return finish(None)
            else:
                return finish(None)
    sample = RankStarSample(tuple(values), center,
                            tuple(tuple(v) for v in branches), tuple(ranks),
                            tuple(tuple(v) for v in fork_ranks))
    return finish(sample)
