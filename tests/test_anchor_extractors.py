"""Exact local contracts and finite laws, not end-to-end security tests."""
from dataclasses import replace
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path
import unittest

from prototype.anchor_extractors import (
    KernelCertificate, compare_full_with_weak, extract_with_weak_anchor,
    sample_excluding, sample_rank_star, short_old_lift,
)
from prototype.comparison_bridges import Ring, make_star_record
from prototype.comparison_filters import compare_fresh
from prototype.challenge_sampler import FixedWeightChallenges


class TinyDomain:
    def __init__(self, size):
        self.size = size
        self.unrank_calls = 0

    def unrank(self, rank):
        assert 0 <= rank < self.size
        self.unrank_calls += 1
        return rank


class Streams:
    def __init__(self, tapes):
        self.tapes = {key: iter(values) for key, values in tapes.items()}
        self.bounds = []

    def __call__(self, key):
        def draw(bound):
            self.bounds.append((key, bound))
            value = next(self.tapes[key])
            assert 0 <= value < bound
            return value
        return draw


class TestWeakAnchorGate(unittest.TestCase):
    def setUp(self):
        self.r = Ring(4, 7)
        r = self.r
        self.z, self.o = r.elt(0), r.elt(1)
        self.A = ((r.elt(2), self.o, self.o),)
        self.P = ((self.o, self.z, self.z),)
        self.a = (self.o, self.o, self.z)
        self.b = (self.o, self.z, self.o)
        self.old = (self.z,) * 3

    def record(self, old, fresh, challenge=1, alternative=-1):
        r = self.r
        y, alt = r.elt(challenge), r.elt(alternative)
        center = r.vadd(old, r.scale(y, fresh))
        branch = r.vadd(old, r.scale(alt, fresh))
        return make_star_record(r, (y,), center, ((alt, branch),), T=1, G=3)

    def kernel(self):
        return compare_fresh(self.r, self.A, self.record(self.old, self.a),
                             self.record(self.old, self.b), projection=self.P)

    def run_gate(self, first, weak, fresh=True, old=True, **overrides):
        options = dict(fresh_valid=lambda _: fresh, tighten=lambda _: None,
                       old_valid=lambda _: old,
                       compare_fresh_only=lambda _a, _b: None,
                       compare_full=lambda _a, _b: None)
        options.update(overrides)
        return extract_with_weak_anchor(lambda: first, weak, **options)

    def test_strong_failure_kernel_and_good_do_not_retry(self):
        first_record = object()
        for first in (None, self.kernel(), first_record):
            result, stats = self.run_gate(first, lambda: self.fail('weak called'))
            self.assertIs(result, first)
            self.assertEqual((stats.strong_calls, stats.weak_calls, stats.weak_loops),
                             (1, 0, 0))

    def test_fresh_bad_is_terminal_and_keeps_first_sidecar(self):
        first, second = object(), object()
        seen = []
        tape = iter((None, None, second))
        result, stats = self.run_gate(
            first, lambda: next(tape), fresh=False,
            tighten=lambda _: self.fail('fresh failure reached tightening'),
            old_valid=lambda _: self.fail('fresh failure reached old gate'),
            compare_fresh_only=lambda a, b: seen.append((a, b)),
            compare_full=lambda _a, _b: self.fail('old compare called'))
        self.assertIsNone(result)
        self.assertEqual(seen, [(first, second)])
        self.assertEqual((stats.weak_calls, stats.weak_loops, stats.branch),
                         (3, 1, 'fresh_bad'))

    def test_old_bad_has_only_one_weak_loop(self):
        first, second, seen = object(), object(), []
        tape = iter((None, second))
        result, stats = self.run_gate(
            first, lambda: next(tape), old=False,
            tighten=lambda a: seen.append(('tight', a)),
            compare_full=lambda a, b: seen.append(('compare', a, b)),
            compare_fresh_only=lambda _a, _b: self.fail('wrong branch'))
        self.assertIsNone(result)
        self.assertEqual(seen, [('tight', first), ('compare', first, second)])
        self.assertEqual((stats.weak_calls, stats.weak_loops, stats.branch),
                         (2, 1, 'old_bad'))

    def test_weak_kernel_is_absorbing_on_both_branches(self):
        kernel = self.kernel()
        for fresh in (False, True):
            tape = iter((None, kernel))
            result, stats = self.run_gate(
                object(), lambda: next(tape), fresh=fresh, old=False,
                compare_fresh_only=lambda _a, _b: self.fail('compared kernel'),
                compare_full=lambda _a, _b: self.fail('compared kernel'))
            self.assertIs(result, kernel)
            self.assertEqual(stats.weak_calls, 2)

    def test_callbacks_cannot_replace_the_first_record(self):
        with self.assertRaisesRegex(ValueError, 'retain the first'):
            self.run_gate(object(), lambda: object(), tighten=lambda _: object())
        with self.assertRaisesRegex(ValueError, 'only failure'):
            self.run_gate(object(), lambda: object(), fresh=False,
                          compare_fresh_only=lambda _a, b: b)

    def test_nonbit_weak_different_fresh_gives_real_kernel(self):
        strong = self.record(self.old, self.a)
        weak = self.record(self.old, (self.o, self.r.elt(2), self.r.elt(6)))
        cert = compare_full_with_weak(self.r, self.A, strong, weak, projection=self.P)
        self.assertIsInstance(cert, KernelCertificate)
        self.assertEqual((cert.branch, cert.bound), ('independent_fresh', 24))
        self.assertEqual(cert.norm, 4)

    def test_equal_fresh_transfers_bits_then_compares_old(self):
        strong = self.record((self.z, self.o, self.z), self.a)
        weak = self.record((self.z, self.z, self.o), self.a)
        cert = compare_full_with_weak(self.r, self.A, strong, weak, projection=self.P)
        self.assertEqual((cert.branch, cert.norm, cert.bound),
                         ('weak_anchor_short_old', 1, 8))
        same = self.record((self.z, self.o, self.z), self.a, challenge=0)
        self.assertIsNone(compare_full_with_weak(self.r, self.A, strong, same,
                                               projection=self.P))

    def test_short_old_uses_unreduced_integer_lift(self):
        fresh = (self.o, self.o)
        strong = self.record((self.z, self.r.elt(4)), fresh,
                             challenge=-1, alternative=0)
        weak = self.record((self.z, self.z), fresh)
        A = ((self.z, self.z),)
        P = ((self.o, self.z),)
        self.assertEqual(short_old_lift(self.r, strong)[1][0], 4)
        self.assertEqual(self.r.centered(strong.old[1])[0], -3)
        cert = compare_full_with_weak(self.r, A, strong, weak, projection=P)
        self.assertEqual(cert.vector[1][0], 4)

    def test_changed_commitment_and_truncated_record_rejected(self):
        strong = self.record(self.old, self.a)
        wrong = self.record(self.old, (self.o, self.z, self.z))
        with self.assertRaisesRegex(ValueError, 'same frozen'):
            compare_full_with_weak(self.r, self.A, strong, wrong, projection=self.P)
        with self.assertRaisesRegex(ValueError, 'incomplete'):
            compare_full_with_weak(self.r, self.A, strong,
                                   replace(strong, numerators=()), projection=self.P)

    def test_asymmetric_exact_distributions_and_correlated_cost(self):
        # failure, kernel, good, bad-fresh class, good-fresh/bad-old class.
        # Weak can have arbitrary class masses; only strong class masses have
        # root bounds. Cost basis vectors include expensive failed weak trials.
        laws = [tuple(Fraction(x, sum(w)) for x in w)
                for w in product(range(2), repeat=5) if sum(w)]
        checked = 0
        for sigma in laws:
            a_s = sum(sigma[2:])
            for omega in laws:
                s_w = 1 - omega[0]
                if not s_w or a_s > s_w:
                    continue
                b_f, b_o = sigma[3:]
                loss = (b_f * omega[3] + b_o * omega[4]) / s_w
                self.assertLessEqual(loss, b_f + b_o)
                good = sigma[2]  # No second record can be returned.
                kernels = sigma[1] + b_f + b_o - loss
                self.assertEqual(good + kernels, 1 - sigma[0] - loss)
                mu_s = sum(p * c for p, c in zip(sigma, (1, 7, 2, 19, 100)))
                for expensive in range(5):
                    mu_w = omega[expensive]
                    total = mu_s + (b_f + b_o) * mu_w / s_w
                    self.assertLessEqual(total, mu_s + mu_w)
                checked += 1
        self.assertGreater(checked, 300)


class TestRankSamplers(unittest.TestCase):
    def test_sample_excluding_is_exact_bijection_for_every_small_exclusion(self):
        domain = TinyDomain(7)
        for count in range(4):
            for excluded in combinations(range(7), count):
                out = [sample_excluding(domain, excluded, lambda n, r=r: r)[0]
                       for r in range(7 - count)]
                self.assertEqual(out, [r for r in range(7) if r not in excluded])

    def test_exclusion_validation(self):
        domain = TinyDomain(3)
        for excluded in ((-1,), (3,), (True,), (0, 1, 2)):
            with self.assertRaises(ValueError):
                sample_excluding(domain, excluded, lambda _: 0)
        with self.assertRaises(ValueError):
            sample_excluding(domain, (), lambda n: n)

    def test_actual_large_fixed_weight_domain_without_enumeration(self):
        base = Path(__file__).resolve().parents[1] / 'prototype'
        cert = json.loads((base / 'data' / 'commitment_prime_certificate.json')
                          .read_text(encoding='utf-8'))
        domain = FixedWeightChallenges(cert, N=512, support=128, weight=64)
        rank, value = sample_excluding(domain, (0, 1, domain.size - 1),
                                       lambda bound: bound - 1)
        self.assertEqual(rank, domain.size - 2)
        self.assertEqual(domain.decode(domain.encode(value)), value)
        self.assertGreater(domain.size, 2**188)

    def test_cap_counts_excluded_draws_and_distinct_forks(self):
        streams = Streams({(0, 0, 'rank'): [0],
                           (0, 1, 'rank'): [0, 0, 1],
                           (0, 2, 'rank'): [1, 0, 2]})
        sample, stats = sample_rank_star(TinyDomain(3), 1, lambda y: ('reply', y),
                                         streams, points=3)
        self.assertEqual(sample.branch_ranks, ((1, 2),))
        self.assertEqual((stats.oracle_calls, stats.fork_trials, stats.rank_draws,
                          stats.excluded_draws, stats.stop_coin_draws), (3, 6, 7, 4, 0))
        self.assertEqual(sample.as_three_point().y, sample.y)

    def test_cap_m_timeout_has_no_unadvertised_retry(self):
        streams = Streams({(0, 0, 'rank'): [0], (0, 1, 'rank'): [0, 0, 0]})
        result, stats = sample_rank_star(TinyDomain(3), 1, lambda _: 'accepted',
                                         streams, points=2)
        self.assertIsNone(result)
        self.assertEqual((stats.oracle_calls, stats.fork_trials), (1, 3))

    def test_strong_first_phase_is_weak_prefix_in_both_modes(self):
        for mode in ('cap_m', 'random_stop'):
            tapes = {(j, 0, 'rank'): [0] for j in range(2)}
            for j in range(2):
                tapes[j, 1, 'rank'] = [1 if mode == 'cap_m' else 0]
                tapes[j, 2, 'rank'] = [2 if mode == 'cap_m' else 0]
            histories = []
            for points in (2, 3):
                history = []
                def oracle(y):
                    history.append(y)
                    return ('reply', y)
                sample, _ = sample_rank_star(TinyDomain(4), 2, oracle,
                                             Streams(tapes), points=points, mode=mode)
                self.assertIsNotNone(sample)
                histories.append(history)
            self.assertEqual(histories[0], histories[1][:3])

    def test_random_stop_failed_points_are_not_excluded_and_no_cap(self):
        streams = Streams({(0, 0, 'rank'): [0],
                           (0, 1, 'rank'): [0] * 6,
                           (0, 1, 'stop'): [2] * 5,
                           (0, 2, 'rank'): [0]})
        seen, failures = [], 0
        def oracle(y):
            nonlocal failures
            seen.append(y)
            if y == (1,) and failures < 5:
                failures += 1
                return None
            return ('accepted', y)
        sample, stats = sample_rank_star(TinyDomain(3), 1, oracle, streams,
                                         points=3, mode='random_stop')
        self.assertEqual(sample.branch_ranks, ((1, 2),))
        self.assertEqual(seen.count((1,)), 6)
        self.assertEqual((stats.oracle_calls, stats.fork_trials, stats.stop_coin_draws),
                         (8, 7, 5))
        self.assertEqual([n for key, n in streams.bounds if key == (0, 1, 'rank')],
                         [2] * 6)

    def test_random_stop_uses_r_over_m_after_failure_only(self):
        streams = Streams({(0, 0, 'rank'): [0], (0, 1, 'rank'): [0],
                           (0, 2, 'rank'): [0], (0, 2, 'stop'): [1]})
        result, stats = sample_rank_star(
            TinyDomain(5), 1, lambda y: None if y == (2,) else 'accepted',
            streams, mode='random_stop')
        self.assertIsNone(result)
        self.assertEqual(stats.stop_coin_draws, 1)  # 1 < r=2, although not < 1.

    def test_kernel_at_center_or_either_fork_is_absorbing(self):
        # Deliberately typed sentinel: sampler contract requires caller to check
        # a real certificate; the gate/bridge tests above construct actual kernels.
        kernel = KernelCertificate('caller_validated', None, (), 1, 1)
        for mode, where in product(('cap_m', 'random_stop'), range(3)):
            tapes = {(0, 0, 'rank'): [0],
                     (0, 1, 'rank'): [1 if mode == 'cap_m' else 0],
                     (0, 2, 'rank'): [2 if mode == 'cap_m' else 0]}
            calls = []
            def oracle(y):
                calls.append(y)
                return kernel if len(calls) - 1 == where else 'accepted'
            result, stats = sample_rank_star(TinyDomain(3), 1, oracle, Streams(tapes),
                                             mode=mode)
            self.assertIs(result, kernel)
            self.assertEqual(stats.oracle_calls, where + 1)
            self.assertEqual(stats.stop_coin_draws, 0)

    def test_random_stop_finite_law_exact_cost_and_success(self):
        # Each stage excludes r SUCCESSFUL points. For a fiber with a additional
        # accepting points, per attempt p=a/(M-r), after failure stop with r/M.
        for M in range(3, 12):
            for r in (1, 2):
                for a in range(M - r + 1):
                    p = Fraction(a, M - r)
                    stop = Fraction(r, M)
                    halt = p + (1 - p) * stop
                    self.assertEqual(1 / halt, Fraction(M * (M-r), a*(M-r)+r*(M-r)))
                    success = p / halt
                    self.assertEqual(success, Fraction(a*M, (M-r)*(a+r)))


if __name__ == '__main__':
    unittest.main()
