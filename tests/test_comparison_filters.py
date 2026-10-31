"""Adversarial bridge and stopping-rule checks; no security estimates."""
from fractions import Fraction
from itertools import product
import unittest

from prototype.comparison_bridges import Ring, KernelCertificate, make_star_record
from prototype.comparison_filters import compare_on_failure, compare_fresh, compare_short_tuples


class TestComparisonFilters(unittest.TestCase):
    def setUp(self):
        self.r = Ring(4, 7)
        r = self.r
        self.z, self.o = r.elt(0), r.elt(1)
        self.A = ((r.elt(2), self.o, self.o),)
        self.P = ((self.o, self.z, self.z),)
        self.a = (self.o, self.o, self.z)
        self.b = (self.o, self.z, self.o)
        self.old = (self.z,) * 3

    def record(self, old, fresh, challenge=1):
        r = self.r
        y, alternative = r.elt(challenge), r.elt(-1)
        center = r.vadd(old, r.scale(y, fresh))
        branch = r.vadd(old, r.scale(alternative, fresh))
        return make_star_record(r, (y,), center, ((alternative, branch),), T=1, G=3)

    def kernel(self):
        return compare_fresh(self.r, self.A, self.record(self.old, self.a),
                             self.record(self.old, self.b), projection=self.P)

    def test_fresh_gate_ignores_old_but_full_tuple_gate_compares_it(self):
        left = self.record((self.z, self.o, self.z), self.a)
        right = self.record((self.z, self.z, self.o), self.a)
        self.assertIsNone(compare_fresh(self.r, self.A, left, right, projection=self.P))
        cert = compare_short_tuples(self.r, self.A, left, right, projection=self.P)
        self.assertEqual((cert.branch, cert.coordinate, cert.norm, cert.bound),
                         ('independent_short_tuple', 0, 1, 8))

    def test_same_old_different_fresh_is_not_compatible_at_second_gate(self):
        left = self.record(self.old, self.a)
        right = self.record(self.old, self.b)
        cert = compare_short_tuples(self.r, self.A, left, right, projection=self.P)
        self.assertEqual(cert.coordinate, 1)
        self.assertEqual(cert.norm, 1)
        cert_fresh = compare_fresh(self.r, self.A, left, right, projection=self.P)
        self.assertEqual(cert_fresh.bound, 24)
        self.assertEqual(cert_fresh.norm, 4)

    def test_short_gate_rejects_nonbit_and_frozen_commitment_mismatch(self):
        nonbit = self.record(self.old, (self.o, self.r.elt(2), self.z))
        with self.assertRaisesRegex(ValueError, 'scalar-bit'):
            compare_short_tuples(self.r, self.A, nonbit, nonbit, projection=self.P)
        right = self.record(self.old, (self.o, self.z, self.z))
        with self.assertRaisesRegex(ValueError, 'same frozen'):
            compare_fresh(self.r, self.A, self.record(self.old, self.a), right,
                          projection=self.P)

    def test_failure_good_and_kernel_first_trials_never_retry(self):
        kernel = self.kernel()
        for first in (None, ('good', 'first-sidecar'), kernel):
            tape = iter((first,))
            self.assertIs(compare_on_failure(lambda: next(tape), lambda _: True,
                                            lambda _a, _b: self.fail()), first)

    def test_retry_skips_failures_and_propagates_kernel(self):
        kernel = self.kernel()
        tape = iter(('bad', None, None, kernel))
        self.assertIs(compare_on_failure(lambda: next(tape), lambda _: False,
                                        lambda _a, _b: self.fail()), kernel)

    def test_second_good_record_is_used_for_kernel_not_returned(self):
        first, second = self.record(self.old, self.a), self.record(self.old, self.b)
        tape = iter((first, None, second))
        result = compare_on_failure(lambda: next(tape), lambda r: r is second,
                lambda a, b: compare_fresh(self.r, self.A, a, b, projection=self.P))
        self.assertIsInstance(result, KernelCertificate)
        self.assertEqual(result.branch, 'independent_fresh')

    def test_compatible_bad_candidates_fail_instead_of_replacing_anchor(self):
        left = self.record(self.old, self.a)
        right = self.record(self.old, self.a, challenge=0)
        self.assertNotEqual(left.y, right.y)
        tape = iter((left, right))
        result = compare_on_failure(lambda: next(tape), lambda _: False,
                lambda a, b: compare_fresh(self.r, self.A, a, b, projection=self.P))
        self.assertIsNone(result)

    def test_exact_finite_distribution_loss_and_correlated_expected_cost(self):
        # Categories: failure, kernel, good, bad-key-a, bad-key-b. Summing the
        # absorbing Markov chain is exact; a rare bad first reply initiates an
        # unbounded geometric retry. Test every nonzero weight vector in 0..2.
        for weights in product(range(3), repeat=5):
            total = sum(weights)
            if not total:
                continue
            p = tuple(Fraction(w, total) for w in weights)
            s = 1 - p[0]
            if not s:
                continue
            theta = max(p[3:])
            loss = sum(v * v / s for v in p[3:])
            self.assertLessEqual(loss, theta)
            returned_records = p[2]  # Always the first, valid record.
            kernel_mass = p[1] + sum(v * (1 - v / s) for v in p[3:])
            self.assertEqual(returned_records + kernel_mass, s - loss)
            for costly_outcome in range(5):
                # All cost basis vectors, including expensive failed trials.
                mu = p[costly_outcome]
                retry_cost = mu / s
                full_cost = mu + (p[3] + p[4]) * retry_cost
                self.assertLessEqual(full_cost, 2 * mu)


if __name__ == '__main__':
    unittest.main()
