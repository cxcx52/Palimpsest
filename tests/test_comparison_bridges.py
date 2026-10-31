"""Algebra/algorithm tests only; no cryptographic security benchmark."""

from fractions import Fraction
from itertools import product
import random
import unittest

from prototype.comparison_bridges import (
    Ring, KernelCertificate, ThreePointSample, analyze_three_point_star, compare_stars,
    comparison_bounds, infinity_norm, integer_mul, make_star_record,
    matrix_vector, sample_three_point_star, sampling_parameters,
    validate_strong_challenges,
)


class CycleChoice:
    """Deterministic sampling tape including duplicate/rejected challenges."""
    def __init__(self, values):
        self.values, self.position = tuple(values), 0

    def choice(self, population):
        value = self.values[self.position % len(self.values)]
        self.position += 1
        if value not in population:
            raise AssertionError("test tape outside challenge set")
        return value


class TestComparisonBridges(unittest.TestCase):
    def setUp(self):
        self.r = Ring(4, 7)
        r = self.r
        self.zero, self.one = r.elt(0), r.elt(1)
        self.x = r.elt((0, 1, 0, 0))
        self.C = tuple(r.elt((a, b, 0, 0)) for a, b in product((-1, 0, 1), repeat=2))
        # Deliberately collision-bearing test matrix, not a uniform-hardness
        # instance. A's last two columns coincide, P fixes the u coordinate.
        self.A = ((r.elt((2, 1, 0, 0)), r.elt((1, 0, 1, 0)),
                   r.elt((1, 0, 1, 0))),)
        self.P = ((self.one, self.zero, self.zero),)
        self.fresh_a = (self.one, self.one, self.zero)
        self.fresh_b = (self.one, self.zero, self.one)
        self.old_zero = (self.zero,) * 3

    def fold(self, old, fresh, y):
        result = old
        for challenge, opening in zip(y, fresh):
            result = self.r.vadd(result, self.r.scale(challenge, opening))
        return result

    def star(self, old, fresh, y, alternatives, *, G=3, T=2):
        branches = []
        for j, alternative in enumerate(alternatives):
            changed = list(y)
            changed[j] = alternative
            branches.append((alternative, self.fold(old, fresh, tuple(changed))))
        return make_star_record(self.r, y, self.fold(old, fresh, y),
                                branches, T=T, G=G)

    def phi(self, witness):
        r = self.r
        u, b, c = witness
        return r.add(r.sub(r.mul(b, b), r.mul(u, b)),
                     r.sub(r.mul(c, c), r.mul(u, c)))

    def error_messages(self, old, fresh):
        r = self.r
        def cross(a, b):
            return r.sub(r.sub(self.phi(r.vadd(a, b)), self.phi(a)), self.phi(b))
        return (self.phi(old), tuple(cross(old, w) for w in fresh),
                tuple(cross(fresh[i], fresh[j]) for i in range(len(fresh))
                      for j in range(i + 1, len(fresh))))

    def assert_certificate(self, certificate):
        self.assertIsNotNone(certificate)
        self.assertTrue(any(c % self.r.q for w in certificate.vector for c in w))
        self.assertTrue(all(not any(w) for w in matrix_vector(self.r, self.A,
                                                            certificate.vector)))
        self.assertTrue(all(not any(w) for w in matrix_vector(self.r, self.P,
                                                            certificate.vector)))
        self.assertEqual(certificate.norm, infinity_norm(certificate.vector))
        self.assertLessEqual(certificate.norm, certificate.bound)

    def test_actual_integer_negacyclic_product_does_not_reduce_mod_q(self):
        result = integer_mul(self.r, (7, 0, 0, 2), (0, 0, 0, 3))
        self.assertEqual(result, (0, 0, -6, 21))
        self.assertNotEqual(result, self.r.elt(result))

    def test_nonconstant_challenge_set_has_pairwise_unit_differences(self):
        self.assertEqual(validate_strong_challenges(self.r, self.C), self.C)
        self.assertTrue(any(c[1] for c in self.C))

    def test_different_fresh_openings_return_real_small_integer_kernel(self):
        left = self.star(self.old_zero, (self.fresh_a,), (self.r.add(self.one, self.x),),
                         (self.r.elt(-1),), G=1)
        right = self.star(self.old_zero, (self.fresh_b,), (self.x,),
                          (self.r.elt((-1, -1, 0, 0)),), G=1)
        certificate = compare_stars(self.r, self.A, left, right, projection=self.P)
        self.assert_certificate(certificate)
        self.assertEqual(certificate.branch, "fresh")
        self.assertEqual(certificate.bound, 8 * 2 * 1)
        self.assertTrue(any(c < 0 for w in certificate.vector for c in w))
        expected = self.r.scale(self.r.mul(self.r.elt(left.slacks[0]),
                                          self.r.elt(right.slacks[0])),
                                self.r.vsub(left.fresh[0], right.fresh[0]))
        self.assertEqual(tuple(self.r.elt(w) for w in certificate.vector), expected)

    def test_fresh_equal_old_different_uses_oriented_product_once(self):
        old_left = (self.zero, self.one, self.zero)
        old_right = (self.zero, self.zero, self.one)
        fresh = (self.fresh_a, self.fresh_b)
        plus, minus = self.r.elt((1, 1, 0, 0)), self.r.elt((-1, -1, 0, 0))
        left = self.star(old_left, fresh, (plus, plus), (minus, minus))
        right = self.star(old_right, fresh, (self.zero, self.zero), (self.one, self.x))
        self.assertEqual(left.fresh, right.fresh)
        self.assertNotEqual(left.old, right.old)
        certificate = compare_stars(self.r, self.A, left, right, projection=self.P)
        self.assert_certificate(certificate)
        self.assertEqual(certificate.branch, "old_oriented")
        self.assertEqual(certificate.bound, 2 * 3 * 3 * 4**2)
        self.assertGreater(certificate.norm, self.r.q)
        self.assertNotEqual(certificate.vector,
                            tuple(self.r.elt(w) for w in certificate.vector))
        S = self.r.mul(self.r.elt(left.slacks[0]), self.r.elt(left.slacks[1]))
        expected = self.r.scale(S, self.r.vsub(left.old, right.old))
        self.assertEqual(tuple(self.r.elt(w) for w in certificate.vector), expected)

    def test_same_full_tuple_has_no_spurious_kernel_certificate(self):
        left = self.star(self.old_zero, (self.fresh_a,), (self.x,), (self.one,))
        right = self.star(self.old_zero, (self.fresh_a,), (self.one,), (self.zero,))
        self.assertIsNone(compare_stars(self.r, self.A, left, right, projection=self.P))

    def test_comparison_rejects_different_input_commitments(self):
        left = self.star(self.old_zero, (self.fresh_a,), (self.x,), (self.one,))
        changed = (self.one, self.zero, self.zero)
        right = self.star(self.old_zero, (changed,), (self.one,), (self.zero,))
        with self.assertRaisesRegex(ValueError, "same input commitments"):
            compare_stars(self.r, self.A, left, right, projection=self.P)

    def test_exact_parameter_bounds_and_rounding(self):
        bounds = comparison_bounds(8, 128, 1016)
        self.assertEqual(bounds.rho, 2**64)
        self.assertEqual(bounds.oriented, 337354055620000279953408)
        self.assertEqual(bounds.legacy, bounds.oriented * bounds.rho)
        self.assertEqual(bounds.three_point, 1040384)
        self.assertEqual(bounds.short_tuple, 2048)
        self.assertEqual(sampling_parameters(8), (1, 17))
        self.assertEqual(sampling_parameters(8, three_point=True), (1, 37))
        self.assertEqual(sampling_parameters(1, three_point=True), (1, Fraction(11, 2)))
        eta = Fraction(1, 2**160 * 64)
        self.assertEqual(sampling_parameters(8, eta, legacy=True), (170, 1377))
        self.assertEqual(sampling_parameters(8, eta, three_point=True, legacy=True),
                         (171, 2753))
        # Outside the current G>=k family the short-old stage can dominate.
        self.assertEqual(comparison_bounds(5, 1, 0).three_point, 10)
        with self.assertRaises(ValueError): sampling_parameters(2, 0.25, legacy=True)
        with self.assertRaises(ValueError): sampling_parameters(2, Fraction(1), legacy=True)
        with self.assertRaises(ValueError): sampling_parameters(2, eta)
        with self.assertRaises(ValueError): comparison_bounds(0, 2, 3)

    def test_real_three_point_sampler_excludes_center_and_first_fork(self):
        C = (self.zero, self.one, self.x)
        tape = CycleChoice((self.zero, self.zero, self.one, self.one, self.zero, self.x))
        sample, stats = sample_three_point_star(self.r, C, 1, lambda y: y,
                                                tape, 2)
        self.assertIsNotNone(sample)
        self.assertEqual(sample.y, (self.zero,))
        self.assertEqual(tuple(c for c, _ in sample.branches[0]), (self.one, self.x))
        self.assertEqual(stats.oracle_calls, 3)
        self.assertEqual(stats.fork_trials, 5)
        self.assertEqual(stats.initial_draws, 1)

    def test_sampler_doubleton_fiber_times_out_on_second_distinct_fork(self):
        C = (self.zero, self.one, self.x)
        tape = CycleChoice(C)
        sample, stats = sample_three_point_star(
            self.r, C, 1, lambda y: y if y[0] in (self.zero, self.one) else None,
            tape, 2)
        self.assertIsNone(sample)
        self.assertEqual(stats.fork_trials, 1 + len(C) * 2)
        self.assertGreater(stats.fork_trials, stats.oracle_calls - 1)

    def test_sampler_rejection_at_real_center_has_no_retry(self):
        sample, stats = sample_three_point_star(self.r, self.C, 2,
                                                lambda _: None, random.Random(9), 2)
        self.assertIsNone(sample)
        self.assertEqual(stats.oracle_calls, 1)
        self.assertEqual(stats.fork_trials, 0)

    def child_kernel(self):
        vector = ((0, 0, 0, 0), (1, 0, 0, 0), (-1, 0, 0, 0))
        certificate = KernelCertificate("child", None, vector, 1, 1)
        self.assert_certificate(certificate)
        return certificate

    def test_sampler_absorbs_valid_kernel_at_center(self):
        certificate = self.child_kernel()
        tape = CycleChoice((self.zero, self.one, self.x))
        result, stats = sample_three_point_star(self.r, tape.values, 1,
                                                lambda _: certificate, tape)
        self.assertIs(result, certificate)
        self.assertEqual((stats.oracle_calls, stats.fork_trials, tape.position), (1, 0, 1))

    def test_sampler_absorbs_valid_kernel_at_first_fork(self):
        certificate = self.child_kernel()
        tape = CycleChoice((self.zero, self.one, self.x))
        result, stats = sample_three_point_star(
            self.r, tape.values, 1,
            lambda y: certificate if y[0] == self.one else y, tape)
        self.assertIs(result, certificate)
        self.assertEqual((stats.oracle_calls, stats.fork_trials, tape.position), (2, 1, 2))

    def test_sampler_absorbs_valid_kernel_at_second_fork(self):
        certificate = self.child_kernel()
        tape = CycleChoice((self.zero, self.one, self.x))
        result, stats = sample_three_point_star(
            self.r, tape.values, 1,
            lambda y: certificate if y[0] == self.x else y, tape)
        self.assertIs(result, certificate)
        self.assertEqual((stats.oracle_calls, stats.fork_trials, tape.position), (3, 2, 3))

    def test_three_point_real_targets_imply_all_fresh_square_coefficients_zero(self):
        r = self.r
        old = (self.one, self.zero, self.zero)
        fresh = (self.fresh_a, self.fresh_b)
        sample, _ = sample_three_point_star(
            r, self.C, 2, lambda y: self.fold(old, fresh, y), random.Random(31), 4)
        constant, linear, mixed = self.error_messages(old, fresh)
        analysis = analyze_three_point_star(r, self.A, sample, self.phi,
                                            constant, linear, mixed, T=2, G=3,
                                            projection=self.P)
        self.assertIsNone(analysis.collision)
        self.assertEqual(analysis.first_star.fresh, fresh)
        self.assertEqual(analysis.first_star.old, old)
        self.assertEqual(analysis.square_coefficients, (self.zero, self.zero))

    def test_three_point_noncollinear_valid_targets_return_actual_kernel(self):
        # Both bit sources are valid and open the same source commitment.
        # The adversary chooses a different opening on the second fork.
        sample = ThreePointSample((self.zero,), self.old_zero,
                                  (((self.one, self.fresh_a),
                                    (self.x, self.r.scale(self.x, self.fresh_b))),))
        analysis = analyze_three_point_star(self.r, self.A, sample, self.phi,
                                            self.zero, (self.zero,), (),
                                            T=1, G=1, projection=self.P)
        self.assert_certificate(analysis.collision)
        self.assertEqual(analysis.collision.branch, "three_point_line")
        self.assertEqual(analysis.collision.bound, 8)
        self.assertEqual(analysis.square_coefficients, ())

    def test_missing_fork_to_fork_unit_has_a_real_quadratic_counterexample(self):
        r = Ring(2, 5)
        z, one, c2 = r.elt(0), r.elt(1), r.elt((0, 3))
        # X^2+1 splits at 2 and 3. e evaluates to (1,0), a nonzero idempotent.
        e = r.elt((3, 4))
        self.assertEqual(r.mul(e, e), e)
        r.inv(r.sub(z, one)); r.inv(r.sub(z, c2))
        with self.assertRaises(ValueError): r.inv(r.sub(one, c2))
        old, fresh = (z, r.elt(-1)), (e, one)
        phi = lambda w: r.mul(w[0], w[1])
        targets = [r.vadd(old, r.scale(c, fresh)) for c in (z, one, c2)]
        self.assertTrue(all(phi(v) == z for v in targets))
        self.assertEqual(phi(fresh), e)  # Nonzero square coefficient!
        sample = ThreePointSample((z,), targets[0],
                                  (((one, targets[1]), (c2, targets[2])),))
        with self.assertRaisesRegex(ValueError, "difference is not a unit"):
            analyze_three_point_star(r, ((one, one),), sample, phi,
                                     z, (z,), (), T=2, G=2)
        with self.assertRaisesRegex(ValueError, "difference is not a unit"):
            sample_three_point_star(r, (z, one, c2), 1, lambda y: y,
                                    random.Random(1), 2)

    def test_vanishing_at_origin_does_not_replace_homogeneity(self):
        r = self.r
        # f(x,z)=xz-x vanishes at zero, but f(c,1)=0 for every c while
        # f(1,0)=-1. Three valid targets do not certify a nonhomogeneous f.
        phi = lambda w: r.sub(r.mul(w[0], w[1]), w[0])
        old, fresh = (self.zero, self.one), (self.one, self.zero)
        values = tuple(r.vadd(old, r.scale(c, fresh))
                       for c in (self.zero, self.one, self.x))
        self.assertEqual(phi((self.zero, self.zero)), self.zero)
        self.assertTrue(all(phi(v) == self.zero for v in values))
        self.assertNotEqual(phi(fresh), self.zero)
        sample = ThreePointSample((self.zero,), values[0],
                                  (((self.one, values[1]), (self.x, values[2])),))
        with self.assertRaisesRegex(ValueError, "quadratic coefficient identity"):
            analyze_three_point_star(r, ((self.one, self.one),), sample, phi,
                                     self.zero, (self.zero,), (), T=1, G=1)

    def test_malformed_and_overbound_targets_do_not_pass_as_proof_data(self):
        with self.assertRaises(ValueError):
            make_star_record(self.r, (self.one,), self.fresh_a,
                             ((self.one, self.fresh_a),), T=1, G=1)
        with self.assertRaisesRegex(ValueError, "exceeds G"):
            make_star_record(self.r, (self.one,), (self.r.elt(2),),
                             ((self.zero, (self.zero,)),), T=1, G=1)
        with self.assertRaisesRegex(ValueError, "exceeds T"):
            self.star(self.old_zero, (self.fresh_a,),
                      (self.r.add(self.one, self.x),), (self.zero,), T=1)
        with self.assertRaisesRegex(ValueError, "distinct"):
            validate_strong_challenges(self.r, (self.zero, self.one, self.r.elt(8)))
        sample = ThreePointSample((self.zero,), self.old_zero,
                                  (((self.one, self.fresh_a),
                                    (self.x, self.r.scale(self.x, self.fresh_a))),))
        with self.assertRaisesRegex(ValueError, "target relation"):
            analyze_three_point_star(self.r, self.A, sample, self.phi,
                                     self.one, (self.zero,), (), T=1, G=1)

    def test_exhaustive_fiber_geometric_cost_bound(self):
        # Exact rational calculation for all acceptance sizes, not a simulation.
        for M in range(3, 12):
            R, L = 3, 3 * M
            for accepted in range(1, M + 1):
                if accepted == 1:
                    weighted = Fraction(L, M)
                else:
                    p1 = Fraction(accepted - 1, M)
                    success_first = 1 - (1 - p1)**L
                    first_cost = success_first / p1
                    if accepted == 2:
                        second_cost = Fraction(L)
                    else:
                        p2 = Fraction(accepted - 2, M)
                        second_cost = (1 - (1 - p2)**L) / p2
                    weighted = Fraction(accepted, M) * (first_cost +
                                                       success_first * second_cost)
                self.assertLessEqual(weighted, 2 + 2 * R)

    def test_constant_cap_exact_loss_and_cost_for_every_small_fiber(self):
        for M in range(3, 101):
            for accepted in range(1, M + 1):
                p1 = Fraction(accepted - 1, M)
                first_success = 1 - (1 - p1)**M
                first_cost = Fraction(M) if p1 == 0 else first_success / p1
                p2 = Fraction(max(0, accepted - 2), M)
                second_success = 1 - (1 - p2)**M
                second_cost = Fraction(M) if p2 == 0 else second_success / p2
                mass = Fraction(accepted, M)
                self.assertLessEqual(mass * (1 - first_success), Fraction(1, M))
                self.assertLessEqual(mass * (1 - first_success * second_success),
                                     Fraction(2, M))
                self.assertLessEqual(mass * first_cost, 2)
                self.assertLessEqual(mass * (first_cost + first_success * second_cost),
                                     Fraction(9, 2))

    def test_constant_cap_all_acceptance_sets_with_arbitrary_cost_coupling(self):
        # For C^2 with |C|=3 exhaust all S and nine unit cost basis vectors.
        # Linearity covers every nonnegative cost vector on these nine points.
        M, k = 3, 2
        points = tuple(product(range(M), repeat=k))
        D = len(points)
        for mask in range(1 << D):
            accepted = {p for i, p in enumerate(points) if mask >> i & 1}
            rates = {}
            for center in accepted:
                for j in range(k):
                    fiber = tuple(i for i, p in enumerate(points)
                                  if p[1 - j] == center[1 - j])
                    count = sum(points[i] in accepted for i in fiber)
                    p1, p2 = Fraction(count - 1, M), Fraction(max(0, count - 2), M)
                    a1, a2 = 1 - (1 - p1)**M, 1 - (1 - p2)**M
                    t1 = Fraction(M) if p1 == 0 else a1 / p1
                    t2 = Fraction(M) if p2 == 0 else a2 / p2
                    rates[center, j] = fiber, a1, a2, t1, t2
            for costly_point in range(D):
                mu = Fraction(1, D)
                cost2 = cost3 = mu
                for center in accepted:
                    alive2 = alive3 = Fraction(1)
                    for j in range(k):
                        fiber, a1, a2, t1, t2 = rates[center, j]
                        cbar = Fraction(costly_point in fiber, M)
                        cost2 += alive2 * t1 * cbar / D
                        cost3 += alive3 * (t1 + a1 * t2) * cbar / D
                        alive2 *= a1
                        alive3 *= a1 * a2
                self.assertLessEqual(cost2, (1 + 2 * k) * mu)
                self.assertLessEqual(cost3, (1 + Fraction(9, 2) * k) * mu)

    def test_sampler_default_cap_is_exactly_M_even_for_doubleton_failure(self):
        C = (self.zero, self.one, self.x)
        sample, stats = sample_three_point_star(
            self.r, C, 1, lambda y: y if y[0] != self.x else None, CycleChoice(C))
        self.assertIsNone(sample)
        self.assertEqual(stats.fork_trials, 1 + len(C))


if __name__ == "__main__":
    unittest.main(verbosity=2)
