"""Reproduce the finite random-stop checks from the independent derivation.

Uses exact fractions and no production sampler code. These finite checks support
the general proof; they do not establish security or test an end-to-end extractor.
The scope is fixed: M=3..120 for success laws, and M=3..8 for every acceptance
subset and every nonnegative-cost basis vector.
"""
from fractions import Fraction
from math import comb
import json


def check_random_stop_costs():
    success_checks = 0
    for M in range(3, 121):
        for accepted in range(M + 1):
            for points in (2, 3):
                success = Fraction(accepted, M)
                if accepted < points:
                    success = Fraction(0)
                else:
                    for excluded in range(1, points):
                        success *= Fraction(
                            M * (accepted - excluded),
                            accepted * (M - excluded),
                        )
                loss = Fraction(accepted, M) - success
                if loss > Fraction(comb(points, 2), M):
                    raise AssertionError((M, accepted, points, loss))
                success_checks += 1

    cost_cases = 0
    for M in range(3, 9):
        for mask in range(1 << M):
            good = [i for i in range(M) if (mask >> i) & 1]
            accepted = len(good)
            for basis in range(M):
                costs = [Fraction(int(i == basis)) for i in range(M)]
                mu = sum(costs) / M
                cost_two = cost_three = mu
                if accepted:
                    # Every stage has halt probability accepted/M, since only
                    # successful points are excluded. Average over the ORIGINAL
                    # uniform center; do not condition its law on later success.
                    halt = Fraction(accepted, M)
                    for center in good:
                        first = (
                            sum(costs[i] for i in range(M) if i != center)
                            / (M - 1)
                            / halt
                        )
                        cost_two += first / M
                        cost_three += first / M
                        if accepted >= 2:
                            # Conditional on first-stage success, its new point
                            # is uniform among the other accepted points.
                            second = sum(
                                sum(
                                    costs[i]
                                    for i in range(M)
                                    if i not in (center, fork)
                                )
                                / (M - 2)
                                / halt
                                for fork in good
                                if fork != center
                            ) / (accepted - 1)
                            first_success = Fraction(
                                M * (accepted - 1), accepted * (M - 1)
                            )
                            cost_three += Fraction(1, M) * first_success * second
                bound_two = (1 + Fraction(M, M - 1)) * mu
                bound_three = (
                    1 + Fraction(M, M - 1) + Fraction(M, M - 2)
                ) * mu
                if cost_two > bound_two or cost_three > bound_three:
                    raise AssertionError(
                        (M, mask, basis, cost_two, cost_three,
                         bound_two, bound_three)
                    )
                cost_cases += 1

    # A positive-cost example showing why a call-count bound cannot simply be
    # multiplied by the unconditional mean cost when success and cost correlate.
    M = 3
    costs = [Fraction(1), Fraction(10), Fraction(10)]
    mu = sum(costs) / M
    actual = mu + Fraction(1, M) * (
        sum(costs[1:]) / (M - 1)
    ) / Fraction(1, M)
    valid_bound = (1 + Fraction(M, M - 1)) * mu
    if not 2 * mu < actual <= valid_bound:
        raise AssertionError((mu, actual, valid_bound))

    return {
        "status": "PASS",
        "arithmetic": "exact fractions; independent of production sampler",
        "success_laws": {
            "M_inclusive": [3, 120],
            "accepted_counts": "all integers 0..M",
            "points": [2, 3],
            "checked_cases": success_checks,
            "loss_bounds": {"two_point": "1/M", "three_point": "3/M"},
        },
        "cost_laws": {
            "M_inclusive": [3, 8],
            "acceptance_sets": "every subset",
            "cost_vectors": "every single-point nonnegative basis vector",
            "checked_cases": cost_cases,
            "two_point_multiplier": "1+M/(M-1)",
            "three_point_multiplier": "1+M/(M-1)+M/(M-2)",
        },
        "correlated_cost_example": {
            "M": M,
            "accepted_point": 0,
            "costs": [str(c) for c in costs],
            "mean_cost": str(mu),
            "actual_two_point_cost": str(actual),
            "invalid_twice_mean_cost": str(2 * mu),
            "valid_weighted_bound": str(valid_bound),
        },
        "scope": (
            "Finite probability/cost checks only. Sampling and reset overhead "
            "enters the augmented cost in the proof; this is not an end-to-end "
            "benchmark or security certification."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(check_random_stop_costs(), ensure_ascii=False, indent=2))
