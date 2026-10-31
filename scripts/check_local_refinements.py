# Adapted from the user-provided local audit, archived with its exact SHA256.
# Changes: portable optional output, one combined JSON, and an explicit
# zero-divisor-ring slope-mass assertion. No production protocol is changed.
"""Exact small-domain checks for proposed Palimpsest refinements.

These checks do not establish full protocol security.  They test local
counting/cost lemmas and independently recompute the stated cost formulas.
Only Python's standard library is required.
"""
from fractions import Fraction
from itertools import permutations, product
from math import comb, log2
import json
from pathlib import Path
import argparse


def without_replacement_coefficients(M, a, t):
    """Expected payment coefficient for each point after a uniform center.

    The first a points are valid records. A failed center aborts. After a
    valid center, enumerate a uniform permutation of the other points and
    stop at t additional records or exhaustion. Each point is queried once.
    """
    pay = [Fraction(0) for _ in range(M)]
    nperm = 1
    for v in range(2, M):
        nperm *= v
    unit = Fraction(1, M * nperm)
    for center in range(a):
        other = [x for x in range(M) if x != center]
        for order in permutations(other):
            found = 0
            for x in order:
                pay[x] += unit
                found += x < a
                if found == t:
                    break
    return pay


def polynomial_mul(a, b, q):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] = (out[i+j] + x*y) % q
    return out


def ring_mul(a, b, q, N):
    out = [0] * N
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            d = i+j
            # Degrees in this audit are below 2N.
            out[d % N] = (out[d % N] + (1 if d < N else -1)*x*y) % q
    return tuple(out)


def main():
    # Exhaustive payment coefficients imply the bound for every nonnegative
    # point-cost vector by linearity; they are not merely equal-cost tests.
    payment_cases = 0
    for M in range(3, 8):
        for a in range(M+1):
            for t in (1, 2):
                coeffs = without_replacement_coefficients(M, a, t)
                assert max(coeffs, default=0) <= Fraction(t, M)
                payment_cases += M

    # Exhaust all deterministic accepted-or-failed square-root response
    # functions V(c) over F_5 satisfying V(c)^2 = e + Kc. For any fixed
    # nonzero slope w, the accepted graph along slope w has degree <= 1.
    q = M = 5
    functions = slopes = 0
    max_pair_mass = Fraction(0)
    for e, K in product(range(q), repeat=2):
        choices = [[None] + [v for v in range(q) if v*v % q == (e+K*c) % q]
                   for c in range(q)]
        for values in product(*choices):
            functions += 1
            accepted = [c for c, v in enumerate(values) if v is not None]
            a = len(accepted)
            for w in range(1, q):
                slopes += 1
                degrees = [sum(d != c and
                               (values[c]-values[d]-(c-d)*w) % q == 0
                               for d in accepted) for c in accepted]
                assert max(degrees, default=0) <= 1
                edges = sum(degrees)
                mass = Fraction(edges, M*(a-1)) if a >= 2 else Fraction(0)
                assert mass <= Fraction(2, M)
                max_pair_mass = max(max_pair_mass, mass)
                if a >= 2:
                    cap_success = 1 - Fraction(M-a+1, M)**M
                    cap_mass = mass * cap_success
                    random_stop_mass = Fraction(edges, a*(M-1))
                    assert cap_mass <= Fraction(2, M)
                    assert random_stop_mass <= Fraction(1, M-1)

    # Support-degree lemma: for 2(D-1)<N, Y(Y-s)=0 mod (q,X^N+1)
    # implies Y=0 or Y=s even without size bounds (unit s not needed here).
    polynomial_pairs = 0
    for q, N, D in [(3, 4, 2), (5, 4, 2), (3, 6, 3), (5, 6, 3)]:
        assert 2*(D-1) < N
        polys = list(product(range(q), repeat=D))
        zero = (0,)*D
        for Y, s in product(polys, repeat=2):
            diff = tuple((x-y) % q for x,y in zip(Y,s))
            prod = ring_mul(Y, diff, q, N)
            if not any(prod):
                assert Y == zero or Y == s
            polynomial_pairs += 1
    # At the missing boundary, a nonconstant idempotent really exists.
    assert ring_mul((3,4), (3,4), 5, 2) == (3,4)
    assert (3,4) not in [(0,0),(1,0)]

    N, k, H, T = 512, 8, 64, 64
    challenge_size = (1 << 64) * comb(128,64)
    rows=[]
    for name, R, blocks, stat_num in [
        ('old two-gate', 148, 13, 68800),
        ('v1.7 capped three-plus-two', 54, 9, 68800),
        ('proposed two-plus-two, original capped sampler', 34, 9, 64*1069),
        ('proposed distinct-query three-plus-two', 26, 9, 68800),
        ('proposed distinct-query two-plus-two', 18, 9, 64*1069),
    ]:
        U = Fraction(1+R**H) + Fraction((R+blocks)*(R**H-1),R-1)
        rows.append(dict(name=name, R=R, local_blocks=blocks,
                         log2_U_over_B0=log2(U.numerator)-log2(U.denominator),
                         statistical_numerator=stat_num,
                         statistical_bits=log2(challenge_size)-log2(stat_num)))
    result = dict(
        verified_local_payment_basis_coefficients=payment_cases,
        field_response_functions=functions,
        fixed_bad_slope_checks=slopes,
        maximum_without_replacement_bad_slope_mass=str(max_pair_mass),
        support_degree_polynomial_pairs=polynomial_pairs,
        boundary_counterexample={'q':5,'N':2,'D':2,'nonconstant_idempotent':[3,4]},
        ledger=rows,
        scope='Local exhaustive checks and exact arithmetic, not an end-to-end or machine-checked security proof.'
    )
    return result


# Supplementary checks for the ring root argument and tensor contraction.
def supplementary_checks():
    from random import Random
    rng = Random(20261031)
    # A ring with zero divisors; challenges (c,c) have unit pairwise differences.
    q = 3
    R = list(product(range(q), repeat=2))
    maps = slope_checks = 0
    for e, K in product(R, repeat=2):
        choices = []
        for c in range(q):
            choices.append([None] + [v for v in R
                           if all(v[i]*v[i] % q == (e[i]+K[i]*c) % q for i in (0,1))])
        for vals in product(*choices):
            maps += 1
            good = [c for c,v in enumerate(vals) if v is not None]
            for w in R:
                if w == (0,0):
                    continue
                slope_checks += 1
                edges = 0
                for c in good:
                    matches = sum(d != c and all(
                        (vals[c][i]-vals[d][i]-(c-d)*w[i]) % q == 0
                        for i in (0,1)) for d in good)
                    assert matches <= 1
                    edges += matches
                a = len(good)
                mass = Fraction(edges, q*(a-1)) if a >= 2 else Fraction(0)
                assert mass <= Fraction(2, q)

    q, N = 5, 4
    zero = (0,)*N
    one = (1,)+(0,)*(N-1)
    def add(x,y): return tuple((a+b)%q for a,b in zip(x,y))
    def mul(x,y): return ring_mul(x,y,q,N)
    def pad_add(x,y):
        return [add(x[i] if i<len(x) else zero,
                    y[i] if i<len(y) else zero) for i in range(max(len(x),len(y)))]
    def linmul(a, beta, d):
        out = [zero]*(len(a)+1)
        for i,v in enumerate(a):
            out[i] = add(out[i],mul(beta,v))
            out[i+1] = add(out[i+1],mul(d,v))
        return out
    def normalize(a):
        a = list(a)
        while len(a)>1 and a[-1] == zero: a.pop()
        return a
    trials = 0
    for n in range(1,34):
        ell=(n-1).bit_length()
        for _ in range(4):
            f=[tuple(rng.randrange(q) for _ in range(N)) for _ in range(n)]
            bs=[tuple(rng.randrange(q) for _ in range(N)) for _ in range(ell)]
            ds=[tuple(rng.randrange(q) for _ in range(N)) for _ in range(ell)]
            row=[[v] for v in f]
            for beta,d in zip(bs,ds):
                row=[pad_add(row[j],linmul(row[j+1],beta,d)) if j+1<len(row)
                     else row[j] for j in range(0,len(row),2)]
            direct=[zero]
            for a,v in enumerate(f):
                p=[v]
                for i,(beta,d) in enumerate(zip(bs,ds)):
                    if (a>>i)&1: p=linmul(p,beta,d)
                direct=pad_add(direct,p)
            assert normalize(row[0]) == normalize(direct)
            trials += 1
    n=809
    levels=[]
    r=n
    while r>1:
        levels.append(r//2)
        r=(r+1)//2
    F_ops=sum(2*(i+1)*a for i,a in enumerate(levels))
    result=dict(zero_divisor_ring_response_maps=maps,
                zero_divisor_ring_fixed_slope_checks=slope_checks,
                polynomial_tensor_contraction_tests=trials,
                scalar_tensor_contraction_ring_multiplications=sum(levels),
                polynomial_F_contraction_ring_multiplication_bound=F_ops,
                factored_full_f_ring_multiplications=805+3+2,
                revised_terminal_generic_ring_multiplications=3224+805+3+2+sum(levels),
                original_terminal_generic_ring_multiplication_bound=6672)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Optional combined JSON output path.')
    args = parser.parse_args()
    result = main()
    result['supplementary_checks'] = supplementary_checks()
    serialized = json.dumps(result, ensure_ascii=False, indent=2) + '\n'
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(serialized, encoding='utf-8')
    print(serialized, end='')
