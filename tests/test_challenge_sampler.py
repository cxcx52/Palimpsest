import json
from math import comb
from pathlib import Path
import random
import unittest

from prototype.challenge_sampler import FixedWeightChallenges
from prototype.comparison_bridges import Ring,operator_norm


class TestFixedWeightChallenges(unittest.TestCase):
    def test_toy_rank_bijection_encoding_and_all_unit_differences(self):
        c=FixedWeightChallenges({'method':'trial','n':5},N=8,support=4,weight=2)
        elements=[c.unrank(i) for i in range(c.size)]
        self.assertEqual(len(set(elements)),comb(4,2)*4)
        r=Ring(8,5)
        for i,a in enumerate(elements):
            self.assertEqual(c.decode(c.encode(a)),a)
            for b in elements[:i]:
                d=r.sub(r.elt(a),r.elt(b))
                self.assertEqual(r.mul(d,r.inv(d)),r.elt(1))

    def test_actual_profile_is_implicit_and_has_exact_norm_and_size(self):
        certificate=json.loads((Path(__file__).resolve().parents[1]/'prototype/data/commitment_prime_certificate.json').read_text())
        c=FixedWeightChallenges(certificate);rng=random.Random(83)
        self.assertEqual(c.factor_degree,256)
        self.assertEqual(c.size,comb(128,64)*2**64)
        self.assertEqual(c.encoded_bytes,24)
        for _ in range(16):
            value=c.sample(rng.randrange)
            self.assertEqual(operator_norm(value),64)
            self.assertEqual(c.decode(c.encode(value)),value)
            self.assertFalse(any(value[128:]))

    def test_bad_factor_degree_and_noncanonical_encoding_rejected(self):
        with self.assertRaises(ValueError):
            FixedWeightChallenges({'method':'trial','n':17},N=8,support=4,weight=2)
        c=FixedWeightChallenges({'method':'trial','n':5},N=8,support=4,weight=2)
        for rank in (-1,c.size):
            with self.assertRaises(ValueError):c.unrank(rank)
        for value in (b'',b'\0',b'\xff'):
            with self.assertRaises(ValueError):c.decode(value)


if __name__=='__main__':unittest.main(verbosity=2)
