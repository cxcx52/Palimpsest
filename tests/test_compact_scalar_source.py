import json
from pathlib import Path
import random
import unittest

from prototype.compact_scalar_source import CompactScalarSource,negacyclic

HERE=Path(__file__).resolve().parent
Q=json.loads((HERE.parent/'prototype/data/commitment_prime_certificate.json').read_text())['n']


class TestCompactSource(unittest.TestCase):
    def setUp(self):self.source=CompactScalarSource(Q)

    def test_boundary_and_random_field_multiplications(self):
        s=self.source;rng=random.Random(20261031)
        cases=[(0,0),(0,s.p-1),(1,s.p-1),(s.p-1,s.p-1)]
        cases += [(rng.randrange(s.p),rng.randrange(s.p)) for _ in range(32)]
        for x,y in cases:
            bits=s.encode(x,y,session=2**255,source_label=2**127,sequence=2**64-1)
            public=s.project(bits);values=s.decode(bits)
            self.assertTrue(s.check(bits,public))
            self.assertEqual(public['E'],(x*y)%s.p)
            self.assertEqual(x*y,values['E']+s.p*values['h'])
            self.assertLessEqual(values['h'],s.p-2)

    def test_every_arithmetic_equation_and_public_field_is_enforced(self):
        s=self.source;bits=s.encode(17,29);values=s.decode(bits);public=s.project(bits)
        for name in ('h','slack_x','slack_y','slack_E'):
            altered=dict(values);altered[name]^=1
            with self.assertRaisesRegex(ValueError,'invalid strict'):
                s.check(s.encode_forms(altered),public)
        altered=dict(values);altered['E']^=1
        changed=s.encode_forms(altered)
        with self.assertRaises(ValueError):s.check(changed,s.project(changed))
        for name in public:
            changed=dict(public);changed[name]+=1
            with self.assertRaises(ValueError):s.check(bits,changed)

    def test_noncanonical_values_and_too_small_modulus_are_rejected(self):
        s=self.source
        for x in (-1,s.p,2**51):
            with self.assertRaises(ValueError):s.encode(x,1)
        for kwargs in ({'session':2**256},{'source_label':2**128},{'sequence':2**64}):
            with self.assertRaises(ValueError):s.encode(1,1,**kwargs)
        for q in (2**64-59,2**96,s.integer_residual_bound):
            with self.assertRaises(ValueError):CompactScalarSource(q)
        bits=list(s.encode(1,1));bits[1]=2
        with self.assertRaises(ValueError):s.decode(bits)

    def test_full_toy_ring_interface_has_exact_rows_and_homogeneity(self):
        class SmallRingSource(CompactScalarSource):N=4
        s=SmallRingSource(Q);bits=s.encode(18,33)
        witness=tuple((b,0,0,0) for b in bits)
        rows=tuple(s.evaluate_homogeneous_rows(witness))
        self.assertEqual(len(rows),1024);self.assertTrue(all(row==(0,0,0,0) for row in rows))
        self.assertEqual(len(tuple(s.evaluate_homogeneous_rows(witness,pad=False))),809)
        c=(1,1,0,0);scaled=tuple(negacyclic(c,w,Q) for w in witness)
        self.assertTrue(all(row==(0,0,0,0) for row in s.evaluate_homogeneous_rows(scaled)))
        self.assertEqual(s.project_ring(scaled)['u'],c)
        corrupt=list(witness);corrupt[-1]=(0,1,0,0)
        self.assertTrue(any(any(row) for row in s.evaluate_homogeneous_rows(corrupt)))

    def test_precise_scope_and_dimensions(self):
        m=self.source.manifest()
        self.assertEqual((m['witness_ring_coordinates'],m['polynomial_rows'],m['padded_rows']),
                         (806,809,1024))
        self.assertEqual(m['integer_residual_abs_bound'],(2**51-1)**2)
        self.assertIn('512-coefficient',m['not_implemented_here'])
        self.assertEqual(m['public_projection_count'],9)
        public=self.source.project(self.source.encode(1,2,session=3,sequence=1))
        self.assertEqual(self.source.check_batch_labels([public],(3,0,0,0),0),1)
        with self.assertRaises(ValueError):self.source.check_batch_labels([public],(3,0,0,0),1)


if __name__=='__main__':unittest.main(verbosity=2)
