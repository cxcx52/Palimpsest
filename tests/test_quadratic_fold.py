from fractions import Fraction
from itertools import product
import random
import unittest

from prototype.quadratic_fold import (Ring,compress,rerandomization,old_polynomial,
    evaluate_polynomial,honest_cross_terms,fold_witness,fold_error,
    extract_star,sample_star,ternary_challenges)


class TestQuadraticFold(unittest.TestCase):
    def setUp(self):
        self.r=Ring(4,7)
        self.C=ternary_challenges(self.r,2)
        self.z,self.one=self.r.elt(0),self.r.elt(1)

    def relation(self,w):
        # w=(u,b,c); valid sources have b,c in {0,1}, u=1.
        r=self.r;u,b,c=w
        return (r.sub(r.mul(b,b),r.mul(b,u)),
                r.sub(r.mul(c,c),r.mul(c,u)),self.z,self.z)

    def test_nonconstant_strong_challenges_are_units_in_differences(self):
        self.assertEqual(len(self.C),9)
        for a,b in product(self.C,repeat=2):
            if a!=b:
                d=self.r.sub(a,b)
                self.assertEqual(self.r.mul(d,self.r.inv(d)),self.one)
        with self.assertRaises(ValueError):self.r.inv(self.z)
        # X^4+1=(X^2+3X+1)(X^2+4X+1) over F_7.
        with self.assertRaises(ValueError):self.r.inv(self.r.elt((1,3,1,0)))

    def test_rerandomization_coefficients_are_exact(self):
        w=(self.one,self.C[1],self.C[5]);beta=(self.C[3],self.C[2])
        for delta,alpha in product(self.C,repeat=2):
            F=old_polynomial(self.r,self.relation(w),beta,delta)
            updated=rerandomization(self.r,beta,delta,alpha)
            self.assertEqual(evaluate_polynomial(self.r,F,alpha),
                             compress(self.r,self.relation(w),updated))

    def test_additive_completeness_and_star_at_high_arity(self):
        r=self.r;beta=(self.C[3],self.C[4]);delta=self.C[2];alpha=self.C[6]
        old=(self.C[2],self.C[5],self.C[8])
        fresh=tuple((self.one,r.elt(j%2),r.elt((j//2)%2)) for j in range(8))
        e=compress(r,self.relation(old),beta)
        F=old_polynomial(r,self.relation(old),beta,delta)
        updated=rerandomization(r,beta,delta,alpha)
        linear,mixed=honest_cross_terms(r,self.relation,updated,old,fresh)
        self.assertEqual(len(linear)+len(mixed),36)
        y=tuple(self.C[j%len(self.C)] for j in range(8))
        anchor=fold_witness(r,old,fresh,y)
        self.assertEqual(compress(r,self.relation(anchor),updated),
                         fold_error(r,e,F[1:],alpha,linear,mixed,y,t=2))
        branches=[]
        for j in range(8):
            changed=self.C[(j+1)%len(self.C)]
            yp=list(y);yp[j]=changed
            branch=fold_witness(r,old,fresh,yp)
            self.assertEqual(compress(r,self.relation(branch),updated),
                             fold_error(r,e,F[1:],alpha,linear,mixed,yp,t=2))
            branches.append((changed,branch))
        recovered,inputs,_,_=extract_star(r,y,anchor,branches)
        self.assertEqual((recovered,inputs),(old,fresh))

    def test_omitted_fresh_square_is_an_actual_validity_check(self):
        r=self.r;old=(self.z,self.z,self.z)
        bad=(self.one,r.elt(2),self.z)
        beta=(self.z,self.z)
        linear,mixed=honest_cross_terms(r,self.relation,beta,old,(bad,))
        output=fold_witness(r,old,(bad,),(self.one,))
        self.assertNotEqual(compress(r,self.relation(output),beta),
                            fold_error(r,self.z,(self.z,self.z),self.one,linear,mixed,(self.one,),t=2))

    def test_archived_formula_homogeneous_counterexample(self):
        # f(a,b)=ab; W0=(1,0), W1=(0,1), both valid. Archived k=1
        # weights give H=Y-1, whereas K*Y*(Y-1) always vanishes at Y=0.
        q=7
        self.assertEqual((1*0)%q,0);self.assertEqual((0*1)%q,0)
        self.assertEqual((0-1)%q,6)
        for K in range(q):self.assertEqual((K*0*(0-1))%q,0)

    def test_actual_star_sampler_rejects_singleton_and_recovers_dense_set(self):
        rng=random.Random(19)
        result,calls=sample_star((0,1,2),2,lambda y:y,rng,8)
        self.assertIsNotNone(result)
        y,center,branches=result
        self.assertEqual(y,center)
        self.assertEqual(len(branches),2)
        for j,(c,branch) in enumerate(branches):
            self.assertNotEqual(c,y[j]);self.assertEqual(branch[j],c)
        for _ in range(30):
            result,calls=sample_star((0,1,2),2,
                                    lambda y:y if y==(0,0) else None,rng,2)
            self.assertIsNone(result)

    def test_all_tiny_acceptance_sets_satisfy_singleton_and_cost_bounds(self):
        # Exact, exhaustive check over every S subset of C^2; not a Monte Carlo
        # substitute for the general proof. Includes sparse/adaptive fibers.
        points=list(product(range(3),repeat=2));M=3;k=2;R=4;L=M*R
        for mask in range(1<<len(points)):
            accepted={p for i,p in enumerate(points) if (mask>>i)&1}
            for j in range(k):
                singleton_mass=Fraction(0);expected_cost=Fraction(0)
                for other in range(M):
                    fiber=[p for p in accepted if p[1-j]==other];n=len(fiber)
                    if n==0:continue
                    if n==1:
                        singleton_mass+=Fraction(1,M**k)
                        trials=Fraction(L)
                    else:
                        success=Fraction(n-1,M)
                        trials=(1-(1-success)**L)/success
                    expected_cost+=Fraction(n,M**k)*trials
                self.assertLessEqual(singleton_mass,Fraction(1,M))
                self.assertLessEqual(expected_cost,2+R)

    def test_malformed_ring_vectors_and_challenge_sets_are_rejected(self):
        with self.assertRaises(ValueError):self.r.add((1,),self.one)
        with self.assertRaises(ValueError):self.r.vsub((self.one,),())
        with self.assertRaises(ValueError):Ring(3,7)
        with self.assertRaises(ValueError):
            sample_star((0,0,1),1,lambda y:y,random.Random(1),2)
        with self.assertRaises(ValueError):
            fold_error(self.r,self.z,(),self.one,(),(),(self.one,),t=0)
        with self.assertRaisesRegex(ValueError,'polynomial message shape'):
            fold_error(self.r,self.z,(self.z,self.z,self.z),self.one,
                       (self.z,),(),(self.one,),t=2)

    def test_extracted_numerator_is_actual_short_integer_difference(self):
        old,fresh,slacks,numerators=extract_star(self.r,(self.one,),
            (self.one,),((self.z,(self.r.elt(2),)),))
        self.assertEqual(numerators,(((-1,0,0,0),),))
        self.assertEqual(fresh,((self.r.elt(-1),),))
        self.assertEqual(old,(self.r.elt(2),))


if __name__=='__main__':unittest.main(verbosity=2)
