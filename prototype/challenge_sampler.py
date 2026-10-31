"""Implicit, uniform fixed-weight ternary challenges with a prime certificate.

Uniform rank sampling avoids enumerating the exponentially large set. The
factor-degree condition proves unit differences; exhaustive inversion is used
only by the tiny-ring tests. No spectral norm is substituted for the induced
coefficient-infinity norm, which here is exactly the fixed weight.
"""
from math import comb
from secrets import randbelow
from .prime_certificate import verify


class FixedWeightChallenges:
    def __init__(self,certificate,N=512,support=128,weight=64):
        if not verify(certificate):raise ValueError('invalid prime certificate')
        q=certificate['n']
        if q<3 or type(N) is not int or N<2 or N&(N-1):
            raise ValueError('odd prime and power-of-two N>=2 required')
        if any(type(v) is not int for v in (support,weight)) or not 1<=weight<=support<=N:
            raise ValueError('invalid support or weight')
        order=1;residue=q%(2*N)
        while residue!=1:
            residue=(residue*q)%(2*N);order+=1
            if order>N:raise ValueError('invalid cyclotomic order')
        if support>order:raise ValueError('support exceeds irreducible factor degree')
        self.N=N;self.q=q;self.support=support;self.weight=weight
        self.factor_degree=order;self.size=comb(support,weight)*2**weight
        self.encoded_bytes=(support+weight+7)//8

    def unrank(self,rank):
        if type(rank) is not int or not 0<=rank<self.size:raise ValueError('invalid rank')
        signs=rank%(2**self.weight);index=rank>>self.weight
        remaining=self.weight;out=[0]*self.N;j=0
        for position in range(self.support):
            if not remaining:break
            count=comb(self.support-position-1,remaining-1)
            if index<count:
                out[position]=1 if (signs>>j)&1 else -1
                j+=1;remaining-=1
            else:index-=count
        if remaining or index:raise ArithmeticError('unranking failed')
        return tuple(out)

    def sample(self,draw_rank=randbelow):
        """draw_rank(M) must be uniform; default uses the OS-backed secrets API."""
        return self.unrank(draw_rank(self.size))

    def encode(self,value):
        if (len(value)!=self.N or any(type(c) is not int or c not in (-1,0,1) for c in value)
                or any(value[self.support:]) or sum(c!=0 for c in value)!=self.weight):
            raise ValueError('invalid fixed-weight challenge')
        positions=0;signs=0;j=0
        for i,c in enumerate(value[:self.support]):
            if c:
                positions|=1<<i
                if c>0:signs|=1<<j
                j+=1
        return (positions|(signs<<self.support)).to_bytes(self.encoded_bytes,'little')

    def decode(self,data):
        if len(data)!=self.encoded_bytes:raise ValueError('incorrect challenge byte length')
        word=int.from_bytes(data,'little')
        if word>>(self.support+self.weight):raise ValueError('nonzero encoding padding')
        positions=word%(2**self.support);signs=word>>self.support
        if positions.bit_count()!=self.weight:raise ValueError('wrong challenge weight')
        out=[0]*self.N;j=0
        for i in range(self.support):
            if (positions>>i)&1:
                out[i]=1 if (signs>>j)&1 else -1;j+=1
        return tuple(out)
