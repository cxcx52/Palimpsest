"""Small, exact interactive quadratic-fold reference (not a production backend).

The relation is a supplied list of homogeneous degree-two ring polynomials.
Messages have fixed slots: F has no freely chosen constant; K has no squares.
The terminal witness is disclosed. No hiding or Fiat--Shamir is claimed.
"""
from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Ring:
    N: int
    q: int

    def __post_init__(self):
        if type(self.N) is not int or self.N<1 or self.N&(self.N-1):
            raise ValueError('power-of-two ring dimension required')
        if type(self.q) is not int or self.q<3:
            raise ValueError('q>=3 required; primality is an external precondition')

    def check_pair(self,a,b):
        if len(a)!=self.N or len(b)!=self.N:raise ValueError('incorrect ring dimension')

    def elt(self, value):
        if isinstance(value,int):
            return (value%self.q,)+(0,)*(self.N-1)
        if len(value)!=self.N:
            raise ValueError('incorrect ring dimension')
        return tuple(x%self.q for x in value)

    def add(self,a,b):
        self.check_pair(a,b)
        return tuple((x+y)%self.q for x,y in zip(a,b))

    def sub(self,a,b):
        self.check_pair(a,b)
        return tuple((x-y)%self.q for x,y in zip(a,b))

    def mul(self,a,b):
        self.check_pair(a,b)
        out=[0]*self.N
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                out[(i+j)%self.N]+=(1 if i+j<self.N else -1)*x*y
        return self.elt(out)

    def power(self,a,n):
        if n<0:raise ValueError('nonnegative power required')
        result=self.elt(1)
        while n:
            if n&1:result=self.mul(result,a)
            a=self.mul(a,a);n//=2
        return result

    def inv(self,a):
        # Exact Gaussian elimination of multiplication-by-a. For toy sizes;
        # a real implementation would use polynomial extended Euclid.
        columns=[self.mul(a,self.elt([int(i==j) for i in range(self.N)]))
                 for j in range(self.N)]
        matrix=[[columns[j][i] for j in range(self.N)]+[int(i==0)]
                for i in range(self.N)]
        for j in range(self.N):
            pivot=next((i for i in range(j,self.N) if matrix[i][j]),None)
            if pivot is None:raise ValueError('nonunit ring element')
            matrix[j],matrix[pivot]=matrix[pivot],matrix[j]
            scale=pow(matrix[j][j],-1,self.q)
            matrix[j]=[(x*scale)%self.q for x in matrix[j]]
            for i in range(self.N):
                if i!=j:
                    scale=matrix[i][j]
                    matrix[i]=[(x-scale*y)%self.q for x,y in zip(matrix[i],matrix[j])]
        return tuple(row[-1] for row in matrix)

    def centered(self,a):
        return tuple(x if x<=self.q//2 else x-self.q for x in a)

    def vadd(self,a,b):
        if len(a)!=len(b):raise ValueError('witness dimension mismatch')
        return tuple(self.add(x,y) for x,y in zip(a,b))
    def vsub(self,a,b):
        if len(a)!=len(b):raise ValueError('witness dimension mismatch')
        return tuple(self.sub(x,y) for x,y in zip(a,b))
    def scale(self,c,a):return tuple(self.mul(c,x) for x in a)


def compress(ring,rows,beta):
    if len(rows)!=2**len(beta):raise ValueError('pad relation to power of two')
    total=ring.elt(0)
    for mask,value in enumerate(rows):
        term=value
        for i,b in enumerate(beta):
            if (mask>>i)&1:term=ring.mul(term,b)
        total=ring.add(total,term)
    return total


def rerandomization(ring,beta,delta,alpha):
    return tuple(ring.add(b,ring.mul(alpha,ring.power(delta,2**i)))
                 for i,b in enumerate(beta))


def old_polynomial(ring,rows,beta,delta):
    """Full coefficients F_0,...,F_t; verifier fixes F_0 to old e."""
    out=[ring.elt(0) for _ in range(len(beta)+1)]
    if len(rows)!=2**len(beta):raise ValueError('incorrect relation size')
    for mask,value in enumerate(rows):
        term=[value]
        for i,b in enumerate(beta):
            if not (mask>>i)&1:continue
            nxt=[ring.elt(0) for _ in range(len(term)+1)]
            d=ring.power(delta,2**i)
            for j,c in enumerate(term):
                nxt[j]=ring.add(nxt[j],ring.mul(c,b))
                nxt[j+1]=ring.add(nxt[j+1],ring.mul(c,d))
            term=nxt
        for j,c in enumerate(term):out[j]=ring.add(out[j],c)
    return tuple(out)


def evaluate_polynomial(ring,coefficients,alpha):
    result=ring.elt(0)
    for coefficient in reversed(coefficients):
        result=ring.add(ring.mul(result,alpha),coefficient)
    return result


def honest_cross_terms(ring,relation,beta,old,fresh):
    def g(w):return compress(ring,relation(w),beta)
    def cross(a,b):return ring.sub(ring.sub(g(ring.vadd(a,b)),g(a)),g(b))
    linear=tuple(cross(old,w) for w in fresh)
    mixed=tuple(cross(fresh[i],fresh[j]) for i in range(len(fresh))
                for j in range(i+1,len(fresh)))
    return linear,mixed


def fold_witness(ring,old,fresh,y):
    if len(fresh)!=len(y):raise ValueError('arity mismatch')
    result=old
    for c,w in zip(y,fresh):result=ring.vadd(result,ring.scale(c,w))
    return result


def fold_error(ring,e,F,alpha,linear,mixed,y,*,t):
    k=len(y)
    if type(t) is not int or t<0 or len(F)!=t:
        raise ValueError('rerandomization polynomial message shape mismatch')
    if len(linear)!=k or len(mixed)!=k*(k-1)//2:
        raise ValueError('cross-term message shape mismatch')
    result=evaluate_polynomial(ring,(e,)+tuple(F),alpha)
    for c,kj in zip(y,linear):result=ring.add(result,ring.mul(c,kj))
    index=0
    for i in range(k):
        for j in range(i+1,k):
            result=ring.add(result,ring.mul(ring.mul(y[i],y[j]),mixed[index]))
            index+=1
    return result


def extract_star(ring,y,anchor,branches):
    """Branches are (different_j_challenge, valid_target_opening) per j.

    The caller must check each opening against the actual target relation and
    the same frozen prefix. This function performs only opening algebra.
    """
    if len(branches)!=len(y):raise ValueError('incomplete star')
    fresh=[];slacks=[];numerators=[]
    for j,(challenge,opening) in enumerate(branches):
        slack=ring.sub(y[j],challenge)
        if len(anchor)!=len(opening):raise ValueError('witness dimension mismatch')
        # Actual integer lifts, not residues such as q-1 in place of -1.
        # These signed coefficients preserve the proven ||Y_j|| <= 2G bound.
        numerator=tuple(tuple(a-b for a,b in zip(ring.centered(v),ring.centered(vj)))
                        for v,vj in zip(anchor,opening))
        for v,vj in zip(anchor,opening):ring.check_pair(v,vj)
        fresh.append(ring.scale(ring.inv(slack),numerator))
        slacks.append(slack);numerators.append(numerator)
    old=anchor
    for challenge,opening in zip(y,fresh):old=ring.vsub(old,ring.scale(challenge,opening))
    return old,tuple(fresh),tuple(slacks),tuple(numerators)


def sample_star(challenges,k,oracle,rng,R):
    """Actual bounded star sampler. oracle(y) -> valid witness or None.

    R is ceil(log2(k/eta))+1; cap is |C|*R. Expected calls are bounded
    unconditionally, including rejection at the initial real transcript.
    This routine is intended only for small explicit challenge sets.
    """
    if (not challenges or len(set(challenges))!=len(challenges)
            or type(k) is not int or type(R) is not int or k<1 or R<1):
        raise ValueError('invalid sampler parameters')
    y=tuple(rng.choice(challenges) for _ in range(k))
    center=oracle(y);calls=1
    if center is None:return None,calls
    branches=[]
    for j in range(k):
        for _ in range(len(challenges)*R):
            c=rng.choice(challenges)
            if c==y[j]:continue
            other=list(y);other[j]=c
            witness=oracle(tuple(other));calls+=1
            if witness is not None:
                branches.append((c,witness));break
        else:return None,calls
    return (y,center,tuple(branches)),calls


def ternary_challenges(ring,T):
    if not 1<=T<=ring.N:raise ValueError('invalid support')
    return tuple(ring.elt(c+(0,)*(ring.N-T)) for c in product((-1,0,1),repeat=T))
