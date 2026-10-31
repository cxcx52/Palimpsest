"""Standard-library verification of Pocklington and Lucas prime certificates.

Search/generation and its optional third-party dependencies are not packaged.
"""
from math import gcd, isqrt


def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2,isqrt(n)+1))


def verify(cert):
    if not isinstance(cert,dict) or type(cert.get('n')) is not int:
        return False
    n=cert['n']
    if cert.get('method') == 'trial':
        return n < 2**32 and trial_prime(n)
    if cert.get('method') == 'lucas_complete_factorization':
        factors=cert.get('factors');a=cert.get('base')
        if n<3 or type(a) is not int or not isinstance(factors,list) or not factors:
            return False
        product=1;primes=set()
        for entry in factors:
            if not isinstance(entry,dict) or not verify(entry.get('certificate')):
                return False
            r=entry['certificate']['n'];e=entry.get('exponent')
            if r in primes or type(e) is not int or e<1:return False
            primes.add(r);product*=r**e
        return (product==n-1 and pow(a,n-1,n)==1
                and all(gcd(pow(a,(n-1)//r,n)-1,n)==1 for r in primes))
    if cert.get('method') != 'pocklington' or not verify(cert.get('factor_certificate')):
        return False
    r=cert['factor_certificate']['n'];a=cert.get('base')
    return (type(a) is int and n>r and (n-1)%r==0 and r*r>n
            and pow(a,n-1,n)==1 and gcd(pow(a,(n-1)//r,n)-1,n)==1)
