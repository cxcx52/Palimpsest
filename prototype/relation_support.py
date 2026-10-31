"""Relation helpers extracted from the archived compiler and source interface.

Only the current compact relation dependencies are retained. The earlier large
relation compiler and its external descriptor files are intentionally absent.
"""
from dataclasses import dataclass


def negacyclic(a, b, q):
    if not a or len(a) != len(b):
        raise ValueError('nonempty equal-length coefficient arrays required')
    out = [0] * len(a)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            t = i + j
            out[t % len(a)] += (1 if t < len(a) else -1) * x * y
    return tuple(x % q for x in out)


@dataclass(frozen=True)
class Row:
    family: str
    descriptor: dict
    # Each term is coefficient * product of one or two named linear forms.
    terms: tuple

    def evaluate(self, values):
        result = 0
        for coefficient, factors in self.terms:
            term = coefficient
            for name in factors:
                term *= values[name]
            result += term
        return result

    def evaluate_ring(self, values, N, q):
        result = [0] * N
        for coefficient, factors in self.terms:
            term = (1,) + (0,) * (N-1)
            for name in factors:
                term = negacyclic(term, values[name], q)
            for i, v in enumerate(term):
                result[i] = (result[i] + coefficient * v) % q
        return tuple(result)

    def interval(self, maxima):
        # After scalar-bitness is established, forms lie in [0, 2^width-1].
        lower = upper = 0
        for coefficient, factors in self.terms:
            magnitude = coefficient
            for name in factors:
                magnitude *= maxima[name]
            lower += min(0, magnitude)
            upper += max(0, magnitude)
        return lower, upper


class RingForms:
    """Lazy named linear forms of one fixed arbitrary ring witness.

    No Booleanity/range assumption is made here. Input must be an immutable
    sequence for the duration of evaluation. Values are intentionally not
    cached, so evaluating the relation does not duplicate the full witness.
    """
    def __init__(self,source,witness):
        if len(witness)!=source.witness_size:raise ValueError('witness size mismatch')
        self.source=source;self.witness=witness

    def coordinate(self,i):
        value=self.witness[i];N,q=self.source.N,self.source.q
        if len(value)!=N or any(type(c) is not int or not 0<=c<q for c in value):
            raise ValueError('noncanonical ring witness coordinate')
        return tuple(value)

    def __getitem__(self,name):
        offset,width=self.source.forms[name]
        result=[0]*self.source.N
        for j in range(width):
            for i,c in enumerate(self.coordinate(offset+j)):
                result[i]+=(1<<j)*c
        return tuple(c%self.source.q for c in result)


def verify_batch_labels(publics, session_words, previous_sequence):
    """Sequence policy after the source validates every public packet."""
    if type(previous_sequence) is not int or not 0 <= previous_sequence < 2**64:
        raise ValueError('previous sequence out of range')
    if len(session_words) != 4 or any(type(w) is not int or not 0 <= w < 2**64 for w in session_words):
        raise ValueError('session must have four canonical uint64 words')
    if previous_sequence+len(publics) >= 2**64:
        raise ValueError('sequence overflow')
    for j, public in enumerate(publics, 1):
        for i, expected in enumerate(session_words):
            value = public[f'session[{i}]']
            if value[0] != expected or any(value[1:]):
                raise ValueError('session mismatch')
        value = public['sequence[0]']
        if value[0] != previous_sequence+j or any(value[1:]):
            raise ValueError('sequence is not consecutive')
    return previous_sequence+len(publics)
