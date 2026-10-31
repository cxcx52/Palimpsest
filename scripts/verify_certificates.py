"""Verify the packaged commitment/semantic prime certificates; print JSON."""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from prototype.prime_certificate import verify


def main():
    values = {}
    for name in ('commitment', 'semantic'):
        path = ROOT / 'prototype' / 'data' / (name + '_prime_certificate.json')
        cert = json.loads(path.read_text(encoding='utf-8'))
        if not verify(cert):
            raise ValueError('invalid ' + name + ' prime certificate')
        values[name] = cert['n']
    q = values['commitment']
    if q % 1024 != 965 or pow(q, 256, 1024) != 1 or pow(q, 128, 1024) == 1:
        raise ValueError('unexpected cyclotomic factor degree')
    if values['semantic'] != 2**51 - 165:
        raise ValueError('unexpected source field')
    print(json.dumps({'status': 'PASS', 'primes': values,
                      'cyclotomic_factor_degree': 256,
                      'scope': 'Primality and factor degree, not computational security.'},
                     indent=2))


if __name__ == '__main__':
    main()
