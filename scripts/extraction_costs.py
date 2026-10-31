"""Exact extraction coefficients; no runtime or security-level benchmark.

Run from any directory. Prints JSON without changing historical ledgers.
The six arity points reuse the frozen q/N/D/s/source count.
"""
from fractions import Fraction as F
from math import comb, log2
import json


def log_fraction(x):
    return log2(x.numerator) - log2(x.denominator)


def fraction_record(x):
    return {"numerator": str(x.numerator), "denominator": str(x.denominator)}


def cost(R, H, local_blocks):
    return 1 + R**H + (R + local_blocks) * (R**H - 1) / (R - 1)


def point(k, D=128, weight=64):
    H, M = 512 // k, (1 << weight) * comb(D, weight)
    assert H*k == 512 and 1 <= weight <= D <= 256
    Q3, Q2 = F(2+9*k, 2), F(1+2*k)
    Q3s = 1 + k*(F(M, M-1) + F(M, M-2))
    Q2s = 1 + k*F(M, M-1)
    Rold, Rcap, Rstop = 4*Q3, Q3+Q2, Q3s+Q2s
    assert Rcap == F(4+13*k, 2)
    assert Rstop == 2 + k*(2*F(M, M-1) + F(M, M-2))
    assert Rstop > 2+3*k
    numerator_cap = H*(1023+20+4*k)
    numerator_stop = H*(1023+20+5*k)
    return {
        "k": k, "H": H, "D": D, "weight": weight, "M": str(M),
        "Q3_cap": fraction_record(Q3), "Q2_cap": fraction_record(Q2),
        "R_old": fraction_record(Rold), "R_cap": fraction_record(Rcap),
        "Q3_stop": fraction_record(Q3s), "Q2_stop": fraction_record(Q2s),
        "R_stop": fraction_record(Rstop),
        "stat_numerator_cap": numerator_cap,
        "stat_numerator_stop": numerator_stop,
        "stat_bits_cap": log2(M)-log2(numerator_cap),
        "stat_bits_stop": log2(M)-log2(numerator_stop),
        "log2_RH_old": H*log_fraction(Rold),
        "log2_RH_cap": H*log_fraction(Rcap),
        "log2_RH_stop": H*log_fraction(Rstop),
        "log2_U_over_common_B0_old": log_fraction(cost(Rold,H,13)),
        "log2_U_over_common_B0_cap": log_fraction(cost(Rcap,H,9)),
        "log2_U_over_common_B0_stop": log_fraction(cost(Rstop,H,9)),
        "SIS_radius": 8*weight*(2*H-1)*k,
        "honest_session_bytes": 16809472 + H*(10+k*(k+1)//2)*8192
            + H*(k+2)*((D+weight+7)//8) + (806*D*11+7)//8,
    }


def main():
    rows = [point(k) for k in (2,4,8,16,32,64)]
    d = rows[2]
    assert d["R_old"] == fraction_record(F(148))
    assert d["R_cap"] == fraction_record(F(54))
    assert (d["stat_numerator_cap"],d["stat_numerator_stop"]) == (68800,69312)
    assert d["honest_session_bytes"] == 41083936 and d["SIS_radius"] == 520192
    print(json.dumps({
        "schema": "palimpsest-anchor-cost-v1",
        "default": "cap_M_fused_strong3_weak2",
        "common_B0_contract": "Known bound covering all named old and new local blocks, terminal, init/output; not measured time.",
        "local_blocks_old": 13, "local_blocks_fused": 9,
        "note": "Exact coefficients are rational strings; logs are display approximations. Optional stop R is strictly greater than 2+3k.",
        "arity_points": rows,
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
