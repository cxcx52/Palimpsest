# Palimpsest

High-arity lattice folding for Boolean quadratic relations.

![Palimpsest folding overview](assets/palimpsest-overview.png)

Palimpsest folds an existing accumulator and multiple source instances into one reusable state. It combines canonical re-encoding and norm control with short-numerator comparison and independent opening anchors for knowledge extraction.

This repository contains Python reference components, reproducible calculations, and proofs for the interactive, bounded-depth protocol.

## Getting started

Python 3.10+ is required; there are no third-party dependencies. Run from the repository root:

```sh
python scripts/run_tests.py
```

The tests cover folding identities, challenge sampling, bit recovery, and extraction interfaces.

## Reproducing the calculations

| Command | Output |
|---|---|
| `python scripts/extraction_costs.py` | Extraction cost bounds across six arities |
| `python scripts/check_random_stop_costs.py` | Finite sampling laws and weighted cost checks |
| `python scripts/check_local_refinements.py` | Two-point sampling, bit recovery, and arithmetic cost checks |
| `python scripts/verify_certificates.py` | Primality and challenge-domain certificate checks |

The implemented extraction baseline uses three-point recovery and a weak comparison anchor. The two-point alternative is covered by the proofs and local checks; see the [extraction guide](docs/extraction.md).

## Code and documentation

- [prototype/](prototype/): folding algebra, samplers, and extraction components.
- [tests/](tests/): algebra and interface tests.
- [scripts/](scripts/): reproducible calculations and certificate checks.
- [docs/](docs/README.md): protocol, proofs, parameters, and model assumptions.

Start with the [protocol](docs/protocol.md). The [research notes](docs/research-notes.md) contain the full derivations; the [parameter guide](docs/parameters.md) connects them to the calculations above.

## License

[MIT](LICENSE).
