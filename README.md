# Palimpsest

High-arity lattice folding for Boolean quadratic relations.

Palimpsest combines an accumulator with multiple source instances under a shared lattice commitment. Its analysis connects bounded openings, source validity, and a matching bounded-depth history through an explicit knowledge extractor.

## Results

- High-arity folding with explicit challenge timing and norm bounds.
- Short-numerator comparison and scalar-bit recovery.
- Independent opening anchors with a linear Module-SIS reduction.
- A reviewed two-point extraction variant with weighted sampling coefficient `2 + 2k`.

The current prototype implements the three-point/weak-anchor baseline (coefficient 54 at `k=8`). The reviewed two-point variant has coefficient 18; its proof and sampling contract are included in the research notes.

## Repository

| Directory | Contents |
|---|---|
| [paper/](paper/research-notes.md) | Complete mathematical research notes |
| [docs/](docs/index.md) | Protocol, extraction, parameters, and scope |
| [prototype/](prototype/) | Python reference components |
| [tests/](tests/) | Local algebra and interface tests |
| [scripts/](scripts/) | Test runner and reproducible cost checks |
| [references/](references/README.md) | Reading list |

## Run

Requires Python 3.10 or later. The packaged checks use the standard library.

```sh
python scripts/run_tests.py
python scripts/extraction_costs.py
python scripts/check_random_stop_costs.py
python scripts/check_local_refinements.py
python scripts/verify_certificates.py
```

Start with the [protocol guide](docs/protocol.md), then the [extraction analysis](docs/extraction.md). See [scope](docs/scope.md) for the precise security model and the public-recovery baseline for the small example.

## Status

Research prototype and proof materials for an interactive, classical, bounded-depth model. No open-source license has been selected for this private repository.
