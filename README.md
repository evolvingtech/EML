# EML

Formalization and tooling for the EML operator and related elementary-function
constructions.

This repository contains a [Lean 4](https://lean-lang.org/) /
[Mathlib](https://leanprover-community.github.io/) formalization of the
core mathematical results concerning the **EML operator**

$$\mathrm{eml}(x, y) \;=\; \exp(x) \;-\; \mathrm{Log}(y),$$

a single binary operator on the complex plane that — together with the
constant $1$ — is sufficient to express all standard elementary functions
on appropriate principal-branch domains. This is a continuous-function
analogue of the Sheffer/NAND completeness result for Boolean logic.

## Status

**Phase 0 (scaffolding + Mathlib API reconnaissance) — complete.**
The build infrastructure is in place, Mathlib is pinned to v4.28.0, and the
Mathlib API surface required for Phases 1–3 has been verified. See
`docs/MATHLIB_RECON.md` for the reconnaissance report.

The work is structured into phases. Subsequent phases formalize the
EML operator's denotation, the three core lemmas, the corollary
identities for arithmetic and basic transcendentals, and (optionally)
the full thirteen standard transcendental functions and the formal
completeness theorem. See `docs/SPEC.md` for the full specification.

## Build

This project requires Lean 4 (toolchain `leanprover/lean4:v4.28.0`,
managed by [`elan`](https://github.com/leanprover/elan)) and Mathlib
v4.28.0.

```bash
lake exe cache get   # one-time, downloads precompiled Mathlib .olean files
lake build           # builds the project
```

The first `lake exe cache get` is multi-gigabyte and takes several
minutes; subsequent builds are fast.

## Repository structure

```
EML/
├── EML.lean                     # top-level entry point
├── EML/
│   ├── Syntax.lean              # EMLTree inductive type
│   ├── Denote.lean              # denotation function and the eml operator
│   ├── Basic.lean               # basic auxiliary lemmas
│   ├── Lemma1.lean              # eml(z, 1) = exp(z)
│   ├── Lemma2.lean              # the reconstructed logarithm L
│   ├── Lemma3.lean              # subtraction via eml
│   ├── Corollary4/              # arithmetic and basic transcendentals
│   └── Transcendentals/         # full transcendental function bootstrap
├── docs/
│   ├── SPEC.md                  # canonical specification
│   ├── MATHLIB_RECON.md         # Mathlib API reconnaissance report
│   ├── PROJECT_ORIENTATION.md   # high-level orientation
│   └── PHASE_*.md               # per-phase implementation briefs
├── lakefile.toml                # Lake build configuration
└── lean-toolchain               # pinned Lean version
```

## References and acknowledgements

The mathematical results formalized here are due to Andrzej Odrzywołek:

> Andrzej Odrzywołek,
> *"All elementary functions from a single operator,"*
> arXiv:2603.21852v2 (March 2026).
> Available at: <https://arxiv.org/abs/2603.21852>

The paper introduces the EML operator, proves its completeness for the
elementary functions, presents a numerical search procedure that
discovers it, and explores related variant operators. **All credit for
the underlying mathematics goes to Odrzywołek.** This repository is an
independent formalization effort and does not reproduce the paper or
its supplementary materials; readers are referred to the arXiv link
above.

## License

Licensed under the Apache License, Version 2.0. See `LICENSE` and
`NOTICE` for full details.

## Contributing

This is an active research-formalization project. Issues and pull
requests are welcome but please open an issue first to discuss any
substantive changes — the phase-gated structure means changes need to
fit within the current phase's scope.
