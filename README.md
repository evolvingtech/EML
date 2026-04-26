# EML: Lean 4 Formalization

A Lean 4 / Mathlib formalization of the core results of:
Andrzej Odrzywołek, *"All elementary functions from a single operator,"*
arXiv:2603.21852v2 (March 2026).

The specification of what is being formalized lives in [`docs/SPEC.md`](docs/SPEC.md).
Phase plans live in `docs/PHASE_*.md`. High-level orientation is in
[`docs/PROJECT_ORIENTATION.md`](docs/PROJECT_ORIENTATION.md).

## Build

```bash
lake exe cache get   # one-time, fetches precompiled Mathlib oleans
lake build
```

Toolchain: Lean `v4.28.0` (`lean-toolchain`) with Mathlib pinned to `v4.28.0`
in `lakefile.toml`.

## Status

Phase 0 (scaffolding + Mathlib API reconnaissance) — **complete**. See
[`docs/MATHLIB_RECON.md`](docs/MATHLIB_RECON.md) for the API surface report.

Phases 1–5: see `docs/SPEC.md` §7.

## License

Apache 2.0 — see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE). The papers in
[`papers/`](papers/) are third-party (Odrzywołek) and are not covered by this
repository's license.
