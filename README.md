# erdos-lean

A collection of Lean proofs for problems from [erdosproblems.com](https://www.erdosproblems.com).

The proofs here come from various sources and target various Lean toolchains and Mathlib revisions. This repo is **not** a single buildable Lake project — each proof carries its own version info in the catalog, and may bring its own `lean-toolchain` / `lakefile.toml` if you want to check it.

Files may be lightly modified from their original source — typically renaming the headline theorem to fit our `Erdos<N>.erdos_<N>` convention and wrapping in a `namespace Erdos<N>` block. Original sources are recorded in the catalog's `sources` field.

Not every proof will be fully legitimate. Some might depend on `sorry`, on extra axioms declared in the proof itself, on unproven results dragged in as hypotheses, or on mechanisms that expand Lean's trusted base. The table below records every such qualification explicitly, with the catalog in [data/problems.yaml](data/problems.yaml) as the ground truth. Field definitions and the meaning of each `state` value / `trust_extensions` tag live in [schema/problems.schema.json](schema/problems.schema.json).

## Conventions

For problem `N`, `problems/N/` contains:

- `ErdosN.lean` — the proof
- `lakefile.toml` — package `erdosN`, library `ErdosN`, Mathlib pinned to the catalog's revision
- `lean-toolchain` — the Lean version
- `lake-manifest.json` — dependency lockfile

Verify with `cd problems/N && lake build`.

## Catalog

<!-- TABLE:START -->
9 proofs in the catalog (out of 1217+ Erdős problems):
- 7 `complete`
- 2 `trust_extended`

| # | State | Proof | Notes |
|---|-------|-------|-------|
| [16](https://www.erdosproblems.com/16) | `complete` | [problems/16/](problems/16/) | |
| [24](https://www.erdosproblems.com/24) | `trust_extended` | [problems/24/](problems/24/) | uses `native_decide` |
| [26](https://www.erdosproblems.com/26) | `complete` | [problems/26/](problems/26/) | |
| [31](https://www.erdosproblems.com/31) | `complete` | [problems/31/](problems/31/) | |
| [34](https://www.erdosproblems.com/34) | `complete` | [problems/34/](problems/34/) | |
| [38](https://www.erdosproblems.com/38) | `complete` | [problems/38/](problems/38/) | |
| [42](https://www.erdosproblems.com/42) | `complete` | [problems/42/](problems/42/) | |
| [56](https://www.erdosproblems.com/56) | `trust_extended` | [problems/56/](problems/56/) | uses `native_decide` |
| [281](https://www.erdosproblems.com/281) | `complete` | [problems/281/](problems/281/) | |

<!-- TABLE:END -->
