# erdos-lean

A collection of Lean proofs for problems from [erdosproblems.com](https://www.erdosproblems.com).

The proofs here come from various sources and target various Lean toolchains and Mathlib revisions. This repo is **not** a single buildable Lake project — each proof carries its own version info in the catalog, and may bring its own `lean-toolchain` / `lakefile.toml` if you want to check it.

Not every proof will be fully legitimate. Some might depend on `sorry`, on extra axioms declared in the proof itself, on unproven results dragged in as hypotheses, or on mechanisms that expand Lean's trusted base. The table below records every such qualification explicitly, with the catalog in [data/problems.yaml](data/problems.yaml) as the ground truth. Field definitions and the meaning of each `state` value / `trust_extensions` tag live in [schema/problems.schema.json](schema/problems.schema.json).

## Catalog

<!-- TABLE:START -->
0 proofs in the catalog (out of 1217+ Erdős problems).

| # | State | Proof | Lean | Notes |
|---|-------|-------|------|-------|

<!-- TABLE:END -->
