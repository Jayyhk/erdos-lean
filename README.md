# erdos-lean

A collection of Lean proofs for problems from [erdosproblems.com](https://www.erdosproblems.com).

The proofs here come from various sources and target various Lean toolchains and Mathlib revisions. Each proof is a single self-contained file that imports only Mathlib, with no dependencies between problems, and brings its own `lean-toolchain` / `lakefile.toml` and version info in the catalog — so any one of them builds and can be checked on its own.

Not every proof will be fully legitimate. Some might depend on `sorry`, on extra axioms declared in the proof itself, on unproven results dragged in as hypotheses, or on mechanisms that expand Lean's trusted base. The table below records every such qualification explicitly, with the catalog in [data/problems.yaml](data/problems.yaml) as the ground truth. Field definitions and the meaning of each `state` value / `trust_extensions` tag live in [schema/problems.schema.json](schema/problems.schema.json).

Files may be lightly modified from their original source — typically renaming the headline theorem to fit our `Erdos<N>.erdos_<N>` convention and wrapping in a `namespace Erdos<N>` block. Original sources are recorded in the `sources` field of [data/problems.yaml](data/problems.yaml).

## Conventions

For problem `N`, `problems/N/` contains:

- `ErdosN.lean` — the proof
- `lakefile.toml` — package `erdosN`, library `ErdosN`, Mathlib pinned to the catalog's revision
- `lean-toolchain` — the Lean version
- `lake-manifest.json` — dependency lockfile

Verify with:

```bash
cd problems/N
lake exe cache get   # download prebuilt Mathlib oleans (skip and it compiles Mathlib from source)
lake build
```

## Catalog

<!-- TABLE:START -->
80 proofs in the catalog (out of 1217 Erdős problems):
- 72 `complete`
- 3 `trust_extended`
- 5 `axiomatic`

| # | State | Lean | Notes |
|---|-------|------|-------|
| [16](https://www.erdosproblems.com/16) | `complete` | [problems/16/](problems/16/) | |
| [24](https://www.erdosproblems.com/24) | `complete` | [problems/24/](problems/24/) | |
| [26](https://www.erdosproblems.com/26) | `complete` | [problems/26/](problems/26/) | |
| [31](https://www.erdosproblems.com/31) | `complete` | [problems/31/](problems/31/) | |
| [34](https://www.erdosproblems.com/34) | `complete` | [problems/34/](problems/34/) | |
| [38](https://www.erdosproblems.com/38) | `complete` | [problems/38/](problems/38/) | |
| [42](https://www.erdosproblems.com/42) | `complete` | [problems/42/](problems/42/) | |
| [45](https://www.erdosproblems.com/45) | `complete` | [problems/45/](problems/45/) | |
| [46](https://www.erdosproblems.com/46) | `complete` | [problems/46/](problems/46/) | |
| [47](https://www.erdosproblems.com/47) | `complete` | [problems/47/](problems/47/) | |
| [56](https://www.erdosproblems.com/56) | `complete` | [problems/56/](problems/56/) | |
| [93](https://www.erdosproblems.com/93) | `complete` | [problems/93/](problems/93/) | |
| [94](https://www.erdosproblems.com/94) | `complete` | [problems/94/](problems/94/) | |
| [105](https://www.erdosproblems.com/105) | `complete` | [problems/105/](problems/105/) | |
| [115](https://www.erdosproblems.com/115) | `complete` | [problems/115/](problems/115/) | |
| [125](https://www.erdosproblems.com/125) | `complete` | [problems/125/](problems/125/) | |
| [134](https://www.erdosproblems.com/134) | `complete` | [problems/134/](problems/134/) | |
| [150](https://www.erdosproblems.com/150) | `complete` | [problems/150/](problems/150/) | |
| [154](https://www.erdosproblems.com/154) | `complete` | [problems/154/](problems/154/) | |
| [164](https://www.erdosproblems.com/164) | `complete` | [problems/164/](problems/164/) | |
| [178](https://www.erdosproblems.com/178) | `complete` | [problems/178/](problems/178/) | |
| [189](https://www.erdosproblems.com/189) | `complete` | [problems/189/](problems/189/) | |
| [192](https://www.erdosproblems.com/192) | `trust_extended` | [problems/192/](problems/192/) | uses `native_decide` |
| [194](https://www.erdosproblems.com/194) | `complete` | [problems/194/](problems/194/) | |
| [198](https://www.erdosproblems.com/198) | `complete` | [problems/198/](problems/198/) | |
| [199](https://www.erdosproblems.com/199) | `complete` | [problems/199/](problems/199/) | |
| [204](https://www.erdosproblems.com/204) | `complete` | [problems/204/](problems/204/) | |
| [205](https://www.erdosproblems.com/205) | `axiomatic` | [problems/205/](problems/205/) | assumes PNT (`nth_prime_asymp`) |
| [206](https://www.erdosproblems.com/206) | `complete` | [problems/206/](problems/206/) | |
| [214](https://www.erdosproblems.com/214) | `complete` | [problems/214/](problems/214/) | |
| [221](https://www.erdosproblems.com/221) | `complete` | [problems/221/](problems/221/) | |
| [224](https://www.erdosproblems.com/224) | `complete` | [problems/224/](problems/224/) | |
| [226](https://www.erdosproblems.com/226) | `complete` | [problems/226/](problems/226/) | |
| [229](https://www.erdosproblems.com/229) | `complete` | [problems/229/](problems/229/) | |
| [231](https://www.erdosproblems.com/231) | `trust_extended` | [problems/231/](problems/231/) | uses `native_decide` |
| [237](https://www.erdosproblems.com/237) | `axiomatic` | [problems/237/](problems/237/) | assumes Maynard–Tao (`maynard_tao`) |
| [246](https://www.erdosproblems.com/246) | `complete` | [problems/246/](problems/246/) | |
| [258](https://www.erdosproblems.com/258) | `axiomatic` | [problems/258/](problems/258/) | assumes Tao–Teräväinen (`tao_teravainen`) |
| [259](https://www.erdosproblems.com/259) | `complete` | [problems/259/](problems/259/) | |
| [268](https://www.erdosproblems.com/268) | `complete` | [problems/268/](problems/268/) | |
| [275](https://www.erdosproblems.com/275) | `complete` | [problems/275/](problems/275/) | |
| [280](https://www.erdosproblems.com/280) | `complete` | [problems/280/](problems/280/) | |
| [281](https://www.erdosproblems.com/281) | `complete` | [problems/281/](problems/281/) | |
| [283](https://www.erdosproblems.com/283) | `complete` | [problems/283/](problems/283/) | |
| [290](https://www.erdosproblems.com/290) | `complete` | [problems/290/](problems/290/) | |
| [296](https://www.erdosproblems.com/296) | `complete` | [problems/296/](problems/296/) | |
| [298](https://www.erdosproblems.com/298) | `complete` | [problems/298/](problems/298/) | |
| [299](https://www.erdosproblems.com/299) | `complete` | [problems/299/](problems/299/) | |
| [303](https://www.erdosproblems.com/303) | `complete` | [problems/303/](problems/303/) | |
| [314](https://www.erdosproblems.com/314) | `complete` | [problems/314/](problems/314/) | |
| [315](https://www.erdosproblems.com/315) | `complete` | [problems/315/](problems/315/) | |
| [316](https://www.erdosproblems.com/316) | `complete` | [problems/316/](problems/316/) | |
| [330](https://www.erdosproblems.com/330) | `complete` | [problems/330/](problems/330/) | |
| [331](https://www.erdosproblems.com/331) | `complete` | [problems/331/](problems/331/) | |
| [333](https://www.erdosproblems.com/333) | `complete` | [problems/333/](problems/333/) | |
| [337](https://www.erdosproblems.com/337) | `complete` | [problems/337/](problems/337/) | |
| [347](https://www.erdosproblems.com/347) | `complete` | [problems/347/](problems/347/) | |
| [350](https://www.erdosproblems.com/350) | `complete` | [problems/350/](problems/350/) | |
| [351](https://www.erdosproblems.com/351) | `complete` | [problems/351/](problems/351/) | |
| [355](https://www.erdosproblems.com/355) | `complete` | [problems/355/](problems/355/) | |
| [363](https://www.erdosproblems.com/363) | `complete` | [problems/363/](problems/363/) | |
| [369](https://www.erdosproblems.com/369) | `complete` | [problems/369/](problems/369/) | |
| [370](https://www.erdosproblems.com/370) | `complete` | [problems/370/](problems/370/) | |
| [379](https://www.erdosproblems.com/379) | `complete` | [problems/379/](problems/379/) | |
| [392](https://www.erdosproblems.com/392) | `axiomatic` | [problems/392/](problems/392/) | assumes PNT (`pi_alt'`) and a numerical log bound (`LogTables.log_7_lt`) |
| [397](https://www.erdosproblems.com/397) | `complete` | [problems/397/](problems/397/) | |
| [399](https://www.erdosproblems.com/399) | `complete` | [problems/399/](problems/399/) | |
| [401](https://www.erdosproblems.com/401) | `complete` | [problems/401/](problems/401/) | |
| [418](https://www.erdosproblems.com/418) | `trust_extended` | [problems/418/](problems/418/) | uses `native_decide` |
| [419](https://www.erdosproblems.com/419) | `complete` | [problems/419/](problems/419/) | |
| [426](https://www.erdosproblems.com/426) | `complete` | [problems/426/](problems/426/) | |
| [427](https://www.erdosproblems.com/427) | `axiomatic` | [problems/427/](problems/427/) | assumes Shiu's theorem (`shiu_consecutive_primes`) |
| [429](https://www.erdosproblems.com/429) | `complete` | [problems/429/](problems/429/) | |
| [433](https://www.erdosproblems.com/433) | `complete` | [problems/433/](problems/433/) | |
| [434](https://www.erdosproblems.com/434) | `complete` | [problems/434/](problems/434/) | |
| [435](https://www.erdosproblems.com/435) | `complete` | [problems/435/](problems/435/) | |
| [443](https://www.erdosproblems.com/443) | `complete` | [problems/443/](problems/443/) | |
| [447](https://www.erdosproblems.com/447) | `complete` | [problems/447/](problems/447/) | |
| [453](https://www.erdosproblems.com/453) | `complete` | [problems/453/](problems/453/) | |
| [457](https://www.erdosproblems.com/457) | `complete` | [problems/457/](problems/457/) | |

<!-- TABLE:END -->
