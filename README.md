# erdos-lean

A collection of Lean proofs for problems from [erdosproblems.com](https://www.erdosproblems.com).

Not every proof will be fully legitimate. Some might depend on extra axioms declared in the proof itself, or on mechanisms that expand Lean's trusted base. The table below shows the state of each problem and any axioms or trust extensions it relies on (state definitions live in [schema/problems.schema.json](schema/problems.schema.json)). Original sources are recorded in the `sources` field of [data/problems.yaml](data/problems.yaml).

For problem `N`, `problems/N/` contains:

- `ErdosN.lean`: the proof
- `lakefile.toml`: package `erdosN`, library `ErdosN`, Mathlib pinned to the catalog's revision
- `lean-toolchain`: the Lean version
- `lake-manifest.json`: dependency lockfile

Verify with:

```bash
cd problems/N
lake exe cache get
lake build
```

## Catalog

<!-- TABLE:START -->
139 proofs in the catalog (out of 186 Erdős problems with formalized solutions):
- 122 `complete`
- 3 `trust_extended`
- 14 `axiomatic`

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
| [202](https://www.erdosproblems.com/202) | `complete` | [problems/202/](problems/202/) | |
| [204](https://www.erdosproblems.com/204) | `complete` | [problems/204/](problems/204/) | |
| [205](https://www.erdosproblems.com/205) | `axiomatic` | [problems/205/](problems/205/) | assumes a result from [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/PrimeNumberTheoremAnd/Consequences.lean#L952) (`nth_prime_asymp`) |
| [206](https://www.erdosproblems.com/206) | `complete` | [problems/206/](problems/206/) | |
| [214](https://www.erdosproblems.com/214) | `complete` | [problems/214/](problems/214/) | |
| [221](https://www.erdosproblems.com/221) | `complete` | [problems/221/](problems/221/) | |
| [224](https://www.erdosproblems.com/224) | `complete` | [problems/224/](problems/224/) | |
| [226](https://www.erdosproblems.com/226) | `complete` | [problems/226/](problems/226/) | |
| [229](https://www.erdosproblems.com/229) | `complete` | [problems/229/](problems/229/) | |
| [231](https://www.erdosproblems.com/231) | `trust_extended` | [problems/231/](problems/231/) | uses `native_decide` |
| [237](https://www.erdosproblems.com/237) | `axiomatic` | [problems/237/](problems/237/) | assumes an intermediate result on page 7 in the proof of Theorem 1.1 of [Maynard](https://jayyhk.github.io/papers/maynard2015.pdf) (`maynard_prime_tuples`) |
| [246](https://www.erdosproblems.com/246) | `complete` | [problems/246/](problems/246/) | |
| [258](https://www.erdosproblems.com/258) | `axiomatic` | [problems/258/](problems/258/) | assumes Theorem 1.1 of [Tao–Teräväinen](https://jayyhk.github.io/papers/tao-teravainen2025.pdf) (`tao_teravainen`) |
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
| [392](https://www.erdosproblems.com/392) | `axiomatic` | [problems/392/](problems/392/) | assumes a result from [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/PrimeNumberTheoremAnd/Consequences.lean#L901) (`pi_alt'`) |
| [397](https://www.erdosproblems.com/397) | `complete` | [problems/397/](problems/397/) | |
| [399](https://www.erdosproblems.com/399) | `complete` | [problems/399/](problems/399/) | |
| [401](https://www.erdosproblems.com/401) | `complete` | [problems/401/](problems/401/) | |
| [418](https://www.erdosproblems.com/418) | `trust_extended` | [problems/418/](problems/418/) | uses `native_decide` |
| [419](https://www.erdosproblems.com/419) | `complete` | [problems/419/](problems/419/) | |
| [426](https://www.erdosproblems.com/426) | `complete` | [problems/426/](problems/426/) | |
| [427](https://www.erdosproblems.com/427) | `axiomatic` | [problems/427/](problems/427/) | assumes Theorem 1 of [Shiu](https://jayyhk.github.io/papers/shiu2000.pdf) (`shiu_consecutive_primes`) |
| [429](https://www.erdosproblems.com/429) | `complete` | [problems/429/](problems/429/) | |
| [433](https://www.erdosproblems.com/433) | `complete` | [problems/433/](problems/433/) | |
| [434](https://www.erdosproblems.com/434) | `complete` | [problems/434/](problems/434/) | |
| [435](https://www.erdosproblems.com/435) | `complete` | [problems/435/](problems/435/) | |
| [443](https://www.erdosproblems.com/443) | `complete` | [problems/443/](problems/443/) | |
| [447](https://www.erdosproblems.com/447) | `complete` | [problems/447/](problems/447/) | |
| [453](https://www.erdosproblems.com/453) | `complete` | [problems/453/](problems/453/) | |
| [457](https://www.erdosproblems.com/457) | `complete` | [problems/457/](problems/457/) | |
| [459](https://www.erdosproblems.com/459) | `complete` | [problems/459/](problems/459/) | |
| [476](https://www.erdosproblems.com/476) | `complete` | [problems/476/](problems/476/) | |
| [481](https://www.erdosproblems.com/481) | `complete` | [problems/481/](problems/481/) | |
| [484](https://www.erdosproblems.com/484) | `complete` | [problems/484/](problems/484/) | |
| [487](https://www.erdosproblems.com/487) | `complete` | [problems/487/](problems/487/) | |
| [490](https://www.erdosproblems.com/490) | `axiomatic` | [problems/490/](problems/490/) | assumes prime bounds of [Dusart](https://jayyhk.github.io/papers/dusart2018.pdf): Theorem 3.3 (`dusart_chebyshev`), equation 5.4 of Corollary 5.2 (`dusart_pi_lower`, `dusart_pi_upper`), and Theorem 5.9 (`dusart_mertens_product`) |
| [493](https://www.erdosproblems.com/493) | `complete` | [problems/493/](problems/493/) | |
| [497](https://www.erdosproblems.com/497) | `complete` | [problems/497/](problems/497/) | |
| [498](https://www.erdosproblems.com/498) | `complete` | [problems/498/](problems/498/) | |
| [499](https://www.erdosproblems.com/499) | `complete` | [problems/499/](problems/499/) | |
| [502](https://www.erdosproblems.com/502) | `complete` | [problems/502/](problems/502/) | |
| [505](https://www.erdosproblems.com/505) | `complete` | [problems/505/](problems/505/) | |
| [519](https://www.erdosproblems.com/519) | `complete` | [problems/519/](problems/519/) | |
| [532](https://www.erdosproblems.com/532) | `complete` | [problems/532/](problems/532/) | |
| [537](https://www.erdosproblems.com/537) | `complete` | [problems/537/](problems/537/) | |
| [540](https://www.erdosproblems.com/540) | `complete` | [problems/540/](problems/540/) | |
| [541](https://www.erdosproblems.com/541) | `complete` | [problems/541/](problems/541/) | |
| [582](https://www.erdosproblems.com/582) | `complete` | [problems/582/](problems/582/) | |
| [613](https://www.erdosproblems.com/613) | `complete` | [problems/613/](problems/613/) | |
| [618](https://www.erdosproblems.com/618) | `complete` | [problems/618/](problems/618/) | |
| [621](https://www.erdosproblems.com/621) | `complete` | [problems/621/](problems/621/) | |
| [639](https://www.erdosproblems.com/639) | `complete` | [problems/639/](problems/639/) | |
| [645](https://www.erdosproblems.com/645) | `complete` | [problems/645/](problems/645/) | |
| [646](https://www.erdosproblems.com/646) | `complete` | [problems/646/](problems/646/) | |
| [648](https://www.erdosproblems.com/648) | `axiomatic` | [problems/648/](problems/648/) | assumes a result from [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/PrimeNumberTheoremAnd/Consequences.lean#L875) (`pi_alt`) |
| [649](https://www.erdosproblems.com/649) | `complete` | [problems/649/](problems/649/) | |
| [650](https://www.erdosproblems.com/650) | `complete` | [problems/650/](problems/650/) | |
| [658](https://www.erdosproblems.com/658) | `axiomatic` | [problems/658/](problems/658/) | assumes Theorem 2.2 of [Solymosi](https://jayyhk.github.io/papers/solymosi2004.pdf) (`frankl_roedl_theorem`) |
| [659](https://www.erdosproblems.com/659) | `axiomatic` | [problems/659/](problems/659/) | assumes Theorems 1 and 2 on page 92 of [Bernays](https://jayyhk.github.io/papers/bernays1912.pdf) (`bernays`) |
| [666](https://www.erdosproblems.com/666) | `complete` | [problems/666/](problems/666/) | |
| [674](https://www.erdosproblems.com/674) | `complete` | [problems/674/](problems/674/) | |
| [678](https://www.erdosproblems.com/678) | `axiomatic` | [problems/678/](problems/678/) | assumes a result from [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/PrimeNumberTheoremAnd/Consequences.lean#L875) (`pi_alt`) |
| [692](https://www.erdosproblems.com/692) | `complete` | [problems/692/](problems/692/) | |
| [694](https://www.erdosproblems.com/694) | `axiomatic` | [problems/694/](problems/694/) | assumes equation 2 of [Linnik](https://jayyhk.github.io/papers/linnik1944.pdf) (`linnik_dvd`) |
| [696](https://www.erdosproblems.com/696) | `axiomatic` | [problems/696/](problems/696/) | assumes equation 22 of [Walfisz](https://jayyhk.github.io/papers/walfisz1936.pdf) (`siegel_walfisz`) |
| [698](https://www.erdosproblems.com/698) | `complete` | [problems/698/](problems/698/) | |
| [707](https://www.erdosproblems.com/707) | `complete` | [problems/707/](problems/707/) | |
| [728](https://www.erdosproblems.com/728) | `complete` | [problems/728/](problems/728/) | |
| [729](https://www.erdosproblems.com/729) | `complete` | [problems/729/](problems/729/) | |
| [741](https://www.erdosproblems.com/741) | `complete` | [problems/741/](problems/741/) | |
| [751](https://www.erdosproblems.com/751) | `complete` | [problems/751/](problems/751/) | |
| [753](https://www.erdosproblems.com/753) | `complete` | [problems/753/](problems/753/) | |
| [756](https://www.erdosproblems.com/756) | `complete` | [problems/756/](problems/756/) | |
| [760](https://www.erdosproblems.com/760) | `complete` | [problems/760/](problems/760/) | |
| [762](https://www.erdosproblems.com/762) | `complete` | [problems/762/](problems/762/) | |
| [765](https://www.erdosproblems.com/765) | `axiomatic` | [problems/765/](problems/765/) | assumes a result from [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/PrimeNumberTheoremAnd/Consequences.lean#L1555) (`prime_between`) |
| [775](https://www.erdosproblems.com/775) | `complete` | [problems/775/](problems/775/) | |
| [785](https://www.erdosproblems.com/785) | `complete` | [problems/785/](problems/785/) | |
| [794](https://www.erdosproblems.com/794) | `complete` | [problems/794/](problems/794/) | |
| [798](https://www.erdosproblems.com/798) | `complete` | [problems/798/](problems/798/) | |
| [818](https://www.erdosproblems.com/818) | `complete` | [problems/818/](problems/818/) | |
| [844](https://www.erdosproblems.com/844) | `complete` | [problems/844/](problems/844/) | |
| [845](https://www.erdosproblems.com/845) | `complete` | [problems/845/](problems/845/) | |
| [846](https://www.erdosproblems.com/846) | `complete` | [problems/846/](problems/846/) | |
| [862](https://www.erdosproblems.com/862) | `axiomatic` | [problems/862/](problems/862/) | assumes a result from [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/main/PrimeNumberTheoremAnd/Consequences.lean#L1555) (`prime_between`) |
| [867](https://www.erdosproblems.com/867) | `complete` | [problems/867/](problems/867/) | |
| [871](https://www.erdosproblems.com/871) | `complete` | [problems/871/](problems/871/) | |
| [897](https://www.erdosproblems.com/897) | `complete` | [problems/897/](problems/897/) | |

<!-- TABLE:END -->
