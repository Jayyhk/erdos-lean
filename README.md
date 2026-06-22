# erdos-lean

A collection of Lean proofs for problems from [erdosproblems.com](https://www.erdosproblems.com).

Each proof is self-contained. Every `ErdosN.lean` file's only import is `import Mathlib`, with no cross-references to other files in the repository. Additionally, some proofs depend on extra axioms declared in the proof itself, or on mechanisms that expand Lean's trusted base. The table below shows the state of each problem and any axioms or trust extensions it relies on (state definitions live in [schema/problems.schema.json](schema/problems.schema.json)). Original sources are recorded in the `sources` field of [data/problems.yaml](data/problems.yaml).

For problem `N`, `problems/N/` contains:

- `ErdosN.lean`: the proof
- `lakefile.toml`: package `erdosN`, Mathlib revision, library `ErdosN`
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
196 proofs in the catalog (out of 196 Erdős problems with formalized solutions):
- 179 `complete`
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
| [71](https://www.erdosproblems.com/71) | `complete` | [problems/71/](problems/71/) | |
| [90](https://www.erdosproblems.com/90) | `axiomatic` | [problems/90/](problems/90/) | assumes Theorem 3.9.7 of [Neukirch–Schmidt–Wingberg](https://jayyhk.github.io/papers/neukirch-schmidt-wingberg2008.pdf) (`golod_shafarevich_inequality`) and Theorem 5.1 of [Mayer](https://jayyhk.github.io/papers/mayer2015.pdf) (`shafarevich_relation_rank_bound`) |
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
| [205](https://www.erdosproblems.com/205) | `complete` | [problems/205/](problems/205/) | |
| [206](https://www.erdosproblems.com/206) | `complete` | [problems/206/](problems/206/) | |
| [209](https://www.erdosproblems.com/209) | `complete` | [problems/209/](problems/209/) | |
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
| [328](https://www.erdosproblems.com/328) | `complete` | [problems/328/](problems/328/) | |
| [330](https://www.erdosproblems.com/330) | `complete` | [problems/330/](problems/330/) | |
| [331](https://www.erdosproblems.com/331) | `complete` | [problems/331/](problems/331/) | |
| [333](https://www.erdosproblems.com/333) | `complete` | [problems/333/](problems/333/) | |
| [337](https://www.erdosproblems.com/337) | `complete` | [problems/337/](problems/337/) | |
| [347](https://www.erdosproblems.com/347) | `complete` | [problems/347/](problems/347/) | |
| [350](https://www.erdosproblems.com/350) | `complete` | [problems/350/](problems/350/) | |
| [351](https://www.erdosproblems.com/351) | `complete` | [problems/351/](problems/351/) | |
| [353](https://www.erdosproblems.com/353) | `complete` | [problems/353/](problems/353/) | |
| [355](https://www.erdosproblems.com/355) | `complete` | [problems/355/](problems/355/) | |
| [363](https://www.erdosproblems.com/363) | `complete` | [problems/363/](problems/363/) | |
| [369](https://www.erdosproblems.com/369) | `complete` | [problems/369/](problems/369/) | |
| [370](https://www.erdosproblems.com/370) | `complete` | [problems/370/](problems/370/) | |
| [379](https://www.erdosproblems.com/379) | `complete` | [problems/379/](problems/379/) | |
| [392](https://www.erdosproblems.com/392) | `complete` | [problems/392/](problems/392/) | |
| [397](https://www.erdosproblems.com/397) | `complete` | [problems/397/](problems/397/) | |
| [399](https://www.erdosproblems.com/399) | `complete` | [problems/399/](problems/399/) | |
| [401](https://www.erdosproblems.com/401) | `complete` | [problems/401/](problems/401/) | |
| [403](https://www.erdosproblems.com/403) | `complete` | [problems/403/](problems/403/) | |
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
| [464](https://www.erdosproblems.com/464) | `complete` | [problems/464/](problems/464/) | |
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
| [610](https://www.erdosproblems.com/610) | `axiomatic` | [problems/610/](problems/610/) | assumes Corollary 2 of [Joret–Micek–Reed–Smid](https://jayyhk.github.io/papers/joret-micek-reed-smid2021.pdf) (`jmrs_theorem`) and Theorem 1.1 of [Kim](https://jayyhk.github.io/papers/kim1995.pdf) (`kim_theorem`) |
| [613](https://www.erdosproblems.com/613) | `complete` | [problems/613/](problems/613/) | |
| [618](https://www.erdosproblems.com/618) | `complete` | [problems/618/](problems/618/) | |
| [621](https://www.erdosproblems.com/621) | `complete` | [problems/621/](problems/621/) | |
| [639](https://www.erdosproblems.com/639) | `complete` | [problems/639/](problems/639/) | |
| [645](https://www.erdosproblems.com/645) | `complete` | [problems/645/](problems/645/) | |
| [646](https://www.erdosproblems.com/646) | `complete` | [problems/646/](problems/646/) | |
| [648](https://www.erdosproblems.com/648) | `complete` | [problems/648/](problems/648/) | |
| [649](https://www.erdosproblems.com/649) | `complete` | [problems/649/](problems/649/) | |
| [650](https://www.erdosproblems.com/650) | `complete` | [problems/650/](problems/650/) | |
| [658](https://www.erdosproblems.com/658) | `axiomatic` | [problems/658/](problems/658/) | assumes Theorem 2.2 of [Solymosi](https://jayyhk.github.io/papers/solymosi2004.pdf) (`frankl_roedl_theorem`) |
| [659](https://www.erdosproblems.com/659) | `axiomatic` | [problems/659/](problems/659/) | assumes Theorems 1 and 2 on page 92 of [Bernays](https://jayyhk.github.io/papers/bernays1912.pdf) (`bernays`) |
| [666](https://www.erdosproblems.com/666) | `complete` | [problems/666/](problems/666/) | |
| [674](https://www.erdosproblems.com/674) | `complete` | [problems/674/](problems/674/) | |
| [678](https://www.erdosproblems.com/678) | `complete` | [problems/678/](problems/678/) | |
| [692](https://www.erdosproblems.com/692) | `complete` | [problems/692/](problems/692/) | |
| [694](https://www.erdosproblems.com/694) | `axiomatic` | [problems/694/](problems/694/) | assumes equation 2 of [Linnik](https://jayyhk.github.io/papers/linnik1944.pdf) (`linnik_dvd`) |
| [696](https://www.erdosproblems.com/696) | `axiomatic` | [problems/696/](problems/696/) | assumes equation 22 of [Walfisz](https://jayyhk.github.io/papers/walfisz1936.pdf) (`siegel_walfisz`) |
| [698](https://www.erdosproblems.com/698) | `complete` | [problems/698/](problems/698/) | |
| [707](https://www.erdosproblems.com/707) | `complete` | [problems/707/](problems/707/) | |
| [716](https://www.erdosproblems.com/716) | `complete` | [problems/716/](problems/716/) | |
| [728](https://www.erdosproblems.com/728) | `complete` | [problems/728/](problems/728/) | |
| [729](https://www.erdosproblems.com/729) | `complete` | [problems/729/](problems/729/) | |
| [741](https://www.erdosproblems.com/741) | `complete` | [problems/741/](problems/741/) | |
| [751](https://www.erdosproblems.com/751) | `complete` | [problems/751/](problems/751/) | |
| [753](https://www.erdosproblems.com/753) | `complete` | [problems/753/](problems/753/) | |
| [756](https://www.erdosproblems.com/756) | `complete` | [problems/756/](problems/756/) | |
| [760](https://www.erdosproblems.com/760) | `complete` | [problems/760/](problems/760/) | |
| [762](https://www.erdosproblems.com/762) | `complete` | [problems/762/](problems/762/) | |
| [765](https://www.erdosproblems.com/765) | `complete` | [problems/765/](problems/765/) | |
| [775](https://www.erdosproblems.com/775) | `complete` | [problems/775/](problems/775/) | |
| [785](https://www.erdosproblems.com/785) | `complete` | [problems/785/](problems/785/) | |
| [794](https://www.erdosproblems.com/794) | `complete` | [problems/794/](problems/794/) | |
| [798](https://www.erdosproblems.com/798) | `complete` | [problems/798/](problems/798/) | |
| [818](https://www.erdosproblems.com/818) | `complete` | [problems/818/](problems/818/) | |
| [844](https://www.erdosproblems.com/844) | `complete` | [problems/844/](problems/844/) | |
| [845](https://www.erdosproblems.com/845) | `complete` | [problems/845/](problems/845/) | |
| [846](https://www.erdosproblems.com/846) | `complete` | [problems/846/](problems/846/) | |
| [862](https://www.erdosproblems.com/862) | `complete` | [problems/862/](problems/862/) | |
| [867](https://www.erdosproblems.com/867) | `complete` | [problems/867/](problems/867/) | |
| [871](https://www.erdosproblems.com/871) | `complete` | [problems/871/](problems/871/) | |
| [897](https://www.erdosproblems.com/897) | `complete` | [problems/897/](problems/897/) | |
| [898](https://www.erdosproblems.com/898) | `complete` | [problems/898/](problems/898/) | |
| [904](https://www.erdosproblems.com/904) | `complete` | [problems/904/](problems/904/) | |
| [905](https://www.erdosproblems.com/905) | `complete` | [problems/905/](problems/905/) | |
| [907](https://www.erdosproblems.com/907) | `complete` | [problems/907/](problems/907/) | |
| [914](https://www.erdosproblems.com/914) | `complete` | [problems/914/](problems/914/) | |
| [923](https://www.erdosproblems.com/923) | `complete` | [problems/923/](problems/923/) | |
| [927](https://www.erdosproblems.com/927) | `complete` | [problems/927/](problems/927/) | |
| [947](https://www.erdosproblems.com/947) | `complete` | [problems/947/](problems/947/) | |
| [958](https://www.erdosproblems.com/958) | `complete` | [problems/958/](problems/958/) | |
| [964](https://www.erdosproblems.com/964) | `axiomatic` | [problems/964/](problems/964/) | assumes Theorem 1 of [Eberhard](https://jayyhk.github.io/papers/eberhard2025.pdf) (`goldston_graham_pintz_yildirim`) |
| [966](https://www.erdosproblems.com/966) | `complete` | [problems/966/](problems/966/) | |
| [967](https://www.erdosproblems.com/967) | `complete` | [problems/967/](problems/967/) | |
| [974](https://www.erdosproblems.com/974) | `complete` | [problems/974/](problems/974/) | |
| [990](https://www.erdosproblems.com/990) | `complete` | [problems/990/](problems/990/) | |
| [997](https://www.erdosproblems.com/997) | `axiomatic` | [problems/997/](problems/997/) | assumes Corollary 3 of [Banks–Freiberg–Turnage-Butterbaugh](https://jayyhk.github.io/papers/banks-freiberg-turnage-butterbaugh2015.pdf) (`maynardTaoBFT`) |
| [1000](https://www.erdosproblems.com/1000) | `complete` | [problems/1000/](problems/1000/) | |
| [1007](https://www.erdosproblems.com/1007) | `complete` | [problems/1007/](problems/1007/) | |
| [1008](https://www.erdosproblems.com/1008) | `complete` | [problems/1008/](problems/1008/) | |
| [1014](https://www.erdosproblems.com/1014) | `complete` | [problems/1014/](problems/1014/) | |
| [1022](https://www.erdosproblems.com/1022) | `complete` | [problems/1022/](problems/1022/) | |
| [1023](https://www.erdosproblems.com/1023) | `complete` | [problems/1023/](problems/1023/) | |
| [1026](https://www.erdosproblems.com/1026) | `complete` | [problems/1026/](problems/1026/) | |
| [1028](https://www.erdosproblems.com/1028) | `complete` | [problems/1028/](problems/1028/) | |
| [1034](https://www.erdosproblems.com/1034) | `complete` | [problems/1034/](problems/1034/) | |
| [1036](https://www.erdosproblems.com/1036) | `complete` | [problems/1036/](problems/1036/) | |
| [1037](https://www.erdosproblems.com/1037) | `complete` | [problems/1037/](problems/1037/) | |
| [1043](https://www.erdosproblems.com/1043) | `complete` | [problems/1043/](problems/1043/) | |
| [1044](https://www.erdosproblems.com/1044) | `complete` | [problems/1044/](problems/1044/) | |
| [1047](https://www.erdosproblems.com/1047) | `complete` | [problems/1047/](problems/1047/) | |
| [1048](https://www.erdosproblems.com/1048) | `complete` | [problems/1048/](problems/1048/) | |
| [1051](https://www.erdosproblems.com/1051) | `complete` | [problems/1051/](problems/1051/) | |
| [1067](https://www.erdosproblems.com/1067) | `complete` | [problems/1067/](problems/1067/) | |
| [1071](https://www.erdosproblems.com/1071) | `complete` | [problems/1071/](problems/1071/) | |
| [1080](https://www.erdosproblems.com/1080) | `complete` | [problems/1080/](problems/1080/) | |
| [1090](https://www.erdosproblems.com/1090) | `complete` | [problems/1090/](problems/1090/) | |
| [1098](https://www.erdosproblems.com/1098) | `complete` | [problems/1098/](problems/1098/) | |
| [1102](https://www.erdosproblems.com/1102) | `complete` | [problems/1102/](problems/1102/) | |
| [1121](https://www.erdosproblems.com/1121) | `complete` | [problems/1121/](problems/1121/) | |
| [1125](https://www.erdosproblems.com/1125) | `complete` | [problems/1125/](problems/1125/) | |
| [1126](https://www.erdosproblems.com/1126) | `complete` | [problems/1126/](problems/1126/) | |
| [1136](https://www.erdosproblems.com/1136) | `complete` | [problems/1136/](problems/1136/) | |
| [1138](https://www.erdosproblems.com/1138) | `complete` | [problems/1138/](problems/1138/) | |
| [1141](https://www.erdosproblems.com/1141) | `axiomatic` | [problems/1141/](problems/1141/) | assumes Theorem 1.3 of [Pollack](https://jayyhk.github.io/papers/pollack2017.pdf) (`pollack_theorem_1_3`) |
| [1148](https://www.erdosproblems.com/1148) | `axiomatic` | [problems/1148/](problems/1148/) | assumes an immediate consequence of Theorem 2.3 of [Einsiedler–Lindenstrauss–Michel–Venkatesh](https://jayyhk.github.io/papers/einsiedler-lindenstrauss-michel-venkatesh2012.pdf) (`theorem_2_3`) |
| [1190](https://www.erdosproblems.com/1190) | `complete` | [problems/1190/](problems/1190/) | |
| [1193](https://www.erdosproblems.com/1193) | `complete` | [problems/1193/](problems/1193/) | |
| [1196](https://www.erdosproblems.com/1196) | `complete` | [problems/1196/](problems/1196/) | |
| [1197](https://www.erdosproblems.com/1197) | `complete` | [problems/1197/](problems/1197/) | |

<!-- TABLE:END -->
