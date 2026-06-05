# Plan: Discharge the `brun_titchmarsh` axiom in problem 696

## Status (current)

| Piece | State |
|---|---|
| `SelbergSieve4` vendored from lean-pool | ✅ Done, builds |
| `Mertens` block vendored from problem 694 | ✅ Done, builds |
| `Erdos696Common.lean` (extracted `piMod` to break import cycle) | ✅ Done |
| `BrunTitchmarshAP.lean` (1421 lines, all proofs no sorries) | ✅ Done, builds |
| ── `mertens_restricted` | ✅ |
| ── `primeInterSieveAP`, `primesBetween_AP` | ✅ |
| ── `joint_iff_crt`, `multSum_AP_eq`, `rem_AP_eq`, `abs_rem_AP_le` | ✅ |
| ── `primeSieve_rem_sum_AP_le` | ✅ |
| ── `boundingSum_AP_ge` (with hypothesis `16q⁴ ≤ z`) | ✅ |
| ── `siftedSum_AP_le`, `primesBetween_AP_le_siftedSum_add`, `primesBetween_AP_le` | ✅ |
| ── `piMod_le_via_primesBetween_AP` | ✅ |
| ── `brun_titchmarsh_large` (BT for `t ≥ 256·q⁹`) | ✅ |
| Replace `axiom brun_titchmarsh` in `Erdos696.lean` | ⚠️ Started, downstream broken |
| Patch downstream consumers | ⏳ TODO |

## Current obstruction (path 2: strengthened-hypothesis variant)

`brun_titchmarsh_large` proves BT for `t ≥ 256·q⁹` only. The downstream code in
`Erdos696.lean` was written assuming BT for all `t ≥ 2q`. After replacing the
axiom with this weakened theorem, the call site at line 4923 (inside
`bt_reciprocal_AP_tail`) fails because it tries to apply BT at `t ≥ 2p` but the
new theorem only covers `t ≥ 256p⁹`.

The full BT theorem (with `t ≥ 2q`) is provably the textbook statement but
requires Möbius inversion + Mertens-type bound `q/φ(q) = O(log log q)`, neither
of which is in Mathlib in usable form. Estimated cost: multi-day.

The **path-2 fix** strengthens the call site's hypothesis to match the new BT
and proves the missing chunk via a trivial bound that fits the target form.
Detailed analysis below.

## Path 2 fix: downstream surgery

### Dependency graph of BT consumers in `Erdos696.lean`

```
brun_titchmarsh  (line 3301, now: ∀ t ≥ 256·q⁹, …)
│
├── bt_reciprocal_AP_tail  (line 4882)   ◄── used externally at line 7238
│   └── (private helpers, all only used here):
│       ├── hBTp  (line 4917, internal)
│       ├── high_AP_sum_le_explicit  (line 4666)
│       ├── tail_integral_le  (line 4575)
│       └── explicit_tail_bound  (line 4759)
│
└── brun_titchmarsh_for_prime  (line 7071) ◄── DEAD CODE, 0 external uses
```

So **only one external consumer touch point** (line 7238) and three private
helper lemmas to update. Plus a one-line edit to the dead-code lemma.

### The mathematical fix

`bt_reciprocal_AP_tail` claims:
```
∑_{q prime, q ≡ 1 (mod p), 2p < q ≤ Q(p)}  1/q  ≤  C · (log p / p + 1/(log p)²)
```
where `Q(p) = exp(exp(p/(log p)²))`.

**Split the sum at `256p⁹`:**

1. **Chunk** `2p < q ≤ 256p⁹` — bounded *without* BT, by:
   ```
   ∑_{q ≡ 1 (mod p), 2p < q ≤ 256p⁹} 1/q  ≤  (1/p) · ∑_{k=2}^{256p⁸} 1/k
                                          ≤  (log(256p⁸))/p
                                          ≤  (log 256 + 8 log p)/p
                                          ≤  9·log p / p     (for p ≥ 2)
   ```
   This fits the target form `C · (log p / p + …)` by bumping `C` ↑ by 9.

2. **Tail** `256p⁹ < q ≤ Q(p)` — apply the existing partial-summation argument
   with `brun_titchmarsh_large` providing BT throughout (since every `t` in
   this range satisfies `t ≥ 256p⁹`).

3. **Verify** `Q(p) ≥ 256p⁹` (needed to make the tail non-empty). Easy:
   `Q(2) = exp(exp(4.16)) ≈ exp(64) ≈ 6×10²⁷ >> 256·2⁹ = 131072`.
   For `p ≥ 2`, `Q(p)` grows exponentially while `256p⁹` grows polynomially.

### Concrete TODO list

1. **Strengthen the three helper-lemma signatures** (lines 4575, 4666, 4759) to
   take `256·p⁹ ≤ Q` and `∀ t ≥ 256·p⁹, …` everywhere. Update their sum/integral
   ranges from `(2p, Q]` to `(256p⁹, Q]`. Their internal proofs propagate
   mechanically since they only apply `hBT` at points in the new range.

2. **Add a chunk lemma** to `Erdos696.lean` near line 4900:
   ```lean
   private lemma chunk_AP_sum_le (p : ℕ) (hp : p.Prime) :
       ∑ q ∈ Finset.filter
           (fun q => q.Prime ∧ q % p = 1 ∧ (2 * p : ℝ) < (q : ℝ)
                     ∧ (q : ℝ) ≤ 256 * (p : ℝ)^9)
           (Finset.Iic ⌊(256 : ℝ) * (p : ℝ)^9⌋₊),
         (1 : ℝ) / (q : ℝ)
       ≤ 9 * Real.log p / p
   ```
   Proof: drop primality (upper bound by all integers ≡ 1 mod p), substitute
   `q = kp + 1`, sum `1/(kp+1) ≤ 1/(kp)`, harmonic sum bound.

3. **Restructure `bt_reciprocal_AP_tail`**:
   - Verify `256·p⁹ ≤ Q(p)`.
   - Split the original sum at `256p⁹`.
   - Bound chunk via the new lemma; bound tail via strengthened
     `high_AP_sum_le_explicit`.
   - Combine: new constant `C := old_C + 9` (or similar absorption).

4. **Weaken `brun_titchmarsh_for_prime`'s statement** (line 7071) from
   `∀ t ≥ 2p` to `∀ t ≥ 256·p⁹`. Single-line edit; no downstream breakage
   because it has zero callers.

5. **Update axiom catalog**:
   - `data/problems.yaml`: remove `brun_titchmarsh` from problem 696's
     `extra_axioms`.
   - `README.md`: remove the `brun_titchmarsh` mention from problem 696's note.

6. **Verify** with `#print axioms Erdos696.erdos_696`: should no longer list
   `Erdos696.brun_titchmarsh`. Only `Erdos696.siegel_walfisz` remains (plus
   the standard `propext, Classical.choice, Quot.sound`).

### Budget

| Task | Est. lines |
|---|---|
| 1. Strengthen 3 helper-lemma signatures + their proofs | ~80 lines edited |
| 2. Add `chunk_AP_sum_le` lemma | ~60 lines new |
| 3. Restructure `bt_reciprocal_AP_tail` (sum-split + recombine) | ~100 lines edited |
| 4. Weaken `brun_titchmarsh_for_prime` | 1 line |
| 5. Catalog updates | 2 lines (yaml + readme) |

Total: ~250 lines of localized surgery, all within `Erdos696.lean`. No new
mathematical content beyond the chunk bound (which is a routine harmonic-sum
estimate).

## Why path 1 (full BT with `t ≥ 2q`) was rejected

The textbook BT proof works for all `t ≥ 2q` but requires:
- Möbius inversion on coprime harmonic sums: `∑_{m ≤ N, gcd(m,q)=1} 1/m = ∑_{d|q} μ(d)/d · H_{N/d} ≥ (φ(q)/q) · log N - C · log log q`.
- The Mertens-type bound `q/φ(q) ≤ C · log log q` (controls the additive error in the above).

Neither lemma is in Mathlib. Formalizing them is multi-day analytic-number-
theory work. The path-2 fix avoids both by using the existing
`boundingSum_AP_ge` (which requires `16q⁴ ≤ z`, equivalently `t ≥ 256q⁹` for
`z = √(t/q)`) and absorbing the small-`t` chunk into the target form.

## References

- Iwaniec & Kowalski, *Analytic Number Theory*, AMS Colloq. 53, §6.6 (full BT
  proof — what path 1 would formalize).
- `BrunTitchmarshAP.lean` (the existing 1421-line proof of `brun_titchmarsh_large`).
- `Erdos696.lean` lines 4575-4940 (the helper chain that needs restructuring).

## How larger projects do this

Real Lean projects (PFR, Liquid Tensor Experiment, FLT, Carleson) use
[leanblueprint](https://github.com/PatrickMassot/leanblueprint): a LaTeX
package where every theorem is a `\begin{theorem}\lean{name}\uses{...}\end{theorem}`
node. A script then renders an interactive web DAG showing which nodes are
proven (by checking the `name` exists in Lean as a theorem) vs. pending,
plus dependency arrows. Worth adopting if this directory ever grows beyond
~5 axioms to discharge; until then, a plain markdown plan like this is the
right amount of structure.
