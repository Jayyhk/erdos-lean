import Mathlib

namespace Erdos1050

/-
# Erdős Problem 1050

Is
$$\sum_{n=1}^\infty \frac{1}{2^n - 3}$$
irrational?

The answer is **yes**. Erdős [Er48] proved that $\sum 1/(2^n-1)$ is irrational and noted
[Er88c] that $\sum 1/(2^n+t)$ should be transcendental for every integer $t \neq 0$;
irrationality was proved by Borwein [Bo91], who more generally showed that
$\sum_{n\ge1} 1/(q^n+r)$ is irrational for any integer $q \ge 2$ and rational $r \neq 0$
distinct from $-q^n$. Problem 1050 is the case $q = 2$, $r = -3$.

Formalised by Trevor Morris in `gotrevor/lean-gallery`; the ten modules forming the
closure of `erdos_1050` are flattened here in dependency order. The general Borwein
theorem, the Lambert-series variant and the (open) transcendence conjecture live in
further modules upstream and are not part of this closure.

`erdos_1050` states the series exactly as posed, encoded over `ℕ` by the reindex
`n ↦ n + 1`, so the tsum's `n = 0` summand is the source's first term `1/(2^1 - 3) = -1`.
The proof engine works with the positive-denominator tail `S = ∑_{n≥0} 1/(2^(n+2) - 3)`;
`Sliteral_eq` proves the reduction rather than assuming it.
-/

/-! ### Upstream module `Basic.lean` -/

section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-!
# Erdős #1050 — irrationality of `∑ 1/(2ⁿ − 3)`

Erdős & Graham asked whether `∑_{n} 1/(2ⁿ − 3)` is irrational. The answer is **yes**, by
P. B. Borwein, *On the irrationality of `∑ 1/(qⁿ + r)`*, J. Number Theory **37** (1991) 253–259;
cleaner self-contained proof in P. B. Borwein, *On the irrationality of certain series*,
Math. Proc. Camb. Phil. Soc. **112** (1992) 141–146 (free: cecm.sfu.ca/~pborwein/PAPERS/P59.pdf).

Method (no transcendence theory): explicit Padé / rational approximants `pₙ/qₙ` to the series with
integer numerators/denominators and a super-exponential error bound `0 < |qₙ·S − pₙ| → 0`, feeding the
classical integer-approximation irrationality criterion (`Criterion.lean`). The contour integral in the
paper is **avoided** — the approximants are reconstructed as explicit finite sums (`Approximants.lean`).

Problem page: <https://www.erdosproblems.com/1050>.
-/

open scoped BigOperators

/-- The Erdős–Graham series `∑_{n≥0} 1/(2^(n+2) − 3)`.

Index base note: every denominator `2^(n+2) − 3 ≥ 1` is positive, so all terms are well-defined
positive reals. The problem is usually written `∑ 1/(2ⁿ − 3)`; the low terms (`n=0,1` give `−1/2, −1`)
are rational, and **adding/removing finitely many rationals does not change irrationality**, so the
index base is a free, faithfulness-irrelevant choice. We start at `n+2` to keep every term positive. -/
noncomputable def S : ℝ := ∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 2) - 3)

/-- The tail series defining `S` is summable: every term `1/(2^(n+2)−3)` is dominated by `2^{-n}`.
(Auto-formalized by Harmonic's Aristotle, ported here and verified kernel-clean.) -/
lemma S_summable : Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 2) - 3)) := by
  ring_nf
  exact Summable.of_nonneg_of_le
    (fun n => inv_nonneg.mpr <| by
      nlinarith [show (2 : ℝ) ^ n ≥ 1 by exact one_le_pow₀ (by norm_num)])
    (fun n => by
      rw [inv_le_comm₀] <;> norm_num <;> induction n <;> norm_num [pow_succ'] at * <;> nlinarith)
    summable_geometric_two

/- The headline theorem `erdos_1050 : Irrational S` is proved in `Approximants.lean` (it needs the
proof engine); `Statement.lean` re-exports it as the audit surface. -/

end

/-! ### Upstream module `Criterion.lean` -/

section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-!
# The integer-approximation irrationality criterion

The single reusable lemma the whole proof feeds: a real `x` is irrational if there are integer
sequences `aₙ, bₙ` with `bₙ·x − aₙ ≠ 0` for all `n` and `bₙ·x − aₙ → 0`. (Hardy–Wright Thm 186 /
Van Assche Lemma 5.1.) The standard one-line argument: if `x = p/q` were rational, then
`bₙ·x − aₙ = (bₙ·p − aₙ·q)/q` is a nonzero rational of absolute value `≥ 1/q`, contradicting `→ 0`.

⚠️ Check whether mathlib already has this (it has `Liouville` machinery in
`Mathlib.NumberTheory.Liouville.*` and `Irrational` API). If a close form exists, delegate to it; this
file is a ~20-line standalone fallback otherwise.
-/

open Filter Topology

/-- Irrationality from integer approximations with nonzero, vanishing error.
If `b n * x - a n ≠ 0` for all `n` and `(fun n => b n * x - a n) → 0`, then `x` is irrational.

Proof: if `x = r` were rational with denominator `d = r.den`, then `d·(bₙ·x − aₙ) =
bₙ·r.num − d·aₙ` is a nonzero integer, hence has absolute value `≥ 1`, so `|bₙ·x − aₙ| ≥ 1/d > 0`
for all `n` — contradicting `bₙ·x − aₙ → 0`. -/
theorem irrational_of_intApprox (x : ℝ) (a b : ℕ → ℤ)
    (hne : ∀ n, (b n : ℝ) * x - a n ≠ 0)
    (hlim : Tendsto (fun n => (b n : ℝ) * x - a n) atTop (𝓝 0)) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  have hden : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast Rat.den_pos r
  have hdne : (r.den : ℝ) ≠ 0 := ne_of_gt hden
  have hrd : (r.den : ℝ) * (r : ℝ) = (r.num : ℝ) := by
    rw [Rat.cast_def]; field_simp
  -- Lower bound: `|bₙ·r − aₙ| ≥ 1/r.den` for every `n`.
  have hlb : ∀ n, 1 / (r.den : ℝ) ≤ |(b n : ℝ) * (r : ℝ) - (a n : ℝ)| := by
    intro n
    have hcast : ((b n * r.num - r.den * a n : ℤ) : ℝ)
        = (r.den : ℝ) * ((b n : ℝ) * (r : ℝ) - (a n : ℝ)) := by
      push_cast
      linear_combination (-(b n : ℝ)) * hrd
    have hcne : (b n * r.num - r.den * a n : ℤ) ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero] at hcast
      rcases mul_eq_zero.mp hcast.symm with h | h
      · exact hdne h
      · exact hne n h
    have h1 : (1 : ℝ) ≤ |((b n * r.num - r.den * a n : ℤ) : ℝ)| := by
      have hz : (1 : ℤ) ≤ |b n * r.num - r.den * a n| := Int.one_le_abs hcne
      calc (1 : ℝ) ≤ ((|b n * r.num - r.den * a n| : ℤ) : ℝ) := by exact_mod_cast hz
        _ = |((b n * r.num - r.den * a n : ℤ) : ℝ)| := by rw [Int.cast_abs]
    rw [hcast, abs_mul, abs_of_pos hden] at h1
    rw [div_le_iff₀ hden]
    nlinarith [h1]
  -- The error tends to `0` in absolute value, contradicting the constant lower bound.
  have habs : Tendsto (fun n => |(b n : ℝ) * (r : ℝ) - (a n : ℝ)|) atTop (𝓝 0) := by
    simpa using hlim.abs
  have hle : 1 / (r.den : ℝ) ≤ 0 := ge_of_tendsto' habs hlb
  have hpos : (0 : ℝ) < 1 / (r.den : ℝ) := by positivity
  linarith

end

/-! ### Upstream module `QBinom.lean` -/

section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-!
# Gaussian (q-)binomial coefficients — toward Borwein Lemma 2

The denominator polynomial `pₙ(c,q)` of Borwein's Padé approximants is built from Gaussian binomial
coefficients `[n choose k]_q`, and its **integrality** (Lemma 2) rests on the **Cauchy q-binomial
theorem**. mathlib has no q-binomial machinery, so we build the minimum here.

`qBin q n k` is defined by the q-Pascal recurrence, so it is *manifestly* an integer polynomial in
`q` (a `CommRing` element); no division. The Cauchy theorem is the engine that makes `pₙ ∈ ℤ[c,q]`.

This is a prerequisite for discharging the `borwein_integrality` assumption (O1).
-/


/-- Gaussian binomial coefficient `[n choose k]_q`, via the q-Pascal recurrence
`[n+1, k+1]_q = q^{k+1}·[n, k+1]_q + [n, k]_q`. Integer-polynomial in `q` by construction. -/
def qBin {R : Type*} [CommRing R] (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => q ^ (k + 1) * qBin q n (k + 1) + qBin q n k

@[simp] lemma qBin_zero_right {R : Type*} [CommRing R] (q : R) (n : ℕ) : qBin q n 0 = 1 := by
  cases n <;> rfl

@[simp] lemma qBin_zero_succ {R : Type*} [CommRing R] (q : R) (k : ℕ) : qBin q 0 (k + 1) = 0 := rfl

lemma qBin_succ_succ {R : Type*} [CommRing R] (q : R) (n k : ℕ) :
    qBin q (n + 1) (k + 1) = q ^ (k + 1) * qBin q n (k + 1) + qBin q n k := rfl

/-- The Gaussian binomial vanishes above the diagonal: `[n,k]_q = 0` for `k > n`. -/
lemma qBin_eq_zero_of_lt {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    ∀ k, n < k → qBin q n k = 0 := by
  induction n with
  | zero => intro k hk; cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih => intro k hk; cases k with
    | zero => omega
    | succ k => rw [qBin_succ_succ, ih (k + 1) (by omega), ih k (by omega), mul_zero, add_zero]

/-- The Gaussian binomial on the diagonal is `1`: `[n,n]_q = 1`. -/
@[simp] lemma qBin_self {R : Type*} [CommRing R] (q : R) (n : ℕ) : qBin q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [qBin_succ_succ, qBin_eq_zero_of_lt q n (n + 1) (by omega), mul_zero,
      zero_add, ih]

/-- The q-integer: `[n,1]_q = 1 + q + ⋯ + q^{n-1}`. -/
lemma qBin_one {R : Type*} [CommRing R] (q : R) (n : ℕ) :
    qBin q n 1 = ∑ i ∈ Finset.range n, q ^ i := by
  induction n with
  | zero => simp [qBin]
  | succ n ih =>
    rw [show (1 : ℕ) = 0 + 1 from rfl, qBin_succ_succ, qBin_zero_right, ih, pow_one,
      Finset.sum_range_succ', pow_zero, Finset.mul_sum]
    simp [pow_succ, mul_comm]

/-- `qBin` commutes with ring homomorphisms. In particular `qBin (2:ℝ) n k` is the integer
`qBin (2:ℤ) n k` cast to `ℝ` — the bridge that makes Borwein's `pₙ(c,q)` integer-valued at `q = 2`. -/
lemma qBin_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : R) :
    ∀ n k, qBin (f q) n k = f (qBin q n k)
  | _, 0 => by rw [qBin_zero_right, qBin_zero_right, map_one]
  | 0, _ + 1 => by rw [qBin_zero_succ, qBin_zero_succ, map_zero]
  | n + 1, k + 1 => by
      rw [qBin_succ_succ, qBin_succ_succ, qBin_map f q n (k + 1), qBin_map f q n k,
        map_add, map_mul, map_pow]

/-- Triangular-number identity in `ℕ`: `k*(k-1)/2 + k = (k+1)*((k+1)-1)/2`. -/
private lemma cauchy_tri_succ (k : ℕ) :
    k * (k - 1) / 2 + k = (k + 1) * ((k + 1) - 1) / 2 := by
  rcases k with _ | m
  · rfl
  · simp only [Nat.add_sub_cancel]
    obtain ⟨c, hc⟩ := Nat.even_mul_succ_self m
    have e1 : (m + 1) * m = c + c := by rw [mul_comm]; omega
    have e2 : (m + 1 + 1) * (m + 1) = (c + (m + 1)) + (c + (m + 1)) := by
      have : (m + 1 + 1) * (m + 1) = m * (m + 1) + 2 * (m + 1) := by ring
      omega
    rw [e1, e2]; omega

/-- Power-level triangular identity: `q^(k(k-1)/2) * q^k = q^((k+1)k/2)`. -/
private lemma cauchy_tri_pow {R : Type*} [CommRing R] (q : R) (k : ℕ) :
    q ^ (k * (k - 1) / 2) * q ^ k = q ^ ((k + 1) * k / 2) := by
  rw [← pow_add]
  congr 1
  have h := cauchy_tri_succ k
  simpa [Nat.add_sub_cancel] using h

/-- **Cauchy q-binomial theorem** (the engine of Borwein Lemma 2):
`∏_{i<n} (1 + q^i·t) = ∑_{k≤n} q^{k(k-1)/2}·[n,k]_q·t^k`.

Borwein's form `∑_{m≤n} y^m q^{m(m+1)/2}[n,m]_q = ∏_{k=1}^n (1+y q^k)` is the `t = q·y` case.
Proved by induction on `n` via the q-Pascal recurrence (Aristotle-formalized, verified kernel-clean
in our kernel). -/
theorem qBin_cauchy {R : Type*} [CommRing R] (q t : R) (n : ℕ) :
    ∏ i ∈ Finset.range n, (1 + q ^ i * t)
      = ∑ k ∈ Finset.range (n + 1), q ^ (k * (k - 1) / 2) * qBin q n k * t ^ k := by
  induction n generalizing t with
  | zero => simp [qBin]
  | succ n ih =>
    set P : R := ∑ k ∈ Finset.range (n + 1),
        q ^ (k * (k - 1) / 2) * q ^ k * qBin q n k * t ^ k with hP
    set Q : R := ∑ k ∈ Finset.range (n + 1),
        q ^ ((k + 1) * k / 2) * qBin q n k * t ^ (k + 1) with hQ
    have hprod : ∏ i ∈ Finset.range (n + 1), (1 + q ^ i * t) = (1 + t) * P := by
      have ev : (∏ i ∈ Finset.range n, (1 + q ^ (i + 1) * t)) = P := by
        rw [show (∏ i ∈ Finset.range n, (1 + q ^ (i + 1) * t))
              = ∏ i ∈ Finset.range n, (1 + q ^ i * (q * t)) from
            Finset.prod_congr rfl (fun i _ => by rw [pow_succ]; ring), ih (q * t), hP]
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_pow]; ring
      rw [Finset.prod_range_succ', ev, pow_zero, one_mul]
      ring
    set A : R := ∑ k ∈ Finset.range n,
        q ^ ((k + 1) * k / 2) * q ^ (k + 1) * qBin q n (k + 1) * t ^ (k + 1) with hA
    have hPA : P = 1 + A := by
      rw [hP, Finset.sum_range_succ', hA]
      simp only [Nat.add_sub_cancel, qBin, Nat.zero_sub, Nat.mul_zero, Nat.zero_div,
        pow_zero, mul_one]
      ring
    have hsplit : ∑ k ∈ Finset.range (n + 2),
        q ^ (k * (k - 1) / 2) * qBin q (n + 1) k * t ^ k = P + Q := by
      rw [Finset.sum_range_succ', hPA, hQ, hA]
      simp only [Nat.add_sub_cancel, qBin, Nat.zero_sub, Nat.mul_zero, Nat.zero_div,
        pow_zero, mul_one]
      rw [show (∑ k ∈ Finset.range (n + 1),
              q ^ ((k + 1) * k / 2) * (q ^ (k + 1) * qBin q n (k + 1) + qBin q n k)
                * t ^ (k + 1))
            = (∑ k ∈ Finset.range (n + 1),
                q ^ ((k + 1) * k / 2) * q ^ (k + 1) * qBin q n (k + 1) * t ^ (k + 1))
              + (∑ k ∈ Finset.range (n + 1),
                q ^ ((k + 1) * k / 2) * qBin q n k * t ^ (k + 1)) from by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)]
      rw [Finset.sum_range_succ, qBin_eq_zero_of_lt q n (n + 1) (Nat.lt_succ_self n)]
      ring
    have htP : t * P = Q := by
      rw [hP, hQ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [show t * (q ^ (k * (k - 1) / 2) * q ^ k * qBin q n k * t ^ k)
            = (q ^ (k * (k - 1) / 2) * q ^ k) * qBin q n k * t ^ (k + 1) by ring, cauchy_tri_pow]
    rw [hprod, hsplit, add_mul, one_mul, htP]

end

/-! ### Upstream module `Approximants.lean` -/

section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-!
# Explicit rational approximants to `S` (contour-free)

Borwein (1992) builds the approximants from a contour integral `Fₙ(q)`. The decisive observation
(buried in his Lemma 5 proof) is that `Fₙ` equals an **explicit convergent series** of finite
products — no contour integral is logically needed:

  `Fₙ = ∑_{m=n}^∞ Iₘ`,   `Iₘ = -(1 - c·q^{m+n})⁻¹ · ∏_{k=1}^{n-1} (1 - q^{k-m})·(1 - c·q^{k+m})⁻¹`.

We take this as the *definition* of the error term `Eₙ` and rebuild the irrationality argument on it.

## Reduction to the q-harmonic form
`S = ∑_{n≥0} 1/(2^{n+2}−3)` is, up to an affine map by nonzero rationals and a finite `q^{m}` shift,
the value `z = ∑_{j≥1} 1/(1 − (8/3)·2^j)` (Borwein's normalized form with `q = 2`, `c = 8/3`,
`|c| > 2`). Irrationality is invariant under both operations, so `Irrational S ⟺ Irrational z`.

See `PENDING_WORK.md` for the full reduction chain and the obligation breakdown (O1–O4).
-/

open scoped BigOperators
open Filter Topology Finset

/-- Borwein base `q = 2`. -/
def qB : ℝ := 2

/-- Reduced shift parameter `c = 8/3` (so `|c| > 2`), obtained from `c' = 1/3` shifted by `q^3`. -/
noncomputable def cB : ℝ := 8 / 3

/-- Denominator of the rational parameter `c = 8/3`. Used for the `β^{2n}` denominator clearing. -/
def βB : ℕ := 3

/-- The reduced q-harmonic target value `z = ∑_{j≥1} 1/(1 − c·q^j)` (with `q = 2`, `c = 8/3`).
`Irrational S ⟺ Irrational z`. -/
noncomputable def zB : ℝ := ∑' j : ℕ, (1 - cB * qB ^ (j + 1))⁻¹

/-- The `m`-th term of the explicit (contour-free) error series. For `m ≥ n` this is Borwein's
residue `Iₘ`. All factors use integer (`zpow`) exponents so that `q^{k-m}` makes sense. -/
noncomputable def Iterm (n m : ℕ) : ℝ :=
  -(1 - cB * qB ^ ((m : ℤ) + n))⁻¹ *
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹

/-- The error term `Eₙ = Fₙ = ∑_{m≥n} Iₘ`, reindexed as `∑_{j≥0} I_{n}(n+j)`. -/
noncomputable def Eterm (n : ℕ) : ℝ := ∑' j : ℕ, Iterm n (n + j)

/-! ### Numeric facts about the base parameters `q = 2`, `c = 8/3`. -/

lemma qB_pos : (0 : ℝ) < qB := by norm_num [qB]
lemma one_lt_qB : (1 : ℝ) < qB := by norm_num [qB]
lemma qB_ne : qB ≠ 0 := ne_of_gt qB_pos
lemma cB_pos : (0 : ℝ) < cB := by norm_num [cB]
lemma two_lt_cB : (2 : ℝ) < cB := by norm_num [cB]

/-- `q^k ≥ 2` for `k ≥ 1` (natural power version). -/
lemma two_le_pow {k : ℕ} (hk : 1 ≤ k) : (2 : ℝ) ≤ qB ^ k := by
  calc (2 : ℝ) = qB ^ 1 := by norm_num [qB]
    _ ≤ qB ^ k := pow_le_pow_right₀ (le_of_lt one_lt_qB) hk

/-- `q^a ≥ q ≥ 2` for `a ≥ 1`. -/
lemma two_le_zpow {a : ℤ} (ha : 1 ≤ a) : (2 : ℝ) ≤ qB ^ a := by
  calc (2 : ℝ) = qB ^ (1 : ℤ) := by norm_num [qB]
    _ ≤ qB ^ a := zpow_le_zpow_right₀ (le_of_lt one_lt_qB) ha

/-- Each `c·q^a − 1` (for `a ≥ 1`) dominates `q^a`, so its inverse is at most `q^{-a}`. -/
lemma inv_cqpow_le {a : ℤ} (ha : 1 ≤ a) : |(1 - cB * qB ^ a)⁻¹| ≤ qB ^ (-a) := by
  have hqa : (2 : ℝ) ≤ qB ^ a := two_le_zpow ha
  have hqpos : (0 : ℝ) < qB ^ a := zpow_pos qB_pos a
  -- `c·q^a − 1 ≥ q^a > 0`
  have hge : qB ^ a ≤ cB * qB ^ a - 1 := by nlinarith [hqa, hqpos, two_lt_cB]
  have hpos : (0 : ℝ) < cB * qB ^ a - 1 := lt_of_lt_of_le hqpos hge
  have habs : |(1 - cB * qB ^ a)⁻¹| = (cB * qB ^ a - 1)⁻¹ := by
    rw [abs_inv]
    congr 1
    rw [abs_of_neg (by linarith)]
    ring
  rw [habs, zpow_neg]
  exact inv_anti₀ hqpos hge

/-- Each product factor `(1 − q^{k−m})·(1 − c·q^{k+m})⁻¹` has absolute value at most `1/2`
(for `1 ≤ k < m`). -/
lemma factor_bound {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ (1 : ℝ) / 2 := by
  rw [abs_mul]
  have h1 : |1 - qB ^ ((k : ℤ) - m)| ≤ 1 := by
    have hexp : (k : ℤ) - m ≤ 0 := by omega
    have hle1 : qB ^ ((k : ℤ) - m) ≤ 1 := by
      calc qB ^ ((k : ℤ) - m) ≤ qB ^ (0 : ℤ) :=
            zpow_le_zpow_right₀ (le_of_lt one_lt_qB) hexp
        _ = 1 := by norm_num
    have hpos : 0 < qB ^ ((k : ℤ) - m) := zpow_pos qB_pos _
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h2 : |(1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ qB ^ (-((k : ℤ) + m)) :=
    inv_cqpow_le (by omega)
  have h3 : qB ^ (-((k : ℤ) + m)) ≤ (1 : ℝ) / 2 := by
    calc qB ^ (-((k : ℤ) + m)) ≤ qB ^ (-1 : ℤ) :=
          zpow_le_zpow_right₀ (le_of_lt one_lt_qB) (by omega)
      _ = 1 / 2 := by rw [zpow_neg, zpow_one]; norm_num [qB]
  calc |1 - qB ^ ((k : ℤ) - m)| * |(1 - cB * qB ^ ((k : ℤ) + m))⁻¹|
      ≤ 1 * (1 / 2) := mul_le_mul h1 (le_trans h2 h3) (abs_nonneg _) (by norm_num)
    _ = 1 / 2 := by ring

/-- **Crude per-term bound.** For `1 ≤ n ≤ m`, `|Iₘ| ≤ q^{-(m+n)}·(1/2)^{n-1}`. The leading
factor carries the geometric `m`-decay; the `(n−1)` product factors are each `≤ 1/2`. (Enough for
summability and non-vanishing; the sharp super-exponential bound is the separate error obligation.) -/
lemma Iterm_abs_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |Iterm n m| ≤ qB ^ (-((m : ℤ) + n)) * (1 / 2) ^ (n - 1) := by
  rw [Iterm, abs_mul, abs_neg]
  have hlead : |(1 - cB * qB ^ ((m : ℤ) + n))⁻¹| ≤ qB ^ (-((m : ℤ) + n)) :=
    inv_cqpow_le (by omega)
  have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
        (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ (1 / 2) ^ (n - 1) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 (n - 1), |(1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹|
        ≤ ∏ _k ∈ Finset.Icc 1 (n - 1), (1 / 2 : ℝ) :=
          Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k hk => by
            rw [Finset.mem_Icc] at hk
            exact factor_bound hk.1 (by omega))
      _ = (1 / 2 : ℝ) ^ (Finset.Icc 1 (n - 1)).card := by rw [Finset.prod_const]
      _ = (1 / 2 : ℝ) ^ (n - 1) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hbnn : (0 : ℝ) ≤ qB ^ (-((m : ℤ) + n)) := le_of_lt (zpow_pos qB_pos _)
  exact mul_le_mul hlead hprod (abs_nonneg _) hbnn

/-- `q^{-j} = (1/2)^j`. -/
lemma qB_neg_zpow (j : ℕ) : qB ^ (-(j : ℤ)) = (1 / 2 : ℝ) ^ j := by
  rw [zpow_neg, zpow_natCast, show qB = 2 from rfl,
    show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]

/-- The reindexed term `I_n(n+j)` is bounded by `(1/2)^j` — enough for absolute summability. -/
lemma Iterm_shift_le {n : ℕ} (hn : 1 ≤ n) (j : ℕ) : |Iterm n (n + j)| ≤ (1 / 2 : ℝ) ^ j := by
  have h := Iterm_abs_le hn (Nat.le_add_right n j)
  have hexp : qB ^ (-(((n + j : ℕ) : ℤ) + n)) ≤ qB ^ (-(j : ℤ)) := by
    apply zpow_le_zpow_right₀ (le_of_lt one_lt_qB)
    push_cast; omega
  have hpow1 : (1 / 2 : ℝ) ^ (n - 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc |Iterm n (n + j)| ≤ qB ^ (-(((n + j : ℕ) : ℤ) + n)) * (1 / 2) ^ (n - 1) := h
    _ ≤ qB ^ (-(j : ℤ)) * 1 :=
        mul_le_mul hexp hpow1 (by positivity) (le_of_lt (zpow_pos qB_pos _))
    _ = (1 / 2) ^ j := by rw [mul_one, qB_neg_zpow]

/-- The error series `Eₙ = ∑_{j} I_n(n+j)` is summable. -/
lemma Eterm_summable {n : ℕ} (hn : 1 ≤ n) : Summable (fun j => Iterm n (n + j)) := by
  apply Summable.of_norm_bounded (g := fun j => (1 / 2 : ℝ) ^ j)
  · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  · intro j; rw [Real.norm_eq_abs]; exact Iterm_shift_le hn j

/-! ### Non-vanishing of the error (Borwein's Lemma 5).

For `q = 2`, `c = 8/3 > 1`, every term `Iₘ` (`m ≥ n`) has the *same* nonzero sign `(-1)^{n-1}`:
the leading factor `(1 − c·q^{m+n})⁻¹` is negative, and each of the `n−1` product factors
`(1 − q^{k−m})·(1 − c·q^{k+m})⁻¹` is negative. A sum of same-sign nonzero terms cannot vanish. -/

/-- The leading factor `(1 − c·q^a)⁻¹` is negative for `a ≥ 1`. -/
lemma leading_neg {a : ℤ} (ha : 1 ≤ a) : (1 - cB * qB ^ a)⁻¹ < 0 := by
  have h2 : (2 : ℝ) ≤ qB ^ a := two_le_zpow ha
  have hneg : (1 - cB * qB ^ a) < 0 := by nlinarith [h2, two_lt_cB, zpow_pos qB_pos a]
  exact inv_neg''.mpr hneg

/-- Each product factor is negative for `1 ≤ k < m`. -/
lemma factor_neg {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹ < 0 := by
  have hnum : 0 < 1 - qB ^ ((k : ℤ) - m) := by
    have hle : qB ^ ((k : ℤ) - m) ≤ qB ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ (le_of_lt one_lt_qB) (by omega)
    have heq : qB ^ (-1 : ℤ) = 1 / 2 := by rw [zpow_neg, zpow_one]; norm_num [qB]
    rw [heq] at hle; linarith
  exact mul_neg_of_pos_of_neg hnum (leading_neg (by omega))

/-- `(-1)^{n-1}` times the product of the `n−1` (negative) factors is positive. -/
lemma prod_factor_sign {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    0 < (-1 : ℝ) ^ (n - 1) * ∏ k ∈ Finset.Icc 1 (n - 1),
          (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹ := by
  have hcard : (Finset.Icc 1 (n - 1)).card = n - 1 := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have h1 : (-1 : ℝ) ^ (n - 1) = ∏ _k ∈ Finset.Icc 1 (n - 1), (-1 : ℝ) := by
    rw [Finset.prod_const, hcard]
  rw [h1, ← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro k hk
  rw [Finset.mem_Icc] at hk
  have hf := factor_neg hk.1 (show k < m by omega)
  linarith

/-- The sign of `Iₘ` (for `m ≥ n ≥ 1`) is exactly `(-1)^{n-1}`, and it is nonzero. -/
lemma Iterm_sign {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) : 0 < (-1 : ℝ) ^ (n - 1) * Iterm n m := by
  rw [Iterm]
  have hL : (1 - cB * qB ^ ((m : ℤ) + n))⁻¹ < 0 := leading_neg (by omega)
  have hP := prod_factor_sign hn hnm
  have hnegL : (0 : ℝ) < -(1 - cB * qB ^ ((m : ℤ) + n))⁻¹ := by linarith
  have := mul_pos hnegL hP
  -- v4.31: `convert … using 1` now also emits the `LT` instance-equality goal
  -- (`Real.instLT = Real.instPreorder.toLT`); close it by `rfl`, the algebra by `ring`.
  convert this using 1 <;> first | rfl | ring

/-! ### Sharp super-exponential error bound (Borwein's Lemma 4).

The decisive estimate. Using `|1 − q^{k−m}| ≤ 1` and `(c·q^a − 1)⁻¹ ≤ q^{-a}`,

  `|Iₘ| ≤ q^{-(m+n)}·∏_{k=1}^{n-1} q^{-(k+m)} = q^{-(n + T + n·m)}`,  `T = ∑_{k=1}^{n-1} k`,

which factors as `Cₙ·rⁿ` with `r = q^{-n} ∈ (0,1)`. Summing the geometric tail gives
`|Eₙ| ≤ 2·Cₙ·q^{-n²}`, super-exponential decay — enough to beat the denominator growth `Wₙ`. -/

/-- Tight per-factor bound: `|(1 − q^{k−m})·(1 − c·q^{k+m})⁻¹| ≤ (q^{k+m})⁻¹` for `1 ≤ k < m`. -/
lemma factor_abs_le {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) :
    |(1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ (qB ^ (k + m))⁻¹ := by
  rw [abs_mul]
  have h1 : |1 - qB ^ ((k : ℤ) - m)| ≤ 1 := by
    have hexp : (k : ℤ) - m ≤ 0 := by omega
    have hle1 : qB ^ ((k : ℤ) - m) ≤ 1 := by
      calc qB ^ ((k : ℤ) - m) ≤ qB ^ (0 : ℤ) :=
            zpow_le_zpow_right₀ (le_of_lt one_lt_qB) hexp
        _ = 1 := by norm_num
    have hpos : 0 < qB ^ ((k : ℤ) - m) := zpow_pos qB_pos _
    rw [abs_of_nonneg (by linarith)]; linarith
  have h2 : |(1 - cB * qB ^ ((k : ℤ) + m))⁻¹| ≤ qB ^ (-((k : ℤ) + m)) := inv_cqpow_le (by omega)
  have h3 : qB ^ (-((k : ℤ) + m)) = (qB ^ (k + m))⁻¹ := by
    rw [zpow_neg, ← zpow_natCast qB (k + m), Nat.cast_add]
  calc |1 - qB ^ ((k : ℤ) - m)| * |(1 - cB * qB ^ ((k : ℤ) + m))⁻¹|
      ≤ 1 * qB ^ (-((k : ℤ) + m)) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = (qB ^ (k + m))⁻¹ := by rw [one_mul, h3]

/-- Sharp per-term bound in product form. -/
lemma Iterm_abs_le_sharp {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |Iterm n m| ≤ (qB ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ (k + m))⁻¹ := by
  rw [Iterm, abs_mul, abs_neg]
  have hlead : |(1 - cB * qB ^ ((m : ℤ) + n))⁻¹| ≤ (qB ^ (m + n))⁻¹ := by
    have h := inv_cqpow_le (a := (m : ℤ) + n) (by omega)
    have he : qB ^ (-((m : ℤ) + n)) = (qB ^ (m + n))⁻¹ := by
      rw [zpow_neg, ← zpow_natCast qB (m + n), Nat.cast_add]
    rwa [he] at h
  have hprod : |∏ k ∈ Finset.Icc 1 (n - 1),
        (1 - qB ^ ((k : ℤ) - m)) * (1 - cB * qB ^ ((k : ℤ) + m))⁻¹|
      ≤ ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ (k + m))⁻¹ := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
    intro k hk; rw [Finset.mem_Icc] at hk
    exact factor_abs_le hk.1 (by omega)
  exact mul_le_mul hlead hprod (abs_nonneg _) (le_of_lt (inv_pos.mpr (pow_pos qB_pos _)))

/-- Exponent bookkeeping: `(m+n) + ∑_{k=1}^{n-1}(k+m) = (n + ∑_{k=1}^{n-1} k) + n·m` for `n ≥ 1`.
The `n·m` term is the source of the super-exponential (`q^{-n·m}`) decay. -/
lemma exp_identity {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    (m + n) + ∑ k ∈ Finset.Icc 1 (n - 1), (k + m)
      = (n + ∑ k ∈ Finset.Icc 1 (n - 1), k) + n * m := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul]
  have hmul : (n - 1) * m + m = n * m := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left m hn)]
  omega

/-- **Closed-form sharp per-term bound** (Borwein Lemma 4 core): `|Iₘ| ≤ Cₙ·(q^{-n})^m` with
`Cₙ = (q^{n + ∑_{k<n} k})⁻¹`. Geometric in `m` with ratio `q^{-n} ≤ 1/2`, so the tail sum is
super-exponentially small. -/
lemma Iterm_abs_le_geom {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    |Iterm n m| ≤ (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ m := by
  refine (Iterm_abs_le_sharp hn hnm).trans (le_of_eq ?_)
  have hL : (qB ^ (m + n))⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ (k + m))⁻¹
      = (qB ^ ((m + n) + ∑ k ∈ Finset.Icc 1 (n - 1), (k + m)))⁻¹ := by
    rw [Finset.prod_inv_distrib, prod_pow_eq_pow_sum, ← mul_inv, ← pow_add]
  have hR : (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ m
      = (qB ^ ((n + ∑ k ∈ Finset.Icc 1 (n - 1), k) + n * m))⁻¹ := by
    rw [inv_pow, ← pow_mul, ← mul_inv, ← pow_add]
  rw [hL, hR, exp_identity hn m]

/-- **Lemma 4 (error bound), `Eₙ` half.** Summing the geometric per-term bound:
`|Eₙ| ≤ Cₙ·(q^{-n})ⁿ·(1 − q^{-n})⁻¹` with `Cₙ = (q^{n + ∑_{k<n} k})⁻¹`. Since `(q^{-n})ⁿ = q^{-n²}`
and `Cₙ = q^{-(n + n(n-1)/2)}`, this is `≈ q^{-3n²/2}` — super-exponential, as in Borwein. -/
lemma Eterm_abs_le {n : ℕ} (hn : 1 ≤ n) :
    |Eterm n| ≤ (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ n
        * (1 - (qB ^ n)⁻¹)⁻¹ := by
  set r : ℝ := (qB ^ n)⁻¹ with hr_def
  set Cn : ℝ := (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ with hCn_def
  have hr0 : 0 ≤ r := by rw [hr_def]; exact le_of_lt (inv_pos.mpr (pow_pos qB_pos n))
  have hqn1 : (1 : ℝ) < qB ^ n := by
    calc (1 : ℝ) < qB := one_lt_qB
      _ = qB ^ 1 := (pow_one qB).symm
      _ ≤ qB ^ n := pow_le_pow_right₀ (le_of_lt one_lt_qB) hn
  have hr1 : r < 1 := by rw [hr_def]; exact inv_lt_one_of_one_lt₀ hqn1
  have hsummabs : Summable (fun j => |Iterm n (n + j)|) :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => Iterm_shift_le hn j)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have h1 : |Eterm n| ≤ ∑' j, |Iterm n (n + j)| := by
    have hnorm := norm_tsum_le_tsum_norm (f := fun j => Iterm n (n + j))
      (by simpa [Real.norm_eq_abs] using hsummabs)
    simpa [Eterm, Real.norm_eq_abs] using hnorm
  have hge : ∀ j, |Iterm n (n + j)| ≤ Cn * r ^ (n + j) := fun j =>
    Iterm_abs_le_geom hn (Nat.le_add_right n j)
  have hsummaj : Summable (fun j => Cn * r ^ (n + j)) := by
    simp_rw [pow_add]
    exact ((summable_geometric_of_lt_one hr0 hr1).mul_left _).mul_left _
  have h2 : ∑' j, |Iterm n (n + j)| ≤ ∑' j, Cn * r ^ (n + j) :=
    hsummabs.tsum_le_tsum hge hsummaj
  have h3 : ∑' j, Cn * r ^ (n + j) = Cn * r ^ n * (1 - r)⁻¹ := by
    simp_rw [pow_add, ← mul_assoc]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  calc |Eterm n| ≤ ∑' j, |Iterm n (n + j)| := h1
    _ ≤ ∑' j, Cn * r ^ (n + j) := h2
    _ = Cn * r ^ n * (1 - r)⁻¹ := h3

/-- Clean closed form of the error bound: `|Eₙ| ≤ 2·(q^{n + ∑_{k<n}k + n²})⁻¹`. The exponent
`n + (n−1)n/2 + n² = (3n² + n)/2` is Borwein's `3n²/2` decay (up to lower order). -/
lemma Eterm_abs_le' {n : ℕ} (hn : 1 ≤ n) :
    |Eterm n| ≤ 2 * (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
  refine (Eterm_abs_le hn).trans ?_
  have hC : (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ n
      = (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by
    rw [inv_pow, ← pow_mul, ← mul_inv, ← pow_add, sq]
  have hqn2 : (2 : ℝ) ≤ qB ^ n := two_le_pow hn
  have h1 : (qB ^ n)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hqn2
  have htail : (1 - (qB ^ n)⁻¹)⁻¹ ≤ 2 := by
    have hb : (0 : ℝ) < 1 / 2 := by norm_num
    calc (1 - (qB ^ n)⁻¹)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ hb (by linarith)
      _ = 2 := by norm_num
  have hCnn : (0 : ℝ) ≤ (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ :=
    le_of_lt (inv_pos.mpr (pow_pos qB_pos _))
  calc (qB ^ (n + ∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ * ((qB ^ n)⁻¹) ^ n * (1 - (qB ^ n)⁻¹)⁻¹
      = (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * (1 - (qB ^ n)⁻¹)⁻¹ := by rw [hC]
    _ ≤ (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left htail hCnn
    _ = 2 * (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹ := by ring

/-- **Lemma 5 (non-vanishing).** `Eₙ ≠ 0` for `n ≥ 1`. -/
lemma Eterm_ne_zero {n : ℕ} (hn : 1 ≤ n) : Eterm n ≠ 0 := by
  have hsum : Summable (fun j => (-1 : ℝ) ^ (n - 1) * Iterm n (n + j)) :=
    (Eterm_summable hn).mul_left _
  have hpos : ∀ j, 0 < (-1 : ℝ) ^ (n - 1) * Iterm n (n + j) :=
    fun j => Iterm_sign hn (Nat.le_add_right n j)
  have hp : 0 < ∑' j, (-1 : ℝ) ^ (n - 1) * Iterm n (n + j) :=
    hsum.tsum_pos (fun j => le_of_lt (hpos j)) 0 (hpos 0)
  rw [tsum_mul_left] at hp
  intro h0
  rw [show (∑' j, Iterm n (n + j)) = Eterm n from rfl, h0, mul_zero] at hp
  exact lt_irrefl 0 hp

/-! ### The denominator-clearing factor `Wₙ` and the assembly into irrationality. -/

lemma one_sub_cqpow_ne {k : ℕ} (hk : 1 ≤ k) : (1 - cB * qB ^ k) ≠ 0 :=
  ne_of_lt (by nlinarith [two_le_pow hk, two_lt_cB, pow_pos qB_pos k])

lemma one_sub_qpow_ne {k : ℕ} (hk : 1 ≤ k) : (1 - qB ^ k) ≠ 0 :=
  ne_of_lt (by nlinarith [two_le_pow hk])

/-- The clearing factor `Wₙ = (n−2)!·∏_{k=1}^n (1 − c·q^k)·∏_{k=⌈n/2⌉}^n (1 − q^k)` (Borwein's
`wₙ` without the `pₙ` factor; `Wₙ·Fₙ = wₙ·z + sₙ`). -/
noncomputable def Wterm (n : ℕ) : ℝ :=
  (Nat.factorial (n - 2) : ℝ)
    * (∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ k))
    * (∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - qB ^ k))

/-- `Wₙ ≠ 0` for `n ≥ 1`: a nonzero factorial times two products of nonzero factors. -/
lemma Wterm_ne_zero {n : ℕ} (hn : 1 ≤ n) : Wterm n ≠ 0 := by
  rw [Wterm]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact_mod_cast Nat.factorial_ne_zero _
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    exact one_sub_cqpow_ne hk.1
  · refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    -- `k ≥ ⌈n/2⌉ ≥ 1` since `n ≥ 1`
    exact one_sub_qpow_ne (by omega)

/-- **Wₙ growth bound** (Borwein Lemma 3 estimate). `|Wₙ| ≤ (n−2)!·cⁿ·(q^{∑_{k≤n}k})²`. Each
`|1 − c·q^k| ≤ c·q^k` and `|1 − q^k| ≤ q^k`; the second product (over `⌈n/2⌉..n`) is bounded by the
full product over `1..n`. -/
lemma Wterm_abs_le {n : ℕ} (hn : 1 ≤ n) :
    |Wterm n| ≤ (Nat.factorial (n - 2) : ℝ) * cB ^ n
        * qB ^ (∑ k ∈ Finset.Icc 1 n, k) * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
  have hfac : (0:ℝ) ≤ (Nat.factorial (n-2) : ℝ) := by positivity
  have hqS : (0:ℝ) ≤ qB ^ (∑ k ∈ Finset.Icc 1 n, k) := pow_nonneg (le_of_lt qB_pos) _
  rw [Wterm, abs_mul, abs_mul, abs_of_nonneg hfac]
  have hP1 : |∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ k)| ≤ cB ^ n * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc 1 n, |1 - cB * qB ^ k|
        ≤ ∏ k ∈ Finset.Icc 1 n, cB * qB ^ k := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk; rw [Finset.mem_Icc] at hk
          rw [abs_of_neg (by nlinarith [two_le_pow hk.1, two_lt_cB, pow_pos qB_pos k] :
            (1 - cB * qB ^ k) < 0)]
          nlinarith [pow_pos qB_pos k, cB_pos]
      _ = cB ^ n * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, prod_pow_eq_pow_sum, Nat.card_Icc,
            Nat.add_sub_cancel]
  have hP2 : |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - qB ^ k)| ≤ qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ Finset.Icc ((n + 1) / 2) n, |1 - qB ^ k|
        ≤ ∏ k ∈ Finset.Icc ((n + 1) / 2) n, qB ^ k := by
          apply Finset.prod_le_prod (fun k _ => abs_nonneg _)
          intro k hk; rw [Finset.mem_Icc] at hk
          rw [abs_of_nonpos (by nlinarith [two_le_pow (show 1 ≤ k by omega)] : (1 - qB ^ k) ≤ 0)]
          linarith
      _ = qB ^ (∑ k ∈ Finset.Icc ((n + 1) / 2) n, k) := prod_pow_eq_pow_sum _ _ _
      _ ≤ qB ^ (∑ k ∈ Finset.Icc 1 n, k) :=
          pow_le_pow_right₀ (le_of_lt one_lt_qB)
            (Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc (by omega) (le_refl n)))
  calc (Nat.factorial (n - 2) : ℝ) * |∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ k)|
        * |∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - qB ^ k)|
      ≤ (Nat.factorial (n - 2) : ℝ) * (cB ^ n * qB ^ (∑ k ∈ Finset.Icc 1 n, k))
          * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
        apply mul_le_mul _ hP2 (abs_nonneg _)
          (mul_nonneg hfac (mul_nonneg (pow_nonneg (le_of_lt cB_pos) n) hqS))
        exact mul_le_mul_of_nonneg_left hP1 hfac
    _ = (Nat.factorial (n - 2) : ℝ) * cB ^ n * qB ^ (∑ k ∈ Finset.Icc 1 n, k)
          * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by ring

/- **O1 — Borwein Lemmas 1+2+3.** Formerly a monolithic assumption `borwein_integrality` lived here; it is
now a fully machine-checked THEOREM (`Lemma3.lean`). Lemma 1 (residue identity) is proved elementarily
(`Residue.lean`, `RESIDUE-IDENTITY-ELEMENTARY-PROOF.md`); Lemma 2 (denominator integrality) is
`Bden_cast` (`Integrality.lean`, via `qBin_cauchy`); Lemma 3 (numerator integrality) is proved
elementarily (`Lemma3.lean`, via q-Lagrange + a 2-adic/odd-denominator clearing for `N_h`). The
headline `erdos_1050` is kernel-clean. -/

/-- Gauss' formula over `Icc 1 n`: `2·∑_{k=1}^n k = n(n+1)`. -/
lemma gauss_Icc (n : ℕ) : 2 * (∑ k ∈ Finset.Icc 1 n, k) = n * (n + 1) := by
  have hconv : (∑ k ∈ Finset.Icc 1 n, k) = ∑ k ∈ Finset.range (n + 1), k := by
    apply Finset.sum_subset
    · intro x hx; rw [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
    · intro x hx hx2; rw [Finset.mem_range] at hx; rw [Finset.mem_Icc] at hx2; omega
  rw [hconv, mul_comm, Finset.sum_range_id_mul_two, Nat.add_sub_cancel, Nat.mul_comm]

/-- **The combine majorant** (Borwein Lemma 4, all factors assembled). The cleared error is bounded
by `2·(n−2)!·(9c)ⁿ·(q^{∑_{k<n}k})⁻¹`: the `q^{2∑_{k≤n}k}` from `Wₙ` and `β^{2n}=9ⁿ` cancel against
`Eₙ`'s `q^{-(n + ∑_{k<n}k + n²)}` decay, leaving the super-exponential `(q^{∑_{k<n}k})⁻¹`. -/
lemma cleared_error_le {n : ℕ} (hn : 1 ≤ n) :
    |(βB : ℝ) ^ (2 * n) * Wterm n * Eterm n|
      ≤ 2 * (Nat.factorial (n - 2) : ℝ) * (9 * cB) ^ n
          * (qB ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
  have hβ : (βB : ℝ) ^ (2 * n) = (9 : ℝ) ^ n := by rw [pow_mul]; norm_num [βB]
  have h2 : n + n ^ 2 = (∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k) := by
    rw [← two_mul, gauss_Icc n]; ring
  have hexp : n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2
      = ((∑ k ∈ Finset.Icc 1 n, k) + (∑ k ∈ Finset.Icc 1 n, k))
        + (∑ k ∈ Finset.Icc 1 (n - 1), k) := by omega
  have hq : qB ^ (∑ k ∈ Finset.Icc 1 n, k) * qB ^ (∑ k ∈ Finset.Icc 1 n, k)
        * (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹
      = (qB ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
    rw [← pow_add, hexp]
    nth_rewrite 2 [pow_add]
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos qB_pos _)), one_mul]
  have hWnn : (0:ℝ) ≤ (Nat.factorial (n - 2) : ℝ) * cB ^ n
      * qB ^ (∑ k ∈ Finset.Icc 1 n, k) * qB ^ (∑ k ∈ Finset.Icc 1 n, k) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (pow_nonneg (le_of_lt cB_pos) n)) ?_) ?_ <;> exact pow_nonneg (le_of_lt qB_pos) _
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
  calc (βB : ℝ) ^ (2 * n) * |Wterm n| * |Eterm n|
      ≤ (βB : ℝ) ^ (2 * n) * ((Nat.factorial (n - 2) : ℝ) * cB ^ n
          * qB ^ (∑ k ∈ Finset.Icc 1 n, k) * qB ^ (∑ k ∈ Finset.Icc 1 n, k))
          * (2 * (qB ^ (n + (∑ k ∈ Finset.Icc 1 (n - 1), k) + n ^ 2))⁻¹) := by
        apply mul_le_mul _ (Eterm_abs_le' hn) (abs_nonneg _)
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hWnn)
        exact mul_le_mul_of_nonneg_left (Wterm_abs_le hn) (pow_nonneg (Nat.cast_nonneg _) _)
    _ = 2 * (Nat.factorial (n - 2) : ℝ) * (9 * cB) ^ n
          * (qB ^ (∑ k ∈ Finset.Icc 1 (n - 1), k))⁻¹ := by
        rw [hβ, mul_pow, ← hq]; ring

/-- `∑_{k=1}^{n-1} k = n(n−1)/2` (Gauss, lower form). -/
lemma gauss_Icc' (n : ℕ) : ∑ k ∈ Finset.Icc 1 (n - 1), k = n * (n - 1) / 2 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0; simp
  · have h := gauss_Icc (n - 1)
    rw [Nat.sub_add_cancel hn0, Nat.mul_comm (n - 1) n] at h
    omega

/-! ### The asymptotic `(n-2)!·Cⁿ·(q^{n(n-1)/2})⁻¹ → 0` (auto-formalized by Aristotle, verified
kernel-clean in our kernel). Super-exponential `(q^{n(n-1)/2})⁻¹` decay beats `(n-2)!·Cⁿ`; proved
by the ratio test (consecutive ratio `(n−1)C/qⁿ → 0`). -/

/-- Triangle-number recurrence `T(n+1) = T(n) + n`. -/
private lemma tri_succ (n : ℕ) : (n + 1) * ((n + 1) - 1) / 2 = n * (n - 1) / 2 + n := by
  have e : ∀ k : ℕ, k * (k - 1) / 2 = k.choose 2 := fun k => (Nat.choose_two_right k).symm
  rw [e, e, Nat.choose_succ_succ n 1]
  simp [Nat.choose_one_right]
  omega

private lemma fact_step (n : ℕ) (hn : 2 ≤ n) :
    Nat.factorial (n - 1) = (n - 1) * Nat.factorial (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [Nat.factorial_succ]

/-- The Borwein cleared-error majorant `(n-2)!·Cⁿ·(q^{n(n-1)/2})⁻¹`. -/
private noncomputable def fseq (q C : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial (n - 2) : ℝ) * C ^ n * (q ^ (n * (n - 1) / 2))⁻¹

private lemma fseq_pos (q C : ℝ) (hq : 1 < q) (hC : 0 < C) (n : ℕ) : 0 < fseq q C n := by
  have hq0 : 0 < q := by linarith
  unfold fseq; positivity

private lemma fseq_ratio (q C : ℝ) (hq : 1 < q) (hC : 0 < C) (n : ℕ) (hn : 2 ≤ n) :
    fseq q C (n + 1) / fseq q C n = (↑(n - 1)) * C * (q ^ n)⁻¹ := by
  have hq0 : 0 < q := by linarith
  unfold fseq
  have hfn : (n + 1) - 2 = n - 1 := by omega
  rw [hfn, fact_step n hn, tri_succ n, pow_add]
  have hpos1 : (0 : ℝ) < q ^ (n * (n - 1) / 2) := by positivity
  have hpos2 : (0 : ℝ) < q ^ n := by positivity
  have hC0 : C ≠ 0 := ne_of_gt hC
  push_cast; field_simp; ring

private lemma ratio_tendsto (q C : ℝ) (hq : 1 < q) :
    Tendsto (fun n : ℕ => (↑(n - 1) : ℝ) * C * (q ^ n)⁻¹) atTop (𝓝 0) := by
  have hr : |q⁻¹| < 1 := by
    rw [abs_of_pos (by positivity), inv_lt_one_iff₀]; right; exact hq
  have hbase : Tendsto (fun n : ℕ => (↑n : ℝ) * (q⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_abs_lt_one hr
  have hsq : Tendsto (fun n : ℕ => (↑(n - 1) : ℝ) * (q⁻¹) ^ n) atTop (𝓝 0) := by
    apply squeeze_zero (f := fun n : ℕ => (↑(n - 1) : ℝ) * (q⁻¹) ^ n)
      (g := fun n => (↑n : ℝ) * (q⁻¹) ^ n) (fun n => by positivity) ?_ hbase
    intro n
    have hb : (0 : ℝ) ≤ (q⁻¹) ^ n := by positivity
    have hle : (↑(n - 1) : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    nlinarith [hle, hb]
  have heq : (fun n : ℕ => (↑(n - 1) : ℝ) * C * (q ^ n)⁻¹)
      = (fun n : ℕ => C * ((↑(n - 1) : ℝ) * (q⁻¹) ^ n)) := by
    funext n; rw [inv_pow]; ring
  rw [heq]; simpa using hsq.const_mul C

/-- **The combine asymptotic** (Aristotle, verified). -/
theorem combine_asymptotic (q C : ℝ) (hq : 1 < q) (hC : 0 < C) :
    Tendsto (fun n : ℕ => (Nat.factorial (n - 2) : ℝ) * C ^ n * (q ^ (n * (n - 1) / 2))⁻¹)
      atTop (nhds 0) := by
  have hsummable : Summable (fseq q C) := by
    apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
    · filter_upwards with n using ne_of_gt (fseq_pos q C hq hC n)
    · have hcongr : (fun n : ℕ => ‖fseq q C (n + 1)‖ / ‖fseq q C n‖)
          =ᶠ[atTop] (fun n : ℕ => (↑(n - 1) : ℝ) * C * (q ^ n)⁻¹) := by
        filter_upwards [eventually_ge_atTop 2] with n hn
        rw [Real.norm_of_nonneg (le_of_lt (fseq_pos q C hq hC _)),
            Real.norm_of_nonneg (le_of_lt (fseq_pos q C hq hC _))]
        exact fseq_ratio q C hq hC n hn
      exact (ratio_tendsto q C hq).congr' hcongr.symm
  exact hsummable.tendsto_atTop_zero

/-- **O2 — error → 0 (Borwein Lemma 4, combine step), PROVED.** The cleared error `β^{2n}·Wₙ·Eₙ → 0`.
Squeeze: `cleared_error_le` bounds `|β^{2n}WₙEₙ|` by `2·(n-2)!·(9c)ⁿ·(q^{n(n-1)/2})⁻¹`, which
`combine_asymptotic` sends to `0`. -/
lemma cleared_error_tendsto :
    Filter.Tendsto (fun n => (βB : ℝ) ^ (2 * n) * Wterm n * Eterm n) Filter.atTop (nhds 0) := by
  have hg : Tendsto (fun n => 2 * ((Nat.factorial (n - 2) : ℝ) * (9 * cB) ^ n
      * (qB ^ (n * (n - 1) / 2))⁻¹)) atTop (𝓝 0) := by
    simpa using (combine_asymptotic qB (9 * cB) one_lt_qB (by have := cB_pos; positivity)).const_mul 2
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  have h := cleared_error_le hn
  rw [gauss_Icc' n] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **O4 — reduction `S ↔ z`, PROVED.** Per-term `(1 − c·q^{j+1})⁻¹ = −3/(2^{j+4}−3)`, so
`zB = −3·∑_{j} 1/(2^{(j+2)+2}−3) = −3·(S − 1 − 1/5) = −3·S + 18/5`. Irrationality is invariant
under the nonzero-rational affine map. -/
lemma irrational_S_iff_zB : Irrational S ↔ Irrational zB := by
  -- Summability (auto-formalized by Aristotle, verified kernel-clean; compare `∑ 2^{-n}`);
  -- lifted to `S_summable` in `Basic.lean`.
  have hsummable : Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 2) - 3)) := S_summable
  have hkey : zB = -3 * S + 18 / 5 := by
    have hterm : ∀ j : ℕ,
        (1 - cB * qB ^ (j + 1))⁻¹ = -3 * ((1 : ℝ) / ((2 : ℝ) ^ ((j + 2) + 2) - 3)) := by
      intro j
      have hp2 : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hexp : (2 : ℝ) ^ ((j + 2) + 2) = 8 * 2 ^ (j + 1) := by
        rw [show (j + 2) + 2 = (j + 1) + 3 from by ring, pow_add]; ring
      rw [hexp]; simp only [cB, qB]
      have hd2 : (1 : ℝ) - 8 / 3 * 2 ^ (j + 1) ≠ 0 := ne_of_lt (by nlinarith [hp2])
      have hd1 : (8 : ℝ) * 2 ^ (j + 1) - 3 ≠ 0 := ne_of_gt (by nlinarith [hp2])
      rw [inv_eq_one_div, mul_one_div, div_eq_div_iff hd2 hd1]
      ring
    rw [zB, tsum_congr hterm, tsum_mul_left]
    have hsum1 : Summable (fun i : ℕ => (1 : ℝ) / ((2 : ℝ) ^ ((i + 1) + 2) - 3)) :=
      hsummable.comp_injective (add_left_injective 1)
    have e1 : S = (1 : ℝ) / ((2 : ℝ) ^ (0 + 2) - 3)
        + ∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ ((i + 1) + 2) - 3) := hsummable.tsum_eq_zero_add
    have e2 : (∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ ((i + 1) + 2) - 3))
        = (1 : ℝ) / ((2 : ℝ) ^ ((0 + 1) + 2) - 3)
          + ∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (((i + 1) + 1) + 2) - 3) := hsum1.tsum_eq_zero_add
    have htail : (∑' j : ℕ, (1 : ℝ) / ((2 : ℝ) ^ ((j + 2) + 2) - 3)) = S - 6 / 5 := by
      have hconv : (∑' j : ℕ, (1 : ℝ) / ((2 : ℝ) ^ ((j + 2) + 2) - 3))
          = ∑' i : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (((i + 1) + 1) + 2) - 3) := rfl
      rw [hconv]
      have hSf0 : (1 : ℝ) / ((2 : ℝ) ^ (0 + 2) - 3) = 1 := by norm_num
      have hSf1 : (1 : ℝ) / ((2 : ℝ) ^ ((0 + 1) + 2) - 3) = 1 / 5 := by norm_num
      rw [hSf0] at e1
      rw [hSf1] at e2
      linarith [e1, e2]
    rw [htail]; ring
  rw [hkey, show (-3 : ℝ) * S + 18 / 5 = ((-3 : ℤ) : ℝ) * S + ((18 / 5 : ℚ) : ℝ) by push_cast; ring,
    irrational_add_ratCast_iff, irrational_intCast_mul_iff]
  exact ⟨fun h => ⟨by decide, h⟩, And.right⟩

/- `irrational_zB` and the headline `erdos_1050 : Irrational S` are assembled in `Integrality.lean`
(they need the `pVal`-based `borwein_integrality` theorem, which is downstream of `Pade.lean`). -/

end

/-! ### Upstream module `QLagrange.lean` -/

section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-!
# The q-Lagrange identity (Borwein Lemma 2, "Piece IIIb")

With the q-Lagrange weights `μ_j = ∏_{l≠j}(1 − q^l/q^j)⁻¹` (j,l ∈ [1,n]) and `1 < q`, for any `k`:

    ∑_{j=1}^n  μ_j · (q^j)^k   =   q^k · [n+k−1, n−1]_q .

This is the harder half of Borwein's first-form = second-form identity for the q-Padé denominator
`pₙ`; together with the Cauchy expansion (`cprod_cauchy`) it gives `pFirst n = pVal n`, discharging
the qLag hypothesis of `Eterm_eq_pVal` and the first clause of `residue_open`.

**Provenance**: auto-formalized by Harmonic's Aristotle (run `e53ca6e8`), then ported onto the repo's
`qBin` (which is the *same* q-Pascal recurrence Aristotle used) and verified kernel-clean in our kernel
(kernel check: `[propext, Classical.choice, Quot.sound]`).

The proof recognizes the LHS as a **divided-difference** sum `Dsum x s m = ∑_j (x j)^m/∏_{l≠j}(x j−x l)`
of the monomial `t^m` at the nodes `x j = q^j`, which satisfies the recurrence `Dsum_rec`, vanishes in
low degree (`Dsum_low`), and has the closed form `Dsum_main` by a double induction using q-Pascal.
-/

open Finset


/-- The product `∏_{l ∈ s, l ≠ j} (x j - x l)`, the denominator of the `j`-th divided-difference
weight. -/
noncomputable def Wprod (x : ℕ → ℝ) (s : Finset ℕ) (j : ℕ) : ℝ :=
  ∏ l ∈ s.erase j, (x j - x l)

/-- The divided difference of the monomial `t^m` at the nodes `x j`, `j ∈ s`. -/
noncomputable def Dsum (x : ℕ → ℝ) (s : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ j ∈ s, (x j) ^ m / Wprod x s j

/-- The node function `j ↦ q^j` is injective when `1 < q`. -/
lemma qpow_injective (q : ℝ) (hq : 1 < q) : Function.Injective (fun j : ℕ => q ^ j) := by
  exact fun a b h => le_antisymm ( le_of_not_gt fun h' => by have := pow_lt_pow_right₀ hq h'; aesop ) ( le_of_not_gt fun h' => by have := pow_lt_pow_right₀ hq h'; aesop )

/-- The node function `j ↦ q^j` is injective when `1 < |q|` (any sign of `q`). `q^a = q^b` ⟹
`|q|^a = |q|^b` ⟹ `a = b`. The entry point for the negative-base (`q ≤ −2`) q-Lagrange identity. -/
lemma qpow_injective_abs (q : ℝ) (hq : 1 < |q|) : Function.Injective (fun j : ℕ => q ^ j) := by
  intro a b h
  have habs : |q| ^ a = |q| ^ b := by rw [← abs_pow, ← abs_pow]; exact congrArg abs h
  exact qpow_injective |q| hq habs

/-- The fundamental divided-difference recurrence: removing any node `a ∈ s`. -/
lemma Dsum_rec (x : ℕ → ℝ) (hx : Function.Injective x) (s : Finset ℕ) (a : ℕ) (ha : a ∈ s)
    (m : ℕ) :
    Dsum x s (m + 1) = Dsum x (s.erase a) m + x a * Dsum x s m := by
  unfold Dsum Wprod;
  have h_split : ∑ j ∈ s, (x j ^ m * (x j - x a)) / (∏ l ∈ s.erase j, (x j - x l)) = ∑ j ∈ s.erase a, x j ^ m / (∏ l ∈ (s.erase a).erase j, (x j - x l)) := by
    have h_split : ∀ j ∈ s.erase a, (x j ^ m * (x j - x a)) / (∏ l ∈ s.erase j, (x j - x l)) = x j ^ m / (∏ l ∈ (s.erase a).erase j, (x j - x l)) := by
      intro j hj; rw [ Finset.prod_eq_prod_sdiff_singleton_mul <| Finset.mem_erase_of_ne_of_mem ( by aesop ) ha ] ; ring_nf;
      rw [ show ( s.erase a ).erase j = s.erase j \ { a } by ext; aesop ] ; ring_nf;
      grind;
    rw [ ← Finset.sum_congr rfl h_split, Finset.sum_erase_eq_sub ha ] ; aesop;
  simp_all +decide [ mul_sub, sub_div, pow_succ, mul_div_assoc, Finset.mul_sum _ _ _ ];
  grind

/-- For at least two distinct nodes, `∑_j 1/∏_{l≠j}(x j - x l) = 0`. -/
lemma Dsum_zero (x : ℕ → ℝ) (hx : Function.Injective x) (s : Finset ℕ) (hs : 2 ≤ s.card) :
    Dsum x s 0 = 0 := by
  induction' s using Finset.strongInduction with s ih;
  by_cases h_two_elements : s.card = 2;
  · rw [ Finset.card_eq_two ] at h_two_elements;
    rcases h_two_elements with ⟨ a, b, hab, rfl ⟩ ; unfold Dsum; simp +decide [ hab ] ; ring_nf;
    unfold Wprod; simp +decide [ *, Finset.prod ] ; ring_nf;
    rw [ show -x a + x b = - ( x a - x b ) by ring, inv_neg ] ; ring;
  · obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ s, ∃ b ∈ s, a ≠ b :=
      one_lt_card.mp hs
    have h_rec_a : Dsum x s 1 = Dsum x (s.erase a) 0 + x a * Dsum x s 0 := by
      exact Dsum_rec x hx s a ha 0
    have h_rec_b : Dsum x s 1 = Dsum x (s.erase b) 0 + x b * Dsum x s 0 := by
      exact Dsum_rec x hx s b hb 0;
    grind +splitIndPred

/-- The divided difference of a monomial of degree below `card - 1` vanishes. -/
lemma Dsum_low (x : ℕ → ℝ) (hx : Function.Injective x) :
    ∀ (s : Finset ℕ) (m : ℕ), m + 1 < s.card → Dsum x s m = 0 := by
  intro s m hm;
  induction' m with m ih generalizing s;
  · exact Dsum_zero x hx s hm;
  · obtain ⟨ a, ha ⟩ := Finset.card_pos.mp ( by linarith );
    rw [ Dsum_rec x hx s a ha m ];
    rw [ ih s ( by linarith ), ih ( s.erase a ) ( by rw [ Finset.card_erase_of_mem ha ] ; omega ), MulZeroClass.mul_zero, add_zero ]

/-- The closed form of the divided difference of `t^{N+k}` at the nodes `q, q^2, …, q^{N+1}`.
Only node *injectivity* is needed (the Gaussian-binomial closed form is a polynomial identity), so this
holds for any `q` with `q^j` injective — both `1 < q` and `1 < |q|` (`q ≤ −2`). -/
lemma Dsum_main (q : ℝ) (hinj : Function.Injective (fun j : ℕ => q ^ j)) :
    ∀ N k : ℕ, Dsum (fun j => q ^ j) (Finset.Icc 1 (N + 1)) (N + k)
      = q ^ k * qBin q (N + k) N := by
  intros N k
  induction' N with N ih generalizing k;
  · unfold Dsum Wprod qBin; norm_num;
  · induction' k with k ihk;
    · have := Dsum_rec ( fun j => q ^ j ) hinj ( Finset.Icc 1 ( N + 2 ) ) ( N + 2 ) ( by norm_num ) N;
      simp_all +decide;
      rw [ show Dsum ( fun j => q ^ j ) ( Icc 1 ( N + 2 ) ) N = 0 from _ ] ; norm_num [ qBin_self ];
      · -- v4.31: `convert … using 1` no longer auto-unifies `Ico 1 (N+2)` with
        -- `Icc 1 (N+1)`, so it leaves a separate interval-reindex goal alongside the
        -- numeric one. Discharge both explicitly.
        convert ih 0 using 1
        · simp only [Nat.add_zero]
          rw [show Finset.Ico 1 (N + 2) = Finset.Icc 1 (N + 1) from by
                ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
        · norm_num [qBin_self]
      · convert Dsum_low ( fun j => q ^ j ) hinj ( Finset.Icc 1 ( N + 2 ) ) N _ using 1 ; simp +arith +decide;
    · have h_rec : Dsum (fun j => q ^ j) (Finset.Icc 1 (N + 2)) (N + 1 + k + 1) = Dsum (fun j => q ^ j) (Finset.Icc 1 (N + 1)) (N + k + 1) + q ^ (N + 2) * Dsum (fun j => q ^ j) (Finset.Icc 1 (N + 2)) (N + 1 + k) := by
        convert Dsum_rec ( fun j => q ^ j ) hinj ( Finset.Icc 1 ( N + 2 ) ) ( N + 2 ) ( by norm_num ) ( N + 1 + k ) using 1;
        simp +arith +decide;
        rfl;
      have hpascal := qBin_succ_succ q (N + k + 1) N
      grind +locals [qBin_succ_succ]

/-- The original q-Lagrange LHS rewritten as a divided-difference sum. Needs only `q ≠ 0`. -/
lemma lhs_eq_Dsum (q : ℝ) (hq0 : q ≠ 0) (n : ℕ) (k : ℕ) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ l ∈ (Finset.Icc 1 n).erase j, (1 - q ^ l / q ^ j)⁻¹) * (q ^ j) ^ k
      = Dsum (fun j => q ^ j) (Finset.Icc 1 n) (n - 1 + k) := by
  refine' Finset.sum_congr rfl fun j hj => _;
  have h_term : ∀ l ∈ Finset.erase (Finset.Icc 1 n) j, (1 - q ^ l / q ^ j)⁻¹ = q ^ j / (q ^ j - q ^ l) := by
    intro l hl; rw [ one_sub_div ( pow_ne_zero j hq0 ) ] ; norm_num;
  rw [ Finset.prod_congr rfl h_term, Finset.prod_div_distrib, Finset.prod_const, Finset.card_erase_of_mem hj, Nat.card_Icc, ( by aesop : n - 1 = n - 1 ) ] ; ring!;

/-- **The q-Lagrange identity** (`1 < q`).  (The hypothesis `hk : k ≤ n - 1` is unnecessary — the identity
holds for every `k` — but is kept for faithfulness with the `residue_open` clause.) -/
theorem qLagrange (q : ℝ) (hq : 1 < q) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k ≤ n - 1) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ l ∈ (Finset.Icc 1 n).erase j, (1 - q ^ l / q ^ j)⁻¹) * (q ^ j) ^ k
      = q ^ k * qBin q (n + k - 1) (n - 1) := by
  rw [lhs_eq_Dsum q (by linarith) n k]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have h := Dsum_main q (qpow_injective q hq) N k
  have e1 : N + 1 - 1 + k = N + k := by omega
  have e2 : N + 1 + k - 1 = N + k := by omega
  have e3 : N + 1 - 1 = N := by omega
  rw [e1, e2, e3]
  exact h

/-- **The q-Lagrange identity for `1 < |q|`** (both signs of `q`, e.g. negative base `q ≤ −2`). Same
divided-difference proof, using `qpow_injective_abs` for node distinctness. A brick toward the
negative-base discharge of `borwein_approximants`. -/
theorem qLagrange_abs (q : ℝ) (hq : 1 < |q|) (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k ≤ n - 1) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ l ∈ (Finset.Icc 1 n).erase j, (1 - q ^ l / q ^ j)⁻¹) * (q ^ j) ^ k
      = q ^ k * qBin q (n + k - 1) (n - 1) := by
  have hq0 : q ≠ 0 := by intro h; rw [h] at hq; norm_num at hq
  rw [lhs_eq_Dsum q hq0 n k]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have h := Dsum_main q (qpow_injective_abs q hq) N k
  have e1 : N + 1 - 1 + k = N + k := by omega
  have e2 : N + 1 + k - 1 = N + k := by omega
  have e3 : N + 1 - 1 = N := by omega
  rw [e1, e2, e3]
  exact h

end

/-! ### Upstream module `Pade.lean` -/

section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-!
# The q-Padé denominator `pₙ` and its integrality (toward Borwein Lemma 2)

`pVal n` is the real value of Borwein's denominator polynomial `pₙ(c,q)` at `c = 8/3`, `q = 2`
(second form, via Gaussian binomials). `pInt n` is the `3^{n-1}`-cleared integer version. The lemma
`pInt_cast` (Borwein Lemma 2, integrality half) says they agree after clearing — so `3^{n-1}·pₙ ∈ ℤ`.

This is a prerequisite for discharging `borwein_integrality` (O1); the remaining piece is the
residue identity (Lemma 1, see `ON-LINE-REQUEST.md`).
-/

open scoped BigOperators

/-- `pₙ(8/3, 2)` (Borwein Lemma 2, second form): the real-valued q-Padé denominator. -/
noncomputable def pVal (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (-cB) ^ k * qB ^ (k * (k + 3) / 2)
    * qBin qB (n - 1) k * qBin qB (n + k - 1) (n - 1)

/-- The `3^{n-1}`-cleared **integer** q-Padé denominator. -/
def pInt (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (-8) ^ k * 3 ^ (n - 1 - k) * 2 ^ (k * (k + 3) / 2)
    * qBin (2 : ℤ) (n - 1) k * qBin (2 : ℤ) (n + k - 1) (n - 1)

/-- `qBin` at the real base `2` is the integer `qBin` cast to `ℝ`. -/
lemma qBin_two_cast (m j : ℕ) : qBin qB m j = ((qBin (2 : ℤ) m j : ℤ) : ℝ) := by
  simpa [qB] using qBin_map (Int.castRingHom ℝ) (2 : ℤ) m j

/-- **Borwein Lemma 2 (integrality of `pₙ`).** `(pInt n : ℝ) = 3^{n-1}·pₙ(8/3,2)`, so the cleared
q-Padé denominator is an integer. -/
lemma pInt_cast (n : ℕ) : (pInt n : ℝ) = 3 ^ (n - 1) * pVal n := by
  rw [pInt, pVal, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hclear : (3 : ℝ) ^ (n - 1) * (-cB) ^ k = (-8) ^ k * 3 ^ (n - 1 - k) := by
    have h3 : (3 : ℝ) ^ (n - 1) = 3 ^ k * 3 ^ (n - 1 - k) := by rw [← pow_add]; congr 1; omega
    have hcB : (-cB : ℝ) = -8 / 3 := by simp only [cB]; ring
    rw [h3, hcB, mul_assoc, mul_comm ((3 : ℝ) ^ (n - 1 - k)) ((-8 / 3 : ℝ) ^ k), ← mul_assoc,
      ← mul_pow, show (3 : ℝ) * (-8 / 3) = -8 by ring]
  rw [qBin_two_cast (n - 1) k, qBin_two_cast (n + k - 1) (n - 1), ← hclear,
    show qB = (2 : ℝ) from rfl]
  ring

end

/-! ### Upstream module `Residue.lean` -/

section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-!
# Elementary (contour-free) proof of Borwein's residue identity — Piece II: the geometric collapse

The previous laps reduced Erdős #1050 to the single assumption `borwein_integrality`, whose only deep
component is Borwein's Lemma 1 (the residue identity). This file begins a **fully elementary** proof
of that identity (no contour integral); see `RESIDUE-IDENTITY-ELEMENTARY-PROOF.md` for the full
strategy. The crux is the **collapse of the auxiliary series**

  `T_i := ∑_{h≥1} q^{-i·h} / (1 − c·q^h)  =  c^i · z  +  R_i`,    `R_i ∈ ℚ`,

which is what the contour integral was hiding. This is proved here by the per-term identity

  `q^{-i·h}/(1−c·q^h) = q^{-i·h} + c · q^{-(i-1)·h}/(1−c·q^h)`

(`key_term` below), a geometric series, and induction on `i`. Indexing matches `zB`: we sum over
`j : ℕ` with `h = j + 1`.
-/


open scoped BigOperators
open Filter Topology

/-- The rational correction `R_i = ∑_{l=1}^{i} c^{i-l}/(q^l − 1)`, via the recurrence
`R_{i+1} = 1/(q^{i+1} − 1) + c·R_i`, `R_0 = 0`. -/
noncomputable def Rrat : ℕ → ℝ
  | 0 => 0
  | (i + 1) => 1 / (qB ^ (i + 1) - 1) + cB * Rrat i

/-- The auxiliary series `T_i = ∑_{h≥1} q^{-i·h}·(1 − c·q^h)⁻¹` (with `h = j + 1`).
All exponents are non-positive, so we use `(qB^…)⁻¹` (natural power) rather than `zpow`. -/
noncomputable def Tser (i : ℕ) : ℝ :=
  ∑' j : ℕ, (qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹

/-- The per-term collapse identity. With `P = q^h` (`P ≠ 0`, `1 − c·P ≠ 0`):
`(P^{i+1})⁻¹·(1−cP)⁻¹ = (P^{i+1})⁻¹ + c·(P^i)⁻¹·(1−cP)⁻¹`. -/
lemma key_term (P : ℝ) (i : ℕ) (hP : P ≠ 0) (hcP : 1 - cB * P ≠ 0) :
    (P ^ (i + 1))⁻¹ * (1 - cB * P)⁻¹
      = (P ^ (i + 1))⁻¹ + cB * (P ^ i)⁻¹ * (1 - cB * P)⁻¹ := by
  have hPi : P ^ i ≠ 0 := pow_ne_zero i hP
  have hPi1 : P ^ (i + 1) ≠ 0 := pow_ne_zero (i + 1) hP
  field_simp
  ring

/-- `q^{j+1} ≠ 0`. -/
private lemma qpow_ne (j : ℕ) : qB ^ (j + 1) ≠ 0 := pow_ne_zero _ qB_ne

/-- Per-term absolute bound `|q^{-i(j+1)}·u_{j+1}| ≤ (1/2)^{j+1}`. -/
lemma Tterm_abs_le (i j : ℕ) :
    |(qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹| ≤ (1 / 2 : ℝ) ^ (j + 1) := by
  rw [abs_mul]
  have h1 : |(qB ^ (i * (j + 1)))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt qB_pos) _))]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt one_lt_qB))
  have h2 : |(1 - cB * qB ^ (j + 1))⁻¹| ≤ qB ^ (-((j : ℤ) + 1)) := by
    have h := inv_cqpow_le (a := (j : ℤ) + 1) (by omega)
    have he : qB ^ ((j : ℤ) + 1) = qB ^ (j + 1) := by
      rw [← zpow_natCast qB (j + 1)]; norm_num
    rwa [he] at h
  have h3 : qB ^ (-((j : ℤ) + 1)) = (1 / 2 : ℝ) ^ (j + 1) := by
    rw [show (-((j : ℤ) + 1)) = -(((j + 1 : ℕ) : ℤ)) by push_cast; ring, qB_neg_zpow]
  calc |(qB ^ (i * (j + 1)))⁻¹| * |(1 - cB * qB ^ (j + 1))⁻¹|
      ≤ 1 * qB ^ (-((j : ℤ) + 1)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = (1 / 2 : ℝ) ^ (j + 1) := by rw [one_mul, h3]

/-- `T_i` is summable (dominated by the geometric `(1/2)^{j+1}`). -/
lemma Tser_summable (i : ℕ) :
    Summable (fun j : ℕ => (qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹) := by
  apply Summable.of_norm_bounded (g := fun j => (1 / 2 : ℝ) ^ (j + 1))
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)
  · intro j; rw [Real.norm_eq_abs]; exact Tterm_abs_le i j

/-- `T_0 = z`. -/
lemma Tser_zero : Tser 0 = zB := by
  unfold Tser zB
  apply tsum_congr
  intro j
  simp

/-- The geometric piece `∑_{j} q^{-(i+1)(j+1)} = 1/(q^{i+1} − 1)`. -/
lemma geom_piece (i : ℕ) :
    ∑' j : ℕ, (qB ^ ((i + 1) * (j + 1)))⁻¹ = 1 / (qB ^ (i + 1) - 1) := by
  set r : ℝ := (qB ^ (i + 1))⁻¹ with hr
  have hrpos : 0 < r := by rw [hr]; exact inv_pos.mpr (pow_pos qB_pos _)
  have hqgt : (1 : ℝ) < qB ^ (i + 1) := by
    calc (1 : ℝ) < qB := one_lt_qB
      _ = qB ^ 1 := (pow_one qB).symm
      _ ≤ qB ^ (i + 1) := pow_le_pow_right₀ (le_of_lt one_lt_qB) (by omega)
  have hr1 : r < 1 := by rw [hr]; exact inv_lt_one_of_one_lt₀ hqgt
  have hconv : ∀ j : ℕ, (qB ^ ((i + 1) * (j + 1)))⁻¹ = r * r ^ j := by
    intro j; rw [hr, ← pow_succ', inv_pow, ← pow_mul]
  rw [tsum_congr hconv, tsum_mul_left, tsum_geometric_of_lt_one (le_of_lt hrpos) hr1, hr]
  have hx1 : (1 : ℝ) - (qB ^ (i + 1))⁻¹ ≠ 0 := by
    have : (qB ^ (i + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hqgt
    linarith
  have hx0 : (qB : ℝ) ^ (i + 1) ≠ 0 := ne_of_gt (pow_pos qB_pos _)
  have hx2 : (qB : ℝ) ^ (i + 1) - 1 ≠ 0 := by linarith [hqgt]
  field_simp

/-- The geometric piece is summable. -/
lemma geom_summable (i : ℕ) : Summable (fun j : ℕ => (qB ^ ((i + 1) * (j + 1)))⁻¹) := by
  apply Summable.of_norm_bounded (g := fun j => (1 / 2 : ℝ) ^ (j + 1))
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)
  · intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt qB_pos) _))]
    have h1 : (qB ^ ((i + 1) * (j + 1)))⁻¹ ≤ (qB ^ (j + 1))⁻¹ :=
      inv_anti₀ (pow_pos qB_pos _)
        (pow_le_pow_right₀ (le_of_lt one_lt_qB) (by rw [Nat.succ_mul]; omega))
    calc (qB ^ ((i + 1) * (j + 1)))⁻¹ ≤ (qB ^ (j + 1))⁻¹ := h1
      _ = (1 / 2 : ℝ) ^ (j + 1) := by
          rw [show (1 / 2 : ℝ) = qB⁻¹ by norm_num [qB], inv_pow]

/-- **The collapse recurrence**: `T_{i+1} = 1/(q^{i+1} − 1) + c·T_i`. -/
lemma Tser_succ (i : ℕ) : Tser (i + 1) = 1 / (qB ^ (i + 1) - 1) + cB * Tser i := by
  unfold Tser
  have hterm : ∀ j : ℕ,
      (qB ^ ((i + 1) * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹
        = (qB ^ ((i + 1) * (j + 1)))⁻¹
          + cB * (qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹ := by
    intro j
    have hk := key_term (qB ^ (j + 1)) i (qpow_ne j) (one_sub_cqpow_ne (k := j + 1) (by omega))
    have e1 : qB ^ ((i + 1) * (j + 1)) = (qB ^ (j + 1)) ^ (i + 1) := by
      rw [← pow_mul, Nat.mul_comm]
    have e2 : qB ^ (i * (j + 1)) = (qB ^ (j + 1)) ^ i := by
      rw [← pow_mul, Nat.mul_comm]
    rw [e1, e2]; exact hk
  rw [tsum_congr hterm]
  have hsum_rest : Summable
      (fun j : ℕ => cB * (qB ^ (i * (j + 1)))⁻¹ * (1 - cB * qB ^ (j + 1))⁻¹) := by
    simp_rw [mul_assoc]
    exact (Tser_summable i).mul_left cB
  rw [Summable.tsum_add (geom_summable i) hsum_rest, geom_piece i]
  congr 1
  simp_rw [mul_assoc]
  rw [tsum_mul_left]

/-- **Piece II — the collapse**: `T_i = c^i · z + R_i`. Every auxiliary series is
`(rational) + (rational)·z`. Proved by induction on `i` from the recurrence. -/
theorem Tser_collapse (i : ℕ) : Tser i = cB ^ i * zB + Rrat i := by
  induction i with
  | zero => rw [Tser_zero, show Rrat 0 = 0 from rfl]; ring
  | succ i ih =>
      rw [Tser_succ, ih, show Rrat (i + 1) = 1 / (qB ^ (i + 1) - 1) + cB * Rrat i from rfl]
      ring

/-! ### Assembly building block: the product form of `Iₘ`

The lead factor `(1 − c·q^{m+n})⁻¹` is the `k = n` term of the `c`-product, so `Iₘ` separates into a
`q`-numerator times a clean `c`-product over `1..n`. This is the first algebraic step toward the
residue identity (then Piece I partial-fractions the `c`-product, Piece II collapses the result). -/

/-- `Iₘ = −(∏_{k=1}^{n-1}(1−q^{k−m}))·∏_{k=1}^{n}(1−c·q^{k+m})⁻¹` (for `n ≥ 1`). -/
lemma Iterm_prod_form (n m : ℕ) (hn : 1 ≤ n) :
    Iterm n m
      = -((∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) - m)))
          * ∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ ((k : ℤ) + m))⁻¹) := by
  rw [Iterm, Finset.prod_mul_distrib,
    show ((m : ℤ) + n) = ((n : ℤ) + m) from by ring,
    show Finset.Icc 1 n = Finset.Icc 1 ((n - 1) + 1) from by rw [Nat.sub_add_cancel hn],
    Finset.prod_Icc_succ_top (by omega : 1 ≤ (n - 1) + 1), Nat.sub_add_cancel hn]
  ring

/-- **`q`-numerator expansion** `D_m = ∏_{k=1}^{n-1}(1−q^{k−m})` as a sum of monomials in `q^{−m}`:
each subset `t` contributes weight `(q^{−m})^{|t|}`. This produces exactly the `q^{−i·m}` weights
that the collapse `Tser_collapse` consumes (with `i = |t|`). -/
lemma Dterm_expand (n m : ℕ) :
    (∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) - m)))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-qB ^ k)) * ((qB ^ m)⁻¹) ^ t.card := by
  have hfac : ∀ k : ℕ, (1 : ℝ) - qB ^ ((k : ℤ) - m) = 1 + (-(qB ^ k)) * (qB ^ m)⁻¹ := by
    intro k
    rw [zpow_sub₀ qB_ne, zpow_natCast, zpow_natCast, div_eq_mul_inv]
    ring
  rw [Finset.prod_congr rfl (fun k _ => hfac k), Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- **Piece IIIa — Cauchy expansion of the `c`-product** `∏_{k=1}^{n-1}(1 − c·q^{k+j})`, a direct
application of the Cauchy q-binomial theorem `qBin_cauchy` (reindex `k = 1 + i`, `t = −c·q^{j+1}`).
This is the first half of the first-form = second-form identity (Borwein Lemma 2); the second half is
the q-Lagrange identity `∑_j μ_j q^{jk} = q^k[n+k−1,n−1]_q` (Piece IIIb). -/
lemma cprod_cauchy {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - cB * qB ^ (k + j))
      = ∑ i ∈ Finset.range n,
          qB ^ (i * (i - 1) / 2) * qBin qB (n - 1) i * (-cB) ^ i * qB ^ ((j + 1) * i) := by
  have hIcc : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.prod_Ico_eq_prod_range]
  have hterm : ∀ k, (1 - cB * qB ^ (1 + k + j)) = 1 + qB ^ k * (-cB * qB ^ (j + 1)) := by
    intro k
    rw [show 1 + k + j = k + (j + 1) from by ring, pow_add]; ring
  rw [Finset.prod_congr rfl (fun k _ => hterm k), qBin_cauchy qB (-cB * qB ^ (j + 1)) (n - 1),
    Nat.sub_add_cancel hn]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, ← pow_mul]
  ring

/-- Exponent bookkeeping `i(i−1)/2 + 2i = i(i+3)/2` (the `qBin_cauchy` exponent plus the two `q^i`
factors from the q-Lagrange step combine into the `pVal` exponent). -/
private lemma exp_iden (i : ℕ) : i * (i - 1) / 2 + 2 * i = i * (i + 3) / 2 := by
  rcases i with _ | m
  · rfl
  · simp only [Nat.add_sub_cancel]
    obtain ⟨c, hc⟩ := Nat.even_mul_succ_self m
    have e1 : (m + 1) * m = c + c := by rw [mul_comm]; omega
    have e2 : (m + 1) * (m + 1 + 3) = (c + 2 * (m + 1)) + (c + 2 * (m + 1)) := by
      have : (m + 1) * (m + 1 + 3) = m * (m + 1) + 4 * (m + 1) := by ring
      omega
    rw [e1, e2]; omega

/-- The q-Lagrange weight `μ_j = ∏_{l∈[1,n], l≠j}(1 − q^l/q^j)⁻¹` (independent of `c`, `m`). -/
noncomputable def muW (n j : ℕ) : ℝ :=
  ∏ l ∈ (Finset.Icc 1 n).erase j, (1 - qB ^ l / qB ^ j)⁻¹

/-- Borwein's q-Padé denominator in **first form** `pₙ = ∑_{j=1}^n μ_j·∏_{k=1}^{n-1}(1−c q^{k+j})`. -/
noncomputable def pFirst (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - cB * qB ^ (k + j))

/-- **Piece III — first form = second form** (Borwein Lemma 2), conditional on the q-Lagrange
identity `qLag` (Piece IIIb, `aristotle/QLagrange.lean`). Assembled from the Cauchy expansion
`cprod_cauchy` + a finite sum swap + the exponent identity `exp_iden`. NO new assumption: `qLag` is a
hypothesis, to be discharged once IIIb is proved. -/
theorem pFirst_eq_pVal {n : ℕ} (hn : 1 ≤ n)
    (qLag : ∀ i, i < n →
      ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ i = qB ^ i * qBin qB (n + i - 1) (n - 1)) :
    pFirst n = pVal n := by
  rw [pFirst, pVal]
  -- expand the c-product inside the j-sum via cprod_cauchy
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - cB * qB ^ (k + j))
        = ∑ i ∈ Finset.range n,
            muW n j * (qB ^ (i * (i - 1) / 2) * qBin qB (n - 1) i * (-cB) ^ i * qB ^ ((j + 1) * i)) := by
    intro j _
    rw [cprod_cauchy hn j, Finset.mul_sum]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  -- pull the i-dependent factors out of the j-sum, leaving ∑_j μ_j (qB^j)^i
  have hfac : ∀ j ∈ Finset.Icc 1 n,
      muW n j * (qB ^ (i * (i - 1) / 2) * qBin qB (n - 1) i * (-cB) ^ i * qB ^ ((j + 1) * i))
        = (qB ^ (i * (i - 1) / 2) * qBin qB (n - 1) i * (-cB) ^ i * qB ^ i)
          * (muW n j * (qB ^ j) ^ i) := by
    intro j _
    rw [show (j + 1) * i = i + j * i from by ring, pow_add, pow_mul]
    ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum, qLag i hi]
  rw [show i * (i + 3) / 2 = i * (i - 1) / 2 + 2 * i from (exp_iden i).symm, pow_add]
  ring

/-! ### Assembly building block: the inner tail-sum collapse

In `Eterm n = ∑'_m Iₘ`, after the partial fraction (Piece I) and the `q`-numerator expansion
(`Dterm_expand`), the inner sum over `m ≥ n` of `q^{−i·m}·u_{m+j}` appears. Reindexing onto the
`Tser` grid and applying `Tser_collapse` turns it into `(rational) + (rational)·z`. This is the step
that makes the whole series collapse to `−pVal·z + (rational)`. -/

/-- The inner tail series `∑_{m≥0} q^{−i(n+m)}·u_{(n+m)+j}` appearing in the assembly. -/
noncomputable def Stail (i j n : ℕ) : ℝ :=
  ∑' m : ℕ, (qB ^ (i * (n + m)))⁻¹ * (1 - cB * qB ^ ((n + m) + j))⁻¹

/-- **Tail collapse**: the inner series equals `q^{ij}·(Tser i − head)`, a finite reindex onto the
`Tser` grid. Combined with `Tser_collapse`, this is `q^{ij}·(c^i·z + R_i − head)`. -/
lemma Stail_collapse (i j n : ℕ) (hnj : 1 ≤ n + j) :
    Stail i j n
      = qB ^ (i * j) * (Tser i
          - ∑ m' ∈ Finset.range (n + j - 1),
              (qB ^ (i * (m' + 1)))⁻¹ * (1 - cB * qB ^ (m' + 1))⁻¹) := by
  have hterm : ∀ m : ℕ,
      (qB ^ (i * (n + m)))⁻¹ * (1 - cB * qB ^ ((n + m) + j))⁻¹
        = qB ^ (i * j) * ((qB ^ (i * ((m + (n + j - 1)) + 1)))⁻¹
            * (1 - cB * qB ^ ((m + (n + j - 1)) + 1))⁻¹) := by
    intro m
    have h1 : (m + (n + j - 1)) + 1 = (n + m) + j := by omega
    have hw : (qB ^ (i * (n + m)))⁻¹ = qB ^ (i * j) * (qB ^ (i * ((n + m) + j)))⁻¹ := by
      rw [show i * ((n + m) + j) = i * j + i * (n + m) from by ring, pow_add, mul_inv,
        ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ qB_ne), one_mul]
    rw [h1, hw]; ring
  rw [Stail, tsum_congr hterm, tsum_mul_left]
  congr 1
  have hsum := Summable.sum_add_tsum_nat_add (n + j - 1) (Tser_summable i)
  rw [show Tser i = ∑' m : ℕ, (qB ^ (i * (m + 1)))⁻¹ * (1 - cB * qB ^ (m + 1))⁻¹ from rfl]
  linarith [hsum]

/-- **z-coefficient bridge**: `pFirst` re-expanded over the same subsets `t ⊆ [1,n−1]` that the
`q`-numerator `Dterm_expand` produces. This matches the assembly's z-coefficient
`−∑_t (∏_{k∈t}−q^k)·c^{|t|}·(∑_j μ_j (q^j)^{|t|})` exactly (since `∏_{k∈t}(−c·q^k) = (∏−q^k)·c^{|t|}`),
so the whole double series' z-part is `−pFirst·z = −pVal·z` — **without** needing the `e_i` or
q-Lagrange identities for the z-collection. -/
lemma pFirst_powerset (n : ℕ) :
    pFirst n = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-cB * qB ^ k)) * ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ t.card := by
  rw [pFirst]
  have hexp : ∀ j, ∏ k ∈ Finset.Icc 1 (n - 1), (1 - cB * qB ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-cB * qB ^ k)) * (qB ^ j) ^ t.card := by
    intro j
    have hf : ∀ k, (1 : ℝ) - cB * qB ^ (k + j) = 1 + (-cB * qB ^ k) * qB ^ j := by
      intro k; rw [pow_add]; ring
    rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_one_add]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hexp j])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro j _
  ring

/-! ### Piece I — the partial-fraction decomposition (Aristotle-harvested, verified kernel-clean)

`1/∏_{k=1}^n(1 − x·q^k) = ∑_{j=1}^n μ_j/(1 − x·q^j)` over the `n` distinct simple poles `x = q^{−j}`,
with `μ_j = ∏_{k≠j}(1 − q^k/q^j)⁻¹`. Proved via mathlib's `Lagrange.sum_basis` (the Lagrange basis
polynomials sum to `1`). Aristotle run `70eb84a6`; it correctly flagged that `n = 0` is false and
added `1 ≤ n`. In the assembly, specialize `x = c·q^m` so `1 − x·q^k = 1 − c·q^{m+k}` and
`μ_j = muW n j`. -/

/-- The nodes `(q^k)⁻¹` are pairwise distinct on `Icc 1 n` (for `q > 1`). -/
lemma pf_injOn (q : ℝ) (hq : 1 < q) (n : ℕ) :
    Set.InjOn (fun k => (q ^ k)⁻¹) (↑(Finset.Icc 1 n)) := by
  exact fun x hx y hy hxy => by rw [inv_inj, pow_right_inj₀] at hxy <;> linarith

/-- Per-factor identity bridging the Lagrange-basis factor and the residue factor. -/
lemma pf_factor (q : ℝ) (hq : 1 < q) (x : ℝ) (j k : ℕ) :
    ((q ^ j)⁻¹ - (q ^ k)⁻¹)⁻¹ * (x - (q ^ k)⁻¹)
      = (1 - q ^ k / q ^ j)⁻¹ * (1 - x * q ^ k) := by
  field_simp
  rw [← neg_div_neg_eq, neg_sub, neg_sub]

/-- Cleared form `∑_{j=1}^n μ_j·∏_{k≠j}(1 − x·q^k) = 1` (Lagrange interpolation of the constant 1). -/
lemma pf_cleared (q : ℝ) (hq : 1 < q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ (Finset.Icc 1 n).erase j, (1 - q ^ k / q ^ j)⁻¹)
          * ∏ k ∈ (Finset.Icc 1 n).erase j, (1 - x * q ^ k) = 1 := by
  have h_sum_basis : ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ Finset.erase (Finset.Icc 1 n) j,
        (Polynomial.C ((q ^ j : ℝ)⁻¹ - (q ^ k : ℝ)⁻¹)⁻¹
          * (Polynomial.X - Polynomial.C ((q ^ k : ℝ)⁻¹)))) = 1 := by
    convert Lagrange.sum_basis (pf_injOn q hq n) (Finset.nonempty_Icc.mpr hn) using 1
    simp only [Lagrange.basis, Lagrange.basisDivisor]
  have h_eval : ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ Finset.erase (Finset.Icc 1 n) j,
        ((q ^ j : ℝ)⁻¹ - (q ^ k : ℝ)⁻¹)⁻¹ * (x - (q ^ k : ℝ)⁻¹)) = 1 := by
    convert congr_arg (Polynomial.eval x) h_sum_basis using 1
    · simp +decide [Polynomial.eval_finsetSum, Polynomial.eval_prod]
    · norm_num
  convert h_eval using 2
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [pf_factor q hq x _ _]

/-- **Piece I — partial-fraction decomposition** `∏_{k=1}^n(1 − x·q^k)⁻¹ = ∑_j μ_j (1 − x·q^j)⁻¹`. -/
theorem partial_fraction (q : ℝ) (hq : 1 < q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : ∀ k, 1 ≤ k → k ≤ n → 1 - x * q ^ k ≠ 0) :
    (∏ k ∈ Finset.Icc 1 n, (1 - x * q ^ k))⁻¹
      = ∑ j ∈ Finset.Icc 1 n,
          (∏ k ∈ (Finset.Icc 1 n).erase j, (1 - q ^ k / q ^ j)⁻¹) * (1 - x * q ^ j)⁻¹ := by
  convert (Eq.symm ?_) using 1
  convert congr_arg (fun y => y * (∏ k ∈ Finset.Icc 1 n, (1 - x * q ^ k))⁻¹)
    (pf_cleared q hq n hn x) using 1
  · rw [Finset.sum_mul _ _ _]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.prod_erase_mul _ _ hj, mul_assoc, mul_comm]
    simp +decide [mul_assoc, mul_comm, mul_left_comm]
    exact Or.inl (by rw [← mul_assoc, mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k hk =>
      hx k (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hk) |>.1)
        (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hk) |>.2)), one_mul])
  · ring

/-! ### Negative-base (`1 < |q|`) partial-fraction decomposition.

Parallel to `pf_injOn`/`pf_factor`/`pf_cleared`/`partial_fraction`, but with the hypothesis weakened
from `1 < q` to `1 < |q|` so it covers negative bases `q ≤ −2`. The only sign-dependent step is node
distinctness (`pf_injOn_abs`), proved via strict monotonicity of `k ↦ |q|^k`; everything else is the
same Lagrange-basis argument. These feed the negative-base residue identity (`ItermG_triple` for
`1 < |q|` in `GeneralResidue.lean`). Left untouched: the `1 < q` originals (the kernel-clean q=2
`erdos_1050` chain routes through those). -/

/-- The nodes `(q^k)⁻¹` are pairwise distinct on `Icc 1 n` for `1 < |q|` (any sign of `q`). -/
lemma pf_injOn_abs (q : ℝ) (hq : 1 < |q|) (n : ℕ) :
    Set.InjOn (fun k => (q ^ k)⁻¹) (↑(Finset.Icc 1 n)) := by
  intro x _ y _ hxy
  simp only [inv_inj] at hxy
  have habs : |q| ^ x = |q| ^ y := by rw [← abs_pow, ← abs_pow, hxy]
  exact (StrictMono.injective (fun a b h => pow_lt_pow_right₀ hq h)) habs

/-- Per-factor identity bridging the Lagrange-basis factor and the residue factor (`q ≠ 0`). -/
lemma pf_factor_abs (q : ℝ) (hq0 : q ≠ 0) (x : ℝ) (j k : ℕ) :
    ((q ^ j)⁻¹ - (q ^ k)⁻¹)⁻¹ * (x - (q ^ k)⁻¹)
      = (1 - q ^ k / q ^ j)⁻¹ * (1 - x * q ^ k) := by
  have hj : (q ^ j : ℝ) ≠ 0 := pow_ne_zero _ hq0
  have hk : (q ^ k : ℝ) ≠ 0 := pow_ne_zero _ hq0
  field_simp
  rw [← neg_div_neg_eq, neg_sub, neg_sub]

/-- Cleared form `∑_{j} μ_j·∏_{k≠j}(1 − x·q^k) = 1` for `1 < |q|`. -/
lemma pf_cleared_abs (q : ℝ) (hq : 1 < |q|) (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ (Finset.Icc 1 n).erase j, (1 - q ^ k / q ^ j)⁻¹)
          * ∏ k ∈ (Finset.Icc 1 n).erase j, (1 - x * q ^ k) = 1 := by
  have hq0 : q ≠ 0 := by intro h; rw [h, abs_zero] at hq; linarith
  have h_sum_basis : ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ Finset.erase (Finset.Icc 1 n) j,
        (Polynomial.C ((q ^ j : ℝ)⁻¹ - (q ^ k : ℝ)⁻¹)⁻¹
          * (Polynomial.X - Polynomial.C ((q ^ k : ℝ)⁻¹)))) = 1 := by
    convert Lagrange.sum_basis (pf_injOn_abs q hq n) (Finset.nonempty_Icc.mpr hn) using 1
    simp only [Lagrange.basis, Lagrange.basisDivisor]
  have h_eval : ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ Finset.erase (Finset.Icc 1 n) j,
        ((q ^ j : ℝ)⁻¹ - (q ^ k : ℝ)⁻¹)⁻¹ * (x - (q ^ k : ℝ)⁻¹)) = 1 := by
    convert congr_arg (Polynomial.eval x) h_sum_basis using 1
    · simp +decide [Polynomial.eval_finsetSum, Polynomial.eval_prod]
    · norm_num
  convert h_eval using 2
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [pf_factor_abs q hq0 x _ _]

/-- **Piece I — partial-fraction decomposition for `1 < |q|`** (negative base allowed). -/
theorem partial_fraction_abs (q : ℝ) (hq : 1 < |q|) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : ∀ k, 1 ≤ k → k ≤ n → 1 - x * q ^ k ≠ 0) :
    (∏ k ∈ Finset.Icc 1 n, (1 - x * q ^ k))⁻¹
      = ∑ j ∈ Finset.Icc 1 n,
          (∏ k ∈ (Finset.Icc 1 n).erase j, (1 - q ^ k / q ^ j)⁻¹) * (1 - x * q ^ j)⁻¹ := by
  convert (Eq.symm ?_) using 1
  convert congr_arg (fun y => y * (∏ k ∈ Finset.Icc 1 n, (1 - x * q ^ k))⁻¹)
    (pf_cleared_abs q hq n hn x) using 1
  · rw [Finset.sum_mul _ _ _]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.prod_erase_mul _ _ hj, mul_assoc, mul_comm]
    simp +decide [mul_assoc, mul_comm, mul_left_comm]
    exact Or.inl (by rw [← mul_assoc, mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k hk =>
      hx k (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hk) |>.1)
        (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hk) |>.2)), one_mul])
  · ring

/-! ### Final assembly: `Eterm n = −pVal n · zB + (rational)`

Combine all pieces. First `Iterm_triple` rewrites each `Iₘ` as a finite double sum (over subsets `t`
of the `q`-numerator and poles `j` of the partial fraction). Then `Eterm_eq_Stail` pulls the two
finite sums out of `∑'_m` (each inner series is `Stail`). Finally `Stail_collapse` + `Tser_collapse`
+ `pFirst_powerset` collect the z-coefficient as `−pFirst = −pVal`. -/

/-- Each `Iₘ` (here `M` general) as a finite double sum over subsets `t ⊆ [1,n−1]` and poles
`j ∈ [1,n]`, via `Iterm_prod_form` (split) + `partial_fraction` (Piece I) + `Dterm_expand`. -/
lemma Iterm_triple {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    Iterm n M
      = -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
          (∏ k ∈ t, (-qB ^ k)) * muW n j
            * (((qB ^ M)⁻¹) ^ t.card * (1 - cB * qB ^ (M + j))⁻¹) := by
  have hpm : ∀ a : ℕ, cB * qB ^ M * qB ^ a = cB * qB ^ (M + a) := by
    intro a; rw [pow_add]; ring
  have hC : ∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ ((k : ℤ) + M))⁻¹
      = ∑ j ∈ Finset.Icc 1 n, muW n j * (1 - cB * qB ^ (M + j))⁻¹ := by
    have hconv : ∀ k : ℕ, (1 : ℝ) - cB * qB ^ ((k : ℤ) + M) = 1 - cB * qB ^ M * qB ^ k := by
      intro k
      have he : ((k : ℤ) + M) = ((k + M : ℕ) : ℤ) := by push_cast; ring
      rw [he, zpow_natCast, pow_add]; ring
    have hx : ∀ k, 1 ≤ k → k ≤ n → 1 - cB * qB ^ M * qB ^ k ≠ 0 := by
      intro k _ _; rw [hpm k]; exact one_sub_cqpow_ne (by omega)
    have hprodeq : ∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ ((k : ℤ) + M))⁻¹
        = (∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ M * qB ^ k))⁻¹ := by
      simp only [hconv, Finset.prod_inv_distrib]
    rw [hprodeq, partial_fraction qB one_lt_qB n hn (cB * qB ^ M) hx]
    apply Finset.sum_congr rfl
    intro j _
    rw [hpm j]
    rfl
  rw [Iterm_prod_form n M hn, hC, Dterm_expand n M]
  rw [Finset.sum_mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- `Stail`'s summand is summable (dominated by the geometric `(1/2)^m`). -/
lemma Stail_summable {n : ℕ} (hn : 1 ≤ n) (i j : ℕ) :
    Summable (fun m : ℕ => (qB ^ (i * (n + m)))⁻¹ * (1 - cB * qB ^ ((n + m) + j))⁻¹) := by
  apply Summable.of_norm_bounded (g := fun m => (1 / 2 : ℝ) ^ m)
  · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  · intro m
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |(qB ^ (i * (n + m)))⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt qB_pos) _))]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt one_lt_qB))
    have h2 : |(1 - cB * qB ^ ((n + m) + j))⁻¹| ≤ qB ^ (-(((n + m) + j : ℕ) : ℤ)) := by
      have h := inv_cqpow_le (a := (((n + m) + j : ℕ) : ℤ)) (by exact_mod_cast (by omega : 1 ≤ (n + m) + j))
      rwa [zpow_natCast] at h
    have h3 : qB ^ (-(((n + m) + j : ℕ) : ℤ)) ≤ (1 / 2 : ℝ) ^ m := by
      rw [show (-(((n + m) + j : ℕ) : ℤ)) = -((m : ℤ) + (n + j)) from by push_cast; ring]
      calc qB ^ (-((m : ℤ) + (n + j))) ≤ qB ^ (-(m : ℤ)) :=
            zpow_le_zpow_right₀ (le_of_lt one_lt_qB) (by omega)
        _ = (1 / 2 : ℝ) ^ m := qB_neg_zpow m
    calc |(qB ^ (i * (n + m)))⁻¹| * |(1 - cB * qB ^ ((n + m) + j))⁻¹|
        ≤ 1 * qB ^ (-(((n + m) + j : ℕ) : ℤ)) := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ ≤ (1 / 2 : ℝ) ^ m := by rw [one_mul]; exact h3

/-- **The pull-out**: `Eterm n` as a finite double sum of `Stail`'s, via `Iterm_triple` and pulling
the two finite sums out of `∑'_m` (`Summable.tsum_finsetSum`). -/
lemma Eterm_eq_Stail {n : ℕ} (hn : 1 ≤ n) :
    Eterm n = -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-qB ^ k)) * muW n j * Stail t.card j n := by
  have hStail : ∀ (t : Finset ℕ) (j : ℕ),
      (fun m : ℕ => (∏ k ∈ t, (-qB ^ k)) * muW n j
          * (((qB ^ (n + m))⁻¹) ^ t.card * (1 - cB * qB ^ ((n + m) + j))⁻¹))
        = (fun m : ℕ => (∏ k ∈ t, (-qB ^ k)) * muW n j
          * ((qB ^ (t.card * (n + m)))⁻¹ * (1 - cB * qB ^ ((n + m) + j))⁻¹)) := by
    intro t j; funext m
    rw [inv_pow, ← pow_mul, mul_comm (n + m) t.card]
  -- summability of each constant-scaled Stail summand
  have hsum : ∀ (t : Finset ℕ) (j : ℕ), Summable (fun m : ℕ =>
      (∏ k ∈ t, (-qB ^ k)) * muW n j
        * (((qB ^ (n + m))⁻¹) ^ t.card * (1 - cB * qB ^ ((n + m) + j))⁻¹)) := by
    intro t j
    rw [hStail t j]
    exact ((Stail_summable hn t.card j).mul_left _)
  rw [Eterm, tsum_congr (fun m => Iterm_triple hn (n + m)), tsum_neg]
  congr 1
  rw [Summable.tsum_finsetSum (fun t _ => summable_sum (fun j _ => hsum t j))]
  apply Finset.sum_congr rfl; intro t _
  rw [Summable.tsum_finsetSum (fun j _ => hsum t j)]
  apply Finset.sum_congr rfl; intro j _
  rw [hStail t j, tsum_mul_left]
  congr 1

/-- The finite rational "head" removed when reindexing `Stail` onto the `Tser` grid. -/
noncomputable def headS (i j n : ℕ) : ℝ :=
  ∑ m' ∈ Finset.range (n + j - 1), (qB ^ (i * (m' + 1)))⁻¹ * (1 - cB * qB ^ (m' + 1))⁻¹

/-- The explicit **rational correction** `Aₙ` of the residue identity `Eₙ = −pFirst·z + Aₙ`. -/
noncomputable def Acorr (n : ℕ) : ℝ :=
  -∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
    (∏ k ∈ t, (-qB ^ k)) * muW n j
      * (qB ^ (t.card * j) * (Rrat t.card - headS t.card j n))

/-- **The residue identity** (contour-free, elementary): `Eₙ = −pFirst n · z + Aₙ`, with `Aₙ` an
explicit rational. Assembled from `Eterm_eq_Stail` (pull-out) + `Stail_collapse` (reindex) +
`Tser_collapse` (Piece II) + `pFirst_powerset` (z-coefficient). This is Borwein's Lemma 1 with the
first-form denominator `pFirst`; `pFirst_eq_pVal` (Piece III, mod q-Lagrange) connects it to `pVal`. -/
theorem Eterm_eq_pFirst {n : ℕ} (hn : 1 ≤ n) :
    Eterm n = -pFirst n * zB + Acorr n := by
  have key : ∀ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∀ j ∈ Finset.Icc 1 n,
      (∏ k ∈ t, (-qB ^ k)) * muW n j * Stail t.card j n
        = ((∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * cB ^ t.card)) * zB
          + (∏ k ∈ t, (-qB ^ k)) * muW n j
              * (qB ^ (t.card * j) * (Rrat t.card - headS t.card j n)) := by
    intro t _ j _
    rw [Stail_collapse t.card j n (by omega), Tser_collapse]
    rw [headS]
    ring
  -- z-coefficient (summed over t,j) equals pFirst n
  have hzcoef : ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
      (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * cB ^ t.card) = pFirst n := by
    rw [pFirst_powerset n]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hpt : ∏ k ∈ t, (-cB * qB ^ k) = cB ^ t.card * ∏ k ∈ t, (-qB ^ k) := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun k _ => by ring)
    have hqp : ((qB ^ j) ^ t.card : ℝ) = qB ^ (t.card * j) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hpt, hqp]; ring
  rw [Eterm_eq_Stail hn,
    Finset.sum_congr rfl (fun t ht => Finset.sum_congr rfl (fun j hj => key t ht j hj))]
  simp_rw [Finset.sum_add_distrib]
  rw [neg_add, Acorr]
  congr 1
  rw [← hzcoef, neg_mul]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_mul]

/-- **Residue identity with the `pVal` denominator** (`Eₙ = −pVal n · z + Aₙ`), conditional on the
q-Lagrange identity `qLag` (Piece IIIb). This is exactly the shape the `residue_open` assumption feeds;
once `qLag` is discharged (Aristotle `aristotle/QLagrange.lean`) and the numerator integrality
`β^{2n}·Wₙ·Aₙ ∈ ℤ` (Borwein Lemma 3) is proved, `residue_open` becomes a theorem and `erdos_1050`
is kernel-clean. -/
theorem Eterm_eq_pVal {n : ℕ} (hn : 1 ≤ n)
    (qLag : ∀ i, i < n →
      ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ i = qB ^ i * qBin qB (n + i - 1) (n - 1)) :
    Eterm n = -pVal n * zB + Acorr n := by
  rw [Eterm_eq_pFirst hn, pFirst_eq_pVal hn qLag]

/-! ### Toward Lemma 3 (numerator integrality): denominator-exposing forms

`Acorr`'s denominators come from `muW`, `Rrat`, `headS`. The first building block: the q-Lagrange
weight `μ_j` as `(q^j)^{n-1} / ∏_{l≠j}(q^j − q^l)` — a single explicit denominator `∏_{l≠j}(q^j−q^l)`
(a Vandermonde-type product). The eventual integrality argument shows `β^{2n}·Wₙ` clears these. -/

/-- `q^j − q^l ≠ 0` for `j ≠ l` (q-powers are distinct since `q > 1`). -/
lemma qpow_sub_ne {j l : ℕ} (hlj : l ≠ j) : (qB ^ j - qB ^ l : ℝ) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  apply hlj
  rcases Nat.lt_trichotomy l j with hlt | heq | hgt
  · exact absurd h.symm (ne_of_lt (pow_lt_pow_right₀ one_lt_qB hlt))
  · exact heq
  · exact absurd h (ne_of_lt (pow_lt_pow_right₀ one_lt_qB hgt))

/-- **Denominator-exposing closed form** of the q-Lagrange weight:
`μ_j = (q^j)^{|erase j|} · (∏_{l≠j}(q^j − q^l))⁻¹`. -/
lemma muW_closed (n j : ℕ) :
    muW n j = (qB ^ j) ^ ((Finset.Icc 1 n).erase j).card
      * (∏ l ∈ (Finset.Icc 1 n).erase j, (qB ^ j - qB ^ l))⁻¹ := by
  rw [muW]
  have hfac : ∀ l ∈ (Finset.Icc 1 n).erase j,
      (1 - qB ^ l / qB ^ j)⁻¹ = qB ^ j * (qB ^ j - qB ^ l)⁻¹ := by
    intro l hl
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hjne : (qB ^ j : ℝ) ≠ 0 := pow_ne_zero _ qB_ne
    have hsub : (qB ^ j - qB ^ l : ℝ) ≠ 0 := qpow_sub_ne hlj
    rw [show (1 - qB ^ l / qB ^ j : ℝ) = (qB ^ j - qB ^ l) / qB ^ j from by field_simp,
      inv_div, div_eq_mul_inv]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
    ← Finset.prod_inv_distrib]

/-- **Closed form of the rational correction term** `Rrat i = ∑_{l=1}^i c^{i-l}/(q^l − 1)`, exposing
its denominators `(q^l − 1)` and the `c`-powers (which clear under `3^{…}`). -/
lemma Rrat_closed (i : ℕ) : Rrat i = ∑ l ∈ Finset.Icc 1 i, cB ^ (i - l) / (qB ^ l - 1) := by
  induction i with
  | zero => simp [Rrat]
  | succ i ih =>
    rw [show Rrat (i + 1) = 1 / (qB ^ (i + 1) - 1) + cB * Rrat i from rfl, ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ i + 1), Nat.sub_self, pow_zero, Finset.mul_sum,
      add_comm (1 / (qB ^ (i + 1) - 1))]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mem_Icc] at hl
    rw [show (i + 1) - l = (i - l) + 1 from by omega, pow_succ]
    ring

/-- **`headS` with integer denominators exposed**: each factor `(1 − c·q^{m'+1})⁻¹` clears to
`3·(3 − 8·q^{m'+1})⁻¹` (`c = 8/3`), surfacing the integer denominators `3 − 8·2^{m'+1}` (the same
factors as `CPint`) that `Wₙ`'s `∏(1 − c·q^k)` clears. -/
lemma headS_clear (i j n : ℕ) :
    headS i j n = ∑ m' ∈ Finset.range (n + j - 1),
      3 * (qB ^ (i * (m' + 1)))⁻¹ * (3 - 8 * qB ^ (m' + 1))⁻¹ := by
  rw [headS]
  apply Finset.sum_congr rfl
  intro m' _
  have h : (1 - cB * qB ^ (m' + 1))⁻¹ = 3 * (3 - 8 * qB ^ (m' + 1))⁻¹ := by
    rw [show (1 - cB * qB ^ (m' + 1) : ℝ) = (3 - 8 * qB ^ (m' + 1)) / 3 from by
      simp only [cB]; ring, inv_div, div_eq_mul_inv]
  rw [h]; ring

end

/-! ### Upstream module `Integrality.lean` -/

section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-!
# Denominator integrality (Borwein Lemma 2) + the q-Lagrange identity

Part of the now-complete, **kernel-clean** proof of Erdős #1050 (kernel check =
[propext, Classical.choice, Quot.sound]`). This file machine-checks **Borwein Lemma 2** (integrality of
the q-Padé denominator `pₙ`) and pins the approximant to the actual Padé denominator `pVal`: the
coefficient `β^{2n}·Wₙ·pVal n` is the PROVEN integer `Bden n` (`Bden_cast`), built from `pInt`
(Lemma 2 via the Cauchy q-binomial theorem `qBin_cauchy`) and the 3-power / 2-power clearings of `Wₙ`.
It also derives `qLag_thm` (the q-Lagrange identity at `q = 2`) from `qLagrange` (`QLagrange.lean`).

The downstream chain `borwein_integrality → irrational_zB → erdos_1050` lives in `Lemma3.lean` (after
the elementary Lemma-3 machinery, which is what made the whole proof kernel-clean).
-/


open scoped BigOperators
open Filter Topology

/-- The `3^n`-cleared `c`-product `∏_{k=1}^n (3 − 8·2^k) ∈ ℤ` (clears `∏(1 − c·q^k)`, `c = 8/3`). -/
def CPint (n : ℕ) : ℤ := ∏ k ∈ Finset.Icc 1 n, (3 - 8 * 2 ^ k)

/-- The integer `q`-product `∏_{k=⌈n/2⌉}^n (1 − 2^k) ∈ ℤ` (equals `∏(1 − q^k)`, `q = 2`). -/
def QPint (n : ℕ) : ℤ := ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - 2 ^ k)

/-- The cleared **integer denominator** `β^{2n}·Wₙ·pₙ`, assembled from the factorial, the cleared
products, and the cleared Padé denominator `pInt`. -/
def Bden (n : ℕ) : ℤ :=
  3 * (Nat.factorial (n - 2)) * CPint n * QPint n * pInt n

/-- `(CPint n : ℝ) = 3^n · ∏_{k=1}^n (1 − c·q^k)`. -/
lemma CPint_cast (n : ℕ) :
    (CPint n : ℝ) = 3 ^ n * ∏ k ∈ Finset.Icc 1 n, (1 - cB * qB ^ k) := by
  have hcard : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
  rw [CPint]
  push_cast
  rw [show (3 : ℝ) ^ n = ∏ _k ∈ Finset.Icc 1 n, (3 : ℝ) from by rw [Finset.prod_const, hcard],
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  simp only [cB, qB]; ring

/-- `(QPint n : ℝ) = ∏_{k=⌈n/2⌉}^n (1 − q^k)`. -/
lemma QPint_cast (n : ℕ) :
    (QPint n : ℝ) = ∏ k ∈ Finset.Icc ((n + 1) / 2) n, (1 - qB ^ k) := by
  rw [QPint]
  push_cast
  apply Finset.prod_congr rfl
  intro k _
  simp only [qB]

/-- **Denominator integrality (Borwein Lemma 2, USED).** `(Bden n : ℝ) = β^{2n}·Wₙ·pVal n`, so the
Padé denominator coefficient is a machine-checked integer. -/
lemma Bden_cast {n : ℕ} (hn : 1 ≤ n) :
    (Bden n : ℝ) = (βB : ℝ) ^ (2 * n) * Wterm n * pVal n := by
  have hb : (βB : ℝ) ^ (2 * n) = 3 ^ (2 * n) := by simp [βB]
  have key : (3 : ℝ) * 3 ^ n * 3 ^ (n - 1) = 3 ^ (2 * n) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, show 2 * (m + 1) = (m + 1) + m + 1 from by ring,
      pow_add, pow_add, pow_one]
    ring
  rw [Bden]
  push_cast
  rw [CPint_cast, QPint_cast, pInt_cast, Wterm, hb]
  rw [← key]
  ring

/-- **The q-Lagrange identity (Piece IIIb), now a THEOREM.** `∑_j μ_j (q^j)^i = q^i·[n+i−1,n−1]_q`
for `i < n`. This was the first clause of the former `residue_open` assumption; it is now discharged by
`qLagrange` (auto-formalized by Aristotle, ported + verified kernel-clean in `QLagrange.lean`),
specialized to `q = qB = 2`. It discharges `pFirst_eq_pVal`'s hypothesis, making `Eterm_eq_pVal`
unconditional. -/
theorem qLag_thm {n : ℕ} (hn : 1 ≤ n) (i : ℕ) (hi : i < n) :
    ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ i = qB ^ i * qBin qB (n + i - 1) (n - 1) := by
  have h := qLagrange qB one_lt_qB n hn i (by omega)
  simpa only [muW] using h

/- **Numerator integrality (Borwein Lemma 3)** is proved elementarily in `Lemma3.lean`, where the
downstream chain `borwein_integrality → irrational_zB → erdos_1050` is also assembled (it needs the
Lemma-3 machinery). With Lemma 3 machine-checked there, `erdos_1050` is kernel-clean. -/

end

/-! ### Upstream module `Lemma3.lean` -/

section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-!
# Borwein Lemma 3 (numerator integrality) — elementary route

Discharges `residue_open`'s second clause: `∃ a:ℕ→ℤ, ∀ n≥1, (a n:ℝ) = −β^{2n}·Wₙ·Acorr n`.

See `LEMMA3-ELEMENTARY-STRATEGY.md`. The key simplification over Borwein's residue/derivative proof:
the same q-Lagrange identity that gives `pFirst = pVal` also clears the Vandermonde `μ_j`
denominators in the numerator. This file builds the clearing infrastructure bottom-up.

## Section 1: the `QPint` divisibility (number-theoretic clearing of `Rrat`'s `q^l−1` denominators)
-/


open scoped BigOperators

/-- For `1 ≤ l ≤ n` the interval `[⌈n/2⌉, n]` (here `⌈n/2⌉ = (n+1)/2`) contains a multiple of `l`.
Either `l` is small enough that the interval (length `⌊(n+1)/2⌋ ≥ l`) spans a full residue cycle, or
`l` itself lies in `[⌈n/2⌉, n]`. -/
lemma interval_has_multiple {l n : ℕ} (hl : 1 ≤ l) (hln : l ≤ n) :
    ∃ k ∈ Finset.Icc ((n + 1) / 2) n, l ∣ k := by
  -- largest multiple of `l` not exceeding `n`
  have hdiv : n = l * (n / l) + n % l := (Nat.div_add_mod n l).symm
  have hmod : n % l < l := Nat.mod_lt n (by omega)
  have h1 : 1 ≤ n / l := (Nat.one_le_div_iff (by omega)).mpr hln
  have h2 : l ≤ l * (n / l) := Nat.le_mul_of_pos_right l h1
  refine ⟨l * (n / l), Finset.mem_Icc.mpr ⟨?_, by omega⟩, Dvd.intro _ rfl⟩
  -- `l * (n/l) ≥ (n+1)/2`: either `l` small (interval spans a full cycle) or `l` itself qualifies
  by_cases hsmall : l ≤ (n + 1) / 2
  · omega
  · omega

/-- `(2^l − 1) ∣ (2^k − 1)` in `ℤ` whenever `l ∣ k`. -/
lemma two_pow_sub_one_dvd {l k : ℕ} (h : l ∣ k) :
    ((2 : ℤ) ^ l - 1) ∣ ((2 : ℤ) ^ k - 1) := by
  obtain ⟨s, rfl⟩ := h
  have := sub_dvd_pow_sub_pow ((2 : ℤ) ^ l) 1 s
  simpa [pow_mul] using this

/-- **`QPint` divisibility.** For `1 ≤ l ≤ n−1`, `(2^l − 1) ∣ QPint n`. This clears `Rrat`'s
denominators `q^l − 1` (Borwein's note: `(1−q^m) | ∏_{k=⌈n/2⌉}^n (1−q^k)`). -/
lemma QPint_dvd {l n : ℕ} (hl : 1 ≤ l) (hln : l ≤ n - 1) :
    ((2 : ℤ) ^ l - 1) ∣ QPint n := by
  have hln' : l ≤ n := by omega
  obtain ⟨k, hk, hdvd⟩ := interval_has_multiple hl hln'
  have hfactor : ((2 : ℤ) ^ k - 1) ∣ QPint n := by
    have hmem : (1 - 2 ^ k) ∈ (Finset.Icc ((n + 1) / 2) n).image (fun k => (1 - 2 ^ k : ℤ)) := by
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    rw [QPint]
    have : ((2 : ℤ) ^ k - 1) ∣ (1 - 2 ^ k) := ⟨-1, by ring⟩
    exact this.trans (Finset.dvd_prod_of_mem _ hk)
  exact (two_pow_sub_one_dvd hdvd).trans hfactor

/-! ## Section 2: reorganizing `Acorr`'s headS-part

The headS-part of `Acorr` is `∑_t (∏_{k∈t}-q^k) ∑_j muW n j q^{|t|j} headS|t| j n`. Summing the
subset `t` first turns the inner factor into `∏_{k=1}^{n-1}(1-q^{k+j-h})`, which vanishes for `h>j`,
so the head sum truncates. See `LEMMA3-ELEMENTARY-STRATEGY.md`. -/

/-- `headS` with the inner sum reindexed from `range (n+j-1)` to `Icc 1 (n+j-1)` (set `h = m'+1`). -/
lemma headS_Icc (i j n : ℕ) :
    headS i j n = ∑ h ∈ Finset.Icc 1 (n + j - 1), (qB ^ (i * h))⁻¹ * (1 - cB * qB ^ h)⁻¹ := by
  rw [headS, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro m' _
  rw [Nat.add_comm 1 m']

/-- **Subset-product collapse** (signed, with a scalar `w`): `∑_{t⊆[1,m]} (∏_{k∈t}-q^k)·w^{|t|}
= ∏_{k=1}^m (1 - q^k·w)`. The engine of the headS reorganization (reverse of `Dterm_expand`). -/
lemma subset_prod_local (w : ℝ) (m : ℕ) :
    ∑ t ∈ (Finset.Icc 1 m).powerset, (∏ k ∈ t, (-qB ^ k)) * w ^ t.card
      = ∏ k ∈ Finset.Icc 1 m, (1 - qB ^ k * w) := by
  have hf : ∀ k, (1 : ℝ) - qB ^ k * w = 1 + (-qB ^ k) * w := by intro k; ring
  rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- `qB^{t·j}·(qB^{t·h})⁻¹ = (qB^{j−h})^t` (mixing nat powers and a zpow base). -/
lemma wpow (j h t : ℕ) : (qB ^ (t * j) : ℝ) * (qB ^ (t * h))⁻¹ = (qB ^ ((j : ℤ) - h)) ^ t := by
  rw [← zpow_natCast (qB ^ ((j : ℤ) - h)) t, ← zpow_mul, ← zpow_natCast qB (t * j),
    ← zpow_natCast qB (t * h), ← zpow_neg, ← zpow_add₀ qB_ne]
  congr 1
  push_cast; ring

/-- **Per-`j` headS reorganization.** Summing the subset `t ⊆ [1,n−1]` first collapses the headS-part
into a single product `∏_{k=1}^{n−1}(1−q^{k+j−h})` over the head index `h`:

`∑_t (∏_{k∈t}−q^k)·(q^{|t|·j}·headS|t| j n) = ∑_{h=1}^{n+j−1} u_h·∏_{k=1}^{n−1}(1−q^{k+j−h})`,
`u_h = (1−c·q^h)⁻¹`. -/
lemma headPart_inner (n j : ℕ) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-qB ^ k)) * (qB ^ (t.card * j) * headS t.card j n)
      = ∑ h ∈ Finset.Icc 1 (n + j - 1),
        (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  -- substitute headS_Icc and distribute the t-term over the h-sum
  have hstep : ∀ t ∈ (Finset.Icc 1 (n - 1)).powerset,
      (∏ k ∈ t, (-qB ^ k)) * (qB ^ (t.card * j) * headS t.card j n)
        = ∑ h ∈ Finset.Icc 1 (n + j - 1),
            (1 - cB * qB ^ h)⁻¹ * ((∏ k ∈ t, (-qB ^ k)) * (qB ^ ((j : ℤ) - h)) ^ t.card) := by
    intro t _
    rw [headS_Icc, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [← wpow j h t.card]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  have hprod : (∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)))
      = ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ k * qB ^ ((j : ℤ) - h)) := by
    apply Finset.prod_congr rfl
    intro k _
    rw [← zpow_natCast qB k, ← zpow_add₀ qB_ne]
    congr 2
    ring
  rw [hprod, ← subset_prod_local (qB ^ ((j : ℤ) - h)) (n - 1), Finset.mul_sum]

/-- The full headS-part of `Acorr`, reorganized: pull `muW n j` out and apply `headPart_inner`. -/
lemma AccH_reorg (n : ℕ) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * headS t.card j n)
      = ∑ j ∈ Finset.Icc 1 n, muW n j *
          ∑ h ∈ Finset.Icc 1 (n + j - 1),
            (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← headPart_inner n j, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- **`Acorr` reorganized** into its Rrat-part (first sum) and the reorganized headS-part (second
sum). The headS-part's high-`h` heads have cancelled (via `headPart_inner`'s product collapse). -/
lemma Acorr_reorg (n : ℕ) :
    Acorr n = -(∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                  (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * Rrat t.card))
              + ∑ j ∈ Finset.Icc 1 n, muW n j *
                  ∑ h ∈ Finset.Icc 1 (n + j - 1),
                    (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  have key : (∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * Rrat t.card))
              - (∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * headS t.card j n))
            = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
                (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * (Rrat t.card - headS t.card j n)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro t _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [Acorr, ← key, AccH_reorg]
  abel

/-! ## Section 3: head truncation + q-Lagrange clearing

`head_truncate` (auto-formalized by Aristotle, run `332e491b`, verified kernel-clean) removes the
high-`h` heads `h ∈ [j+1, n+j−1]` (the product `∏(1−q^{k+j−h})` vanishes there). The surviving
`∑_{h=1}^j` then re-indexes (j,h)-swap with the j-sum extended to `[1,n]` (the added `j<h` terms also
vanish), exposing the q-Lagrange combination `N_h = ∑_j muW n j ∏(1−q^{k+j−h}) ∈ ℤ`. -/

/-- **Head truncation** (Aristotle `332e491b`): for `1 ≤ n`, the head sum over `h ∈ [1, n+j−1]`
truncates to `h ∈ [1, j]` because the product `∏_{k=1}^{n−1}(1−q^{k+j−h})` vanishes for `h > j`
(the `k = h−j ∈ [1,n−1]` factor is `1 − q^0 = 0`). -/
theorem head_truncate (q : ℝ) (u : ℕ → ℝ) (n j : ℕ) (hn : 1 ≤ n) :
    ∑ h ∈ Finset.Icc 1 (n + j - 1),
        u h * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h))
      = ∑ h ∈ Finset.Icc 1 j,
        u h * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - q ^ ((k : ℤ) + j - h)) := by
  rw [ ← Finset.sum_subset ( Finset.Icc_subset_Icc_right ( show j ≤ n + j - 1 from Nat.le_sub_one_of_lt ( by omega ) ) ) ];
  intros x hx hnx
  obtain ⟨k, hk⟩ : ∃ k ∈ Finset.Icc 1 (n - 1), (k : ℤ) + j - x = 0 := by
    exact ⟨ x - j, Finset.mem_Icc.mpr ⟨ Nat.sub_pos_of_lt <| lt_of_not_ge fun h => hnx <| Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], h ⟩, Nat.sub_le_of_le_add <| by linarith [ Finset.mem_Icc.mp hx, Nat.sub_add_cancel <| show 1 ≤ n from hn, Nat.sub_add_cancel <| show 1 ≤ n + j from by linarith ] ⟩, by rw [ Nat.cast_sub <| by linarith [ Finset.mem_Icc.mp hx, not_le.mp fun h => hnx <| Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], h ⟩ ] ] ; ring ⟩;
  rw [ Finset.prod_eq_zero hk.1 ] <;> aesop

/-- The product `∏_{k=1}^{n−1}(1−q^{k+j−h})` vanishes for `j < h ≤ n` (the `k = h−j ∈ [1,n−1]`
factor is `1 − q^0 = 0`). Used to extend partial `j`-sums to full ones. -/
lemma prod_vanish {n j h : ℕ} (hj : 1 ≤ j) (hjh : j < h) (hhn : h ≤ n) :
    ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) = 0 := by
  apply Finset.prod_eq_zero (i := h - j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have : ((h - j : ℕ) : ℤ) + j - h = 0 := by
    rw [Nat.cast_sub (by omega)]; ring
  rw [this, zpow_zero, sub_self]

/-- **headS-part in `N_h` form.** After truncation (`head_truncate`) the (j,h)-sum swaps and the
inner `j`-sum extends to `[1,n]` (the added `j<h` terms vanish by `prod_vanish`), exposing the
q-Lagrange combination `N_h = ∑_j muW n j ∏_{k=1}^{n−1}(1−q^{k+j−h})`:

`∑_j muW n j ∑_{h=1}^{n+j−1} u_h ∏(…) = ∑_{h=1}^n u_h · (∑_j muW n j ∏(…))`. -/
lemma headSPart_NhForm (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n, muW n j *
        ∑ h ∈ Finset.Icc 1 (n + j - 1),
          (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))
      = ∑ h ∈ Finset.Icc 1 n, (1 - cB * qB ^ h)⁻¹ *
          ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  -- Step 1: truncate each head sum to h ≤ j, and bring muW inside.
  have h1 : ∀ j ∈ Finset.Icc 1 n,
      muW n j * ∑ h ∈ Finset.Icc 1 (n + j - 1),
          (1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))
        = ∑ h ∈ Finset.Icc 1 j,
            muW n j * ((1 - cB * qB ^ h)⁻¹ * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))) := by
    intro j _
    rw [head_truncate qB (fun h => (1 - cB * qB ^ h)⁻¹) n j hn, Finset.mul_sum]
  rw [Finset.sum_congr rfl h1]
  -- Step 2: swap the triangular double sum ∑_{j} ∑_{h≤j} = ∑_{h} ∑_{j≥h}.
  rw [Finset.sum_comm' (s := Finset.Icc 1 n) (t := fun j => Finset.Icc 1 j)
        (t' := Finset.Icc 1 n) (s' := fun h => Finset.Icc h n)
        (by intro j h
            show (j ∈ Finset.Icc 1 n ∧ h ∈ Finset.Icc 1 j)
              ↔ (j ∈ Finset.Icc h n ∧ h ∈ Finset.Icc 1 n)
            simp only [Finset.mem_Icc]; omega)]
  -- Step 3: extend the inner j-sum to [1,n] and pull u_h out.
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mem_Icc] at hh
  rw [Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_left (by omega : (1 : ℕ) ≤ h))]
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · intro j hj hjh
    rw [Finset.mem_Icc] at hj hjh
    have : ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) = 0 :=
      prod_vanish (by omega) (by omega) hh.2
    rw [this]; ring

/-- **Rrat-part via q-Lagrange.** Each `t`-term's `j`-sum `∑_j muW n j (q^j)^{|t|}` is the Gaussian
binomial `q^{|t|}·[n+|t|−1,n−1]_q` (`qLag_thm`, valid as `|t| ≤ n−1 < n`), eliminating the Vandermonde
`muW` denominators. The result is `muW`-free: integer products times `Rrat |t|`. -/
lemma RratPart_qLag (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, ∑ j ∈ Finset.Icc 1 n,
        (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * Rrat t.card)
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-qB ^ k)) * Rrat t.card * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)) := by
  apply Finset.sum_congr rfl
  intro t ht
  have hcard : t.card < n := by
    have h1 : t.card ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rw [Nat.card_Icc] at h1
    omega
  have hpull : ∑ j ∈ Finset.Icc 1 n, (∏ k ∈ t, (-qB ^ k)) * muW n j * (qB ^ (t.card * j) * Rrat t.card)
      = (∏ k ∈ t, (-qB ^ k)) * Rrat t.card * ∑ j ∈ Finset.Icc 1 n, muW n j * (qB ^ j) ^ t.card := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← pow_mul, Nat.mul_comm j t.card]; ring
  rw [hpull, qLag_thm hn t.card hcard]

/-- **`Acorr` in clean form** — the structural target of the elementary Lemma-3 route. The Rrat-part
is now `muW`-free (Gaussian binomials), and the headS-part is `∑_{h=1}^n u_h·N_h` with the
q-Lagrange combination `N_h = ∑_j muW n j ∏_{k=1}^{n−1}(1−q^{k+j−h})`. Integrality of
`β^{2n}·Wₙ·Acorr n` reduces to: (i) `β^{2n}·Wₙ·(Rrat-part) ∈ ℤ` (clear `Rrat`'s `q^l−1` denominators
by `QPint_dvd` and `c`-powers by `β`); (ii) `N_h ∈ ℤ` (out to Aristotle, `Lemma3-Nh-Leaf.lean`) with
`β^{2n}·Wₙ·u_h ∈ ℤ` (clear `u_h` by `CPint`). -/
theorem Acorr_clean (n : ℕ) (hn : 1 ≤ n) :
    Acorr n = -(∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
                  (∏ k ∈ t, (-qB ^ k)) * Rrat t.card * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)))
              + ∑ h ∈ Finset.Icc 1 n, (1 - cB * qB ^ h)⁻¹ *
                  ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  rw [Acorr_reorg n, RratPart_qLag n hn, headSPart_NhForm n hn]

/-! ## Section 4: the integer clearing factor `β^{2n}·Wₙ` -/

/-- The cleared **integer** form of `β^{2n}·Wₙ = 3^{2n}·(n−2)!·∏(1−c·q^k)·∏(1−q^k)`. Since
`3^n·∏(1−c·q^k) = CPint` and `∏(1−q^k) = QPint`, this is `3^n·(n−2)!·CPint·QPint ∈ ℤ`. -/
def WI (n : ℕ) : ℤ := 3 ^ n * (Nat.factorial (n - 2)) * CPint n * QPint n

/-- `(WI n : ℝ) = β^{2n}·Wₙ`: the clearing factor is a machine-checked integer. -/
lemma WI_cast (n : ℕ) : (WI n : ℝ) = (βB : ℝ) ^ (2 * n) * Wterm n := by
  rw [WI, Wterm]
  push_cast
  rw [CPint_cast, QPint_cast]
  have hb : (βB : ℝ) ^ (2 * n) = 3 ^ n * 3 ^ n := by
    rw [show (βB : ℝ) = 3 from by simp [βB], ← pow_add]; congr 1; omega
  rw [hb]; ring

/-- The integer witness for `β^{2n}·Wₙ·(c^{i−l}/(q^l−1))`: clears `3^{i−l}` by `3^n` and `q^l−1` by
`QPint` (via `QPint_dvd`). -/
def RratTermInt (n i l : ℕ) : ℤ :=
  8 ^ (i - l) * 3 ^ (n - (i - l)) * (Nat.factorial (n - 2)) * CPint n * (QPint n / (2 ^ l - 1))

/-- **Per-term Rrat clearing**: `(RratTermInt n i l : ℝ) = WI n · c^{i−l}/(q^l−1)` for `1 ≤ l ≤ n−1`,
`l ≤ i ≤ n−1`. -/
lemma RratTermInt_cast {n i l : ℕ} (hn : 1 ≤ n) (hl1 : 1 ≤ l) (hli : l ≤ i) (hin : i ≤ n - 1) :
    (RratTermInt n i l : ℝ) = (WI n : ℝ) * (cB ^ (i - l) / (qB ^ l - 1)) := by
  obtain ⟨d, hd⟩ := QPint_dvd (l := l) (n := n) hl1 (by omega)
  have hne : ((2 : ℤ) ^ l - 1) ≠ 0 := by
    have : (1 : ℤ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℤ) ^ l ≠ 1 := by
      have : (2 : ℤ) ^ 1 ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hl1
      omega
    omega
  have hdiv : QPint n / (2 ^ l - 1) = d := by rw [hd]; exact Int.mul_ediv_cancel_left d hne
  have hq : (qB ^ l - 1 : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ qB ^ l := two_le_pow hl1
    simp only [qB] at this ⊢; linarith
  have hQ : (QPint n : ℝ) = (qB ^ l - 1) * (d : ℝ) := by
    have h1 : (QPint n : ℝ) = (((2 ^ l - 1) * d : ℤ) : ℝ) := by rw [← hd]
    rw [h1]; push_cast; simp only [qB]
  have h3 : (3 : ℝ) ^ n = 3 ^ (i - l) * 3 ^ (n - (i - l)) := by rw [← pow_add]; congr 1; omega
  rw [RratTermInt, hdiv, WI]
  push_cast
  rw [hQ, h3, show (cB : ℝ) = 8 / 3 from rfl, div_pow]
  field_simp

/-- **Rrat clearing.** `WI n · Rrat i ∈ ℤ` for `i ≤ n−1`: each `Rrat_closed` term clears. -/
lemma WI_mul_Rrat_int {n : ℕ} (hn : 1 ≤ n) {i : ℕ} (hi : i ≤ n - 1) :
    ∃ z : ℤ, (z : ℝ) = (WI n : ℝ) * Rrat i := by
  refine ⟨∑ l ∈ Finset.Icc 1 i, RratTermInt n i l, ?_⟩
  rw [Rrat_closed, Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mem_Icc] at hl
  exact RratTermInt_cast hn hl.1 hl.2 hi

/-- Per-`t` integer witness for the whole Rrat-part of `Acorr_clean`. -/
def RratCleanTermInt (n : ℕ) (t : Finset ℕ) : ℤ :=
  (∏ k ∈ t, (-(2 : ℤ) ^ k)) * (2 ^ t.card * qBin (2 : ℤ) (n + t.card - 1) (n - 1))
    * (∑ l ∈ Finset.Icc 1 t.card, RratTermInt n t.card l)

/-- Each Rrat-part `t`-term, times `β^{2n}·Wₙ`, is the integer `RratCleanTermInt n t`. -/
lemma RratCleanTermInt_cast {n : ℕ} (hn : 1 ≤ n) {t : Finset ℕ}
    (ht : t ∈ (Finset.Icc 1 (n - 1)).powerset) :
    (RratCleanTermInt n t : ℝ) = (WI n : ℝ) *
      ((∏ k ∈ t, (-qB ^ k)) * Rrat t.card * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1))) := by
  have hcard : t.card ≤ n - 1 := by
    have h := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
  have e1 : ((∏ k ∈ t, (-(2 : ℤ) ^ k) : ℤ) : ℝ) = ∏ k ∈ t, (-qB ^ k) := by
    rw [Int.cast_prod]; apply Finset.prod_congr rfl; intro k _; push_cast; simp [qB]
  have e4 : ((∑ l ∈ Finset.Icc 1 t.card, RratTermInt n t.card l : ℤ) : ℝ)
      = (WI n : ℝ) * Rrat t.card := by
    rw [Rrat_closed, Finset.mul_sum, Int.cast_sum]
    apply Finset.sum_congr rfl; intro l hl; rw [Finset.mem_Icc] at hl
    exact RratTermInt_cast hn hl.1 hl.2 hcard
  rw [RratCleanTermInt, Int.cast_mul, Int.cast_mul, e4, e1,
    show ((2 ^ t.card * qBin (2 : ℤ) (n + t.card - 1) (n - 1) : ℤ) : ℝ)
        = qB ^ t.card * qBin qB (n + t.card - 1) (n - 1) from by
      push_cast [← qBin_two_cast]; simp [qB]]
  ring

/-- **Rrat-part integrality.** `β^{2n}·Wₙ · (Rrat-part of `Acorr_clean`) ∈ ℤ` — the entire `muW`-free
Rrat-part clears (integer products × `WI·Rrat`). The "clean half" of Lemma 3. -/
lemma WI_mul_RratClean_int (n : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℝ) = (WI n : ℝ) * ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
        (∏ k ∈ t, (-qB ^ k)) * Rrat t.card * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)) := by
  refine ⟨∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, RratCleanTermInt n t, ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact RratCleanTermInt_cast hn ht

/-! ## Section 5: the headS-part `u_h` clearing (toward headS-part integrality)

The headS-part is `∑_{h=1}^n u_h·N_h`, `u_h = (1−c·q^h)⁻¹`. `β^{2n}·Wₙ·u_h ∈ ℤ` because
`CPint = ∏_{k=1}^n(3−8·2^k)` carries the factor `(3−8·2^h)` that `u_h = 3/(3−8·2^h)` exposes. The
other factor `N_h ∈ ℤ` is the q-Lagrange crux (Aristotle leaf `06c2c62c`). -/

/-- `CPint` with its `h`-th factor removed (`h ∈ [1,n]`). -/
def CPdrop (n h : ℕ) : ℤ := ∏ k ∈ (Finset.Icc 1 n).erase h, (3 - 8 * 2 ^ k)

/-- `(3 − 8·2^h)·CPdrop n h = CPint n` for `h ∈ [1,n]`. -/
lemma CPint_factor {n h : ℕ} (hh : h ∈ Finset.Icc 1 n) :
    (3 - 8 * 2 ^ h) * CPdrop n h = CPint n :=
  Finset.mul_prod_erase (Finset.Icc 1 n) (fun k => 3 - 8 * 2 ^ k) hh

/-- The integer witness for `β^{2n}·Wₙ·u_h = 3^{n+1}·(n−2)!·QPint·CPdrop`. -/
def uClearInt (n h : ℕ) : ℤ := 3 ^ (n + 1) * (Nat.factorial (n - 2)) * QPint n * CPdrop n h

/-- **`u_h` clearing**: `(uClearInt n h : ℝ) = β^{2n}·Wₙ·(1−c·q^h)⁻¹` for `1 ≤ h ≤ n`. -/
lemma uClearInt_cast {n h : ℕ} (hh1 : 1 ≤ h) (hhn : h ≤ n) :
    (uClearInt n h : ℝ) = (WI n : ℝ) * (1 - cB * qB ^ h)⁻¹ := by
  have hmem : h ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hh1, hhn⟩
  have hfac : (3 - 8 * 2 ^ h) * CPdrop n h = CPint n := CPint_factor hmem
  have h2 : (2 : ℝ) ≤ qB ^ h := two_le_pow hh1
  have hne : (3 - 8 * qB ^ h : ℝ) ≠ 0 := by simp only [qB] at h2 ⊢; nlinarith
  have hu : (1 - cB * qB ^ h)⁻¹ = 3 / (3 - 8 * qB ^ h) := by
    rw [show (1 - cB * qB ^ h : ℝ) = (3 - 8 * qB ^ h) / 3 from by simp only [cB]; ring, inv_div]
  have hCP : (CPint n : ℝ) = (3 - 8 * qB ^ h) * (CPdrop n h : ℝ) := by
    rw [← hfac]; push_cast; simp only [qB]
  rw [uClearInt, WI]
  push_cast
  rw [hu, hCP]
  field_simp
  ring

/-! ## Section 6: headS-part integrality and the full numerator clearing (conditional on `N_h ∈ ℤ`) -/

/-- **headS-part integrality**, given integer witnesses `Nz h = N_h`. `β^{2n}·Wₙ·(headS-part)
= ∑_h (β^{2n}·Wₙ·u_h)·N_h = ∑_h uClearInt·Nz h ∈ ℤ`. -/
lemma WI_mul_headS_int (n : ℕ) (Nz : ℕ → ℤ)
    (hNz : ∀ h, 1 ≤ h → h ≤ n → (Nz h : ℝ)
      = ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))) :
    ∃ z : ℤ, (z : ℝ) = (WI n : ℝ) *
      ∑ h ∈ Finset.Icc 1 n, (1 - cB * qB ^ h)⁻¹ *
        ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  refine ⟨∑ h ∈ Finset.Icc 1 n, uClearInt n h * Nz h, ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mem_Icc] at hh
  rw [Int.cast_mul, uClearInt_cast hh.1 hh.2, hNz h hh.1 hh.2]
  ring

/-- **Borwein Lemma 3 (numerator integrality), conditional on `N_h ∈ ℤ`.** Combines the Rrat-part
(`WI_mul_RratClean_int`) and headS-part (`WI_mul_headS_int`) integralities via `Acorr_clean` and
`WI_cast`: `−β^{2n}·Wₙ·Acorr n ∈ ℤ`. -/
lemma Acorr_int (n : ℕ) (hn : 1 ≤ n) (Nz : ℕ → ℤ)
    (hNz : ∀ h, 1 ≤ h → h ≤ n → (Nz h : ℝ)
      = ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))) :
    ∃ a : ℤ, (a : ℝ) = -((βB : ℝ) ^ (2 * n) * Wterm n * Acorr n) := by
  obtain ⟨rInt, hr⟩ := WI_mul_RratClean_int n hn
  obtain ⟨hInt, hh⟩ := WI_mul_headS_int n Nz hNz
  refine ⟨rInt - hInt, ?_⟩
  rw [← WI_cast]
  push_cast
  rw [hr, hh, Acorr_clean n hn]
  ring

/-! ## Section 6b: toward `N_h ∈ ℤ` — the 2-adic cleared product (port scaffold)

The crux integrality `N_h ∈ ℤ` rests on a 2-adic clearing: `qB^{(n−1)h}·∏_{k=1}^{n−1}(1−q^{k+j−h})`
is an INTEGER-coefficient polynomial in `qB^j` (`clearedProd`), so `qB^{(n−1)h}·N_h ∈ ℤ` via q-Lagrange;
combined with `μ_j`'s odd denominator this gives `N_h ∈ ℤ`. This lemma is the foundation either way
(local proof or porting the Aristotle result). -/

/-- **Cleared product**: `(qB^h)^{n−1}·∏_{k=1}^{n−1}(1−qB^{k+j−h}) = ∏_{k=1}^{n−1}(qB^h−qB^{k+j})`,
turning the zpow product (with `q^{−h}` denominators) into an integer-valued nat-power product. -/
lemma clearedProd (n j h : ℕ) :
    (qB ^ h) ^ (n - 1) * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))
      = ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j)) := by
  have hcard : (qB ^ h) ^ (n - 1) = ∏ _k ∈ Finset.Icc 1 (n - 1), qB ^ h := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel]
  rw [hcard, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  rw [mul_sub, mul_one]
  congr 1
  rw [← zpow_natCast qB h, ← zpow_add₀ qB_ne, ← zpow_natCast qB (k + j)]
  congr 1
  push_cast
  ring

/-- **2-adic clearing of `N_h`**: `qB^{(n−1)h}·N_h = ∑_j muW n j ∏_{k=1}^{n−1}(qB^h−qB^{k+j})`. The RHS
product is an INTEGER-coefficient polynomial in `qB^j` (each factor `2^h−2^{k+j} ∈ ℤ`), so by
`qLag_thm` (termwise, after expanding the product) the RHS — hence `qB^{(n−1)h}·N_h` — is an integer.
This is the 2-adic half (`N_h ∈ ℤ[1/2]`) of `N_h ∈ ℤ`. -/
lemma Nh_2adic (n h : ℕ) :
    (qB ^ h) ^ (n - 1) *
        ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))
      = ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_left_comm, clearedProd n j h]

/-- Expand `∏_{k=1}^{n−1}(qB^h − qB^{k+j})` over subsets `t ⊆ [1,n−1]` as a polynomial in `qB^j`. -/
lemma prod_diff_expand (n j h : ℕ) :
    ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-qB ^ k)) * (qB ^ j) ^ t.card * (qB ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card) := by
  have hf : ∀ k, (qB ^ h - qB ^ (k + j) : ℝ) = (-qB ^ (k + j)) + qB ^ h := fun k => by ring
  rw [Finset.prod_congr rfl (fun k _ => hf k), Finset.prod_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_const]
  have hexp : ∏ k ∈ t, (-qB ^ (k + j)) = (∏ k ∈ t, (-qB ^ k)) * (qB ^ j) ^ t.card := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro k _; rw [pow_add]; ring
  rw [hexp]

/-- **q-Lagrange reduction of the cleared `N_h`** (the `muW`-free form): `∑_j muW n j ∏(qB^h−qB^{k+j})`
equals a sum over subsets `t` of integer-valued terms (Gaussian binomials), via `prod_diff_expand` +
`qLag_thm`. With `Nh_2adic`, this gives `qB^{(n−1)h}·N_h ∈ ℤ` (the 2-adic half of `N_h ∈ ℤ`). -/
lemma Nh_prod_qLag (n h : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j))
      = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
          (∏ k ∈ t, (-qB ^ k)) * (qB ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
            * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)) := by
  have hstep : ∀ j ∈ Finset.Icc 1 n,
      muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (qB ^ h - qB ^ (k + j))
        = ∑ t ∈ (Finset.Icc 1 (n - 1)).powerset,
            (∏ k ∈ t, (-qB ^ k)) * (qB ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
              * (muW n j * (qB ^ j) ^ t.card) := by
    intro j _
    rw [prod_diff_expand n j h, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hcard : t.card < n := by
    have h1 : t.card ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_le_card (Finset.mem_powerset.mp ht)
    rw [Nat.card_Icc] at h1; omega
  rw [← Finset.mul_sum, qLag_thm hn t.card hcard]

/-- Per-`t` integer witness for the cleared `N_h`. -/
def Nh2TermInt (n h : ℕ) (t : Finset ℕ) : ℤ :=
  (∏ k ∈ t, (-(2 : ℤ) ^ k)) * (2 ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
    * (2 ^ t.card * qBin (2 : ℤ) (n + t.card - 1) (n - 1))

/-- Each `Nh_prod_qLag` `t`-term is the integer `Nh2TermInt n h t`. -/
lemma Nh2TermInt_cast (n h : ℕ) (t : Finset ℕ) :
    (Nh2TermInt n h t : ℝ) = (∏ k ∈ t, (-qB ^ k)) * (qB ^ h) ^ ((Finset.Icc 1 (n - 1) \ t).card)
      * (qB ^ t.card * qBin qB (n + t.card - 1) (n - 1)) := by
  rw [Nh2TermInt]
  push_cast [← qBin_two_cast]
  simp only [qB]

/-- **Part (a) of `N_h ∈ ℤ`: the 2-adic half.** `(qB^h)^{n−1}·N_h ∈ ℤ`. (Combined with `μ_j`'s odd
denominator — part (b), still TODO — this gives `N_h ∈ ℤ`, discharging `Nh_integral`.) -/
lemma Nh_2adic_int (n h : ℕ) (hn : 1 ≤ n) :
    ∃ z : ℤ, (z : ℝ) = (qB ^ h) ^ (n - 1) *
      ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  rw [Nh_2adic n h, Nh_prod_qLag n h hn]
  refine ⟨∑ t ∈ (Finset.Icc 1 (n - 1)).powerset, Nh2TermInt n h t, ?_⟩
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact Nh2TermInt_cast n h t

/-- **The combine** `ℤ[1/2] ∩ ℤ[1/odd] = ℤ`: if `2^m·N` and `D·N` are integers with `D` odd, then
`N` is an integer. (`A·D = 2^m·B`, `IsCoprime 2^m D` ⟹ `2^m ∣ A` ⟹ `N = A/2^m ∈ ℤ`.) -/
lemma int_of_clearings {N : ℝ} {A B D : ℤ} {m : ℕ} (hD : Odd D)
    (hA : (A : ℝ) = (2 : ℝ) ^ m * N) (hB : (B : ℝ) = (D : ℝ) * N) :
    ∃ z : ℤ, (z : ℝ) = N := by
  have hAD : A * D = 2 ^ m * B := by
    have hr : ((A * D : ℤ) : ℝ) = ((2 ^ m * B : ℤ) : ℝ) := by
      push_cast; rw [hA, hB]; ring
    exact_mod_cast hr
  have hmod : D % 2 = 1 := Int.odd_iff.mp hD
  have hnd : ¬ (2 : ℤ) ∣ D := by rw [Int.dvd_iff_emod_eq_zero]; omega
  have hdvd : (2 : ℤ) ^ m ∣ A :=
    (Int.prime_two).pow_dvd_of_dvd_mul_right m hnd ⟨B, hAD⟩
  obtain ⟨C, hC⟩ := hdvd
  refine ⟨C, ?_⟩
  have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
  have : (2 : ℝ) ^ m * (C : ℝ) = (2 : ℝ) ^ m * N := by
    rw [← hA, hC]; push_cast; ring
  exact mul_left_cancel₀ h2m this

/-! ### Part (b): `μ_j` has odd denominator (the last piece of `N_h ∈ ℤ`)

`muW n j = ∏_{l≠j}(1−q^l/q^j)⁻¹`. Multiplying the `l`-factor by the ODD integer `2^{|j−l|}−1` gives an
integer (`−1` if `l>j`, `2^{j−l}` if `l<j`), so the odd product `Vodd n j = ∏_{l≠j}(2^{|j−l|}−1)`
clears `muW n j`. Hence `N_h ∈ ℤ[1/odd]`, which with part (a) and `int_of_clearings` gives `N_h ∈ ℤ`. -/

/-- The explicit integer value of the cleared `l`-factor: `2^{j−l}` if `l<j`, else `−1`. -/
def zfac (j l : ℕ) : ℤ := if l < j then 2 ^ (j - l) else -1

/-- Per-factor odd clearing: `(2^{|j−l|}−1)·(1−q^l/q^j)⁻¹ = zfac j l ∈ ℤ`. -/
lemma factor_clear {j l : ℕ} (hlj : l ≠ j) :
    ((zfac j l : ℤ) : ℝ) = (((2 : ℤ) ^ (max j l - min j l) - 1 : ℤ) : ℝ) * (1 - qB ^ l / qB ^ j)⁻¹ := by
  have hq2 : (qB : ℝ) = 2 := rfl
  rw [zfac]
  rcases lt_or_gt_of_ne hlj with hlt | hgt
  · -- l < j : value 2^{j−l}
    rw [if_pos hlt]
    have hmm : max j l - min j l = j - l := by omega
    have ha1 : (2 : ℝ) ^ (j - l) - 1 ≠ 0 := by
      have : (2 : ℝ) ^ 1 ≤ 2 ^ (j - l) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this; linarith
    have hdiv : (qB ^ l / qB ^ j : ℝ) = ((2 : ℝ) ^ (j - l))⁻¹ := by
      rw [hq2, show (2 : ℝ) ^ j = 2 ^ (j - l) * 2 ^ l from by rw [← pow_add]; congr 1; omega]
      field_simp
    rw [hmm, hdiv]
    push_cast
    field_simp
  · -- l > j : value −1
    rw [if_neg (by omega)]
    have hmm : max j l - min j l = l - j := by omega
    have ha1 : (2 : ℝ) ^ (l - j) - 1 ≠ 0 := by
      have : (2 : ℝ) ^ 1 ≤ 2 ^ (l - j) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this; linarith
    have hdiv : (qB ^ l / qB ^ j : ℝ) = (2 : ℝ) ^ (l - j) := by
      rw [hq2, show (2 : ℝ) ^ l = 2 ^ (l - j) * 2 ^ j from by rw [← pow_add]; congr 1; omega]
      field_simp
    rw [hmm, hdiv]
    push_cast
    rw [show (1 : ℝ) - 2 ^ (l - j) = -(2 ^ (l - j) - 1) from by ring, inv_neg]
    field_simp

/-- The **odd** clearing product `Vodd n j = ∏_{l≠j}(2^{|j−l|}−1)`. -/
def Vodd (n j : ℕ) : ℤ := ∏ l ∈ (Finset.Icc 1 n).erase j, ((2 : ℤ) ^ (max j l - min j l) - 1)

/-- `Vodd n j` is odd (product of `2^{|j−l|}−1`, each odd since `|j−l| ≥ 1`). -/
lemma Vodd_odd (n j : ℕ) : Odd (Vodd n j) := by
  rw [Vodd]
  apply Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
  intro l hl
  have hne : max j l - min j l ≠ 0 := by
    have : l ≠ j := (Finset.mem_erase.mp hl).1; omega
  have heven : Even ((2 : ℤ) ^ (max j l - min j l)) := by
    rw [Int.even_pow]; exact ⟨by decide, hne⟩
  exact heven.sub_odd odd_one

/-- **Part (b): the odd clearing.** `Vodd n j · muW n j ∈ ℤ` — the odd product clears `μ_j`'s
denominator (per-factor `factor_clear`). -/
lemma Vodd_muW_int (n j : ℕ) : ∃ z : ℤ, (z : ℝ) = (Vodd n j : ℝ) * muW n j := by
  refine ⟨∏ l ∈ (Finset.Icc 1 n).erase j, zfac j l, ?_⟩
  rw [Int.cast_prod, Vodd, Int.cast_prod, muW, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l hl
  exact factor_clear (Finset.mem_erase.mp hl).1

/-- The odd common denominator `Dfull n = ∏_{j∈[1,n]} Vodd n j`, clearing every `muW n j`. -/
def Dfull (n : ℕ) : ℤ := ∏ j ∈ Finset.Icc 1 n, Vodd n j

/-- `Dfull n` is odd. -/
lemma Dfull_odd (n : ℕ) : Odd (Dfull n) := by
  rw [Dfull]
  exact Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one (fun j _ => Vodd_odd n j)

/-- `Dfull n · muW n j ∈ ℤ` for `j ∈ [1,n]`. -/
lemma Dfull_muW_int {n j : ℕ} (hj : j ∈ Finset.Icc 1 n) :
    ∃ m : ℤ, (m : ℝ) = (Dfull n : ℝ) * muW n j := by
  obtain ⟨z, hz⟩ := Vodd_muW_int n j
  refine ⟨(∏ j' ∈ (Finset.Icc 1 n).erase j, Vodd n j') * z, ?_⟩
  have hD : (Dfull n : ℝ)
      = (Vodd n j : ℝ) * ((∏ j' ∈ (Finset.Icc 1 n).erase j, Vodd n j' : ℤ) : ℝ) := by
    rw [Dfull, ← Finset.mul_prod_erase (Finset.Icc 1 n) (Vodd n) hj]; push_cast; ring
  rw [hD]; push_cast; rw [hz]; ring

/-- `P_j = ∏_{k=1}^{n−1}(1−q^{k+j−h})` is an integer when `j ≥ h` (all exponents `≥ 1`). -/
lemma Pj_int {n j h : ℕ} (hjh : h ≤ j) :
    ∃ p : ℤ, (p : ℝ) = ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  refine ⟨∏ k ∈ Finset.Icc 1 (n - 1), (1 - 2 ^ (k + j - h)), ?_⟩
  rw [Int.cast_prod]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [show ((k : ℤ) + j - h) = ((k + j - h : ℕ) : ℤ) from by omega, zpow_natCast]
  push_cast
  simp [qB]

/-- **Part (b) at the `N_h` level**: `Dfull n · N_h ∈ ℤ`, with `Dfull n` odd. So `N_h ∈ ℤ[1/odd]`. -/
lemma Nh_odd_int (n h : ℕ) (_hh1 : 1 ≤ h) (hhn : h ≤ n) :
    ∃ z : ℤ, (z : ℝ) = (Dfull n : ℝ) *
      ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  rw [Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.Icc 1 n, ∃ b : ℤ, (b : ℝ) = (Dfull n : ℝ) *
      (muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h))) := by
    intro j hj
    rcases Nat.lt_or_ge j h with hlt | hge
    · refine ⟨0, ?_⟩
      rw [Finset.mem_Icc] at hj
      have hv : ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) = 0 :=
        prod_vanish hj.1 hlt hhn
      rw [hv]; push_cast; ring
    · obtain ⟨m, hm⟩ := Dfull_muW_int hj
      obtain ⟨p, hp⟩ := Pj_int (n := n) hge
      exact ⟨m * p, by push_cast; rw [hm, hp]; ring⟩
  choose b hb using hterm
  refine ⟨∑ j ∈ (Finset.Icc 1 n).attach, b j.1 j.2, ?_⟩
  rw [Int.cast_sum, ← Finset.sum_attach (Finset.Icc 1 n) _]
  apply Finset.sum_congr rfl
  rintro ⟨j, hj⟩ _
  exact hb j hj

/-- **`N_h ∈ ℤ`** (per `(n,h)`): combine part (a) (`Nh_2adic_int`, 2-adic) and part (b)
(`Nh_odd_int`, odd) via `int_of_clearings`. -/
lemma Nh_int (n h : ℕ) (hn : 1 ≤ n) (hh1 : 1 ≤ h) (hhn : h ≤ n) :
    ∃ z : ℤ, (z : ℝ) =
      ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  obtain ⟨A, hA⟩ := Nh_2adic_int n h hn
  obtain ⟨B, hB⟩ := Nh_odd_int n h hh1 hhn
  have hA' : (A : ℝ) = (2 : ℝ) ^ (h * (n - 1)) *
      ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
    rw [hA, show (qB ^ h) ^ (n - 1) = (2 : ℝ) ^ (h * (n - 1)) from by
      rw [show qB = (2 : ℝ) from rfl, ← pow_mul]]
  exact int_of_clearings (Dfull_odd n) hA' hB

/-! ## Section 7: `N_h ∈ ℤ` DISCHARGED — and the now kernel-clean headline

The integrality of the q-Lagrange combination `N_h = ∑_j muW n j ∏_{k=1}^{n−1}(1−q^{k+j−h})` — the
last open input — is now **machine-checked** (`Nh_int`), via 2-adic (`Nh_2adic_int`) ∧ odd-denominator
(`Nh_odd_int`) ⟹ `int_of_clearings`. So `Nh_integral` is a THEOREM and `erdos_1050_S` is kernel-clean. -/

/-- **`N_h ∈ ℤ`, now a THEOREM** (was the last remaining assumption). For each `n ≥ 1` there are integer witnesses
`Nz h = N_h` (`1 ≤ h ≤ n`), assembled from the per-`(n,h)` integrality `Nh_int`. -/
theorem Nh_integral : ∀ n, 1 ≤ n → ∃ Nz : ℕ → ℤ, ∀ h, 1 ≤ h → h ≤ n →
    (Nz h : ℝ) = ∑ j ∈ Finset.Icc 1 n, muW n j * ∏ k ∈ Finset.Icc 1 (n - 1), (1 - qB ^ ((k : ℤ) + j - h)) := by
  intro n hn
  choose Nz hNz using fun h (hh1 : 1 ≤ h) (hhn : h ≤ n) => Nh_int n h hn hh1 hhn
  refine ⟨fun h => if H : 1 ≤ h ∧ h ≤ n then Nz h H.1 H.2 else 0, fun h hh1 hhn => ?_⟩
  show ((dite (1 ≤ h ∧ h ≤ n) (fun H => Nz h H.1 H.2) (fun _ => 0) : ℤ) : ℝ) = _
  rw [dif_pos (⟨hh1, hhn⟩ : 1 ≤ h ∧ h ≤ n)]
  exact hNz h hh1 hhn

/-- **Borwein Lemma 3 (numerator integrality), now a THEOREM** modulo `Nh_integral`: there is an
integer sequence `aₙ = −β^{2n}·Wₙ·Acorr n`. -/
theorem numerator_integrality : ∃ a : ℕ → ℤ, ∀ n, 1 ≤ n →
    (a n : ℝ) = -((βB : ℝ) ^ (2 * n) * Wterm n * Acorr n) := by
  have key : ∀ n, 1 ≤ n → ∃ a : ℤ, (a : ℝ) = -((βB : ℝ) ^ (2 * n) * Wterm n * Acorr n) := by
    intro n hn
    obtain ⟨Nz, hNz⟩ := Nh_integral n hn
    exact Acorr_int n hn Nz hNz
  choose a ha using key
  exact ⟨fun n => if h : 1 ≤ n then a n h else 0, fun n hn => by simp only [dif_pos hn]; exact ha n hn⟩

/-- **O1 — Borwein Lemmas 1+2+3, all discharged modulo `Nh_integral`.** -/
theorem borwein_integrality : ∃ a b : ℕ → ℤ, ∀ n, 1 ≤ n →
    (b n : ℝ) * zB - a n = (βB : ℝ) ^ (2 * n) * Wterm n * Eterm n := by
  obtain ⟨a, ha⟩ := numerator_integrality
  refine ⟨a, fun n => -Bden n, fun n hn => ?_⟩
  rw [Eterm_eq_pVal hn (qLag_thm hn)]
  have hB := Bden_cast hn
  push_cast
  rw [ha n hn, hB]
  ring

/-- The reduced q-harmonic value `z = ∑_{j≥1} 1/(1 − (8/3)·2^j)` is irrational. -/
theorem irrational_zB : Irrational zB := by
  obtain ⟨a, b, hab⟩ := borwein_integrality
  apply irrational_of_intApprox zB (fun n => a (n + 1)) (fun n => b (n + 1))
  · intro n
    rw [hab (n + 1) (by omega)]
    refine mul_ne_zero (mul_ne_zero ?_ (Wterm_ne_zero (by omega))) (Eterm_ne_zero (by omega))
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (by decide))
  · have hshift : Filter.Tendsto
        (fun n => (βB : ℝ) ^ (2 * (n + 1)) * Wterm (n + 1) * Eterm (n + 1)) Filter.atTop (nhds 0) :=
      cleared_error_tendsto.comp (Filter.tendsto_add_atTop_nat 1)
    exact hshift.congr (fun n => (hab (n + 1) (by omega)).symm)

/-- **Erdős #1050**, positive-denominator tail form: the engine's series `S = ∑_{n ≥ 0} 1/(2^(n+2) − 3)`
is irrational. The literal, as-posed headline `erdos_1050 : Irrational (∑' n, 1/(2^(n+1) − 3))` is
derived from this in `Statement.lean` (they differ by the single rational term `1/(2¹ − 3) = −1`). -/
theorem erdos_1050_S : Irrational S := irrational_S_iff_zB.mpr irrational_zB

end

/-! ### Upstream module `Statement.lean` -/

section

/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/

/-!
# Erdős Problem #1050 — is `∑_{n ≥ 1} 1/(2ⁿ − 3)` irrational?

## The statement

> The real number `∑_{n ≥ 1} 1/(2ⁿ − 3)` is irrational.

exactly as posed on erdosproblems.com (`Is ∑_{n=1}^∞ 1/(2ⁿ − 3) irrational?`, answer: yes).

Formalised as `erdos_1050 : Irrational (∑' n : ℕ, 1/(2^(n+1) − 3))`. Lean's `∑' n : ℕ` ranges over
`n ≥ 0`, so the source's `n ≥ 1` sum is encoded by the standard reindex `n ↦ n + 1` (the tsum's
`n = 0` summand is the source's first term, `1/(2¹ − 3)`). That `(n+1)` shift is the *only* thing to
reconcile against the source, and it is transparent.

**This file is the audit surface.** To check that this repository proves the *right thing*, read only
this file: the theorem `erdos_1050` is the entire trusted statement. Everything else
(`Basic.lean`, `Criterion.lean`, `Approximants.lean`, `Lemma3.lean`, …) is the proof engine.

## Provenance

* **Problem source.** P. Erdős & R. Graham, relayed at <https://www.erdosproblems.com/1050>
  ("Is `∑_{n=1}^∞ 1/(2ⁿ − 3)` irrational?", answer yes).
* **Resolving theorem.** P. B. Borwein, *On the irrationality of `∑ 1/(qⁿ + r)`*, J. Number Theory
  **37** (1991) 253–259 (and the cleaner *On the irrationality of certain series*, Math. Proc. Camb.
  Phil. Soc. **112** (1992) 141–146), specialized to `q = 2, r = −3`.

## Faithfulness notes

* **Indexing.** The series runs over `n ≥ 1` (the source's `∑_{n=1}^∞`). In Lean it is the tsum
  `∑' n : ℕ, 1/(2^(n+1) − 3)`, whose `n = 0` summand `1/(2¹ − 3) = −1` is the source's first term.
* **Well-definedness.** `2ⁿ − 3` is never `0` (`2ⁿ = 3` has no solution), so every term `1/(2ⁿ − 3)`
  is a genuine real.
* **Reduction (proved, not asserted).** The proof engine works with the positive-denominator tail
  `S = ∑_{n ≥ 0} 1/(2^(n+2) − 3)` (see `Basic.lean`); the headline reduces the literal series to it by
  `(∑_{n ≥ 1} 1/(2ⁿ − 3)) = -1 + S` — the single low term `1/(2¹−3) = -1` is rational, and
  irrationality is invariant under adding a rational, so `erdos_1050 ↔ erdos_1050_irrational`. This
  equivalence is `Sliteral_eq`, proved below.
* **Kernel footprint.** The final check at the foot of this file should end at
  `[propext, Classical.choice, Quot.sound]` (kernel-pure; nothing beyond Lean's three standard assumptions).
-/


open scoped BigOperators

/-- The literal Erdős–Graham series `∑_{n ≥ 1} 1/(2ⁿ − 3)`, exactly as posed on erdosproblems.com,
encoded over `ℕ` by the reindex `n ↦ n + 1` (so the tsum's `n = 0` summand is the source's first
term, `1/(2¹ − 3)`). -/
noncomputable def Sliteral : ℝ := ∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)

/-- The literal series is the positive-denominator tail `S` shifted by the one rational low term:
`∑_{n ≥ 1} 1/(2ⁿ − 3) = -1 + S`, since its first term is `1/(2¹−3) = -1`. -/
theorem Sliteral_eq : Sliteral = -1 + S := by
  have hsummable : Summable (fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) 1)
    exact h.mp (by simpa using S_summable)
  have hsplit := Summable.sum_add_tsum_nat_add
    (f := fun n : ℕ => (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) 1 hsummable
  have hfin : (∑ i ∈ Finset.range 1, (1 : ℝ) / ((2 : ℝ) ^ (i + 1) - 3)) = -1 := by
    simp only [Finset.sum_range_one]; norm_num
  rw [hfin] at hsplit
  simp only [Sliteral, S]
  rw [← hsplit]


/-- **Erdős Problem #1050** (positive-denominator tail form, used by the proof engine). -/
theorem erdos_1050_irrational : Irrational S := erdos_1050_S

/-! ### Non-vacuity

The claim is self-certifying against the worst failure mode: mathlib sets a non-summable
`tsum` to `0`, and `Irrational 0` is false — so `erdos_1050` is provable only because the
series genuinely converges to a non-rational real, never vacuously. The denominator
`2ⁿ − 3` is never zero, so no term is a junk `1/0`; the first term (`n = 1`) is exactly
`−1`, which is the rational shift `Sliteral_eq` uses. -/

/-- **Erdős Problem #1050.** The series `∑_{n ≥ 1} 1/(2ⁿ − 3)` is irrational, exactly as posed on
erdosproblems.com and encoded over `ℕ` by the reindex `n ↦ n + 1`. This is the trusted headline; its
statement is character-for-character the one published to `formal-conjectures`. -/
theorem erdos_1050 : Irrational (∑' n : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (n + 1) - 3)) := by
  show Irrational Sliteral
  rw [Sliteral_eq, show (-1 : ℝ) + S = S + ((-1 : ℚ) : ℝ) by push_cast; ring,
    irrational_add_ratCast_iff]
  exact erdos_1050_S

end

#print axioms erdos_1050
-- 'Erdos1050.erdos_1050' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1050
