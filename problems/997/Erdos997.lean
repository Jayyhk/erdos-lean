/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/

import Mathlib

namespace Erdos997

/-!
# Erdős Problem 997: Fractional parts `{α pₙ}` are not well-distributed

The solution follows Section 4 of Alexeev–Putterman–Sawhney–Sellke–Valiant (arXiv:2603.29961),
which combines Dirichlet's approximation theorem with the Maynard–Tao theorem on consecutive primes
in arithmetic progressions (specifically the Banks–Freiberg–Turnage-Butterbaugh corollary).

## Main result

For every `α ∈ ℝ`, the sequence `{α pₙ}` of fractional parts is not well-distributed in the sense of
Hlawka–Petersen.

The Maynard–Tao–BFT theorem (a deep result not in Mathlib) is taken as an axiom.
Everything else is proved formally.

## References

* B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, G. Valiant,
  "Short proofs in combinatorics and number theory", Section 4,
  [arXiv:2603.29961](https://arxiv.org/abs/2603.29961) (2026).
* [Erdős Problem #997](https://www.erdosproblems.com/997).
-/

noncomputable section
open Finset Int Nat Real

/-! ## Core definitions -/

/-- The `n`-th prime (0-indexed). -/
abbrev nthPrime (n : ℕ) : ℕ := nth Nat.Prime n

/-- The fractional-part sequence `n ↦ fract(α · pₙ)`. -/
def fracSeq (α : ℝ) (n : ℕ) : ℝ := fract (α * (nthPrime n : ℝ))

/-- Number of indices `i ∈ (n, n + k]` with `x i ∈ [a, b]`. -/
def countInIcc (x : ℕ → ℝ) (a b : ℝ) (n k : ℕ) : ℕ :=
  ((Ioc n (n + k)).filter fun i ↦ a ≤ x i ∧ x i ≤ b).card

/-- A sequence `x : ℕ → ℝ` is **well-distributed** (Hlawka–Petersen) if the
discrepancy `|count − (b−a)·k|` is `o(k)` uniformly over all starting points
`n` and subintervals `[a, b] ⊆ [0, 1]`. -/
def IsWellDistributed (x : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ n : ℕ,
    ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      |((countInIcc x a b n k) : ℝ) - (b - a) * (k : ℝ)| < ε * (k : ℝ)

/-- A sequence has the **clustering property** when for every `m ≥ 1` one can
find `n ∈ ℕ` and `[a, b] ⊆ [0, 1]` of width `≤ 1/4` with at least half the
terms `x(n+1), …, x(n+m)` inside `[a, b]`. -/
def HasClustering (x : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 0 < m → ∃ n : ℕ, ∃ a b : ℝ,
    0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ b - a ≤ 1 / 4 ∧
      (m : ℝ) / 2 ≤ (countInIcc x a b n m : ℝ)

/-! ## Step 1: Clustering ⟹ non-well-distribution -/

/-- The clustering property with parameter `1/4` forces discrepancy `≥ k/4`
for arbitrarily large `k`, contradicting well-distribution. -/
theorem not_wellDistributed_of_clustering {x : ℕ → ℝ} (hc : HasClustering x) :
    ¬IsWellDistributed x := by
  intro h
  obtain ⟨K, hK⟩ := h (1 / 4) (by norm_num)
  obtain ⟨n, a, b, ha, hb, hab, h₁, h₂⟩ := hc (K + 1) (succ_pos _)
  specialize hK (K + 1) (by linarith) n a b ha hb hab
  norm_num at *
  nlinarith [abs_lt.mp hK]

/-! ## Step 2: The Maynard–Tao–BFT hypothesis -/

/-- **Corollary 3 of Banks–Freiberg–Turnage-Butterbaugh** (Acta Arith. 167 (2015),
arXiv:1311.7003): for every `m ≥ 2` and every coprime residue class `a mod q` with `q ≥ 3`,
there exist infinitely many index-runs of `m` consecutive primes in that class with total
gap `≤ q · Cₘ`. -/
axiom maynardTaoBFT :
  ∀ m : ℕ, 2 ≤ m → ∃ C : ℕ, 0 < C ∧ ∀ q : ℕ, 3 ≤ q → ∀ a : ℤ, Int.gcd a (q : ℤ) = 1 →
    ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧ (∀ j, j < m → (nthPrime (r + j) : ℤ) ≡ a [ZMOD (q : ℤ)]) ∧
      nthPrime (r + m - 1) - nthPrime r ≤ q * C

/-- **Theorem 1.1 of Maynard** (Ann. Math. 181 (2015), arXiv:1311.4600): for every `m ≥ 2`,
there exists `Cₘ` such that there are infinitely many index-runs of `m` consecutive primes
whose total gap is at most `Cₘ`.

This is *derived* from `maynardTaoBFT` by applying Corollary 3 of BFT with the trivial AP
(`q = 3`, `a = 1`), which gives `m` primes ≡ 1 (mod 3) with gap `≤ 3 · Cₘ`. -/
lemma maynardBoundedGaps :
    ∀ m : ℕ, 2 ≤ m → ∃ C : ℕ, 0 < C ∧
    ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧ nthPrime (r + m - 1) - nthPrime r ≤ C := by
  intro m hm
  obtain ⟨CB, hCB₀, hCB⟩ := maynardTaoBFT m hm
  refine ⟨3 * CB, by positivity, fun N => ?_⟩
  obtain ⟨r, hrN, _, hrGap⟩ := hCB 3 (by norm_num) 1 (by decide) N
  exact ⟨r, hrN, by linarith⟩

/-- For `r ≥ 1`, `nthPrime r ≥ 3`. -/
private lemma three_le_nthPrime_of_pos {r : ℕ} (hr : 1 ≤ r) : 3 ≤ nthPrime r := by
  have h_mono : StrictMono (nth Nat.Prime) :=
    Nat.nth_strictMono Nat.infinite_setOf_prime
  have h := h_mono hr
  rw [Nat.nth_prime_zero_eq_two] at h
  unfold nthPrime
  -- nth Prime r > 2, and nth Prime r is a prime
  have hp : (nth Nat.Prime r).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime r
  rcases hp.eq_two_or_odd' with h2 | hodd
  · omega
  · -- odd and > 2, so ≥ 3
    obtain ⟨k, hk⟩ := hodd
    omega

/-- For `r ≥ 1`, `nthPrime r % 2 = 1`. -/
private lemma nthPrime_odd_of_pos {r : ℕ} (hr : 1 ≤ r) : nthPrime r % 2 = 1 := by
  have hp : (nth Nat.Prime r).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime r
  have h3 : 3 ≤ nthPrime r := three_le_nthPrime_of_pos hr
  rcases hp.eq_two_or_odd with h2 | hodd
  · unfold nthPrime at h3 ⊢; omega
  · exact hodd

/-! ## Step 3: Helper lemmas for the clustering proof -/

/-
Circle-clustering: using `maynardTaoBFT`, for any `α` and `m ≥ 1`, there exist `m` consecutive
primes (starting at index `r+1`) whose fractional parts `{αp}` are pairwise within `1/8` on `ℝ/ℤ`.
-/
set_option maxHeartbeats 800000 in
theorem circleCluster (α : ℝ) (m : ℕ) (hm : 2 ≤ m) :
    ∃ r, ∀ i j, i < m → j < m → ∃ k : ℤ, |fracSeq α (r + 1 + i) - fracSeq α (r + 1 + j) - ↑k| ≤ 1 / 8 := by
  obtain ⟨CB, hCB₀, hCB⟩ := maynardTaoBFT m hm
  obtain ⟨CM, hCM₀, hCM⟩ := maynardBoundedGaps m hm
  set C : ℕ := max CB CM with hC_def
  have hC₀ : 0 < C := lt_of_lt_of_le hCB₀ (Nat.le_max_left _ _)
  have hCB_le : CB ≤ C := Nat.le_max_left _ _
  have hCM_le : CM ≤ C := Nat.le_max_right _ _
  obtain ⟨q, hq⟩ : ∃ q : ℚ, |α - q| ≤ 1 / ((8 * C + 1) * q.den) ∧ q.den ≤ 8 * C := by
    have := exists_rat_abs_sub_le_and_den_le α (show 0 < 8 * C by positivity); aesop
  obtain ⟨r, hr⟩ : ∃ r : ℕ, ∀ i < m, (nth Nat.Prime (r + 1 + i) : ℤ) ≡ q.num [ZMOD q.den] ∧
        nth Nat.Prime (r + m) - nth Nat.Prime (r + 1) ≤ q.den * C := by
    rcases Nat.lt_or_ge q.den 3 with hq3 | hq3
    · -- q.den ∈ {1, 2}: use Maynard bounded gaps; AP condition follows automatically
      -- (q.den = 1: trivial mod 1. q.den = 2: q.num odd, primes > 2 are odd.)
      have hqd12 : q.den = 1 ∨ q.den = 2 := by
        have : 0 < q.den := q.pos
        interval_cases q.den
        · left; rfl
        · right; rfl
      -- Use Maynard with N' = 2 to ensure r ≥ 2, so r + 1 ≥ 3, so r + 1 + i ≥ 1 (all primes odd).
      obtain ⟨r, hrN, hrGap⟩ := hCM 2
      have hr_pos : 1 ≤ r := by linarith
      refine ⟨r - 1, fun i hi ↦ ⟨?_, ?_⟩⟩
      · -- AP condition
        rcases hqd12 with h1 | h2
        · -- q.den = 1: trivially mod 1
          rw [h1]; exact Int.modEq_one
        · -- q.den = 2: both sides ≡ 1 mod 2
          rw [h2]
          have hidx : 1 ≤ r - 1 + 1 + i := by omega
          have hp_odd : nthPrime (r - 1 + 1 + i) % 2 = 1 := nthPrime_odd_of_pos hidx
          have hqn_odd : q.num % 2 ≠ 0 := by
            have hred : q.num.natAbs.Coprime q.den := q.reduced
            rw [h2] at hred
            intro habs
            have h2dvd : 2 ∣ q.num.natAbs := by
              have : (2 : ℤ) ∣ q.num := Int.dvd_of_emod_eq_zero habs
              exact_mod_cast Int.natAbs_dvd_natAbs.mpr this
            have h2gcd : 2 ∣ Nat.gcd q.num.natAbs 2 := Nat.dvd_gcd h2dvd dvd_rfl
            have : Nat.gcd q.num.natAbs 2 = 1 := hred
            omega
          -- Both ≡ 1 mod 2
          show (↑(nth Nat.Prime (r - 1 + 1 + i)) : ℤ) ≡ q.num [ZMOD 2]
          rw [Int.ModEq]
          have hp_mod : (↑(nth Nat.Prime (r - 1 + 1 + i)) : ℤ) % 2 = 1 := by
            exact_mod_cast hp_odd
          have hqn_mod : q.num % 2 = 1 := by
            rcases Int.emod_two_eq_zero_or_one q.num with h0 | h1'
            · exact absurd h0 hqn_odd
            · exact h1'
          rw [hp_mod, hqn_mod]
      · -- Gap condition
        have hrm : r - 1 + m = r + m - 1 := by omega
        have hr1 : r - 1 + 1 = r := by omega
        rw [hrm, hr1]
        calc nth Nat.Prime (r + m - 1) - nth Nat.Prime r
            ≤ CM := hrGap
          _ ≤ q.den * C := by
              have hqd1 : 1 ≤ q.den := q.pos
              nlinarith [hCM_le, hqd1]
    · -- q.den ≥ 3: use BFT Corollary 3
      obtain ⟨r, hr₁, hr₂, hr₃⟩ :=
        hCB q.den hq3 q.num (by simpa [Int.gcd, natAbs_neg] using q.reduced) 1
      have hr1_pos : 1 ≤ r := hr₁
      refine ⟨r - 1, fun i hi ↦ ⟨?_, ?_⟩⟩
      · -- AP condition from BFT: nth Nat.Prime (r - 1 + 1 + i) = nth Nat.Prime (r + i)
        have hreq : r - 1 + 1 + i = r + i := by omega
        rw [hreq]
        exact hr₂ i hi
      · -- Gap condition from BFT, padded to qC bound
        have hrm : r - 1 + m = r + m - 1 := by omega
        have hr1 : r - 1 + 1 = r := by omega
        rw [hrm, hr1]
        calc nth Nat.Prime (r + m - 1) - nth Nat.Prime r
            ≤ q.den * CB := hr₃
          _ ≤ q.den * C := by nlinarith [q.pos, hCB_le]
  use r; intro i j hi hj
  set pi := nth Nat.Prime (r + 1 + i)
  set pj := nth Nat.Prime (r + 1 + j)
  have h_mono := nth_monotone infinite_setOf_prime
  have h_diff : |α * (pi - pj) - (q.num * ((pi - pj) / q.den))| ≤ 1 / 8 := by
    have h1 : |α * (pi - pj) - (q.num * ((pi - pj) / q.den))| ≤
        |α - q| * |(pi - pj : ℝ)| := by
      rw [← abs_mul]; ring_nf; rw [Rat.cast_def]; ring_nf; norm_num
    have h2 : |(pi - pj : ℝ)| ≤ q.den * C := by
      have := h_mono (show r + 1 + i ≤ r + m by linarith)
      have := h_mono (show r + 1 + j ≤ r + m by linarith)
      have := h_mono (show r + 1 ≤ r + 1 + i by linarith)
      have := h_mono (show r + 1 ≤ r + 1 + j by linarith)
      norm_cast; grind
    calc _ ≤ |α - q| * |(pi - pj : ℝ)| := h1
      _ ≤ 1 / ((8 * C + 1) * q.den) * (q.den * C) := by
          exact mul_le_mul_of_nonneg_right hq.1 (abs_nonneg _) |>.trans
            (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ ≤ 1 / 8 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀] <;>
            nlinarith [show (q.den : ℝ) ≥ 1 by exact_mod_cast q.pos,
              show (C : ℝ) ≥ 1 by exact_mod_cast hC₀]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, q.num * ((pi - pj) / q.den : ℝ) = k := by
    use q.num * ((pi - pj) / q.den : ℤ)
    have hi_eq : ((pi : ℤ)) % (q.den : ℤ) = q.num % q.den := (hr i hi).1
    have hj_eq : ((pj : ℤ)) % (q.den : ℤ) = q.num % q.den := (hr j hj).1
    have hdvd : (q.den : ℤ) ∣ ((pi : ℤ) - pj) := by
      apply Int.dvd_of_emod_eq_zero
      rw [Int.sub_emod, hi_eq, hj_eq]; simp
    push_cast
    rw [Int.cast_div hdvd (by norm_cast; exact q.pos.ne')]
    push_cast; ring
  use k - ⌊α * pi⌋ + ⌊α * pj⌋; simp_all +decide [fracSeq]
  exact abs_le.mpr ⟨by linarith! [abs_le.mp h_diff, fract_add_floor (α * pi), fract_add_floor (α * pj)],
    by linarith! [abs_le.mp h_diff, fract_add_floor (α * pi), fract_add_floor (α * pj)]⟩

/-- Pigeonhole: if `m` values in `[0, 1)` are pairwise within `1/8` on `ℝ/ℤ`, then `≥ m/2` lie
in a single interval `[a, b] ⊆ [0, 1]` of width `≤ 1/4`. -/
theorem pigeonholeCluster (x : ℕ → ℝ) (n m : ℕ) (hm : 0 < m)
    (hx01 : ∀ j, j < m → 0 ≤ x (n + 1 + j) ∧ x (n + 1 + j) < 1)
    (hclose : ∀ i j, i < m → j < m → ∃ k : ℤ, |x (n + 1 + i) - x (n + 1 + j) - k| ≤ 1 / 8) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ b - a ≤ 1 / 4 ∧ (m : ℝ) / 2 ≤ (countInIcc x a b n m : ℝ) := by
  set S_low := (Finset.range m).filter (fun j ↦ x (n + 1 + j) < 1 / 2)
  set S_high := (Finset.range m).filter (fun j ↦ x (n + 1 + j) ≥ 1 / 2)
  obtain ⟨S, hSsub, hScard, hSclose⟩ :
      ∃ S : Finset ℕ, S ⊆ Finset.range m ∧ S.card * 2 ≥ m ∧
        ∀ i ∈ S, ∀ j ∈ S, |x (n + 1 + i) - x (n + 1 + j)| ≤ 1 / 8 := by
    by_cases hS_low : S_low.card * 2 ≥ m
    · refine ⟨S_low, Finset.filter_subset _ _, hS_low, ?_⟩
      intro i hi j hj
      have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      obtain ⟨k, hk⟩ := hclose i j hi' hj'
      rcases k with ⟨_ | _ | k⟩ <;> norm_num at * <;>
        exact abs_le.mpr ⟨by linarith [abs_le.mp hk, hx01 i hi', hx01 j hj',
            (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2],
              by linarith [abs_le.mp hk, hx01 i hi', hx01 j hj',
                (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2]⟩
    · refine ⟨S_high, Finset.filter_subset _ _, ?_, ?_⟩
      · have : S_low.card + S_high.card = m := by
          have := (Finset.range m).card_filter_add_card_filter_not (fun j ↦ x (n + 1 + j) < 1 / 2)
          simp only [Finset.card_range, not_lt] at this; exact this
        linarith
      · intro i hi j hj
        have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
        have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        obtain ⟨k, hk⟩ := hclose i j hi' hj'
        rcases k with ⟨_ | _ | k⟩ <;> norm_num at * <;>
          linarith [abs_le.mp hk, hx01 i hi', hx01 j hj',
            (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2]
  obtain ⟨a, b, hab, habx, habw⟩ : ∃ a b : ℝ, a ≤ b ∧
      (∀ i ∈ S, a ≤ x (n + 1 + i) ∧ x (n + 1 + i) ≤ b) ∧ b - a ≤ 1 / 4 := by
    by_cases hne : S.Nonempty
    · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image S (fun i ↦ x (n + 1 + i)) hne
      obtain ⟨i₁, hi₁, hmax⟩ := Finset.exists_max_image S (fun i ↦ x (n + 1 + i)) hne
      exact ⟨x (n+1+i₀), x (n+1+i₁), hmin i₁ hi₁,
        fun i hi ↦ ⟨hmin i hi, hmax i hi⟩, by linarith [abs_le.mp (hSclose i₀ hi₀ i₁ hi₁)]⟩
    · grind
  refine ⟨max a 0, min b 1, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num
  · obtain ⟨i, hi⟩ := Finset.card_pos.mp (by linarith)
    exact ⟨⟨hab, by linarith [(habx i hi).1, (habx i hi).2, (hx01 i (Finset.mem_range.mp (hSsub hi))).1]⟩,
        by linarith [(habx i hi).1, (habx i hi).2, (hx01 i (Finset.mem_range.mp (hSsub hi))).2]⟩
  · exact Classical.or_iff_not_imp_left.2 fun h ↦ by
      linarith [le_max_left a 0, le_max_right a 0]
  · have : countInIcc x (max a 0) (min b 1) n m ≥ S.card := by
      refine le_trans ?_ (Finset.card_mono <| show S.image (fun i ↦ n + 1 + i) ⊆
          (Finset.Ioc n (n + m)).filter (fun i ↦ max a 0 ≤ x i ∧ x i ≤ min b 1) from ?_)
      · rw [Finset.card_image_of_injective _ fun i j hij ↦ by simpa using hij]
      · grind
    rw [div_le_iff₀] <;> norm_cast; linarith

/-! ## Step 4: Assembly -/

/-- `fracSeq α` takes values in `[0, 1)`. -/
lemma fracSeq_mem_Ico (α : ℝ) (n : ℕ) : 0 ≤ fracSeq α n ∧ fracSeq α n < 1 :=
  ⟨fract_nonneg _, fract_lt_one _⟩

/-- The sequence `{α pₙ}` has the clustering property. For `m ≥ 2` this uses `maynardTaoBFT`
and `maynardBoundedGaps`; the `m = 1` case is trivial. -/
theorem fracSeq_hasClustering (α : ℝ) : HasClustering (fracSeq α) := by
  intro m hm
  rcases Nat.lt_or_ge m 2 with hm1 | hm2
  · -- m = 1: single fractional part trivially clusters in any 1/4-window containing it.
    interval_cases m
    have hv_mem := fracSeq_mem_Ico α 1
    have hv_in_lo : max 0 (fracSeq α 1 - 1/8) ≤ fracSeq α 1 := max_le hv_mem.1 (by linarith)
    have hv_in_hi : fracSeq α 1 ≤ min 1 (fracSeq α 1 + 1/8) :=
      le_min hv_mem.2.le (by linarith)
    refine ⟨0, max 0 (fracSeq α 1 - 1/8), min 1 (fracSeq α 1 + 1/8),
      le_max_left _ _, hv_in_lo.trans hv_in_hi, min_le_left _ _, ?_, ?_⟩
    · -- width ≤ 1/4
      have h1 : max 0 (fracSeq α 1 - 1/8) ≥ fracSeq α 1 - 1/8 := le_max_right _ _
      have h2 : min 1 (fracSeq α 1 + 1/8) ≤ fracSeq α 1 + 1/8 := min_le_right _ _
      linarith
    · -- count ≥ (1:ℝ)/2
      show ((1 : ℕ) : ℝ) / 2 ≤
        (countInIcc (fracSeq α) (max 0 (fracSeq α 1 - 1/8)) (min 1 (fracSeq α 1 + 1/8)) 0 1 : ℝ)
      have hcount_ge :
          1 ≤ countInIcc (fracSeq α) (max 0 (fracSeq α 1 - 1/8))
                (min 1 (fracSeq α 1 + 1/8)) 0 1 := by
        unfold countInIcc
        have hIoc : Finset.Ioc 0 (0 + 1) = ({1} : Finset ℕ) := by
          ext k; simp [Finset.mem_Ioc]
        rw [hIoc]
        rw [show ({1} : Finset ℕ).filter
            (fun i => max 0 (fracSeq α 1 - 1/8) ≤ fracSeq α i ∧
              fracSeq α i ≤ min 1 (fracSeq α 1 + 1/8)) = {1} from by
          rw [Finset.filter_singleton, if_pos ⟨hv_in_lo, hv_in_hi⟩]]
        simp
      have : (1 : ℝ) ≤
          (countInIcc (fracSeq α) (max 0 (fracSeq α 1 - 1/8))
            (min 1 (fracSeq α 1 + 1/8)) 0 1 : ℝ) := by
        exact_mod_cast hcount_ge
      linarith
  · -- m ≥ 2: use circleCluster + pigeonholeCluster
    obtain ⟨r, hr⟩ := circleCluster α m hm2
    have hm' : 0 < m := by linarith
    exact ⟨r, pigeonholeCluster (fracSeq α) r m hm' (fun j _ ↦ fracSeq_mem_Ico α _) (fun i j hi hj ↦ hr i j hi hj)⟩

/-! ## Main theorem -/

/-- **Erdős Problem 997**: for every `α ∈ ℝ`, the sequence `{α pₙ}` is not well-distributed.
Uses the Maynard–Tao–BFT axiom. -/
theorem erdos_997 (α : ℝ) : ¬IsWellDistributed (fracSeq α) :=
  not_wellDistributed_of_clustering (fracSeq_hasClustering α)

end

#print axioms erdos_997
-- 'Erdos997.erdos_997' depends on axioms: [propext, Classical.choice, Erdos997.maynardTaoBFT, Quot.sound]

end Erdos997
