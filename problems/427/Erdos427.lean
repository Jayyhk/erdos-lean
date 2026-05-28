/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Jennings, Aristotle (Harmonic)
-/

/-
# Erdős Problem 427

**Question.** Is it true that, for every `n` and `d`, there exists `k` such that
`d ∣ p_{n+1} + ⋯ + p_{n+k}`, where `pᵣ` denotes the `r`-th prime?

**Answer.** Yes.

Cedric Pilatte observed that a positive answer follows from a result of
Shiu (2000): for any `l ≥ 1` and coprime `a, q`, there exist infinitely many
`l`-tuples of consecutive primes all congruent to `a` modulo `q`.

The argument: apply Shiu's result with `l = q = d` and `a = 1` to obtain
consecutive primes `p_m, …, p_{m+d-1}` all `≡ 1 (mod d)` with `m` arbitrarily
large. Let `r` be the residue of `p_{n+1} + ⋯ + p_{m-1}` modulo `d`. Then
adding `(d − r) mod d` of the Shiu primes (each contributing 1 mod d) clears
the residue.
-/
import Mathlib

namespace Erdos427

noncomputable abbrev nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-! ## Shiu's Theorem (2000)

For any `l ≥ 1` and `(a, q) = 1` with `q ≥ 1`, there are infinitely many
runs of `l` consecutive primes all congruent to `a` modulo `q`.

*D. K. L. Shiu, "Strings of Congruent Primes", J. London Math. Soc. 61 (2000), 359–373.*
-/

/-- Shiu's theorem: for any positive length `l`, any modulus `q ≥ 1`, and any
`a` coprime to `q`, there are arbitrarily late runs of `l` consecutive primes
each congruent to `a` modulo `q`. -/
axiom shiu_consecutive_primes
    (l : ℕ) (hl : 1 ≤ l) (a q : ℕ) (hq : 1 ≤ q) (haq : Nat.Coprime a q) (N : ℕ) :
    ∃ m, N ≤ m ∧ ∀ i, i < l → nthPrime (m + i) ≡ a [MOD q]

/-! ## Helper lemmas -/

/-
Sum of `k` values each `≡ a [MOD d]` is `≡ k * a [MOD d]`.
-/
lemma sum_modeq_of_all_modeq (f : ℕ → ℕ) (k a d : ℕ)
    (h : ∀ i, i < k → f i ≡ a [MOD d]) :
    (Finset.range k).sum f ≡ k * a [MOD d] := by
  simpa [ Nat.modEq_iff_dvd ] using
    Finset.dvd_sum fun i hi => Nat.modEq_iff_dvd.mp ( h i ( Finset.mem_range.mp hi ) )

/-
Splitting a range sum into two halves.
-/
lemma sum_range_split (f : ℕ → ℕ) (a b : ℕ) :
    (Finset.range (a + b)).sum f =
    (Finset.range a).sum f + (Finset.range b).sum (fun i => f (a + i)) := by
  rw [ Finset.sum_range_add ]

/-
**Erdős Problem 427.** For every `n` and every `d ≥ 1`, there exists a
positive `k` such that `d` divides the sum of `k` consecutive primes starting
from the `(n+1)`-th prime (0-indexed via `nthPrime`).
-/
theorem erdos_427 (n d : ℕ) (hd : 1 ≤ d) :
    ∃ k, 1 ≤ k ∧ d ∣ (Finset.range k).sum (fun i => nthPrime (n + i)) := by
  obtain ⟨ m, hm ⟩ := shiu_consecutive_primes d hd 1 d hd ( Nat.coprime_one_left d ) ( n+1 );
  -- Let `len := m - n`, `S := (Finset.range len).sum (fun i => nthPrime (n + i))`, and `r := S % d`.
  set len := m - n
  set S := (Finset.range len).sum (fun i => nthPrime (n + i))
  set r := S % d;
  -- If `r ≠ 0`, take `k = len + (d - r)`. Note `d - r < d` so `d - r ≤ d - 1 < d`.
  use len + (d - r);
  -- Use `sum_range_split` to write the sum over `range k` as `S + T` where
  -- `T = (Finset.range (d-r)).sum (fun j => nthPrime (n + len + j))`.
  have h_split : (Finset.range (len + (d - r))).sum (fun i => nthPrime (n + i)) =
      S + (Finset.range (d - r)).sum (fun j => nthPrime (m + j)) := by
    convert sum_range_split _ _ _ using 2;
    exact Finset.sum_congr rfl fun _ _ => by rw [ ← add_assoc, Nat.add_sub_of_le ( by linarith ) ] ;
  -- Each `nthPrime(m+j) ≡ 1 [MOD d]` for `j < d-r < d` by Shiu's result.
  have h_cong : (Finset.range (d - r)).sum (fun j => nthPrime (m + j)) ≡ (d - r) * 1 [MOD d] := by
    exact Nat.ModEq.trans ( Nat.ModEq.sum <| fun i hi => hm.2 i
      <| Nat.lt_of_lt_of_le ( Finset.mem_range.mp hi )
      <| Nat.sub_le _ _ ) <| by simp +decide [ Nat.ModEq ] ;
  simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
  rw [ ← ZMod.natCast_eq_zero_iff ] ;
  simp_all +decide [ Nat.cast_sub ( show r ≤ d from Nat.le_of_lt <| Nat.mod_lt _ hd ) ] ;
  exact ⟨ Nat.one_le_iff_ne_zero.mpr ( by omega ), by rw [ ← Nat.mod_add_div S d ] ; aesop ⟩

#print axioms erdos_427
-- 'Erdos427.erdos_427' depends on axioms: [propext, Classical.choice, Erdos427.shiu_consecutive_primes, Quot.sound]

end Erdos427
