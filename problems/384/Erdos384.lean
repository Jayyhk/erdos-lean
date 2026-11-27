import Mathlib

namespace Erdos384

/-
# Erdős Problem 384

If $1<k<n-1$ then $\binom{n}{k}$ is divisible by a prime $p<n/2$ (except $\binom{7}{3}=5\cdot 7$).

This is a conjecture of Erdős and Selfridge, proved by Ecklund [Ec69] with the bound
$p \leq n/2$. The strict bound printed above is false already for $\binom{4}{2} = 6$, and the
exception $\binom{7}{3}$ comes with its mirror image $\binom{7}{4}$. `erdos_384` states the theorem
with $2p \leq n$ and both exceptions, as in `formal-conjectures`.

The proof assumes Ecklund's theorem (`ecklund`) exactly as he states it, the theorem of [Ec69]
(page 267): if $n \geq 2k$, then $\binom{n}{k}$ has a prime divisor
$p \leq \max\{\frac{n}{k}, \frac{n}{2}\}$, with the exception $\binom{7}{3}$. For $k \geq 2$ the
bound is $n/2$, and the range $k > n/2$ follows from the symmetry
$\binom{n}{k} = \binom{n}{n-k}$.
-/

/-- **Ecklund's theorem** (E. F. Ecklund Jr., *On prime divisors of the binomial coefficient*,
Pacific J. Math. 29 (1969), 267–270, the theorem on page 267): if `n ≥ 2k`, then `n.choose k` has a
prime divisor `p ≤ max (n / k) (n / 2)`, with the exception `Nat.choose 7 3`. The bound is
written `k * p ≤ n ∨ 2 * p ≤ n` to avoid division, and `0 < k`, implicit in the paper, is
explicit here. Not yet in Mathlib. -/
axiom ecklund (n k : ℕ) (hk : 0 < k) (hn : 2 * k ≤ n) (hex : (n, k) ≠ (7, 3)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ (k * p ≤ n ∨ 2 * p ≤ n)

/-- For `k ≥ 2`, Ecklund's bound `max (n / k) (n / 2)` is `n / 2`. -/
theorem ecklund_half (n k : ℕ) (hk : 1 < k) (hn : 2 * k ≤ n) (hex : (n, k) ≠ (7, 3)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  obtain ⟨p, hp, hdvd, hle⟩ := ecklund n k (by omega) hn hex
  refine ⟨p, hp, hdvd, ?_⟩
  rcases hle with h | h
  · exact le_trans (Nat.mul_le_mul_right p hk) h
  · exact h

/-- **Erdős Problem 384** (Ecklund): if `1 < k < n - 1` and `(n, k)` is neither `(7, 3)` nor
`(7, 4)`, then `n.choose k` has a prime divisor `p` with `2 * p ≤ n`. -/
theorem erdos_384 (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3))
    (h₄ : (n, k) ≠ (7, 4)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  by_cases h : 2 * k ≤ n
  · exact ecklund_half n k hk h h₃
  · have hex : (n, n - k) ≠ (7, 3) := by
      intro he
      simp only [Prod.mk.injEq] at he
      exact h₄ (by simp only [Prod.mk.injEq]; omega)
    obtain ⟨p, hp, hdvd, hle⟩ := ecklund_half n (n - k) (by omega) (by omega) hex
    exact ⟨p, hp, by rwa [Nat.choose_symm (by omega)] at hdvd, hle⟩

#print axioms erdos_384
-- 'Erdos384.erdos_384' depends on axioms: [propext, Classical.choice, ecklund, Quot.sound]

end Erdos384
