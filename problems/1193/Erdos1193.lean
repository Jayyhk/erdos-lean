/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/

import Mathlib

namespace Erdos1193

/-!
# Erdős Problem 1193

Let `A ⊂ ℕ` and let `g(n)` be a non-decreasing function that is always positive.
Is the lower density of `{n : 1_A ∗ 1_A(n) = g(n)}` always `0`?
Is the upper density always `< c` for some constant `c < 1`?

## Answer

**No** to both questions. Taking `A = ℕ` and `g(n) = n + 1`, we have
`(1_A ∗ 1_A)(n) = n + 1 = g(n)` for all `n`, so the matching set is all of `ℕ`
and has lower and upper density `1`. Presumably Erdős had additional
restrictions on `g` or `A` in mind, but these are not recorded in [Er80].

## References

* P. Erdős, *A survey of problems in combinatorial number theory*,
Ann. Discrete Math. (1980), 89–115.
* [Erdős Problem #1193](https://www.erdosproblems.com/1193).
-/

open Finset Filter

open scoped Classical in
/-- The additive convolution of indicator functions of `A ⊆ ℕ`:
`conv_ind A n = #{k ∈ {0, …, n} | k ∈ A ∧ n - k ∈ A}`. -/
noncomputable def conv_ind (A : Set ℕ) (n : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun k => k ∈ A ∧ (n - k) ∈ A)).card

/-- The matching-set ratio at scale `N`:
`#{n ≤ N : (1_A ∗ 1_A)(n) = g(n)} / (N+1)`. -/
noncomputable def matchRatio (A : Set ℕ) (g : ℕ → ℕ) (N : ℕ) : ℝ :=
  (((range (N + 1)).filter (fun n => conv_ind A n = g n)).card : ℝ) / (N + 1)

/-- Lower asymptotic density of the matching set. -/
noncomputable def lowerDensity (A : Set ℕ) (g : ℕ → ℕ) : ℝ :=
  liminf (matchRatio A g) atTop

/-- Upper asymptotic density of the matching set. -/
noncomputable def upperDensity (A : Set ℕ) (g : ℕ → ℕ) : ℝ :=
  limsup (matchRatio A g) atTop

/-- For `A = ℕ`, the convolution is `(1_A ∗ 1_A)(n) = n + 1`. -/
private lemma conv_ind_univ (n : ℕ) : conv_ind Set.univ n = n + 1 := by
  simp [conv_ind]

/-- For `A = ℕ` and `g(n) = n + 1`, the matching ratio is `1` at every scale. -/
private lemma matchRatio_univ (N : ℕ) :
    matchRatio Set.univ (fun n => n + 1) N = 1 := by
  unfold matchRatio
  have h_filter :
      ((range (N + 1)).filter (fun n => conv_ind Set.univ n = n + 1)) = range (N + 1) := by
    apply Finset.filter_eq_self.mpr
    intro n _
    exact conv_ind_univ n
  rw [h_filter, card_range]
  have : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  rw [this]
  field_simp

/-- **Erdős Problem 1193.** Both of Erdős's questions are false:
the lower density of the matching set is not always `0`, and the upper density
is not always `< c` for any constant `c < 1`. Counterexample: `A = ℕ`,
`g(n) = n + 1`; then `(1_A ∗ 1_A)(n) = n + 1 = g(n)` for every `n`,
so the matching set has lower and upper density `1`. -/
theorem erdos_1193 :
    (¬ ∀ (A : Set ℕ) (g : ℕ → ℕ), Monotone g → (∀ n, 0 < g n) →
       lowerDensity A g = 0) ∧
    (¬ ∃ c : ℝ, c < 1 ∧ ∀ (A : Set ℕ) (g : ℕ → ℕ), Monotone g → (∀ n, 0 < g n) →
       upperDensity A g < c) := by
  -- Counterexample setup: A = ℕ, g(n) = n + 1.
  set A : Set ℕ := Set.univ
  set g : ℕ → ℕ := fun n => n + 1
  have hg_mono : Monotone g := fun _ _ h => Nat.add_le_add_right h 1
  have hg_pos : ∀ n, 0 < g n := fun n => Nat.succ_pos n
  -- matchRatio A g N = 1 for every N.
  have h_ratio : ∀ N, matchRatio A g N = 1 := matchRatio_univ
  -- The matchRatio sequence is identically 1.
  have h_eq_one : (fun N => matchRatio A g N) = (fun _ => (1 : ℝ)) := by
    funext N; exact h_ratio N
  -- liminf and limsup of the constant 1 sequence are both 1.
  have h_lower : lowerDensity A g = 1 := by
    show liminf (fun N => matchRatio A g N) atTop = 1
    rw [h_eq_one]; exact liminf_const 1
  have h_upper : upperDensity A g = 1 := by
    show limsup (fun N => matchRatio A g N) atTop = 1
    rw [h_eq_one]; exact limsup_const 1
  refine ⟨?_, ?_⟩
  · -- ¬ (∀ A g, ... → lowerDensity A g = 0)
    intro h
    have := h A g hg_mono hg_pos
    rw [h_lower] at this
    norm_num at this
  · -- ¬ ∃ c < 1, ∀ A g, ... → upperDensity A g < c
    rintro ⟨c, hc1, hupper⟩
    have := hupper A g hg_mono hg_pos
    rw [h_upper] at this
    linarith

#print axioms erdos_1193
-- 'Erdos1193.erdos_1193' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1193
