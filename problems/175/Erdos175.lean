import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos175

/-
# Problem Description

Erdős Problem 175. Show that for any `n ≥ 5` the central binomial coefficient `C(2n, n)` is
not squarefree. `erdos_175` proves exactly this, with Mathlib's `Squarefree`.

It is easy to see that `4 ∣ C(2n, n)` except when `n` is a power of two, so the content is
concentrated on `n = 2ᵏ`. Proved by Sárközy for all sufficiently large `n`, and
independently by Granville--Ramaré and by Velammal for all `n ≥ 5`. The formalization here
follows the latter route: a finite carry check disposes of the small powers of two, and a
separate argument supplies a large prime power for every `2ᵏ ≥ 8192`.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/Phase.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The standard additive phase and reciprocal-phase derivatives

This file packages the elementary complex identities for
`e(t) = exp(2 * pi * i * t)` and the real derivatives of `a / x` used in
reciprocal exponential sums.
-/

noncomputable section

open Complex

/-- The standard additive character `e(t) = exp(2 * pi * i * t)`. -/
def e (t : ℝ) : ℂ :=
  Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * t)

@[simp]
lemma e_zero : e 0 = 1 := by
  simp [e]

/-- The additive character turns addition into multiplication. -/
lemma e_add (s t : ℝ) : e (s + t) = e s * e t := by
  rw [e, e, e, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Negating the argument inverts the additive character. -/
lemma e_neg (t : ℝ) : e (-t) = (e t)⁻¹ := by
  rw [e, e, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- The additive character takes values on the complex unit circle. -/
@[simp]
lemma norm_e (t : ℝ) : ‖e t‖ = 1 := by
  simp [e, Complex.norm_exp]

/-- Complex conjugation negates the argument of the additive character. -/
lemma conj_e (t : ℝ) : (starRingEnd ℂ) (e t) = e (-t) := by
  have harg :
      (starRingEnd ℂ) ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) =
        (2 * (Real.pi : ℂ) * Complex.I) * (-t : ℝ) := by
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_neg]
    ring
  rw [e, e, ← Complex.exp_conj, harg]

/-- A subtraction identity in the form used when expanding squared norms. -/
lemma e_sub (s t : ℝ) : e (s - t) = e s * (starRingEnd ℂ) (e t) := by
  rw [sub_eq_add_neg, e_add, conj_e]

/-- Integer arguments are periods of the standard additive character. -/
@[simp]
lemma e_int (n : ℤ) : e n = 1 := by
  rw [e]
  convert Complex.exp_int_mul_two_pi_mul_I n using 1
  push_cast
  ring

/-- The real reciprocal phase appearing in `e(a / x)`. -/
def reciprocalPhase (a x : ℝ) : ℝ := a / x

/-- First derivative of the real reciprocal phase. -/
lemma hasDerivAt_reciprocalPhase (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (reciprocalPhase a) (-a / x ^ 2) x := by
  have h := (hasDerivAt_inv hx).const_mul a
  have hd : a * (-(x ^ 2)⁻¹) = -a / x ^ 2 := by
    rw [div_eq_mul_inv]
    ring
  exact (h.congr_deriv hd).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦ rfl)

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/ReciprocalDerivatives.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Derivatives of the reciprocal phase

This file records the elementary differential estimates for the phase
`t ↦ x / t` on a dyadic interval.  They are the input concerning this
particular phase in the derivative estimates used by Granville--Ramaré.
-/

open Set

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/MobiusMeanSquare.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The Granville--Ramaré truncated Möbius mean square

This file supplies the arithmetic coefficient estimate used in the proof of
Erdős Problem 175.  It follows Section 10 of Granville--Ramaré,
*Explicit bounds on exponential sums and the scarcity of squarefree binomial
coefficients*, Mathematika 43 (1996), 73--107.

The first part is their Lemma 10.2.  Its proof is the elementary Davenport
argument: a coprime-filtered Möbius divisor sum is the indicator of the
integers all of whose prime factors divide the modulus, and the two relevant
sets meet only at `1`.
-/

open scoped BigOperators
open ArithmeticFunction

/-! ## Granville--Ramaré Lemma 10.2 -/

/-- The Möbius function restricted to integers coprime to `q`. -/
noncomputable def coprimeMoebius (q : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if Nat.Coprime n q then ArithmeticFunction.moebius n else 0, by
    by_cases h : Nat.Coprime 0 q <;> simp [h]⟩

@[simp] theorem coprimeMoebius_apply (q n : ℕ) :
    coprimeMoebius q n =
      if Nat.Coprime n q then ArithmeticFunction.moebius n else 0 := rfl

/-! ## The elementary squarefree-density estimates of Lemma 10.3 -/

/-- Integers not divisible by either `4` or `9`.  Every squarefree integer is
in this set. -/
def fourNineFree (N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter fun n => ¬4 ∣ n ∧ ¬9 ∣ n

/-- Exact inclusion--exclusion formula for `fourNineFree`. -/
theorem card_fourNineFree (N : ℕ) :
    (fourNineFree N).card = N - N / 4 - N / 9 + N / 36 := by
  classical
  let s := Finset.Ioc 0 N
  let A := s.filter fun n => 4 ∣ n
  let B := s.filter fun n => 9 ∣ n
  let G := fourNineFree N
  have hs : s.card = N := by simp [s]
  have hA : A.card = N / 4 := by
    simpa [A, s] using Nat.Ioc_filter_dvd_card_eq_div N 4
  have hB : B.card = N / 9 := by
    simpa [B, s] using Nat.Ioc_filter_dvd_card_eq_div N 9
  have hAB : (A ∩ B).card = N / 36 := by
    have heq : A ∩ B = s.filter fun n => 36 ∣ n := by
      ext n
      simp only [A, B, Finset.mem_inter, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hns, h4⟩, _, h9⟩
        exact ⟨hns, by
          rw [show (36 : ℕ) = 4 * 9 by norm_num]
          exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h9⟩
      · rintro ⟨hns, h36⟩
        exact ⟨⟨hns, dvd_trans (by norm_num : 4 ∣ 36) h36⟩,
          hns, dvd_trans (by norm_num : 9 ∣ 36) h36⟩
    rw [heq]
    simpa [s] using Nat.Ioc_filter_dvd_card_eq_div N 36
  have hpartition : G ∪ (A ∪ B) = s := by
    ext n
    simp only [G, fourNineFree, A, B, Finset.mem_union, Finset.mem_filter]
    tauto
  have hdis : Disjoint G (A ∪ B) := by
    rw [Finset.disjoint_left]
    intro n hnG hnU
    simp only [G, fourNineFree, Finset.mem_filter] at hnG
    simp only [A, B, Finset.mem_union, Finset.mem_filter] at hnU
    rcases hnU with h4 | h9
    · exact hnG.2.1 h4.2
    · exact hnG.2.2 h9.2
  have hpartcard : G.card + (A ∪ B).card = N := by
    rw [← hs, ← hpartition, Finset.card_union_of_disjoint hdis]
  have hunion : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  change G.card = N - N / 4 - N / 9 + N / 36
  omega

/-- The `4`--`9` sieve gives the uniform density bound used by
Granville--Ramaré. -/
theorem three_mul_card_fourNineFree_le (N : ℕ) :
    3 * (fourNineFree N).card ≤ 2 * (N + 2) := by
  rw [card_fourNineFree]
  omega

/-- Finite summation by parts for reciprocal weights, in the exact form used
below. -/
theorem sum_div_eq_prefix_sum (a : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ)) =
      (∑ n ∈ Finset.Icc 1 N, a n) / (N : ℝ) +
        ∑ n ∈ Finset.Ico 1 N,
          (∑ k ∈ Finset.Icc 1 n, a k) / ((n : ℝ) * (n + 1 : ℝ)) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Ico_succ_top hN,
        Finset.sum_Icc_succ_top (by omega), ih]
      have hNR : (N : ℝ) ≠ 0 := by positivity
      have hNsR : (N + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring

/-- The square of the real Möbius value is the indicator of squarefreeness,
summed over an initial interval. -/
theorem sum_mobius_sq_eq_card_squarefree (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2)) =
      (((Finset.Icc 1 N).filter Squarefree).card : ℝ) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2)) =
        ∑ n ∈ Finset.Icc 1 N, if Squarefree n then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro n _
          rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
          split_ifs <;> norm_num
    _ = (((Finset.Icc 1 N).filter Squarefree).card : ℝ) := by
      rw [Finset.sum_boole]

/-- The number of squarefree integers in `[1,N]` is at most
`(2/3)(N+2)`. -/
theorem three_mul_card_squarefree_le (N : ℕ) :
    3 * ((Finset.Icc 1 N).filter Squarefree).card ≤ 2 * (N + 2) := by
  classical
  apply le_trans (Nat.mul_le_mul_left 3 (Finset.card_le_card ?_))
    (three_mul_card_fourNineFree_le N)
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  rw [fourNineFree, Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨hn.1.1, hn.1.2⟩, ?_, ?_⟩
  · intro h4
    have hu : IsUnit (2 : ℕ) := hn.2 2 (by simpa using h4)
    norm_num at hu
  · intro h9
    have hu : IsUnit (3 : ℕ) := hn.2 3 (by simpa using h9)
    norm_num at hu

/-- Real-valued form of the squarefree-density prefix bound. -/
theorem sum_mobius_sq_le_two_thirds (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2)) ≤
      (2 / 3 : ℝ) * (N + 2 : ℕ) := by
  rw [sum_mobius_sq_eq_card_squarefree]
  have h := three_mul_card_squarefree_le N
  have hR : (3 : ℝ) * (((Finset.Icc 1 N).filter Squarefree).card : ℝ) ≤
      2 * (N + 2 : ℕ) := by exact_mod_cast h
  nlinarith

/-- The elementary telescoping identity behind partial summation of the
density bound. -/
theorem squarefree_density_weight_identity (N : ℕ) (hN : 1 ≤ N) :
    (N + 2 : ℝ) / (N : ℝ) +
        ∑ n ∈ Finset.Ico 1 N,
          (n + 2 : ℝ) / ((n : ℝ) * (n + 1 : ℝ)) =
      (harmonic N : ℝ) + 2 := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [harmonic]
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN, harmonic_succ]
      push_cast
      have hNR : (N : ℝ) ≠ 0 := by positivity
      have hNsR : (N + 1 : ℝ) ≠ 0 := by positivity
      calc
        ((N : ℝ) + 1 + 2) / ((N : ℝ) + 1) +
              ((∑ k ∈ Finset.Ico 1 N,
                (↑k + 2) / (↑k * (↑k + 1))) +
                (↑N + 2) / (↑N * (↑N + 1))) =
            ((N + 2 : ℝ) / (N : ℝ) +
              ∑ k ∈ Finset.Ico 1 N,
                (↑k + 2) / (↑k * (↑k + 1))) +
              1 / (N + 1 : ℝ) := by
                field_simp
                push_cast
                ring
        _ = ((harmonic N : ℝ) + 2) + 1 / (N + 1 : ℝ) := by rw [ih]
        _ = (harmonic N : ℝ) + (N + 1 : ℝ)⁻¹ + 2 := by
          rw [one_div]
          ring

/-- First inequality of Granville--Ramaré Lemma 10.3. -/
theorem sum_mobius_sq_div_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2) / (n : ℝ)) ≤
      (2 / 3 : ℝ) * (Real.log N + 3) := by
  rw [sum_div_eq_prefix_sum
    (fun n => (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2)) N hN]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hend := div_le_div_of_nonneg_right (sum_mobius_sq_le_two_thirds N)
    (le_of_lt hNpos)
  have hsum :
      (∑ n ∈ Finset.Ico 1 N,
          (∑ k ∈ Finset.Icc 1 n,
            (((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2)) /
              ((n : ℝ) * (n + 1 : ℝ))) ≤
        ∑ n ∈ Finset.Ico 1 N,
          ((2 / 3 : ℝ) * (n + 2 : ℕ)) /
            ((n : ℝ) * (n + 1 : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    apply div_le_div_of_nonneg_right (sum_mobius_sq_le_two_thirds n)
    positivity
  have hcombine :
      ((2 / 3 : ℝ) * (N + 2 : ℕ)) / (N : ℝ) +
          ∑ n ∈ Finset.Ico 1 N,
            ((2 / 3 : ℝ) * (n + 2 : ℕ)) /
              ((n : ℝ) * (n + 1 : ℝ)) =
        (2 / 3 : ℝ) * ((harmonic N : ℝ) + 2) := by
    rw [← squarefree_density_weight_identity N hN]
    push_cast
    have hfac :
        (∑ n ∈ Finset.Ico 1 N,
            (2 / 3 : ℝ) * (n + 2 : ℝ) / ((n : ℝ) * (n + 1 : ℝ))) =
          (2 / 3 : ℝ) *
            ∑ n ∈ Finset.Ico 1 N,
              (n + 2 : ℝ) / ((n : ℝ) * (n + 1 : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [hfac]
    ring
  have hharm : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  calc
    (∑ n ∈ Finset.Icc 1 N,
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2)) / (N : ℝ) +
        ∑ n ∈ Finset.Ico 1 N,
          (∑ k ∈ Finset.Icc 1 n,
            (((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2)) /
              ((n : ℝ) * (n + 1 : ℝ)) ≤
      ((2 / 3 : ℝ) * (N + 2 : ℕ)) / (N : ℝ) +
        ∑ n ∈ Finset.Ico 1 N,
          ((2 / 3 : ℝ) * (n + 2 : ℕ)) /
            ((n : ℝ) * (n + 1 : ℝ)) := add_le_add hend hsum
    _ = (2 / 3 : ℝ) * ((harmonic N : ℝ) + 2) := hcombine
    _ ≤ (2 / 3 : ℝ) * (Real.log N + 3) := by nlinarith

/-- The real square of the Möbius function. -/
noncomputable def mobiusSqReal (n : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2)

theorem mobiusSqReal_nonneg (n : ℕ) : 0 ≤ mobiusSqReal n := by
  exact sq_nonneg _

theorem mobiusSqReal_eq_one_of_squarefree {n : ℕ} (hn : Squarefree n) :
    mobiusSqReal n = 1 := by
  rw [mobiusSqReal, ← Int.cast_pow, ArithmeticFunction.moebius_sq, if_pos hn]
  norm_num

theorem mobiusSqReal_eq_zero_of_not_squarefree {n : ℕ} (hn : ¬Squarefree n) :
    mobiusSqReal n = 0 := by
  rw [mobiusSqReal, ← Int.cast_pow, ArithmeticFunction.moebius_sq, if_neg hn]
  norm_num

/-- For a squarefree number every divisor and complementary divisor is
squarefree.  For a non-squarefree number the left side below vanishes. -/
theorem mobiusSqReal_card_divisors_div_le_convolution
    {n : ℕ} (hn : 1 ≤ n) :
    mobiusSqReal n * (n.divisors.card : ℝ) / (n : ℝ) ≤
      ∑ d ∈ n.divisors,
        (mobiusSqReal d / (d : ℝ)) *
          (mobiusSqReal (n / d) / ((n / d : ℕ) : ℝ)) := by
  classical
  by_cases hsq : Squarefree n
  · rw [mobiusSqReal_eq_one_of_squarefree hsq]
    have hterm : ∀ d ∈ n.divisors,
        (mobiusSqReal d / (d : ℝ)) *
            (mobiusSqReal (n / d) / ((n / d : ℕ) : ℝ)) = 1 / (n : ℝ) := by
      intro d hd
      have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hdsq : Squarefree d := hsq.squarefree_of_dvd hdn
      have hqsq : Squarefree (n / d) :=
        hsq.squarefree_of_dvd ⟨d, (Nat.div_mul_cancel hdn).symm⟩
      rw [mobiusSqReal_eq_one_of_squarefree hdsq,
        mobiusSqReal_eq_one_of_squarefree hqsq]
      have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
      simp only [one_div]
      rw [← mul_inv, ← Nat.cast_mul, hmul]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    simp only [one_mul, div_eq_mul_inv]
    exact le_rfl
  · rw [mobiusSqReal_eq_zero_of_not_squarefree hsq, zero_mul, zero_div]
    exact Finset.sum_nonneg fun d _ =>
      mul_nonneg (div_nonneg (mobiusSqReal_nonneg d) (by positivity))
        (div_nonneg (mobiusSqReal_nonneg (n / d)) (by positivity))

/-- Reindex a divisor convolution by its factor pair. -/
theorem sum_divisor_convolution_eq_sum_factor_pairs
    (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, f d * f (n / d)) =
      ∑ p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
          (fun p => p.1 * p.2 ≤ N),
        f p.1 * f p.2 := by
  classical
  rw [Finset.sum_sigma']
  apply Finset.sum_bij'
    (i := fun p _ => (p.2, p.1 / p.2))
    (j := fun p _ => (⟨p.1 * p.2, p.1⟩ : Σ _ : ℕ, ℕ))
  · rintro ⟨n, d⟩ hp
    have hp' : (1 ≤ n ∧ n ≤ N) ∧ d ∈ n.divisors := by
      simpa only [Finset.mem_sigma, Finset.mem_Icc] using hp
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hp'.2
    have hn0 : n ≠ 0 := Nat.ne_of_gt hp'.1.1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
    have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdn
    have hqpos : 1 ≤ n / d := (Nat.one_le_div_iff hdpos).2 hdle
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨hdpos, hdle.trans hp'.1.2⟩,
      ⟨hqpos, (Nat.div_le_self n d).trans hp'.1.2⟩⟩,
      by simpa only [Nat.mul_div_cancel' hdn] using hp'.1.2⟩
  · rintro ⟨a, b⟩ hp
    have hp' : ((1 ≤ a ∧ a ≤ N) ∧ (1 ≤ b ∧ b ≤ N)) ∧ a * b ≤ N := by
      simpa only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] using hp
    rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
    exact ⟨⟨Nat.mul_pos hp'.1.1.1 hp'.1.2.1, hp'.2⟩,
      ⟨dvd_mul_right a b, Nat.mul_ne_zero (by omega) (by omega)⟩⟩
  · rintro ⟨n, d⟩ hp
    have hp' : (1 ≤ n ∧ n ≤ N) ∧ d ∈ n.divisors := by
      simpa only [Finset.mem_sigma, Finset.mem_Icc] using hp
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hp'.2
    simp only [Nat.mul_div_cancel' hdn]
  · rintro ⟨a, b⟩ hp
    have hp' : ((1 ≤ a ∧ a ≤ N) ∧ (1 ≤ b ∧ b ≤ N)) ∧ a * b ≤ N := by
      simpa only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] using hp
    have ha0 : 0 < a := hp'.1.1.1
    simp only [Nat.mul_div_cancel_left b ha0]
  · rintro ⟨n, d⟩ _
    rfl

/-- The divisor-weighted Möbius square sum is bounded by the square of its
unweighted reciprocal sum. -/
theorem sum_mobius_sq_card_divisors_div_le_sq (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
        mobiusSqReal n * (n.divisors.card : ℝ) / (n : ℝ)) ≤
      (∑ n ∈ Finset.Icc 1 N, mobiusSqReal n / (n : ℝ)) ^ 2 := by
  calc
    (∑ n ∈ Finset.Icc 1 N,
        mobiusSqReal n * (n.divisors.card : ℝ) / (n : ℝ)) ≤
        ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
          (mobiusSqReal d / (d : ℝ)) *
            (mobiusSqReal (n / d) / ((n / d : ℕ) : ℝ)) := by
              apply Finset.sum_le_sum
              intro n hn
              exact mobiusSqReal_card_divisors_div_le_convolution
                (Finset.mem_Icc.mp hn).1
    _ = ∑ p ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
          (fun p => p.1 * p.2 ≤ N),
        (mobiusSqReal p.1 / (p.1 : ℝ)) *
          (mobiusSqReal p.2 / (p.2 : ℝ)) :=
      sum_divisor_convolution_eq_sum_factor_pairs
        (fun n => mobiusSqReal n / (n : ℝ)) N
    _ ≤ ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        (mobiusSqReal p.1 / (p.1 : ℝ)) *
          (mobiusSqReal p.2 / (p.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p _ _
      exact mul_nonneg
        (div_nonneg (mobiusSqReal_nonneg p.1) (by positivity))
        (div_nonneg (mobiusSqReal_nonneg p.2) (by positivity))
    _ = (∑ n ∈ Finset.Icc 1 N, mobiusSqReal n / (n : ℝ)) ^ 2 := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

/-- Second inequality of Granville--Ramaré Lemma 10.3. -/
theorem sum_mobius_sq_card_divisors_div_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
        mobiusSqReal n * (n.divisors.card : ℝ) / (n : ℝ)) ≤
      (4 / 9 : ℝ) * (Real.log N + 3) ^ 2 := by
  have hsq := sum_mobius_sq_card_divisors_div_le_sq N hN
  have hfirst :
      (∑ n ∈ Finset.Icc 1 N, mobiusSqReal n / (n : ℝ)) ≤
        (2 / 3 : ℝ) * (Real.log N + 3) := by
    simpa [mobiusSqReal] using sum_mobius_sq_div_le N hN
  have hleft : 0 ≤ ∑ n ∈ Finset.Icc 1 N, mobiusSqReal n / (n : ℝ) :=
    Finset.sum_nonneg fun n _ => div_nonneg (mobiusSqReal_nonneg n) (by positivity)
  have hlog : 0 ≤ Real.log N + 3 := by
    have : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    linarith
  calc
    (∑ n ∈ Finset.Icc 1 N,
        mobiusSqReal n * (n.divisors.card : ℝ) / (n : ℝ)) ≤
        (∑ n ∈ Finset.Icc 1 N, mobiusSqReal n / (n : ℝ)) ^ 2 := hsq
    _ ≤ ((2 / 3 : ℝ) * (Real.log N + 3)) ^ 2 :=
      pow_le_pow_left₀ hleft hfirst 2
    _ = (4 / 9 : ℝ) * (Real.log N + 3) ^ 2 := by ring

/-! ## The least-common-multiple quadratic form -/

/-! ## Counting multiples in `(N,2N]` -/

def intervalMultipleCount (N q : ℕ) : ℕ :=
  ((Finset.Ioc N (2 * N)).filter fun n => q ∣ n).card

theorem intervalMultipleCount_eq (N q : ℕ) :
    intervalMultipleCount N q = (2 * N) / q - N / q := by
  classical
  let A := (Finset.Ioc 0 N).filter fun n => q ∣ n
  let B := (Finset.Ioc N (2 * N)).filter fun n => q ∣ n
  let C := (Finset.Ioc 0 (2 * N)).filter fun n => q ∣ n
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro n hnA hnB
    simp only [A, B, Finset.mem_filter, Finset.mem_Ioc] at hnA hnB
    omega
  have hunion : A ∪ B = C := by
    ext n
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro (h | h)
      · exact ⟨⟨h.1.1, by omega⟩, h.2⟩
      · exact ⟨⟨by omega, h.1.2⟩, h.2⟩
    · rintro ⟨hn, hq⟩
      by_cases hle : n ≤ N
      · exact Or.inl ⟨⟨hn.1, hle⟩, hq⟩
      · exact Or.inr ⟨⟨by omega, hn.2⟩, hq⟩
  have hA : A.card = N / q := by
    simpa only [A] using Nat.Ioc_filter_dvd_card_eq_div N q
  have hC : C.card = (2 * N) / q := by
    simpa only [C] using Nat.Ioc_filter_dvd_card_eq_div (2 * N) q
  have hcard : A.card + B.card = C.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdis]
  have hB : B.card = (2 * N) / q - N / q := by omega
  simpa only [B, intervalMultipleCount] using hB

/-! ## The rounding-error pairs -/

/-

noncomputable def squarefreeLcmPairs (z X : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 z).product (Finset.Icc 1 z)).filter fun p =>
    Squarefree p.1 ∧ Squarefree p.2 ∧ Nat.lcm p.1 p.2 ≤ X

noncomputable def squarefreeFactorTriples (z X : ℕ) :
    Finset (Σ _r : ℕ, Σ _s : ℕ, ℕ) :=
  ((Finset.Icc 1 z).filter Squarefree).sigma fun r =>
    ((Finset.Icc 1 z).filter Squarefree).sigma fun s =>
      Finset.Icc 1 (X / (r * s))

theorem card_squarefreeLcmPairs_le_factorTriples (z X : ℕ) :
    (squarefreeLcmPairs z X).card ≤ (squarefreeFactorTriples z X).card := by
  classical
  let enc : ℕ × ℕ → (Σ _r : ℕ, Σ _s : ℕ, ℕ) := fun p =>
    ⟨p.1 / Nat.gcd p.1 p.2, ⟨p.2 / Nat.gcd p.1 p.2, Nat.gcd p.1 p.2⟩⟩
  refine Finset.card_le_card_of_injOn enc ?_ ?_
  · rintro ⟨a, b⟩ hp
    change (a, b) ∈ squarefreeLcmPairs z X at hp
    rw [squarefreeLcmPairs] at hp
    have hpf := Finset.mem_filter.mp hp
    have hpp := Finset.mem_product.mp hpf.1
    rw [Finset.mem_Icc] at hpp
    obtain ⟨⟨ha1, haz⟩, hb1, hbz⟩ := hpp
    obtain ⟨hsa, hsb, hl⟩ := hpf.2
    let g := Nat.gcd a b
    have hgpos : 1 ≤ g := Nat.gcd_pos_of_pos_left b ha1
    have hga : g ∣ a := Nat.gcd_dvd_left a b
    have hgb : g ∣ b := Nat.gcd_dvd_right a b
    have hra1 : 1 ≤ a / g :=
      (Nat.one_le_div_iff hgpos).2 (Nat.le_of_dvd (by omega) hga)
    have hrs1 : 1 ≤ b / g :=
      (Nat.one_le_div_iff hgpos).2 (Nat.le_of_dvd (by omega) hgb)
    have hraz : a / g ≤ z := (Nat.div_le_self _ _).trans haz
    have hrsz : b / g ≤ z := (Nat.div_le_self _ _).trans hbz
    have hrdiv : a / g ∣ a :=
      ⟨g, by simpa [Nat.mul_comm] using (Nat.div_mul_cancel hga).symm⟩
    have hsdiv : b / g ∣ b :=
      ⟨g, by simpa [Nat.mul_comm] using (Nat.div_mul_cancel hgb).symm⟩
    have hsqr : Squarefree (a / g) := hsa.squarefree_of_dvd hrdiv
    have hsqs : Squarefree (b / g) := hsb.squarefree_of_dvd hsdiv
    have hlcmform : Nat.lcm a b = g * (a / g * (b / g)) := by
      apply Nat.eq_of_mul_eq_mul_left hgpos
      rw [Nat.gcd_mul_lcm]
      dsimp only [g]
      rw [Nat.div_mul_cancel hga, Nat.div_mul_cancel hgb]
      ring
    have hprodpos : 0 < a / g * (b / g) := Nat.mul_pos hra1 hrs1
    have hgle : g ≤ X / (a / g * (b / g)) := by
      rw [Nat.le_div_iff_mul_le hprodpos]
      simpa [hlcmform, Nat.mul_assoc] using hl
    change enc (a, b) ∈ squarefreeFactorTriples z X
    simp only [enc, squarefreeFactorTriples, Finset.mem_sigma, Finset.mem_filter,
      Finset.mem_Icc]
    exact ⟨⟨⟨hra1, hraz⟩, hsqr⟩, ⟨⟨⟨hrs1, hrsz⟩, hsqs⟩, hgpos, hgle⟩⟩
  · intro p hp q hq heq
    have hpa : Nat.gcd p.1 p.2 ∣ p.1 := Nat.gcd_dvd_left _ _
    have hpb : Nat.gcd p.1 p.2 ∣ p.2 := Nat.gcd_dvd_right _ _
    have hqa : Nat.gcd q.1 q.2 ∣ q.1 := Nat.gcd_dvd_left _ _
    have hqb : Nat.gcd q.1 q.2 ∣ q.2 := Nat.gcd_dvd_right _ _
    have hr := congrArg (fun t => t.1) heq
    have hs := congrArg (fun t => t.2.1) heq
    have hg := congrArg (fun t => t.2.2) heq
    dsimp only [enc] at hr hs hg
    apply Prod.ext
    · calc
        p.1 = p.1 / Nat.gcd p.1 p.2 * Nat.gcd p.1 p.2 :=
          (Nat.div_mul_cancel hpa).symm
        _ = q.1 / Nat.gcd q.1 q.2 * Nat.gcd q.1 q.2 := by rw [hr, hg]
        _ = q.1 := Nat.div_mul_cancel hqa
    · calc
        p.2 = p.2 / Nat.gcd p.1 p.2 * Nat.gcd p.1 p.2 :=
          (Nat.div_mul_cancel hpb).symm
        _ = q.2 / Nat.gcd q.1 q.2 * Nat.gcd q.1 q.2 := by rw [hs, hg]
        _ = q.2 := Nat.div_mul_cancel hqb

theorem card_squarefreeFactorTriples_le (z X : ℕ) :
    ((squarefreeFactorTriples z X).card : ℝ) ≤
      (X : ℝ) *
        (∑ n ∈ Finset.Icc 1 z, mobiusSqReal n / (n : ℝ)) ^ 2 := by
  classical
  let S := (Finset.Icc 1 z).filter Squarefree
  have hsum : (∑ n ∈ S, (1 : ℝ) / (n : ℝ)) =
      ∑ n ∈ Finset.Icc 1 z, mobiusSqReal n / (n : ℝ) := by
    rw [show S = (Finset.Icc 1 z).filter Squarefree by rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hs : Squarefree n
    · rw [if_pos hs, mobiusSqReal_eq_one_of_squarefree hs]
    · rw [if_neg hs, mobiusSqReal_eq_zero_of_not_squarefree hs, zero_div]
  simp only [squarefreeFactorTriples, Finset.card_sigma]
  push_cast
  change (∑ r ∈ S, (∑ s ∈ S, ((Finset.Icc 1 (X / (r * s))).card : ℝ))) ≤ _
  calc
    (∑ r ∈ S, (∑ s ∈ S, ((Finset.Icc 1 (X / (r * s))).card : ℝ))) ≤
        ∑ r ∈ S, ∑ s ∈ S, (X : ℝ) / ((r : ℝ) * (s : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      rw [Nat.card_Icc, Nat.add_sub_cancel]
      simpa only [Nat.cast_mul] using
        (Nat.cast_div_le : (((X / (r * s) : ℕ) : ℝ) ≤
          (X : ℝ) / ((r * s : ℕ) : ℝ)))
    _ = (X : ℝ) * (∑ n ∈ S, (1 : ℝ) / (n : ℝ)) ^ 2 := by
      have hinner : ∀ r ∈ S,
          (∑ s ∈ S, (X : ℝ) / ((r : ℝ) * (s : ℝ))) =
            ((X : ℝ) / (r : ℝ)) * ∑ s ∈ S, (1 : ℝ) / (s : ℝ) := by
        intro r hr
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      rw [Finset.sum_congr rfl hinner, Finset.sum_mul]
      have hx : (∑ r ∈ S, (X : ℝ) / (r : ℝ)) =
          (X : ℝ) * ∑ r ∈ S, (1 : ℝ) / (r : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      rw [hx, pow_two]
      ring
    _ = (X : ℝ) *
        (∑ n ∈ Finset.Icc 1 z, mobiusSqReal n / (n : ℝ)) ^ 2 := by rw [hsum]
-/

/-! ## A positive quadratic-form bound -/

/-- Reindex a sum over multiples by dividing out the fixed divisor. -/
theorem sum_multiples_eq_sum_mul (f : ℕ → ℝ) {d z : ℕ}
    (hdpos : 1 ≤ d) :
    (∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b), f b) =
      ∑ c ∈ Finset.Icc 1 (z / d), f (d * c) := by
  classical
  apply Finset.sum_bij'
    (i := fun b _ => b / d)
    (j := fun c _ => d * c)
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_div_iff hdpos).2
        (Nat.le_of_dvd (by omega) hb.2), Nat.div_le_div_right hb.1.2⟩
  · intro c hc
    rw [Finset.mem_Icc] at hc
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.mul_pos hdpos hc.1, ?_⟩, dvd_mul_right d c⟩
    have h := (Nat.le_div_iff_mul_le hdpos).1 hc.2
    simpa only [Nat.mul_comm] using h
  · intro b hb
    rw [Finset.mem_filter] at hb
    exact Nat.mul_div_cancel' hb.2
  · intro c hc
    exact Nat.mul_div_cancel_left c hdpos
  · intro b hb
    rw [Finset.mem_filter] at hb
    rw [Nat.mul_div_cancel' hb.2]

/-- Removing a fixed factor can only increase the squarefree indicator. -/
theorem mobiusSqReal_mul_le_right (d c : ℕ) :
    mobiusSqReal (d * c) ≤ mobiusSqReal c := by
  by_cases h : Squarefree (d * c)
  · have hc : Squarefree c := h.squarefree_of_dvd (dvd_mul_left c d)
    rw [mobiusSqReal_eq_one_of_squarefree h,
      mobiusSqReal_eq_one_of_squarefree hc]
  · rw [mobiusSqReal_eq_zero_of_not_squarefree h]
    exact mobiusSqReal_nonneg c

/-- A positive squarefree reciprocal sum over multiples. -/
theorem sum_mobiusSqReal_multiples_le {d z : ℕ}
    (hdpos : 1 ≤ d) (hdz : d ≤ z) :
    (∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b),
        mobiusSqReal b / (b : ℝ)) ≤
      (1 / (d : ℝ)) * ((2 / 3 : ℝ) * (Real.log z + 3)) := by
  rw [sum_multiples_eq_sum_mul
    (fun b => mobiusSqReal b / (b : ℝ)) hdpos]
  calc
    (∑ c ∈ Finset.Icc 1 (z / d),
        mobiusSqReal (d * c) / ((d * c : ℕ) : ℝ)) ≤
      (1 / (d : ℝ)) *
        ∑ c ∈ Finset.Icc 1 (z / d), mobiusSqReal c / (c : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro c hc
      have hcpos : 1 ≤ c := (Finset.mem_Icc.mp hc).1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
      have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
      push_cast
      calc
        mobiusSqReal (d * c) / ((d : ℝ) * (c : ℝ)) ≤
            mobiusSqReal c / ((d : ℝ) * (c : ℝ)) := by
          gcongr
          exact mobiusSqReal_mul_le_right d c
        _ = (1 / (d : ℝ)) * (mobiusSqReal c / (c : ℝ)) := by ring
    _ ≤ (1 / (d : ℝ)) *
        ((2 / 3 : ℝ) * (Real.log ((z / d : ℕ) : ℝ) + 3)) := by
      gcongr
      have hquot : 1 ≤ z / d := (Nat.one_le_div_iff hdpos).2 hdz
      simpa [mobiusSqReal] using sum_mobius_sq_div_le (z / d) hquot
    _ ≤ (1 / (d : ℝ)) * ((2 / 3 : ℝ) * (Real.log z + 3)) := by
      have hquot : 1 ≤ z / d := (Nat.one_le_div_iff hdpos).2 hdz
      have hzpos : 1 ≤ z := hdpos.trans hdz
      have hle : ((z / d : ℕ) : ℝ) ≤ (z : ℝ) := by
        exact_mod_cast Nat.div_le_self z d
      have hqR : (0 : ℝ) < ((z / d : ℕ) : ℝ) := by exact_mod_cast hquot
      have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hzpos
      have hlog : Real.log ((z / d : ℕ) : ℝ) ≤ Real.log (z : ℝ) :=
        Real.strictMonoOn_log.monotoneOn hqR hzR hle
      have hadd : Real.log ((z / d : ℕ) : ℝ) + 3 ≤ Real.log (z : ℝ) + 3 := by
        linarith
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hadd (by norm_num))
        (by positivity)

/-- The gcd expansion, for an arbitrary real coefficient sequence. -/
theorem sum_mul_gcd_div_eq_general (f : ℕ → ℝ) {a z : ℕ} (ha : 1 ≤ a) :
    (∑ b ∈ Finset.Icc 1 z, f b * (Nat.gcd a b : ℝ) / (b : ℝ)) =
      ∑ d ∈ a.divisors, (Nat.totient d : ℝ) *
        ∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b), f b / (b : ℝ) := by
  classical
  have hterm : ∀ b ∈ Finset.Icc 1 z,
      f b * (Nat.gcd a b : ℝ) / (b : ℝ) =
        ∑ d ∈ a.divisors,
          if d ∣ b then (Nat.totient d : ℝ) * (f b / (b : ℝ)) else 0 := by
    intro b hb
    have hdivs : (Nat.gcd a b).divisors =
        a.divisors.filter (fun d => d ∣ b) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hdg, hg0⟩
        exact ⟨⟨dvd_trans hdg (Nat.gcd_dvd_left a b), by omega⟩,
          dvd_trans hdg (Nat.gcd_dvd_right a b)⟩
      · rintro ⟨⟨hda, ha0⟩, hdb⟩
        exact ⟨Nat.dvd_gcd hda hdb, (Nat.gcd_pos_of_pos_left b ha).ne'⟩
    have hgcd := Nat.sum_totient (Nat.gcd a b)
    calc
      f b * (Nat.gcd a b : ℝ) / (b : ℝ) =
          (f b / (b : ℝ)) *
            ((∑ d ∈ (Nat.gcd a b).divisors, Nat.totient d : ℕ) : ℝ) := by
        rw [hgcd]
        ring
      _ = (f b / (b : ℝ)) *
          ∑ d ∈ a.divisors.filter (fun d => d ∣ b), (Nat.totient d : ℝ) := by
        rw [hdivs]
        push_cast
        rfl
      _ = ∑ d ∈ a.divisors,
          if d ∣ b then (Nat.totient d : ℝ) * (f b / (b : ℝ)) else 0 := by
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum, Finset.sum_filter]

/-- A row of the positive lcm form. -/
theorem sum_mobiusSqReal_gcd_div_le {a z : ℕ}
    (ha : Squarefree a) (hapos : 1 ≤ a) (haz : a ≤ z) :
    (∑ b ∈ Finset.Icc 1 z,
        mobiusSqReal b * (Nat.gcd a b : ℝ) / (b : ℝ)) ≤
      (a.divisors.card : ℝ) * ((2 / 3 : ℝ) * (Real.log z + 3)) := by
  rw [sum_mul_gcd_div_eq_general mobiusSqReal hapos]
  calc
    (∑ d ∈ a.divisors, (Nat.totient d : ℝ) *
        ∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b),
          mobiusSqReal b / (b : ℝ)) ≤
      ∑ _d ∈ a.divisors, ((2 / 3 : ℝ) * (Real.log z + 3)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hda : d ∣ a := Nat.dvd_of_mem_divisors hd
      have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hda hapos
      have hdz : d ≤ z := (Nat.le_of_dvd (by omega) hda).trans haz
      calc
        (Nat.totient d : ℝ) *
            ∑ b ∈ (Finset.Icc 1 z).filter (fun b => d ∣ b),
              mobiusSqReal b / (b : ℝ) ≤
          (Nat.totient d : ℝ) *
            ((1 / (d : ℝ)) * ((2 / 3 : ℝ) * (Real.log z + 3))) := by
          gcongr
          exact sum_mobiusSqReal_multiples_le hdpos hdz
        _ ≤ (d : ℝ) *
            ((1 / (d : ℝ)) * ((2 / 3 : ℝ) * (Real.log z + 3))) := by
          gcongr
          exact_mod_cast Nat.totient_le d
        _ = (2 / 3 : ℝ) * (Real.log z + 3) := by
          have : (d : ℝ) ≠ 0 := by positivity
          field_simp
    _ = (a.divisors.card : ℝ) *
        ((2 / 3 : ℝ) * (Real.log z + 3)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- A row of the positive least-common-multiple quadratic form. -/
theorem sum_mobiusSqReal_lcm_row_le {a z : ℕ}
    (hapos : 1 ≤ a) (haz : a ≤ z) :
    (∑ b ∈ Finset.Icc 1 z,
        mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) ≤
      (mobiusSqReal a * (a.divisors.card : ℝ) / (a : ℝ)) *
        ((2 / 3 : ℝ) * (Real.log z + 3)) := by
  by_cases ha : Squarefree a
  · have hrewrite :
        (∑ b ∈ Finset.Icc 1 z,
            mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) =
          (mobiusSqReal a / (a : ℝ)) *
            ∑ b ∈ Finset.Icc 1 z,
              mobiusSqReal b * (Nat.gcd a b : ℝ) / (b : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hbpos : 1 ≤ b := (Finset.mem_Icc.mp hb).1
      have hgl : (Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ) =
          (a : ℝ) * (b : ℝ) := by exact_mod_cast Nat.gcd_mul_lcm a b
      have haR : (a : ℝ) ≠ 0 := by positivity
      have hbR : (b : ℝ) ≠ 0 := by positivity
      have hlR : (Nat.lcm a b : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.lcm_pos hapos hbpos).ne'
      field_simp
      calc
        mobiusSqReal a * mobiusSqReal b * (a : ℝ) * (b : ℝ) =
            mobiusSqReal a * mobiusSqReal b * ((a : ℝ) * (b : ℝ)) := by ring
        _ =
            mobiusSqReal a * mobiusSqReal b *
              ((Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ)) := by rw [hgl]
        _ = mobiusSqReal a * mobiusSqReal b * (Nat.lcm a b : ℝ) *
              (Nat.gcd a b : ℝ) := by ring
    rw [hrewrite]
    have hinner := sum_mobiusSqReal_gcd_div_le ha hapos haz
    calc
      (mobiusSqReal a / (a : ℝ)) *
          ∑ b ∈ Finset.Icc 1 z,
            mobiusSqReal b * (Nat.gcd a b : ℝ) / (b : ℝ) ≤
        (mobiusSqReal a / (a : ℝ)) *
          ((a.divisors.card : ℝ) * ((2 / 3 : ℝ) * (Real.log z + 3))) := by
        gcongr
        exact div_nonneg (mobiusSqReal_nonneg a) (Nat.cast_nonneg a)
      _ = (mobiusSqReal a * (a.divisors.card : ℝ) / (a : ℝ)) *
          ((2 / 3 : ℝ) * (Real.log z + 3)) := by ring
  · rw [mobiusSqReal_eq_zero_of_not_squarefree ha]
    simp

/-- The positive lcm form costs one additional logarithm. -/
theorem sum_mobiusSqReal_lcm_le (z : ℕ) (hz : 1 ≤ z) :
    (∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) ≤
      (8 / 27 : ℝ) * (Real.log z + 3) ^ 3 := by
  let C : ℝ := (2 / 3 : ℝ) * (Real.log z + 3)
  calc
    (∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) ≤
      ∑ a ∈ Finset.Icc 1 z,
        (mobiusSqReal a * (a.divisors.card : ℝ) / (a : ℝ)) * C := by
      apply Finset.sum_le_sum
      intro a ha
      exact sum_mobiusSqReal_lcm_row_le
        (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2
    _ = (∑ a ∈ Finset.Icc 1 z,
        mobiusSqReal a * (a.divisors.card : ℝ) / (a : ℝ)) * C := by
      rw [Finset.sum_mul]
    _ ≤ ((4 / 9 : ℝ) * (Real.log z + 3) ^ 2) * C := by
      gcongr
      exact sum_mobius_sq_card_divisors_div_le z hz
    _ = (8 / 27 : ℝ) * (Real.log z + 3) ^ 3 := by
      dsimp [C]
      ring

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/MobiusMeanSquareEndpoint.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The truncated Mobius mean-square endpoint

This file packages the positive least-common-multiple estimate proved in
`MobiusMeanSquare` as the concrete coefficient bound used by the Type II
argument.  The interval is the half-open dyadic interval `(N, 2N]`.
-/

open scoped BigOperators
open ArithmeticFunction

/-- The real truncated Mobius divisor sum used by Granville--Ramare. -/
noncomputable def truncatedMobiusDivisorSum (z n : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 z).filter (fun d => d ∣ n),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-- Pointwise expansion of the square as a least-common-multiple sum. -/
theorem truncatedMobiusDivisorSum_sq (z n : ℕ) :
    truncatedMobiusDivisorSum z n ^ 2 =
      ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        if Nat.lcm a b ∣ n then
          ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
            ((ArithmeticFunction.moebius b : ℤ) : ℝ)
        else 0 := by
  classical
  rw [truncatedMobiusDivisorSum, pow_two]
  rw [Finset.sum_filter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases han : a ∣ n <;> by_cases hbn : b ∣ n
  · rw [if_pos han, if_pos hbn, if_pos (Nat.lcm_dvd han hbn)]
  · rw [if_pos han, if_neg hbn, mul_zero, if_neg]
    intro hl
    exact hbn (dvd_trans (Nat.dvd_lcm_right a b) hl)
  · rw [if_neg han, zero_mul, if_neg]
    intro hl
    exact han (dvd_trans (Nat.dvd_lcm_left a b) hl)
  · rw [if_neg han, zero_mul, if_neg]
    intro hl
    exact han (dvd_trans (Nat.dvd_lcm_left a b) hl)

/-- The number of multiples of a positive modulus in `(N,2N]` is at most
`2N/q`.  The rational upper bound avoids any rounding-error term. -/
theorem intervalMultipleCount_le_two_mul_div
    (N q : ℕ) :
    (intervalMultipleCount N q : ℝ) ≤ (2 * (N : ℝ)) / (q : ℝ) := by
  have hnat : intervalMultipleCount N q ≤ (2 * N) / q := by
    rw [intervalMultipleCount_eq]
    exact Nat.sub_le _ _
  calc
    (intervalMultipleCount N q : ℝ) ≤ (((2 * N) / q : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ ≤ ((2 * N : ℕ) : ℝ) / (q : ℝ) := Nat.cast_div_le
    _ = (2 * (N : ℝ)) / (q : ℝ) := by push_cast; ring

/-- Absolute value of the real Mobius value is its square. -/
theorem abs_mobius_real_eq_mobiusSqReal (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| = mobiusSqReal n := by
  by_cases hn : Squarefree n
  · have h := ArithmeticFunction.abs_moebius_eq_one_of_squarefree hn
    have hreal : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| = 1 := by
      exact_mod_cast h
    rw [hreal, mobiusSqReal_eq_one_of_squarefree hn]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn,
      mobiusSqReal_eq_zero_of_not_squarefree hn]
    norm_num

/-- Summing the pointwise expansion counts multiples of each lcm. -/
theorem sum_truncatedMobiusDivisorSum_sq_eq_lcm (N z : ℕ) :
    (∑ n ∈ Finset.Ioc N (2 * N), truncatedMobiusDivisorSum z n ^ 2) =
      ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
            ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
          (intervalMultipleCount N (Nat.lcm a b) : ℝ) := by
  classical
  calc
    (∑ n ∈ Finset.Ioc N (2 * N), truncatedMobiusDivisorSum z n ^ 2) =
        ∑ n ∈ Finset.Ioc N (2 * N), ∑ a ∈ Finset.Icc 1 z,
          ∑ b ∈ Finset.Icc 1 z,
            if Nat.lcm a b ∣ n then
              ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
                ((ArithmeticFunction.moebius b : ℤ) : ℝ)
            else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact truncatedMobiusDivisorSum_sq z n
    _ = ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
          ∑ n ∈ Finset.Ioc N (2 * N),
            if Nat.lcm a b ∣ n then
              ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
                ((ArithmeticFunction.moebius b : ℤ) : ℝ)
            else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
            ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
          (intervalMultipleCount N (Nat.lcm a b) : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [← Finset.sum_filter]
      simp only [intervalMultipleCount, Finset.sum_const, nsmul_eq_mul]
      ring

/-- A signed lcm-count term is dominated by the corresponding positive
Mobius-square term and the rational multiple-count bound. -/
theorem mobius_mul_intervalMultipleCount_le
    (N a b : ℕ) :
    ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
        (intervalMultipleCount N (Nat.lcm a b) : ℝ) ≤
      (2 * (N : ℝ)) *
        (mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) := by
  have hmu :
      ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius b : ℤ) : ℝ) ≤
        mobiusSqReal a * mobiusSqReal b := by
    calc
      ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius b : ℤ) : ℝ) ≤
          |((ArithmeticFunction.moebius a : ℤ) : ℝ) *
            ((ArithmeticFunction.moebius b : ℤ) : ℝ)| := le_abs_self _
      _ = mobiusSqReal a * mobiusSqReal b := by
        rw [abs_mul, abs_mobius_real_eq_mobiusSqReal,
          abs_mobius_real_eq_mobiusSqReal]
  have hcount := intervalMultipleCount_le_two_mul_div N (Nat.lcm a b)
  calc
    ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
        (intervalMultipleCount N (Nat.lcm a b) : ℝ) ≤
      (mobiusSqReal a * mobiusSqReal b) *
        (intervalMultipleCount N (Nat.lcm a b) : ℝ) := by
          gcongr
    _ ≤ (mobiusSqReal a * mobiusSqReal b) *
        ((2 * (N : ℝ)) / (Nat.lcm a b : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hcount
            (mul_nonneg (mobiusSqReal_nonneg a) (mobiusSqReal_nonneg b))
    _ = (2 * (N : ℝ)) *
        (mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) := by ring

/-- Granville--Ramare Proposition 10.1 in the explicit weakened form needed
by the Type II estimate.  The proof actually gives the smaller coefficient
`16/27`; the published `8/9` form is exposed for downstream use. -/
theorem granville_ramare_prop_10_1
    (N z : ℕ) (hz : 1 ≤ z) :
    (∑ n ∈ Finset.Ioc N (2 * N), truncatedMobiusDivisorSum z n ^ 2) ≤
      (8 / 9 : ℝ) * (N : ℝ) * (Real.log z + 3) ^ 3 := by
  have hpos := sum_mobiusSqReal_lcm_le z hz
  have hlog : 0 ≤ Real.log z + 3 := by
    have : 0 ≤ Real.log (z : ℝ) := Real.log_nonneg (by exact_mod_cast hz)
    linarith
  calc
    (∑ n ∈ Finset.Ioc N (2 * N), truncatedMobiusDivisorSum z n ^ 2) =
        ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
          ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
              ((ArithmeticFunction.moebius b : ℤ) : ℝ) *
            (intervalMultipleCount N (Nat.lcm a b) : ℝ) :=
      sum_truncatedMobiusDivisorSum_sq_eq_lcm N z
    _ ≤ ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
        (2 * (N : ℝ)) *
          (mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact mobius_mul_intervalMultipleCount_le N a b
    _ = (2 * (N : ℝ)) *
        ∑ a ∈ Finset.Icc 1 z, ∑ b ∈ Finset.Icc 1 z,
          mobiusSqReal a * mobiusSqReal b / (Nat.lcm a b : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
    _ ≤ (2 * (N : ℝ)) *
        ((8 / 27 : ℝ) * (Real.log z + 3) ^ 3) := by
      exact mul_le_mul_of_nonneg_left hpos (by positivity)
    _ ≤ (8 / 9 : ℝ) * (N : ℝ) * (Real.log z + 3) ^ 3 := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      have hprod : 0 ≤ (N : ℝ) * (Real.log z + 3) ^ 3 :=
        mul_nonneg hN0 (pow_nonneg hlog 3)
      nlinarith

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/Vaughan.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.

The arithmetic-function proof below is adapted from
`AnalyticNT/Vaughan/Identity.lean` in `gersh/ternary-goldbach-lean`.
-/

/-!
# A finite Vaughan identity for reciprocal exponential sums

This file proves Vaughan's identity first as an equality of arithmetic
functions and then applies it term by term to an arbitrary finite weighted
sum.  The latter formulation can be used with the reciprocal phase
`exp (2 * pi * I * x / n)` without any convergence side conditions.

With `muLow U` and `lambdaLow V` denoting the indicated truncations, the
three pieces are

* `lambdaLow V`;
* `typeI U V = muLow U * (log - zeta * lambdaLow V)`;
* `typeII U V = lambdaHigh V * (muHigh U * zeta)`.

The proved identity is

`vonMangoldt = lambdaLow V + typeI U V + typeII U V`.

The final two theorems also unfold the Type-I and Type-II convolutions as
finite sums over divisor antidiagonals.  These are the forms used before
applying exponential-sum estimates.
-/

noncomputable section

namespace Vaughan

open scoped ArithmeticFunction BigOperators

/-- The Möbius function truncated to indices at most `U`. -/
def muLow (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

/-- The complementary Möbius tail. -/
def muHigh (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if U < n then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

/-- The von Mangoldt function truncated to indices at most `V`. -/
def lambdaLow (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ V then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

/-- The complementary von Mangoldt tail. -/
def lambdaHigh (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if V < n then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

/-- The Type-I part of Vaughan's identity. -/
def typeI (U V : ℕ) : ArithmeticFunction ℝ :=
  muLow U *
    (ArithmeticFunction.log -
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLow V)

/-- The Type-II part of Vaughan's identity. -/
def typeII (U V : ℕ) : ArithmeticFunction ℝ :=
  lambdaHigh V *
    (muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))

/-- The low and high Möbius truncations partition the Möbius function. -/
theorem muLow_add_muHigh (U : ℕ) :
    muLow U + muHigh U =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
  ext n
  change (if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0) +
      (if U < n then (ArithmeticFunction.moebius n : ℝ) else 0) =
    (ArithmeticFunction.moebius n : ℝ)
  by_cases hn : n ≤ U
  · have hnot : ¬ U < n := not_lt.mpr hn
    simp [hn, hnot]
  · have hlt : U < n := lt_of_not_ge hn
    simp [hn, hlt]

/-- The low and high von Mangoldt truncations partition `vonMangoldt`. -/
theorem lambdaLow_add_lambdaHigh (V : ℕ) :
    lambdaLow V + lambdaHigh V =
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) := by
  ext n
  change (if n ≤ V then ArithmeticFunction.vonMangoldt n else 0) +
      (if V < n then ArithmeticFunction.vonMangoldt n else 0) =
    ArithmeticFunction.vonMangoldt n
  by_cases hn : n ≤ V
  · have hnot : ¬ V < n := not_lt.mpr hn
    simp [hn, hnot]
  · have hlt : V < n := lt_of_not_ge hn
    simp [hn, hlt]

/-- The Type-I term can equivalently be written using the high von Mangoldt
tail.  This form makes the final convolution cancellation transparent. -/
theorem typeI_eq (U V : ℕ) :
    typeI U V =
      lambdaHigh V *
        (muLow U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
  have hlog :
      ArithmeticFunction.log -
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLow V =
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaHigh V := by
    calc
      ArithmeticFunction.log -
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLow V =
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLow V := by
              rw [ArithmeticFunction.zeta_mul_vonMangoldt]
      _ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              (lambdaLow V + lambdaHigh V) -
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaLow V := by
              rw [lambdaLow_add_lambdaHigh]
      _ = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaHigh V := by
              ring
  unfold typeI
  rw [hlog]
  ring

/-- The two non-low pieces add to the high von Mangoldt tail. -/
theorem typeI_add_typeII (U V : ℕ) :
    typeI U V + typeII U V = lambdaHigh V := by
  rw [typeI_eq, typeII]
  calc
    lambdaHigh V *
          (muLow U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) +
        lambdaHigh V *
          (muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) =
        lambdaHigh V *
          ((muLow U + muHigh U) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by ring
    _ = lambdaHigh V *
          ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
          rw [muLow_add_muHigh]
    _ = lambdaHigh V := by simp

/-- Vaughan's identity as an equality of arithmetic functions.  No positivity
hypothesis on the cutoffs is needed for this algebraic identity. -/
theorem identity (U V : ℕ) :
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      lambdaLow V + typeI U V + typeII U V := by
  calc
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
        lambdaLow V + lambdaHigh V := (lambdaLow_add_lambdaHigh V).symm
    _ = lambdaLow V + (typeI U V + typeII U V) := by
      rw [typeI_add_typeII]
    _ = lambdaLow V + typeI U V + typeII U V := by ring

/-- A finite sum of an arithmetic function with an arbitrary complex weight. -/
def finiteWeightedSum
    (s : Finset ℕ) (w : ℕ → ℂ) (F : ArithmeticFunction ℝ) : ℂ :=
  ∑ n ∈ s, (F n : ℂ) * w n

/-- The reciprocal additive character `e(x/n)`.  The value at `n = 0` is
harmless in finite sums because every arithmetic function vanishes at zero. -/
def reciprocalPhase (x : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((x / (n : ℝ) : ℝ) : ℂ))

/-- A finite reciprocal exponential sum weighted by an arithmetic function. -/
def reciprocalSum
    (s : Finset ℕ) (x : ℝ) (F : ArithmeticFunction ℝ) : ℂ :=
  finiteWeightedSum s (reciprocalPhase x) F

end Vaughan

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/VaughanFourSums.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The four-sum form of Vaughan's identity used by Granville--Ramaré

This is the exact algebraic content of Lemma 9.1 in Granville--Ramaré.  Put

`a = μ_{≤ M} * ζ`,  `b = μ_{≤ M} * Λ_{≤ K}`.

Split `b` at `M` into `bLow + bHigh`, and remove the convolution identity
coefficient from `a` by writing `a = 1 + aHigh`.  Then

`Λ_{> K} = μ_{≤ M} * log - ζ * bLow - ζ * bHigh - Λ_{> K} * aHigh`.

On an interval `(y,y']` with `K ≤ y`, `Λ = Λ_{>K}` term by term.  Applying
an arbitrary finite weight therefore gives the paper's signed decomposition

`Σ Λ(n)f(n) = Σ₁ - Σ₂,₁ - Σ₂,₂ - Σ₃`.

For the application the weight is `e(x/n)`, but the algebraic theorem is
stated for every complex-valued weight.
-/

noncomputable section

namespace VaughanFourSums

open scoped ArithmeticFunction BigOperators

open Vaughan

/-- `a_l = ∑_{m r = l, m ≤ M} μ(m)`. -/
def aCoeff (M : ℕ) : ArithmeticFunction ℝ :=
  muLow M * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

/-- The portion of `a_l` with `l > M`; below this cutoff the full coefficient
is exactly the Dirichlet-convolution identity. -/
def aHigh (M : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun l => if M < l then aCoeff M l else 0, by simp [aCoeff]⟩

/-- `b_r = ∑_{m k = r, m ≤ M, k ≤ K} μ(m) Λ(k)`. -/
def bCoeff (M K : ℕ) : ArithmeticFunction ℝ :=
  muLow M * lambdaLow K

/-- The part of `b_r` with `r ≤ M`. -/
def bLow (M K : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun r => if r ≤ M then bCoeff M K r else 0, by simp [bCoeff]⟩

/-- The part of `b_r` with `M < r`.  The convolution defining `bCoeff`
automatically vanishes beyond `M*K`. -/
def bHigh (M K : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun r => if M < r then bCoeff M K r else 0, by simp [bCoeff]⟩

/-- The first paper term, `μ_{≤M} * log`. -/
def sigma1AF (M : ℕ) : ArithmeticFunction ℝ :=
  muLow M * ArithmeticFunction.log

/-- The part of `ζ * b` with `r ≤ M`. -/
def sigma21AF (M K : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * bLow M K

/-- The part of `ζ * b` with `M < r ≤ MK`. -/
def sigma22AF (M K : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * bHigh M K

/-- The Type-II paper term, `Λ_{>K} * a_{>M}`. -/
def sigma3AF (M K : ℕ) : ArithmeticFunction ℝ :=
  lambdaHigh K * aHigh M

/-- Below `M`, `a_l` is the convolution identity. -/
theorem aCoeff_eq_one_of_le {M l : ℕ} (hM : 1 ≤ M) (hl : l ≤ M) :
    aCoeff M l = (1 : ArithmeticFunction ℝ) l := by
  rcases Nat.eq_zero_or_pos l with rfl | hlpos
  · simp [aCoeff, ArithmeticFunction.map_zero]
  · rw [aCoeff, ArithmeticFunction.coe_mul_zeta_apply]
    calc
      ∑ d ∈ l.divisors, muLow M d =
          ∑ d ∈ l.divisors, (ArithmeticFunction.moebius d : ℝ) := by
        refine Finset.sum_congr rfl fun d hd => ?_
        change (if d ≤ M then (ArithmeticFunction.moebius d : ℝ) else 0) =
          (ArithmeticFunction.moebius d : ℝ)
        rw [if_pos ((Nat.divisor_le hd).trans hl)]
      _ = (((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) l) := by
        rw [ArithmeticFunction.coe_mul_zeta_apply]
        simp
      _ = (1 : ArithmeticFunction ℝ) l := by
        rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]

/-- The exact decomposition `a = 1 + aHigh`. -/
theorem one_add_aHigh (M : ℕ) (hM : 1 ≤ M) :
    (1 : ArithmeticFunction ℝ) + aHigh M = aCoeff M := by
  ext l
  by_cases hl : l ≤ M
  · have hnot : ¬ M < l := not_lt.mpr hl
    change (1 : ArithmeticFunction ℝ) l +
        (if M < l then aCoeff M l else 0) = aCoeff M l
    rw [if_neg hnot, add_zero, aCoeff_eq_one_of_le hM hl]
  · have hlt : M < l := lt_of_not_ge hl
    have hlone : (1 : ArithmeticFunction ℝ) l = 0 := by
      have hlne : l ≠ 1 := by omega
      simp [hlne]
    change (1 : ArithmeticFunction ℝ) l +
        (if M < l then aCoeff M l else 0) = aCoeff M l
    rw [if_pos hlt, hlone, zero_add]

/-- The two ranges of the `b` coefficient form all of `b`. -/
theorem bLow_add_bHigh (M K : ℕ) :
    bLow M K + bHigh M K = bCoeff M K := by
  ext r
  change (if r ≤ M then bCoeff M K r else 0) +
      (if M < r then bCoeff M K r else 0) = bCoeff M K r
  by_cases hr : r ≤ M
  · simp [hr, not_lt.mpr hr]
  · simp [hr, lt_of_not_ge hr]

/-- Every truncated Möbius coefficient has absolute value at most one. -/
lemma abs_muLow_le_one (M m : ℕ) : |muLow M m| ≤ (1 : ℝ) := by
  unfold muLow
  by_cases hm : m ≤ M
  · simp [hm]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m)
  · simp [hm]

/-- Truncation preserves nonnegativity of the von Mangoldt function. -/
lemma lambdaLow_nonneg (K k : ℕ) : 0 ≤ lambdaLow K k := by
  change 0 ≤ if k ≤ K then ArithmeticFunction.vonMangoldt k else 0
  by_cases hk : k ≤ K
  · simp [hk, ArithmeticFunction.vonMangoldt_nonneg]
  · simp [hk]

/-- The truncated von Mangoldt function is bounded by the full function. -/
lemma lambdaLow_le (K k : ℕ) :
    lambdaLow K k ≤ ArithmeticFunction.vonMangoldt k := by
  change (if k ≤ K then ArithmeticFunction.vonMangoldt k else 0) ≤
    ArithmeticFunction.vonMangoldt k
  by_cases hk : k ≤ K
  · simp [hk]
  · simp [hk, ArithmeticFunction.vonMangoldt_nonneg]

/-- Granville--Ramaré's elementary coefficient estimate
`|b_r| ≤ log r`.  The proof uses only `|μ| ≤ 1`, positivity of `Λ`, and
`∑_{d∣r} Λ(d) = log r`; hence both truncations may be completely arbitrary. -/
theorem abs_bCoeff_le_log (M K r : ℕ) :
    |bCoeff M K r| ≤ Real.log r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [bCoeff, ArithmeticFunction.map_zero]
  · rw [bCoeff, ArithmeticFunction.mul_apply]
    calc
      |∑ mk ∈ r.divisorsAntidiagonal,
          muLow M mk.1 * lambdaLow K mk.2| ≤
          ∑ mk ∈ r.divisorsAntidiagonal,
            |muLow M mk.1 * lambdaLow K mk.2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ mk ∈ r.divisorsAntidiagonal,
          ArithmeticFunction.vonMangoldt mk.2 := by
        refine Finset.sum_le_sum fun mk _hmk => ?_
        rw [abs_mul, abs_of_nonneg (lambdaLow_nonneg K mk.2)]
        calc
          |muLow M mk.1| * lambdaLow K mk.2 ≤
              1 * lambdaLow K mk.2 := by
            exact mul_le_mul_of_nonneg_right
              (abs_muLow_le_one M mk.1) (lambdaLow_nonneg K mk.2)
          _ ≤ ArithmeticFunction.vonMangoldt mk.2 := by
            simpa using lambdaLow_le K mk.2
      _ = (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ)) r) := by
        rw [ArithmeticFunction.mul_apply]
        refine Finset.sum_congr rfl fun mk _hmk => ?_
        have hm0 : mk.1 ≠ 0 :=
          Nat.left_ne_zero_of_mem_divisorsAntidiagonal _hmk
        simp [hm0]
      _ = Real.log r := by
        rw [ArithmeticFunction.zeta_mul_vonMangoldt]
        simp [ArithmeticFunction.log_apply]

/-- The coefficient `b_r` is supported on `r ≤ M*K`. -/
theorem bCoeff_eq_zero_of_mul_lt
    (M K r : ℕ) (hr : M * K < r) : bCoeff M K r = 0 := by
  rw [bCoeff, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro mk hmk
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hmk).1
  by_cases hm : mk.1 ≤ M
  · have hk : K < mk.2 := by
      apply lt_of_not_ge
      intro hkle
      have hmul : mk.1 * mk.2 ≤ M * K := Nat.mul_le_mul hm hkle
      rw [hprod] at hmul
      exact (not_le_of_gt hr) hmul
    change (if mk.1 ≤ M then (ArithmeticFunction.moebius mk.1 : ℝ) else 0) *
        (if mk.2 ≤ K then ArithmeticFunction.vonMangoldt mk.2 else 0) = 0
    simp [hm, not_le.mpr hk]
  · change (if mk.1 ≤ M then (ArithmeticFunction.moebius mk.1 : ℝ) else 0) *
        (if mk.2 ≤ K then ArithmeticFunction.vonMangoldt mk.2 else 0) = 0
    simp [hm]

/-- The logarithmic piece is `a * Λ`. -/
theorem sigma1AF_eq (M : ℕ) :
    sigma1AF M =
      aCoeff M *
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) := by
  unfold sigma1AF aCoeff
  rw [← ArithmeticFunction.zeta_mul_vonMangoldt]
  ring

/-- The two `Σ₂` pieces reassemble as `a * Λ_{≤K}`. -/
theorem sigma21AF_add_sigma22AF (M K : ℕ) :
    sigma21AF M K + sigma22AF M K = aCoeff M * lambdaLow K := by
  unfold sigma21AF sigma22AF
  rw [← mul_add, bLow_add_bHigh]
  unfold bCoeff aCoeff
  ring

/-- The global four-piece arithmetic-function identity. -/
theorem four_piece_identity (M K : ℕ) (hM : 1 ≤ M) :
    sigma1AF M - sigma21AF M K - sigma22AF M K - sigma3AF M K =
      lambdaHigh K := by
  have ha : aCoeff M = (1 : ArithmeticFunction ℝ) + aHigh M :=
    (one_add_aHigh M hM).symm
  have hΛ :
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
        lambdaLow K + lambdaHigh K := (lambdaLow_add_lambdaHigh K).symm
  rw [show sigma1AF M = aCoeff M *
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) from sigma1AF_eq M]
  calc
    aCoeff M * (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
          sigma21AF M K - sigma22AF M K - sigma3AF M K =
        aCoeff M * (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
          (sigma21AF M K + sigma22AF M K) - sigma3AF M K := by ring
    _ = aCoeff M * (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
          aCoeff M * lambdaLow K - lambdaHigh K * aHigh M := by
      rw [sigma21AF_add_sigma22AF]
      rfl
    _ = lambdaHigh K := by
      rw [ha, hΛ]
      ring

/-- The weighted version of each paper term. -/
def sigma1 (s : Finset ℕ) (w : ℕ → ℂ) (M : ℕ) : ℂ :=
  finiteWeightedSum s w (sigma1AF M)

def sigma21 (s : Finset ℕ) (w : ℕ → ℂ) (M K : ℕ) : ℂ :=
  finiteWeightedSum s w (sigma21AF M K)

def sigma22 (s : Finset ℕ) (w : ℕ → ℂ) (M K : ℕ) : ℂ :=
  finiteWeightedSum s w (sigma22AF M K)

def sigma3 (s : Finset ℕ) (w : ℕ → ℂ) (M K : ℕ) : ℂ :=
  finiteWeightedSum s w (sigma3AF M K)

/-! ## Exact product regrouping -/

/-- The possible second factors for a fixed positive first factor `m`, subject
to `y < m*l ≤ y'`. -/
def innerProductInterval (y y' m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 y').filter fun l => y < m * l ∧ m * l ≤ y'

/-- For a positive multiplier, the product condition is the usual quotient
interval. -/
theorem innerProductInterval_eq_Ioc
    (y y' m : ℕ) (hm : 0 < m) :
    innerProductInterval y y' m = Finset.Ioc (y / m) (y' / m) := by
  ext l
  simp only [innerProductInterval, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_Ioc]
  constructor
  · rintro ⟨_hl, hyl, hly'⟩
    constructor
    · apply (Nat.div_lt_iff_lt_mul hm).2
      simpa [Nat.mul_comm] using hyl
    · apply (Nat.le_div_iff_mul_le hm).2
      simpa [Nat.mul_comm] using hly'
  · rintro ⟨hyl, hly'⟩
    have hyl' : y < m * l := by
      simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hm).1 hyl
    have hly'' : m * l ≤ y' := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).1 hly'
    have hlpos : 0 < l := lt_of_le_of_lt (Nat.zero_le _) hyl
    have hlle : l ≤ y' :=
      (Nat.le_mul_of_pos_left l hm).trans hly''
    exact ⟨⟨hlpos, hlle⟩, hyl', hly''⟩

/-- All factor pairs whose product belongs to `(y,y']`, with the first
factor restricted to `[1,M]`. -/
def factorPairs (y y' M : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 M).product (Finset.Icc 1 y')).filter fun ml =>
    y < ml.1 * ml.2 ∧ ml.1 * ml.2 ≤ y'

/-- Flatten the divisor antidiagonals of all integers in `(y,y']`. -/
def flatInterval (y y' : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc y y').biUnion fun n => n.divisorsAntidiagonal

private theorem divisorsAntidiagonal_pairwiseDisjoint (y y' : ℕ) :
    ((Finset.Ioc y y' : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun n => n.divisorsAntidiagonal := by
  intro a _ha b _hb hab
  simp only [Function.onFun]
  refine Finset.disjoint_left.mpr ?_
  intro p hpa hpb
  rw [Nat.mem_divisorsAntidiagonal] at hpa hpb
  exact hab (by rw [← hpa.1, ← hpb.1])

private theorem sum_Ioc_antidiagonal_eq_flatInterval
    {R : Type*} [AddCommMonoid R] (y y' : ℕ) (F : ℕ × ℕ → R) :
    ∑ n ∈ Finset.Ioc y y', ∑ p ∈ n.divisorsAntidiagonal, F p =
      ∑ p ∈ flatInterval y y', F p := by
  rw [flatInterval,
    Finset.sum_biUnion (divisorsAntidiagonal_pairwiseDisjoint y y')]

/-- Regroup a weighted convolution over `(y,y']` with a first factor
supported on `[1,M]`.  This is a completely finite equality. -/
theorem finiteWeightedSum_Ioc_mul_eq_outer
    (y y' M : ℕ) (w : ℕ → ℂ) (A B : ArithmeticFunction ℝ)
    (hA : ∀ m, M < m → A m = 0) :
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
      ∑ m ∈ Finset.Icc 1 M, ∑ l ∈ innerProductInterval y y' m,
        (A m : ℂ) * (B l : ℂ) * w (m * l) := by
  unfold finiteWeightedSum
  calc
    (∑ n ∈ Finset.Ioc y y', ((A * B) n : ℂ) * w n) =
        ∑ n ∈ Finset.Ioc y y', ∑ ml ∈ n.divisorsAntidiagonal,
          (A ml.1 : ℂ) * (B ml.2 : ℂ) * w (ml.1 * ml.2) := by
      refine Finset.sum_congr rfl fun n _hn => ?_
      rw [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ml hml => ?_
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hml).1
      rw [hprod]
      push_cast
      ring
    _ = ∑ ml ∈ flatInterval y y',
          (A ml.1 : ℂ) * (B ml.2 : ℂ) * w (ml.1 * ml.2) :=
      sum_Ioc_antidiagonal_eq_flatInterval y y' _
    _ = ∑ ml ∈ factorPairs y y' M,
          (A ml.1 : ℂ) * (B ml.2 : ℂ) * w (ml.1 * ml.2) := by
      symm
      refine Finset.sum_subset ?_ ?_
      · intro ml hml
        rw [factorPairs] at hml
        obtain ⟨hmlmem, hyl, hly'⟩ := Finset.mem_filter.mp hml
        obtain ⟨hm, hl⟩ := Finset.mem_product.mp hmlmem
        rw [flatInterval, Finset.mem_biUnion]
        refine ⟨ml.1 * ml.2, ?_, ?_⟩
        · exact Finset.mem_Ioc.mpr ⟨hyl, hly'⟩
        · rw [Nat.mem_divisorsAntidiagonal]
          exact ⟨rfl, by
            have hmpos := (Finset.mem_Icc.mp hm).1
            have hlpos := (Finset.mem_Icc.mp hl).1
            positivity⟩
      · intro ml hflat hnot
        rw [flatInterval, Finset.mem_biUnion] at hflat
        obtain ⟨n, hn, hml⟩ := hflat
        have hprod := (Nat.mem_divisorsAntidiagonal.mp hml).1
        have hmpos : 0 < ml.1 :=
          Nat.pos_of_ne_zero
            (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hml)
        have hlpos : 0 < ml.2 :=
          Nat.pos_of_ne_zero
            (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hml)
        have hle2 : ml.2 ≤ n := by
          have h := Nat.le_mul_of_pos_left ml.2 hmpos
          rwa [hprod] at h
        have hgt : M < ml.1 := by
          by_contra hnotgt
          apply hnot
          rw [factorPairs]
          apply Finset.mem_filter.mpr
          have hn' := Finset.mem_Ioc.mp hn
          exact ⟨Finset.mem_product.mpr
              ⟨Finset.mem_Icc.mpr ⟨hmpos, Nat.le_of_not_gt hnotgt⟩,
                Finset.mem_Icc.mpr ⟨hlpos, hle2.trans hn'.2⟩⟩,
            by simpa [hprod] using hn'.1,
            by simpa [hprod] using hn'.2⟩
        rw [hA ml.1 hgt, Complex.ofReal_zero, zero_mul, zero_mul]
    _ = ∑ m ∈ Finset.Icc 1 M, ∑ l ∈ innerProductInterval y y' m,
          (A m : ℂ) * (B l : ℂ) * w (m * l) := by
      simp only [factorPairs, innerProductInterval, Finset.sum_filter]
      rw [← Finset.sum_product']
      rfl

/-
/-- Without a support hypothesis the first factor is automatically at most
the interval's upper endpoint. -/
theorem finiteWeightedSum_Ioc_mul_eq_outer_to_endpoint
    (y y' : ℕ) (w : ℕ → ℂ) (A B : ArithmeticFunction ℝ) :
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
      ∑ m ∈ Finset.Icc 1 y', ∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (A m : ℂ) * (B l : ℂ) * w (m * l) := by
  unfold finiteWeightedSum
  calc
    (∑ n ∈ Finset.Ioc y y', ((A * B) n : ℂ) * w n) =
        ∑ n ∈ Finset.Ioc y y', ∑ ml ∈ n.divisorsAntidiagonal,
          (A ml.1 : ℂ) * (B ml.2 : ℂ) * w (ml.1 * ml.2) := by
      refine Finset.sum_congr rfl fun n _hn => ?_
      rw [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ml hml => ?_
      rw [(Nat.mem_divisorsAntidiagonal.mp hml).1]
      push_cast
      ring
    _ = ∑ ml ∈ flatInterval y y',
          (A ml.1 : ℂ) * (B ml.2 : ℂ) * w (ml.1 * ml.2) :=
      sum_Ioc_antidiagonal_eq_flatInterval y y' _
    _ = ∑ ml ∈ factorPairs y y' y',
          (A ml.1 : ℂ) * (B ml.2 : ℂ) * w (ml.1 * ml.2) := by
      apply Finset.sum_congr
      · ext ml
        constructor
        · intro hflat
          rw [flatInterval, Finset.mem_biUnion] at hflat
          obtain ⟨n, hn, hml⟩ := hflat
          have hprod := (Nat.mem_divisorsAntidiagonal.mp hml).1
          have hmpos : 0 < ml.1 := Nat.pos_of_ne_zero
            (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hml)
          have hlpos : 0 < ml.2 := Nat.pos_of_ne_zero
            (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hml)
          have hle1 : ml.1 ≤ n := by
            have h := Nat.le_mul_of_pos_right ml.1 hlpos
            rwa [hprod] at h
          have hle2 : ml.2 ≤ n := by
            have h := Nat.le_mul_of_pos_left ml.2 hmpos
            rwa [hprod] at h
          rw [factorPairs]
          apply Finset.mem_filter.mpr
          have hn' := Finset.mem_Ioc.mp hn
          exact ⟨Finset.mem_product.mpr
              ⟨Finset.mem_Icc.mpr ⟨hmpos, hle1.trans hn'.2⟩,
                Finset.mem_Icc.mpr ⟨hlpos, hle2.trans hn'.2⟩⟩,
            by simpa [hprod] using hn'.1,
            by simpa [hprod] using hn'.2⟩
        · intro hpairs
          rw [factorPairs] at hpairs
          obtain ⟨_hmem, hyl, hly'⟩ := Finset.mem_filter.mp hpairs
          rw [flatInterval, Finset.mem_biUnion]
          refine ⟨ml.1 * ml.2, Finset.mem_Ioc.mpr ⟨hyl, hly'⟩, ?_⟩
          rw [Nat.mem_divisorsAntidiagonal]
          exact ⟨rfl, by
            obtain ⟨hm, hl⟩ := Finset.mem_product.mp _hmem
            have hmpos := (Finset.mem_Icc.mp hm).1
            have hlpos := (Finset.mem_Icc.mp hl).1
            positivity⟩
      · intro _ _
        rfl
    _ = ∑ m ∈ Finset.Icc 1 y', ∑ l ∈ innerProductInterval y y' m,
          (A m : ℂ) * (B l : ℂ) * w (m * l) := by
      simp only [factorPairs, innerProductInterval, Finset.sum_filter]
      rw [← Finset.sum_product']
      rfl
    _ = ∑ m ∈ Finset.Icc 1 y', ∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (A m : ℂ) * (B l : ℂ) * w (m * l) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [innerProductInterval_eq_Ioc y y' m (Finset.mem_Icc.mp hm).1]

/-- Lower-annular form of the endpoint regrouping. -/
theorem finiteWeightedSum_Ioc_mul_eq_outer_endpoint_Ioc
    (y y' L : ℕ) (w : ℕ → ℂ) (A B : ArithmeticFunction ℝ)
    (hBelow : ∀ m, m ≤ L → A m = 0) :
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
      ∑ m ∈ Finset.Ioc L y', ∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (A m : ℂ) * (B l : ℂ) * w (m * l) := by
  rw [finiteWeightedSum_Ioc_mul_eq_outer_to_endpoint]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro m hm
    have hm' := Finset.mem_Ioc.mp hm
    exact Finset.mem_Icc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) hm'.1, hm'.2⟩
  · intro m hmIcc hmnot
    have hmle : m ≤ L := by
      by_contra hnotle
      apply hmnot
      exact Finset.mem_Ioc.mpr ⟨lt_of_not_ge hnotle, (Finset.mem_Icc.mp hmIcc).2⟩
    simp [hBelow m hmle]

-/
/-- Expanded paper form of `Σ₁`. -/
theorem sigma1_Ioc_eq_outer
    (y y' M : ℕ) (w : ℕ → ℂ) :
    sigma1 (Finset.Ioc y y') w M =
      ∑ m ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (ArithmeticFunction.moebius m : ℂ) *
          (Real.log l : ℂ) * w (m * l) := by
  unfold sigma1 sigma1AF
  rw [finiteWeightedSum_Ioc_mul_eq_outer]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [innerProductInterval_eq_Ioc y y' m (Finset.mem_Icc.mp hm).1]
    refine Finset.sum_congr rfl fun l _hl => ?_
    have hmle := (Finset.mem_Icc.mp hm).2
    change ((if m ≤ M then (ArithmeticFunction.moebius m : ℝ) else 0 : ℝ) : ℂ) *
        ((ArithmeticFunction.log l : ℝ) : ℂ) * w (m * l) = _
    rw [if_pos hmle]
    simp [ArithmeticFunction.log_apply]
  · intro m hm
    change (if m ≤ M then (ArithmeticFunction.moebius m : ℝ) else 0) = 0
    rw [if_neg (not_le.mpr hm)]

/-- Expanded paper form of `Σ₂,₁`. -/
theorem sigma21_Ioc_eq_outer
    (y y' M K : ℕ) (w : ℕ → ℂ) :
    sigma21 (Finset.Ioc y y') w M K =
      ∑ r ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Ioc (y / r) (y' / r),
        (bCoeff M K r : ℂ) * w (r * l) := by
  unfold sigma21 sigma21AF
  rw [mul_comm]
  rw [finiteWeightedSum_Ioc_mul_eq_outer]
  · refine Finset.sum_congr rfl fun r hr => ?_
    rw [innerProductInterval_eq_Ioc y y' r (Finset.mem_Icc.mp hr).1]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hrle := (Finset.mem_Icc.mp hr).2
    have hlne : l ≠ 0 := Nat.ne_of_gt
      (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hl).1)
    change ((if r ≤ M then bCoeff M K r else 0 : ℝ) : ℂ) *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) l : ℂ) * w (r * l) = _
    rw [if_pos hrle]
    simp [hlne]
  · intro r hr
    change (if r ≤ M then bCoeff M K r else 0) = 0
    rw [if_neg (not_le.mpr hr)]

/-- Granville--Ramaré Lemma 9.1 for an arbitrary finite set supported above
`K`. -/
theorem finite_four_sum_identity
    (s : Finset ℕ) (w : ℕ → ℂ) (M K : ℕ) (hM : 1 ≤ M)
    (hs : ∀ n ∈ s, K < n) :
    finiteWeightedSum s w
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      sigma1 s w M - sigma21 s w M K - sigma22 s w M K - sigma3 s w M K := by
  unfold sigma1 sigma21 sigma22 sigma3 finiteWeightedSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hpoint := congr_arg (fun F : ArithmeticFunction ℝ => F n)
    (four_piece_identity M K hM)
  have hhigh : lambdaHigh K n = ArithmeticFunction.vonMangoldt n := by
    simp [lambdaHigh, hs n hn]
  rw [hhigh] at hpoint
  have hpointC :
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) =
        (((sigma1AF M - sigma21AF M K - sigma22AF M K - sigma3AF M K) n : ℝ) : ℂ) := by
    exact_mod_cast hpoint.symm
  rw [hpointC]
  simp only [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply]
  push_cast
  ring

/-- The interval version of Lemma 9.1. -/
theorem Ioc_four_sum_identity
    (y y' M K : ℕ) (w : ℕ → ℂ) (hM : 1 ≤ M) (hKy : K ≤ y) :
    finiteWeightedSum (Finset.Ioc y y') w
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      sigma1 (Finset.Ioc y y') w M -
        sigma21 (Finset.Ioc y y') w M K -
        sigma22 (Finset.Ioc y y') w M K -
        sigma3 (Finset.Ioc y y') w M K := by
  apply finite_four_sum_identity _ _ _ _ hM
  intro n hn
  exact lt_of_le_of_lt hKy (Finset.mem_Ioc.mp hn).1

/-- Lemma 9.1 specialized to the reciprocal phase `e(x/n)`. -/
theorem reciprocal_Ioc_four_sum_identity
    (y y' M K : ℕ) (x : ℝ) (hM : 1 ≤ M) (hKy : K ≤ y) :
    reciprocalSum (Finset.Ioc y y') x
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
      sigma1 (Finset.Ioc y y') (Erdos175.Vaughan.reciprocalPhase x) M -
        sigma21 (Finset.Ioc y y') (Erdos175.Vaughan.reciprocalPhase x) M K -
        sigma22 (Finset.Ioc y y') (Erdos175.Vaughan.reciprocalPhase x) M K -
        sigma3 (Finset.Ioc y y') (Erdos175.Vaughan.reciprocalPhase x) M K := by
  exact Ioc_four_sum_identity y y' M K (Erdos175.Vaughan.reciprocalPhase x) hM hKy

end VaughanFourSums

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/VanDerCorput.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# A finite van der Corput averaging inequality

This file isolates the algebraic averaging step in van der Corput's method.
For a sequence supported on `0, ..., N - 1`, average its `H` translates in
the zero-padded interval `0, ..., N + H - 2`.  Cauchy--Schwarz then gives an
inequality whose shift length `H` remains free.

The formulation before expanding the square is useful in its own right: a
later argument may expand the sliding-window energy and estimate its
correlations in whichever form is most convenient.
-/

open scoped BigOperators ComplexConjugate

namespace VanDerCorput

/-- The `h`-th zero-padded translate of a finite sequence at the point `m`.
It is `z (m - h)` precisely when that index belongs to `Finset.range N`. -/
def translatedTerm (z : ℕ → ℂ) (N m h : ℕ) : ℂ :=
  if h ≤ m ∧ m - h < N then z (m - h) else 0

/-- The sum of the first `H` zero-padded translates at `m`. -/
def slidingWindow (z : ℕ → ℂ) (N H m : ℕ) : ℂ :=
  ∑ h ∈ Finset.range H, translatedTerm z N m h

/-- The strict upper-triangular part of the correlation matrix of a finite
complex sequence. -/
def strictUpper (w : ℕ → ℂ) (H : ℕ) : ℂ :=
  ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h, w h * conj (w k)

/-- The strict upper-triangular part of the correlation matrix of the
translated terms at one padded index. -/
def strictUpperAt (z : ℕ → ℂ) (N H m : ℕ) : ℂ :=
  strictUpper (fun h ↦ translatedTerm z N m h) H

/-- Polarization of a finite complex sum into its diagonal and strict upper
triangle. -/
lemma sum_mul_conj_sum_eq_diagonal_add_strictUpper
    (w : ℕ → ℂ) (H : ℕ) :
    (∑ h ∈ Finset.range H, w h) * conj (∑ h ∈ Finset.range H, w h) =
      (∑ h ∈ Finset.range H, w h * conj (w h)) +
        strictUpper w H + conj (strictUpper w H) := by
  induction H with
  | zero => simp [strictUpper]
  | succ H ih =>
      have hupper : strictUpper w (H + 1) =
          strictUpper w H + ∑ k ∈ Finset.range H, w H * conj (w k) := by
        simp [strictUpper, Finset.sum_range_succ]
      rw [Finset.sum_range_succ, map_add, hupper]
      simp only [Finset.sum_range_succ, map_add, starRingEnd_apply]
      simp_rw [← Finset.mul_sum]
      simp only [← star_sum, star_mul, star_star]
      simp only [Complex.star_def] at ih ⊢
      linear_combination ih

/-- Real form of finite polarization. -/
lemma sq_norm_sum_eq_diagonal_add_two_re_strictUpper
    (w : ℕ → ℂ) (H : ℕ) :
    ‖∑ h ∈ Finset.range H, w h‖ ^ 2 =
      (∑ h ∈ Finset.range H, ‖w h‖ ^ 2) +
        2 * (strictUpper w H).re := by
  have h := sum_mul_conj_sum_eq_diagonal_add_strictUpper w H
  rw [Complex.mul_conj'] at h
  simp_rw [Complex.mul_conj'] at h
  rw [add_assoc] at h
  rw [Complex.add_conj] at h
  exact_mod_cast h

/-- On the natural padded interval, every fixed translate has the same sum
as the original finite sequence. -/
lemma sum_translatedTerm (z : ℕ → ℂ) (N H h : ℕ) (hh : h < H) :
    (∑ m ∈ Finset.range (N + H - 1), translatedTerm z N m h) =
      ∑ n ∈ Finset.range N, z n := by
  classical
  simp only [translatedTerm, ← Finset.sum_filter]
  apply Finset.sum_bij (fun m _hm ↦ m - h)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
    exact hm.2.2
  · intro m₁ hm₁ m₂ hm₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hm₁ hm₂
    omega
  · intro n hn
    simp only [Finset.mem_range] at hn
    refine ⟨n + h, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · omega
  · intro m hm
    rfl

/-- The squared norms in a single zero-padded translate have the same sum as
the squared norms in the original interval. -/
lemma sum_sq_norm_translatedTerm
    (z : ℕ → ℂ) (N H h : ℕ) (hh : h < H) :
    (∑ m ∈ Finset.range (N + H - 1), ‖translatedTerm z N m h‖ ^ 2) =
      ∑ n ∈ Finset.range N, ‖z n‖ ^ 2 := by
  classical
  have hterm (m : ℕ) :
      ‖translatedTerm z N m h‖ ^ 2 =
        if h ≤ m ∧ m - h < N then ‖z (m - h)‖ ^ 2 else 0 := by
    by_cases hm : h ≤ m ∧ m - h < N <;> simp [translatedTerm, hm]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun m _hm ↦ m - h)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
    exact hm.2.2
  · intro m₁ hm₁ m₂ hm₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hm₁ hm₂
    omega
  · intro n hn
    simp only [Finset.mem_range] at hn
    refine ⟨n + h, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · omega
  · intro m hm
    rfl

/-- Summing all sliding windows counts each term of the original sequence
exactly `H` times.  This identity remains valid for `N = 0` or `H = 0`. -/
lemma sum_slidingWindow (z : ℕ → ℂ) (N H : ℕ) :
    (∑ m ∈ Finset.range (N + H - 1), slidingWindow z N H m) =
      (H : ℂ) * ∑ n ∈ Finset.range N, z n := by
  classical
  simp only [slidingWindow]
  calc
    (∑ m ∈ Finset.range (N + H - 1),
        ∑ h ∈ Finset.range H, translatedTerm z N m h) =
        ∑ h ∈ Finset.range H,
          ∑ m ∈ Finset.range (N + H - 1), translatedTerm z N m h := by
      rw [Finset.sum_comm]
    _ = ∑ h ∈ Finset.range H, ∑ n ∈ Finset.range N, z n := by
      apply Finset.sum_congr rfl
      intro h hh
      exact sum_translatedTerm z N H h (Finset.mem_range.mp hh)
    _ = (H : ℂ) * ∑ n ∈ Finset.range N, z n := by simp

/-- **Finite van der Corput averaging inequality.**

For every complex sequence and every natural `N, H`,
`H²` times the squared norm of its length-`N` sum is bounded by the length
of the zero-padded interval times the energy of the `H`-translate sliding
windows.  Keeping natural-number coefficients cast to `ℝ` avoids division,
so no side condition such as `0 < H` is needed. -/
theorem sq_norm_sum_le_slidingWindow_energy
    (z : ℕ → ℂ) (N H : ℕ) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 ≤
      (N + H - 1 : ℕ) *
        ∑ m ∈ Finset.range (N + H - 1), ‖slidingWindow z N H m‖ ^ 2 := by
  classical
  let S : ℂ := ∑ n ∈ Finset.range N, z n
  let W : ℕ → ℂ := slidingWindow z N H
  have hsum : ∑ m ∈ Finset.range (N + H - 1), W m = (H : ℂ) * S := by
    simpa [S, W] using sum_slidingWindow z N H
  have htriangle :
      ‖∑ m ∈ Finset.range (N + H - 1), W m‖ ≤
        ∑ m ∈ Finset.range (N + H - 1), ‖W m‖ :=
    norm_sum_le _ _
  have hsquare :
      ‖∑ m ∈ Finset.range (N + H - 1), W m‖ ^ 2 ≤
        (∑ m ∈ Finset.range (N + H - 1), ‖W m‖) ^ 2 := by
    rw [sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    exact htriangle
  have hcauchy :
      (∑ m ∈ Finset.range (N + H - 1), ‖W m‖) ^ 2 ≤
        (N + H - 1 : ℕ) *
          ∑ m ∈ Finset.range (N + H - 1), ‖W m‖ ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.range (N + H - 1)) (f := fun m ↦ ‖W m‖))
  calc
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 =
        ‖(H : ℂ) * S‖ ^ 2 := by
      simp only [S, norm_mul, Complex.norm_natCast]
      ring
    _ = ‖∑ m ∈ Finset.range (N + H - 1), W m‖ ^ 2 := by rw [hsum]
    _ ≤ (∑ m ∈ Finset.range (N + H - 1), ‖W m‖) ^ 2 := hsquare
    _ ≤ (N + H - 1 : ℕ) *
          ∑ m ∈ Finset.range (N + H - 1), ‖W m‖ ^ 2 := hcauchy
    _ = (N + H - 1 : ℕ) *
          ∑ m ∈ Finset.range (N + H - 1),
            ‖slidingWindow z N H m‖ ^ 2 := by rfl

/-- The total sliding-window energy is bounded by its diagonal plus the norm
of the aggregate strict-upper correlation.  Crucially, the norm is outside
the sum over padded indices, so cancellation is retained. -/
lemma slidingWindow_energy_le_diagonal_add_correlation
    (z : ℕ → ℂ) (N H : ℕ) :
    (∑ m ∈ Finset.range (N + H - 1), ‖slidingWindow z N H m‖ ^ 2) ≤
      (H : ℝ) * (∑ n ∈ Finset.range N, ‖z n‖ ^ 2) +
        2 * ‖∑ m ∈ Finset.range (N + H - 1), strictUpperAt z N H m‖ := by
  classical
  have hdiag :
      (∑ m ∈ Finset.range (N + H - 1),
          ∑ h ∈ Finset.range H, ‖translatedTerm z N m h‖ ^ 2) =
        (H : ℝ) * ∑ n ∈ Finset.range N, ‖z n‖ ^ 2 := by
    calc
      (∑ m ∈ Finset.range (N + H - 1),
          ∑ h ∈ Finset.range H, ‖translatedTerm z N m h‖ ^ 2) =
          ∑ h ∈ Finset.range H,
            ∑ m ∈ Finset.range (N + H - 1),
              ‖translatedTerm z N m h‖ ^ 2 := by
        rw [Finset.sum_comm]
      _ = ∑ h ∈ Finset.range H,
          ∑ n ∈ Finset.range N, ‖z n‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro h hh
        exact sum_sq_norm_translatedTerm z N H h (Finset.mem_range.mp hh)
      _ = (H : ℝ) * ∑ n ∈ Finset.range N, ‖z n‖ ^ 2 := by simp
  have henergy :
      (∑ m ∈ Finset.range (N + H - 1), ‖slidingWindow z N H m‖ ^ 2) =
        (H : ℝ) * (∑ n ∈ Finset.range N, ‖z n‖ ^ 2) +
          2 * (∑ m ∈ Finset.range (N + H - 1),
            strictUpperAt z N H m).re := by
    calc
      (∑ m ∈ Finset.range (N + H - 1), ‖slidingWindow z N H m‖ ^ 2) =
          ∑ m ∈ Finset.range (N + H - 1),
            ((∑ h ∈ Finset.range H, ‖translatedTerm z N m h‖ ^ 2) +
              2 * (strictUpperAt z N H m).re) := by
        apply Finset.sum_congr rfl
        intro m _hm
        exact sq_norm_sum_eq_diagonal_add_two_re_strictUpper
          (fun h ↦ translatedTerm z N m h) H
      _ = (∑ m ∈ Finset.range (N + H - 1),
            ∑ h ∈ Finset.range H, ‖translatedTerm z N m h‖ ^ 2) +
          2 * (∑ m ∈ Finset.range (N + H - 1),
            strictUpperAt z N H m).re := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, Complex.re_sum]
      _ = _ := by rw [hdiag]
  rw [henergy]
  gcongr
  exact Complex.re_le_norm _

/-- Correlation form of the finite van der Corput inequality.  This is the
same adjustable-shift estimate as `sq_norm_sum_le_slidingWindow_energy`, with
the sliding-window square polarized and its diagonal evaluated exactly. -/
theorem sq_norm_sum_le_diagonal_add_correlation
    (z : ℕ → ℂ) (N H : ℕ) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 ≤
      (N + H - 1 : ℕ) *
        ((H : ℝ) * (∑ n ∈ Finset.range N, ‖z n‖ ^ 2) +
          2 * ‖∑ m ∈ Finset.range (N + H - 1), strictUpperAt z N H m‖) := by
  calc
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, z n‖ ^ 2 ≤
        (N + H - 1 : ℕ) *
          ∑ m ∈ Finset.range (N + H - 1), ‖slidingWindow z N H m‖ ^ 2 :=
      sq_norm_sum_le_slidingWindow_energy z N H
    _ ≤ (N + H - 1 : ℕ) *
        ((H : ℝ) * (∑ n ∈ Finset.range N, ‖z n‖ ^ 2) +
          2 * ‖∑ m ∈ Finset.range (N + H - 1), strictUpperAt z N H m‖) := by
      gcongr
      exact slidingWindow_energy_le_diagonal_add_correlation z N H

end VanDerCorput

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/KusminLandau.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The Kusmin--Landau first derivative estimate

This file proves the first-derivative exponential-sum estimate used as
Lemma 8.4 of Granville--Ramaré, *Explicit bounds on exponential sums and the
scarcity of squarefree binomial coefficients*.  The proof is split into a
finite telescoping identity and a calculus wrapper.  The convention is
`expPhase x = exp (2 * π * i * x)`.
-/

open scoped BigOperators
open Set Finset

noncomputable section

/-- The standard real additive character `e(x) = exp(2πix)`. -/
def expPhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma expPhase_eq_e (x : ℝ) : expPhase x = e x := by
  unfold expPhase e
  congr 1
  push_cast
  ring

lemma star_expPhase (x : ℝ) : (starRingEnd ℂ) (expPhase x) = expPhase (-x) := by
  simpa only [expPhase_eq_e] using conj_e x

@[simp] lemma norm_expPhase (x : ℝ) : ‖expPhase x‖ = 1 := by
  unfold expPhase
  convert Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x) using 1

@[simp] lemma expPhase_ne_zero (x : ℝ) : expPhase x ≠ 0 := by
  exact Complex.exp_ne_zero _

lemma expPhase_add (x y : ℝ) : expPhase (x + y) = expPhase x * expPhase y := by
  rw [expPhase, expPhase, expPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The reciprocal chord which occurs in the Kusmin--Landau telescoping
argument. -/
def chordInv (x : ℝ) : ℂ :=
  (1 - expPhase x)⁻¹

/-- On the upper semicircle, the reciprocal chord has constant real part.
This identity is the geometric reason that the variation term in the
Kusmin--Landau proof telescopes without loss. -/
lemma chordInv_eq_half_add_cot_mul_I {x : ℝ}
    (hs : Real.sin (Real.pi * x) ≠ 0) :
    chordInv x =
      (1 / 2 : ℂ) +
        (((Real.cos (Real.pi * x) / Real.sin (Real.pi * x)) / 2 : ℝ) : ℂ) * Complex.I := by
  unfold chordInv expPhase
  rw [show (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) =
      (((2 * (Real.pi * x) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_ofReal_mul_I, Real.cos_two_mul, Real.sin_two_mul]
  apply Complex.ext <;>
    simp only [Complex.inv_re, Complex.inv_im, Complex.normSq_apply,
      Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  · norm_num
    have hu := Real.sin_sq_add_cos_sq (Real.pi * x)
    have hc : 1 - Real.cos (Real.pi * x) ^ 2 = Real.sin (Real.pi * x) ^ 2 := by
      nlinarith
    rw [show 1 - (2 * Real.cos (Real.pi * x) ^ 2 - 1) =
        2 * Real.sin (Real.pi * x) ^ 2 by nlinarith]
    field_simp [hs]
    linear_combination -hu
  · norm_num
    have hu := Real.sin_sq_add_cos_sq (Real.pi * x)
    have hc : 1 - Real.cos (Real.pi * x) ^ 2 = Real.sin (Real.pi * x) ^ 2 := by
      nlinarith
    rw [show 1 - (2 * Real.cos (Real.pi * x) ^ 2 - 1) =
        2 * Real.sin (Real.pi * x) ^ 2 by nlinarith]
    field_simp [hs]
    linear_combination -Real.cos (Real.pi * x) * hu

/-- The real cotangent factor occurring in `chordInv`.  It is named
separately so that no complex cotangent API is needed below. -/
def cotPi (x : ℝ) : ℝ :=
  Real.cos (Real.pi * x) / Real.sin (Real.pi * x)

lemma sin_pi_mul_pos {x : ℝ} (hx : 0 < x) (hxhalf : x ≤ 1 / 2) :
    0 < Real.sin (Real.pi * x) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

lemma two_mul_le_sin_pi_mul {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    2 * x ≤ Real.sin (Real.pi * x) := by
  have h := Real.mul_le_sin (x := Real.pi * x) (by positivity)
    (by nlinarith [Real.pi_pos] : Real.pi * x ≤ Real.pi / 2)
  convert h using 1 <;> field_simp [Real.pi_ne_zero]

lemma cotPi_antitoneOn : AntitoneOn cotPi (Ioc 0 (1 / 2 : ℝ)) := by
  intro x hx y hy hxy
  have hsx : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx.1 hx.2
  have hsy : 0 < Real.sin (Real.pi * y) := sin_pi_mul_pos hy.1 hy.2
  rw [cotPi, cotPi, div_le_div_iff₀ hsy hsx]
  have hsin : 0 ≤ Real.sin (Real.pi * y - Real.pi * x) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · rw [show Real.pi * y - Real.pi * x = Real.pi * (y - x) by ring]
      exact mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hxy)
    · rw [show Real.pi * y - Real.pi * x = Real.pi * (y - x) by ring]
      have hyx : y - x ≤ 1 := by linarith [hx.1, hy.2]
      calc
        Real.pi * (y - x) ≤ Real.pi * 1 :=
          mul_le_mul_of_nonneg_left hyx Real.pi_pos.le
        _ = Real.pi := mul_one _
  rw [Real.sin_sub] at hsin
  nlinarith

lemma chordInv_sub_norm {x y : ℝ}
    (hx : x ∈ Ioc 0 (1 / 2 : ℝ)) (hy : y ∈ Ioc 0 (1 / 2 : ℝ)) (hxy : x ≤ y) :
    ‖chordInv y - chordInv x‖ = (cotPi x - cotPi y) / 2 := by
  rw [chordInv_eq_half_add_cot_mul_I (sin_pi_mul_pos hx.1 hx.2).ne',
    chordInv_eq_half_add_cot_mul_I (sin_pi_mul_pos hy.1 hy.2).ne']
  have hcot : cotPi y ≤ cotPi x := cotPi_antitoneOn hx hy hxy
  let cx : ℝ := Real.cos (Real.pi * x) / Real.sin (Real.pi * x)
  let cy : ℝ := Real.cos (Real.pi * y) / Real.sin (Real.pi * y)
  simp only [cotPi]
  change ‖(1 / 2 : ℂ) + ((cy / 2 : ℝ) : ℂ) * Complex.I -
      ((1 / 2 : ℂ) + ((cx / 2 : ℝ) : ℂ) * Complex.I)‖ = (cx - cy) / 2
  rw [show (1 / 2 : ℂ) + ((cy / 2 : ℝ) : ℂ) * Complex.I -
        ((1 / 2 : ℂ) + ((cx / 2 : ℝ) : ℂ) * Complex.I) =
      ((((cy - cx) / 2 : ℝ) : ℂ) * Complex.I) by push_cast; ring]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    abs_of_nonpos]
  · ring
  · dsimp [cotPi, cx, cy] at hcot
    linarith

lemma chordInv_sub_norm_of_ge {x y : ℝ}
    (hx : x ∈ Ioc 0 (1 / 2 : ℝ)) (hy : y ∈ Ioc 0 (1 / 2 : ℝ)) (hyx : y ≤ x) :
    ‖chordInv y - chordInv x‖ = (cotPi y - cotPi x) / 2 := by
  rw [← norm_neg, neg_sub]
  exact chordInv_sub_norm hy hx hyx

lemma chordInv_norm_le {m x : ℝ} (hm : 0 < m) (hmx : m ≤ x) (hxhalf : x ≤ 1 / 2) :
    ‖chordInv x‖ ≤ 1 / (4 * m) := by
  have hx : 0 < x := hm.trans_le hmx
  have hs : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx hxhalf
  have hsin : 2 * x ≤ Real.sin (Real.pi * x) :=
    two_mul_le_sin_pi_mul hx.le hxhalf
  unfold chordInv
  rw [norm_inv, ← norm_neg, neg_sub]
  have hnorm : ‖expPhase x - 1‖ = 2 * Real.sin (Real.pi * x) := by
    unfold expPhase
    rw [show (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) =
        Complex.I * (((2 * Real.pi * x : ℝ) : ℂ)) by ring,
      Complex.norm_exp_I_mul_ofReal_sub_one]
    norm_num
    rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
    rw [abs_of_pos hs]
  rw [hnorm]
  have hden : 4 * m ≤ 2 * Real.sin (Real.pi * x) := by nlinarith
  simpa [one_div] using (one_div_le_one_div_of_le (by positivity) hden)

lemma norm_one_sub_chordInv_eq {x : ℝ} (hx : 0 < x) (hxhalf : x ≤ 1 / 2) :
    ‖1 - chordInv x‖ = ‖chordInv x‖ := by
  rw [chordInv_eq_half_add_cot_mul_I (sin_pi_mul_pos hx hxhalf).ne']
  let c : ℝ := Real.cos (Real.pi * x) / Real.sin (Real.pi * x)
  change ‖1 - ((1 / 2 : ℂ) + ((c / 2 : ℝ) : ℂ) * Complex.I)‖ =
    ‖(1 / 2 : ℂ) + ((c / 2 : ℝ) : ℂ) * Complex.I‖
  rw [show 1 - ((1 / 2 : ℂ) + ((c / 2 : ℝ) : ℂ) * Complex.I) =
      (1 / 2 : ℂ) + ((-c / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

lemma cotPi_nonneg {x : ℝ} (hx : 0 < x) (hxhalf : x ≤ 1 / 2) : 0 ≤ cotPi x := by
  have hsin : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx hxhalf
  have hcos : 0 ≤ Real.cos (Real.pi * x) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  exact div_nonneg hcos hsin.le

lemma cotPi_le_inv_two_mul {m x : ℝ}
    (hm : 0 < m) (hmx : m ≤ x) (hxhalf : x ≤ 1 / 2) :
    cotPi x ≤ 1 / (2 * m) := by
  have hx : 0 < x := hm.trans_le hmx
  have hsin : 0 < Real.sin (Real.pi * x) := sin_pi_mul_pos hx hxhalf
  have hsin_lower : 2 * m ≤ Real.sin (Real.pi * x) := by
    have := two_mul_le_sin_pi_mul hx.le hxhalf
    linarith
  calc
    cotPi x ≤ 1 / Real.sin (Real.pi * x) := by
      rw [cotPi, div_le_div_iff₀ hsin hsin]
      nlinarith [Real.cos_le_one (Real.pi * x)]
    _ ≤ 1 / (2 * m) := one_div_le_one_div_of_le (by positivity) hsin_lower

/-- A finite summation-by-parts identity tailored to the reciprocal-chord
proof. -/
lemma phase_telescoping_identity (A z : ℕ → ℂ) (N : ℕ)
    (hstep : ∀ n ≤ N, z n = A n * (z n - z (n + 1))) :
    ∑ n ∈ range (N + 2), z n =
      A 0 * z 0 + (1 - A N) * z (N + 1) +
        ∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1) := by
  induction N with
  | zero =>
      norm_num [sum_range_succ]
      linear_combination hstep 0 le_rfl
  | succ N ih =>
      have ih' := ih (fun n hn ↦ hstep n (hn.trans (Nat.le_succ N)))
      rw [show N + 1 + 2 = (N + 2) + 1 by omega, sum_range_succ, ih',
        sum_range_succ]
      linear_combination hstep (N + 1) le_rfl

lemma sum_range_adjacent_sub (c : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, (c n - c (n + 1)) = c 0 - c N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih]
      ring

lemma sum_range_adjacent_sub_rev (c : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ range N, (c (n + 1) - c n) = c N - c 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih]
      ring

/-- Discrete Kusmin--Landau estimate for forward differences monotone in
either direction.  The constant `1 / m` is a convenient rational weakening
of the classical `cot (π m / 2)` bound. -/
theorem kusminLandau_discrete_of_monotone_or_antitone
    (u : ℕ → ℝ) {m : ℝ} (hm : 0 < m) (N : ℕ)
    (hbounds : ∀ n ≤ N, m ≤ u (n + 1) - u n ∧ u (n + 1) - u n ≤ 1 / 2)
    (hmonotone :
      (∀ n < N, u (n + 1) - u n ≤ u (n + 2) - u (n + 1)) ∨
      (∀ n < N, u (n + 2) - u (n + 1) ≤ u (n + 1) - u n)) :
    ‖∑ n ∈ range (N + 2), expPhase (u n)‖ ≤ 1 / m := by
  let d : ℕ → ℝ := fun n ↦ u (n + 1) - u n
  let A : ℕ → ℂ := fun n ↦ chordInv (d n)
  let z : ℕ → ℂ := fun n ↦ expPhase (u n)
  have hd (n : ℕ) (hn : n ≤ N) : m ≤ d n ∧ d n ≤ 1 / 2 := hbounds n hn
  have hdpos (n : ℕ) (hn : n ≤ N) : 0 < d n := hm.trans_le (hd n hn).1
  have hden (n : ℕ) (hn : n ≤ N) : 1 - expPhase (d n) ≠ 0 := by
    intro he
    have hzero : chordInv (d n) = 0 := by simp [chordInv, he]
    have hform := chordInv_eq_half_add_cot_mul_I
      (sin_pi_mul_pos (hdpos n hn) (hd n hn).2).ne'
    rw [hzero] at hform
    let c : ℝ := Real.cos (Real.pi * d n) / Real.sin (Real.pi * d n)
    change (0 : ℂ) = (1 / 2 : ℂ) + ((c / 2 : ℝ) : ℂ) * Complex.I at hform
    have hre : (0 : ℝ) = 1 / 2 := by
      calc
        (0 : ℝ) = (0 : ℂ).re := rfl
        _ = ((1 / 2 : ℂ) + ((c / 2 : ℝ) : ℂ) * Complex.I).re :=
          congrArg Complex.re hform
        _ = 1 / 2 := by norm_num [Complex.mul_re]
    norm_num at hre
  have hz_mul (n : ℕ) : z (n + 1) = z n * expPhase (d n) := by
    dsimp [z, d]
    rw [← expPhase_add]
    congr 1
    ring
  have hphase (n : ℕ) (hn : n ≤ N) : z n = A n * (z n - z (n + 1)) := by
    rw [hz_mul]
    dsimp [A]
    unfold chordInv
    field_simp [hden n hn]
  have hid := phase_telescoping_identity A z N hphase
  change ‖∑ n ∈ range (N + 2), z n‖ ≤ 1 / m
  rw [hid]
  have hA0 : ‖A 0‖ ≤ 1 / (4 * m) := by
    exact chordInv_norm_le hm (hd 0 (Nat.zero_le N)).1 (hd 0 (Nat.zero_le N)).2
  have hAN : ‖1 - A N‖ ≤ 1 / (4 * m) := by
    rw [norm_one_sub_chordInv_eq (hdpos N le_rfl) (hd N le_rfl).2]
    exact chordInv_norm_le hm (hd N le_rfl).1 (hd N le_rfl).2
  have hsumNorm :
      ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ ≤ 1 / (4 * m) := by
    rcases hmonotone with hmono | hanti
    · have htel :
          ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ ≤
            (cotPi (d 0) - cotPi (d N)) / 2 := by
        calc
          _ ≤ ∑ n ∈ range N, ‖(A (n + 1) - A n) * z (n + 1)‖ :=
            norm_sum_le _ _
          _ = ∑ n ∈ range N, (cotPi (d n) - cotPi (d (n + 1))) / 2 := by
            apply sum_congr rfl
            intro n hn
            have hnlt : n < N := mem_range.mp hn
            rw [norm_mul, show ‖z (n + 1)‖ = 1 by simp [z], mul_one]
            exact chordInv_sub_norm
              ⟨hdpos n (by omega), (hd n (by omega)).2⟩
              ⟨hdpos (n + 1) (by omega), (hd (n + 1) (by omega)).2⟩
              (hmono n hnlt)
          _ = (cotPi (d 0) - cotPi (d N)) / 2 := by
            rw [← sum_div, sum_range_adjacent_sub]
      have hnonneg : 0 ≤ cotPi (d N) := cotPi_nonneg (hdpos N le_rfl) (hd N le_rfl).2
      have hupper : cotPi (d 0) ≤ 1 / (2 * m) :=
        cotPi_le_inv_two_mul hm (hd 0 (Nat.zero_le N)).1 (hd 0 (Nat.zero_le N)).2
      refine htel.trans ?_
      calc
        (cotPi (d 0) - cotPi (d N)) / 2 ≤ cotPi (d 0) / 2 := by linarith
        _ ≤ (1 / (2 * m)) / 2 := by gcongr
        _ = 1 / (4 * m) := by field_simp; norm_num
    · have htel :
          ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ ≤
            (cotPi (d N) - cotPi (d 0)) / 2 := by
        calc
          _ ≤ ∑ n ∈ range N, ‖(A (n + 1) - A n) * z (n + 1)‖ :=
            norm_sum_le _ _
          _ = ∑ n ∈ range N, (cotPi (d (n + 1)) - cotPi (d n)) / 2 := by
            apply sum_congr rfl
            intro n hn
            have hnlt : n < N := mem_range.mp hn
            rw [norm_mul, show ‖z (n + 1)‖ = 1 by simp [z], mul_one]
            exact chordInv_sub_norm_of_ge
              ⟨hdpos n (by omega), (hd n (by omega)).2⟩
              ⟨hdpos (n + 1) (by omega), (hd (n + 1) (by omega)).2⟩
              (hanti n hnlt)
          _ = (cotPi (d N) - cotPi (d 0)) / 2 := by
            rw [← sum_div]
            exact congrArg (fun t : ℝ ↦ t / 2)
              (sum_range_adjacent_sub_rev (fun n ↦ cotPi (d n)) N)
      have hnonneg : 0 ≤ cotPi (d 0) :=
        cotPi_nonneg (hdpos 0 (Nat.zero_le N)) (hd 0 (Nat.zero_le N)).2
      have hupper : cotPi (d N) ≤ 1 / (2 * m) :=
        cotPi_le_inv_two_mul hm (hd N le_rfl).1 (hd N le_rfl).2
      refine htel.trans ?_
      calc
        (cotPi (d N) - cotPi (d 0)) / 2 ≤ cotPi (d N) / 2 := by linarith
        _ ≤ (1 / (2 * m)) / 2 := by gcongr
        _ = 1 / (4 * m) := by field_simp; norm_num
  have htri :
      ‖A 0 * z 0 + (1 - A N) * z (N + 1) +
          ∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ ≤
        ‖A 0‖ + ‖1 - A N‖ +
          ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ := by
    calc
      _ ≤ ‖A 0 * z 0 + (1 - A N) * z (N + 1)‖ +
          ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ := norm_add_le _ _
      _ ≤ (‖A 0 * z 0‖ + ‖(1 - A N) * z (N + 1)‖) +
          ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ := by
            gcongr
            exact norm_add_le _ _
      _ = ‖A 0‖ + ‖1 - A N‖ +
          ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ := by
            simp [z]
  calc
    _ ≤ ‖A 0‖ + ‖1 - A N‖ +
        ‖∑ n ∈ range N, (A (n + 1) - A n) * z (n + 1)‖ := htri
    _ ≤ 1 / (4 * m) + 1 / (4 * m) + 1 / (4 * m) := by
      gcongr
    _ ≤ 1 / m := by
      have hq : 0 ≤ 1 / (4 * m) := by positivity
      have heq : 1 / m = 4 * (1 / (4 * m)) := by field_simp
      rw [heq]
      linarith

/-- First-derivative Kusmin--Landau estimate on a real interval.  This is the
calculus-facing form of Granville--Ramaré Lemma 8.4 (with the harmlessly
weaker rational constant `1 / m`). -/
theorem kusminLandau_of_deriv_monotone_or_antitone
    (f : ℝ → ℝ) (a : ℝ) {m : ℝ} (hm : 0 < m) (N : ℕ)
    (hdiff : DifferentiableOn ℝ f (Icc a (a + (N + 1 : ℕ))))
    (hderiv_bounds : ∀ x ∈ Icc a (a + (N + 1 : ℕ)),
      m ≤ deriv f x ∧ deriv f x ≤ 1 / 2)
    (hderiv_monotone :
      MonotoneOn (deriv f) (Icc a (a + (N + 1 : ℕ))) ∨
      AntitoneOn (deriv f) (Icc a (a + (N + 1 : ℕ)))) :
    ‖∑ n ∈ range (N + 2), expPhase (f (a + n))‖ ≤ 1 / m := by
  let u : ℕ → ℝ := fun n ↦ f (a + n)
  have hmean (n : ℕ) (hn : n ≤ N) :
      ∃ c ∈ Ioo (a + (n : ℝ)) (a + (n + 1 : ℕ)),
        u (n + 1) - u n = deriv f c := by
    let x : ℝ := a + n
    let y : ℝ := a + (n + 1 : ℕ)
    have hxy : x < y := by dsimp [x, y]; norm_num
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
    have hsubcc : Icc x y ⊆ Icc a (a + (N + 1 : ℕ)) := by
      intro t ht
      dsimp [x, y] at ht
      constructor
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        exact (le_add_of_nonneg_right hn0).trans ht.1
      · norm_num at ht ⊢
        linarith
    have hsuboo : Ioo x y ⊆ Icc a (a + (N + 1 : ℕ)) :=
      Ioo_subset_Icc_self.trans hsubcc
    obtain ⟨c, hc, hcder⟩ := exists_deriv_eq_slope f hxy
      (hdiff.continuousOn.mono hsubcc) (hdiff.mono hsuboo)
    refine ⟨c, hc, ?_⟩
    dsimp [u, x, y] at hcder ⊢
    have hunit : a + (n + 1 : ℕ) - (a + (n : ℝ)) = 1 := by norm_num
    rw [hunit, div_one] at hcder
    simpa using hcder.symm
  have hbounds : ∀ n ≤ N,
      m ≤ u (n + 1) - u n ∧ u (n + 1) - u n ≤ 1 / 2 := by
    intro n hn
    obtain ⟨c, hc, heq⟩ := hmean n hn
    have hcwhole : c ∈ Icc a (a + (N + 1 : ℕ)) := by
      constructor
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        linarith [hc.1]
      · have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
        norm_num at hc ⊢
        linarith [hc.2]
    simpa [heq] using hderiv_bounds c hcwhole
  apply kusminLandau_discrete_of_monotone_or_antitone u hm N hbounds
  rcases hderiv_monotone with hinc | hdec
  · left
    intro n hn
    obtain ⟨c, hc, hcEq⟩ := hmean n (by omega)
    obtain ⟨d, hd, hdEq⟩ := hmean (n + 1) (by omega)
    have hcwhole : c ∈ Icc a (a + (N + 1 : ℕ)) := by
      constructor
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        linarith [hc.1]
      · have hnR : (n : ℝ) < N := by exact_mod_cast hn
        norm_num at hc ⊢
        linarith [hc.2]
    have hdwhole : d ∈ Icc a (a + (N + 1 : ℕ)) := by
      constructor
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        norm_num at hd
        linarith [hd.1]
      · have hnR : (n : ℝ) < N := by exact_mod_cast hn
        norm_num at hd ⊢
        have hn2 : (n : ℝ) + 2 ≤ (N : ℝ) + 1 := by
          have hs : (n : ℝ) + 1 ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
          linarith
        calc
          d ≤ a + ((n : ℝ) + 1 + 1) := hd.2.le
          _ = a + ((n : ℝ) + 2) := by ring
          _ ≤ a + ((N : ℝ) + 1) := add_le_add_right hn2 a
    rw [hcEq, hdEq]
    exact hinc hcwhole hdwhole (le_of_lt (hc.2.trans hd.1))
  · right
    intro n hn
    obtain ⟨c, hc, hcEq⟩ := hmean n (by omega)
    obtain ⟨d, hd, hdEq⟩ := hmean (n + 1) (by omega)
    have hcwhole : c ∈ Icc a (a + (N + 1 : ℕ)) := by
      constructor
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        linarith [hc.1]
      · have hnR : (n : ℝ) < N := by exact_mod_cast hn
        norm_num at hc ⊢
        linarith [hc.2]
    have hdwhole : d ∈ Icc a (a + (N + 1 : ℕ)) := by
      constructor
      · have hn0 : (0 : ℝ) ≤ n := by positivity
        norm_num at hd
        linarith [hd.1]
      · have hnR : (n : ℝ) < N := by exact_mod_cast hn
        norm_num at hd ⊢
        have hn2 : (n : ℝ) + 2 ≤ (N : ℝ) + 1 := by
          have hs : (n : ℝ) + 1 ≤ N := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
          linarith
        calc
          d ≤ a + ((n : ℝ) + 1 + 1) := hd.2.le
          _ = a + ((n : ℝ) + 2) := by ring
          _ ≤ a + ((N : ℝ) + 1) := add_le_add_right hn2 a
    rw [hcEq, hdEq]
    exact hdec hcwhole hdwhole (le_of_lt (hc.2.trans hd.1))

/-! ### The once-differenced reciprocal phase -/

/-- A forward difference with positive increment `r`. -/
def onceDiff (f : ℝ → ℝ) (r t : ℝ) : ℝ :=
  f (t + r) - f t

/-- The mean value theorem expresses a forward difference using a derivative
at an intermediate point. -/
lemma onceDiff_eq_mul_deriv (f f' : ℝ → ℝ) {t r : ℝ} (hr : 0 < r)
    (hf : ∀ u ∈ Icc t (t + r), HasDerivAt f (f' u) u) :
    ∃ ξ ∈ Ioo t (t + r), onceDiff f r t = r * f' ξ := by
  have hcont : ContinuousOn f (Icc t (t + r)) :=
    fun u hu ↦ (hf u hu).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξSlope⟩ := exists_hasDerivAt_eq_slope f f'
    (by linarith : t < t + r) hcont (fun u hu ↦ hf u (Ioo_subset_Icc_self hu))
  refine ⟨ξ, hξ, ?_⟩
  have hr0 : t + r - t = r := by ring
  rw [hr0] at hξSlope
  have hEq := (eq_div_iff (ne_of_gt hr)).mp hξSlope
  dsimp [onceDiff]
  nlinarith

/-- Differentiating a forward difference commutes with taking the forward
difference. -/
lemma hasDerivAt_onceDiff (f f' : ℝ → ℝ) (r t : ℝ)
    (h0 : HasDerivAt f (f' t) t)
    (hr : HasDerivAt f (f' (t + r)) (t + r)) :
    HasDerivAt (onceDiff f r) (onceDiff f' r t) t := by
  have hshift : HasDerivAt (fun u : ℝ ↦ f (u + r)) (f' (t + r)) t := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      hr.comp t ((hasDerivAt_id t).add_const r)
  change HasDerivAt ((fun u : ℝ ↦ f (u + r)) - f) (f' (t + r) - f' t) t
  exact hshift.sub h0

/-- The once-differenced reciprocal phase `x/(t+r) - x/t`. -/
def onceDiffReciprocal (x r t : ℝ) : ℝ :=
  onceDiff (reciprocalPhase x) r t

/-! ### The twice-differenced reciprocal phase -/

/-- The mixed forward difference with positive increments `r` and `s`. -/
def twiceDiff (f : ℝ → ℝ) (r s t : ℝ) : ℝ :=
  (f (t + r + s) - f (t + r)) - (f (t + s) - f t)

/-- Two applications of the mean value theorem express a mixed difference in
terms of a second derivative at an intermediate point. -/
lemma twiceDiff_eq_mul_secondDeriv
    (f f' f'' : ℝ → ℝ) {t r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hf : ∀ u ∈ Icc t (t + r + s), HasDerivAt f (f' u) u)
    (hf' : ∀ u ∈ Icc t (t + r + s), HasDerivAt f' (f'' u) u) :
    ∃ ξ ∈ Ioo t (t + r + s), twiceDiff f r s t = r * s * f'' ξ := by
  let h : ℝ → ℝ := fun u ↦ f (u + s) - f u
  let h' : ℝ → ℝ := fun u ↦ f' (u + s) - f' u
  have hh : ∀ u ∈ Icc t (t + r), HasDerivAt h (h' u) u := by
    intro u hu
    have hu0 : u ∈ Icc t (t + r + s) := by
      exact ⟨hu.1, hu.2.trans (by linarith)⟩
    have hus : u + s ∈ Icc t (t + r + s) := by
      exact ⟨hu.1.trans (by linarith), by linarith [hu.2]⟩
    have hshift : HasDerivAt (fun v : ℝ ↦ f (v + s)) (f' (u + s)) u :=
      by simpa only [Function.comp_def, id_eq, mul_one] using
        (hf (u + s) hus).comp u ((hasDerivAt_id u).add_const s)
    change HasDerivAt ((fun v : ℝ ↦ f (v + s)) - f) (f' (u + s) - f' u) u
    exact hshift.sub (hf u hu0)
  have hcont : ContinuousOn h (Icc t (t + r)) :=
    fun u hu ↦ (hh u hu).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcSlope⟩ := exists_hasDerivAt_eq_slope h h'
    (by linarith : t < t + r) hcont (fun u hu ↦ hh u (Ioo_subset_Icc_self hu))
  have hc0 : c ∈ Icc t (t + r + s) := by
    exact ⟨hc.1.le, hc.2.le.trans (by linarith)⟩
  have hcs : c + s ∈ Icc t (t + r + s) := by
    exact ⟨hc.1.le.trans (by linarith), by linarith [hc.2]⟩
  have hprimeDeriv : ∀ u ∈ Icc c (c + s), HasDerivAt f' (f'' u) u := by
    intro u hu
    apply hf' u
    exact ⟨hc.1.le.trans hu.1, hu.2.trans (by linarith [hc.2])⟩
  have hprimeCont : ContinuousOn f' (Icc c (c + s)) :=
    fun u hu ↦ (hprimeDeriv u hu).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξSlope⟩ := exists_hasDerivAt_eq_slope f' f''
    (by linarith : c < c + s) hprimeCont
    (fun u hu ↦ hprimeDeriv u (Ioo_subset_Icc_self hu))
  refine ⟨ξ, ?_, ?_⟩
  · exact ⟨hc.1.trans hξ.1, hξ.2.trans (by linarith [hc.2])⟩
  · dsimp [h, h'] at hcSlope
    rw [show t + r + s = (t + r) + s by ring] at hcSlope
    dsimp [twiceDiff]
    have hr0 : t + r - t = r := by ring
    have hs0 : c + s - c = s := by ring
    rw [hr0] at hcSlope
    rw [hs0] at hξSlope
    have hcEq := (eq_div_iff (ne_of_gt hr)).mp hcSlope
    have hξEq := (eq_div_iff (ne_of_gt hs)).mp hξSlope
    nlinarith

/-- Differentiating a mixed difference commutes with taking the mixed
difference. -/
lemma hasDerivAt_twiceDiff (f f' : ℝ → ℝ) (r s t : ℝ)
    (h0 : HasDerivAt f (f' t) t)
    (hr : HasDerivAt f (f' (t + r)) (t + r))
    (hs : HasDerivAt f (f' (t + s)) (t + s))
    (hrs : HasDerivAt f (f' (t + r + s)) (t + r + s)) :
    HasDerivAt (twiceDiff f r s) (twiceDiff f' r s t) t := by
  have shift (c : ℝ) (hc : HasDerivAt f (f' (t + c)) (t + c)) :
      HasDerivAt (fun u : ℝ ↦ f (u + c)) (f' (t + c)) t := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      hc.comp t ((hasDerivAt_id t).add_const c)
  have hrs' : HasDerivAt (fun u : ℝ ↦ f (u + r + s)) (f' (t + r + s)) t := by
    have h := shift (r + s) (by simpa [add_assoc] using hrs)
    convert h using 1
    · ext u
      congr 1
      ring
    · congr 1
      ring
  have hr' := shift r hr
  have hs' := shift s hs
  change HasDerivAt
    (((fun u : ℝ ↦ f (u + r + s)) - (fun u : ℝ ↦ f (u + r))) -
      ((fun u : ℝ ↦ f (u + s)) - f))
    ((f' (t + r + s) - f' (t + r)) - (f' (t + s) - f' t)) t
  exact (hrs'.sub hr').sub (hs'.sub h0)

/-- The twice-differenced reciprocal phase used after the last van der
Corput step. -/
def twiceDiffReciprocal (x r s t : ℝ) : ℝ :=
  twiceDiff (reciprocalPhase x) r s t

private lemma hasDerivAt_reciprocalSquare (x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ x / u ^ 2) (-2 * x / t ^ 3) t := by
  have h := (hasDerivAt_const (x := t) x).div ((hasDerivAt_id t).pow 2)
    (pow_ne_zero 2 ht)
  apply h.congr_deriv
  simp only [Pi.pow_apply, id_eq]
  field_simp [ht]
  ring

private lemma hasDerivAt_reciprocalSquare_deriv (x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ -2 * x / u ^ 3) (6 * x / t ^ 4) t := by
  have h := (hasDerivAt_const (x := t) (-2 * x)).div ((hasDerivAt_id t).pow 3)
    (pow_ne_zero 3 ht)
  apply h.congr_deriv
  simp only [Pi.pow_apply, id_eq]
  field_simp [ht]
  ring

private lemma hasDerivAt_reciprocalSquare_deriv2 (x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ 6 * x / u ^ 4) (-24 * x / t ^ 5) t := by
  have h := (hasDerivAt_const (x := t) (6 * x)).div ((hasDerivAt_id t).pow 4)
    (pow_ne_zero 4 ht)
  apply h.congr_deriv
  simp only [Pi.pow_apply, id_eq]
  field_simp [ht]
  ring

private lemma hasDerivAt_onceDiffReciprocal
    (x r t : ℝ) (ht : 0 < t) (hr : 0 < r) :
    HasDerivAt (onceDiffReciprocal x r)
      (-onceDiff (fun u : ℝ ↦ x / u ^ 2) r t) t := by
  have h0 := hasDerivAt_reciprocalPhase x (ne_of_gt ht)
  have hR := hasDerivAt_reciprocalPhase x (ne_of_gt (by linarith : 0 < t + r))
  have h := hasDerivAt_onceDiff (reciprocalPhase x)
    (fun u : ℝ ↦ -x / u ^ 2) r t h0 hR
  change HasDerivAt (onceDiff (reciprocalPhase x) r)
    (-onceDiff (fun u : ℝ ↦ x / u ^ 2) r t) t
  apply h.congr_deriv
  simp only [onceDiff]
  ring

private lemma neg_onceDiff_reciprocalSquare_eq
    {x r t : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ∃ ξ ∈ Ioo t (t + r),
      -onceDiff (fun u : ℝ ↦ x / u ^ 2) r t = 2 * x * r / ξ ^ 3 := by
  obtain ⟨ξ, hξ, hξEq⟩ := onceDiff_eq_mul_deriv
    (fun u : ℝ ↦ x / u ^ 2) (fun u : ℝ ↦ -2 * x / u ^ 3) hr
    (fun u hu ↦ hasDerivAt_reciprocalSquare x (ne_of_gt (ht.trans_le hu.1)))
  refine ⟨ξ, hξ, ?_⟩
  rw [hξEq]
  ring

private lemma antitoneOn_neg_onceDiff_reciprocalSquare
    {x r a A : ℝ} (hx : 0 < x) (hr : 0 < r) (ha : 0 < a) :
    AntitoneOn (-onceDiff (fun u : ℝ ↦ x / u ^ 2) r) (Icc a A) := by
  let q : ℝ → ℝ := fun u ↦ x / u ^ 2
  let q' : ℝ → ℝ := fun u ↦ -2 * x / u ^ 3
  let D : ℝ → ℝ := -onceDiff q r
  have hd : ∀ t ∈ Icc a A, HasDerivAt D (-onceDiff q' r t) t := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have h0 := hasDerivAt_reciprocalSquare x (ne_of_gt ht0)
    have hR := hasDerivAt_reciprocalSquare x
      (ne_of_gt (by linarith : 0 < t + r))
    exact (hasDerivAt_onceDiff q q' r t h0 hR).neg
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a A)
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hd t (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    have htI : t ∈ Icc a A := interior_subset ht
    have ht0 : 0 < t := ha.trans_le htI.1
    obtain ⟨ξ, hξ, hξEq⟩ := onceDiff_eq_mul_deriv q'
      (fun u : ℝ ↦ 6 * x / u ^ 4) hr
      (fun u hu ↦ hasDerivAt_reciprocalSquare_deriv x
        (ne_of_gt (ht0.trans_le hu.1)))
    rw [hξEq]
    have hξ0 : 0 < ξ := ht0.trans hξ.1
    have hlast : 0 < 6 * x / ξ ^ 4 := by positivity
    exact neg_nonpos.mpr (mul_nonneg hr.le hlast.le)

/-- The concrete first-derivative estimate for a once-differenced reciprocal
phase.  Its derivative lies between `2*x*r/B^3` and `2*x*r/a^3`; the last
hypothesis is the latter endpoint written in the convenient form used in the
one-step van der Corput argument. -/
theorem kusminLandau_onceDiffReciprocal
    (x r a B : ℝ) (N : ℕ)
    (hx : 0 < x) (hr : 0 < r) (ha : 0 < a)
    (hendpoint : a + (N + 1 : ℕ) + r ≤ B)
    (hupper : 4 * x * r / a ^ 3 ≤ 1) :
    ‖∑ n ∈ range (N + 2), expPhase (onceDiffReciprocal x r (a + n))‖ ≤
      B ^ 3 / (2 * x * r) := by
  let F : ℝ → ℝ := onceDiffReciprocal x r
  let D : ℝ → ℝ := -onceDiff (fun u : ℝ ↦ x / u ^ 2) r
  let m : ℝ := 2 * x * r / B ^ 3
  have hC : 0 < 2 * x * r := by positivity
  have hN0 : (0 : ℝ) ≤ (N + 1 : ℕ) := by positivity
  have hB : 0 < B := by nlinarith [hendpoint]
  have hm : 0 < m := by
    dsimp [m]
    exact div_pos hC (pow_pos hB 3)
  have hhalf : 2 * x * r / a ^ 3 ≤ 1 / 2 := by
    rw [show 2 * x * r / a ^ 3 = (4 * x * r / a ^ 3) / 2 by ring]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [hupper]
  have hF : ∀ t ∈ Icc a (a + (N + 1 : ℕ)), HasDerivAt F (D t) t := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    change HasDerivAt F (-onceDiff (fun u : ℝ ↦ x / u ^ 2) r t) t
    simpa only [F] using hasDerivAt_onceDiffReciprocal x r t ht0 hr
  have hbounds : ∀ t ∈ Icc a (a + (N + 1 : ℕ)),
      m ≤ deriv F t ∧ deriv F t ≤ 1 / 2 := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    obtain ⟨ξ, hξ, hξEq⟩ := neg_onceDiff_reciprocalSquare_eq
      (x := x) (r := r) (t := t) ht0 hr
    have haξ : a < ξ := ht.1.trans_lt hξ.1
    have htB : t + r ≤ B := by linarith [ht.2, hendpoint]
    have hξB : ξ < B := hξ.2.trans_le htB
    have hξ0 : 0 < ξ := ha.trans haξ
    have ha3 : 0 < a ^ 3 := pow_pos ha 3
    have hξ3 : 0 < ξ ^ 3 := pow_pos hξ0 3
    have hB3 : 0 < B ^ 3 := pow_pos hB 3
    have haξ3 : a ^ 3 ≤ ξ ^ 3 := by
      gcongr
    have hξB3 : ξ ^ 3 ≤ B ^ 3 := by
      gcongr
    rw [(hF t ht).deriv]
    change m ≤ -onceDiff (fun u : ℝ ↦ x / u ^ 2) r t ∧
      -onceDiff (fun u : ℝ ↦ x / u ^ 2) r t ≤ 1 / 2
    rw [hξEq]
    constructor
    · dsimp [m]
      apply (div_le_div_iff₀ hB3 hξ3).2
      exact mul_le_mul_of_nonneg_left hξB3 hC.le
    · exact (div_le_div_of_nonneg_left hC.le ha3 haξ3).trans hhalf
  have hantiD : AntitoneOn D (Icc a (a + (N + 1 : ℕ))) := by
    simpa only [D] using
      (antitoneOn_neg_onceDiff_reciprocalSquare
        (A := a + (N + 1 : ℕ)) hx hr ha)
  have hanti : AntitoneOn (deriv F) (Icc a (a + (N + 1 : ℕ))) := by
    intro p hp q hq hpq
    rw [(hF p hp).deriv, (hF q hq).deriv]
    exact hantiD hp hq hpq
  have hKL := kusminLandau_of_deriv_monotone_or_antitone F a hm N
    (fun t ht ↦ (hF t ht).differentiableAt.differentiableWithinAt)
    hbounds (Or.inr hanti)
  calc
    ‖∑ n ∈ range (N + 2), expPhase (onceDiffReciprocal x r (a + n))‖ ≤ 1 / m := by
      simpa only [F] using hKL
    _ = B ^ 3 / (2 * x * r) := by
      dsimp [m]
      field_simp [ne_of_gt hC, ne_of_gt hB]

private lemma hasDerivAt_neg_twiceDiffReciprocal
    (x r s t : ℝ) (ht : 0 < t) (hr : 0 < r) (hs : 0 < s) :
    HasDerivAt (fun u : ℝ ↦ -twiceDiffReciprocal x r s u)
      (twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s t) t := by
  have h0 := hasDerivAt_reciprocalPhase x (ne_of_gt ht)
  have hR := hasDerivAt_reciprocalPhase x (ne_of_gt (by linarith : 0 < t + r))
  have hS := hasDerivAt_reciprocalPhase x (ne_of_gt (by linarith : 0 < t + s))
  have hRS := hasDerivAt_reciprocalPhase x
    (ne_of_gt (by linarith : 0 < t + r + s))
  have h := (hasDerivAt_twiceDiff (reciprocalPhase x)
    (fun u : ℝ ↦ -x / u ^ 2) r s t h0 hR hS hRS).neg
  change HasDerivAt (-(twiceDiff (reciprocalPhase x) r s))
    (twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s t) t
  apply h.congr_deriv
  simp only [twiceDiff]
  ring

private lemma twiceDiff_reciprocalSquare_eq
    {x r s t : ℝ} (ht : 0 < t) (hr : 0 < r) (hs : 0 < s) :
    ∃ ξ ∈ Ioo t (t + r + s),
      twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s t = 6 * x * r * s / ξ ^ 4 := by
  obtain ⟨ξ, hξ, hξEq⟩ := twiceDiff_eq_mul_secondDeriv
    (fun u : ℝ ↦ x / u ^ 2) (fun u : ℝ ↦ -2 * x / u ^ 3)
    (fun u : ℝ ↦ 6 * x / u ^ 4) hr hs
    (fun u hu ↦ hasDerivAt_reciprocalSquare x (ne_of_gt (ht.trans_le hu.1)))
    (fun u hu ↦ hasDerivAt_reciprocalSquare_deriv x (ne_of_gt (ht.trans_le hu.1)))
  refine ⟨ξ, hξ, ?_⟩
  rw [hξEq]
  ring

private lemma antitoneOn_twiceDiff_reciprocalSquare
    {x r s a A : ℝ} (hx : 0 < x) (hr : 0 < r) (hs : 0 < s) (ha : 0 < a) :
    AntitoneOn (twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s) (Icc a A) := by
  let q : ℝ → ℝ := fun u ↦ x / u ^ 2
  let q' : ℝ → ℝ := fun u ↦ -2 * x / u ^ 3
  have hd : ∀ t ∈ Icc a A, HasDerivAt (twiceDiff q r s) (twiceDiff q' r s t) t := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    apply hasDerivAt_twiceDiff q q' r s t
    · exact hasDerivAt_reciprocalSquare x (ne_of_gt ht0)
    · exact hasDerivAt_reciprocalSquare x (ne_of_gt (by linarith : 0 < t + r))
    · exact hasDerivAt_reciprocalSquare x (ne_of_gt (by linarith : 0 < t + s))
    · exact hasDerivAt_reciprocalSquare x
        (ne_of_gt (by linarith : 0 < t + r + s))
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a A)
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hd t (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    have htI : t ∈ Icc a A := interior_subset ht
    have ht0 : 0 < t := ha.trans_le htI.1
    obtain ⟨ξ, hξ, hξEq⟩ := twiceDiff_eq_mul_secondDeriv q'
      (fun u : ℝ ↦ 6 * x / u ^ 4) (fun u : ℝ ↦ -24 * x / u ^ 5) hr hs
      (fun u hu ↦ hasDerivAt_reciprocalSquare_deriv x
        (ne_of_gt (ht0.trans_le hu.1)))
      (fun u hu ↦ hasDerivAt_reciprocalSquare_deriv2 x
        (ne_of_gt (ht0.trans_le hu.1)))
    rw [hξEq]
    have hξ0 : 0 < ξ := ht0.trans hξ.1
    have hlast : -24 * x / ξ ^ 5 < 0 := by
      exact div_neg_of_neg_of_pos (by nlinarith [hx]) (pow_pos hξ0 5)
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hr.le hs.le) hlast.le

/-- The concrete first-derivative estimate for the twice-differenced
reciprocal phase.  This is the terminal Kusmin--Landau estimate needed in the
two-step van der Corput argument of Granville--Ramaré, Proposition 8.2. -/
theorem kusminLandau_twiceDiffReciprocal
    (x r s a B : ℝ) (N : ℕ)
    (hx : 0 < x) (hr : 0 < r) (hs : 0 < s) (ha : 0 < a)
    (hendpoint : a + (N + 1 : ℕ) + r + s ≤ B)
    (hhalf : 6 * x * r * s / a ^ 4 ≤ 1 / 2) :
    ‖∑ n ∈ range (N + 2),
        expPhase (-twiceDiffReciprocal x r s (a + n))‖ ≤
      B ^ 4 / (6 * x * r * s) := by
  let F : ℝ → ℝ := fun t ↦ -twiceDiffReciprocal x r s t
  let D : ℝ → ℝ := twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s
  let m : ℝ := 6 * x * r * s / B ^ 4
  have hC : 0 < 6 * x * r * s := by positivity
  have hN0 : (0 : ℝ) ≤ (N + 1 : ℕ) := by positivity
  have hB : 0 < B := by nlinarith [hendpoint]
  have hm : 0 < m := by
    dsimp [m]
    exact div_pos hC (pow_pos hB 4)
  have hF : ∀ t ∈ Icc a (a + (N + 1 : ℕ)), HasDerivAt F (D t) t := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    simpa only [F, D] using hasDerivAt_neg_twiceDiffReciprocal x r s t ht0 hr hs
  have hbounds : ∀ t ∈ Icc a (a + (N + 1 : ℕ)),
      m ≤ deriv F t ∧ deriv F t ≤ 1 / 2 := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    obtain ⟨ξ, hξ, hξEq⟩ := twiceDiff_reciprocalSquare_eq
      (x := x) (r := r) (s := s) (t := t) ht0 hr hs
    have haξ : a < ξ := ht.1.trans_lt hξ.1
    have htB : t + r + s ≤ B := by linarith [ht.2, hendpoint]
    have hξB : ξ < B := hξ.2.trans_le htB
    have hξ0 : 0 < ξ := ha.trans haξ
    have ha4 : 0 < a ^ 4 := pow_pos ha 4
    have hξ4 : 0 < ξ ^ 4 := pow_pos hξ0 4
    have hB4 : 0 < B ^ 4 := pow_pos hB 4
    have haξ4 : a ^ 4 ≤ ξ ^ 4 := by gcongr
    have hξB4 : ξ ^ 4 ≤ B ^ 4 := by gcongr
    rw [(hF t ht).deriv]
    change m ≤ twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s t ∧
      twiceDiff (fun u : ℝ ↦ x / u ^ 2) r s t ≤ 1 / 2
    rw [hξEq]
    constructor
    · dsimp [m]
      apply (div_le_div_iff₀ hB4 hξ4).2
      exact mul_le_mul_of_nonneg_left hξB4 hC.le
    · exact (div_le_div_of_nonneg_left hC.le ha4 haξ4).trans hhalf
  have hantiD : AntitoneOn D (Icc a (a + (N + 1 : ℕ))) := by
    simpa only [D] using
      (antitoneOn_twiceDiff_reciprocalSquare
        (A := a + (N + 1 : ℕ)) hx hr hs ha)
  have hanti : AntitoneOn (deriv F) (Icc a (a + (N + 1 : ℕ))) := by
    intro p hp q hq hpq
    rw [(hF p hp).deriv, (hF q hq).deriv]
    exact hantiD hp hq hpq
  have hKL := kusminLandau_of_deriv_monotone_or_antitone F a hm N
    (fun t ht ↦ (hF t ht).differentiableAt.differentiableWithinAt)
    hbounds (Or.inr hanti)
  calc
    ‖∑ n ∈ range (N + 2),
        expPhase (-twiceDiffReciprocal x r s (a + n))‖ ≤ 1 / m := by
      simpa only [F] using hKL
    _ = B ^ 4 / (6 * x * r * s) := by
      dsimp [m]
      field_simp [ne_of_gt hC, ne_of_gt hB]

/-- Direct first-derivative estimate for the negative reciprocal phase.  The
minus sign makes the derivative positive; its decrease is exactly the
antitone branch of the calculus-facing Kusmin--Landau theorem. -/
theorem kusminLandau_neg_reciprocalPhase
    (x a B : ℝ) (N : ℕ) (hx : 0 < x) (ha : 0 < a)
    (hendpoint : a + (N + 1 : ℕ) ≤ B)
    (hhalf : x / a ^ 2 ≤ 1 / 2) :
    ‖∑ n ∈ range (N + 2), expPhase (-reciprocalPhase x (a + n))‖ ≤ B ^ 2 / x := by
  let F : ℝ → ℝ := -(reciprocalPhase x)
  let D : ℝ → ℝ := fun t ↦ x / t ^ 2
  let m : ℝ := x / B ^ 2
  have hN0 : (0 : ℝ) ≤ (N + 1 : ℕ) := by positivity
  have hB : 0 < B := by nlinarith [hendpoint]
  have hm : 0 < m := by
    dsimp [m]
    exact div_pos hx (pow_pos hB 2)
  have hF : ∀ t ∈ Icc a (a + (N + 1 : ℕ)), HasDerivAt F (D t) t := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have h := (hasDerivAt_reciprocalPhase x (ne_of_gt ht0)).neg
    change HasDerivAt (-(reciprocalPhase x)) (x / t ^ 2) t
    exact h.congr_deriv (by ring)
  have hbounds : ∀ t ∈ Icc a (a + (N + 1 : ℕ)),
      m ≤ deriv F t ∧ deriv F t ≤ 1 / 2 := by
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have htB : t ≤ B := by linarith [ht.2, hendpoint]
    have ht2 : 0 < t ^ 2 := pow_pos ht0 2
    have ha2 : 0 < a ^ 2 := pow_pos ha 2
    have hB2 : 0 < B ^ 2 := pow_pos hB 2
    have hat2 : a ^ 2 ≤ t ^ 2 := by
      gcongr
      exact ht.1
    have htB2 : t ^ 2 ≤ B ^ 2 := by gcongr
    rw [(hF t ht).deriv]
    constructor
    · dsimp [m, D]
      apply (div_le_div_iff₀ hB2 ht2).2
      exact mul_le_mul_of_nonneg_left htB2 hx.le
    · dsimp [D]
      exact (div_le_div_of_nonneg_left hx.le ha2 hat2).trans hhalf
  have hantiD : AntitoneOn D (Icc a (a + (N + 1 : ℕ))) := by
    have hD : ∀ t ∈ Icc a (a + (N + 1 : ℕ)),
        HasDerivAt D (-2 * x / t ^ 3) t := by
      intro t ht
      exact hasDerivAt_reciprocalSquare x (ne_of_gt (ha.trans_le ht.1))
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t ht ↦ (hD t ht).continuousAt.continuousWithinAt)
    · intro t ht
      exact (hD t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 < t := ha.trans_le (interior_subset ht).1
      exact (div_neg_of_neg_of_pos (by nlinarith [hx]) (pow_pos ht0 3)).le
  have hanti : AntitoneOn (deriv F) (Icc a (a + (N + 1 : ℕ))) := by
    intro p hp q hq hpq
    rw [(hF p hp).deriv, (hF q hq).deriv]
    exact hantiD hp hq hpq
  have hKL := kusminLandau_of_deriv_monotone_or_antitone F a hm N
    (fun t ht ↦ (hF t ht).differentiableAt.differentiableWithinAt)
    hbounds (Or.inr hanti)
  calc
    ‖∑ n ∈ range (N + 2), expPhase (-reciprocalPhase x (a + n))‖ ≤ 1 / m := by
      simpa only [F, Pi.neg_apply] using hKL
    _ = B ^ 2 / x := by
      dsimp [m]
      field_simp [ne_of_gt hx, ne_of_gt hB]

/-- Direct reciprocal-phase estimate in the positive-sign convention.  It is
equivalent to `kusminLandau_neg_reciprocalPhase` by complex conjugation. -/
theorem kusminLandau_reciprocalPhase
    (x a B : ℝ) (N : ℕ) (hx : 0 < x) (ha : 0 < a)
    (hendpoint : a + (N + 1 : ℕ) ≤ B)
    (hhalf : x / a ^ 2 ≤ 1 / 2) :
    ‖∑ n ∈ range (N + 2), expPhase (reciprocalPhase x (a + n))‖ ≤ B ^ 2 / x := by
  have hneg := kusminLandau_neg_reciprocalPhase x a B N hx ha hendpoint hhalf
  have hstar :
      (starRingEnd ℂ) (∑ n ∈ range (N + 2), expPhase (reciprocalPhase x (a + n))) =
        ∑ n ∈ range (N + 2), expPhase (-reciprocalPhase x (a + n)) := by
    rw [map_sum]
    apply sum_congr rfl
    intro n hn
    exact star_expPhase _
  calc
    ‖∑ n ∈ range (N + 2), expPhase (reciprocalPhase x (a + n))‖ =
        ‖(starRingEnd ℂ)
          (∑ n ∈ range (N + 2), expPhase (reciprocalPhase x (a + n)))‖ := by
      simpa using
        (Complex.norm_conj
          (∑ n ∈ range (N + 2), expPhase (reciprocalPhase x (a + n)))).symm
    _ = ‖∑ n ∈ range (N + 2), expPhase (-reciprocalPhase x (a + n))‖ := by
      rw [hstar]
    _ ≤ B ^ 2 / x := hneg

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/ReciprocalExpSum.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Explicit reciprocal exponential sums

This file supplies the integer-interval formulation of the reciprocal
exponential sums in Granville--Ramaré, Proposition 8.1.
-/

open scoped BigOperators
open Finset

noncomputable section

/-- The unweighted reciprocal exponential sum over `A < n ≤ B`. -/
def reciprocalExpSum (x : ℝ) (A B : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc A B, e (x / n)

/-- The same sum, normalized to a range starting at zero. -/
def reciprocalExpRange (x : ℝ) (C N : ℕ) : ℂ :=
  ∑ j ∈ range N, e (x / (C + j))

lemma reciprocalExpSum_eq_range (x : ℝ) (A B : ℕ) (hAB : A ≤ B) :
    reciprocalExpSum x A B = reciprocalExpRange x (A + 1) (B - A) := by
  classical
  rw [reciprocalExpSum, reciprocalExpRange]
  apply Finset.sum_bij (fun n _ ↦ n - (A + 1))
  · intro n hn
    simp only [mem_Ioc] at hn
    simp only [mem_range]
    omega
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [mem_Ioc] at hn₁ hn₂
    omega
  · intro j hj
    simp only [mem_range] at hj
    refine ⟨A + 1 + j, ?_, ?_⟩
    · simp only [mem_Ioc]
      omega
    · omega
  · intro n hn
    simp only [mem_Ioc] at hn
    have hind : A + 1 + (n - (A + 1)) = n := by omega
    have hind' : (n : ℝ) = (A + 1 : ℕ) + (n - (A + 1) : ℕ) := by
      exact_mod_cast hind.symm
    rw [hind']

lemma norm_reciprocalExpRange_le (x : ℝ) (C N : ℕ) :
    ‖reciprocalExpRange x C N‖ ≤ N := by
  rw [reciprocalExpRange]
  calc
    ‖∑ j ∈ range N, e (x / (C + j))‖ ≤
        ∑ j ∈ range N, ‖e (x / (C + j))‖ := norm_sum_le _ _
    _ = N := by simp

lemma norm_reciprocalExpSum_le (x : ℝ) (A B : ℕ) :
    ‖reciprocalExpSum x A B‖ ≤ ((B - A : ℕ) : ℝ) := by
  by_cases hAB : A ≤ B
  · rw [reciprocalExpSum_eq_range x A B hAB]
    exact norm_reciprocalExpRange_le x (A + 1) (B - A)
  · have hempty : Ioc A B = ∅ := by
      exact Ioc_eq_empty (by omega)
    simp [reciprocalExpSum, hempty]

/-- Sign invariance for a reciprocal sum over an arbitrary natural
half-open/closed interval. -/
lemma norm_reciprocalExpSum_neg (x : ℝ) (A B : ℕ) :
    ‖reciprocalExpSum (-x) A B‖ = ‖reciprocalExpSum x A B‖ := by
  rw [reciprocalExpSum, reciprocalExpSum, ← Complex.norm_conj]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [conj_e]
  congr 1
  ring

/-- A positive shift is represented by `h + 1`; this convention avoids a
zero shift in finite Weyl differencing while keeping every index natural. -/
def positivePhaseDifference (f : ℕ → ℝ) (h n : ℕ) : ℝ :=
  f (n + h + 1) - f n

/-- Two successive positive phase differences. -/
def positivePhaseDifference₂ (f : ℕ → ℝ) (h₁ h₂ n : ℕ) : ℝ :=
  positivePhaseDifference (positivePhaseDifference f h₂) h₁ n

/-- The multiplicative correlation corresponding to a positive shift. -/
def positiveCorrelation (z : ℕ → ℂ) (h n : ℕ) : ℂ :=
  z (n + h + 1) * (starRingEnd ℂ) (z n)

/-- Two successive positive correlations. -/
def positiveCorrelation₂ (z : ℕ → ℂ) (h₁ h₂ n : ℕ) : ℂ :=
  positiveCorrelation (positiveCorrelation z h₂) h₁ n

lemma positiveCorrelation_e (f : ℕ → ℝ) (h n : ℕ) :
    positiveCorrelation (fun j ↦ e (f j)) h n =
      e (positivePhaseDifference f h n) := by
  simp only [positiveCorrelation, positivePhaseDifference]
  exact (e_sub _ _).symm

lemma positiveCorrelation₂_e (f : ℕ → ℝ) (h₁ h₂ n : ℕ) :
    positiveCorrelation₂ (fun j ↦ e (f j)) h₁ h₂ n =
      e (positivePhaseDifference₂ f h₁ h₂ n) := by
  simp only [positiveCorrelation₂, positivePhaseDifference₂]
  rw [show positiveCorrelation (fun j ↦ e (f j)) h₂ =
      fun j ↦ e (positivePhaseDifference f h₂ j) by
    funext j
    exact positiveCorrelation_e f h₂ j]
  exact positiveCorrelation_e (positivePhaseDifference f h₂) h₁ n

lemma positivePhaseDifference₂_apply (f : ℕ → ℝ) (h₁ h₂ n : ℕ) :
    positivePhaseDifference₂ f h₁ h₂ n =
      (f (n + h₁ + 1 + h₂ + 1) - f (n + h₁ + 1)) -
        (f (n + h₂ + 1) - f n) := by
  simp only [positivePhaseDifference₂, positivePhaseDifference]

/-! ## Mean-value bounds for shifted differences -/

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/VanDerCorputTwoStep.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Two concrete van der Corput steps

This file connects the zero-padded adjustable-shift inequality in
`VanDerCorput.lean` with the positive correlations used for reciprocal
phases in `ReciprocalExpSum.lean`.  It supplies the two finite differencing
steps needed before the Kusmin--Landau estimate in the `k = 2` case of
Granville--Ramaré, Proposition 8.2.
-/

open scoped BigOperators ComplexConjugate

namespace VanDerCorput

/-- A fixed pair in the upper triangle of a zero-padded sliding window
reindexes exactly as an ordinary positive-shift correlation. -/
lemma sum_translated_mul_conj_eq
    (z : ℕ → ℂ) (N H h k : ℕ) (hh : h < H) (hk : k < h) :
    (∑ m ∈ Finset.range (N + H - 1),
        translatedTerm z N m h * conj (translatedTerm z N m k)) =
      ∑ n ∈ Finset.range (N - (h - k)),
        z n * conj (z (n + (h - k))) := by
  classical
  have hterm (m : ℕ) :
      translatedTerm z N m h * conj (translatedTerm z N m k) =
        if h ≤ m ∧ m - k < N then
          z (m - h) * conj (z (m - k)) else 0 := by
    by_cases hm : h ≤ m ∧ m - k < N
    · have hkm : k ≤ m := (Nat.le_of_lt hk).trans hm.1
      have hmhn : m - h < N := by omega
      simp [translatedTerm, hm.1, hkm, hm.2, hmhn]
    · by_cases hhm : h ≤ m
      · have hkm : k ≤ m := (Nat.le_of_lt hk).trans hhm
        have hmkn : ¬m - k < N := by
          intro hmkn
          exact hm ⟨hhm, hmkn⟩
        simp [translatedTerm, hhm, hkm, hmkn]
      · simp [translatedTerm, hhm]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun m _hm ↦ m - h)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
    omega
  · intro m₁ hm₁ m₂ hm₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hm₁ hm₂
    omega
  · intro n hn
    simp only [Finset.mem_range] at hn
    refine ⟨n + h, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · omega
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    have hindex : m - h + (h - k) = m - k := by omega
    rw [hindex]

/-- Norm form of `sum_translated_mul_conj_eq`, oriented as the
`positiveCorrelation` convention from `ReciprocalExpSum.lean`. -/
lemma norm_sum_translated_mul_conj_eq_positiveCorrelation
    (z : ℕ → ℂ) (N H h k : ℕ) (hh : h < H) (hk : k < h) :
    ‖∑ m ∈ Finset.range (N + H - 1),
        translatedTerm z N m h * conj (translatedTerm z N m k)‖ =
      ‖∑ n ∈ Finset.range (N - (h - k)),
        positiveCorrelation z (h - k - 1) n‖ := by
  rw [sum_translated_mul_conj_eq z N H h k hh hk]
  have hconj :
      (∑ n ∈ Finset.range (N - (h - k)),
          z n * conj (z (n + (h - k)))) =
        conj (∑ n ∈ Finset.range (N - (h - k)),
          positiveCorrelation z (h - k - 1) n) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [positiveCorrelation, map_mul]
    have hshift : n + (h - k - 1) + 1 = n + (h - k) := by omega
    rw [hshift]
    rw [Complex.conj_conj]
    ring
  rw [hconj, Complex.norm_conj]

/-- The aggregate upper-triangle term in the zero-padded inequality is
bounded by the corresponding finite positive-shift correlation sums. -/
lemma norm_sum_strictUpperAt_le_positiveCorrelations
    (z : ℕ → ℂ) (N H : ℕ) :
    ‖∑ m ∈ Finset.range (N + H - 1), strictUpperAt z N H m‖ ≤
      ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
        ‖∑ n ∈ Finset.range (N - (h - k)),
          positiveCorrelation z (h - k - 1) n‖ := by
  classical
  change
    ‖∑ m ∈ Finset.range (N + H - 1),
        ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
          translatedTerm z N m h * conj (translatedTerm z N m k)‖ ≤ _
  rw [Finset.sum_comm]
  calc
    ‖∑ h ∈ Finset.range H, ∑ m ∈ Finset.range (N + H - 1),
        ∑ k ∈ Finset.range h,
          translatedTerm z N m h * conj (translatedTerm z N m k)‖ ≤
        ∑ h ∈ Finset.range H,
          ‖∑ m ∈ Finset.range (N + H - 1),
            ∑ k ∈ Finset.range h,
              translatedTerm z N m h * conj (translatedTerm z N m k)‖ :=
      norm_sum_le _ _
    _ = ∑ h ∈ Finset.range H,
        ‖∑ k ∈ Finset.range h,
          ∑ m ∈ Finset.range (N + H - 1),
            translatedTerm z N m h * conj (translatedTerm z N m k)‖ := by
      apply Finset.sum_congr rfl
      intro h _hh
      rw [Finset.sum_comm]
    _ ≤ ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
        ‖∑ m ∈ Finset.range (N + H - 1),
          translatedTerm z N m h * conj (translatedTerm z N m k)‖ := by
      apply Finset.sum_le_sum
      intro h _hh
      exact norm_sum_le _ _
    _ = ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
        ‖∑ n ∈ Finset.range (N - (h - k)),
          positiveCorrelation z (h - k - 1) n‖ := by
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro k hk
      exact norm_sum_translated_mul_conj_eq_positiveCorrelation z N H h k
        (Finset.mem_range.mp hh) (Finset.mem_range.mp hk)

/-! ## The normalized `k = 2` Weyl--van der Corput inequality -/

/-- Reversing `k = 0, ..., h-1` turns the upper-triangle gap into an
ordinary initial range. -/
lemma sum_upper_gaps_le
    (F : ℕ → ℝ) (H : ℕ) (hF : ∀ r, 0 ≤ F r) :
    (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h, F (h - k - 1)) ≤
      (H : ℝ) * ∑ r ∈ Finset.range H, F r := by
  calc
    (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h, F (h - k - 1)) =
        ∑ h ∈ Finset.range H, ∑ r ∈ Finset.range h, F r := by
      apply Finset.sum_congr rfl
      intro h _hh
      calc
        (∑ k ∈ Finset.range h, F (h - k - 1)) =
            ∑ k ∈ Finset.range h, F (h - 1 - k) := by
          apply Finset.sum_congr rfl
          intro k hk
          congr 1
          omega
        _ = ∑ r ∈ Finset.range h, F r := Finset.sum_range_reflect F h
    _ ≤ ∑ _h ∈ Finset.range H, ∑ r ∈ Finset.range H, F r := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.le_of_lt (Finset.mem_range.mp hh))
      · intro r _rH _rh
        exact hF r
    _ = (H : ℝ) * ∑ r ∈ Finset.range H, F r := by simp

/-- A one-step estimate normalized by an ambient length `N`.  The actual
sequence length `L` may be shorter than the shift parameter; only
`L ≤ N` and `H ≤ N` are needed.  This form is stable under the second
differencing step near the right endpoint. -/
theorem sq_norm_sum_le_positiveCorrelations_ambient
    (z : ℕ → ℂ) (L N H : ℕ)
    (hL : L ≤ N) (hH : H ≤ N)
    (hz : ∀ n < L, ‖z n‖ ≤ 1) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range L, z n‖ ^ 2 ≤
      2 * (N : ℝ) *
        ((H : ℝ) * N +
          2 * (H : ℝ) * ∑ r ∈ Finset.range H,
            ‖∑ n ∈ Finset.range (L - (r + 1)),
              positiveCorrelation z r n‖) := by
  have hdiag : (∑ n ∈ Finset.range L, ‖z n‖ ^ 2) ≤ (N : ℝ) := by
    calc
      (∑ n ∈ Finset.range L, ‖z n‖ ^ 2) ≤
          ∑ _n ∈ Finset.range L, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn0 := norm_nonneg (z n)
        have hn1 := hz n (Finset.mem_range.mp hn)
        nlinarith
      _ = (L : ℝ) := by simp
      _ ≤ (N : ℝ) := by exact_mod_cast hL
  have hpad : (L + H - 1 : ℕ) ≤ 2 * N := by
    calc
      L + H - 1 ≤ L + H := Nat.sub_le _ _
      _ ≤ N + N := Nat.add_le_add hL hH
      _ = 2 * N := by omega
  have hgap := sum_upper_gaps_le
    (fun r ↦ ‖∑ n ∈ Finset.range (L - (r + 1)),
      positiveCorrelation z r n‖) H (fun r ↦ norm_nonneg _)
  have hcorr := norm_sum_strictUpperAt_le_positiveCorrelations z L H
  have hcorr' :
      ‖∑ m ∈ Finset.range (L + H - 1), strictUpperAt z L H m‖ ≤
        (H : ℝ) * ∑ r ∈ Finset.range H,
          ‖∑ n ∈ Finset.range (L - (r + 1)),
            positiveCorrelation z r n‖ := by
    have hrewrite :
        (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
          ‖∑ n ∈ Finset.range (L - (h - k)),
            positiveCorrelation z (h - k - 1) n‖) =
          ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range h,
            ‖∑ n ∈ Finset.range (L - ((h - k - 1) + 1)),
              positiveCorrelation z (h - k - 1) n‖ := by
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro k hk
      have hgap_pos : 0 < h - k := Nat.sub_pos_of_lt (Finset.mem_range.mp hk)
      have hindex : h - k - 1 + 1 = h - k := by omega
      rw [hindex]
    rw [hrewrite] at hcorr
    exact hcorr.trans hgap
  calc
    (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.range L, z n‖ ^ 2 ≤
        (L + H - 1 : ℕ) *
          ((H : ℝ) * (∑ n ∈ Finset.range L, ‖z n‖ ^ 2) +
            2 * ‖∑ m ∈ Finset.range (L + H - 1), strictUpperAt z L H m‖) :=
      sq_norm_sum_le_diagonal_add_correlation z L H
    _ ≤ (L + H - 1 : ℕ) *
        ((H : ℝ) * N +
          2 * ((H : ℝ) * ∑ r ∈ Finset.range H,
            ‖∑ n ∈ Finset.range (L - (r + 1)),
              positiveCorrelation z r n‖)) := by
      gcongr
    _ ≤ 2 * (N : ℝ) *
        ((H : ℝ) * N +
          2 * (H : ℝ) * ∑ r ∈ Finset.range H,
            ‖∑ n ∈ Finset.range (L - (r + 1)),
              positiveCorrelation z r n‖) := by
      have hnonneg : 0 ≤
          (H : ℝ) * N +
            2 * (H : ℝ) * ∑ r ∈ Finset.range H,
              ‖∑ n ∈ Finset.range (L - (r + 1)),
                positiveCorrelation z r n‖ := by positivity
      have hpadR : ((L + H - 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
        calc
          ((L + H - 1 : ℕ) : ℝ) ≤ ((L + H : ℕ) : ℝ) := by
            exact_mod_cast (Nat.sub_le (L + H) 1)
          _ = (L : ℝ) + (H : ℝ) := by norm_num
          _ ≤ (N : ℝ) + (N : ℝ) := by
            exact add_le_add (by exact_mod_cast hL) (by exact_mod_cast hH)
          _ = 2 * (N : ℝ) := by ring
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right hpadR hnonneg)
    _ = _ := by ring

/-- Divided form of the ambient one-step bound. -/
lemma normalized_sq_norm_sum_le_positiveCorrelations_ambient
    (z : ℕ → ℂ) (L N H : ℕ)
    (hN : 0 < N) (hHpos : 0 < H) (hL : L ≤ N) (hH : H ≤ N)
    (hz : ∀ n < L, ‖z n‖ ≤ 1) :
    (‖∑ n ∈ Finset.range L, z n‖ / (N : ℝ)) ^ 2 ≤
      2 / (H : ℝ) +
        4 / (H : ℝ) * ∑ r ∈ Finset.range H,
          (‖∑ n ∈ Finset.range (L - (r + 1)),
            positiveCorrelation z r n‖ / (N : ℝ)) := by
  have hraw := sq_norm_sum_le_positiveCorrelations_ambient z L N H hL hH hz
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  let T : ℝ := ∑ r ∈ Finset.range H,
    ‖∑ n ∈ Finset.range (L - (r + 1)), positiveCorrelation z r n‖
  have hraw' :
      (H : ℝ) * ((H : ℝ) * ‖∑ n ∈ Finset.range L, z n‖ ^ 2) ≤
        (H : ℝ) * (2 * (N : ℝ) ^ 2 + 4 * (N : ℝ) * T) := by
    dsimp only [T]
    convert hraw using 1 <;> ring
  have hcancel :
      (H : ℝ) * ‖∑ n ∈ Finset.range L, z n‖ ^ 2 ≤
        2 * (N : ℝ) ^ 2 + 4 * (N : ℝ) * T := by
    by_contra hn
    have hstrict :
        2 * (N : ℝ) ^ 2 + 4 * (N : ℝ) * T <
          (H : ℝ) * ‖∑ n ∈ Finset.range L, z n‖ ^ 2 :=
      lt_of_not_ge hn
    have hmul := mul_lt_mul_of_pos_left hstrict hHr
    exact (not_lt_of_ge hraw') hmul
  have hsumdiv :
      (∑ r ∈ Finset.range H,
        ‖∑ n ∈ Finset.range (L - (r + 1)),
          positiveCorrelation z r n‖ / (N : ℝ)) = T / (N : ℝ) := by
    dsimp only [T]
    rw [Finset.sum_div]
  rw [hsumdiv]
  field_simp
  nlinarith [hcancel]

/-- Granville--Ramaré Lemma 8.3 specialized to two differencing steps,
with `Q = q²`.  The constants are slightly stronger than the displayed
`1/8` constants in the paper; the conclusion is kept in the paper's form.
The two shift ranges are `r₁ < q²` and `r₂ < q`, and their coefficient
is exactly of order `q⁻³`. -/
theorem gr_lemma_8_3_k2
    (z : ℕ → ℂ) (N q : ℕ) (hq : 1 ≤ q) (hqN : q ^ 2 ≤ N)
    (hz : ∀ n < N, ‖z n‖ ≤ 1) :
    (‖∑ n ∈ Finset.range N, z n‖ / (8 * (N : ℝ))) ^ 4 ≤
      1 / (8 * (q : ℝ) ^ 2) +
        1 / (8 * (q : ℝ) ^ 3) *
          ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
            (‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
              positiveCorrelation₂ z r₁ r₂ n‖ / (N : ℝ)) := by
  have hqpos : 0 < q := by omega
  have hN : 0 < N := (pow_pos hqpos 2).trans_le hqN
  have hqN' : q ≤ N := by nlinarith
  let C : ℕ → ℝ := fun r₂ ↦
    ‖∑ n ∈ Finset.range (N - (r₂ + 1)),
      positiveCorrelation z r₂ n‖ / (N : ℝ)
  let D : ℕ → ℕ → ℝ := fun r₁ r₂ ↦
    ‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
      positiveCorrelation₂ z r₁ r₂ n‖ / (N : ℝ)
  have hfirst :
      (‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ)) ^ 2 ≤
        2 / (q : ℝ) + 4 / (q : ℝ) * ∑ r₂ ∈ Finset.range q, C r₂ := by
    simpa only [C] using
      normalized_sq_norm_sum_le_positiveCorrelations_ambient
        z N N q hN hqpos le_rfl hqN' hz
  have hsecond (r₂ : ℕ) (hr₂ : r₂ < q) :
      (C r₂) ^ 2 ≤
        2 / (q : ℝ) ^ 2 +
          4 / (q : ℝ) ^ 2 * ∑ r₁ ∈ Finset.range (q ^ 2), D r₁ r₂ := by
    let L := N - (r₂ + 1)
    have hL : L ≤ N := Nat.sub_le _ _
    have hcorr : ∀ n < L, ‖positiveCorrelation z r₂ n‖ ≤ 1 := by
      intro n hn
      have hnN : n < N := hn.trans_le hL
      have hnshift : n + r₂ + 1 < N := by
        dsimp [L] at hn
        omega
      rw [positiveCorrelation, norm_mul, Complex.norm_conj]
      nlinarith [hz _ hnshift, hz _ hnN, norm_nonneg (z (n + r₂ + 1)),
        norm_nonneg (z n)]
    have hs := normalized_sq_norm_sum_le_positiveCorrelations_ambient
      (fun n ↦ positiveCorrelation z r₂ n) L N (q ^ 2)
      hN (pow_pos hqpos 2) hL hqN hcorr
    simpa only [C, D, positiveCorrelation₂, Nat.cast_pow] using hs
  have hCnonneg (r : ℕ) : 0 ≤ C r := by
    dsimp [C]
    positivity
  have hDnonneg (r₁ r₂ : ℕ) : 0 ≤ D r₁ r₂ := by
    dsimp [D]
    positivity
  have hCsq :
      (∑ r₂ ∈ Finset.range q, C r₂) ^ 2 ≤
        (q : ℝ) * ∑ r₂ ∈ Finset.range q, (C r₂) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := Finset.range q) (f := C))
  have hsumSecond :
      (∑ r₂ ∈ Finset.range q, (C r₂) ^ 2) ≤
        2 / (q : ℝ) +
          4 / (q : ℝ) ^ 2 *
            ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
              D r₁ r₂ := by
    calc
      (∑ r₂ ∈ Finset.range q, (C r₂) ^ 2) ≤
          ∑ r₂ ∈ Finset.range q,
            (2 / (q : ℝ) ^ 2 +
              4 / (q : ℝ) ^ 2 * ∑ r₁ ∈ Finset.range (q ^ 2),
                D r₁ r₂) := by
        apply Finset.sum_le_sum
        intro r₂ hr₂
        exact hsecond r₂ (Finset.mem_range.mp hr₂)
      _ = 2 / (q : ℝ) +
          4 / (q : ℝ) ^ 2 *
            ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
              D r₁ r₂ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        rw [Finset.sum_comm]
        field_simp
  have hnormnonneg : 0 ≤
      ‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ) := by positivity
  have hfirstRhsNonneg : 0 ≤
      2 / (q : ℝ) + 4 / (q : ℝ) * ∑ r₂ ∈ Finset.range q, C r₂ := by
    positivity
  have hfourth :
      (‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ)) ^ 4 ≤
        8 / (q : ℝ) ^ 2 +
          32 / (q : ℝ) * ∑ r₂ ∈ Finset.range q, (C r₂) ^ 2 := by
    have hsquare := (sq_le_sq₀ (sq_nonneg _) hfirstRhsNonneg).2 hfirst
    calc
      (‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ)) ^ 4 =
          ((‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ)) ^ 2) ^ 2 := by ring
      _ ≤ (2 / (q : ℝ) +
          4 / (q : ℝ) * ∑ r₂ ∈ Finset.range q, C r₂) ^ 2 := hsquare
      _ ≤ 8 / (q : ℝ) ^ 2 +
          32 / (q : ℝ) ^ 2 *
            (∑ r₂ ∈ Finset.range q, C r₂) ^ 2 := by
        calc
          _ ≤ 2 * (2 / (q : ℝ)) ^ 2 +
              2 * (4 / (q : ℝ) *
                ∑ r₂ ∈ Finset.range q, C r₂) ^ 2 := by
            nlinarith [sq_nonneg
              (2 / (q : ℝ) - 4 / (q : ℝ) *
                ∑ r₂ ∈ Finset.range q, C r₂)]
          _ = _ := by ring
      _ ≤ 8 / (q : ℝ) ^ 2 +
          32 / (q : ℝ) * ∑ r₂ ∈ Finset.range q, (C r₂) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left hCsq
          (show 0 ≤ 32 / (q : ℝ) ^ 2 by positivity)
        calc
          _ ≤ 8 / (q : ℝ) ^ 2 +
              32 / (q : ℝ) ^ 2 *
                ((q : ℝ) * ∑ r₂ ∈ Finset.range q, (C r₂) ^ 2) :=
            by
              simpa [add_comm] using
                (add_le_add_right hmul (8 / (q : ℝ) ^ 2))
          _ = _ := by field_simp
  have hDsumNonneg : 0 ≤
      ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q, D r₁ r₂ := by
    positivity
  have hcombined :
      (‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ)) ^ 4 ≤
        72 / (q : ℝ) ^ 2 +
          128 / (q : ℝ) ^ 3 *
            ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
              D r₁ r₂ := by
    calc
      _ ≤ 8 / (q : ℝ) ^ 2 +
          32 / (q : ℝ) * ∑ r₂ ∈ Finset.range q, (C r₂) ^ 2 := hfourth
      _ ≤ 8 / (q : ℝ) ^ 2 +
          32 / (q : ℝ) *
            (2 / (q : ℝ) + 4 / (q : ℝ) ^ 2 *
              ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
                D r₁ r₂) := by
        gcongr
      _ = _ := by field_simp; ring
  have hqr : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (‖∑ n ∈ Finset.range N, z n‖ / (8 * (N : ℝ))) ^ 4 =
        (‖∑ n ∈ Finset.range N, z n‖ / (N : ℝ)) ^ 4 / 4096 := by
      field_simp
      ring
    _ ≤ (72 / (q : ℝ) ^ 2 +
          128 / (q : ℝ) ^ 3 *
            ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
              D r₁ r₂) / 4096 := by
      exact div_le_div_of_nonneg_right hcombined (by norm_num)
    _ = 9 / (512 * (q : ℝ) ^ 2) +
          1 / (32 * (q : ℝ) ^ 3) *
            ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
              D r₁ r₂ := by ring
    _ ≤ 1 / (8 * (q : ℝ) ^ 2) +
          1 / (8 * (q : ℝ) ^ 3) *
            ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
              D r₁ r₂ := by
      have hmain : 9 / (512 * (q : ℝ) ^ 2) ≤
          1 / (8 * (q : ℝ) ^ 2) := by
        calc
          9 / (512 * (q : ℝ) ^ 2) ≤
              64 / (512 * (q : ℝ) ^ 2) := by
            exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
          _ = 1 / (8 * (q : ℝ) ^ 2) := by ring
      have hcoef : 1 / (32 * (q : ℝ) ^ 3) ≤
          1 / (8 * (q : ℝ) ^ 3) := by
        calc
          1 / (32 * (q : ℝ) ^ 3) ≤
              4 / (32 * (q : ℝ) ^ 3) := by
            exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
          _ = 1 / (8 * (q : ℝ) ^ 3) := by ring
      exact add_le_add hmain
        (mul_le_mul_of_nonneg_right hcoef hDsumNonneg)

/-! ## Reciprocal-phase terminal identities -/

end VanDerCorput

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/ReciprocalExpSumBound.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The two-step reciprocal exponential-sum bound

This file combines the normalized two-step van der Corput inequality with
the Kusmin--Landau estimate for the twice-differenced reciprocal phase.
-/

open scoped BigOperators

noncomputable section

/-- The finite harmonic factor produced by one family of Weyl shifts. -/
def finiteHarmonic (H : ℕ) : ℝ :=
  ∑ r ∈ Finset.range H, ((r + 1 : ℕ) : ℝ)⁻¹

lemma finiteHarmonic_nonneg (H : ℕ) : 0 ≤ finiteHarmonic H := by
  unfold finiteHarmonic
  positivity

lemma sum_double_inv_eq_finiteHarmonic_mul (H₁ H₂ : ℕ) :
    (∑ r₁ ∈ Finset.range H₁, ∑ r₂ ∈ Finset.range H₂,
        (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹) =
      finiteHarmonic H₁ * finiteHarmonic H₂ := by
  simp only [mul_inv]
  rw [finiteHarmonic, finiteHarmonic, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r₁ _hr₁
  rw [Finset.mul_sum]

/-- Combine the normalized two-step Weyl inequality with a reciprocal
`1/(r₁r₂)` estimate for every terminal correlation. -/
theorem reciprocalExpRange_fourth_le_of_terminal
    (x : ℝ) (C N q : ℕ) (hq : 1 ≤ q) (hqN : q ^ 2 ≤ N)
    (K : ℝ) (hK : 0 ≤ K)
    (hterminal : ∀ r₁ < q ^ 2, ∀ r₂ < q,
      ‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
        positiveCorrelation₂
          (fun j ↦ e (reciprocalPhase x (C + j))) r₁ r₂ n‖ ≤
        K * (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹) :
    ‖reciprocalExpRange x C N‖ ^ 4 ≤
      512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
        (512 : ℝ) * (N : ℝ) ^ 3 * K / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
  have hqpos : 0 < q := by omega
  have hNpos : 0 < N := (pow_pos hqpos 2).trans_le hqN
  let z : ℕ → ℂ := fun j ↦ e (reciprocalPhase x (C + j))
  have hz : ∀ n < N, ‖z n‖ ≤ 1 := by
    intro n hn
    simp [z]
  have hweyl := VanDerCorput.gr_lemma_8_3_k2 z N q hq hqN hz
  have hsum :
      (∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
        ‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
          positiveCorrelation₂ z r₁ r₂ n‖ / (N : ℝ)) ≤
        K / (N : ℝ) *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
    calc
      _ ≤ ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
          (K * (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹) /
            (N : ℝ) := by
        apply Finset.sum_le_sum
        intro r₁ hr₁
        apply Finset.sum_le_sum
        intro r₂ hr₂
        exact div_le_div_of_nonneg_right
          (hterminal r₁ (Finset.mem_range.mp hr₁) r₂
            (Finset.mem_range.mp hr₂)) (by positivity)
      _ = K / (N : ℝ) *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
        calc
          _ = K / (N : ℝ) *
              (∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
                (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r₁ _hr₁
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r₂ _hr₂
            ring
          _ = _ := by rw [sum_double_inv_eq_finiteHarmonic_mul]
  have hnormalized :
      (‖reciprocalExpRange x C N‖ / (8 * (N : ℝ))) ^ 4 ≤
        1 / (8 * (q : ℝ) ^ 2) +
          1 / (8 * (q : ℝ) ^ 3) *
            (K / (N : ℝ) *
              (finiteHarmonic (q ^ 2) * finiteHarmonic q)) := by
    rw [reciprocalExpRange]
    have hcoef : 0 ≤ 1 / (8 * (q : ℝ) ^ 3) := by positivity
    have hweighted := mul_le_mul_of_nonneg_left hsum hcoef
    exact hweyl.trans (add_le_add_right hweighted _)
  have hscale : 0 < (8 * (N : ℝ)) ^ 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hnormalized hscale.le
  calc
    ‖reciprocalExpRange x C N‖ ^ 4 =
        (‖reciprocalExpRange x C N‖ / (8 * (N : ℝ))) ^ 4 *
          (8 * (N : ℝ)) ^ 4 := by
      field_simp
    _ ≤ (1 / (8 * (q : ℝ) ^ 2) +
          1 / (8 * (q : ℝ) ^ 3) *
            (K / (N : ℝ) *
              (finiteHarmonic (q ^ 2) * finiteHarmonic q))) *
          (8 * (N : ℝ)) ^ 4 := hmul
    _ = 512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
        (512 : ℝ) * (N : ℝ) ^ 3 * K / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
      field_simp
      ring

/-! ## The concrete twice-difference terminal phase -/

/-- The second multiplicative correlation is exactly the mixed forward
difference used by the Kusmin--Landau estimate. -/
lemma positiveCorrelation₂_reciprocal_eq_expPhase_twiceDiff
    (x : ℝ) (C h₁ h₂ n : ℕ) :
    positiveCorrelation₂
        (fun j ↦ e (reciprocalPhase x (C + j))) h₁ h₂ n =
      expPhase
        (twiceDiffReciprocal x (h₁ + 1 : ℕ) (h₂ + 1 : ℕ) (C + n : ℕ)) := by
  rw [expPhase_eq_e, positiveCorrelation₂_e]
  congr 1
  rw [positivePhaseDifference₂_apply]
  simp only [twiceDiffReciprocal, twiceDiff, reciprocalPhase]
  push_cast
  ring

/-- Negating every real phase conjugates the complex sum and therefore
does not change its norm. -/
lemma norm_sum_expPhase_neg_eq (f : ℕ → ℝ) (L : ℕ) :
    ‖∑ n ∈ Finset.range L, expPhase (-f n)‖ =
      ‖∑ n ∈ Finset.range L, expPhase (f n)‖ := by
  rw [← Complex.norm_conj]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [expPhase_eq_e, expPhase_eq_e, conj_e]
  simp

/-- The first-derivative branch of the reciprocal exponential-sum bound,
wrapped so that it applies to a range of any natural length. -/
theorem norm_reciprocalExpRange_le_firstDerivative
    (x : ℝ) (C N : ℕ) (hx : 0 < x) (hC : 0 < C)
    (hhalf : x / (C : ℝ) ^ 2 ≤ 1 / 2) :
    ‖reciprocalExpRange x C N‖ ≤ ((C + N : ℕ) : ℝ) ^ 2 / x := by
  have hlarge : 2 ≤ ((C + N : ℕ) : ℝ) ^ 2 / x := by
    apply (le_div_iff₀ hx).2
    have hCpow : 0 < (C : ℝ) ^ 2 := by positivity
    have hbase : 2 * x ≤ (C : ℝ) ^ 2 := by
      have := (div_le_iff₀ hCpow).1 hhalf
      nlinarith
    have hCN : (C : ℝ) ≤ ((C + N : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right C N)
    have hpow : (C : ℝ) ^ 2 ≤ ((C + N : ℕ) : ℝ) ^ 2 := by
      gcongr
    linarith
  by_cases hN : 2 ≤ N
  · have hlength : N - 2 + 2 = N := by omega
    have hendNat : C + (N - 2 + 1) ≤ C + N := by omega
    have hend :
        (C : ℝ) + ((N - 2 + 1 : ℕ) : ℝ) ≤ ((C + N : ℕ) : ℝ) := by
      exact_mod_cast hendNat
    have hKL := kusminLandau_reciprocalPhase x (C : ℝ)
      ((C + N : ℕ) : ℝ) (N - 2) hx (by positivity) hend hhalf
    rw [reciprocalExpRange]
    simpa only [hlength, expPhase_eq_e, reciprocalPhase, Nat.cast_add] using hKL
  · have hNtwo : N ≤ 1 := by omega
    calc
      ‖reciprocalExpRange x C N‖ ≤ (N : ℝ) := norm_reciprocalExpRange_le x C N
      _ ≤ 2 := by exact_mod_cast (show N ≤ 2 by omega)
      _ ≤ _ := hlarge

/-- Every terminal correlation in the two-step Weyl process satisfies the
concrete Kusmin--Landau bound.  The short ranges of length zero or one are
included: in that case the derivative-size hypothesis makes the displayed
right-hand side at least two. -/
lemma terminalCorrelation_reciprocal_le
    (x : ℝ) (C N q r₁ r₂ : ℕ)
    (hx : 0 < x) (hC : 0 < C)
    (hr₁ : r₁ < q ^ 2) (hr₂ : r₂ < q)
    (hderiv : 12 * x * (q : ℝ) ^ 3 ≤ (C : ℝ) ^ 4) :
    ‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
        positiveCorrelation₂
          (fun j ↦ e (reciprocalPhase x (C + j))) r₁ r₂ n‖ ≤
      ((C + N : ℕ) : ℝ) ^ 4 / (6 * x) *
        (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹ := by
  let L : ℕ := N - (r₂ + 1) - (r₁ + 1)
  have hr₁q : r₁ + 1 ≤ q ^ 2 := by omega
  have hr₂q : r₂ + 1 ≤ q := by omega
  have hrsNat : (r₁ + 1) * (r₂ + 1) ≤ q ^ 3 := by
    calc
      (r₁ + 1) * (r₂ + 1) ≤ q ^ 2 * q :=
        Nat.mul_le_mul hr₁q hr₂q
      _ = q ^ 3 := by ring
  have hrs :
      ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ) ≤
        (q : ℝ) ^ 3 := by
    exact_mod_cast hrsNat
  have hrsPos :
      0 < ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ) := by
    positivity
  have hsmall :
      6 * x * ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ) /
          (C : ℝ) ^ 4 ≤ 1 / 2 := by
    have hCpow : 0 < (C : ℝ) ^ 4 := by positivity
    apply (div_le_iff₀ hCpow).2
    have hxq :
        12 * x *
            (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ)) ≤
          12 * x * (q : ℝ) ^ 3 := by
      gcongr
    nlinarith
  have hlarge :
      2 ≤ ((C + N : ℕ) : ℝ) ^ 4 /
        (6 * x * ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ)) := by
    have hden :
        0 < 6 * x * ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ) := by
      positivity
    apply (le_div_iff₀ hden).2
    have hCN : (C : ℝ) ≤ ((C + N : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right C N)
    have hpow : (C : ℝ) ^ 4 ≤ ((C + N : ℕ) : ℝ) ^ 4 := by
      gcongr
    have hxrs :
        12 * x *
            (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ)) ≤
          (C : ℝ) ^ 4 := by
      calc
        _ ≤ 12 * x * (q : ℝ) ^ 3 := by gcongr
        _ ≤ _ := hderiv
    nlinarith
  by_cases hL : 2 ≤ L
  · have hlength : L - 2 + 2 = L := by omega
    have hendNat :
        C + (L - 2 + 1) + (r₁ + 1) + (r₂ + 1) ≤ C + N := by
      dsimp [L]
      omega
    have hend :
        (C : ℝ) + ((L - 2 + 1 : ℕ) : ℝ) +
              ((r₁ + 1 : ℕ) : ℝ) + ((r₂ + 1 : ℕ) : ℝ) ≤
            ((C + N : ℕ) : ℝ) := by
      exact_mod_cast hendNat
    have hKL := kusminLandau_twiceDiffReciprocal
      x ((r₁ + 1 : ℕ) : ℝ) ((r₂ + 1 : ℕ) : ℝ)
      (C : ℝ) ((C + N : ℕ) : ℝ) (L - 2)
      hx (by positivity) (by positivity) (by positivity) hend hsmall
    calc
      ‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
          positiveCorrelation₂
            (fun j ↦ e (reciprocalPhase x (C + j))) r₁ r₂ n‖ =
          ‖∑ n ∈ Finset.range L,
            expPhase (twiceDiffReciprocal x (r₁ + 1 : ℕ) (r₂ + 1 : ℕ)
              (C + n : ℕ))‖ := by
        dsimp [L]
        congr 1
        apply Finset.sum_congr rfl
        intro n _hn
        exact positiveCorrelation₂_reciprocal_eq_expPhase_twiceDiff x C r₁ r₂ n
      _ = ‖∑ n ∈ Finset.range L,
            expPhase (-twiceDiffReciprocal x (r₁ + 1 : ℕ) (r₂ + 1 : ℕ)
              (C + n : ℕ))‖ := by
        symm
        exact norm_sum_expPhase_neg_eq
          (fun n ↦ twiceDiffReciprocal x (r₁ + 1 : ℕ) (r₂ + 1 : ℕ)
            (C + n : ℕ)) L
      _ ≤ ((C + N : ℕ) : ℝ) ^ 4 /
          (6 * x * ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ)) := by
        rw [← hlength]
        simpa only [Nat.cast_add] using hKL
      _ = ((C + N : ℕ) : ℝ) ^ 4 / (6 * x) *
          (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹ := by
        field_simp

  · have hLtwo : L ≤ 1 := by omega
    calc
      ‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
          positiveCorrelation₂
            (fun j ↦ e (reciprocalPhase x (C + j))) r₁ r₂ n‖ ≤
          ∑ n ∈ Finset.range L,
            ‖positiveCorrelation₂
              (fun j ↦ e (reciprocalPhase x (C + j))) r₁ r₂ n‖ := by
        dsimp [L]
        exact norm_sum_le _ _
      _ = (L : ℝ) := by
        simp [positiveCorrelation₂, positiveCorrelation]
      _ ≤ 2 := by exact_mod_cast (show L ≤ 2 by omega)
      _ ≤ ((C + N : ℕ) : ℝ) ^ 4 /
          (6 * x * ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ)) := hlarge
      _ = ((C + N : ℕ) : ℝ) ^ 4 / (6 * x) *
          (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹ := by
        field_simp

/-- The concrete `k = 2` reciprocal exponential-sum estimate obtained from
two Weyl differencing steps and Kusmin--Landau.  This is the fourth-power
form of Granville--Ramaré's Proposition 8 estimate, retaining the exact two
finite harmonic factors generated by the positive shifts. -/
theorem reciprocalExpRange_fourth_le
    (x : ℝ) (C N q : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hq : 1 ≤ q) (hqN : q ^ 2 ≤ N)
    (hderiv : 12 * x * (q : ℝ) ^ 3 ≤ (C : ℝ) ^ 4) :
    ‖reciprocalExpRange x C N‖ ^ 4 ≤
      512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
        (512 : ℝ) * (N : ℝ) ^ 3 *
            (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
  apply reciprocalExpRange_fourth_le_of_terminal x C N q hq hqN
    (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) (by positivity)
  intro r₁ hr₁ r₂ hr₂
  exact terminalCorrelation_reciprocal_le x C N q r₁ r₂ hx hC hr₁ hr₂ hderiv

/-- Natural-endpoint form of the first-derivative branch. -/
theorem norm_reciprocalExpSum_le_firstDerivative
    (x : ℝ) (A B : ℕ) (hx : 0 < x) (hAB : A ≤ B)
    (hhalf : x / ((A + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 2) :
    ‖reciprocalExpSum x A B‖ ≤ ((B + 1 : ℕ) : ℝ) ^ 2 / x := by
  rw [reciprocalExpSum_eq_range x A B hAB]
  have h := norm_reciprocalExpRange_le_firstDerivative x (A + 1) (B - A)
    hx (by omega) hhalf
  have hend : A + 1 + (B - A) = B + 1 := by omega
  simpa only [hend] using h

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/ReciprocalExpSumRounding.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Shift selection and harmonic-factor bounds

This file contains the rounding and elementary real-algebra part of the
two-step reciprocal exponential-sum estimate.  The selected shift is the
largest integer `q ≤ √N` for which the terminal Kusmin--Landau phase is
admissible.  In the high-frequency branch this is an integer cube-root
choice up to the harmless rounding factor `2^3`.
-/

noncomputable section

/-- The upper-phase constraint imposed on the two Weyl shift ranges. -/
def reciprocalShiftAdmissible (x : ℝ) (C q : ℕ) : Prop :=
  12 * x * (q : ℝ) ^ 3 ≤ (C : ℝ) ^ 4

/-- The largest phase-admissible shift not exceeding `⌊√N⌋`. -/
def reciprocalShift (x : ℝ) (C N : ℕ) : ℕ :=
  by
    classical
    exact Nat.findGreatest (reciprocalShiftAdmissible x C) (Nat.sqrt N)

lemma reciprocalShift_le_sqrt (x : ℝ) (C N : ℕ) :
    reciprocalShift x C N ≤ Nat.sqrt N := by
  classical
  unfold reciprocalShift
  exact Nat.findGreatest_le _

/-- The selected shift is always short enough for both differencing steps. -/
lemma reciprocalShift_sq_le (x : ℝ) (C N : ℕ) :
    (reciprocalShift x C N) ^ 2 ≤ N := by
  exact (Nat.pow_le_pow_left (reciprocalShift_le_sqrt x C N) 2).trans
    (Nat.sqrt_le' N)

/-- The selected shift satisfies the terminal phase constraint. -/
lemma reciprocalShift_admissible (x : ℝ) (C N : ℕ) :
    reciprocalShiftAdmissible x C (reciprocalShift x C N) := by
  classical
  unfold reciprocalShift
  exact Nat.findGreatest_spec (P := reciprocalShiftAdmissible x C)
    (m := 0) (n := Nat.sqrt N) (Nat.zero_le _) (by
      simp [reciprocalShiftAdmissible])

/-- If shift `1` is admissible and the interval is nonempty, then the
selected shift is positive. -/
lemma reciprocalShift_pos {x : ℝ} {C N : ℕ} (hN : 0 < N)
    (hone : 12 * x ≤ (C : ℝ) ^ 4) :
    0 < reciprocalShift x C N := by
  classical
  rw [reciprocalShift, Nat.findGreatest_pos]
  refine ⟨1, by omega, ?_, ?_⟩
  · exact Nat.sqrt_pos.mpr hN
  · simpa [reciprocalShiftAdmissible] using hone

/-- If the selected shift has not reached the square-root ceiling, its
successor violates the phase constraint. -/
lemma reciprocalShift_succ_not_admissible {x : ℝ} {C N : ℕ}
    (hlt : reciprocalShift x C N < Nat.sqrt N) :
    ¬ reciprocalShiftAdmissible x C (reciprocalShift x C N + 1) := by
  classical
  exact Nat.findGreatest_is_greatest (P := reciprocalShiftAdmissible x C)
    (Nat.lt_succ_self _) (Nat.succ_le_iff.mpr hlt)

/-- Cube-root rounding: below the square-root ceiling, a positive selected
shift is within a factor `2` of the real phase threshold. -/
lemma reciprocalShift_rounding_lower {x : ℝ} {C N : ℕ} (hx : 0 < x)
    (hq : 1 ≤ reciprocalShift x C N)
    (hlt : reciprocalShift x C N < Nat.sqrt N) :
    (C : ℝ) ^ 4 <
      96 * x * (reciprocalShift x C N : ℝ) ^ 3 := by
  let q := reciprocalShift x C N
  have hfail := reciprocalShift_succ_not_admissible (x := x) (C := C) (N := N) hlt
  have hnext : (C : ℝ) ^ 4 < 12 * x * ((q + 1 : ℕ) : ℝ) ^ 3 := by
    exact lt_of_not_ge hfail
  have hqdoubleNat : q + 1 ≤ 2 * q := by omega
  have hqdouble : ((q + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by
    exact_mod_cast hqdoubleNat
  calc
    (C : ℝ) ^ 4 < 12 * x * ((q + 1 : ℕ) : ℝ) ^ 3 := hnext
    _ ≤ 12 * x * (2 * (q : ℝ)) ^ 3 := by gcongr
    _ = 96 * x * (q : ℝ) ^ 3 := by ring

/-- The high-frequency hypothesis says that the phase constraint already
fails at `⌊√N⌋`; hence the selected shift lies strictly below that ceiling. -/
lemma reciprocalShift_lt_sqrt_of_highFrequency {x : ℝ} {C N : ℕ}
    (hhigh : (C : ℝ) ^ 4 <
      12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    reciprocalShift x C N < Nat.sqrt N := by
  have hle := reciprocalShift_le_sqrt x C N
  by_contra hnot
  have heq : reciprocalShift x C N = Nat.sqrt N :=
    Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
  have hadm := reciprocalShift_admissible x C N
  rw [heq] at hadm
  exact (not_le_of_gt hhigh) hadm

/-- All integer rounding facts for the high-frequency cube-root choice. -/
lemma reciprocalShift_scale_bounds {x : ℝ} {C N : ℕ}
    (hx : 0 < x) (hN : 0 < N)
    (hone : 12 * x ≤ (C : ℝ) ^ 4)
    (hhigh : (C : ℝ) ^ 4 <
      12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    let q := reciprocalShift x C N
    1 ≤ q ∧ q ^ 2 ≤ N ∧
      12 * x * (q : ℝ) ^ 3 ≤ (C : ℝ) ^ 4 ∧
      (C : ℝ) ^ 4 < 96 * x * (q : ℝ) ^ 3 := by
  let q := reciprocalShift x C N
  have hqpos : 0 < q := reciprocalShift_pos hN hone
  have hq : 1 ≤ q := hqpos
  have hlt : q < Nat.sqrt N := reciprocalShift_lt_sqrt_of_highFrequency hhigh
  exact ⟨hq, reciprocalShift_sq_le x C N,
    reciprocalShift_admissible x C N,
    reciprocalShift_rounding_lower hx hq hlt⟩

/-- `finiteHarmonic` is Mathlib's harmonic number, coerced to the reals. -/
lemma finiteHarmonic_eq_harmonic (H : ℕ) :
    finiteHarmonic H = (harmonic H : ℝ) := by
  unfold finiteHarmonic harmonic
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma finiteHarmonic_le_one_add_log (H : ℕ) :
    finiteHarmonic H ≤ 1 + Real.log H := by
  rw [finiteHarmonic_eq_harmonic]
  exact harmonic_le_one_add_log H

/-- The two harmonic factors produced by the Weyl shifts cost at most two
squares of the usual logarithmic factor. -/
lemma finiteHarmonic_sq_mul_le {q : ℕ} (hq : 1 ≤ q) :
    finiteHarmonic (q ^ 2) * finiteHarmonic q ≤
      2 * (1 + Real.log q) ^ 2 := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hq2 := finiteHarmonic_le_one_add_log (q ^ 2)
  have hq1 := finiteHarmonic_le_one_add_log q
  have hlogpow : Real.log ((q ^ 2 : ℕ) : ℝ) = 2 * Real.log (q : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hlogpow] at hq2
  calc
    finiteHarmonic (q ^ 2) * finiteHarmonic q ≤
        (1 + 2 * Real.log (q : ℝ)) * (1 + Real.log (q : ℝ)) := by
      exact mul_le_mul hq2 hq1 (finiteHarmonic_nonneg q)
        (by positivity)
    _ ≤ 2 * (1 + Real.log (q : ℝ)) ^ 2 := by nlinarith

/-- The terminal part of the fourth-power estimate after cube-root
rounding.  On a dyadic interval (`N ≤ C`) the apparent fourth power of the
right endpoint is absorbed by the lower rounding inequality. -/
lemma dyadic_terminal_term_le {x : ℝ} {C N q : ℕ}
    (hx : 0 < x) (hq : 1 ≤ q) (hNC : N ≤ C)
    (hscale : (C : ℝ) ^ 4 ≤ 96 * x * (q : ℝ) ^ 3) :
    (512 : ℝ) * (N : ℝ) ^ 3 *
          (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) ≤
      131072 * (N : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hCN : ((C + N : ℕ) : ℝ) ≤ 2 * (C : ℝ) := by
    exact_mod_cast (show C + N ≤ 2 * C by omega)
  have hpow : ((C + N : ℕ) : ℝ) ^ 4 ≤ (2 * (C : ℝ)) ^ 4 := by
    gcongr
  have hratio : ((C + N : ℕ) : ℝ) ^ 4 / (6 * x) /
      (q : ℝ) ^ 3 ≤ 256 := by
    rw [div_le_iff₀ (pow_pos hqpos 3), div_le_iff₀ (by positivity : 0 < 6 * x)]
    calc
      ((C + N : ℕ) : ℝ) ^ 4 ≤ (2 * (C : ℝ)) ^ 4 := hpow
      _ = 16 * (C : ℝ) ^ 4 := by ring
      _ ≤ 16 * (96 * x * (q : ℝ) ^ 3) := by gcongr
      _ = 256 * (q : ℝ) ^ 3 * (6 * x) := by ring
  have hH : 0 ≤ finiteHarmonic (q ^ 2) * finiteHarmonic q :=
    mul_nonneg (finiteHarmonic_nonneg _) (finiteHarmonic_nonneg _)
  calc
    (512 : ℝ) * (N : ℝ) ^ 3 *
          (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) =
        (512 * (N : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q)) *
          (((C + N : ℕ) : ℝ) ^ 4 / (6 * x) / (q : ℝ) ^ 3) := by ring
    _ ≤ (512 * (N : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q)) * 256 := by
      gcongr
    _ = 131072 * (N : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by ring

/-- Fully elementary simplification of the fourth-power right-hand side:
after the dyadic and cube-root inequalities only the diagonal power-saving
term and a squared logarithm remain. -/
lemma dyadic_fourth_rhs_le {x : ℝ} {C N q : ℕ}
    (hx : 0 < x) (hq : 1 ≤ q) (hNC : N ≤ C)
    (hscale : (C : ℝ) ^ 4 ≤ 96 * x * (q : ℝ) ^ 3) :
    512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
        (512 : ℝ) * (N : ℝ) ^ 3 *
          (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
            (finiteHarmonic (q ^ 2) * finiteHarmonic q) ≤
      512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
        262144 * (N : ℝ) ^ 3 * (1 + Real.log q) ^ 2 := by
  have hterm :
    (512 : ℝ) * (N : ℝ) ^ 3 *
          (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) ≤
        262144 * (N : ℝ) ^ 3 * (1 + Real.log q) ^ 2 := by
    calc
      (512 : ℝ) * (N : ℝ) ^ 3 *
            (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
            (finiteHarmonic (q ^ 2) * finiteHarmonic q) ≤
          131072 * (N : ℝ) ^ 3 *
            (finiteHarmonic (q ^ 2) * finiteHarmonic q) :=
        dyadic_terminal_term_le hx hq hNC hscale
      _ ≤ 131072 * (N : ℝ) ^ 3 *
            (2 * (1 + Real.log q) ^ 2) := by
        exact mul_le_mul_of_nonneg_left (finiteHarmonic_sq_mul_le hq) (by positivity)
      _ = 262144 * (N : ℝ) ^ 3 * (1 + Real.log q) ^ 2 := by ring
  exact add_le_add_right hterm _

/-- The concrete high-frequency, dyadic reciprocal exponential-sum bound.
The shift parameter is selected internally, so no rounding side conditions
remain in the statement. -/
theorem reciprocalExpRange_fourth_le_dyadic_highFrequency
    (x : ℝ) (C N : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hN : 0 < N) (hNC : N ≤ C)
    (hone : 12 * x ≤ (C : ℝ) ^ 4)
    (hhigh : (C : ℝ) ^ 4 <
      12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    let q := reciprocalShift x C N
    ‖reciprocalExpRange x C N‖ ^ 4 ≤
      512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
        262144 * (N : ℝ) ^ 3 * (1 + Real.log q) ^ 2 := by
  let q := reciprocalShift x C N
  obtain ⟨hq, hqN, hderiv, hscale⟩ :=
    reciprocalShift_scale_bounds hx hN hone hhigh
  have hraw := reciprocalExpRange_fourth_le
    x C N q hx hC hq hqN hderiv
  exact hraw.trans (dyadic_fourth_rhs_le hx hq hNC hscale.le)

/-! ### Eliminating the shift parameter -/

/-- A cubic scale inequality gives the inverse-square saving used below. -/
private lemma inv_sq_le_rpow_two_thirds {a : ℝ} {q : ℕ}
    (ha : 0 ≤ a) (hq : 1 ≤ q)
    (hscale : 1 ≤ a * (q : ℝ) ^ 3) :
    1 / (q : ℝ) ^ 2 ≤ a ^ (2 / 3 : ℝ) := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (Real.rpow_nonneg ha _)
  have hsquare : (1 : ℝ) ≤ (a * (q : ℝ) ^ 3) ^ 2 := by
    nlinarith [sq_nonneg (a * (q : ℝ) ^ 3 - 1)]
  have hrpow : (a ^ (2 / 3 : ℝ)) ^ 3 = a ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul ha]
    norm_num
  rw [hrpow]
  calc
    (1 / (q : ℝ) ^ 2) ^ 3 = 1 / ((q : ℝ) ^ 3) ^ 2 := by
      field_simp
    _ ≤ a ^ 2 := by
      rw [div_le_iff₀ (by positivity : 0 < ((q : ℝ) ^ 3) ^ 2)]
      simpa [mul_pow] using hsquare

/-- The selected shift's diagonal factor, with the shift eliminated. -/
private lemma reciprocalShift_inv_sq_le {x : ℝ} {C N : ℕ}
    (hx : 0 < x) (hC : 0 < C) (hN : 0 < N)
    (hone : 12 * x ≤ (C : ℝ) ^ 4)
    (hhigh : (C : ℝ) ^ 4 < 12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    let q := reciprocalShift x C N
    1 / (q : ℝ) ^ 2 ≤
      (96 * x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) := by
  let q := reciprocalShift x C N
  obtain ⟨hq, -, -, hscale⟩ :=
    reciprocalShift_scale_bounds hx hN hone hhigh
  have hC4 : 0 < (C : ℝ) ^ 4 := by positivity
  have honeScale :
      1 ≤ (96 * x / (C : ℝ) ^ 4) * (q : ℝ) ^ 3 := by
    calc
      (1 : ℝ) = (C : ℝ) ^ 4 / (C : ℝ) ^ 4 := by field_simp
      _ ≤ (96 * x * (q : ℝ) ^ 3) / (C : ℝ) ^ 4 := by gcongr
      _ = (96 * x / (C : ℝ) ^ 4) * (q : ℝ) ^ 3 := by ring
  exact inv_sq_le_rpow_two_thirds (by positivity) hq honeScale

/-- In the high-frequency branch, the interval-length loss is absorbed by
the same sixth-root scale as the selected shift. -/
private lemma inv_length_le_scale {x : ℝ} {C N : ℕ}
    (hx : 0 < x) (hC : 0 < C) (hN : 0 < N)
    (hhigh : (C : ℝ) ^ 4 < 12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    1 / (N : ℝ) ≤
      (96 * x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) := by
  have hsqrt : 1 ≤ Nat.sqrt N := Nat.sqrt_pos.mpr hN
  have hC4 : 0 < (C : ℝ) ^ 4 := by positivity
  have honeScale :
      1 ≤ (96 * x / (C : ℝ) ^ 4) * (Nat.sqrt N : ℝ) ^ 3 := by
    have hscaled : (C : ℝ) ^ 4 < 96 * x * (Nat.sqrt N : ℝ) ^ 3 := by
      calc
        (C : ℝ) ^ 4 < 12 * x * (Nat.sqrt N : ℝ) ^ 3 := hhigh
        _ ≤ 96 * x * (Nat.sqrt N : ℝ) ^ 3 := by
          have : 0 ≤ x * (Nat.sqrt N : ℝ) ^ 3 := by positivity
          nlinarith
    calc
      (1 : ℝ) = (C : ℝ) ^ 4 / (C : ℝ) ^ 4 := by field_simp
      _ ≤ (96 * x * (Nat.sqrt N : ℝ) ^ 3) / (C : ℝ) ^ 4 := by gcongr
      _ = (96 * x / (C : ℝ) ^ 4) * (Nat.sqrt N : ℝ) ^ 3 := by ring
  have hsqrtInv :
      1 / (Nat.sqrt N : ℝ) ^ 2 ≤
        (96 * x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) :=
    inv_sq_le_rpow_two_thirds (by positivity) hsqrt honeScale
  have hsqrtSq : (Nat.sqrt N : ℝ) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast Nat.sqrt_le' N
  exact (one_div_le_one_div_of_le (by positivity) hsqrtSq).trans hsqrtInv

/-- A q-free fourth-power estimate.  The deliberately generous numerical
constant keeps all later consumers independent of rounding details. -/
theorem reciprocalExpRange_fourth_le_dyadic_qfree
    (x : ℝ) (C N : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hN : 0 < N) (hNC : N ≤ C)
    (hone : 12 * x ≤ (C : ℝ) ^ 4)
    (hhigh : (C : ℝ) ^ 4 <
      12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    ‖reciprocalExpRange x C N‖ ^ 4 ≤
      25214976 * (N : ℝ) ^ 4 *
        (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) *
        (1 + Real.log C) ^ 2 := by
  let q := reciprocalShift x C N
  let D := (96 * x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ)
  have hq : 1 ≤ q := (reciprocalShift_scale_bounds hx hN hone hhigh).1
  have hqC : q ≤ C :=
    (reciprocalShift_le_sqrt x C N).trans
      ((Nat.sqrt_le_self N).trans hNC)
  have hlogq : Real.log (q : ℝ) ≤ Real.log (C : ℝ) := by
    exact Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqC)
  have hlogC : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hD : 0 ≤ D := Real.rpow_nonneg (by positivity) _
  have hqInv : 1 / (q : ℝ) ^ 2 ≤ D :=
    reciprocalShift_inv_sq_le hx hC hN hone hhigh
  have hNInv : 1 / (N : ℝ) ≤ D :=
    inv_length_le_scale hx hC hN hhigh
  have hbase := reciprocalExpRange_fourth_le_dyadic_highFrequency
    x C N hx hC hN hNC hone hhigh
  change ‖reciprocalExpRange x C N‖ ^ 4 ≤
    512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
      262144 * (N : ℝ) ^ 3 * (1 + Real.log q) ^ 2 at hbase
  have hdiag :
      512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 ≤
        512 * (N : ℝ) ^ 4 * D := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hqInv) (by positivity)
  have hNpow : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 4 * D := by
    have hNr : (N : ℝ) ≠ 0 := by positivity
    calc
      (N : ℝ) ^ 3 = (N : ℝ) ^ 4 * (1 / (N : ℝ)) := by
        field_simp
      _ ≤ (N : ℝ) ^ 4 * D := by gcongr
  have hlogpow :
      (1 + Real.log (q : ℝ)) ^ 2 ≤
        (1 + Real.log (C : ℝ)) ^ 2 := by
    gcongr
  have hrough :
      ‖reciprocalExpRange x C N‖ ^ 4 ≤
        262656 * (N : ℝ) ^ 4 * D *
          (1 + Real.log (C : ℝ)) ^ 2 := by
    calc
      ‖reciprocalExpRange x C N‖ ^ 4 ≤
          512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
            262144 * (N : ℝ) ^ 3 * (1 + Real.log q) ^ 2 := hbase
      _ ≤ 512 * (N : ℝ) ^ 4 * D +
            262144 * ((N : ℝ) ^ 4 * D) *
              (1 + Real.log C) ^ 2 := by gcongr
      _ ≤ 262656 * (N : ℝ) ^ 4 * D *
            (1 + Real.log C) ^ 2 := by
        have : 1 ≤ (1 + Real.log (C : ℝ)) ^ 2 := by nlinarith
        have hND : 0 ≤ (N : ℝ) ^ 4 * D := by positivity
        nlinarith
  have hfactor :
      D ≤ 96 * (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) := by
    dsimp [D]
    have hδ : 0 ≤ x / (C : ℝ) ^ 4 := by positivity
    have h96 : (96 : ℝ) ^ (2 / 3 : ℝ) ≤ 96 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    rw [show 96 * x / (C : ℝ) ^ 4 =
      96 * (x / (C : ℝ) ^ 4) by ring, Real.mul_rpow (by norm_num) hδ]
    gcongr
  exact hrough.trans (by
    have hL : 0 ≤ (1 + Real.log (C : ℝ)) ^ 2 := sq_nonneg _
    calc
      262656 * (N : ℝ) ^ 4 * D * (1 + Real.log C) ^ 2 ≤
          262656 * (N : ℝ) ^ 4 *
            (96 * (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ)) *
              (1 + Real.log C) ^ 2 := by gcongr
      _ = 25214976 * (N : ℝ) ^ 4 *
            (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) *
              (1 + Real.log C) ^ 2 := by ring)

/-- Norm form of the q-free high-frequency estimate. -/
theorem norm_reciprocalExpRange_le_dyadic_qfree
    (x : ℝ) (C N : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hN : 0 < N) (hNC : N ≤ C)
    (hone : 12 * x ≤ (C : ℝ) ^ 4)
    (hhigh : (C : ℝ) ^ 4 <
      12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    ‖reciprocalExpRange x C N‖ ≤
      128 * (N : ℝ) *
        (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log C) := by
  have hδ : 0 ≤ x / (C : ℝ) ^ 4 := by positivity
  have hlogC : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hL : 0 ≤ 1 + Real.log (C : ℝ) := by positivity
  have hδpow :
      ((x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ)) ^ 4 =
        (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hδ]
    norm_num
  have hsqrtpow :
      (Real.sqrt (1 + Real.log (C : ℝ))) ^ 4 =
        (1 + Real.log (C : ℝ)) ^ 2 := by
    calc
      (Real.sqrt (1 + Real.log (C : ℝ))) ^ 4 =
          ((Real.sqrt (1 + Real.log (C : ℝ))) ^ 2) ^ 2 := by ring
      _ = (1 + Real.log (C : ℝ)) ^ 2 := by rw [Real.sq_sqrt hL]
  apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
  calc
    ‖reciprocalExpRange x C N‖ ^ 4 ≤
        25214976 * (N : ℝ) ^ 4 *
          (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) *
          (1 + Real.log C) ^ 2 :=
      reciprocalExpRange_fourth_le_dyadic_qfree
        x C N hx hC hN hNC hone hhigh
    _ ≤ (128 * (N : ℝ) *
          (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt (1 + Real.log C)) ^ 4 := by
      rw [mul_pow, mul_pow, mul_pow, hδpow, hsqrtpow]
      have hprod : 0 ≤ (N : ℝ) ^ 4 *
          (x / (C : ℝ) ^ 4) ^ (2 / 3 : ℝ) *
          (1 + Real.log (C : ℝ)) ^ 2 := by positivity
      norm_num
      nlinarith

/-- Natural-interval form of the q-free high-frequency estimate, for
`A < n ≤ B`. -/
theorem norm_reciprocalExpSum_le_dyadic_qfree
    (x : ℝ) (A B : ℕ)
    (hx : 0 < x) (hAB : A ≤ B) (hne : A < B)
    (hdyadic : B - A ≤ A + 1)
    (hone : 12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4)
    (hhigh : ((A + 1 : ℕ) : ℝ) ^ 4 <
      12 * x * (Nat.sqrt (B - A) : ℝ) ^ 3) :
    ‖reciprocalExpSum x A B‖ ≤
      128 * ((B - A : ℕ) : ℝ) *
        (x / ((A + 1 : ℕ) : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log ((A + 1 : ℕ) : ℝ)) := by
  rw [reciprocalExpSum_eq_range x A B hAB]
  exact norm_reciprocalExpRange_le_dyadic_qfree
    x (A + 1) (B - A) hx (by omega) (by omega) hdyadic hone hhigh

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/TypeI.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Dyadic bookkeeping for Type-I sums

This file contains the combinatorial part of a Type-I estimate.  The
oscillatory estimate on one dyadic block is deliberately exposed as a
hypothesis: the results here turn such block estimates into estimates for an
arbitrary initial interval, while keeping track of coefficient bounds and the
single loss `Nat.log 2 N + 1` from dyadic subdivision.
-/

namespace TypeI

open scoped BigOperators

/-- The half-open dyadic interval `[2^j, 2^(j+1))`. -/
def dyadicBlock (j : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ j) (2 ^ (j + 1))

@[simp] lemma mem_dyadicBlock {j m : ℕ} :
    m ∈ dyadicBlock j ↔ 2 ^ j ≤ m ∧ m < 2 ^ (j + 1) := by
  simp [dyadicBlock]

/-- A dyadic interval has exactly `2^j` elements. -/
lemma card_dyadicBlock (j : ℕ) : (dyadicBlock j).card = 2 ^ j := by
  rw [dyadicBlock, Nat.card_Ico, pow_succ]
  omega

/-- The number of dyadic blocks needed to cover `{1, ..., N}`. -/
def dyadicCount (N : ℕ) : ℕ := Nat.log 2 N + 1

/-- The last endpoint supplied by `dyadicCount` lies strictly beyond `N`. -/
lemma lt_two_pow_dyadicCount (N : ℕ) : N < 2 ^ dyadicCount N := by
  simpa [dyadicCount] using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N

/-- The part of a dyadic block that remains in `{1, ..., N}`. -/
def truncatedDyadicBlock (N j : ℕ) : Finset ℕ :=
  (dyadicBlock j).filter (fun m => m ≤ N)

@[simp] lemma mem_truncatedDyadicBlock {N j m : ℕ} :
    m ∈ truncatedDyadicBlock N j ↔
      2 ^ j ≤ m ∧ m < 2 ^ (j + 1) ∧ m ≤ N := by
  simp [truncatedDyadicBlock, and_assoc]

/-- Exact dyadic decomposition up to a power of two. -/
lemma sum_dyadicBlocks {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (J : ℕ) :
    (∑ m ∈ Finset.Ico 1 (2 ^ J), f m) =
      ∑ j ∈ Finset.range J, ∑ m ∈ dyadicBlock j, f m := by
  induction J with
  | zero => simp [dyadicBlock]
  | succ J ih =>
      rw [Finset.sum_range_succ, ← ih]
      simpa [dyadicBlock, Nat.succ_eq_add_one] using
        (Finset.sum_Ico_consecutive f
          (show 1 ≤ 2 ^ J by
            have : 0 < 2 ^ J := pow_pos (by norm_num) J
            omega)
          (show 2 ^ J ≤ 2 ^ (J + 1) by
            rw [pow_succ]
            omega)).symm

/-- Exact dyadic decomposition of an arbitrary initial interval.  Empty
tails of the final block are removed by `truncatedDyadicBlock`. -/
lemma sum_truncatedDyadicBlocks {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) :
    (∑ m ∈ Finset.Ico 1 (N + 1), f m) =
      ∑ j ∈ Finset.range (dyadicCount N),
        ∑ m ∈ truncatedDyadicBlock N j, f m := by
  let g : ℕ → M := fun m => if m ≤ N then f m else 0
  have hdecomp := sum_dyadicBlocks g (dyadicCount N)
  have hupper : N + 1 ≤ 2 ^ dyadicCount N := by
    exact lt_two_pow_dyadicCount N
  have hleft :
      (∑ m ∈ Finset.Ico 1 (2 ^ dyadicCount N), g m) =
        ∑ m ∈ Finset.Ico 1 (N + 1), f m := by
    rw [← Finset.sum_Ico_consecutive g (by omega : 1 ≤ N + 1) hupper]
    have hfirst : (∑ m ∈ Finset.Ico 1 (N + 1), g m) =
        ∑ m ∈ Finset.Ico 1 (N + 1), f m := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_Ico] at hm
      simp [g, Nat.le_of_lt_succ hm.2]
    have htail :
        (∑ m ∈ Finset.Ico (N + 1) (2 ^ dyadicCount N), g m) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      simp only [Finset.mem_Ico] at hm
      simp [g, show ¬m ≤ N by omega]
    rw [hfirst, htail, add_zero]
  rw [hleft] at hdecomp
  rw [hdecomp]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [truncatedDyadicBlock, g, Finset.sum_filter]

/-- A finite Type-I sum: coefficients `a m` multiply a family of inner
oscillatory sums `F m`. -/
def sum (K : Type*) [Semiring K] (a F : ℕ → K) (N : ℕ) : K :=
  ∑ m ∈ Finset.Ico 1 (N + 1), a m * F m

/-- The contribution from one (possibly truncated) dyadic block. -/
def blockSum (K : Type*) [Semiring K] (a F : ℕ → K) (N j : ℕ) : K :=
  ∑ m ∈ truncatedDyadicBlock N j, a m * F m

/-- Truncation can only decrease the cardinality of a dyadic block. -/
lemma card_truncatedDyadicBlock_le (N j : ℕ) :
    (truncatedDyadicBlock N j).card ≤ 2 ^ j := by
  rw [← card_dyadicBlock j]
  exact Finset.card_filter_le _ _

section NormBounds

variable {K : Type*} [NormedRing K]

/-- The abstract analytic input for Type-I bookkeeping.  It says that every
coefficient sequence bounded by `A` admits the stated estimate on each
truncated dyadic block.  In the Granville--Ramaré application, proving this
predicate is the oscillatory-sum part of the argument. -/
def HasBlockEstimate (F : ℕ → K) (N : ℕ) (A : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ j < dyadicCount N, ∀ a : ℕ → K,
    (∀ m ∈ truncatedDyadicBlock N j, ‖a m‖ ≤ A) →
      ‖blockSum K a F N j‖ ≤ B j

end NormBounds

section InnerIntervals

end InnerIntervals

section PartialSummation

/-- Masking a sequence below `A` turns an ordinary prefix into a local
prefix on `(A,t]`. -/
lemma sum_range_intervalMask {K : Type*} [AddCommMonoid K]
    (z : ℕ → K) (A t : ℕ) :
    (∑ n ∈ Finset.range (t + 1), if A < n then z n else 0) =
      ∑ n ∈ Finset.Ioc A t, z n := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  · intro n hn
    rfl

/-- Local summation by parts on a half-open natural interval. -/
lemma sum_Ioc_by_parts_local
    (f : ℕ → ℝ) (z : ℕ → ℂ) {A B : ℕ} (hAB : A < B) :
    (∑ n ∈ Finset.Ioc A B, f n • z n) =
      f B • (∑ n ∈ Finset.Ioc A B, z n) -
        ∑ t ∈ Finset.Ioc A (B - 1),
          (f (t + 1) - f t) • (∑ n ∈ Finset.Ioc A t, z n) := by
  let g : ℕ → ℂ := fun n => if A < n then z n else 0
  have habel := Finset.sum_Ioc_by_parts f g hAB
  have hleft : (∑ n ∈ Finset.Ioc A B, f n • g n) =
      ∑ n ∈ Finset.Ioc A B, f n • z n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp [g, hn.1]
  have hprefix (t : ℕ) :
      (∑ n ∈ Finset.range (t + 1), g n) =
        ∑ n ∈ Finset.Ioc A t, z n := by
    exact sum_range_intervalMask z A t
  rw [hleft, hprefix B, hprefix A] at habel
  have hzero : (∑ n ∈ Finset.Ioc A A, z n) = 0 := by simp
  rw [hzero, smul_zero, sub_zero] at habel
  simpa only [hprefix] using habel

/-- Adjacent differences telescope on a local interval. -/
lemma sum_Ioc_adjacent_sub (f : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    (∑ t ∈ Finset.Ioc A B, (f (t + 1) - f t)) =
      f (B + 1) - f (A + 1) := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
      rw [Finset.sum_Ioc_succ_top hAB, ih]
      ring

/-- Norm form of local summation by parts. -/
lemma norm_sum_Ioc_smul_le
    (f : ℕ → ℝ) (z : ℕ → ℂ) {A B : ℕ} (P : ℝ)
    (hAB : A < B) (_hP : 0 ≤ P) (hfB : 0 ≤ f B)
    (hmono : ∀ t, A < t → t < B → 0 ≤ f (t + 1) - f t)
    (hprefix : ∀ t, A ≤ t → t ≤ B →
      ‖∑ n ∈ Finset.Ioc A t, z n‖ ≤ P) :
    ‖∑ n ∈ Finset.Ioc A B, f n • z n‖ ≤
      (f B + (f B - f (A + 1))) * P := by
  rw [sum_Ioc_by_parts_local f z hAB]
  calc
    ‖f B • (∑ n ∈ Finset.Ioc A B, z n) -
          ∑ t ∈ Finset.Ioc A (B - 1),
            (f (t + 1) - f t) • (∑ n ∈ Finset.Ioc A t, z n)‖ ≤
        ‖f B • (∑ n ∈ Finset.Ioc A B, z n)‖ +
          ‖∑ t ∈ Finset.Ioc A (B - 1),
            (f (t + 1) - f t) • (∑ n ∈ Finset.Ioc A t, z n)‖ :=
      norm_sub_le _ _
    _ ≤ f B * P +
        ∑ t ∈ Finset.Ioc A (B - 1), (f (t + 1) - f t) * P := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfB]
        exact mul_le_mul_of_nonneg_left (hprefix B (by omega) le_rfl) hfB
      · calc
          ‖∑ t ∈ Finset.Ioc A (B - 1),
              (f (t + 1) - f t) • (∑ n ∈ Finset.Ioc A t, z n)‖ ≤
              ∑ t ∈ Finset.Ioc A (B - 1),
                ‖(f (t + 1) - f t) •
                  (∑ n ∈ Finset.Ioc A t, z n)‖ := norm_sum_le _ _
          _ ≤ ∑ t ∈ Finset.Ioc A (B - 1),
                (f (t + 1) - f t) * P := by
            apply Finset.sum_le_sum
            intro t ht
            have ht' := Finset.mem_Ioc.mp ht
            have hdiff : 0 ≤ f (t + 1) - f t := hmono t ht'.1 (by omega)
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff]
            exact mul_le_mul_of_nonneg_left
              (hprefix t (by omega) (by omega)) hdiff
    _ = (f B + (f B - f (A + 1))) * P := by
      rw [← Finset.sum_mul]
      have hle : A ≤ B - 1 := by omega
      rw [sum_Ioc_adjacent_sub f hle]
      have hsub : B - 1 + 1 = B := by omega
      rw [hsub]
      ring

/-- Granville--Ramaré Lemma 9.2 in a form without a finite `max`: `P` is
any common bound for all partial reciprocal sums on `(A,t]`. -/
lemma norm_logWeightedSum_le
    (z : ℕ → ℂ) {A B : ℕ} (P : ℝ)
    (hA : 1 ≤ A) (hAB : A < B) (hP : 0 ≤ P)
    (hprefix : ∀ t, A ≤ t → t ≤ B →
      ‖∑ n ∈ Finset.Ioc A t, z n‖ ≤ P) :
    ‖∑ n ∈ Finset.Ioc A B, Real.log (n : ℝ) • z n‖ ≤
      Real.log (((B : ℝ) ^ 2) / (A : ℝ)) * P := by
  have hBlog : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have hmono : ∀ t, A < t → t < B →
      0 ≤ Real.log ((t + 1 : ℕ) : ℝ) - Real.log (t : ℝ) := by
    intro t htA htB
    apply sub_nonneg.mpr
    exact Real.strictMonoOn_log.monotoneOn
      (show (t : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        exact_mod_cast (show 0 < t by omega))
      (show ((t + 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        exact_mod_cast (show 0 < t + 1 by omega))
      (by norm_cast; omega)
  have hbasic := norm_sum_Ioc_smul_le
    (fun n => Real.log (n : ℝ)) z P hAB hP hBlog hmono hprefix
  refine hbasic.trans ?_
  apply mul_le_mul_of_nonneg_right ?_ hP
  have hApos : (0 : ℝ) < A := by positivity
  have hA1pos : (0 : ℝ) < A + 1 := by positivity
  have hlogA : Real.log (A : ℝ) ≤ Real.log (A + 1 : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hApos hA1pos (by norm_cast; omega)
  have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  have hAne : (A : ℝ) ≠ 0 := by exact_mod_cast (show A ≠ 0 by omega)
  rw [Real.log_div (pow_ne_zero 2 hBne) hAne, Real.log_pow]
  norm_num
  linarith

/-- Dyadic grouping gives the elementary harmonic bound needed in the Type-I
outer sum.  Keeping the exact natural logarithm count avoids any analytic
integration argument. -/
lemma sum_inv_le_dyadicCount (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹) ≤ dyadicCount N := by
  have hsets : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hsets, sum_truncatedDyadicBlocks]
  calc
    (∑ j ∈ Finset.range (dyadicCount N),
        ∑ m ∈ truncatedDyadicBlock N j, (m : ℝ)⁻¹) ≤
        ∑ _j ∈ Finset.range (dyadicCount N), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        (∑ m ∈ truncatedDyadicBlock N j, (m : ℝ)⁻¹) ≤
            ∑ _m ∈ truncatedDyadicBlock N j, ((2 ^ j : ℕ) : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro m hm
          have hm' := mem_truncatedDyadicBlock.mp hm
          rw [← one_div, ← one_div]
          exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hm'.1)
        _ = ((truncatedDyadicBlock N j).card : ℝ) *
            ((2 ^ j : ℕ) : ℝ)⁻¹ := by simp
        _ ≤ ((2 ^ j : ℕ) : ℝ) * ((2 ^ j : ℕ) : ℝ)⁻¹ := by
          gcongr
          exact_mod_cast card_truncatedDyadicBlock_le N j
        _ = 1 := by
          rw [mul_inv_cancel₀]
          positivity
    _ = dyadicCount N := by simp

/-- Convert the exact block count to a real logarithmic factor. -/
lemma dyadicCount_cast_le_log_div_add_one {N : ℕ} (hN : N ≠ 0) :
    (dyadicCount N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 + 1 := by
  have hpowN : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN
  have hpowpos : (0 : ℝ) < ((2 ^ Nat.log 2 N : ℕ) : ℝ) := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hN
  have hpowNR : (((2 ^ Nat.log 2 N : ℕ) : ℝ)) ≤ (N : ℝ) := by
    exact_mod_cast hpowN
  have hlog := Real.strictMonoOn_log.monotoneOn hpowpos hNpos hpowNR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    rw [show (((2 ^ Nat.log 2 N : ℕ) : ℝ)) =
      (2 : ℝ) ^ Nat.log 2 N by norm_num] at hlog
    rw [Real.log_pow] at hlog
    simpa [mul_comm] using hlog
  simpa [dyadicCount] using add_le_add_right hk 1

/-! ## Endpoint scaling for Proposition 8.1 -/

/-- Dividing an interval with `y' ≤ 2y` by a positive natural number
produces a dyadic interval up to the single unavoidable rounding unit. -/
lemma quotient_interval_sub_le {y y' m : ℕ} (hm : 1 ≤ m)
    (hy' : y' ≤ 2 * y) :
    y' / m - y / m ≤ y / m + 1 := by
  have hB : y' / m ≤ 2 * (y / m) + 1 := by
    calc
      y' / m ≤ (2 * y) / m := Nat.div_le_div_right hy'
      _ = (y + y) / m := by rw [two_mul]
      _ ≤ y / m + y / m + 1 :=
        Nat.add_div_le_div_add_div_add_one y y m
      _ = 2 * (y / m) + 1 := by omega
  omega

/-- A single global fourth-derivative inequality at `M` implies the
rescaled inequality needed for every outer variable `m ≤ M`.  The `+1`
is exactly the natural-floor endpoint in the reciprocal-sum theorem. -/
lemma scaled_fourth_derivative_condition
    {x : ℝ} {y m M : ℕ} (hx : 0 ≤ x) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hglobal : 12 * x * (M : ℝ) ^ 3 ≤ (y : ℝ) ^ 4) :
    12 * (x / (m : ℝ)) ≤ (((y / m) + 1 : ℕ) : ℝ) ^ 4 := by
  have hmpos : (0 : ℝ) < m := by positivity
  have hmpow : (m : ℝ) ^ 3 ≤ (M : ℝ) ^ 3 := by
    gcongr
  have hnum : 12 * x * (m : ℝ) ^ 3 ≤ (y : ℝ) ^ 4 :=
    (mul_le_mul_of_nonneg_left hmpow (mul_nonneg (by norm_num) hx)).trans hglobal
  have hlocal :
      12 * (x / (m : ℝ)) ≤ ((y : ℝ) / (m : ℝ)) ^ 4 := by
    calc
      12 * (x / (m : ℝ)) =
          (12 * x * (m : ℝ) ^ 3) / (m : ℝ) ^ 4 := by field_simp
      _ ≤ (y : ℝ) ^ 4 / (m : ℝ) ^ 4 :=
        (div_le_div_iff_of_pos_right (pow_pos hmpos 4)).2 hnum
      _ = ((y : ℝ) / (m : ℝ)) ^ 4 := by rw [div_pow]
  have hfloor :
      ((y : ℝ) / (m : ℝ)) < (((y / m) + 1 : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one ((y : ℝ) / (m : ℝ))
    rw [Nat.floor_div_natCast] at h
    simpa using h
  exact hlocal.trans (by gcongr)

/-- Rescaling the reciprocal phase from `x` to `x/m`. -/
lemma div_div_natCast_eq_div_mul_natCast
    (x : ℝ) {m l : ℕ} (hm : m ≠ 0) (hl : l ≠ 0) :
    (x / (m : ℝ)) / (l : ℝ) = x / ((m * l : ℕ) : ℝ) := by
  push_cast
  field_simp

/-- Exact identification of a product-phase sum on an arbitrary natural
interval with a reciprocal exponential sum after rescaling by the outer
variable. -/
lemma vaughanProductInner_eq_reciprocalExpSum
    (x : ℝ) (A B m : ℕ) (hm : 1 ≤ m) :
    (∑ l ∈ Finset.Ioc A B,
        Vaughan.reciprocalPhase x (m * l)) =
      reciprocalExpSum (x / (m : ℝ)) A B := by
  have hm0 : m ≠ 0 := by omega
  unfold reciprocalExpSum
  apply Finset.sum_congr rfl
  intro l hl
  have hl0 : l ≠ 0 := by
    have hl' := Finset.mem_Ioc.mp hl
    exact Nat.ne_of_gt ((Nat.zero_le _).trans_lt hl'.1)
  unfold Vaughan.reciprocalPhase e
  rw [div_div_natCast_eq_div_mul_natCast x hm0 hl0]

/-- The short-prefix complement to the q-free high-frequency estimate.
When the first-derivative test does not apply and the optimal Weyl shift
hits its length cap, taking `q = ⌊√N⌋` in the proved fourth-power
estimate gives an `N^(3/8) C^(1/2)` remainder after taking fourth roots.
The nested square roots keep the statement and proof free of fractional
power normalization side conditions. -/
lemma norm_reciprocalExpRange_le_cappedShift
    (x : ℝ) (C N : ℕ) (hx : 0 < x) (hC : 0 < C)
    (hN : 0 < N) (hNC : N ≤ C)
    (hone : 12 * x ≤ (C : ℝ) ^ 4)
    (hnotHalf : ¬ x / (C : ℝ) ^ 2 ≤ 1 / 2)
    (hnotHigh : ¬ (C : ℝ) ^ 4 <
      12 * x * (Nat.sqrt N : ℝ) ^ 3) :
    ‖reciprocalExpRange x C N‖ ≤
      16 * Real.sqrt (Real.sqrt (
        (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
          (1 + Real.log C) ^ 2)) := by
  let q := Nat.sqrt N
  have hq : 1 ≤ q := by
    dsimp [q]
    exact Nat.sqrt_pos.mpr hN
  have hqN : q ^ 2 ≤ N := by
    dsimp [q]
    exact Nat.sqrt_le' N
  have hsqrtCap : N ≤ 4 * q ^ 2 := by
    have hs := Nat.lt_succ_sqrt' N
    have hqpos : 0 < q := by omega
    dsimp [q] at hs ⊢
    nlinarith
  have hderiv : 12 * x * (q : ℝ) ^ 3 ≤ (C : ℝ) ^ 4 := by
    exact le_of_not_gt hnotHigh
  have hfour := reciprocalExpRange_fourth_le x C N q hx hC hq hqN hderiv
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hNCr : (N : ℝ) ≤ C := by exact_mod_cast hNC
  have hcapR : (N : ℝ) ≤ 4 * (q : ℝ) ^ 2 := by exact_mod_cast hsqrtCap
  have hCadd : ((C + N : ℕ) : ℝ) ≤ 2 * (C : ℝ) := by
    push_cast
    linarith
  have hxlower : (C : ℝ) ^ 2 < 2 * x := by
    have := lt_of_not_ge hnotHalf
    rw [lt_div_iff₀ (by positivity)] at this
    norm_num at this ⊢
    nlinarith
  have hratio :
      (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) ≤ 6 * (C : ℝ) ^ 2 := by
    have hp : ((C + N : ℕ) : ℝ) ^ 4 ≤ (2 * (C : ℝ)) ^ 4 := by gcongr
    rw [div_le_iff₀ (by positivity)]
    calc
      ((C + N : ℕ) : ℝ) ^ 4 ≤ (2 * (C : ℝ)) ^ 4 := hp
      _ ≤ (6 * (C : ℝ) ^ 2) * (6 * x) := by
        nlinarith [sq_nonneg ((C : ℝ) ^ 2)]
  have hqRatio :
      (N : ℝ) ^ 3 / (q : ℝ) ^ 3 ≤
        8 * Real.sqrt ((N : ℝ) ^ 3) := by
    have hcube : (N : ℝ) ^ 3 ≤ 64 * (q : ℝ) ^ 6 := by
      have hcubed : (N : ℝ) ^ 3 ≤ (4 * (q : ℝ) ^ 2) ^ 3 := by gcongr
      nlinarith
    have hsqrtBound : Real.sqrt ((N : ℝ) ^ 3) ≤ 8 * (q : ℝ) ^ 3 := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · nlinarith
    have hsqrtSq : Real.sqrt ((N : ℝ) ^ 3) ^ 2 = (N : ℝ) ^ 3 :=
      Real.sq_sqrt (by positivity)
    rw [div_le_iff₀ (by positivity)]
    have hmul := mul_le_mul_of_nonneg_left hsqrtBound
      (Real.sqrt_nonneg ((N : ℝ) ^ 3))
    nlinarith
  have hlogC : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hlogFactor : 1 ≤ (1 + Real.log (C : ℝ)) ^ 2 := by nlinarith
  have hharm :
      finiteHarmonic (q ^ 2) * finiteHarmonic q ≤
        2 * (1 + Real.log (C : ℝ)) ^ 2 := by
    have hqC : q ≤ C := (Nat.sqrt_le_self N).trans hNC
    have hlogq : Real.log (q : ℝ) ≤ Real.log (C : ℝ) :=
      Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqC)
    calc
      finiteHarmonic (q ^ 2) * finiteHarmonic q ≤
          2 * (1 + Real.log (q : ℝ)) ^ 2 := finiteHarmonic_sq_mul_le hq
      _ ≤ 2 * (1 + Real.log (C : ℝ)) ^ 2 := by gcongr
  let X := (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
    (1 + Real.log C) ^ 2
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hsqrtN : (N : ℝ) ≤ Real.sqrt ((N : ℝ) ^ 3) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast hN]
  have hNcube : (N : ℝ) ^ 3 ≤ X := by
    dsimp [X]
    calc
      (N : ℝ) ^ 3 = (N : ℝ) ^ 2 * (N : ℝ) := by ring
      _ ≤ (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) := by gcongr
      _ ≤ (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
          (1 + Real.log C) ^ 2 := by
        exact le_mul_of_one_le_right (by positivity) hlogFactor
  have hdiag :
      512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 ≤ 2048 * X := by
    have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hq2]
    calc
      512 * (N : ℝ) ^ 4 =
          (512 * (N : ℝ) ^ 3) * (N : ℝ) := by ring
      _ ≤ (512 * (N : ℝ) ^ 3) * (4 * (q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcapR (by positivity)
      _ = 2048 * (N : ℝ) ^ 3 * (q : ℝ) ^ 2 := by ring
      _ ≤ 2048 * X * (q : ℝ) ^ 2 := by gcongr
      _ = (2048 * X) * (q : ℝ) ^ 2 := by ring
  have hterminal :
      (512 : ℝ) * (N : ℝ) ^ 3 *
          (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) ≤
        49152 * X := by
    calc
      (512 : ℝ) * (N : ℝ) ^ 3 *
            (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
            (finiteHarmonic (q ^ 2) * finiteHarmonic q) =
          512 * ((N : ℝ) ^ 3 / (q : ℝ) ^ 3) *
            (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) *
              (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by ring
      _ ≤ 512 * (8 * Real.sqrt ((N : ℝ) ^ 3)) *
            (6 * (C : ℝ) ^ 2) *
              (2 * (1 + Real.log C) ^ 2) := by
        gcongr
        exact mul_nonneg (finiteHarmonic_nonneg _) (finiteHarmonic_nonneg _)
      _ = 49152 * X := by dsimp [X]; ring
  have hpow : ‖reciprocalExpRange x C N‖ ^ 4 ≤ (16 * Real.sqrt (Real.sqrt X)) ^ 4 := by
    have hsqrtX : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX
    have hsqrtsqrt : Real.sqrt (Real.sqrt X) ^ 2 = Real.sqrt X :=
      Real.sq_sqrt (Real.sqrt_nonneg X)
    have hnested : Real.sqrt (Real.sqrt X) ^ 4 = X := by
      calc
        Real.sqrt (Real.sqrt X) ^ 4 =
            (Real.sqrt (Real.sqrt X) ^ 2) ^ 2 := by ring
        _ = Real.sqrt X ^ 2 := by rw [hsqrtsqrt]
        _ = X := hsqrtX
    calc
      ‖reciprocalExpRange x C N‖ ^ 4 ≤
          512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
            (512 : ℝ) * (N : ℝ) ^ 3 *
              (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
              (finiteHarmonic (q ^ 2) * finiteHarmonic q) := hfour
      _ ≤ 2048 * X + 49152 * X := add_le_add hdiag hterminal
      _ ≤ 65536 * X := by nlinarith
      _ = (16 * Real.sqrt (Real.sqrt X)) ^ 4 := by
        rw [mul_pow, hnested]
        norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
    (by positivity) hpow

/-- An unconditional (within the standard dyadic derivative range) concrete
bound for a reciprocal exponential sum.  The three displayed terms are,
respectively, the first-derivative branch, the optimized two-step branch,
and the capped-shift remainder.  The proof chooses the applicable branch by
decidable real inequalities, so no exponential-sum estimate remains as a
hypothesis. -/
lemma norm_reciprocalExpRange_le_threeBranch
    (x : ℝ) (C N : ℕ) (hx : 0 < x) (hC : 0 < C)
    (hN : 0 < N) (hNC : N ≤ C)
    (hone : 12 * x ≤ (C : ℝ) ^ 4) :
    ‖reciprocalExpRange x C N‖ ≤
      ((C + N : ℕ) : ℝ) ^ 2 / x +
      128 * (N : ℝ) * (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log C) +
      16 * Real.sqrt (Real.sqrt (
        (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
          (1 + Real.log C) ^ 2)) := by
  have hfirst_nonneg : 0 ≤ ((C + N : ℕ) : ℝ) ^ 2 / x := by positivity
  have hhigh_nonneg : 0 ≤
      128 * (N : ℝ) * (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log C) := by positivity
  have hcap_nonneg : 0 ≤
      16 * Real.sqrt (Real.sqrt (
        (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
          (1 + Real.log C) ^ 2)) := by positivity
  by_cases hhalf : x / (C : ℝ) ^ 2 ≤ 1 / 2
  · have h := norm_reciprocalExpRange_le_firstDerivative x C N hx hC hhalf
    linarith
  · by_cases hhigh : (C : ℝ) ^ 4 <
        12 * x * (Nat.sqrt N : ℝ) ^ 3
    · have h := norm_reciprocalExpRange_le_dyadic_qfree
        x C N hx hC hN hNC hone hhigh
      linarith
    · have h := norm_reciprocalExpRange_le_cappedShift
        x C N hx hC hN hNC hone hhalf hhigh
      linarith

/-- Natural interval form of `norm_reciprocalExpRange_le_threeBranch`. -/
lemma norm_reciprocalExpSum_le_threeBranch
    (x : ℝ) (A B : ℕ) (hx : 0 < x) (hAB : A < B)
    (hdyadic : B - A ≤ A + 1)
    (hone : 12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4) :
    ‖reciprocalExpSum x A B‖ ≤
      ((B + 1 : ℕ) : ℝ) ^ 2 / x +
      128 * ((B - A : ℕ) : ℝ) *
        (x / ((A + 1 : ℕ) : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt (1 + Real.log (((A + 1 : ℕ) : ℝ))) +
      16 * Real.sqrt (Real.sqrt (
        ((A + 1 : ℕ) : ℝ) ^ 2 *
          Real.sqrt (((B - A : ℕ) : ℝ) ^ 3) *
            (1 + Real.log (((A + 1 : ℕ) : ℝ))) ^ 2)) := by
  rw [reciprocalExpSum_eq_range x A B hAB.le]
  have h := norm_reciprocalExpRange_le_threeBranch x (A + 1) (B - A)
    hx (by omega) (by omega) hdyadic
    (by simpa using hone)
  have hend : A + 1 + (B - A) = B + 1 := by omega
  simpa only [hend] using h

/-- The explicit three-branch majorant, packaged for partial summation. -/
noncomputable def threeBranchBound (x : ℝ) (A B : ℕ) : ℝ :=
  ((B + 1 : ℕ) : ℝ) ^ 2 / x +
    128 * ((B - A : ℕ) : ℝ) *
      (x / ((A + 1 : ℕ) : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log (((A + 1 : ℕ) : ℝ))) +
    16 * Real.sqrt (Real.sqrt (
      ((A + 1 : ℕ) : ℝ) ^ 2 *
        Real.sqrt (((B - A : ℕ) : ℝ) ^ 3) *
          (1 + Real.log (((A + 1 : ℕ) : ℝ))) ^ 2))

/-- A closed-form numerator for summing the three-branch bounds over
`1 ≤ m ≤ M`.  Its three summands correspond to the three summands in
`threeBranchBound`; division by `m` is proved below. -/
noncomputable def threeBranchOuterNumerator (x : ℝ) (y M : ℕ) : ℝ :=
  16 * (y : ℝ) ^ 2 / x +
    256 * (y : ℝ) *
      (x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log (2 * y : ℕ)) +
    16 * Real.sqrt (Real.sqrt (
      (2 * (y : ℝ)) ^ 3 * Real.sqrt (2 * (y : ℝ)) * (M : ℝ) *
        (1 + Real.log (2 * y : ℕ)) ^ 2))

lemma threeBranchBound_nonneg {x : ℝ} (A B : ℕ) (hx : 0 < x) :
    0 ≤ threeBranchBound x A B := by
  unfold threeBranchBound
  positivity

/-- Each concrete inner bound has harmonic dependence on the outer
variable after replacing its parameters by the global endpoints. -/
lemma threeBranchBound_le_outerNumerator_div
    {x : ℝ} {y y' m M : ℕ} (hx : 0 < x) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hA : 1 ≤ y / m) (hy' : y' ≤ 2 * y) :
    threeBranchBound (x / (m : ℝ)) (y / m) (y' / m) ≤
      threeBranchOuterNumerator x y M / (m : ℝ) := by
  let A := y / m
  let B := y' / m
  let C := A + 1
  let N := B - A
  let a : ℝ := 2 * (y : ℝ)
  let L : ℝ := 1 + Real.log a
  have hmpos : (0 : ℝ) < m := by positivity
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmMR : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hmy : m ≤ y := by
    have h := (Nat.le_div_iff_mul_le (show 0 < m by omega)).mp hA
    simpa using h
  have hypos : (0 : ℝ) < y := by
    exact_mod_cast (lt_of_lt_of_le (show 0 < m by omega) hmy)
  have hapos : 0 < a := by dsimp [a]; positivity
  have hAcast : (A : ℝ) ≤ (y : ℝ) / (m : ℝ) := by
    dsimp [A]
    exact Nat.cast_div_le
  have hAone : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hCpos : (0 : ℝ) < C := by positivity
  have hCreal : (C : ℝ) ≤ a / (m : ℝ) := by
    have hCA : C ≤ 2 * A := by
      dsimp [C]
      omega
    calc
      (C : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hCA
      _ ≤ 2 * ((y : ℝ) / (m : ℝ)) := by gcongr
      _ = a / (m : ℝ) := by dsimp [a]; ring
  have hCa : (C : ℝ) ≤ a := hCreal.trans (div_le_self hapos.le hmone)
  have hNnat : N ≤ C := by
    dsimp [N, C, A, B]
    exact quotient_interval_sub_le hm hy'
  have hNC : (N : ℝ) ≤ C := by exact_mod_cast hNnat
  have hBC : B + 1 ≤ 2 * C := by
    have hB : B ≤ 2 * A + 1 := by
      dsimp [A, B]
      have hs := quotient_interval_sub_le hm hy'
      omega
    dsimp [C]
    omega
  have hBCreal : ((B + 1 : ℕ) : ℝ) ≤ 2 * (C : ℝ) := by exact_mod_cast hBC
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    have : 0 ≤ Real.log a := Real.log_nonneg (by
      dsimp [a]
      exact_mod_cast (show 1 ≤ 2 * y by omega))
    linarith
  have hlog : 1 + Real.log (C : ℝ) ≤ L := by
    dsimp [L]
    gcongr
  have hfirst :
      ((B + 1 : ℕ) : ℝ) ^ 2 / (x / (m : ℝ)) ≤
        (16 * (y : ℝ) ^ 2 / x) / (m : ℝ) := by
    have hupper : ((B + 1 : ℕ) : ℝ) ≤
        4 * (y : ℝ) / (m : ℝ) := by
      calc
        ((B + 1 : ℕ) : ℝ) ≤ 2 * (C : ℝ) := hBCreal
        _ ≤ 2 * (a / (m : ℝ)) := by gcongr
        _ = 4 * (y : ℝ) / (m : ℝ) := by dsimp [a]; ring
    have hid :
        (16 * (y : ℝ) ^ 2 / x) / (m : ℝ) =
          (4 * (y : ℝ) / (m : ℝ)) ^ 2 / (x / (m : ℝ)) := by
      field_simp
      norm_num
    rw [hid]
    exact div_le_div_of_nonneg_right (by gcongr) (by positivity)
  have hfloor : (y : ℝ) / (m : ℝ) ≤ (C : ℝ) := by
    have h := Nat.lt_floor_add_one ((y : ℝ) / (m : ℝ))
    rw [Nat.floor_div_natCast] at h
    simpa [C, A] using h.le
  have hbase :
      (x / (m : ℝ)) / (C : ℝ) ^ 4 ≤
        x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4 := by
    calc
      (x / (m : ℝ)) / (C : ℝ) ^ 4 ≤
          (x / (m : ℝ)) / ((y : ℝ) / (m : ℝ)) ^ 4 := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      _ = x * (m : ℝ) ^ 3 / (y : ℝ) ^ 4 := by field_simp
      _ ≤ x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4 := by gcongr
  have hsixth :
      128 * (N : ℝ) *
          ((x / (m : ℝ)) / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
            Real.sqrt (1 + Real.log C) ≤
        (256 * (y : ℝ) *
          (x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
            Real.sqrt L) / (m : ℝ) := by
    have hNupper : (N : ℝ) ≤ 2 * (y : ℝ) / (m : ℝ) := hNC.trans hCreal
    have hid :
        (256 * (y : ℝ) *
          (x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
            Real.sqrt L) / (m : ℝ) =
          128 * (2 * (y : ℝ) / (m : ℝ)) *
            (x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
              Real.sqrt L := by ring
    rw [hid]
    gcongr
  let X : ℝ := (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
    (1 + Real.log C) ^ 2
  let XG : ℝ := a ^ 3 * Real.sqrt a * (M : ℝ) * L ^ 2
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hXG : 0 ≤ XG := by dsimp [XG]; positivity
  have hsqrtN : Real.sqrt ((N : ℝ) ^ 3) ≤
      (C : ℝ) * Real.sqrt a := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hpow : (N : ℝ) ^ 3 ≤ (C : ℝ) ^ 3 := by gcongr
      have hCa' : (C : ℝ) ^ 3 ≤ (C : ℝ) ^ 2 * a := by
        nlinarith [sq_nonneg (C : ℝ)]
      calc
        (N : ℝ) ^ 3 ≤ (C : ℝ) ^ 3 := hpow
        _ ≤ (C : ℝ) ^ 2 * a := hCa'
        _ = ((C : ℝ) * Real.sqrt a) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hapos.le]
  have hXscale : X ≤ XG / (m : ℝ) ^ 4 := by
    have hcore : X ≤
        (a / (m : ℝ)) ^ 3 * Real.sqrt a * L ^ 2 := by
      dsimp [X]
      calc
        (C : ℝ) ^ 2 * Real.sqrt ((N : ℝ) ^ 3) *
            (1 + Real.log C) ^ 2 ≤
          (C : ℝ) ^ 2 * ((C : ℝ) * Real.sqrt a) * L ^ 2 := by gcongr
        _ = (C : ℝ) ^ 3 * Real.sqrt a * L ^ 2 := by ring
        _ ≤ (a / (m : ℝ)) ^ 3 * Real.sqrt a * L ^ 2 := by gcongr
    calc
      X ≤ (a / (m : ℝ)) ^ 3 * Real.sqrt a * L ^ 2 := hcore
      _ = (a ^ 3 * Real.sqrt a * (m : ℝ) * L ^ 2) /
          (m : ℝ) ^ 4 := by field_simp
      _ ≤ (a ^ 3 * Real.sqrt a * (M : ℝ) * L ^ 2) /
          (m : ℝ) ^ 4 := by gcongr
      _ = XG / (m : ℝ) ^ 4 := by rfl
  have hcaproot : Real.sqrt (Real.sqrt X) ≤
      Real.sqrt (Real.sqrt XG) / (m : ℝ) := by
    have hu4 : Real.sqrt (Real.sqrt X) ^ 4 = X := by
      calc
        Real.sqrt (Real.sqrt X) ^ 4 =
            (Real.sqrt (Real.sqrt X) ^ 2) ^ 2 := by ring
        _ = Real.sqrt X ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg X)]
        _ = X := Real.sq_sqrt hX
    have hv4 : (Real.sqrt (Real.sqrt XG) / (m : ℝ)) ^ 4 =
        XG / (m : ℝ) ^ 4 := by
      rw [div_pow]
      congr 1
      calc
        Real.sqrt (Real.sqrt XG) ^ 4 =
            (Real.sqrt (Real.sqrt XG) ^ 2) ^ 2 := by ring
        _ = Real.sqrt XG ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg XG)]
        _ = XG := Real.sq_sqrt hXG
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity)
    rw [hu4, hv4]
    exact hXscale
  have hcap : 16 * Real.sqrt (Real.sqrt X) ≤
      (16 * Real.sqrt (Real.sqrt XG)) / (m : ℝ) := by
    rw [show (16 * Real.sqrt (Real.sqrt XG)) / (m : ℝ) =
      16 * (Real.sqrt (Real.sqrt XG) / (m : ℝ)) by ring]
    gcongr
  change
    ((B + 1 : ℕ) : ℝ) ^ 2 / (x / (m : ℝ)) +
        128 * (N : ℝ) *
          ((x / (m : ℝ)) / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
            Real.sqrt (1 + Real.log C) +
        16 * Real.sqrt (Real.sqrt X) ≤ _
  unfold threeBranchOuterNumerator
  have ha_cast : (((2 * y : ℕ) : ℝ)) = a := by
    dsimp [a]
    push_cast
    rfl
  rw [ha_cast]
  change _ ≤
    ((16 * (y : ℝ) ^ 2 / x) +
      (256 * (y : ℝ) *
        (x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4) ^ (1 / 6 : ℝ) * Real.sqrt L) +
      16 * Real.sqrt (Real.sqrt XG)) / (m : ℝ)
  calc
    _ ≤ (16 * (y : ℝ) ^ 2 / x) / (m : ℝ) +
          (256 * (y : ℝ) *
            (x * (M : ℝ) ^ 3 / (y : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
              Real.sqrt L) / (m : ℝ) +
          (16 * Real.sqrt (Real.sqrt XG)) / (m : ℝ) := by
      exact add_le_add (add_le_add hfirst hsixth) hcap
    _ = _ := by ring

lemma threeBranchOuterNumerator_nonneg {x : ℝ} (y M : ℕ) (hx : 0 < x) :
    0 ≤ threeBranchOuterNumerator x y M := by
  unfold threeBranchOuterNumerator
  positivity

/-- Increasing the upper endpoint can only increase the packaged majorant. -/
lemma threeBranchBound_mono_upper {x : ℝ} {A B B' : ℕ}
    (hx : 0 < x) (hAB : A ≤ B) (hBB' : B ≤ B') :
    threeBranchBound x A B ≤ threeBranchBound x A B' := by
  have hsub : B - A ≤ B' - A := Nat.sub_le_sub_right hBB' A
  have hlog : 0 ≤ 1 + Real.log (((A + 1 : ℕ) : ℝ)) := by
    have : 0 ≤ Real.log (((A + 1 : ℕ) : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ A + 1 by omega))
    linarith
  unfold threeBranchBound
  gcongr

/-- Every partial sum of `(A,B]` is bounded by the full-interval packaged
majorant.  This is the exact interface required by Abel summation. -/
lemma norm_reciprocalExpSum_prefix_le_threeBranchBound
    (x : ℝ) (A B t : ℕ) (hx : 0 < x)
    (hAt : A ≤ t) (htB : t ≤ B)
    (hdyadic : B - A ≤ A + 1)
    (hone : 12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4) :
    ‖reciprocalExpSum x A t‖ ≤ threeBranchBound x A B := by
  by_cases hstrict : A < t
  · have htDyadic : t - A ≤ A + 1 :=
      (Nat.sub_le_sub_right htB A).trans hdyadic
    have h := norm_reciprocalExpSum_le_threeBranch
      x A t hx hstrict htDyadic hone
    exact h.trans (threeBranchBound_mono_upper hx hAt htB)
  · have ht : t = A := by omega
    subst t
    simp only [reciprocalExpSum, Finset.Ioc_self, Finset.sum_empty, norm_zero]
    exact threeBranchBound_nonneg A B hx

/-- Sum a family whose `m`-th estimate has the harmonic shape `Q/m`. -/
lemma sum_Icc_le_mul_dyadicCount
    (P : ℕ → ℝ) {M : ℕ} {Q : ℝ} (hQ : 0 ≤ Q)
    (hP : ∀ m ∈ Finset.Icc 1 M, P m ≤ Q / (m : ℝ)) :
    (∑ m ∈ Finset.Icc 1 M, P m) ≤ Q * dyadicCount M := by
  calc
    (∑ m ∈ Finset.Icc 1 M, P m) ≤
        ∑ m ∈ Finset.Icc 1 M, Q / (m : ℝ) :=
      Finset.sum_le_sum hP
    _ = Q * ∑ m ∈ Finset.Icc 1 M, (m : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      simp only [div_eq_mul_inv]
    _ ≤ Q * dyadicCount M :=
      mul_le_mul_of_nonneg_left (sum_inv_le_dyadicCount M) hQ

/-- Closed summation of all three analytic branches. -/
lemma sum_threeBranchBound_le
    {x : ℝ} {y y' M : ℕ} (hx : 0 < x) (hM : 1 ≤ M)
    (hy' : y' ≤ 2 * y)
    (hA : ∀ m ∈ Finset.Icc 1 M, 1 ≤ y / m) :
    (∑ m ∈ Finset.Icc 1 M,
        threeBranchBound (x / (m : ℝ)) (y / m) (y' / m)) ≤
      threeBranchOuterNumerator x y M * dyadicCount M := by
  apply sum_Icc_le_mul_dyadicCount
    (fun m => threeBranchBound (x / (m : ℝ)) (y / m) (y' / m))
    (Q := threeBranchOuterNumerator x y M)
    (threeBranchOuterNumerator_nonneg y M hx)
  intro m hm
  have hm' := Finset.mem_Icc.mp hm
  exact threeBranchBound_le_outerNumerator_div hx hm'.1 hm'.2 (hA m hm) hy'

/-- Coefficient and inner-sum bounds for a concrete finite outer Type-I
sum.  This is the final triangle-inequality step after Lemma 9.2. -/
lemma norm_outerSum_le
    (c : ℕ → ℂ) (S : ℕ → ℂ) (P : ℕ → ℝ) {M : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hc : ∀ m ∈ Finset.Icc 1 M, ‖c m‖ ≤ C)
    (hS : ∀ m ∈ Finset.Icc 1 M, ‖S m‖ ≤ P m) :
    ‖∑ m ∈ Finset.Icc 1 M, c m * S m‖ ≤
      C * ∑ m ∈ Finset.Icc 1 M, P m := by
  calc
    ‖∑ m ∈ Finset.Icc 1 M, c m * S m‖ ≤
        ∑ m ∈ Finset.Icc 1 M, ‖c m * S m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M, C * P m := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul]
      exact mul_le_mul (hc m hm) (hS m hm) (norm_nonneg _) hC
    _ = C * ∑ m ∈ Finset.Icc 1 M, P m := by
      rw [Finset.mul_sum]

/-! ## The actual Vaughan Type-I coefficients -/

open scoped ArithmeticFunction

/-- Bound the paper's `Σ₁` after its exact Vaughan expansion. -/
lemma norm_sigma1_le_of_inner
    (y y' M : ℕ) (w : ℕ → ℂ) (P : ℕ → ℝ)
    (hinner : ∀ m ∈ Finset.Icc 1 M,
      ‖∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (Real.log l : ℂ) * w (m * l)‖ ≤ P m) :
    ‖VaughanFourSums.sigma1 (Finset.Ioc y y') w M‖ ≤
      ∑ m ∈ Finset.Icc 1 M, P m := by
  rw [VaughanFourSums.sigma1_Ioc_eq_outer]
  have heq :
      (∑ m ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (ArithmeticFunction.moebius m : ℂ) *
            (Real.log l : ℂ) * w (m * l)) =
        ∑ m ∈ Finset.Icc 1 M,
          (ArithmeticFunction.moebius m : ℂ) *
            (∑ l ∈ Finset.Ioc (y / m) (y' / m),
              (Real.log l : ℂ) * w (m * l)) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [heq]
  simpa using norm_outerSum_le
    (fun m => (ArithmeticFunction.moebius m : ℂ))
    (fun m => ∑ l ∈ Finset.Ioc (y / m) (y' / m),
      (Real.log l : ℂ) * w (m * l)) P
    (C := 1) (by norm_num)
    (by
      intro m hm
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m))
    hinner

/-- Bound the paper's `Σ₂,₁` using its actual coefficient
`b_r = ∑_{mk=r,m≤M,k≤K} μ(m)Λ(k)` and the proved estimate
`|b_r| ≤ log r ≤ log M`. -/
lemma norm_sigma21_le_of_inner
    (y y' M K : ℕ) (w : ℕ → ℂ) (P : ℕ → ℝ) (hM : 1 ≤ M)
    (hinner : ∀ r ∈ Finset.Icc 1 M,
      ‖∑ l ∈ Finset.Ioc (y / r) (y' / r), w (r * l)‖ ≤ P r) :
    ‖VaughanFourSums.sigma21 (Finset.Ioc y y') w M K‖ ≤
      Real.log M * ∑ r ∈ Finset.Icc 1 M, P r := by
  rw [VaughanFourSums.sigma21_Ioc_eq_outer]
  have heq :
      (∑ r ∈ Finset.Icc 1 M, ∑ l ∈ Finset.Ioc (y / r) (y' / r),
          (VaughanFourSums.bCoeff M K r : ℂ) * w (r * l)) =
        ∑ r ∈ Finset.Icc 1 M,
          (VaughanFourSums.bCoeff M K r : ℂ) *
            (∑ l ∈ Finset.Ioc (y / r) (y' / r), w (r * l)) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
  rw [heq]
  apply norm_outerSum_le
  · exact Real.log_nonneg (by exact_mod_cast hM)
  · intro r hr
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (VaughanFourSums.abs_bCoeff_le_log M K r).trans ?_
    have hr' := Finset.mem_Icc.mp hr
    exact Real.strictMonoOn_log.monotoneOn
      (show (r : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        exact_mod_cast hr'.1)
      (show (M : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        exact_mod_cast hM)
      (by exact_mod_cast hr'.2)
  · exact hinner

/-- Assemble the two concrete Type-I pieces.  The only remaining input is a
pair of estimates for the displayed reciprocal inner sums; no abstract
`HasBlockEstimate` predicate occurs in the conclusion. -/
lemma norm_sigma1_add_sigma21_le_of_inner
    (y y' M K : ℕ) (w : ℕ → ℂ) (P : ℕ → ℝ) (L : ℝ)
    (hM : 1 ≤ M) (_hL : 0 ≤ L) (_hP : ∀ m, 0 ≤ P m)
    (hlogInner : ∀ m ∈ Finset.Icc 1 M,
      ‖∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (Real.log l : ℂ) * w (m * l)‖ ≤ L * P m)
    (hinner : ∀ m ∈ Finset.Icc 1 M,
      ‖∑ l ∈ Finset.Ioc (y / m) (y' / m), w (m * l)‖ ≤ P m) :
    ‖VaughanFourSums.sigma1 (Finset.Ioc y y') w M‖ +
        ‖VaughanFourSums.sigma21 (Finset.Ioc y y') w M K‖ ≤
      (L + Real.log M) * ∑ m ∈ Finset.Icc 1 M, P m := by
  have h1 := norm_sigma1_le_of_inner y y' M w (fun m => L * P m) hlogInner
  have h21 := norm_sigma21_le_of_inner y y' M K w P hM hinner
  calc
    ‖VaughanFourSums.sigma1 (Finset.Ioc y y') w M‖ +
          ‖VaughanFourSums.sigma21 (Finset.Ioc y y') w M K‖ ≤
        (∑ m ∈ Finset.Icc 1 M, L * P m) +
          Real.log M * ∑ m ∈ Finset.Icc 1 M, P m := add_le_add h1 h21
    _ = (L + Real.log M) * ∑ m ∈ Finset.Icc 1 M, P m := by
      have hs : (∑ m ∈ Finset.Icc 1 M, L * P m) =
          L * ∑ m ∈ Finset.Icc 1 M, P m := by rw [Finset.mul_sum]
      rw [hs]
      ring

/-- Lemma 9.2 specialized to one of the paper's inner product intervals.
The harmless factor `2 log(2y)` is a coarse, rounding-stable replacement for
the paper's `log(y'^2/(my))`. -/
lemma norm_logInner_le_two_log
    (y y' m : ℕ) (w : ℕ → ℂ) (P : ℝ)
    (hA : 1 ≤ y / m) (hy' : y' ≤ 2 * y) (hP : 0 ≤ P)
    (hprefix : ∀ t, y / m ≤ t → t ≤ y' / m →
      ‖∑ l ∈ Finset.Ioc (y / m) t, w (m * l)‖ ≤ P) :
    ‖∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (Real.log l : ℂ) * w (m * l)‖ ≤
      (2 * Real.log (2 * y : ℕ)) * P := by
  by_cases hAB : y / m < y' / m
  · have hraw := norm_logWeightedSum_le
      (fun l => w (m * l)) P hA hAB hP hprefix
    change ‖∑ l ∈ Finset.Ioc (y / m) (y' / m),
      Real.log (l : ℝ) • w (m * l)‖ ≤ _
    refine hraw.trans ?_
    apply mul_le_mul_of_nonneg_right ?_ hP
    let A := y / m
    let B := y' / m
    have hApos : (0 : ℝ) < A := by
      exact_mod_cast (show 0 < A by omega)
    have hBpos : (0 : ℝ) < B := by
      exact_mod_cast (show 0 < B by omega)
    have hAy : 0 ≤ Real.log (A : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hA)
    have hBle : B ≤ 2 * y := by
      dsimp [B]
      exact (Nat.div_le_self y' m).trans hy'
    have htwoYpos : (0 : ℝ) < (2 * y : ℕ) := by
      have hmpos : 0 < m := by
        by_contra hm
        have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        simp [hm0] at hA
      have hmy : m ≤ y := by
        have h := (Nat.le_div_iff_mul_le hmpos).mp hA
        simpa using h
      exact_mod_cast (show 0 < 2 * y by
        have : 0 < y := hmpos.trans_le hmy
        omega)
    have hlogB : Real.log (B : ℝ) ≤ Real.log (2 * y : ℕ) :=
      Real.strictMonoOn_log.monotoneOn hBpos htwoYpos (by exact_mod_cast hBle)
    have hAne : (A : ℝ) ≠ 0 := ne_of_gt hApos
    have hBne : (B : ℝ) ≠ 0 := ne_of_gt hBpos
    change Real.log (((B : ℝ) ^ 2) / (A : ℝ)) ≤
      2 * Real.log (2 * y : ℕ)
    calc
      Real.log (((B : ℝ) ^ 2) / (A : ℝ)) =
          2 * Real.log (B : ℝ) - Real.log (A : ℝ) := by
        rw [Real.log_div (pow_ne_zero 2 hBne) hAne, Real.log_pow]
        norm_num
      _ ≤ 2 * Real.log (B : ℝ) := sub_le_self _ hAy
      _ ≤ 2 * Real.log (2 * y : ℕ) :=
        mul_le_mul_of_nonneg_left hlogB (by norm_num)
  · have hempty : Finset.Ioc (y / m) (y' / m) = ∅ :=
      Finset.Ioc_eq_empty (by omega)
    rw [hempty]
    simp only [Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.log_nonneg (by
        have hypos : 0 < y := by
          by_contra hy0
          have : y = 0 := Nat.eq_zero_of_not_pos hy0
          simp [this] at hA
        exact_mod_cast (show 1 ≤ 2 * y by omega)))) hP

/-! ## Closed concrete Type-I estimate -/

/-- The actual `Σ₁ + Σ₂,₁` estimate obtained by combining Vaughan's
coefficients, the three proved reciprocal-sum branches, and Abel summation.
All hypotheses are explicit endpoint or derivative-range inequalities; in
particular there is no `HasBlockEstimate` or inner exponential-sum premise.

The finite sum on the right is intentionally left exact.  Its three terms
have respectively the first-derivative, sixth-root, and capped-shift shapes,
so later parameter specialization can sum each with the most convenient
elementary power estimate. -/
theorem norm_sigma1_add_sigma21_le_threeBranch
    (x : ℝ) (y y' M K : ℕ)
    (hx : 0 < x) (hM : 1 ≤ M) (hyy' : y ≤ y') (hy' : y' ≤ 2 * y)
    (hA : ∀ m ∈ Finset.Icc 1 M, 1 ≤ y / m)
    (hone : ∀ m ∈ Finset.Icc 1 M,
      12 * (x / (m : ℝ)) ≤ (((y / m) + 1 : ℕ) : ℝ) ^ 4) :
    ‖VaughanFourSums.sigma1 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M‖ +
      ‖VaughanFourSums.sigma21 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      (2 * Real.log (2 * y : ℕ) + Real.log M) *
        ∑ m ∈ Finset.Icc 1 M,
          threeBranchBound (x / (m : ℝ)) (y / m) (y' / m) := by
  have h1mem : 1 ∈ Finset.Icc 1 M := by simp [hM]
  have hyone : 1 ≤ y := by
    have := hA 1 h1mem
    simpa using this
  have hL : 0 ≤ 2 * Real.log (2 * y : ℕ) := by
    positivity
  have hP : ∀ m : ℕ, 0 ≤
      threeBranchBound (x / (m : ℝ)) (y / m) (y' / m) := by
    intro m
    unfold threeBranchBound
    positivity
  apply norm_sigma1_add_sigma21_le_of_inner
    y y' M K (Vaughan.reciprocalPhase x)
    (fun m => threeBranchBound (x / (m : ℝ)) (y / m) (y' / m))
    (2 * Real.log (2 * y : ℕ)) hM hL hP
  · intro m hm
    have hm' := Finset.mem_Icc.mp hm
    have hmpos : 0 < m := by omega
    apply norm_logInner_le_two_log y y' m
      (Vaughan.reciprocalPhase x)
      (threeBranchBound (x / (m : ℝ)) (y / m) (y' / m))
      (hA m hm) hy' (hP m)
    intro t hAt htB
    rw [vaughanProductInner_eq_reciprocalExpSum x (y / m) t m hm'.1]
    apply norm_reciprocalExpSum_prefix_le_threeBranchBound
      (x / (m : ℝ)) (y / m) (y' / m) t
      (div_pos hx (by exact_mod_cast hmpos)) hAt htB
      (quotient_interval_sub_le hm'.1 hy') (hone m hm)
  · intro m hm
    have hm' := Finset.mem_Icc.mp hm
    rw [vaughanProductInner_eq_reciprocalExpSum
      x (y / m) (y' / m) m hm'.1]
    apply norm_reciprocalExpSum_prefix_le_threeBranchBound
      (x / (m : ℝ)) (y / m) (y' / m) (y' / m)
      (div_pos hx (by exact_mod_cast (show 0 < m by omega)))
      (Nat.div_le_div_right hyy') le_rfl
      (quotient_interval_sub_le hm'.1 hy') (hone m hm)

/-- Fully summed Type-I endpoint in the global parameter range used by the
Granville--Ramaré assembly.  The right hand side contains no finite outer
sum and no analytic premise. -/
theorem norm_sigma1_add_sigma21_le_closed
    (x : ℝ) (y y' M K : ℕ)
    (hx : 0 < x) (hM : 1 ≤ M) (hMy : M ≤ y)
    (hyy' : y ≤ y') (hy' : y' ≤ 2 * y)
    (hglobal : 12 * x * (M : ℝ) ^ 3 ≤ (y : ℝ) ^ 4) :
    ‖VaughanFourSums.sigma1 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M‖ +
      ‖VaughanFourSums.sigma21 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      (2 * Real.log (2 * y : ℕ) + Real.log M) *
        (threeBranchOuterNumerator x y M * dyadicCount M) := by
  have hA : ∀ m ∈ Finset.Icc 1 M, 1 ≤ y / m := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    apply (Nat.le_div_iff_mul_le (show 0 < m by omega)).2
    simpa using hm'.2.trans hMy
  have hone : ∀ m ∈ Finset.Icc 1 M,
      12 * (x / (m : ℝ)) ≤ (((y / m) + 1 : ℕ) : ℝ) ^ 4 := by
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    exact scaled_fourth_derivative_condition hx.le hm'.1 hm'.2 hglobal
  have hraw := norm_sigma1_add_sigma21_le_threeBranch
    x y y' M K hx hM hyy' hy' hA hone
  refine hraw.trans ?_
  apply mul_le_mul_of_nonneg_left
    (sum_threeBranchBound_le hx hM hy' hA)
  exact add_nonneg
    (mul_nonneg (by norm_num) (Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * y by omega))))
    (Real.log_nonneg (by exact_mod_cast hM))

end PartialSummation

end TypeI

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/VaughanTypeIIExpansion.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Product expansions for the two Type-II Vaughan terms

This module is separate from `VaughanFourSums` so the basic four-piece
identity and the Type-I development do not depend on these further
reindexings.
-/

noncomputable section

namespace VaughanTypeIIExpansion

open scoped ArithmeticFunction BigOperators
open Vaughan VaughanFourSums

/-- Restrict an arithmetic function to indices at most `U`. -/
def truncateUpper (U : ℕ) (A : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ U then A n else 0, by simp⟩

/-- Truncating the first factor above `U` does not change a convolution at an
index `n ≤ U`. -/
theorem truncateUpper_mul_apply_of_le
    (U n : ℕ) (A B : ArithmeticFunction ℝ) (hn : n ≤ U) :
    (truncateUpper U A * B) n = (A * B) n := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl fun ml hml => ?_
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hml).1
  have hlpos : 0 < ml.2 := Nat.pos_of_ne_zero
    (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hml)
  have hmle : ml.1 ≤ n := by
    have h := Nat.le_mul_of_pos_right ml.1 hlpos
    rwa [hprod] at h
  change (if ml.1 ≤ U then A ml.1 else 0) * B ml.2 = A ml.1 * B ml.2
  rw [if_pos (hmle.trans hn)]

/-- The finite product regrouping with the automatic upper cutoff `y'`. -/
theorem finiteWeightedSum_Ioc_mul_eq_outer_to_endpoint
    (y y' : ℕ) (w : ℕ → ℂ) (A B : ArithmeticFunction ℝ) :
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
      ∑ m ∈ Finset.Icc 1 y', ∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (A m : ℂ) * (B l : ℂ) * w (m * l) := by
  calc
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
        finiteWeightedSum (Finset.Ioc y y') w (truncateUpper y' A * B) := by
      unfold finiteWeightedSum
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [truncateUpper_mul_apply_of_le y' n A B (Finset.mem_Ioc.mp hn).2]
    _ = ∑ m ∈ Finset.Icc 1 y', ∑ l ∈ innerProductInterval y y' m,
          (truncateUpper y' A m : ℂ) * (B l : ℂ) * w (m * l) := by
      apply finiteWeightedSum_Ioc_mul_eq_outer
      intro m hm
      change (if m ≤ y' then A m else 0) = 0
      rw [if_neg (not_le.mpr hm)]
    _ = ∑ m ∈ Finset.Icc 1 y', ∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (A m : ℂ) * (B l : ℂ) * w (m * l) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [innerProductInterval_eq_Ioc y y' m (Finset.mem_Icc.mp hm).1]
      change (∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (((if m ≤ y' then A m else 0 : ℝ)) : ℂ) *
            (B l : ℂ) * w (m * l)) = _
      rw [if_pos (Finset.mem_Icc.mp hm).2]

/-- Lower-annular form of the endpoint regrouping. -/
theorem finiteWeightedSum_Ioc_mul_eq_outer_endpoint_Ioc
    (y y' L : ℕ) (w : ℕ → ℂ) (A B : ArithmeticFunction ℝ)
    (hBelow : ∀ m, m ≤ L → A m = 0) :
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
      ∑ m ∈ Finset.Ioc L y', ∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (A m : ℂ) * (B l : ℂ) * w (m * l) := by
  rw [finiteWeightedSum_Ioc_mul_eq_outer_to_endpoint]
  symm
  refine Finset.sum_subset (M := ℂ) ?_ ?_
  · intro m hm
    have hm' := Finset.mem_Ioc.mp hm
    exact Finset.mem_Icc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) hm'.1, hm'.2⟩
  · intro m hmIcc hmnot
    have hmle : m ≤ L := by
      by_contra hnotle
      apply hmnot
      exact Finset.mem_Ioc.mpr ⟨lt_of_not_ge hnotle, (Finset.mem_Icc.mp hmIcc).2⟩
    simp [hBelow m hmle]

/-- Regroup a convolution whose first factor is supported on `(L,U]`. -/
theorem finiteWeightedSum_Ioc_mul_eq_outer_Ioc
    (y y' L U : ℕ) (w : ℕ → ℂ) (A B : ArithmeticFunction ℝ)
    (hAbove : ∀ m, U < m → A m = 0)
    (hBelow : ∀ m, m ≤ L → A m = 0) :
    finiteWeightedSum (Finset.Ioc y y') w (A * B) =
      ∑ m ∈ Finset.Ioc L U, ∑ l ∈ Finset.Ioc (y / m) (y' / m),
        (A m : ℂ) * (B l : ℂ) * w (m * l) := by
  rw [finiteWeightedSum_Ioc_mul_eq_outer y y' U w A B hAbove]
  have hconvert :
      (∑ m ∈ Finset.Icc 1 U, ∑ l ∈ innerProductInterval y y' m,
          (A m : ℂ) * (B l : ℂ) * w (m * l)) =
        ∑ m ∈ Finset.Icc 1 U, ∑ l ∈ Finset.Ioc (y / m) (y' / m),
          (A m : ℂ) * (B l : ℂ) * w (m * l) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [innerProductInterval_eq_Ioc y y' m (Finset.mem_Icc.mp hm).1]
  rw [hconvert]
  symm
  refine Finset.sum_subset (M := ℂ) ?_ ?_
  · intro m hm
    have hm' := Finset.mem_Ioc.mp hm
    exact Finset.mem_Icc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) hm'.1, hm'.2⟩
  · intro m hmIcc hmnot
    have hmle : m ≤ L := by
      by_contra hnotle
      apply hmnot
      exact Finset.mem_Ioc.mpr ⟨lt_of_not_ge hnotle, (Finset.mem_Icc.mp hmIcc).2⟩
    simp [hBelow m hmle]

/-- Exact outer-sum expansion of the paper's `Σ₂,₂`. -/
theorem sigma22_Ioc_eq_outer
    (y y' M K : ℕ) (w : ℕ → ℂ) :
    sigma22 (Finset.Ioc y y') w M K =
      ∑ r ∈ Finset.Ioc M (M * K), ∑ l ∈ Finset.Ioc (y / r) (y' / r),
        (bCoeff M K r : ℂ) * w (r * l) := by
  unfold sigma22 sigma22AF
  rw [mul_comm (ArithmeticFunction.zeta : ArithmeticFunction ℝ) (bHigh M K)]
  rw [finiteWeightedSum_Ioc_mul_eq_outer_Ioc]
  · refine Finset.sum_congr rfl fun r hr => ?_
    refine Finset.sum_congr rfl fun l hl => ?_
    have hrgt := (Finset.mem_Ioc.mp hr).1
    have hlne : l ≠ 0 := Nat.ne_of_gt
      (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hl).1)
    change ((if M < r then bCoeff M K r else 0 : ℝ) : ℂ) *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) l : ℂ) * w (r * l) = _
    rw [if_pos hrgt]
    simp [hlne]
  · intro r hr
    change (if M < r then bCoeff M K r else 0) = 0
    by_cases hMr : M < r
    · rw [if_pos hMr, bCoeff_eq_zero_of_mul_lt M K r hr]
    · rw [if_neg hMr]
  · intro r hr
    change (if M < r then bCoeff M K r else 0) = 0
    rw [if_neg (not_lt.mpr hr)]

/-- Exact outer-sum expansion of the paper's `Σ₃`. -/
theorem sigma3_Ioc_eq_outer
    (y y' M K : ℕ) (w : ℕ → ℂ) :
    sigma3 (Finset.Ioc y y') w M K =
      ∑ l ∈ Finset.Ioc M y',
        ∑ k ∈ Finset.Ioc (max K (y / l)) (y' / l),
          (aCoeff M l : ℂ) *
            (ArithmeticFunction.vonMangoldt k : ℂ) * w (k * l) := by
  unfold sigma3 sigma3AF
  rw [mul_comm (lambdaHigh K) (aHigh M)]
  rw [finiteWeightedSum_Ioc_mul_eq_outer_endpoint_Ioc]
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hlgt := (Finset.mem_Ioc.mp hl).1
    change ∑ k ∈ Finset.Ioc (y / l) (y' / l),
        ((if M < l then aCoeff M l else 0 : ℝ) : ℂ) *
          (lambdaHigh K k : ℂ) * w (l * k) = _
    rw [if_pos hlgt]
    have hset :
        (Finset.Ioc (y / l) (y' / l)).filter (fun k => K < k) =
          Finset.Ioc (max K (y / l)) (y' / l) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      omega
    rw [← hset, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _hk => ?_
    change (aCoeff M l : ℂ) *
        (((if K < k then ArithmeticFunction.vonMangoldt k else 0 : ℝ)) : ℂ) *
          w (l * k) =
        if K < k then
          (aCoeff M l : ℂ) *
            (ArithmeticFunction.vonMangoldt k : ℂ) * w (k * l)
        else 0
    by_cases hKk : K < k
    · simp [hKk, Nat.mul_comm]
    · simp [hKk]
  · intro l hl
    change (if M < l then aCoeff M l else 0) = 0
    rw [if_neg (not_lt.mpr hl)]

end VaughanTypeIIExpansion

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/TypeII.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The Type II Cauchy--Schwarz block for Erdős Problem 175

Granville--Ramaré, Proposition 9.4, first applies Cauchy--Schwarz in the
outer variable of a bilinear exponential sum.  All of the analytic content
then sits in a mean-square estimate for the reciprocal inner sums.  This file
separates that analytic input from the finite Hilbert-space bookkeeping.

The formulation below deliberately allows an arbitrary complex kernel.  In
the application the kernel is the product of the indicator of `uv ∈ I` and
`exp (2 * pi * I * x / (u * v))`.  Thus `ReciprocalInnerBound` is precisely
the premise to be supplied by the reciprocal exponential-sum estimates.

The last section assembles finitely many dyadic blocks and records the exact
decimal constant `10.54 = 527 / 50` used in Corollary 9.7.
-/

open scoped BigOperators

namespace TypeII

section OneBlock

variable {U V : Type*} [DecidableEq U] [DecidableEq V]

/-- The unnormalised `L²` norm of coefficients on a finite support. -/
noncomputable def l2Norm (s : Finset U) (a : U → ℂ) : ℝ :=
  Real.sqrt (∑ u ∈ s, ‖a u‖ ^ 2)

lemma l2Norm_nonneg (s : Finset U) (a : U → ℂ) : 0 ≤ l2Norm s a :=
  Real.sqrt_nonneg _

lemma l2Norm_sq (s : Finset U) (a : U → ℂ) :
    l2Norm s a ^ 2 = ∑ u ∈ s, ‖a u‖ ^ 2 := by
  rw [l2Norm, Real.sq_sqrt]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The inner sum in the second variable of a bilinear block. -/
def innerSum (vSupport : Finset V) (beta : V → ℂ) (kernel : U → V → ℂ)
    (u : U) : ℂ :=
  ∑ v ∈ vSupport, beta v * kernel u v

/-- A finite bilinear block. -/
def bilinearSum (uSupport : Finset U) (vSupport : Finset V)
    (alpha : U → ℂ) (beta : V → ℂ) (kernel : U → V → ℂ) : ℂ :=
  ∑ u ∈ uSupport, alpha u * innerSum vSupport beta kernel u

/-- The only analytic input used by the Type II block: a mean-square bound
for the reciprocal inner sums. -/
def ReciprocalInnerBound (uSupport : Finset U) (vSupport : Finset V)
    (beta : V → ℂ) (kernel : U → V → ℂ) (R : ℝ) : Prop :=
  (∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2) ≤
    R * ∑ v ∈ vSupport, ‖beta v‖ ^ 2

/-- The Gram kernel obtained after expanding the square of the inner sum. -/
def kernelCorrelation (uSupport : Finset U) (kernel : U → V → ℂ)
    (v w : V) : ℂ :=
  ∑ u ∈ uSupport, (starRingEnd ℂ) (kernel u v) * kernel u w

/-- Exact finite Gram expansion of the mean square of the inner sums. -/
lemma innerSum_meanSquare_eq_gram
    (uSupport : Finset U) (vSupport : Finset V)
    (beta : V → ℂ) (kernel : U → V → ℂ) :
    ((∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2 : ℝ) : ℂ) =
      ∑ v ∈ vSupport, ∑ w ∈ vSupport,
        (starRingEnd ℂ) (beta v) * beta w *
          kernelCorrelation uSupport kernel v w := by
  classical
  simp only [innerSum, kernelCorrelation]
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro u hu
  ring

/-- The Gram expansion followed by the triangle inequality.  This is the
source-level Cauchy step used to split pairs `(v,w)` into near and far ranges. -/
lemma innerSum_meanSquare_le_sum_norm_correlation
    (uSupport : Finset U) (vSupport : Finset V)
    (beta : V → ℂ) (kernel : U → V → ℂ) :
    (∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2) ≤
      ∑ v ∈ vSupport, ∑ w ∈ vSupport,
        ‖beta v‖ * ‖beta w‖ * ‖kernelCorrelation uSupport kernel v w‖ := by
  have heq := innerSum_meanSquare_eq_gram uSupport vSupport beta kernel
  have hre :
      (∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2) =
        (∑ v ∈ vSupport, ∑ w ∈ vSupport,
          (starRingEnd ℂ) (beta v) * beta w *
            kernelCorrelation uSupport kernel v w).re := by
    exact_mod_cast congr_arg Complex.re heq
  rw [hre]
  calc
    (∑ v ∈ vSupport, ∑ w ∈ vSupport,
        (starRingEnd ℂ) (beta v) * beta w *
          kernelCorrelation uSupport kernel v w).re
        ≤ ‖∑ v ∈ vSupport, ∑ w ∈ vSupport,
            (starRingEnd ℂ) (beta v) * beta w *
              kernelCorrelation uSupport kernel v w‖ := Complex.re_le_norm _
    _ ≤ ∑ v ∈ vSupport, ‖∑ w ∈ vSupport,
          (starRingEnd ℂ) (beta v) * beta w *
            kernelCorrelation uSupport kernel v w‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ vSupport, ∑ w ∈ vSupport,
          ‖(starRingEnd ℂ) (beta v) * beta w *
            kernelCorrelation uSupport kernel v w‖ := by
          apply Finset.sum_le_sum
          intro v hv
          exact norm_sum_le _ _
    _ = ∑ v ∈ vSupport, ∑ w ∈ vSupport,
          ‖beta v‖ * ‖beta w‖ * ‖kernelCorrelation uSupport kernel v w‖ := by
          apply Finset.sum_congr rfl
          intro v hv
          apply Finset.sum_congr rfl
          intro w hw
          simp [norm_mul]

/-- Cauchy--Schwarz in the outer variable, before any estimate for the
reciprocal inner sums is used. -/
lemma bilinear_cauchy_sq (uSupport : Finset U) (vSupport : Finset V)
    (alpha : U → ℂ) (beta : V → ℂ) (kernel : U → V → ℂ) :
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ^ 2 ≤
      (∑ u ∈ uSupport, ‖alpha u‖ ^ 2) *
        ∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2 := by
  classical
  calc
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ^ 2
        ≤ (∑ u ∈ uSupport,
            ‖alpha u * innerSum vSupport beta kernel u‖) ^ 2 := by
          gcongr
          exact norm_sum_le _ _
    _ = (∑ u ∈ uSupport,
          ‖alpha u‖ * ‖innerSum vSupport beta kernel u‖) ^ 2 := by
          simp_rw [norm_mul]
    _ ≤ (∑ u ∈ uSupport, ‖alpha u‖ ^ 2) *
          ∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2 := by
          exact Finset.sum_mul_sq_le_sq_mul_sq uSupport _ _

/-- Squared Type II estimate, conditional only on the reciprocal inner-sum
bound.  This division-free form is useful when the analytic estimate has
already been squared. -/
lemma bilinear_sq_le_of_reciprocalInnerBound
    (uSupport : Finset U) (vSupport : Finset V)
    (alpha : U → ℂ) (beta : V → ℂ) (kernel : U → V → ℂ) (R : ℝ)
    (hinner : ReciprocalInnerBound uSupport vSupport beta kernel R) :
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ^ 2 ≤
      (∑ u ∈ uSupport, ‖alpha u‖ ^ 2) *
        (R * ∑ v ∈ vSupport, ‖beta v‖ ^ 2) := by
  calc
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ^ 2
        ≤ (∑ u ∈ uSupport, ‖alpha u‖ ^ 2) *
            ∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2 :=
          bilinear_cauchy_sq uSupport vSupport alpha beta kernel
    _ ≤ (∑ u ∈ uSupport, ‖alpha u‖ ^ 2) *
          (R * ∑ v ∈ vSupport, ‖beta v‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hinner
            (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- Unsquared Type II estimate in `L² × L²` form. -/
lemma norm_bilinearSum_le_of_reciprocalInnerBound
    (uSupport : Finset U) (vSupport : Finset V)
    (alpha : U → ℂ) (beta : V → ℂ) (kernel : U → V → ℂ) (R : ℝ)
    (hR : 0 ≤ R)
    (hinner : ReciprocalInnerBound uSupport vSupport beta kernel R) :
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ≤
      l2Norm uSupport alpha * Real.sqrt R * l2Norm vSupport beta := by
  have hsquare := bilinear_sq_le_of_reciprocalInnerBound
    uSupport vSupport alpha beta kernel R hinner
  have hrhs_sq :
      (l2Norm uSupport alpha * Real.sqrt R * l2Norm vSupport beta) ^ 2 =
        (∑ u ∈ uSupport, ‖alpha u‖ ^ 2) *
          (R * ∑ v ∈ vSupport, ‖beta v‖ ^ 2) := by
    rw [mul_pow, mul_pow, l2Norm_sq, Real.sq_sqrt hR, l2Norm_sq]
    ring
  rw [← hrhs_sq] at hsquare
  have hleft : 0 ≤ ‖bilinearSum uSupport vSupport alpha beta kernel‖ := norm_nonneg _
  have hright :
      0 ≤ l2Norm uSupport alpha * Real.sqrt R * l2Norm vSupport beta := by
    exact mul_nonneg
      (mul_nonneg (l2Norm_nonneg _ _) (Real.sqrt_nonneg _))
      (l2Norm_nonneg _ _)
  nlinarith

end OneBlock

section ReciprocalKernel

/-- The unrestricted reciprocal phase kernel on a rectangle. -/
noncomputable def reciprocalKernel (x : ℝ) (u v : ℕ) : ℂ :=
  e (x / ((u * v : ℕ) : ℝ))

@[simp] lemma norm_reciprocalKernel (x : ℝ) (u v : ℕ) :
    ‖reciprocalKernel x u v‖ = 1 := by
  simp [reciprocalKernel]

/-- The kernel of a reciprocal bilinear sum, restricted to those products
which lie in an arbitrary finite interval `I`. -/
noncomputable def restrictedReciprocalKernel
    (I : Finset ℕ) (x : ℝ) (u v : ℕ) : ℂ :=
  if u * v ∈ I then e (x / ((u * v : ℕ) : ℝ)) else 0

lemma norm_restrictedReciprocalKernel_le_one
    (I : Finset ℕ) (x : ℝ) (u v : ℕ) :
    ‖restrictedReciprocalKernel I x u v‖ ≤ 1 := by
  simp only [restrictedReciprocalKernel]
  split_ifs
  · rw [norm_e]
  · simp

/-- Common support on an arbitrary outer interval `(A,B]`.  This variant is
used for the exact power-of-two partition, whose natural blocks are
`(2^j-1,2^(j+1)-1]`. -/
def productCorrelationSupportOn
    (y y' A B v w : ℕ) : Finset ℕ :=
  (Finset.Ioc A B).filter fun u ↦
    u * v ∈ Finset.Ioc y y' ∧ u * w ∈ Finset.Ioc y y'

lemma productCorrelationSupportOn_eq_Ioc
    (y y' A B v w : ℕ) (hv : 0 < v) (hw : 0 < w) :
    productCorrelationSupportOn y y' A B v w =
      Finset.Ioc (max A (max (y / v) (y / w)))
        (min B (min (y' / v) (y' / w))) := by
  ext u
  simp only [productCorrelationSupportOn, Finset.mem_filter, Finset.mem_Ioc]
  simp only [max_lt_iff, le_min_iff]
  rw [Nat.div_lt_iff_lt_mul hv, Nat.div_lt_iff_lt_mul hw,
    Nat.le_div_iff_mul_le hv, Nat.le_div_iff_mul_le hw]
  omega

/-- Exact product-restricted Gram correlation on an arbitrary outer
interval. -/
lemma kernelCorrelation_restrictedReciprocalKernel_Ioc_eq
    (x : ℝ) (y y' A B v w : ℕ) (hv : 0 < v) (hw : 0 < w) :
    kernelCorrelation (Finset.Ioc A B)
        (restrictedReciprocalKernel (Finset.Ioc y y') x) v w =
      ∑ u ∈ Finset.Ioc (max A (max (y / v) (y / w)))
          (min B (min (y' / v) (y' / w))),
        e ((x * (1 / (w : ℝ) - 1 / (v : ℝ))) / (u : ℝ)) := by
  rw [← productCorrelationSupportOn_eq_Ioc y y' A B v w hv hw]
  unfold kernelCorrelation productCorrelationSupportOn restrictedReciprocalKernel
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases huv : u * v ∈ Finset.Ioc y y'
  · by_cases huw : u * w ∈ Finset.Ioc y y'
    · simp only [huv, huw, if_pos, and_self]
      have huI := Finset.mem_Ioc.mp hu
      have hu0 : (u : ℝ) ≠ 0 := by
        exact_mod_cast (by omega : u ≠ 0)
      have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
      have hw0 : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
      rw [conj_e, ← e_add]
      congr 1
      push_cast
      field_simp
      ring
    · simp [huv, huw]
  · simp [huv]

/-- Norm form of the preceding identity with a positive phase.  This is the
exact interface expected by the q-free reciprocal exponential-sum bounds. -/
lemma norm_kernelCorrelation_restrictedReciprocalKernel_Ioc_eq_abs
    (x : ℝ) (y y' A B v w : ℕ) (hv : 0 < v) (hw : 0 < w) :
    ‖kernelCorrelation (Finset.Ioc A B)
        (restrictedReciprocalKernel (Finset.Ioc y y') x) v w‖ =
      ‖reciprocalExpSum
        |x * (1 / (w : ℝ) - 1 / (v : ℝ))|
        (max A (max (y / v) (y / w)))
        (min B (min (y' / v) (y' / w)))‖ := by
  rw [kernelCorrelation_restrictedReciprocalKernel_Ioc_eq x y y' A B v w hv hw]
  change ‖reciprocalExpSum
      (x * (1 / (w : ℝ) - 1 / (v : ℝ)))
      (max A (max (y / v) (y / w)))
      (min B (min (y' / v) (y' / w)))‖ = _
  by_cases hphase : 0 ≤ x * (1 / (w : ℝ) - 1 / (v : ℝ))
  · rw [abs_of_nonneg hphase]
  · rw [abs_of_neg (lt_of_not_ge hphase)]
    exact (norm_reciprocalExpSum_neg
      (x * (1 / (w : ℝ) - 1 / (v : ℝ)))
      (max A (max (y / v) (y / w)))
      (min B (min (y' / v) (y' / w)))).symm

/-- The exact finite bilinear reciprocal sum to which Proposition 9.4 is
applied.  The product restriction encodes the paper's arbitrary interval
`uv ∈ I`. -/
noncomputable def reciprocalBilinearSum
    (I uSupport vSupport : Finset ℕ) (x : ℝ)
    (alpha beta : ℕ → ℂ) : ℂ :=
  bilinearSum uSupport vSupport alpha beta
    (restrictedReciprocalKernel I x)

lemma reciprocalBilinearSum_eq
    (I uSupport vSupport : Finset ℕ) (x : ℝ)
    (alpha beta : ℕ → ℂ) :
    reciprocalBilinearSum I uSupport vSupport x alpha beta =
      ∑ u ∈ uSupport, ∑ v ∈ vSupport,
        if u * v ∈ I then alpha u * beta v * e (x / ((u * v : ℕ) : ℝ))
        else 0 := by
  unfold reciprocalBilinearSum bilinearSum innerSum restrictedReciprocalKernel
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs <;> ring

/-- The product-restricted reciprocal bilinear sum is symmetric after
swapping the two supports and their coefficient sequences.  This permits
each dyadic rectangle to be oriented with its larger side as the
Cauchy--Schwarz variable. -/
lemma reciprocalBilinearSum_comm
    (I uSupport vSupport : Finset ℕ) (x : ℝ)
    (alpha beta : ℕ → ℂ) :
    reciprocalBilinearSum I uSupport vSupport x alpha beta =
      reciprocalBilinearSum I vSupport uSupport x beta alpha := by
  rw [reciprocalBilinearSum_eq, reciprocalBilinearSum_eq, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  by_cases huv : u * v ∈ I
  · rw [if_pos huv]
    have hvu : v * u ∈ I := by simpa [Nat.mul_comm] using huv
    rw [if_pos hvu]
    simp only [Nat.mul_comm]
    ring
  · rw [if_neg huv]
    have hvu : v * u ∉ I := by simpa [Nat.mul_comm] using huv
    rw [if_neg hvu]

/-- In the residual branch of the reciprocal exponential-sum estimate the
one-step upper-frequency condition has failed, while the two-step
lower-frequency condition has also failed.  These two failures force the
remaining summation interval to be short.  This polynomial form avoids any
rounding issues involving fractional powers: if `N` is the interval length,
then `N⁴ ≤ 256 C³`.

Downstream we use this as the elementary source of the harmless
`4 * C^(3/4)` residual term. -/
lemma residual_interval_length_fourth_le
    (C N : ℕ) (t : ℝ) (hC : 0 < C) (hN : 0 < N)
    (hmiddle : (C : ℝ) ^ 3 < 4 * t)
    (hhighFails : 12 * t * (Nat.sqrt N : ℝ) ^ 3 ≤ (C : ℝ) ^ 4) :
    N ^ 4 ≤ 256 * C ^ 3 := by
  let s := Nat.sqrt N
  have hs : 0 < s := by
    dsimp only [s]
    exact Nat.sqrt_pos.mpr hN
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hscaled :
      3 * (C : ℝ) ^ 3 * (s : ℝ) ^ 3 <
        12 * t * (s : ℝ) ^ 3 := by
    have hmul := mul_lt_mul_of_pos_right hmiddle
      (mul_pos (by norm_num : (0 : ℝ) < 3) (pow_pos hsR 3))
    nlinarith
  have hcancel : (s : ℝ) ^ 3 < (C : ℝ) := by
    have hCpos : 0 < (C : ℝ) := by exact_mod_cast hC
    have hcombined :
        3 * (C : ℝ) ^ 3 * (s : ℝ) ^ 3 < (C : ℝ) ^ 4 :=
      hscaled.trans_le hhighFails
    have hC3pos : 0 < (C : ℝ) ^ 3 := pow_pos hCpos 3
    by_contra hnot
    have hle : (C : ℝ) ≤ (s : ℝ) ^ 3 := le_of_not_gt hnot
    have hmulNonneg :
        0 ≤ (C : ℝ) ^ 3 * ((s : ℝ) ^ 3 - (C : ℝ)) :=
      mul_nonneg hC3pos.le (sub_nonneg.mpr hle)
    nlinarith [pow_pos hCpos 4]
  have hscube : s ^ 3 ≤ C := by
    have hscubeLt : s ^ 3 < C := by exact_mod_cast hcancel
    exact hscubeLt.le
  have hNsq : N ≤ 4 * s ^ 2 := by
    have hsOne : 1 ≤ s := hs
    have hroot := Nat.lt_succ_sqrt N
    dsimp only [s] at hroot ⊢
    nlinarith
  have hpow := Nat.pow_le_pow_left hNsq 4
  have hsEightNine : s ^ 8 ≤ s ^ 9 := by
    rw [show s ^ 9 = s ^ 8 * s by ring]
    exact Nat.le_mul_of_pos_right _ hs
  calc
    N ^ 4 ≤ (4 * s ^ 2) ^ 4 := hpow
    _ = 256 * s ^ 8 := by ring
    _ ≤ 256 * s ^ 9 := Nat.mul_le_mul_left 256 hsEightNine
    _ = 256 * (s ^ 3) ^ 3 := by ring
    _ ≤ 256 * C ^ 3 :=
      Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left hscube 3)

/-- Interpolation for the difficult middle-frequency residual.  If `q` is
simultaneously bounded by the correlation length and by the one-step
reciprocal estimate, while the two-step high-frequency inequality fails,
then its seventh power has the uniform `C⁶` scale.  This is the
power-saving substitute for taking either of the two bounds separately. -/
lemma effective_k1_highFailure_seventh_le
    (C N : ℕ) (t L q : ℝ) (hC : 0 < C) (hN : 0 < N)
    (ht : 0 ≤ t) (hL : 0 ≤ L) (hq : 0 ≤ q)
    (hqN : q ≤ (N : ℝ))
    (hqK : q ≤ 24 * (C : ℝ) * Real.sqrt (t / (C : ℝ) ^ 3) *
      Real.sqrt L)
    (hhighFails : 12 * t * (Nat.sqrt N : ℝ) ^ 3 ≤ (C : ℝ) ^ 4) :
    q ^ 7 ≤ 147456 * (C : ℝ) ^ 6 * L ^ 2 := by
  let s := Nat.sqrt N
  have hCpos : 0 < (C : ℝ) := by exact_mod_cast hC
  have hs : 0 < s := by
    dsimp only [s]
    exact Nat.sqrt_pos.mpr hN
  have hsR : 0 ≤ (s : ℝ) := by positivity
  have hNsqNat : N ≤ 4 * s ^ 2 := by
    have hroot := Nat.lt_succ_sqrt N
    dsimp only [s] at hroot ⊢
    nlinarith
  have hNsq : (N : ℝ) ≤ 4 * (s : ℝ) ^ 2 := by
    exact_mod_cast hNsqNat
  have hq3 : q ^ 3 ≤ 64 * (s : ℝ) ^ 6 := by
    calc
      q ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ hq hqN 3
      _ ≤ (4 * (s : ℝ) ^ 2) ^ 3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg N) hNsq 3
      _ = 64 * (s : ℝ) ^ 6 := by ring
  have hratio : 0 ≤ t / (C : ℝ) ^ 3 :=
    div_nonneg ht (pow_nonneg hCpos.le 3)
  have hsratio : Real.sqrt (t / (C : ℝ) ^ 3) ^ 2 =
      t / (C : ℝ) ^ 3 := Real.sq_sqrt hratio
  have hsL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL
  let K := 24 * (C : ℝ) * Real.sqrt (t / (C : ℝ) ^ 3) * Real.sqrt L
  have hq4 : q ^ 4 ≤ K ^ 4 :=
    pow_le_pow_left₀ hq (by simpa only [K] using hqK) 4
  have hKscaled : (C : ℝ) ^ 2 * K ^ 4 = 24 ^ 4 * t ^ 2 * L ^ 2 := by
    dsimp only [K]
    rw [show (24 * (C : ℝ) * Real.sqrt (t / (C : ℝ) ^ 3) *
        Real.sqrt L) ^ 4 =
        24 ^ 4 * (C : ℝ) ^ 4 *
          (Real.sqrt (t / (C : ℝ) ^ 3) ^ 2) ^ 2 *
          (Real.sqrt L ^ 2) ^ 2 by ring, hsratio, hsL]
    field_simp
  have hq4scaled : (C : ℝ) ^ 2 * q ^ 4 ≤ 24 ^ 4 * t ^ 2 * L ^ 2 := by
    calc
      (C : ℝ) ^ 2 * q ^ 4 ≤ (C : ℝ) ^ 2 * K ^ 4 :=
        mul_le_mul_of_nonneg_left hq4 (sq_nonneg _)
      _ = 24 ^ 4 * t ^ 2 * L ^ 2 := hKscaled
  have hhighSq : 144 * t ^ 2 * (s : ℝ) ^ 6 ≤ (C : ℝ) ^ 8 := by
    have hleft : 0 ≤ 12 * t * (s : ℝ) ^ 3 := by positivity
    have hsquare := pow_le_pow_left₀ hleft
      (by simpa only [s] using hhighFails) 2
    nlinarith
  have hscaled : (C : ℝ) ^ 2 * q ^ 7 ≤
      (C : ℝ) ^ 2 * (147456 * (C : ℝ) ^ 6 * L ^ 2) := by
    have hmul := mul_le_mul hq3 hq4scaled
      (mul_nonneg (sq_nonneg _) (pow_nonneg hq 4))
      (mul_nonneg (by positivity) (pow_nonneg hsR 6))
    nlinarith [mul_nonneg (sq_nonneg L)
      (sub_nonneg.mpr hhighSq)]
  by_contra hnot
  have hlt : 147456 * (C : ℝ) ^ 6 * L ^ 2 < q ^ 7 :=
    lt_of_not_ge hnot
  have hscaledLt := mul_lt_mul_of_pos_left hlt (sq_pos_of_pos hCpos)
  exact (not_lt_of_ge hscaled) hscaledLt

/-- A convenient seventh-root form of the preceding polynomial bound.
The round coefficient `128` is deliberately generous; its seventh power
dominates `147456`. -/
lemma effective_k1_highFailure_le
    (C : ℕ) (L q : ℝ) (hC : 0 < C) (hL : 0 ≤ L)
    (hseven : q ^ 7 ≤ 147456 * (C : ℝ) ^ 6 * L ^ 2) :
    q ≤ 128 * (C : ℝ) ^ (6 / 7 : ℝ) * L ^ (2 / 7 : ℝ) := by
  have hC0 : 0 ≤ (C : ℝ) := by positivity
  have hCp : ((C : ℝ) ^ (6 / 7 : ℝ)) ^ 7 = (C : ℝ) ^ 6 := by
    rw [← Real.rpow_mul_natCast hC0]
    norm_num [Real.rpow_natCast]
  have hLp : (L ^ (2 / 7 : ℝ)) ^ 7 = L ^ 2 := by
    rw [← Real.rpow_mul_natCast hL]
    norm_num [Real.rpow_natCast]
  have hrhs :
      (128 * (C : ℝ) ^ (6 / 7 : ℝ) * L ^ (2 / 7 : ℝ)) ^ 7 =
        128 ^ 7 * (C : ℝ) ^ 6 * L ^ 2 := by
    rw [mul_pow, mul_pow, hCp, hLp]
  apply le_of_pow_le_pow_left₀ (by norm_num : (7 : ℕ) ≠ 0) (by positivity)
  rw [hrhs]
  calc
    q ^ 7 ≤ 147456 * (C : ℝ) ^ 6 * L ^ 2 := hseven
    _ ≤ 128 ^ 7 * (C : ℝ) ^ 6 * L ^ 2 := by gcongr <;> norm_num

/-- The integer near-pair threshold used on the power block of length
`2^j`.  Taking the exponent floor at the integer level makes the threshold
exactly computable while retaining the scale `(2^j)^(3/4)`. -/
def powerBlockThreshold (j : ℕ) : ℕ := 2 ^ (3 * j / 4)

@[simp] lemma powerBlockThreshold_pos (j : ℕ) :
    0 < powerBlockThreshold j := by
  simp [powerBlockThreshold]

/-- The standard dyadic support `(U,2U]`. -/
def dyadicNatBlock (U : ℕ) : Finset ℕ := Finset.Ioc U (2 * U)

@[simp] lemma card_dyadicNatBlock (U : ℕ) : (dyadicNatBlock U).card = U := by
  simp [dyadicNatBlock]
  omega

/-! ## Concrete Vaughan coefficient input -/

open VaughanFourSums

/-- On a positive input, the coefficient `a_z = μ_{≤z} * ζ` is exactly
the truncated Möbius divisor sum estimated in Proposition 10.1. -/
lemma aCoeff_eq_truncatedMobiusDivisorSum
    (z n : ℕ) (hn : 0 < n) :
    aCoeff z n = truncatedMobiusDivisorSum z n := by
  rw [aCoeff, ArithmeticFunction.coe_mul_zeta_apply]
  simp only [Vaughan.muLow, ArithmeticFunction.coe_mk]
  rw [← Finset.sum_filter]
  unfold truncatedMobiusDivisorSum
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd, _⟩, hdz⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn, hdz⟩, hd⟩
  · rintro ⟨⟨_hdpos, hdz⟩, hd⟩
    exact ⟨⟨hd, hn.ne'⟩, hdz⟩

/-- At a power of two, the truncated Möbius divisor sum is either `1`
or `0`: only the divisors `1` and `2` can contribute.  This controls the
single endpoint by which a closed-open power block differs from `(N,2N]`. -/
lemma abs_aCoeff_two_pow_le_one (M j : ℕ) (hM : 1 ≤ M) :
    |aCoeff M (2 ^ j)| ≤ 1 := by
  rw [aCoeff, ArithmeticFunction.coe_mul_zeta_apply,
    Nat.sum_divisors_prime_pow Nat.prime_two]
  simp only [Vaughan.muLow, ArithmeticFunction.coe_mk]
  let t : ℕ → ℝ := fun i ↦
    if 2 ^ i ≤ M then (ArithmeticFunction.moebius (2 ^ i) : ℝ) else 0
  change |∑ i ∈ Finset.range (j + 1), t i| ≤ 1
  have ht0 : t 0 = 1 := by simp [t, hM]
  have ht_ge_two (i : ℕ) (hi : 2 ≤ i) : t i = 0 := by
    simp only [t]
    split_ifs
    · rw [ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by omega)]
      simp [show i ≠ 1 by omega]
    · rfl
  rcases eq_or_lt_of_le hM with rfl | htwo
  · have ht_pos (i : ℕ) (hi : 1 ≤ i) : t i = 0 := by
      simp [t, show ¬ 2 ^ i ≤ 1 by
        exact not_le.mpr (Nat.one_lt_pow (by omega) (by norm_num))]
    have hsum : ∀ j : ℕ, ∑ i ∈ Finset.range (j + 1), t i = 1 := by
      intro k
      induction k with
      | zero => simpa using ht0
      | succ k ih =>
          rw [show k + 1 + 1 = (k + 1) + 1 by omega,
            Finset.sum_range_succ, ih, ht_pos (k + 1) (by omega), add_zero]
    rw [hsum j]
    norm_num
  · have ht1 : t 1 = -1 := by
      have h2M : 2 ≤ M := by omega
      simp [t, h2M, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    have hsum : ∀ k : ℕ, ∑ i ∈ Finset.range (k + 2), t i = 0 := by
      intro k
      induction k with
      | zero =>
          rw [show 0 + 2 = (1 : ℕ) + 1 by omega, Finset.sum_range_succ]
          simp [ht0, ht1]
      | succ k ih =>
          rw [show k + 1 + 2 = (k + 2) + 1 by omega,
            Finset.sum_range_succ, ih, ht_ge_two (k + 2) (by omega), add_zero]
    by_cases hj : j = 0
    · subst j
      simp [ht0]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := by
        exact ⟨j - 1, by omega⟩
      rw [show k + 1 + 1 = k + 2 by omega, hsum k]
      norm_num

/-- Proposition 10.1, transported to the actual complex `a` coefficients
on a dyadic block. -/
lemma sum_norm_aCoeff_sq_le (N z : ℕ) (hz : 1 ≤ z) :
    (∑ n ∈ dyadicNatBlock N, ‖((aCoeff z n : ℝ) : ℂ)‖ ^ 2) ≤
      (8 / 9 : ℝ) * (N : ℝ) * (Real.log z + 3) ^ 3 := by
  rw [show dyadicNatBlock N = Finset.Ioc N (2 * N) from rfl]
  have h := granville_ramare_prop_10_1 N z hz
  convert h using 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [aCoeff_eq_truncatedMobiusDivisorSum z n (by
    have := (Finset.mem_Ioc.mp hn).1
    omega)]
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

end ReciprocalKernel

section DyadicAssembly

variable {J : Type*} [DecidableEq J]

end DyadicAssembly

section ExplicitConstant

end ExplicitConstant

end TypeII

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/ReciprocalExpSumOneStep.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The one-step reciprocal exponential-sum bound

This file treats the middle-frequency branch of Granville--Ramaré,
Proposition 8.1.  One Weyl differencing step is followed by the concrete
Kusmin--Landau estimate for a first difference of the reciprocal phase.
-/

open scoped BigOperators

noncomputable section

private lemma finiteHarmonic_le_one_add_log_k1 (H : ℕ) :
    finiteHarmonic H ≤ 1 + Real.log H := by
  have heq : finiteHarmonic H = (harmonic H : ℝ) := by
    unfold finiteHarmonic harmonic
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [heq]
  exact harmonic_le_one_add_log H

/-- Ambient-length version of the preceding one-step inequality.  This is
the form needed for arbitrary subintervals of a fixed dyadic block. -/
theorem reciprocalExpRange_sq_le_of_terminal_ambient
    (x : ℝ) (C L M q : ℕ) (hM : 0 < M) (hq : 1 ≤ q)
    (hLM : L ≤ M) (hqM : q ≤ M)
    (K : ℝ) (_hK : 0 ≤ K)
    (hterminal : ∀ r < q,
      ‖∑ n ∈ Finset.range (L - (r + 1)),
        positiveCorrelation
          (fun j ↦ e (reciprocalPhase x (C + j))) r n‖ ≤
        K * (((r + 1 : ℕ) : ℝ))⁻¹) :
    ‖reciprocalExpRange x C L‖ ^ 2 ≤
      2 * (M : ℝ) ^ 2 / (q : ℝ) +
        4 * (M : ℝ) * K / (q : ℝ) * finiteHarmonic q := by
  have hqpos : 0 < q := by omega
  let z : ℕ → ℂ := fun j ↦ e (reciprocalPhase x (C + j))
  have hz : ∀ n < L, ‖z n‖ ≤ 1 := by
    intro n hn
    simp [z]
  have hweyl := VanDerCorput.normalized_sq_norm_sum_le_positiveCorrelations_ambient
    z L M q hM hqpos hLM hqM hz
  have hsum :
      (∑ r ∈ Finset.range q,
        ‖∑ n ∈ Finset.range (L - (r + 1)),
          positiveCorrelation z r n‖ / (M : ℝ)) ≤
        K / (M : ℝ) * finiteHarmonic q := by
    calc
      _ ≤ ∑ r ∈ Finset.range q,
          (K * (((r + 1 : ℕ) : ℝ))⁻¹) / (M : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        exact div_le_div_of_nonneg_right
          (hterminal r (Finset.mem_range.mp hr)) (by positivity)
      _ = K / (M : ℝ) * finiteHarmonic q := by
        unfold finiteHarmonic
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _hr
        ring
  have hnormalized :
      (‖reciprocalExpRange x C L‖ / (M : ℝ)) ^ 2 ≤
        2 / (q : ℝ) +
          4 / (q : ℝ) * (K / (M : ℝ) * finiteHarmonic q) := by
    rw [reciprocalExpRange]
    have hcoef : 0 ≤ 4 / (q : ℝ) := by positivity
    have hweighted := mul_le_mul_of_nonneg_left hsum hcoef
    exact hweyl.trans (add_le_add_right hweighted _)
  have hscale : 0 < (M : ℝ) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hnormalized hscale.le
  calc
    ‖reciprocalExpRange x C L‖ ^ 2 =
        (‖reciprocalExpRange x C L‖ / (M : ℝ)) ^ 2 * (M : ℝ) ^ 2 := by
      field_simp
    _ ≤ (2 / (q : ℝ) +
          4 / (q : ℝ) * (K / (M : ℝ) * finiteHarmonic q)) *
          (M : ℝ) ^ 2 := hmul
    _ = 2 * (M : ℝ) ^ 2 / (q : ℝ) +
        4 * (M : ℝ) * K / (q : ℝ) * finiteHarmonic q := by
      field_simp
/-- A first multiplicative correlation is the once-differenced reciprocal
phase used by the concrete Kusmin--Landau theorem. -/
lemma positiveCorrelation_reciprocal_eq_expPhase_onceDiff
    (x : ℝ) (C r n : ℕ) :
    positiveCorrelation (fun j ↦ e (reciprocalPhase x (C + j))) r n =
      expPhase (onceDiffReciprocal x (r + 1 : ℕ) (C + n : ℕ)) := by
  rw [expPhase_eq_e, positiveCorrelation_e]
  congr 1
  simp only [positivePhaseDifference, onceDiffReciprocal, onceDiff, reciprocalPhase]
  push_cast
  ring

/-- Concrete terminal bound for every first-order correlation, including
the ranges of length zero or one. -/
lemma terminalCorrelation_reciprocal_k1_le
    (x : ℝ) (C N q r : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hr : r < q)
    (hderiv : 4 * x * (q : ℝ) ≤ (C : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range (N - (r + 1)),
        positiveCorrelation
          (fun j ↦ e (reciprocalPhase x (C + j))) r n‖ ≤
      ((C + N : ℕ) : ℝ) ^ 3 / (2 * x) * (((r + 1 : ℕ) : ℝ))⁻¹ := by
  let L : ℕ := N - (r + 1)
  have hrq : r + 1 ≤ q := by omega
  have hrqR : ((r + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hrq
  have hupper :
      4 * x * ((r + 1 : ℕ) : ℝ) / (C : ℝ) ^ 3 ≤ 1 := by
    have hC3 : 0 < (C : ℝ) ^ 3 := by positivity
    apply (div_le_iff₀ hC3).2
    calc
      4 * x * ((r + 1 : ℕ) : ℝ) ≤ 4 * x * (q : ℝ) := by gcongr
      _ ≤ (C : ℝ) ^ 3 := hderiv
      _ = 1 * (C : ℝ) ^ 3 := by ring
  have hlarge :
      2 ≤ ((C + N : ℕ) : ℝ) ^ 3 /
        (2 * x * ((r + 1 : ℕ) : ℝ)) := by
    have hden : 0 < 2 * x * ((r + 1 : ℕ) : ℝ) := by positivity
    apply (le_div_iff₀ hden).2
    have hCN : (C : ℝ) ≤ ((C + N : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right C N)
    have hpow : (C : ℝ) ^ 3 ≤ ((C + N : ℕ) : ℝ) ^ 3 := by gcongr
    have hxr : 4 * x * ((r + 1 : ℕ) : ℝ) ≤ (C : ℝ) ^ 3 := by
      calc
        _ ≤ 4 * x * (q : ℝ) := by gcongr
        _ ≤ _ := hderiv
    nlinarith
  by_cases hL : 2 ≤ L
  · have hlength : L - 2 + 2 = L := by omega
    have hendNat : C + (L - 2 + 1) + (r + 1) ≤ C + N := by
      dsimp [L]
      omega
    have hend :
        (C : ℝ) + ((L - 2 + 1 : ℕ) : ℝ) + ((r + 1 : ℕ) : ℝ) ≤
          ((C + N : ℕ) : ℝ) := by
      exact_mod_cast hendNat
    have hKL := kusminLandau_onceDiffReciprocal
      x ((r + 1 : ℕ) : ℝ) (C : ℝ) ((C + N : ℕ) : ℝ) (L - 2)
      hx (by positivity) (by positivity) hend hupper
    calc
      ‖∑ n ∈ Finset.range (N - (r + 1)),
          positiveCorrelation
            (fun j ↦ e (reciprocalPhase x (C + j))) r n‖ =
          ‖∑ n ∈ Finset.range L,
            expPhase (onceDiffReciprocal x (r + 1 : ℕ) (C + n : ℕ))‖ := by
        dsimp [L]
        congr 1
        apply Finset.sum_congr rfl
        intro n _hn
        exact positiveCorrelation_reciprocal_eq_expPhase_onceDiff x C r n
      _ ≤ ((C + N : ℕ) : ℝ) ^ 3 /
          (2 * x * ((r + 1 : ℕ) : ℝ)) := by
        rw [← hlength]
        simpa only [Nat.cast_add] using hKL
      _ = ((C + N : ℕ) : ℝ) ^ 3 / (2 * x) *
          (((r + 1 : ℕ) : ℝ))⁻¹ := by field_simp
  · have hLtwo : L ≤ 1 := by omega
    calc
      ‖∑ n ∈ Finset.range (N - (r + 1)),
          positiveCorrelation
            (fun j ↦ e (reciprocalPhase x (C + j))) r n‖ ≤
          ∑ n ∈ Finset.range L,
            ‖positiveCorrelation
              (fun j ↦ e (reciprocalPhase x (C + j))) r n‖ := by
        dsimp [L]
        exact norm_sum_le _ _
      _ = (L : ℝ) := by simp [positiveCorrelation]
      _ ≤ 2 := by exact_mod_cast (show L ≤ 2 by omega)
      _ ≤ ((C + N : ℕ) : ℝ) ^ 3 /
          (2 * x * ((r + 1 : ℕ) : ℝ)) := hlarge
      _ = ((C + N : ℕ) : ℝ) ^ 3 / (2 * x) *
          (((r + 1 : ℕ) : ℝ))⁻¹ := by field_simp

/-- Concrete one-step estimate for a short range inside an ambient block of
length `M`. -/
theorem reciprocalExpRange_sq_le_k1_ambient
    (x : ℝ) (C L M q : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hM : 0 < M)
    (hq : 1 ≤ q) (hLM : L ≤ M) (hqM : q ≤ M)
    (hderiv : 4 * x * (q : ℝ) ≤ (C : ℝ) ^ 3) :
    ‖reciprocalExpRange x C L‖ ^ 2 ≤
      2 * (M : ℝ) ^ 2 / (q : ℝ) +
        4 * (M : ℝ) * (((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) /
          (q : ℝ) * finiteHarmonic q := by
  apply reciprocalExpRange_sq_le_of_terminal_ambient x C L M q hM hq hLM hqM
    (((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) (by positivity)
  intro r hr
  exact terminalCorrelation_reciprocal_k1_le x C L q r hx hC hr hderiv

/-! ## Selecting and eliminating the one-step shift -/

def reciprocalShiftAdmissibleK1 (x : ℝ) (C q : ℕ) : Prop :=
  4 * x * (q : ℝ) ≤ (C : ℝ) ^ 3

def reciprocalShiftK1 (x : ℝ) (C N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (reciprocalShiftAdmissibleK1 x C) N

lemma reciprocalShiftK1_le (x : ℝ) (C N : ℕ) :
    reciprocalShiftK1 x C N ≤ N := by
  classical
  exact Nat.findGreatest_le _

lemma reciprocalShiftK1_admissible (x : ℝ) (C N : ℕ) :
    reciprocalShiftAdmissibleK1 x C (reciprocalShiftK1 x C N) := by
  classical
  unfold reciprocalShiftK1
  exact Nat.findGreatest_spec (P := reciprocalShiftAdmissibleK1 x C)
    (m := 0) (n := N) (Nat.zero_le _) (by simp [reciprocalShiftAdmissibleK1])

lemma reciprocalShiftK1_pos {x : ℝ} {C N : ℕ} (hN : 0 < N)
    (hone : 4 * x ≤ (C : ℝ) ^ 3) :
    0 < reciprocalShiftK1 x C N := by
  classical
  rw [reciprocalShiftK1, Nat.findGreatest_pos]
  refine ⟨1, by omega, hN, ?_⟩
  simpa [reciprocalShiftAdmissibleK1] using hone

lemma reciprocalShiftK1_succ_not_admissible {x : ℝ} {C N : ℕ}
    (hlt : reciprocalShiftK1 x C N < N) :
    ¬ reciprocalShiftAdmissibleK1 x C (reciprocalShiftK1 x C N + 1) := by
  classical
  exact Nat.findGreatest_is_greatest (P := reciprocalShiftAdmissibleK1 x C)
    (Nat.lt_succ_self _) (Nat.succ_le_iff.mpr hlt)

lemma reciprocalShiftK1_lt_of_middle {x : ℝ} {C N : ℕ}
    (hmiddle : (C : ℝ) ^ 3 < 4 * x * (N : ℝ)) :
    reciprocalShiftK1 x C N < N := by
  have hle := reciprocalShiftK1_le x C N
  by_contra hnot
  have heq : reciprocalShiftK1 x C N = N :=
    Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
  have hadm := reciprocalShiftK1_admissible x C N
  rw [heq] at hadm
  exact (not_le_of_gt hmiddle) hadm

/-- The selected one-step shift is within a factor two of its real
threshold. -/
lemma reciprocalShiftK1_scale_bounds {x : ℝ} {C N : ℕ}
    (hx : 0 < x) (hN : 0 < N)
    (hone : 4 * x ≤ (C : ℝ) ^ 3)
    (hmiddle : (C : ℝ) ^ 3 < 4 * x * (N : ℝ)) :
    let q := reciprocalShiftK1 x C N
    1 ≤ q ∧ q ≤ N ∧
      4 * x * (q : ℝ) ≤ (C : ℝ) ^ 3 ∧
      (C : ℝ) ^ 3 < 8 * x * (q : ℝ) := by
  let q := reciprocalShiftK1 x C N
  have hq : 1 ≤ q := reciprocalShiftK1_pos hN hone
  have hlt : q < N := reciprocalShiftK1_lt_of_middle hmiddle
  have hfail := reciprocalShiftK1_succ_not_admissible hlt
  have hnext : (C : ℝ) ^ 3 < 4 * x * ((q + 1 : ℕ) : ℝ) :=
    lt_of_not_ge hfail
  have hqdoubleNat : q + 1 ≤ 2 * q := by omega
  have hqdouble : ((q + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by
    exact_mod_cast hqdoubleNat
  refine ⟨hq, reciprocalShiftK1_le x C N,
    reciprocalShiftK1_admissible x C N, ?_⟩
  calc
    (C : ℝ) ^ 3 < 4 * x * ((q + 1 : ℕ) : ℝ) := hnext
    _ ≤ 4 * x * (2 * (q : ℝ)) := by gcongr
    _ = 8 * x * (q : ℝ) := by ring

/-- Ambient q-free square estimate.  The summation length `L` may be any
prefix of the ambient dyadic length `M`. -/
theorem reciprocalExpRange_sq_le_dyadic_qfree_k1_ambient
    (x : ℝ) (C L M : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hM : 0 < M)
    (hLM : L ≤ M) (hMC : M ≤ C)
    (hone : 4 * x ≤ (C : ℝ) ^ 3)
    (hmiddle : (C : ℝ) ^ 3 < 4 * x * (M : ℝ)) :
    ‖reciprocalExpRange x C L‖ ^ 2 ≤
      528 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
        (1 + Real.log C) := by
  let q := reciprocalShiftK1 x C M
  obtain ⟨hq, hqM, hderiv, hscale⟩ :=
    reciprocalShiftK1_scale_bounds hx hM hone hmiddle
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hC3 : 0 < (C : ℝ) ^ 3 := by positivity
  have hqC : q ≤ C := hqM.trans hMC
  have hlogq : Real.log (q : ℝ) ≤ Real.log (C : ℝ) :=
    Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqC)
  have hlogC : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hH := finiteHarmonic_le_one_add_log_k1 q
  have hinvq : 1 / (q : ℝ) ≤ 8 * x / (C : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ hqpos hC3]
    nlinarith [hscale]
  have hinvM : 1 / (M : ℝ) ≤ 4 * x / (C : ℝ) ^ 3 := by
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    rw [div_le_div_iff₀ hMr hC3]
    simpa only [one_mul] using hmiddle.le
  have hLC : L ≤ C := hLM.trans hMC
  have hCL : ((C + L : ℕ) : ℝ) ≤ 2 * (C : ℝ) := by
    exact_mod_cast (show C + L ≤ 2 * C by omega)
  have hCLpow : ((C + L : ℕ) : ℝ) ^ 3 ≤ 8 * (C : ℝ) ^ 3 := by
    calc
      _ ≤ (2 * (C : ℝ)) ^ 3 := by gcongr
      _ = _ := by ring
  have hraw := reciprocalExpRange_sq_le_k1_ambient
    x C L M q hx hC hM hq hLM hqM hderiv
  have hdiag :
      2 * (M : ℝ) ^ 2 / (q : ℝ) ≤
        16 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) := by
    calc
      2 * (M : ℝ) ^ 2 / (q : ℝ) =
          2 * (M : ℝ) ^ 2 * (1 / (q : ℝ)) := by ring
      _ ≤ 2 * (M : ℝ) ^ 2 * (8 * x / (C : ℝ) ^ 3) := by gcongr
      _ = 16 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) := by ring
  have hKq :
      (((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) / (q : ℝ) ≤ 32 := by
    rw [div_le_iff₀ hqpos, div_le_iff₀ (by positivity : 0 < 2 * x)]
    nlinarith [hCLpow, hscale]
  have hMfactor :
      (M : ℝ) ≤ 4 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) := by
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hm := mul_le_mul_of_nonneg_left hinvM (show 0 ≤ (M : ℝ) ^ 2 by positivity)
    field_simp at hm ⊢
    nlinarith
  have hterminal :
      4 * (M : ℝ) * (((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) /
          (q : ℝ) * finiteHarmonic q ≤
        512 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
          (1 + Real.log C) := by
    have hlog : 0 ≤ 1 + Real.log (C : ℝ) := by positivity
    have hHnonneg := finiteHarmonic_nonneg q
    calc
      4 * (M : ℝ) * (((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) /
            (q : ℝ) * finiteHarmonic q ≤
          128 * (M : ℝ) * finiteHarmonic q := by
        calc
          _ = 4 * (M : ℝ) *
              ((((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) / (q : ℝ)) *
                finiteHarmonic q := by ring
          _ ≤ 4 * (M : ℝ) * 32 * finiteHarmonic q := by gcongr
          _ = _ := by ring
      _ ≤ 128 * (M : ℝ) * (1 + Real.log C) := by
        have hadd : 1 + Real.log (q : ℝ) ≤ 1 + Real.log (C : ℝ) := by
          linarith
        have := hH.trans hadd
        gcongr
      _ ≤ 512 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
          (1 + Real.log C) := by
        calc
          _ ≤ 128 * (4 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3)) *
              (1 + Real.log C) := by gcongr
          _ = _ := by ring
  calc
    ‖reciprocalExpRange x C L‖ ^ 2 ≤
        2 * (M : ℝ) ^ 2 / (q : ℝ) +
          4 * (M : ℝ) * (((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) /
            (q : ℝ) * finiteHarmonic q := hraw
    _ ≤ 16 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) +
        512 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
          (1 + Real.log C) := add_le_add hdiag hterminal
    _ ≤ 528 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
        (1 + Real.log C) := by
      have : 1 ≤ 1 + Real.log (C : ℝ) := by linarith
      have hbase : 0 ≤ (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) := by positivity
      nlinarith

/-- Norm form of the ambient one-step estimate. -/
theorem norm_reciprocalExpRange_le_dyadic_qfree_k1_ambient
    (x : ℝ) (C L M : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hM : 0 < M)
    (hLM : L ≤ M) (hMC : M ≤ C)
    (hone : 4 * x ≤ (C : ℝ) ^ 3)
    (hmiddle : (C : ℝ) ^ 3 < 4 * x * (M : ℝ)) :
    ‖reciprocalExpRange x C L‖ ≤
      24 * (M : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
        Real.sqrt (1 + Real.log C) := by
  have hdelta : 0 ≤ x / (C : ℝ) ^ 3 := by positivity
  have hlogC : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hLlog : 0 ≤ 1 + Real.log (C : ℝ) := by positivity
  apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity)
  calc
    ‖reciprocalExpRange x C L‖ ^ 2 ≤
        528 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
          (1 + Real.log C) :=
      reciprocalExpRange_sq_le_dyadic_qfree_k1_ambient
        x C L M hx hC hM hLM hMC hone hmiddle
    _ ≤ (24 * (M : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
          Real.sqrt (1 + Real.log C)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hdelta, Real.sq_sqrt hLlog]
      have hprod : 0 ≤ (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
          (1 + Real.log (C : ℝ)) := by positivity
      norm_num
      nlinarith

/-- Natural-Ioc middle-frequency estimate.  The ambient length is the left
endpoint scale `A+1`, so the result is uniform over all prefixes of the
dyadic interval. -/
theorem norm_reciprocalExpSum_le_dyadic_qfree_k1
    (x : ℝ) (A B : ℕ) (hx : 0 < x) (hAB : A ≤ B)
    (hdyadic : B - A ≤ A + 1)
    (hone : 4 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 3)
    (hmiddle : ((A + 1 : ℕ) : ℝ) ^ 3 <
      4 * x * ((A + 1 : ℕ) : ℝ)) :
    ‖reciprocalExpSum x A B‖ ≤
      24 * ((A + 1 : ℕ) : ℝ) *
        Real.sqrt (x / ((A + 1 : ℕ) : ℝ) ^ 3) *
        Real.sqrt (1 + Real.log ((A + 1 : ℕ) : ℝ)) := by
  rw [reciprocalExpSum_eq_range x A B hAB]
  exact norm_reciprocalExpRange_le_dyadic_qfree_k1_ambient
    x (A + 1) (B - A) (A + 1) hx (by omega) (by omega)
    hdyadic (by rfl) hone hmiddle

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/TypeIINearFar.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Near--far splitting for Type II reciprocal sums

This file supplies the finite combinatorics used in Granville--Ramaré's
Type II estimate.  Pairs of second variables within a prescribed integer
distance are estimated trivially, while the remaining Gram correlations
may be bounded by a reciprocal exponential-sum estimate.
-/

open scoped BigOperators

namespace TypeII

/-- The elements of `s` at integer distance at most `T` from `v`. -/
def nearNeighbors (s : Finset ℕ) (T v : ℕ) : Finset ℕ :=
  s.filter fun w ↦ Nat.dist v w ≤ T

@[simp] lemma mem_nearNeighbors {s : Finset ℕ} {T v w : ℕ} :
    w ∈ nearNeighbors s T v ↔ w ∈ s ∧ Nat.dist v w ≤ T := by
  simp [nearNeighbors]

/-- An integer interval contains at most `2T+1` integers at distance at
most `T` from any fixed integer. -/
lemma card_nearNeighbors_le (s : Finset ℕ) (T v : ℕ) :
    (nearNeighbors s T v).card ≤ 2 * T + 1 := by
  have hsub : nearNeighbors s T v ⊆ Finset.Icc (v - T) (v + T) := by
    intro w hw
    have hd := (mem_nearNeighbors.mp hw).2
    by_cases hvw : v ≤ w
    · rw [Nat.dist_eq_sub_of_le hvw] at hd
      simp only [Finset.mem_Icc]
      omega
    · have hwv : w ≤ v := Nat.le_of_not_ge hvw
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hwv] at hd
      simp only [Finset.mem_Icc]
      omega
  calc
    (nearNeighbors s T v).card ≤ (Finset.Icc (v - T) (v + T)).card :=
      Finset.card_le_card hsub
    _ = v + T + 1 - (v - T) := by simp
    _ ≤ 2 * T + 1 := by omega

/-- A concrete near--far Gram estimate.  Near correlations cost `D`, but
there are at most `2T+1` near neighbors of each second variable.  Far
correlations cost `Q`.  The factor `2` in the near term comes from the
elementary inequality `ab ≤ a²+b²`; it is harmless for the application.
-/
lemma reciprocalInnerBound_of_natDist_near_far
    (uSupport vSupport : Finset ℕ)
    (beta : ℕ → ℂ) (kernel : ℕ → ℕ → ℂ)
    (T : ℕ) (D Q : ℝ)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hnear : ∀ v ∈ vSupport, ∀ w ∈ vSupport,
      Nat.dist v w ≤ T →
        ‖kernelCorrelation uSupport kernel v w‖ ≤ D)
    (hfar : ∀ v ∈ vSupport, ∀ w ∈ vSupport,
      T < Nat.dist v w →
        ‖kernelCorrelation uSupport kernel v w‖ ≤ Q) :
    ReciprocalInnerBound uSupport vSupport beta kernel
      (2 * D * (2 * T + 1) + Q * (vSupport.card : ℝ)) := by
  classical
  let a : ℕ → ℝ := fun v ↦ ‖beta v‖
  let S : ℝ := ∑ v ∈ vSupport, a v ^ 2
  let L : ℝ := ∑ v ∈ vSupport, ∑ w ∈ vSupport,
    if Nat.dist v w ≤ T then a v ^ 2 else 0
  let R : ℝ := ∑ v ∈ vSupport, ∑ w ∈ vSupport,
    if Nat.dist v w ≤ T then a w ^ 2 else 0
  have hleft : L ≤ (2 * T + 1 : ℕ) * S := by
    dsimp only [L, S]
    calc
      (∑ v ∈ vSupport, ∑ w ∈ vSupport,
          if Nat.dist v w ≤ T then a v ^ 2 else 0) =
          ∑ v ∈ vSupport,
            ((nearNeighbors vSupport T v).card : ℝ) * a v ^ 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [← Finset.sum_filter]
        simp [nearNeighbors]
      _ ≤ ∑ v ∈ vSupport, ((2 * T + 1 : ℕ) : ℝ) * a v ^ 2 := by
        apply Finset.sum_le_sum
        intro v hv
        gcongr
        exact_mod_cast card_nearNeighbors_le vSupport T v
      _ = ((2 * T + 1 : ℕ) : ℝ) *
          ∑ v ∈ vSupport, a v ^ 2 := by rw [Finset.mul_sum]
  have hright : R ≤ (2 * T + 1 : ℕ) * S := by
    have hRL : R = L := by
      dsimp only [R, L]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      rw [Nat.dist_comm]
    rw [hRL]
    exact hleft
  have hnearMass :
      (∑ v ∈ vSupport, ∑ w ∈ vSupport,
        if Nat.dist v w ≤ T then (a v ^ 2 + a w ^ 2) else 0) ≤
        2 * ((2 * T + 1 : ℕ) : ℝ) * S := by
    have hsplit :
        (∑ v ∈ vSupport, ∑ w ∈ vSupport,
          if Nat.dist v w ≤ T then (a v ^ 2 + a w ^ 2) else 0) = L + R := by
      dsimp only [L, R]
      simp only [ite_add_zero, Finset.sum_add_distrib]
    rw [hsplit]
    nlinarith
  have hmass :
      (∑ v ∈ vSupport, ∑ w ∈ vSupport, a v * a w) ≤
        (vSupport.card : ℝ) * S := by
    have hcs :
        (∑ v ∈ vSupport, a v) ^ 2 ≤
          (vSupport.card : ℝ) * S := by
      dsimp only [S]
      simpa using (Finset.sum_mul_sq_le_sq_mul_sq vSupport
        (fun _v ↦ (1 : ℝ)) a)
    calc
      (∑ v ∈ vSupport, ∑ w ∈ vSupport, a v * a w) =
          (∑ v ∈ vSupport, a v) ^ 2 := by
        rw [pow_two, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.mul_sum]
      _ ≤ (vSupport.card : ℝ) * S := hcs
  have hpair (v : ℕ) (hv : v ∈ vSupport)
      (w : ℕ) (hw : w ∈ vSupport) :
      a v * a w * ‖kernelCorrelation uSupport kernel v w‖ ≤
        D * (if Nat.dist v w ≤ T then (a v ^ 2 + a w ^ 2) else 0) +
          Q * (a v * a w) := by
    by_cases hn : Nat.dist v w ≤ T
    · rw [if_pos hn]
      have hab : a v * a w ≤ a v ^ 2 + a w ^ 2 := by
        dsimp only [a]
        nlinarith [sq_nonneg (‖beta v‖ - ‖beta w‖)]
      calc
        a v * a w * ‖kernelCorrelation uSupport kernel v w‖ ≤
            a v * a w * D := by
          exact mul_le_mul_of_nonneg_left (hnear v hv w hw hn)
            (mul_nonneg (by dsimp only [a]; positivity)
              (by dsimp only [a]; positivity))
        _ ≤ D * (a v ^ 2 + a w ^ 2) := by
          rw [mul_comm (a v * a w) D]
          exact mul_le_mul_of_nonneg_left hab hD
        _ ≤ D * (a v ^ 2 + a w ^ 2) + Q * (a v * a w) := by
          exact le_add_of_nonneg_right
            (mul_nonneg hQ (mul_nonneg
              (by dsimp only [a]; positivity) (by dsimp only [a]; positivity)))
    · simp only [if_neg hn, mul_zero, zero_add]
      have hdist : T < Nat.dist v w := Nat.lt_of_not_ge hn
      calc
        a v * a w * ‖kernelCorrelation uSupport kernel v w‖ ≤
            a v * a w * Q := by
          exact mul_le_mul_of_nonneg_left (hfar v hv w hw hdist)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = Q * (a v * a w) := by ring
  unfold ReciprocalInnerBound
  calc
    (∑ u ∈ uSupport, ‖innerSum vSupport beta kernel u‖ ^ 2) ≤
        ∑ v ∈ vSupport, ∑ w ∈ vSupport,
          a v * a w * ‖kernelCorrelation uSupport kernel v w‖ :=
      innerSum_meanSquare_le_sum_norm_correlation
        uSupport vSupport beta kernel
    _ ≤ ∑ v ∈ vSupport, ∑ w ∈ vSupport,
        (D * (if Nat.dist v w ≤ T then (a v ^ 2 + a w ^ 2) else 0) +
          Q * (a v * a w)) := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro w hw
      exact hpair v hv w hw
    _ = D * (∑ v ∈ vSupport, ∑ w ∈ vSupport,
          if Nat.dist v w ≤ T then (a v ^ 2 + a w ^ 2) else 0) +
        Q * (∑ v ∈ vSupport, ∑ w ∈ vSupport, a v * a w) := by
      simp only [Finset.sum_add_distrib]
      simp only [Finset.mul_sum]
    _ ≤ D * (2 * ((2 * T + 1 : ℕ) : ℝ) * S) +
        Q * ((vSupport.card : ℝ) * S) := by gcongr
    _ = (2 * D * (2 * T + 1) + Q * (vSupport.card : ℝ)) *
        ∑ v ∈ vSupport, ‖beta v‖ ^ 2 := by
      dsimp only [S, a]
      push_cast
      ring

/-- Unsquared bilinear consequence of the concrete near--far split. -/
lemma norm_bilinearSum_le_natDist_near_far
    (uSupport vSupport : Finset ℕ)
    (alpha beta : ℕ → ℂ) (kernel : ℕ → ℕ → ℂ)
    (T : ℕ) (D Q : ℝ)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hnear : ∀ v ∈ vSupport, ∀ w ∈ vSupport,
      Nat.dist v w ≤ T →
        ‖kernelCorrelation uSupport kernel v w‖ ≤ D)
    (hfar : ∀ v ∈ vSupport, ∀ w ∈ vSupport,
      T < Nat.dist v w →
        ‖kernelCorrelation uSupport kernel v w‖ ≤ Q) :
    ‖bilinearSum uSupport vSupport alpha beta kernel‖ ≤
      l2Norm uSupport alpha *
        Real.sqrt (2 * D * (2 * T + 1) + Q * (vSupport.card : ℝ)) *
          l2Norm vSupport beta := by
  apply norm_bilinearSum_le_of_reciprocalInnerBound
  · positivity
  · exact reciprocalInnerBound_of_natDist_near_far
      uSupport vSupport beta kernel T D Q hD hQ hnear hfar

/-! ## Restricted reciprocal kernels -/

/-- The completely trivial correlation estimate for the restricted
reciprocal kernel. -/
lemma norm_kernelCorrelation_restrictedReciprocalKernel_le_card
    (I uSupport : Finset ℕ) (x : ℝ) (v w : ℕ) :
    ‖kernelCorrelation uSupport (restrictedReciprocalKernel I x) v w‖ ≤
      (uSupport.card : ℝ) := by
  calc
    ‖kernelCorrelation uSupport (restrictedReciprocalKernel I x) v w‖ ≤
        ∑ _u ∈ uSupport, (1 : ℝ) := by
      unfold kernelCorrelation
      calc
        ‖∑ u ∈ uSupport,
            (starRingEnd ℂ) (restrictedReciprocalKernel I x u v) *
              restrictedReciprocalKernel I x u w‖ ≤
            ∑ u ∈ uSupport,
              ‖(starRingEnd ℂ) (restrictedReciprocalKernel I x u v) *
                restrictedReciprocalKernel I x u w‖ := norm_sum_le _ _
        _ ≤ ∑ _u ∈ uSupport, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro u hu
          rw [norm_mul]
          change ‖star (restrictedReciprocalKernel I x u v)‖ *
              ‖restrictedReciprocalKernel I x u w‖ ≤ 1
          rw [norm_star]
          have hv := norm_restrictedReciprocalKernel_le_one I x u v
          have hw := norm_restrictedReciprocalKernel_le_one I x u w
          nlinarith [norm_nonneg (restrictedReciprocalKernel I x u v),
            norm_nonneg (restrictedReciprocalKernel I x u w)]
    _ = (uSupport.card : ℝ) := by simp

/-! ### A premise-free finite majorant -/

/-- The lower endpoint of a product-restricted Gram correlation. -/
def correlationLower (y A v w : ℕ) : ℕ :=
  max A (max (y / v) (y / w))

/-- The upper endpoint of a product-restricted Gram correlation. -/
def correlationUpper (y' B v w : ℕ) : ℕ :=
  min B (min (y' / v) (y' / w))

/-- A completely explicit bound for one far correlation.  In the frequency
range covered by one of the three analytic branches it selects exactly one
branch; outside those ranges it falls back to the trivial interval length.
In particular, inactive `k = 1` and `k = 2` terms are not added. -/
noncomputable def selectedReciprocalBound (x : ℝ) (A B : ℕ) : ℝ :=
  let C : ℕ := A + 1
  if x / (C : ℝ) ^ 2 ≤ 1 / 2 then
    ((B + 1 : ℕ) : ℝ) ^ 2 / x
  else if 12 * x ≤ (C : ℝ) ^ 4 ∧
      (C : ℝ) ^ 4 <
        12 * x * (Nat.sqrt (B - A) : ℝ) ^ 3 then
    128 * ((B - A : ℕ) : ℝ) *
      (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log (C : ℝ))
  else if 4 * x ≤ (C : ℝ) ^ 3 then
    24 * (C : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
      Real.sqrt (1 + Real.log (C : ℝ))
  else
    (B - A : ℕ)

/-- The direct-frequency branch of `selectedReciprocalBound`. -/
lemma selectedReciprocalBound_eq_direct
    (x : ℝ) (A B : ℕ)
    (h : x / ((A + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 2) :
    selectedReciprocalBound x A B = ((B + 1 : ℕ) : ℝ) ^ 2 / x := by
  simp only [selectedReciprocalBound, if_pos h]

/-- The one-step branch of `selectedReciprocalBound`. -/
lemma selectedReciprocalBound_eq_k1
    (x : ℝ) (A B : ℕ)
    (hdirect : ¬ x / ((A + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 2)
    (hk2 : ¬ (12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4 ∧
      ((A + 1 : ℕ) : ℝ) ^ 4 <
        12 * x * (Nat.sqrt (B - A) : ℝ) ^ 3))
    (hk1 : 4 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 3) :
    selectedReciprocalBound x A B =
      24 * (((A + 1 : ℕ) : ℝ)) *
        Real.sqrt (x / (((A + 1 : ℕ) : ℝ)) ^ 3) *
          Real.sqrt (1 + Real.log (((A + 1 : ℕ) : ℝ))) := by
  simp only [selectedReciprocalBound, if_neg hdirect, if_neg hk2, if_pos hk1]

/-- The two-step branch of `selectedReciprocalBound`. -/
lemma selectedReciprocalBound_eq_k2
    (x : ℝ) (A B : ℕ)
    (hdirect : ¬ x / ((A + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 2)
    (hk2 : 12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4 ∧
      ((A + 1 : ℕ) : ℝ) ^ 4 <
        12 * x * (Nat.sqrt (B - A) : ℝ) ^ 3) :
    selectedReciprocalBound x A B =
      128 * ((B - A : ℕ) : ℝ) *
        (x / (((A + 1 : ℕ) : ℝ)) ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt (1 + Real.log (((A + 1 : ℕ) : ℝ))) := by
  simp only [selectedReciprocalBound, if_neg hdirect, if_pos hk2]

/-- The selected bound controls every nonempty dyadic reciprocal interval.
The proof performs the same direct/one-step/two-step split encoded in the
definition, and uses the trivial estimate only in the residual branch. -/
lemma norm_reciprocalExpSum_le_selected
    (x : ℝ) (A B : ℕ) (hx : 0 < x) (hAB : A < B)
    (hdyadic : B - A ≤ A + 1) :
    ‖reciprocalExpSum x A B‖ ≤ selectedReciprocalBound x A B := by
  let C : ℕ := A + 1
  have hC : 0 < C := by omega
  by_cases hdirect : x / (C : ℝ) ^ 2 ≤ 1 / 2
  · have h := norm_reciprocalExpSum_le_firstDerivative
      x A B hx hAB.le (by simpa only [C] using hdirect)
    simpa only [selectedReciprocalBound, C, if_pos hdirect] using h
  · have hC2 : (C : ℝ) ^ 2 < 2 * x := by
      have hC2pos : 0 < (C : ℝ) ^ 2 := by positivity
      have hlt : 1 / 2 < x / (C : ℝ) ^ 2 := lt_of_not_ge hdirect
      rw [lt_div_iff₀ hC2pos] at hlt
      nlinarith
    have hmiddle : (C : ℝ) ^ 3 < 4 * x * (C : ℝ) := by
      have hCr : 0 < (C : ℝ) := by positivity
      nlinarith [mul_lt_mul_of_pos_right hC2 hCr]
    by_cases hk2 : 12 * x ≤ (C : ℝ) ^ 4 ∧
        (C : ℝ) ^ 4 <
          12 * x * (Nat.sqrt (B - A) : ℝ) ^ 3
    · have h := norm_reciprocalExpSum_le_dyadic_qfree
        x A B hx hAB.le hAB hdyadic
          (by simpa only [C] using hk2.1) (by simpa only [C] using hk2.2)
      simp only [selectedReciprocalBound, C, if_neg hdirect, if_pos hk2]
      exact h
    · by_cases hk1 : 4 * x ≤ (C : ℝ) ^ 3
      · have h := norm_reciprocalExpSum_le_dyadic_qfree_k1
          x A B hx hAB.le hdyadic (by simpa only [C] using hk1)
            (by simpa only [C] using hmiddle)
        simp only [selectedReciprocalBound, C, if_neg hdirect, if_neg hk2,
          if_pos hk1]
        exact h
      · have h := norm_reciprocalExpSum_le x A B
        simpa only [selectedReciprocalBound, C, if_neg hdirect, if_neg hk2,
          if_neg hk1] using h

/-- The effective pointwise majorant is the better of the selected analytic
estimate and the trivial interval-length estimate.  This minimum is crucial
when the two-step high-frequency condition fails: the correlation interval
is then short even if the one-step formula itself is comparatively large. -/
noncomputable def effectiveReciprocalBound (x : ℝ) (A B : ℕ) : ℝ :=
  min (selectedReciprocalBound x A B) (B - A : ℕ)

/-- Every nonempty dyadic reciprocal interval is bounded by the effective
minimum of the analytic and trivial estimates. -/
lemma norm_reciprocalExpSum_le_effective
    (x : ℝ) (A B : ℕ) (hx : 0 < x) (hAB : A < B)
    (hdyadic : B - A ≤ A + 1) :
    ‖reciprocalExpSum x A B‖ ≤ effectiveReciprocalBound x A B := by
  unfold effectiveReciprocalBound
  apply le_min
  · exact norm_reciprocalExpSum_le_selected x A B hx hAB hdyadic
  · exact norm_reciprocalExpSum_le x A B

/-- The effective majorant is nonnegative at positive frequency. -/
lemma effectiveReciprocalBound_nonneg
    (x : ℝ) (A B : ℕ) (hx : 0 < x) :
    0 ≤ effectiveReciprocalBound x A B := by
  unfold effectiveReciprocalBound selectedReciprocalBound
  dsimp only
  split_ifs <;> positivity

/-- Interpolation in the middle/high-failure range.  Write `C=A+1`,
`N=B-A`, and `L=1+log C`.  If the direct branch fails, the two-step upper
condition holds, but its lower-frequency condition fails, then taking the
minimum with the trivial length bound gives the uniform seventh-power
estimate `q⁷ ≤ 147456 C⁶ L²`.  This covers both the one-step branch and
the final trivial branch. -/
lemma effectiveReciprocalBound_seventh_le_of_high_fail
    (t : ℝ) (A B : ℕ) (ht : 0 < t) (hAB : A < B)
    (hdyadic : B - A ≤ A + 1)
    (hdirect : ¬ t / (((A + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / 2)
    (hhone : 12 * t ≤ (((A + 1 : ℕ) : ℝ)) ^ 4)
    (hhigh : ¬ (((A + 1 : ℕ) : ℝ)) ^ 4 <
      12 * t * (Nat.sqrt (B - A) : ℝ) ^ 3) :
    effectiveReciprocalBound t A B ^ 7 ≤
      147456 * (((A + 1 : ℕ) : ℝ)) ^ 6 *
        (1 + Real.log (((A + 1 : ℕ) : ℝ))) ^ 2 := by
  let C : ℕ := A + 1
  let N : ℕ := B - A
  let s : ℕ := Nat.sqrt N
  let L : ℝ := 1 + Real.log (C : ℝ)
  let q : ℝ := effectiveReciprocalBound t A B
  have hC : 0 < C := by omega
  have hN : 0 < N := by dsimp only [N]; omega
  have hq0 : 0 ≤ q := effectiveReciprocalBound_nonneg t A B ht
  have hqN : q ≤ (N : ℝ) := by
    dsimp only [q, effectiveReciprocalBound, N]
    exact min_le_right _ _
  have hLone : 1 ≤ L := by
    dsimp only [L]
    have hlog : 0 ≤ Real.log (C : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ C by omega)
    linarith
  have hL0 : 0 ≤ L := hLone.trans' (by norm_num)
  have hhighFails : 12 * t * (s : ℝ) ^ 3 ≤ (C : ℝ) ^ 4 := by
    have hh : 12 * t * (Nat.sqrt (B - A) : ℝ) ^ 3 ≤
        (((A + 1 : ℕ) : ℝ)) ^ 4 := le_of_not_gt hhigh
    simpa only [C, N, s] using hh
  have hk2 : ¬ (12 * t ≤ (C : ℝ) ^ 4 ∧
      (C : ℝ) ^ 4 < 12 * t * (s : ℝ) ^ 3) := by
    push_neg
    intro _
    exact hhighFails
  by_cases hk1 : 4 * t ≤ (C : ℝ) ^ 3
  · have hqSelected : q ≤ selectedReciprocalBound t A B := by
      dsimp only [q, effectiveReciprocalBound]
      exact min_le_left _ _
    have hqFormula : q ≤
        24 * (C : ℝ) * Real.sqrt (t / (C : ℝ) ^ 3) * Real.sqrt L := by
      rw [selectedReciprocalBound_eq_k1 t A B
        (by simpa only [C] using hdirect)
        (by simpa only [C, N, s] using hk2)
        (by simpa only [C] using hk1)] at hqSelected
      simpa only [C, L] using hqSelected
    have hinterp := effective_k1_highFailure_seventh_le
      C N t L q hC hN ht.le hL0 hq0 hqN hqFormula hhighFails
    simpa only [q, C, L] using hinterp
  · have hmiddle : (C : ℝ) ^ 3 < 4 * t := lt_of_not_ge hk1
    have hN4 : N ^ 4 ≤ 256 * C ^ 3 :=
      residual_interval_length_fourth_le C N t hC hN hmiddle hhighFails
    have hq7N : q ^ 7 ≤ (N : ℝ) ^ 7 := pow_le_pow_left₀ hq0 hqN 7
    have hNleC : N ≤ C := by simpa only [N, C] using hdyadic
    have hpoly : N ^ 7 ≤ 256 * C ^ 6 := by
      calc
        N ^ 7 = N ^ 3 * N ^ 4 := by ring
        _ ≤ C ^ 3 * (256 * C ^ 3) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hNleC 3) hN4
        _ = 256 * C ^ 6 := by ring
    calc
      q ^ 7 ≤ (N : ℝ) ^ 7 := hq7N
      _ ≤ 256 * (C : ℝ) ^ 6 := by exact_mod_cast hpoly
      _ ≤ 147456 * (C : ℝ) ^ 6 * L ^ 2 := by
        have hLsq : 1 ≤ L ^ 2 := by nlinarith
        nlinarith [sq_nonneg ((C : ℝ) ^ 3)]
      _ = 147456 * (((A + 1 : ℕ) : ℝ)) ^ 6 *
          (1 + Real.log (((A + 1 : ℕ) : ℝ))) ^ 2 := by rfl

/-- Effective-bound eliminator in the direct branch. -/
lemma effectiveReciprocalBound_le_direct
    (t : ℝ) (A B : ℕ)
    (hdirect : t / (((A + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / 2) :
    effectiveReciprocalBound t A B ≤ ((B + 1 : ℕ) : ℝ) ^ 2 / t := by
  calc
    effectiveReciprocalBound t A B ≤ selectedReciprocalBound t A B := by
      exact min_le_left _ _
    _ = ((B + 1 : ℕ) : ℝ) ^ 2 / t :=
      selectedReciprocalBound_eq_direct t A B hdirect

/-- Effective-bound eliminator in the two-step branch. -/
lemma effectiveReciprocalBound_le_k2
    (t : ℝ) (A B : ℕ)
    (hdirect : ¬ t / (((A + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / 2)
    (hk2 : 12 * t ≤ (((A + 1 : ℕ) : ℝ)) ^ 4 ∧
      (((A + 1 : ℕ) : ℝ)) ^ 4 <
        12 * t * (Nat.sqrt (B - A) : ℝ) ^ 3) :
    effectiveReciprocalBound t A B ≤
      128 * ((B - A : ℕ) : ℝ) *
        (t / (((A + 1 : ℕ) : ℝ)) ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt (1 + Real.log (((A + 1 : ℕ) : ℝ))) := by
  calc
    effectiveReciprocalBound t A B ≤ selectedReciprocalBound t A B := by
      exact min_le_left _ _
    _ = _ := selectedReciprocalBound_eq_k2 t A B hdirect hk2

/-- Complete branch trichotomy for the effective reciprocal majorant.
Under the two-step upper condition, every nonempty dyadic interval is
controlled either by the direct formula, by the k2 formula, or by the
seventh-power interpolation bound. -/
lemma effectiveReciprocalBound_direct_or_k2_or_seventh
    (t : ℝ) (A B : ℕ) (ht : 0 < t) (hAB : A < B)
    (hdyadic : B - A ≤ A + 1)
    (hhone : 12 * t ≤ (((A + 1 : ℕ) : ℝ)) ^ 4) :
    effectiveReciprocalBound t A B ≤ ((B + 1 : ℕ) : ℝ) ^ 2 / t ∨
      effectiveReciprocalBound t A B ≤
        128 * ((B - A : ℕ) : ℝ) *
          (t / (((A + 1 : ℕ) : ℝ)) ^ 4) ^ (1 / 6 : ℝ) *
            Real.sqrt (1 + Real.log (((A + 1 : ℕ) : ℝ))) ∨
      effectiveReciprocalBound t A B ^ 7 ≤
        147456 * (((A + 1 : ℕ) : ℝ)) ^ 6 *
          (1 + Real.log (((A + 1 : ℕ) : ℝ))) ^ 2 := by
  by_cases hdirect : t / (((A + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / 2
  · exact Or.inl (effectiveReciprocalBound_le_direct t A B hdirect)
  · by_cases hhigh : (((A + 1 : ℕ) : ℝ)) ^ 4 <
        12 * t * (Nat.sqrt (B - A) : ℝ) ^ 3
    · exact Or.inr <| Or.inl <|
        effectiveReciprocalBound_le_k2 t A B hdirect ⟨hhone, hhigh⟩
    · exact Or.inr <| Or.inr <|
        effectiveReciprocalBound_seventh_le_of_high_fail
          t A B ht hAB hdyadic hdirect hhone hhigh

/-! ### Elementary dyadic phase and endpoint bounds -/

/-- Exact absolute reciprocal-difference formula in terms of natural
distance. -/
lemma abs_one_div_sub_one_div_eq_dist_div
    (v w : ℕ) (hv : 0 < v) (hw : 0 < w) :
    |1 / (w : ℝ) - 1 / (v : ℝ)| =
      (Nat.dist v w : ℝ) / ((v : ℝ) * (w : ℝ)) := by
  by_cases hvw : v ≤ w
  · have hinv : 1 / (w : ℝ) ≤ 1 / (v : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hvw)
    rw [abs_of_nonpos (sub_nonpos.mpr hinv), Nat.dist_eq_sub_of_le hvw,
      Nat.cast_sub hvw]
    field_simp <;> ring
  · have hwv : w ≤ v := Nat.le_of_not_ge hvw
    have hinv : 1 / (v : ℝ) ≤ 1 / (w : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hwv)
    rw [abs_of_nonneg (sub_nonneg.mpr hinv), Nat.dist_comm,
      Nat.dist_eq_sub_of_le hwv, Nat.cast_sub hwv]
    field_simp <;> ring

/-- On the power block `V ≤ v,w < 2V`, written as the shifted interval
`(V-1,2V-1]`, a nonzero reciprocal phase difference has the uniform lower
bound used for the direct branch. -/
lemma dyadic_reciprocalPhaseDifference_lower
    (x : ℝ) (V v w : ℕ) (hx : 0 < x) (hV : 0 < V)
    (hv : v ∈ Finset.Ioc (V - 1) (2 * V - 1))
    (hw : w ∈ Finset.Ioc (V - 1) (2 * V - 1))
    (hvw : v ≠ w) :
    x / (4 * (V : ℝ) ^ 2) ≤
      |x * (1 / (w : ℝ) - 1 / (v : ℝ))| := by
  have hvI := Finset.mem_Ioc.mp hv
  have hwI := Finset.mem_Ioc.mp hw
  have hvpos : 0 < v := by omega
  have hwpos : 0 < w := by omega
  have hdist : 1 ≤ Nat.dist v w := by
    unfold Nat.dist
    omega
  have hden : (v : ℝ) * (w : ℝ) ≤
      (2 * (V : ℝ)) * (2 * (V : ℝ)) := by
    have hvR : (v : ℝ) ≤ 2 * (V : ℝ) := by
      exact_mod_cast (show v ≤ 2 * V by omega)
    have hwR : (w : ℝ) ≤ 2 * (V : ℝ) := by
      exact_mod_cast (show w ≤ 2 * V by omega)
    exact mul_le_mul hvR hwR (by positivity) (by positivity)
  have hratio : 1 / (4 * (V : ℝ) ^ 2) ≤
      (Nat.dist v w : ℝ) / ((v : ℝ) * (w : ℝ)) := by
    have hnum : (1 : ℝ) ≤ Nat.dist v w := by exact_mod_cast hdist
    have hdenpos : 0 < (v : ℝ) * (w : ℝ) := by positivity
    have hfourpos : 0 < 4 * (V : ℝ) ^ 2 := by positivity
    rw [div_le_div_iff₀ hfourpos hdenpos]
    nlinarith
  rw [abs_mul, abs_of_pos hx,
    abs_one_div_sub_one_div_eq_dist_div v w hvpos hwpos]
  calc
    x / (4 * (V : ℝ) ^ 2) =
        x * (1 / (4 * (V : ℝ) ^ 2)) := by ring
    _ ≤ x * ((Nat.dist v w : ℝ) / ((v : ℝ) * (w : ℝ))) :=
      mul_le_mul_of_nonneg_left hratio hx.le

/-- On the same dyadic block, every reciprocal phase difference is at most
`x/V`. -/
lemma dyadic_reciprocalPhaseDifference_upper
    (x : ℝ) (V v w : ℕ) (hx : 0 < x) (hV : 0 < V)
    (hv : v ∈ Finset.Ioc (V - 1) (2 * V - 1))
    (hw : w ∈ Finset.Ioc (V - 1) (2 * V - 1)) :
    |x * (1 / (w : ℝ) - 1 / (v : ℝ))| ≤ x / (V : ℝ) := by
  have hvI := Finset.mem_Ioc.mp hv
  have hwI := Finset.mem_Ioc.mp hw
  have hvpos : 0 < v := by omega
  have hwpos : 0 < w := by omega
  have hdist : Nat.dist v w ≤ V := by
    unfold Nat.dist
    omega
  have hden : (V : ℝ) * (V : ℝ) ≤ (v : ℝ) * (w : ℝ) := by
    have hvR : (V : ℝ) ≤ v := by
      exact_mod_cast (show V ≤ v by omega)
    have hwR : (V : ℝ) ≤ w := by
      exact_mod_cast (show V ≤ w by omega)
    exact mul_le_mul hvR hwR (by positivity) (by positivity)
  have hratio : (Nat.dist v w : ℝ) / ((v : ℝ) * (w : ℝ)) ≤
      1 / (V : ℝ) := by
    have hnum : (Nat.dist v w : ℝ) ≤ V := by exact_mod_cast hdist
    have hdenpos : 0 < (v : ℝ) * (w : ℝ) := by positivity
    have hVpos : 0 < (V : ℝ) := by positivity
    rw [div_le_div_iff₀ hdenpos hVpos]
    nlinarith
  rw [abs_mul, abs_of_pos hx,
    abs_one_div_sub_one_div_eq_dist_div v w hvpos hwpos]
  calc
    x * ((Nat.dist v w : ℝ) / ((v : ℝ) * (w : ℝ))) ≤
        x * (1 / (V : ℝ)) := mul_le_mul_of_nonneg_left hratio hx.le
    _ = x / (V : ℝ) := by ring

/-- The lower correlation endpoint for a power block satisfies
`U ≤ C+1`. -/
lemma correlationLower_powerBlock_add_one_ge
    (y U v w : ℕ) (hU : 0 < U) :
    U ≤ correlationLower y (U - 1) v w + 1 := by
  have h := le_max_left (U - 1) (max (y / v) (y / w))
  unfold correlationLower
  omega

/-- The upper correlation endpoint for a power block satisfies
`E+1 ≤ 2U`. -/
lemma correlationUpper_powerBlock_add_one_le
    (y' U v w : ℕ) (hU : 0 < U) :
    correlationUpper y' (2 * U - 1) v w + 1 ≤ 2 * U := by
  have h := min_le_left (2 * U - 1) (min (y' / v) (y' / w))
  unfold correlationUpper
  omega

/-- Every nonempty correlation interval cut out of a power block has length
at most `U`. -/
lemma correlationEndpoints_powerBlock_length_le
    (y y' U v w : ℕ) (hU : 0 < U) :
    correlationUpper y' (2 * U - 1) v w -
        correlationLower y (U - 1) v w ≤ U := by
  have hC := correlationLower_powerBlock_add_one_ge y U v w hU
  have hE := correlationUpper_powerBlock_add_one_le y' U v w hU
  omega

/-- On a nonempty correlation interval, its shifted lower endpoint is at
most the upper edge `2U`; consequently its logarithm is at most
`log(2U)`. -/
lemma log_correlationLower_powerBlock_add_one_le
    (y y' U v w : ℕ) (hU : 0 < U)
    (hCE : correlationLower y (U - 1) v w <
      correlationUpper y' (2 * U - 1) v w) :
    Real.log ((correlationLower y (U - 1) v w + 1 : ℕ) : ℝ) ≤
      Real.log ((2 * U : ℕ) : ℝ) := by
  have hE := correlationUpper_powerBlock_add_one_le y' U v w hU
  have hnat : correlationLower y (U - 1) v w + 1 ≤ 2 * U := by omega
  apply Real.log_le_log
  · positivity
  · exact_mod_cast hnat

/-- Closed T=0 far-correlation majorant for an oriented pair of power
blocks.  The three summands are respectively the direct, two-step, and
interpolated high-failure bounds. -/
noncomputable def orientedPowerBlockFarQ (x : ℝ) (U V : ℕ) : ℝ :=
  16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x +
    128 * (U : ℝ) *
      (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log (2 * (U : ℝ))) +
    128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
      (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ)

noncomputable def farCorrelationMajorant
    (x : ℝ) (y y' A B v w : ℕ) : ℝ :=
  let C := correlationLower y A v w
  let E := correlationUpper y' B v w
  let t := |x * (1 / (w : ℝ) - 1 / (v : ℝ))|
  if C < E then effectiveReciprocalBound t C E else 0

/-- Every nonzero-distance correlation of two oriented power blocks is
bounded by `orientedPowerBlockFarQ`, provided the simple upper-frequency
scale inequality holds. -/
lemma farCorrelationMajorant_powerBlock_zero_le
    (x : ℝ) (y y' U V v w : ℕ)
    (hx : 0 < x) (hU : 0 < U) (hV : 0 < V)
    (hhoneScale : 12 * (x / (V : ℝ)) ≤ (U : ℝ) ^ 4)
    (hv : v ∈ Finset.Ioc (V - 1) (2 * V - 1))
    (hw : w ∈ Finset.Ioc (V - 1) (2 * V - 1))
    (hdist : 0 < Nat.dist v w) :
    farCorrelationMajorant x y y' (U - 1) (2 * U - 1) v w ≤
      orientedPowerBlockFarQ x U V := by
  let C := correlationLower y (U - 1) v w
  let E := correlationUpper y' (2 * U - 1) v w
  let t : ℝ := |x * (1 / (w : ℝ) - 1 / (v : ℝ))|
  have hLU : 0 ≤ 1 + Real.log (2 * (U : ℝ)) := by
    have harg : (1 : ℝ) ≤ 2 * (U : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * U by omega)
    have := Real.log_nonneg harg
    linarith
  have hQ0 : 0 ≤ orientedPowerBlockFarQ x U V := by
    unfold orientedPowerBlockFarQ
    positivity
  by_cases hCE : C < E
  · have hvw : v ≠ w := by
      intro heq
      subst w
      simp at hdist
    have ht : 0 < t := by
      dsimp only [t]
      have hvpos : 0 < v := by
        have := (Finset.mem_Ioc.mp hv).1
        omega
      have hwpos : 0 < w := by
        have := (Finset.mem_Ioc.mp hw).1
        omega
      have hdiff : 1 / (w : ℝ) - 1 / (v : ℝ) ≠ 0 := by
        intro hzero
        have hinv : (w : ℝ)⁻¹ = (v : ℝ)⁻¹ := by
          simpa only [one_div] using sub_eq_zero.mp hzero
        have hcast : (w : ℝ) = (v : ℝ) := inv_injective hinv
        apply hvw
        exact_mod_cast hcast.symm
      exact abs_pos.mpr (mul_ne_zero (ne_of_gt hx) hdiff)
    have htLower : x / (4 * (V : ℝ) ^ 2) ≤ t := by
      simpa only [t] using
        dyadic_reciprocalPhaseDifference_lower x V v w hx hV hv hw hvw
    have htUpper : t ≤ x / (V : ℝ) := by
      simpa only [t] using
        dyadic_reciprocalPhaseDifference_upper x V v w hx hV hv hw
    have hClo : U ≤ C + 1 := by
      simpa only [C] using correlationLower_powerBlock_add_one_ge y U v w hU
    have hEhi : E + 1 ≤ 2 * U := by
      simpa only [E] using correlationUpper_powerBlock_add_one_le y' U v w hU
    have hN : E - C ≤ U := by
      simpa only [C, E] using
        correlationEndpoints_powerBlock_length_le y y' U v w hU
    have hlog : Real.log ((C + 1 : ℕ) : ℝ) ≤
        Real.log (2 * (U : ℝ)) := by
      simpa only [C, Nat.cast_mul, Nat.cast_ofNat] using
        log_correlationLower_powerBlock_add_one_le y y' U v w hU hCE
    have hdyadic : E - C ≤ C + 1 := hN.trans hClo
    have hhone : 12 * t ≤ ((C + 1 : ℕ) : ℝ) ^ 4 := by
      have hU4 : (U : ℝ) ^ 4 ≤ ((C + 1 : ℕ) : ℝ) ^ 4 := by
        gcongr
      exact (mul_le_mul_of_nonneg_left htUpper (by norm_num)).trans
        (hhoneScale.trans hU4)
    have hcases := effectiveReciprocalBound_direct_or_k2_or_seventh
      t C E ht hCE hdyadic hhone
    have hmajor : farCorrelationMajorant x y y' (U - 1) (2 * U - 1) v w =
        effectiveReciprocalBound t C E := by
      unfold farCorrelationMajorant
      change (if C < E then effectiveReciprocalBound t C E else 0) = _
      rw [if_pos hCE]
    rw [hmajor]
    rcases hcases with hdirect | hk2 | hseven
    · have hnum : (((E + 1 : ℕ) : ℝ)) ^ 2 ≤
          4 * (U : ℝ) ^ 2 := by
        have hER : (((E + 1 : ℕ) : ℝ)) ≤ 2 * (U : ℝ) := by
          exact_mod_cast hEhi
        nlinarith [sq_nonneg (((E + 1 : ℕ) : ℝ) - 2 * (U : ℝ))]
      have hphaseCross : x ≤ 4 * (V : ℝ) ^ 2 * t := by
        rw [div_le_iff₀ (by positivity : 0 < 4 * (V : ℝ) ^ 2)] at htLower
        simpa only [mul_comm] using htLower
      have hdirectQ : (((E + 1 : ℕ) : ℝ)) ^ 2 / t ≤
          16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x := by
        rw [div_le_div_iff₀ ht hx]
        calc
          (((E + 1 : ℕ) : ℝ)) ^ 2 * x ≤
              (4 * (U : ℝ) ^ 2) * x :=
            mul_le_mul_of_nonneg_right hnum hx.le
          _ ≤ (4 * (U : ℝ) ^ 2) *
              (4 * (V : ℝ) ^ 2 * t) :=
            mul_le_mul_of_nonneg_left hphaseCross (by positivity)
          _ = 16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 * t := by ring
      exact (hdirect.trans hdirectQ).trans (by
        unfold orientedPowerBlockFarQ
        have htwo : 0 ≤ 128 * (U : ℝ) *
            (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
              Real.sqrt (1 + Real.log (2 * (U : ℝ))) := by positivity
        have hthree : 0 ≤ 128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
            (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ) := by
          exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
            (Real.rpow_nonneg hLU _)
        linarith)
    · have hratio : t / (((C + 1 : ℕ) : ℝ)) ^ 4 ≤
          x / ((V : ℝ) * (U : ℝ) ^ 4) := by
        calc
          t / (((C + 1 : ℕ) : ℝ)) ^ 4 ≤
              (x / (V : ℝ)) / (((C + 1 : ℕ) : ℝ)) ^ 4 :=
            div_le_div_of_nonneg_right htUpper (by positivity)
          _ ≤ (x / (V : ℝ)) / (U : ℝ) ^ 4 := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            gcongr
          _ = x / ((V : ℝ) * (U : ℝ) ^ 4) := by ring
      have hratio0 : 0 ≤ t / (((C + 1 : ℕ) : ℝ)) ^ 4 := by positivity
      have hrpow := Real.rpow_le_rpow hratio0 hratio
        (by norm_num : (0 : ℝ) ≤ 1 / 6)
      have hsqrt : Real.sqrt (1 + Real.log (((C + 1 : ℕ) : ℝ))) ≤
          Real.sqrt (1 + Real.log (2 * (U : ℝ))) := by
        apply Real.sqrt_le_sqrt
        linarith
      have hk2Q :
          128 * (((E - C : ℕ) : ℝ)) *
              (t / (((C + 1 : ℕ) : ℝ)) ^ 4) ^ (1 / 6 : ℝ) *
                Real.sqrt (1 + Real.log (((C + 1 : ℕ) : ℝ))) ≤
            128 * (U : ℝ) *
              (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
                Real.sqrt (1 + Real.log (2 * (U : ℝ))) := by
        gcongr
      exact (hk2.trans hk2Q).trans (by
        unfold orientedPowerBlockFarQ
        have hone : 0 ≤ 16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x := by
          positivity
        have hthree : 0 ≤ 128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
            (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ) := by
          exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
            (Real.rpow_nonneg hLU _)
        linarith)
    · let L : ℝ := 1 + Real.log (((C + 1 : ℕ) : ℝ))
      have hCupper : (((C + 1 : ℕ) : ℝ)) ≤ 2 * (U : ℝ) := by
        have : C + 1 ≤ 2 * U := by omega
        exact_mod_cast this
      have hL0 : 0 ≤ L := by
        dsimp only [L]
        have hCpos : (1 : ℝ) ≤ ((C + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ C + 1 by omega)
        have := Real.log_nonneg hCpos
        linarith
      have hroot := effective_k1_highFailure_le (C + 1) L
        (effectiveReciprocalBound t C E) (by omega) hL0 hseven
      have hLupper : L ≤ 1 + Real.log (2 * (U : ℝ)) := by
        dsimp only [L]
        linarith
      have hCupPow : (((C + 1 : ℕ) : ℝ)) ^ (6 / 7 : ℝ) ≤
          (2 * (U : ℝ)) ^ (6 / 7 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hCupper (by norm_num)
      have hLPow : L ^ (2 / 7 : ℝ) ≤
          (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ) :=
        Real.rpow_le_rpow hL0 hLupper (by norm_num)
      have hroot' : effectiveReciprocalBound t C E ≤
          128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
            (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ) := by
        exact hroot.trans (by gcongr)
      exact hroot'.trans (by
        unfold orientedPowerBlockFarQ
        have hone : 0 ≤ 16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x := by
          positivity
        have htwo : 0 ≤ 128 * (U : ℝ) *
            (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
              Real.sqrt (1 + Real.log (2 * (U : ℝ))) := by positivity
        linarith)
  · unfold farCorrelationMajorant
    change (if C < E then effectiveReciprocalBound t C E else 0) ≤ _
    rw [if_neg hCE]
    exact hQ0

/-- Ordered far pairs in the second-variable support. -/
def farPairs (V₀ V₁ T : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc V₀ V₁ ×ˢ Finset.Ioc V₀ V₁).filter fun p ↦
    T < Nat.dist p.1 p.2

/-- The maximum of the explicit correlation majorants over the finite set
of far pairs.  Inserting zero makes the maximum total and visibly
nonnegative, including when there are no far pairs. -/
noncomputable def threeBranchFarQ
    (x : ℝ) (y y' A B V₀ V₁ T : ℕ) : ℝ :=
  let values := (farPairs V₀ V₁ T).image fun p ↦
    farCorrelationMajorant x y y' A B p.1 p.2
  (insert 0 values).max' (by simp)

lemma threeBranchFarQ_nonneg
    (x : ℝ) (y y' A B V₀ V₁ T : ℕ) :
    0 ≤ threeBranchFarQ x y y' A B V₀ V₁ T := by
  unfold threeBranchFarQ
  dsimp only
  apply Finset.le_max'
  simp

lemma farCorrelationMajorant_le_threeBranchFarQ
    (x : ℝ) (y y' A B V₀ V₁ T v w : ℕ)
    (hv : v ∈ Finset.Ioc V₀ V₁) (hw : w ∈ Finset.Ioc V₀ V₁)
    (hfar : T < Nat.dist v w) :
    farCorrelationMajorant x y y' A B v w ≤
      threeBranchFarQ x y y' A B V₀ V₁ T := by
  unfold threeBranchFarQ
  dsimp only
  apply Finset.le_max'
  simp only [Finset.mem_insert, Finset.mem_image]
  right
  exact ⟨(v, w), by simp [farPairs, hv, hw, hfar], rfl⟩

/-- Eliminate the finite maximum by proving a uniform bound for every far
pair.  This is the main simplification interface used by the dyadic Type II
assembly. -/
lemma threeBranchFarQ_le
    (x : ℝ) (y y' A B V₀ V₁ T : ℕ) (Q : ℝ)
    (hQ : 0 ≤ Q)
    (hmajor : ∀ v ∈ Finset.Ioc V₀ V₁,
      ∀ w ∈ Finset.Ioc V₀ V₁, T < Nat.dist v w →
        farCorrelationMajorant x y y' A B v w ≤ Q) :
    threeBranchFarQ x y y' A B V₀ V₁ T ≤ Q := by
  classical
  unfold threeBranchFarQ
  dsimp only
  let values := (farPairs V₀ V₁ T).image fun p ↦
      farCorrelationMajorant x y y' A B p.1 p.2
  change (insert 0 values).max' (by simp) ≤ Q
  have hne : (insert 0 values).Nonempty := ⟨0, by simp⟩
  have hmem := Finset.max'_mem (insert 0 values) hne
  rcases Finset.mem_insert.mp hmem with hzero | hvalue
  · calc
      (insert 0 values).max' (by simp) = 0 := hzero
      _ ≤ Q := hQ
  · rcases Finset.mem_image.mp hvalue with ⟨p, hp, hpval⟩
    have hp' : (p.1 ∈ Finset.Ioc V₀ V₁ ∧
        p.2 ∈ Finset.Ioc V₀ V₁) ∧ T < Nat.dist p.1 p.2 := by
      simpa only [farPairs, Finset.mem_filter, Finset.mem_product] using hp
    rw [← hpval]
    exact hmajor p.1 hp'.1.1 p.2 hp'.1.2 hp'.2

/-- Finite-max version of the oriented power-block far-correlation bound.
At threshold zero every far pair is covered by
`farCorrelationMajorant_powerBlock_zero_le`. -/
lemma threeBranchFarQ_powerBlock_zero_le
    (x : ℝ) (y y' U V : ℕ)
    (hx : 0 < x) (hU : 0 < U) (hV : 0 < V)
    (hhoneScale : 12 * (x / (V : ℝ)) ≤ (U : ℝ) ^ 4) :
    threeBranchFarQ x y y' (U - 1) (2 * U - 1)
        (V - 1) (2 * V - 1) 0 ≤
      orientedPowerBlockFarQ x U V := by
  apply threeBranchFarQ_le
  · unfold orientedPowerBlockFarQ
    have hLU : 0 ≤ 1 + Real.log (2 * (U : ℝ)) := by
      have harg : (1 : ℝ) ≤ 2 * (U : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * U by omega)
      have := Real.log_nonneg harg
      linarith
    have hthree : 0 ≤ 128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
        (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ) := by
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg hLU _)
    positivity
  · intro v hv w hw hdist
    exact farCorrelationMajorant_powerBlock_zero_le
      x y y' U V v w hx hU hV hhoneScale hv hw hdist

/-- A fully concrete near--far Type II bound.  It has no exponential-sum,
mean-square, `hfarQ`, or high-frequency premise.  Each far pair is handled
by the three-branch reciprocal estimate when its upper-frequency condition
holds and by the trivial cardinality estimate otherwise. -/
lemma norm_reciprocalBilinearSum_Ioc_le_near_far
    (x : ℝ) (y y' A B V₀ V₁ T : ℕ) (alpha beta : ℕ → ℂ)
    (hx : 0 < x) (hdyadic : B - A ≤ A + 1) :
    ‖reciprocalBilinearSum (Finset.Ioc y y') (Finset.Ioc A B)
        (Finset.Ioc V₀ V₁) x alpha beta‖ ≤
      l2Norm (Finset.Ioc A B) alpha *
        Real.sqrt
          (2 * (B - A : ℕ) * (2 * T + 1) +
            threeBranchFarQ x y y' A B V₀ V₁ T *
              ((V₁ - V₀ : ℕ) : ℝ)) *
          l2Norm (Finset.Ioc V₀ V₁) beta := by
  let Q := threeBranchFarQ x y y' A B V₀ V₁ T
  have hQ : 0 ≤ Q := threeBranchFarQ_nonneg x y y' A B V₀ V₁ T
  have hcardAB : (Finset.Ioc A B).card = B - A := by simp
  have hcardV : (Finset.Ioc V₀ V₁).card = V₁ - V₀ := by simp
  have hnear : ∀ v ∈ Finset.Ioc V₀ V₁,
      ∀ w ∈ Finset.Ioc V₀ V₁, Nat.dist v w ≤ T →
        ‖kernelCorrelation (Finset.Ioc A B)
          (restrictedReciprocalKernel (Finset.Ioc y y') x) v w‖ ≤
            ((B - A : ℕ) : ℝ) := by
    intro v hv w hw hn
    simpa only [hcardAB] using
      norm_kernelCorrelation_restrictedReciprocalKernel_le_card
        (Finset.Ioc y y') (Finset.Ioc A B) x v w
  have hfar : ∀ v ∈ Finset.Ioc V₀ V₁,
      ∀ w ∈ Finset.Ioc V₀ V₁, T < Nat.dist v w →
        ‖kernelCorrelation (Finset.Ioc A B)
          (restrictedReciprocalKernel (Finset.Ioc y y') x) v w‖ ≤ Q := by
    intro v hv w hw hdist
    have hvpos : 0 < v := by
      have := (Finset.mem_Ioc.mp hv).1
      omega
    have hwpos : 0 < w := by
      have := (Finset.mem_Ioc.mp hw).1
      omega
    let C := correlationLower y A v w
    let E := correlationUpper y' B v w
    let t : ℝ := |x * (1 / (w : ℝ) - 1 / (v : ℝ))|
    have htoQ : farCorrelationMajorant x y y' A B v w ≤ Q :=
      farCorrelationMajorant_le_threeBranchFarQ
        x y y' A B V₀ V₁ T v w hv hw hdist
    rw [norm_kernelCorrelation_restrictedReciprocalKernel_Ioc_eq_abs
      x y y' A B v w hvpos hwpos]
    change ‖reciprocalExpSum t C E‖ ≤ Q
    by_cases hCE : C < E
    · have ht : 0 < t := by
        dsimp only [t]
        have hvw : v ≠ w := by
          intro heq
          subst w
          simp at hdist
        have hdiff : 1 / (w : ℝ) - 1 / (v : ℝ) ≠ 0 := by
          intro hzero
          have hinv : (w : ℝ)⁻¹ = (v : ℝ)⁻¹ := by
            simpa only [one_div] using sub_eq_zero.mp hzero
          have hcast : (w : ℝ) = (v : ℝ) := inv_injective hinv
          apply hvw
          exact_mod_cast hcast.symm
        exact abs_pos.mpr (mul_ne_zero (ne_of_gt hx) hdiff)
      have hbase := norm_reciprocalExpSum_le_effective
        t C E ht hCE (by
          dsimp only [C, E, correlationLower, correlationUpper]
          omega)
      have hmajor : farCorrelationMajorant x y y' A B v w =
          effectiveReciprocalBound t C E := by
        unfold farCorrelationMajorant
        change (if C < E then effectiveReciprocalBound t C E else 0) = _
        rw [if_pos hCE]
      rw [hmajor] at htoQ
      exact hbase.trans htoQ
    · have hempty : Finset.Ioc C E = ∅ := Finset.Ioc_eq_empty hCE
      simpa [reciprocalExpSum, hempty] using hQ
  unfold reciprocalBilinearSum
  have hbound := norm_bilinearSum_le_natDist_near_far
    (Finset.Ioc A B) (Finset.Ioc V₀ V₁) alpha beta
    (restrictedReciprocalKernel (Finset.Ioc y y') x)
    T (B - A : ℕ) Q (by positivity) hQ hnear hfar
  simpa only [Q, hcardV] using hbound

end TypeII

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/VaughanTypeIIBridge.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The Type-II Vaughan terms as reciprocal bilinear sums

The product-restricted kernel in `TypeII` is the analytic form used in
Granville--Ramaré, Proposition 9.4.  This file identifies it exactly with
the two Type-II terms in the four-sum Vaughan decomposition.  It is kept as
a separate bridge so neither the algebraic Vaughan development nor the
generic Type-II estimates acquire a circular dependency.
-/

noncomputable section

namespace VaughanTypeIIBridge

open scoped ArithmeticFunction BigOperators
open Vaughan VaughanFourSums VaughanTypeIIExpansion

private lemma vaughan_reciprocalPhase_eq_e (x : ℝ) (n : ℕ) :
    Vaughan.reciprocalPhase x n = e (x / (n : ℝ)) := by
  unfold Vaughan.reciprocalPhase e
  congr 1

/-- The `Σ₂,₂` term is the reciprocal bilinear sum with outer coefficient
`b_r` and inner coefficient one.  The rectangular inner support `[1,y']`
is cut down to the exact hyperbolic interval by the kernel. -/
theorem sigma22_eq_reciprocalBilinearSum
    (y y' M K : ℕ) (x : ℝ) :
    sigma22 (Finset.Ioc y y') (Vaughan.reciprocalPhase x) M K =
      TypeII.reciprocalBilinearSum
        (Finset.Ioc y y') (Finset.Ioc M (M * K)) (Finset.Icc 1 y') x
        (fun r => (bCoeff M K r : ℂ)) (fun _ => 1) := by
  rw [sigma22_Ioc_eq_outer, TypeII.reciprocalBilinearSum_eq]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrpos : 0 < r := by
    have := (Finset.mem_Ioc.mp hr).1
    omega
  rw [← innerProductInterval_eq_Ioc y y' r hrpos]
  unfold innerProductInterval
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun l hl => ?_
  simp only [Finset.mem_Ioc]
  by_cases hprod : y < r * l ∧ r * l ≤ y'
  · rw [if_pos hprod, if_pos hprod]
    rw [vaughan_reciprocalPhase_eq_e]
    ring
  · rw [if_neg hprod, if_neg hprod]

/-- The `Σ₃` term is the reciprocal bilinear sum with outer coefficient
`a_l` and inner von Mangoldt coefficient.  The support `(K,y']`, together
with the product-restricted kernel, is exactly the interval
`(max K (y/l), y'/l]` in the expanded Vaughan term. -/
theorem sigma3_eq_reciprocalBilinearSum
    (y y' M K : ℕ) (x : ℝ) :
    sigma3 (Finset.Ioc y y') (Vaughan.reciprocalPhase x) M K =
      TypeII.reciprocalBilinearSum
        (Finset.Ioc y y') (Finset.Ioc M y') (Finset.Ioc K y') x
        (fun l => (aCoeff M l : ℂ))
        (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) := by
  rw [sigma3_Ioc_eq_outer, TypeII.reciprocalBilinearSum_eq]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlpos : 0 < l := by
    have := (Finset.mem_Ioc.mp hl).1
    omega
  have hset :
      (Finset.Ioc K y').filter (fun k => l * k ∈ Finset.Ioc y y') =
        Finset.Ioc (max K (y / l)) (y' / l) := by
    ext k
    constructor
    · intro hk
      obtain ⟨hkI, hprodI⟩ := Finset.mem_filter.mp hk
      have hkI' := Finset.mem_Ioc.mp hkI
      have hprodI' := Finset.mem_Ioc.mp hprodI
      apply Finset.mem_Ioc.mpr
      constructor
      · rw [max_lt_iff]
        exact ⟨hkI'.1, (Nat.div_lt_iff_lt_mul hlpos).2
          (by simpa [Nat.mul_comm] using hprodI'.1)⟩
      · exact (Nat.le_div_iff_mul_le hlpos).2
          (by simpa [Nat.mul_comm] using hprodI'.2)
    · intro hk
      have hk' := Finset.mem_Ioc.mp hk
      have hklow := (max_lt_iff.mp hk'.1)
      have hprodLow : y < l * k :=
        by simpa [Nat.mul_comm] using
          (Nat.div_lt_iff_lt_mul hlpos).1 hklow.2
      have hprodHigh : l * k ≤ y' :=
        by simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hlpos).1 hk'.2
      have hky' : k ≤ y' :=
        (Nat.le_mul_of_pos_left k hlpos).trans hprodHigh
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hklow.1, hky'⟩,
          Finset.mem_Ioc.mpr ⟨hprodLow, hprodHigh⟩⟩
  rw [← hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hprod : l * k ∈ Finset.Ioc y y'
  · rw [if_pos hprod, if_pos hprod]
    rw [vaughan_reciprocalPhase_eq_e]
    simp only [Nat.mul_comm]
  · rw [if_neg hprod, if_neg hprod]

end VaughanTypeIIBridge

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/VaughanTypeIIDyadic.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Dyadic support decomposition for the Type-II Vaughan sums

This file decomposes an arbitrary finite positive support into the exact
power blocks used by the reciprocal exponential-sum estimate.  Coefficients
are extended by zero outside their original support, so the rectangular
dyadic blocks introduce no extra terms.
-/

noncomputable section

namespace VaughanTypeIIDyadic

open scoped BigOperators

/-- Extend a coefficient sequence by zero outside a finite support. -/
def restrictCoeff (s : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ s then a n else 0

@[simp] lemma restrictCoeff_of_mem
    (s : Finset ℕ) (a : ℕ → ℂ) {n : ℕ} (hn : n ∈ s) :
    restrictCoeff s a n = a n := by
  simp [restrictCoeff, hn]

@[simp] lemma restrictCoeff_of_not_mem
    (s : Finset ℕ) (a : ℕ → ℂ) {n : ℕ} (hn : n ∉ s) :
    restrictCoeff s a n = 0 := by
  simp [restrictCoeff, hn]

/-- Restricting a coefficient sequence cannot increase its squared mass on
any finite block. -/
theorem sum_norm_sq_restrictCoeff_le
    (block support : Finset ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ block, ‖restrictCoeff support a n‖ ^ 2) ≤
      ∑ n ∈ block, ‖a n‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  by_cases hns : n ∈ support
  · simp [restrictCoeff, hns]
  · simp [restrictCoeff, hns]

/-- The half-open power block used in `TypeI` is the natural-number `Ioc`
interval whose endpoints are one less than consecutive powers of two. -/
theorem dyadicBlock_eq_Ioc_pred (j : ℕ) :
    TypeI.dyadicBlock j = Finset.Ioc (2 ^ j - 1) (2 ^ (j + 1) - 1) := by
  ext n
  have hjpos : 0 < 2 ^ j := pow_pos (by norm_num) j
  simp only [TypeI.dyadicBlock, Finset.mem_Ico, Finset.mem_Ioc]
  omega

/-! ## Coefficient estimates on the shifted power blocks -/

/-- Proposition 10.1 on `[2^j,2^(j+1))`.  Compared with its native
interval `(2^j,2^(j+1)]`, this costs only the left endpoint, whose
`aCoeff` has norm at most one.  An arbitrary support mask can only decrease
the squared mass. -/
theorem l2Norm_restrict_aCoeff_dyadicBlock_sq_le
    (support : Finset ℕ) (M j : ℕ) (hM : 1 ≤ M) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (restrictCoeff support
          (fun n => ((VaughanFourSums.aCoeff M n : ℝ) : ℂ))) ^ 2 ≤
      (8 / 9 : ℝ) * (2 ^ j : ℕ) * (Real.log M + 3) ^ 3 + 1 := by
  let p : ℕ := 2 ^ j
  have hp : 0 < p := pow_pos (by norm_num) j
  have hsubset : TypeI.dyadicBlock j ⊆
      insert p (TypeII.dyadicNatBlock p) := by
    intro n hn
    have hn' : p ≤ n ∧ n < 2 * p := by
      simpa [TypeI.dyadicBlock, p, pow_succ, Nat.mul_comm] using
        (Finset.mem_Ico.mp hn)
    simp only [Finset.mem_insert, TypeII.dyadicNatBlock, Finset.mem_Ioc]
    omega
  have hpnot : p ∉ TypeII.dyadicNatBlock p := by
    simp [TypeII.dyadicNatBlock]
  have hpoint :
      ‖((VaughanFourSums.aCoeff M p : ℝ) : ℂ)‖ ^ 2 ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h : |VaughanFourSums.aCoeff M p| ≤ (1 : ℝ) := by
      simpa [p] using TypeII.abs_aCoeff_two_pow_le_one M j hM
    change |VaughanFourSums.aCoeff M p| ^ 2 ≤ 1
    simpa using pow_le_pow_left₀ (abs_nonneg _ ) h 2
  rw [TypeII.l2Norm_sq]
  calc
    (∑ n ∈ TypeI.dyadicBlock j,
        ‖restrictCoeff support
          (fun n => ((VaughanFourSums.aCoeff M n : ℝ) : ℂ)) n‖ ^ 2) ≤
        ∑ n ∈ TypeI.dyadicBlock j,
          ‖((VaughanFourSums.aCoeff M n : ℝ) : ℂ)‖ ^ 2 :=
      sum_norm_sq_restrictCoeff_le _ _ _
    _ ≤ ∑ n ∈ insert p (TypeII.dyadicNatBlock p),
          ‖((VaughanFourSums.aCoeff M n : ℝ) : ℂ)‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n hn _hnblock
      positivity
    _ = ‖((VaughanFourSums.aCoeff M p : ℝ) : ℂ)‖ ^ 2 +
          ∑ n ∈ TypeII.dyadicNatBlock p,
            ‖((VaughanFourSums.aCoeff M n : ℝ) : ℂ)‖ ^ 2 := by
      rw [Finset.sum_insert hpnot]
    _ ≤ 1 + (8 / 9 : ℝ) * (p : ℝ) * (Real.log M + 3) ^ 3 :=
      add_le_add hpoint (TypeII.sum_norm_aCoeff_sq_le p M hM)
    _ = (8 / 9 : ℝ) * (2 ^ j : ℕ) * (Real.log M + 3) ^ 3 + 1 := by
      simp only [p]
      ring

/-- The elementary `|b_r| ≤ log r` estimate on the shifted power block,
again allowing an arbitrary support mask. -/
theorem l2Norm_restrict_bCoeff_dyadicBlock_sq_le
    (support : Finset ℕ) (M K j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (restrictCoeff support
          (fun r => ((VaughanFourSums.bCoeff M K r : ℝ) : ℂ))) ^ 2 ≤
      (2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2 := by
  let p : ℕ := 2 ^ j
  have hp : 0 < p := pow_pos (by norm_num) j
  have hterm (r : ℕ) (hr : r ∈ TypeI.dyadicBlock j) :
      ‖restrictCoeff support
          (fun r => ((VaughanFourSums.bCoeff M K r : ℝ) : ℂ)) r‖ ^ 2 ≤
        Real.log (2 * p : ℕ) ^ 2 := by
    by_cases hrs : r ∈ support
    · rw [restrictCoeff_of_mem support _ hrs, Complex.norm_real,
          Real.norm_eq_abs]
      have hrI := TypeI.mem_dyadicBlock.mp hr
      have hrpos : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le hp hrI.1)
      have hrle : r ≤ 2 * p := by
        simpa [p, pow_succ, Nat.mul_comm] using (Nat.le_of_lt hrI.2)
      have hlog : Real.log (r : ℝ) ≤ Real.log (2 * p : ℕ) :=
        Real.log_le_log hrpos (by exact_mod_cast hrle)
      exact pow_le_pow_left₀ (abs_nonneg _)
        ((VaughanFourSums.abs_bCoeff_le_log M K r).trans hlog) 2
    · rw [restrictCoeff_of_not_mem support _ hrs, norm_zero]
      simpa using sq_nonneg (Real.log (2 * p : ℕ))
  rw [TypeII.l2Norm_sq]
  calc
    (∑ r ∈ TypeI.dyadicBlock j,
        ‖restrictCoeff support
          (fun r => ((VaughanFourSums.bCoeff M K r : ℝ) : ℂ)) r‖ ^ 2) ≤
        ∑ _r ∈ TypeI.dyadicBlock j, Real.log (2 * p : ℕ) ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact hterm r hr
    _ = (2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2 := by
      simp [TypeI.card_dyadicBlock, p]

/-- The pointwise von Mangoldt estimate on the shifted power block. -/
theorem l2Norm_restrict_vonMangoldt_dyadicBlock_sq_le
    (support : Finset ℕ) (j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (restrictCoeff support
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))) ^ 2 ≤
      (2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2 := by
  let p : ℕ := 2 ^ j
  have hp : 0 < p := pow_pos (by norm_num) j
  have hterm (k : ℕ) (hk : k ∈ TypeI.dyadicBlock j) :
      ‖restrictCoeff support
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) k‖ ^ 2 ≤
        Real.log (2 * p : ℕ) ^ 2 := by
    by_cases hks : k ∈ support
    · rw [restrictCoeff_of_mem support _ hks]
      have hkI := TypeI.mem_dyadicBlock.mp hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le hp hkI.1)
      have hkle : k ≤ 2 * p := by
        simpa [p, pow_succ, Nat.mul_comm] using (Nat.le_of_lt hkI.2)
      have hlog : Real.log (k : ℝ) ≤ Real.log (2 * p : ℕ) :=
        Real.log_le_log hkpos (by exact_mod_cast hkle)
      have hlam0 := ArithmeticFunction.vonMangoldt_nonneg (n := k)
      rw [Complex.norm_of_nonneg hlam0]
      exact pow_le_pow_left₀ hlam0
        (ArithmeticFunction.vonMangoldt_le_log.trans hlog) 2
    · rw [restrictCoeff_of_not_mem support _ hks, norm_zero]
      simpa using sq_nonneg (Real.log (2 * p : ℕ))
  rw [TypeII.l2Norm_sq]
  calc
    (∑ k ∈ TypeI.dyadicBlock j,
        ‖restrictCoeff support
          (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) k‖ ^ 2) ≤
        ∑ _k ∈ TypeI.dyadicBlock j, Real.log (2 * p : ℕ) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact hterm k hk
    _ = (2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2 := by
      simp [TypeI.card_dyadicBlock, p]

/-- A finite sum on positive indices bounded by `N` is the sum of its power
blocks after extending the summand by zero outside the original support. -/
theorem sum_eq_sum_dyadic_restrict
    {A : Type*} [AddCommMonoid A]
    (s : Finset ℕ) (f : ℕ → A) (N : ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) :
    (∑ n ∈ s, f n) =
      ∑ j ∈ Finset.range (TypeI.dyadicCount N),
        ∑ n ∈ TypeI.dyadicBlock j, if n ∈ s then f n else 0 := by
  rw [← TypeI.sum_dyadicBlocks]
  have hsub : s ⊆ Finset.Ico 1 (2 ^ TypeI.dyadicCount N) := by
    intro n hn
    have hnrange := hs n hn
    exact Finset.mem_Ico.mpr
      ⟨hnrange.1,
        lt_of_le_of_lt hnrange.2 (TypeI.lt_two_pow_dyadicCount N)⟩
  calc
    (∑ n ∈ s, f n) = ∑ n ∈ s, if n ∈ s then f n else 0 := by simp
    _ = ∑ n ∈ Finset.Ico 1 (2 ^ TypeI.dyadicCount N),
          if n ∈ s then f n else 0 := by
      apply Finset.sum_subset hsub
      intro n _hnIco hnnot
      simp [hnnot]

/-- Two bounded positive supports decompose into rectangular power blocks.
The two membership tests are retained explicitly for later identification
with restricted coefficient sequences. -/
theorem doubleSum_eq_sum_dyadic_restrict
    {A : Type*} [AddCommMonoid A]
    (s t : Finset ℕ) (F : ℕ → ℕ → A) (S T : ℕ)
    (hs : ∀ u ∈ s, 1 ≤ u ∧ u ≤ S)
    (ht : ∀ v ∈ t, 1 ≤ v ∧ v ≤ T) :
    (∑ u ∈ s, ∑ v ∈ t, F u v) =
      ∑ j ∈ Finset.range (TypeI.dyadicCount S),
        ∑ k ∈ Finset.range (TypeI.dyadicCount T),
          ∑ u ∈ TypeI.dyadicBlock j,
            ∑ v ∈ TypeI.dyadicBlock k,
              if u ∈ s then (if v ∈ t then F u v else 0) else 0 := by
  rw [sum_eq_sum_dyadic_restrict s (fun u => ∑ v ∈ t, F u v) S hs]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ u ∈ TypeI.dyadicBlock j,
        if u ∈ s then (∑ v ∈ t, F u v) else 0) =
        ∑ u ∈ TypeI.dyadicBlock j,
          ∑ k ∈ Finset.range (TypeI.dyadicCount T),
            ∑ v ∈ TypeI.dyadicBlock k,
              if u ∈ s then (if v ∈ t then F u v else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hus : u ∈ s
      · simp only [hus, if_pos]
        exact sum_eq_sum_dyadic_restrict t (F u) T ht
      · simp [hus]
    _ = ∑ k ∈ Finset.range (TypeI.dyadicCount T),
          ∑ u ∈ TypeI.dyadicBlock j,
            ∑ v ∈ TypeI.dyadicBlock k,
              if u ∈ s then (if v ∈ t then F u v else 0) else 0 := by
      rw [Finset.sum_comm]

/-- Exact dyadic decomposition of the concrete product-restricted reciprocal
bilinear sum. -/
theorem reciprocalBilinearSum_eq_sum_dyadic
    (I uSupport vSupport : Finset ℕ) (x : ℝ)
    (alpha beta : ℕ → ℂ) (HU HV : ℕ)
    (hu : ∀ u ∈ uSupport, 1 ≤ u ∧ u ≤ HU)
    (hv : ∀ v ∈ vSupport, 1 ≤ v ∧ v ≤ HV) :
    TypeII.reciprocalBilinearSum I uSupport vSupport x alpha beta =
      ∑ j ∈ Finset.range (TypeI.dyadicCount HU),
        ∑ k ∈ Finset.range (TypeI.dyadicCount HV),
          TypeII.reciprocalBilinearSum I
            (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x
            (restrictCoeff uSupport alpha) (restrictCoeff vSupport beta) := by
  unfold TypeII.reciprocalBilinearSum TypeII.bilinearSum TypeII.innerSum
  simp_rw [Finset.mul_sum]
  rw [doubleSum_eq_sum_dyadic_restrict uSupport vSupport
    (fun u v => alpha u *
      (beta v * TypeII.restrictedReciprocalKernel I x u v)) HU HV hu hv]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro u huj
  apply Finset.sum_congr rfl
  intro v hvk
  by_cases hus : u ∈ uSupport
  · by_cases hvs : v ∈ vSupport
    · simp [restrictCoeff, hus, hvs]
    · simp [restrictCoeff, hus, hvs]
  · simp [restrictCoeff, hus]

/-- Dyadic decomposition of the actual `Σ₂,₂` Vaughan term. -/
theorem sigma22_eq_sum_dyadic
    (y y' M K : ℕ) (x : ℝ) :
    VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K =
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          TypeII.reciprocalBilinearSum (Finset.Ioc y y')
            (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x
            (restrictCoeff (Finset.Ioc M (M * K))
              (fun r => (VaughanFourSums.bCoeff M K r : ℂ)))
            (restrictCoeff (Finset.Icc 1 y') (fun _ => 1)) := by
  rw [VaughanTypeIIBridge.sigma22_eq_reciprocalBilinearSum]
  apply reciprocalBilinearSum_eq_sum_dyadic
  · intro r hr
    have hr' := Finset.mem_Ioc.mp hr
    exact ⟨by omega, hr'.2⟩
  · intro l hl
    exact Finset.mem_Icc.mp hl

/-- Dyadic decomposition of the actual `Σ₃` Vaughan term. -/
theorem sigma3_eq_sum_dyadic
    (y y' M K : ℕ) (x : ℝ) :
    VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K =
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          TypeII.reciprocalBilinearSum (Finset.Ioc y y')
            (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x
            (restrictCoeff (Finset.Ioc M y')
              (fun l => (VaughanFourSums.aCoeff M l : ℂ)))
            (restrictCoeff (Finset.Ioc K y')
              (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))) := by
  rw [VaughanTypeIIBridge.sigma3_eq_reciprocalBilinearSum]
  apply reciprocalBilinearSum_eq_sum_dyadic
  · intro l hl
    have hl' := Finset.mem_Ioc.mp hl
    exact ⟨by omega, hl'.2⟩
  · intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    exact ⟨by omega, hk'.2⟩

/-! ## Norm endpoints for the dyadic bilinear sums -/

/-- Triangle inequality for a finite rectangular family of complex sums. -/
theorem norm_doubleSum_le_of_norm_le
    (J K : Finset ℕ) (z : ℕ → ℕ → ℂ) (F : ℕ → ℕ → ℝ)
    (h : ∀ j ∈ J, ∀ k ∈ K, ‖z j k‖ ≤ F j k) :
    ‖∑ j ∈ J, ∑ k ∈ K, z j k‖ ≤
      ∑ j ∈ J, ∑ k ∈ K, F j k := by
  calc
    ‖∑ j ∈ J, ∑ k ∈ K, z j k‖ ≤
        ∑ j ∈ J, ‖∑ k ∈ K, z j k‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, ∑ k ∈ K, ‖z j k‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_sum_le _ _
    _ ≤ ∑ j ∈ J, ∑ k ∈ K, F j k := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact h j hj k hk

/-- Raw norm endpoint for the dyadic `Σ₂,₂` expansion. -/
theorem norm_sigma22_le_sum_dyadic_of_block
    (y y' M K : ℕ) (x : ℝ) (F : ℕ → ℕ → ℝ)
    (hblock : ∀ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
      ∀ k ∈ Finset.range (TypeI.dyadicCount y'),
        ‖TypeII.reciprocalBilinearSum (Finset.Ioc y y')
          (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x
          (restrictCoeff (Finset.Ioc M (M * K))
            (fun r => (VaughanFourSums.bCoeff M K r : ℂ)))
          (restrictCoeff (Finset.Icc 1 y') (fun _ => 1))‖ ≤ F j k) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'), F j k := by
  rw [sigma22_eq_sum_dyadic]
  exact norm_doubleSum_le_of_norm_le _ _ _ F hblock

/-- Raw norm endpoint for the dyadic `Σ₃` expansion. -/
theorem norm_sigma3_le_sum_dyadic_of_block
    (y y' M K : ℕ) (x : ℝ) (F : ℕ → ℕ → ℝ)
    (hblock : ∀ j ∈ Finset.range (TypeI.dyadicCount y'),
      ∀ k ∈ Finset.range (TypeI.dyadicCount y'),
        ‖TypeII.reciprocalBilinearSum (Finset.Ioc y y')
          (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x
          (restrictCoeff (Finset.Ioc M y')
            (fun l => (VaughanFourSums.aCoeff M l : ℂ)))
          (restrictCoeff (Finset.Ioc K y')
            (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)))‖ ≤ F j k) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'), F j k := by
  rw [sigma3_eq_sum_dyadic]
  exact norm_doubleSum_le_of_norm_le _ _ _ F hblock

/-- The fully explicit near--far factor for a pair of power blocks. -/
noncomputable def dyadicNearFarFactor
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) : ℝ :=
  TypeII.l2Norm (TypeI.dyadicBlock j) alpha *
    Real.sqrt
      (2 * (2 ^ j : ℕ) * (2 * T + 1) +
        TypeII.threeBranchFarQ x y y'
          (2 ^ j - 1) (2 ^ (j + 1) - 1)
          (2 ^ k - 1) (2 ^ (k + 1) - 1) T * (2 ^ k : ℕ)) *
    TypeII.l2Norm (TypeI.dyadicBlock k) beta

/-- The premise-free near--far estimate on two power blocks. -/
theorem norm_reciprocalBilinearSum_dyadic_le_near_far
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) (hx : 0 < x) :
    ‖TypeII.reciprocalBilinearSum (Finset.Ioc y y')
        (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x alpha beta‖ ≤
      dyadicNearFarFactor x y y' j k T alpha beta := by
  have hjpos : 0 < 2 ^ j := pow_pos (by norm_num) j
  have hkpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hjdiff :
      (2 ^ (j + 1) - 1) - (2 ^ j - 1) = 2 ^ j := by
    rw [pow_succ]
    omega
  have hkdiff :
      (2 ^ (k + 1) - 1) - (2 ^ k - 1) = 2 ^ k := by
    rw [pow_succ]
    omega
  have hdyadic :
      (2 ^ (j + 1) - 1) - (2 ^ j - 1) ≤ (2 ^ j - 1) + 1 := by
    rw [hjdiff]
    omega
  rw [dyadicBlock_eq_Ioc_pred j, dyadicBlock_eq_Ioc_pred k]
  have h := TypeII.norm_reciprocalBilinearSum_Ioc_le_near_far
    x y y' (2 ^ j - 1) (2 ^ (j + 1) - 1)
      (2 ^ k - 1) (2 ^ (k + 1) - 1) T alpha beta hx hdyadic
  simpa only [dyadicNearFarFactor, dyadicBlock_eq_Ioc_pred, hjdiff, hkdiff]
    using h

/-- A power-block rectangle can meet the product interval `(y,y']` only if
its exclusive upper product is above `y` and its inclusive lower product is
at most `y'`. -/
def blockActive (y y' j k : ℕ) : Prop :=
  y < 2 ^ (j + 1) * 2 ^ (k + 1) ∧ 2 ^ j * 2 ^ k ≤ y'

instance blockActiveDecidable (y y' j k : ℕ) : Decidable (blockActive y y' j k) :=
  by
    unfold blockActive
    infer_instance

/-- An active block has lower product at most `y'`. -/
theorem blockActive_lower_product_le
    {y y' j k : ℕ} (h : blockActive y y' j k) :
    2 ^ j * 2 ^ k ≤ y' := h.2

/-- An active block also has lower product greater than `y/4`; the factor
four is the ratio between the exclusive upper and inclusive lower products
of two power blocks. -/
theorem blockActive_y_lt_four_mul_lower_product
    {y y' j k : ℕ} (h : blockActive y y' j k) :
    y < 4 * (2 ^ j * 2 ^ k) := by
  calc
    y < 2 ^ (j + 1) * 2 ^ (k + 1) := h.1
    _ = 4 * (2 ^ j * 2 ^ k) := by
      rw [pow_succ, pow_succ]
      ring

/-- An inactive power rectangle contributes exactly zero to the
product-restricted reciprocal bilinear sum. -/
theorem reciprocalBilinearSum_dyadic_eq_zero_of_not_blockActive
    (y y' j k : ℕ) (x : ℝ) (alpha beta : ℕ → ℂ)
    (hinactive : ¬ blockActive y y' j k) :
    TypeII.reciprocalBilinearSum (Finset.Ioc y y')
        (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x alpha beta = 0 := by
  rw [TypeII.reciprocalBilinearSum_eq]
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  have huI := TypeI.mem_dyadicBlock.mp hu
  have hvI := TypeI.mem_dyadicBlock.mp hv
  have hvpos : 0 < v :=
    lt_of_lt_of_le (pow_pos (by norm_num) k) hvI.1
  have huppos : 0 < 2 ^ (j + 1) := pow_pos (by norm_num) (j + 1)
  have huvUpper : u * v < 2 ^ (j + 1) * 2 ^ (k + 1) := by
    calc
      u * v < 2 ^ (j + 1) * v :=
        (Nat.mul_lt_mul_right hvpos).2 huI.2
      _ < 2 ^ (j + 1) * 2 ^ (k + 1) :=
        (Nat.mul_lt_mul_left huppos).2 hvI.2
  have huvLower : 2 ^ j * 2 ^ k ≤ u * v :=
    Nat.mul_le_mul huI.1 hvI.1
  have hnotmem : u * v ∉ Finset.Ioc y y' := by
    intro hmem
    have hmem' := Finset.mem_Ioc.mp hmem
    rcases not_and_or.mp hinactive with hlow | hupp
    · have : 2 ^ (j + 1) * 2 ^ (k + 1) ≤ y := Nat.le_of_not_gt hlow
      omega
    · have : y' < 2 ^ j * 2 ^ k := Nat.lt_of_not_ge hupp
      omega
  rw [if_neg hnotmem]

/-- Orient a dyadic rectangle so the larger power block is the first
variable (the reciprocal-summation variable), using the supplied diagonal
threshold. -/
noncomputable def orientedDyadicNearFarFactorAt
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) : ℝ :=
  if j < k then
    dyadicNearFarFactor x y y' k j T beta alpha
  else
    dyadicNearFarFactor x y y' j k T alpha beta

/-- Premise-free near--far estimate with the larger of the two blocks
chosen as the reciprocal-summation variable and arbitrary threshold. -/
theorem norm_reciprocalBilinearSum_dyadic_le_oriented_at
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) (hx : 0 < x) :
    ‖TypeII.reciprocalBilinearSum (Finset.Ioc y y')
        (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x alpha beta‖ ≤
      orientedDyadicNearFarFactorAt x y y' j k T alpha beta := by
  by_cases hjk : j < k
  · rw [TypeII.reciprocalBilinearSum_comm]
    rw [orientedDyadicNearFarFactorAt, if_pos hjk]
    exact norm_reciprocalBilinearSum_dyadic_le_near_far
      x y y' k j T beta alpha hx
  · rw [orientedDyadicNearFarFactorAt, if_neg hjk]
    exact norm_reciprocalBilinearSum_dyadic_le_near_far
      x y y' j k T alpha beta hx

/-- Active-block version of the oriented bound with arbitrary threshold. -/
theorem norm_reciprocalBilinearSum_dyadic_le_oriented_active_at
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) (hx : 0 < x) :
    ‖TypeII.reciprocalBilinearSum (Finset.Ioc y y')
        (TypeI.dyadicBlock j) (TypeI.dyadicBlock k) x alpha beta‖ ≤
      if blockActive y y' j k then
        orientedDyadicNearFarFactorAt x y y' j k T alpha beta
      else 0 := by
  by_cases hactive : blockActive y y' j k
  · rw [if_pos hactive]
    exact norm_reciprocalBilinearSum_dyadic_le_oriented_at
      x y y' j k T alpha beta hx
  · rw [if_neg hactive,
      reciprocalBilinearSum_dyadic_eq_zero_of_not_blockActive
        y y' j k x alpha beta hactive, norm_zero]

end VaughanTypeIIDyadic

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/VaughanTypeIICoefficients.lean` -/

section
/- leanprover/lean4:v4.33.0 -/

/-!
# Explicit coefficient majorants for the dyadic Vaughan Type-II sums

This file removes the coefficient norms from the oriented active-block
estimates.  What remains in each block is the explicit near--far analytic
factor multiplied by square roots of the concrete `a`, `b`, von Mangoldt,
and constant-sequence mass bounds.
-/

noncomputable section

namespace VaughanTypeIICoefficients

open scoped BigOperators

open VaughanTypeIIDyadic

/-- The square-root term in the dyadic near--far estimate, separated from
the two coefficient norms. -/
noncomputable def dyadicAnalyticFactor
    (x : ℝ) (y y' j k T : ℕ) : ℝ :=
  Real.sqrt
    (2 * (2 ^ j : ℕ) * (2 * T + 1) +
      TypeII.threeBranchFarQ x y y'
        (2 ^ j - 1) (2 ^ (j + 1) - 1)
        (2 ^ k - 1) (2 ^ (k + 1) - 1) T * (2 ^ k : ℕ))

theorem dyadicNearFarFactor_eq
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) :
    dyadicNearFarFactor x y y' j k T alpha beta =
      TypeII.l2Norm (TypeI.dyadicBlock j) alpha *
        dyadicAnalyticFactor x y y' j k T *
          TypeII.l2Norm (TypeI.dyadicBlock k) beta := rfl

/-- A nonnegative quantity whose square is at most `C` is at most
`sqrt C`. -/
lemma le_sqrt_of_nonneg_of_sq_le {a C : ℝ}
    (_ha : 0 ≤ a) (h : a ^ 2 ≤ C) : a ≤ Real.sqrt C := by
  have hC : 0 ≤ C := (sq_nonneg a).trans h
  have hsqrt := Real.sq_sqrt hC
  have hsqrt0 := Real.sqrt_nonneg C
  nlinarith

lemma l2Norm_nonneg (s : Finset ℕ) (a : ℕ → ℂ) :
    0 ≤ TypeII.l2Norm s a := by
  unfold TypeII.l2Norm
  exact Real.sqrt_nonneg _

/-- The masked constant-one sequence has squared mass at most the size of
the full dyadic block. -/
theorem l2Norm_restrict_one_dyadicBlock_sq_le
    (support : Finset ℕ) (j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (restrictCoeff support (fun _ => (1 : ℂ))) ^ 2 ≤
      (2 ^ j : ℕ) := by
  rw [TypeII.l2Norm_sq]
  calc
    (∑ n ∈ TypeI.dyadicBlock j,
        ‖restrictCoeff support (fun _ => (1 : ℂ)) n‖ ^ 2) ≤
        ∑ _n ∈ TypeI.dyadicBlock j, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hns : n ∈ support
      · simp [restrictCoeff, hns]
      · simp [restrictCoeff, hns]
    _ = (2 ^ j : ℕ) := by
      simp [TypeI.card_dyadicBlock]

/-- Replace both coefficient norms in the oriented near--far factor by
arbitrary proved squared-mass bounds. -/
theorem orientedDyadicNearFarFactor_le_of_l2_sq
    (x : ℝ) (y y' j k T : ℕ) (alpha beta : ℕ → ℂ) (A B : ℝ)
    (hA : TypeII.l2Norm (TypeI.dyadicBlock j) alpha ^ 2 ≤ A)
    (hB : TypeII.l2Norm (TypeI.dyadicBlock k) beta ^ 2 ≤ B) :
    orientedDyadicNearFarFactorAt x y y' j k T alpha beta ≤
      if j < k then
        Real.sqrt B * dyadicAnalyticFactor x y y' k j T * Real.sqrt A
      else
        Real.sqrt A * dyadicAnalyticFactor x y y' j k T * Real.sqrt B := by
  have hAlpha : TypeII.l2Norm (TypeI.dyadicBlock j) alpha ≤ Real.sqrt A :=
    le_sqrt_of_nonneg_of_sq_le (l2Norm_nonneg _ _) hA
  have hBeta : TypeII.l2Norm (TypeI.dyadicBlock k) beta ≤ Real.sqrt B :=
    le_sqrt_of_nonneg_of_sq_le (l2Norm_nonneg _ _) hB
  by_cases hjk : j < k
  · simp only [orientedDyadicNearFarFactorAt, hjk, if_pos,
      dyadicNearFarFactor_eq]
    have hroot : 0 ≤ dyadicAnalyticFactor x y y' k j T := by
      unfold dyadicAnalyticFactor
      positivity
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right hBeta hroot) hAlpha
      (l2Norm_nonneg _ _) (mul_nonneg (Real.sqrt_nonneg _) hroot)
  · simp only [orientedDyadicNearFarFactorAt, hjk,
      dyadicNearFarFactor_eq]
    have hroot : 0 ≤ dyadicAnalyticFactor x y y' j k T := by
      unfold dyadicAnalyticFactor
      positivity
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right hAlpha hroot) hBeta
      (l2Norm_nonneg _ _) (mul_nonneg (Real.sqrt_nonneg _) hroot)

/-- The explicit coefficient-replaced block majorant for `Σ₂,₂`. -/
noncomputable def sigma22OrientedBlockMajorant
    (x : ℝ) (y y' j k T : ℕ) : ℝ :=
  let bMass := (2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2
  let oneMass : ℝ := (2 ^ k : ℕ)
  if j < k then
    Real.sqrt oneMass * dyadicAnalyticFactor x y y' k j T *
      Real.sqrt bMass
  else
    Real.sqrt bMass * dyadicAnalyticFactor x y y' j k T *
      Real.sqrt oneMass

/-- The explicit coefficient-replaced block majorant for `Σ₃`. -/
noncomputable def sigma3OrientedBlockMajorant
    (x : ℝ) (y y' M j k T : ℕ) : ℝ :=
  let aMass :=
    (8 / 9 : ℝ) * (2 ^ j : ℕ) * (Real.log M + 3) ^ 3 + 1
  let lambdaMass :=
    (2 ^ k : ℕ) * Real.log (2 * (2 ^ k : ℕ)) ^ 2
  if j < k then
    Real.sqrt lambdaMass * dyadicAnalyticFactor x y y' k j T *
      Real.sqrt aMass
  else
    Real.sqrt aMass * dyadicAnalyticFactor x y y' j k T *
      Real.sqrt lambdaMass

theorem sigma22_orientedFactor_le_majorant
    (y y' M K j k T : ℕ) (x : ℝ) :
    orientedDyadicNearFarFactorAt x y y' j k T
        (restrictCoeff (Finset.Ioc M (M * K))
          (fun r => (VaughanFourSums.bCoeff M K r : ℂ)))
        (restrictCoeff (Finset.Icc 1 y') (fun _ => 1)) ≤
      sigma22OrientedBlockMajorant x y y' j k T := by
  simpa only [sigma22OrientedBlockMajorant] using
    orientedDyadicNearFarFactor_le_of_l2_sq x y y' j k T _ _
      ((2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2)
      (2 ^ k : ℕ)
      (l2Norm_restrict_bCoeff_dyadicBlock_sq_le
        (Finset.Ioc M (M * K)) M K j)
      (l2Norm_restrict_one_dyadicBlock_sq_le (Finset.Icc 1 y') k)

theorem sigma3_orientedFactor_le_majorant
    (y y' M K j k T : ℕ) (x : ℝ) (hM : 1 ≤ M) :
    orientedDyadicNearFarFactorAt x y y' j k T
        (restrictCoeff (Finset.Ioc M y')
          (fun l => (VaughanFourSums.aCoeff M l : ℂ)))
        (restrictCoeff (Finset.Ioc K y')
          (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))) ≤
      sigma3OrientedBlockMajorant x y y' M j k T := by
  simpa only [sigma3OrientedBlockMajorant] using
    orientedDyadicNearFarFactor_le_of_l2_sq x y y' j k T _ _
      ((8 / 9 : ℝ) * (2 ^ j : ℕ) * (Real.log M + 3) ^ 3 + 1)
      ((2 ^ k : ℕ) * Real.log (2 * (2 ^ k : ℕ)) ^ 2)
      (l2Norm_restrict_aCoeff_dyadicBlock_sq_le
        (Finset.Ioc M y') M j hM)
      (l2Norm_restrict_vonMangoldt_dyadicBlock_sq_le
        (Finset.Ioc K y') k)

/-! ## Support-sensitive coefficient majorants

The coarse coefficient estimates above remain positive even when a power
block misses the original Vaughan support.  Keeping this elementary support
information is essential in the quantitative Type-II application: it gives
a lower bound for the smaller of the two oriented block scales. -/

/-- A reciprocal bilinear block vanishes when its first coefficient is zero
on the first support. -/
theorem reciprocalBilinearSum_eq_zero_of_left
    (I us vs : Finset ℕ) (x : ℝ) (alpha beta : ℕ → ℂ)
    (hzero : ∀ u ∈ us, alpha u = 0) :
    TypeII.reciprocalBilinearSum I us vs x alpha beta = 0 := by
  unfold TypeII.reciprocalBilinearSum TypeII.bilinearSum
  apply Finset.sum_eq_zero
  intro u hu
  rw [hzero u hu, zero_mul]

/-- A reciprocal bilinear block vanishes when its second coefficient is zero
on the second support. -/
theorem reciprocalBilinearSum_eq_zero_of_right
    (I us vs : Finset ℕ) (x : ℝ) (alpha beta : ℕ → ℂ)
    (hzero : ∀ v ∈ vs, beta v = 0) :
    TypeII.reciprocalBilinearSum I us vs x alpha beta = 0 := by
  unfold TypeII.reciprocalBilinearSum TypeII.bilinearSum TypeII.innerSum
  apply Finset.sum_eq_zero
  intro u hu
  rw [show (∑ v ∈ vs,
      beta v * TypeII.restrictedReciprocalKernel I x u v) = 0 by
    apply Finset.sum_eq_zero
    intro v hv
    rw [hzero v hv, zero_mul]]
  simp

/-- A block below the lower endpoint of an `Ioc` coefficient support carries
only zero restricted coefficients. -/
theorem restrictCoeff_Ioc_eq_zero_on_dyadicBlock_of_upper_le
    (L R j : ℕ) (a : ℕ → ℂ) (hupper : 2 ^ (j + 1) ≤ L) :
    ∀ n ∈ TypeI.dyadicBlock j,
      restrictCoeff (Finset.Ioc L R) a n = 0 := by
  intro n hn
  apply restrictCoeff_of_not_mem
  have hnlt := (TypeI.mem_dyadicBlock.mp hn).2
  simp only [Finset.mem_Ioc, not_and_or]
  left
  omega

/-- `Σ₂,₂` block support: the `b`-coefficient block must reach above
the strict lower endpoint `M`. -/
def sigma22SupportActive (M j : ℕ) : Prop := M < 2 ^ (j + 1)

instance sigma22SupportActiveDecidable (M j : ℕ) :
    Decidable (sigma22SupportActive M j) := by
  unfold sigma22SupportActive
  infer_instance

/-- `Σ₃` block support: both coefficient blocks must reach above their
strict lower endpoints. -/
def sigma3SupportActive (M K j k : ℕ) : Prop :=
  M < 2 ^ (j + 1) ∧ K < 2 ^ (k + 1)

instance sigma3SupportActiveDecidable (M K j k : ℕ) :
    Decidable (sigma3SupportActive M K j k) := by
  unfold sigma3SupportActive
  infer_instance

/-- Larger power scale after orienting a dyadic rectangle. -/
def orientedLargeScale (j k : ℕ) : ℕ :=
  if j < k then 2 ^ k else 2 ^ j

/-- Smaller power scale after orienting a dyadic rectangle. -/
def orientedSmallScale (j k : ℕ) : ℕ :=
  if j < k then 2 ^ j else 2 ^ k

@[simp] theorem orientedLargeScale_mul_orientedSmallScale (j k : ℕ) :
    orientedLargeScale j k * orientedSmallScale j k = 2 ^ j * 2 ^ k := by
  by_cases hjk : j < k <;>
    simp [orientedLargeScale, orientedSmallScale, hjk, Nat.mul_comm]

theorem orientedSmallScale_le_orientedLargeScale (j k : ℕ) :
    orientedSmallScale j k ≤ orientedLargeScale j k := by
  by_cases hjk : j < k
  · simp only [orientedSmallScale, orientedLargeScale, hjk, if_pos]
    exact Nat.pow_le_pow_right (by norm_num) hjk.le
  · simp only [orientedSmallScale, orientedLargeScale, hjk, if_neg]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_gt hjk)

@[simp] theorem orientedLargeScale_pos (j k : ℕ) :
    0 < orientedLargeScale j k := by
  by_cases hjk : j < k <;>
    simp [orientedLargeScale, hjk, pow_pos]

@[simp] theorem orientedSmallScale_pos (j k : ℕ) :
    0 < orientedSmallScale j k := by
  by_cases hjk : j < k <;>
    simp [orientedSmallScale, hjk, pow_pos]

/-- Every dyadic block index used to cover a nonempty initial interval has
lower endpoint at most that interval's endpoint. -/
theorem two_pow_le_of_mem_range_dyadicCount
    {N j : ℕ} (hN : N ≠ 0)
    (hj : j ∈ Finset.range (TypeI.dyadicCount N)) :
    2 ^ j ≤ N := by
  have hjlog : j ≤ Nat.log 2 N := by
    have hj' : j < Nat.log 2 N + 1 := by
      simpa only [Finset.mem_range, TypeI.dyadicCount] using hj
    omega
  exact (Nat.pow_le_pow_right (by norm_num) hjlog).trans
    (Nat.pow_log_le_self 2 hN)

/-- On a support-active `Σ₃` block, the smaller oriented scale reaches
half of any common lower bound for `M` and `K`. -/
theorem sigma3SupportActive_lt_two_mul_orientedSmallScale
    {L M K j k : ℕ} (hLM : L ≤ M) (hLK : L ≤ K)
    (hs : sigma3SupportActive M K j k) :
    L < 2 * orientedSmallScale j k := by
  rcases hs with ⟨hsj, hsk⟩
  by_cases hjk : j < k
  · simpa [orientedSmallScale, hjk, pow_succ, Nat.mul_comm] using
      hLM.trans_lt hsj
  · simpa [orientedSmallScale, hjk, pow_succ, Nat.mul_comm] using
      hLK.trans_lt hsk

/-- Product activity, orientation, and a large first scale imply the simple
upper-frequency hypothesis needed by the closed far-correlation estimate.
The generous cutoff `2304` keeps this entirely polynomial. -/
theorem honeScale_of_active_oriented
    {x : ℝ} {y U V : ℕ}
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2)
    (hU : 2304 ≤ U) (hV : 0 < V) (hVU : V ≤ U)
    (hproduct : y < 4 * (U * V)) :
    12 * (x / (V : ℝ)) ≤ (U : ℝ) ^ 4 := by
  have hVreal : 0 < (V : ℝ) := by exact_mod_cast hV
  have hproductR : (y : ℝ) ≤ 4 * (U : ℝ) * V := by
    have hproductR' : (y : ℝ) ≤ ((4 * (U * V) : ℕ) : ℝ) := by
      exact_mod_cast hproduct.le
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hproductR'
    simpa only [mul_assoc] using hproductR'
  have hUreal : (2304 : ℝ) ≤ U := by exact_mod_cast hU
  have hVUreal : (V : ℝ) ≤ U := by exact_mod_cast hVU
  have hyU : (y : ℝ) ≤ 4 * (U : ℝ) ^ 2 := by
    calc
      (y : ℝ) ≤ 4 * (U : ℝ) * V := hproductR
      _ ≤ 4 * (U : ℝ) * U := by gcongr
      _ = 4 * (U : ℝ) ^ 2 := by ring
  have hU3 : 576 * (y : ℝ) ≤ (U : ℝ) ^ 3 := by
    calc
      576 * (y : ℝ) ≤ 576 * (4 * (U : ℝ) ^ 2) := by gcongr
      _ = 2304 * (U : ℝ) ^ 2 := by ring
      _ ≤ (U : ℝ) * (U : ℝ) ^ 2 := by gcongr
      _ = (U : ℝ) ^ 3 := by ring
  have hy2 : 144 * (y : ℝ) ^ 2 ≤
      (U : ℝ) ^ 4 * V := by
    have hmulProduct :
        0 ≤ (y : ℝ) * (4 * (U : ℝ) * V - (y : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg y) (sub_nonneg.mpr hproductR)
    have hfirst : 144 * (y : ℝ) ^ 2 ≤
        144 * (y : ℝ) * (4 * (U : ℝ) * V) := by
      nlinarith
    have hsecond : (576 * (y : ℝ)) * ((U : ℝ) * V) ≤
        (U : ℝ) ^ 3 * ((U : ℝ) * V) :=
      mul_le_mul_of_nonneg_right hU3 (by positivity)
    calc
      144 * (y : ℝ) ^ 2 ≤
          144 * (y : ℝ) * (4 * (U : ℝ) * V) := hfirst
      _ = (576 * (y : ℝ)) * ((U : ℝ) * V) := by ring
      _ ≤ (U : ℝ) ^ 3 * ((U : ℝ) * V) := hsecond
      _ = (U : ℝ) ^ 4 * V := by ring
  have hxscaled : 12 * x ≤ (U : ℝ) ^ 4 * V := by
    calc
      12 * x ≤ 144 * (y : ℝ) ^ 2 := by nlinarith
      _ ≤ (U : ℝ) ^ 4 * V := hy2
  rw [show 12 * (x / (V : ℝ)) = (12 * x) / V by ring,
    div_le_iff₀ hVreal]
  simpa [mul_comm] using hxscaled

/-- Replace the finite far-pair maximum in the zero-threshold analytic
factor by the closed oriented power-block expression. -/
theorem dyadicAnalyticFactor_zero_le_orientedPowerBlockFarQ
    (x : ℝ) (y y' j k : ℕ) (hx : 0 < x)
    (hhoneScale :
      12 * (x / ((2 ^ k : ℕ) : ℝ)) ≤ (((2 ^ j : ℕ) : ℝ)) ^ 4) :
    dyadicAnalyticFactor x y y' j k 0 ≤
      Real.sqrt
        (2 * ((2 ^ j : ℕ) : ℝ) +
          TypeII.orientedPowerBlockFarQ x (2 ^ j) (2 ^ k) *
            ((2 ^ k : ℕ) : ℝ)) := by
  have hQ := TypeII.threeBranchFarQ_powerBlock_zero_le
    x y y' (2 ^ j) (2 ^ k) hx
      (pow_pos (by norm_num) j) (pow_pos (by norm_num) k) hhoneScale
  unfold dyadicAnalyticFactor
  apply Real.sqrt_le_sqrt
  norm_num only [Nat.cast_pow, Nat.cast_ofNat, mul_one]
  have hk0 : 0 ≤ (((2 ^ k : ℕ) : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hQ hk0
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hmul
  simpa only [pow_succ, Nat.mul_comm, add_comm] using
    add_le_add_left hmul (2 * (2 : ℝ) ^ j)

/-- Sharp form of the common-support scale calculation used after the
power-of-two Vaughan specialization. -/
theorem orientedLargeScale_cube_le_of_common_lower
    {c y y' M U V : ℕ} (hy : 0 < y) (hy' : y' ≤ 2 * y)
    (hyM : y ≤ c * M ^ 3) (hsmall : M ≤ 2 * V)
    (hUV : U * V ≤ y') :
    U ^ 3 ≤ (64 * c) * y ^ 2 := by
  have hMU : M * U ≤ 4 * y := by
    calc
      M * U ≤ (2 * V) * U := Nat.mul_le_mul_right U hsmall
      _ = 2 * (U * V) := by ring
      _ ≤ 2 * y' := Nat.mul_le_mul_left 2 hUV
      _ ≤ 4 * y := by omega
  have hcube := Nat.pow_le_pow_left hMU 3
  have hMUcube : M ^ 3 * U ^ 3 ≤ 64 * y ^ 3 := by
    calc
      M ^ 3 * U ^ 3 = (M * U) ^ 3 := by ring
      _ ≤ (4 * y) ^ 3 := hcube
      _ = 64 * y ^ 3 := by ring
  have hscaled : y * U ^ 3 ≤ y * ((64 * c) * y ^ 2) := by
    calc
      y * U ^ 3 ≤ (c * M ^ 3) * U ^ 3 :=
        Nat.mul_le_mul_right (U ^ 3) hyM
      _ = c * (M ^ 3 * U ^ 3) := by ring
      _ ≤ c * (64 * y ^ 3) := Nat.mul_le_mul_left c hMUcube
      _ = y * ((64 * c) * y ^ 2) := by ring
  exact Nat.le_of_mul_le_mul_left hscaled hy

/-- With `y ≤ 8 M³`, every support-active `Σ₃` block has the exact
cube bound consumed by `TypeIIScalar`. -/
theorem sigma3_orientedLargeScale_cube_le_512
    {y y' M j k : ℕ} (hy : 0 < y) (hy' : y' ≤ 2 * y)
    (hyM : y ≤ 8 * M ^ 3)
    (hactive : blockActive y y' j k)
    (hs : sigma3SupportActive M M j k) :
    orientedLargeScale j k ^ 3 ≤ 512 * y ^ 2 := by
  apply orientedLargeScale_cube_le_of_common_lower
    (c := 8) hy hy' hyM
  · exact (sigma3SupportActive_lt_two_mul_orientedSmallScale
      (L := M) (M := M) (K := M) (j := j) (k := k)
      le_rfl le_rfl hs).le
  · rw [orientedLargeScale_mul_orientedSmallScale]
    exact blockActive_lower_product_le hactive

/-- The analogous exact cube bound for support-active `Σ₂,₂`
blocks. -/
theorem sigma22_orientedLargeScale_cube_le_512
    {y y' M j k : ℕ} (hy : 0 < y) (hy' : y' ≤ 2 * y)
    (hylow : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hj : j ∈ Finset.range (TypeI.dyadicCount (M * M)))
    (hactive : blockActive y y' j k)
    (hs : sigma22SupportActive M j) :
    orientedLargeScale j k ^ 3 ≤ 512 * y ^ 2 := by
  by_cases hjk : j < k
  · apply orientedLargeScale_cube_le_of_common_lower
      (c := 8) (M := M) (U := orientedLargeScale j k)
        (V := orientedSmallScale j k) hy hy' hyM
    · simpa [sigma22SupportActive, orientedSmallScale, hjk, pow_succ,
        Nat.mul_comm] using hs.le
    · rw [orientedLargeScale_mul_orientedSmallScale]
      exact blockActive_lower_product_le hactive
  · have hM : 0 < M := by
      by_contra hnot
      have : M = 0 := Nat.eq_zero_of_not_pos hnot
      subst M
      simp at hyM
      omega
    have hMM : M * M ≠ 0 := mul_ne_zero hM.ne' hM.ne'
    have hU : orientedLargeScale j k ≤ M ^ 2 := by
      simp only [orientedLargeScale, hjk, if_neg]
      simpa [pow_two] using
        two_pow_le_of_mem_range_dyadicCount hMM hj
    have hcube := Nat.pow_le_pow_left hU 3
    calc
      orientedLargeScale j k ^ 3 ≤ (M ^ 2) ^ 3 := hcube
      _ = (M ^ 3) ^ 2 := by ring
      _ ≤ y ^ 2 := Nat.pow_le_pow_left hylow 2
      _ ≤ 512 * y ^ 2 := by nlinarith

/-- Actual `Σ₂,₂` with both product activity and the original
`b`-coefficient support retained in the explicit majorant. -/
theorem norm_sigma22_le_sum_dyadic_coefficient_majorant_supported
    (y y' M K : ℕ) (x : ℝ) (hx : 0 < x) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount (M * K)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k ∧ sigma22SupportActive M j then
            sigma22OrientedBlockMajorant x y y' j k 0
          else 0 := by
  apply norm_sigma22_le_sum_dyadic_of_block
  intro j hj k hk
  by_cases hactive : blockActive y y' j k
  · by_cases hs : sigma22SupportActive M j
    · simp only [hactive, hs, and_self, if_pos]
      exact (norm_reciprocalBilinearSum_dyadic_le_oriented_active_at
        x y y' j k 0 _ _ hx).trans (by
          simp only [hactive, if_pos]
          exact sigma22_orientedFactor_le_majorant y y' M K j k 0 x)
    · have hupper : 2 ^ (j + 1) ≤ M := by
        exact Nat.le_of_not_gt hs
      have hzero := restrictCoeff_Ioc_eq_zero_on_dyadicBlock_of_upper_le
        M (M * K) j
          (fun r => (VaughanFourSums.bCoeff M K r : ℂ)) hupper
      rw [reciprocalBilinearSum_eq_zero_of_left _ _ _ _ _ _ hzero,
        norm_zero]
      simp [hs]
  · rw [VaughanTypeIIDyadic.reciprocalBilinearSum_dyadic_eq_zero_of_not_blockActive
      y y' j k x _ _ hactive, norm_zero]
    simp [hactive]

/-- Actual `Σ₃` with both original strict lower coefficient supports
retained in the explicit majorant. -/
theorem norm_sigma3_le_sum_dyadic_coefficient_majorant_supported
    (y y' M K : ℕ) (x : ℝ) (hx : 0 < x) (hM : 1 ≤ M) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M K‖ ≤
      ∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k ∧ sigma3SupportActive M K j k then
            sigma3OrientedBlockMajorant x y y' M j k 0
          else 0 := by
  apply norm_sigma3_le_sum_dyadic_of_block
  intro j hj k hk
  by_cases hactive : blockActive y y' j k
  · by_cases hs : sigma3SupportActive M K j k
    · simp only [hactive, hs, and_self, if_pos]
      exact (norm_reciprocalBilinearSum_dyadic_le_oriented_active_at
        x y y' j k 0 _ _ hx).trans (by
          simp only [hactive, if_pos]
          exact sigma3_orientedFactor_le_majorant y y' M K j k 0 x hM)
    · rcases not_and_or.mp hs with hsj | hsk
      · have hupper : 2 ^ (j + 1) ≤ M := Nat.le_of_not_gt hsj
        have hzero := restrictCoeff_Ioc_eq_zero_on_dyadicBlock_of_upper_le
          M y' j (fun l => (VaughanFourSums.aCoeff M l : ℂ)) hupper
        rw [reciprocalBilinearSum_eq_zero_of_left _ _ _ _ _ _ hzero,
          norm_zero]
        simp [hs]
      · have hupper : 2 ^ (k + 1) ≤ K := Nat.le_of_not_gt hsk
        have hzero := restrictCoeff_Ioc_eq_zero_on_dyadicBlock_of_upper_le
          K y' k
            (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) hupper
        rw [reciprocalBilinearSum_eq_zero_of_right _ _ _ _ _ _ hzero,
          norm_zero]
        simp [hs]
  · rw [VaughanTypeIIDyadic.reciprocalBilinearSum_dyadic_eq_zero_of_not_blockActive
      y y' j k x _ _ hactive, norm_zero]
    simp [hactive]

end VaughanTypeIICoefficients

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/TypeIICoefficientCollapse.lean` -/

section
/- leanprover/lean4:v4.33.0 -/

/-!
# Closed coefficient bounds for the Vaughan Type-II blocks

This file is deliberately independent of the proof of the analytic
near--far estimate.  It turns a bound for `dyadicAnalyticFactor` on an
active oriented rectangle into a closed `y^(27/28)` bound for each of the
two coefficient majorants.
-/

noncomputable section

namespace TypeIICoefficientCollapse

open Erdos175.VaughanTypeIIDyadic
open Erdos175.VaughanTypeIICoefficients

private lemma rpow_half_mul_rpow_thirteen_twentyEight
    {y : ℝ} (hy : 0 < y) :
    y ^ (1 / 2 : ℝ) * y ^ (13 / 28 : ℝ) = y ^ (27 / 28 : ℝ) := by
  rw [← Real.rpow_add hy]
  norm_num

/-! The next two lemmas contain all coefficient-specific algebra. -/

/-- A constant block paired with a logarithmically weighted block costs at
most `2 sqrt(y) H³` when the product of their dyadic scales is at most
`2y`.  The third power of `H` is intentionally generous, so that both
Type-II coefficient families share one final log exponent. -/
lemma sqrt_const_mul_sqrt_logMass_le
    {y A B : ℕ} {H : ℝ}
    (hy : 0 < y) (hA : 0 < A) (hB : 0 < B)
    (hAB : A * B ≤ 2 * y) (hH : 1 ≤ H)
    (hlog : Real.log (2 * (A : ℝ)) ≤ H) :
    Real.sqrt B *
        Real.sqrt ((A : ℝ) * Real.log (2 * (A : ℝ)) ^ 2) ≤
      2 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3 := by
  let ell := Real.log (2 * (A : ℝ))
  let c := Real.sqrt B * Real.sqrt ((A : ℝ) * ell ^ 2)
  have hell0 : 0 ≤ ell := by
    dsimp only [ell]
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast (show 1 ≤ 2 * A by omega)
    exact this
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hellsq : ell ^ 2 ≤ H ^ 2 := by
    have hell : ell ≤ H := by simpa only [ell] using hlog
    nlinarith
  have hABR : (A : ℝ) * B ≤ 2 * (y : ℝ) := by
    exact_mod_cast hAB
  have hmass0 : 0 ≤ (A : ℝ) * ell ^ 2 := by positivity
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hcsq : c ^ 2 = ((A : ℝ) * B) * ell ^ 2 := by
    dsimp only [c]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (B : ℝ)),
      Real.sq_sqrt hmass0]
    ring
  have hcsq_le : c ^ 2 ≤ 2 * (y : ℝ) * H ^ 2 := by
    rw [hcsq]
    gcongr
  have hyr0 : 0 ≤ (y : ℝ) := by positivity
  have hyrpow : ((y : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (y : ℝ) := by
    rw [← Real.rpow_mul_natCast hyr0]
    norm_num [Real.rpow_one]
  have htargetsq :
      c ^ 2 ≤ (2 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) ^ 2 := by
    have htarget :
        (2 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) ^ 2 =
          4 * (y : ℝ) * H ^ 6 := by
      rw [mul_pow, mul_pow, hyrpow]
      ring
    rw [htarget]
    calc
      c ^ 2 ≤ 2 * (y : ℝ) * H ^ 2 := hcsq_le
      _ ≤ 4 * (y : ℝ) * H ^ 6 := by gcongr <;> norm_num
  change c ≤ _
  have ht0 : 0 ≤ 2 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3 := by positivity
  nlinarith

/-- The shifted Möbius-convolution mass paired with a von Mangoldt mass
costs at most `4 sqrt(y) H³`.  Here `A` is the scale carrying the shifted
coefficient and `B` the scale carrying von Mangoldt. -/
lemma sqrt_lambdaMass_mul_sqrt_aMass_le
    {y M A B : ℕ} {H : ℝ}
    (hy : 0 < y) (hM : 1 ≤ M) (hA : 0 < A) (hB : 0 < B)
    (hAB : A * B ≤ 2 * y) (hH : 1 ≤ H)
    (hlogScale : Real.log (2 * (B : ℝ)) ≤ H)
    (hlogM : Real.log M + 3 ≤ H) :
    Real.sqrt ((B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2) *
        Real.sqrt ((8 / 9 : ℝ) * (A : ℝ) *
          (Real.log M + 3) ^ 3 + 1) ≤
      4 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3 := by
  let ell := Real.log (2 * (B : ℝ))
  let mu := Real.log M + 3
  let lambdaMass : ℝ := B * ell ^ 2
  let aMass : ℝ := (8 / 9 : ℝ) * A * mu ^ 3 + 1
  let c := Real.sqrt lambdaMass * Real.sqrt aMass
  have hell0 : 0 ≤ ell := by
    dsimp only [ell]
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ 2 * (B : ℝ) := by exact_mod_cast (show 1 ≤ 2 * B by omega)
    exact this
  have hmu0 : 0 ≤ mu := by
    dsimp only [mu]
    have hlogM0 : 0 ≤ Real.log (M : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast hM
    linarith
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hellsq : ell ^ 2 ≤ H ^ 2 := by
    have hell : ell ≤ H := by simpa only [ell] using hlogScale
    nlinarith
  have hmu3 : mu ^ 3 ≤ H ^ 3 := by
    have hmule : mu ≤ H := by simpa only [mu] using hlogM
    exact pow_le_pow_left₀ hmu0 hmule 3
  have hABR : (A : ℝ) * B ≤ 2 * (y : ℝ) := by exact_mod_cast hAB
  have hBle : (B : ℝ) ≤ 2 * (y : ℝ) := by
    have hAle : (1 : ℝ) ≤ A := by exact_mod_cast hA
    nlinarith [mul_nonneg (sub_nonneg.mpr hAle) (by positivity : 0 ≤ (B : ℝ))]
  have hlambda0 : 0 ≤ lambdaMass := by dsimp only [lambdaMass]; positivity
  have ha0 : 0 ≤ aMass := by dsimp only [aMass]; positivity
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hcsq : c ^ 2 = lambdaMass * aMass := by
    dsimp only [c]
    rw [mul_pow, Real.sq_sqrt hlambda0, Real.sq_sqrt ha0]
  have hinner : (B : ℝ) * ((8 / 9 : ℝ) * A * mu ^ 3 + 1) ≤
      4 * (y : ℝ) * H ^ 3 := by
    calc
      (B : ℝ) * ((8 / 9 : ℝ) * A * mu ^ 3 + 1) =
          (8 / 9 : ℝ) * ((A : ℝ) * B) * mu ^ 3 + B := by ring
      _ ≤ (8 / 9 : ℝ) * (2 * (y : ℝ)) * H ^ 3 +
          2 * (y : ℝ) := by gcongr
      _ ≤ 4 * (y : ℝ) * H ^ 3 := by
        have hH3 : 1 ≤ H ^ 3 :=
          by simpa using
            (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hH 3)
        have hyH : (y : ℝ) ≤ (y : ℝ) * H ^ 3 := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hH3 (by positivity : (0 : ℝ) ≤ y)
        nlinarith [mul_nonneg (by positivity : 0 ≤ (y : ℝ))
          (by positivity : 0 ≤ H ^ 3)]
  have hcsq_le : c ^ 2 ≤ 4 * (y : ℝ) * H ^ 5 := by
    rw [hcsq]
    dsimp only [lambdaMass, aMass]
    calc
      (B : ℝ) * ell ^ 2 *
          ((8 / 9 : ℝ) * (A : ℝ) * mu ^ 3 + 1) =
          ell ^ 2 * ((B : ℝ) *
            ((8 / 9 : ℝ) * A * mu ^ 3 + 1)) := by ring
      _ ≤ H ^ 2 * (4 * (y : ℝ) * H ^ 3) := by gcongr
      _ = 4 * (y : ℝ) * H ^ 5 := by ring
  have hyr0 : 0 ≤ (y : ℝ) := by positivity
  have hyrpow : ((y : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (y : ℝ) := by
    rw [← Real.rpow_mul_natCast hyr0]
    norm_num [Real.rpow_one]
  have htargetsq :
      c ^ 2 ≤ (4 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) ^ 2 := by
    have htarget :
        (4 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) ^ 2 =
          16 * (y : ℝ) * H ^ 6 := by
      rw [mul_pow, mul_pow, hyrpow]
      ring
    rw [htarget]
    calc
      c ^ 2 ≤ 4 * (y : ℝ) * H ^ 5 := hcsq_le
      _ ≤ 16 * (y : ℝ) * H ^ 6 := by gcongr <;> norm_num
  change c ≤ _
  have ht0 : 0 ≤ 4 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3 := by positivity
  nlinarith

/-! ### Block-majorant endpoints -/

/-- Coefficient collapse for an active `Σ₂,₂` block. -/
theorem sigma22OrientedBlockMajorant_le_closed
    {x : ℝ} {y y' j k : ℕ} {C H : ℝ}
    (hy : 0 < y) (hy' : y' ≤ 2 * y)
    (hactive : blockActive y y' j k)
    (_hsupport : sigma22SupportActive 1 j)
    (_hC : 0 ≤ C) (hH : 1 ≤ H)
    (hlogLarge : Real.log (2 * (orientedLargeScale j k : ℝ)) ≤ H)
    (hlogSmall : Real.log (2 * (orientedSmallScale j k : ℝ)) ≤ H)
    (hanalytic :
      (if j < k then dyadicAnalyticFactor x y y' k j 0
       else dyadicAnalyticFactor x y y' j k 0) ≤
        C * (y : ℝ) ^ (13 / 28 : ℝ) * H) :
    sigma22OrientedBlockMajorant x y y' j k 0 ≤
      (2 * C) * (y : ℝ) ^ (27 / 28 : ℝ) * H ^ 4 := by
  have hprod : 2 ^ j * 2 ^ k ≤ 2 * y :=
    (blockActive_lower_product_le hactive).trans hy'
  have hf0 : 0 ≤
      (if j < k then dyadicAnalyticFactor x y y' k j 0
       else dyadicAnalyticFactor x y y' j k 0) := by
    split <;> unfold dyadicAnalyticFactor <;> positivity
  have hyr : 0 < (y : ℝ) := by exact_mod_cast hy
  by_cases hjk : j < k
  · have hcoeff := sqrt_const_mul_sqrt_logMass_le
      hy (pow_pos (by omega) j) (pow_pos (by omega) k) hprod hH (by
        simpa [orientedSmallScale, hjk] using hlogSmall)
    simp only [sigma22OrientedBlockMajorant, hjk, if_pos]
    have hf := hanalytic
    simp only [hjk, if_pos] at hf hf0
    calc
      Real.sqrt (2 ^ k : ℕ) * dyadicAnalyticFactor x y y' k j 0 *
          Real.sqrt ((2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2) =
          (Real.sqrt (2 ^ k : ℕ) *
            Real.sqrt ((2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2)) *
              dyadicAnalyticFactor x y y' k j 0 := by ring
      _ ≤ (2 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) *
          (C * (y : ℝ) ^ (13 / 28 : ℝ) * H) :=
        mul_le_mul hcoeff hf hf0 (by positivity)
      _ = (2 * C) * (y : ℝ) ^ (27 / 28 : ℝ) * H ^ 4 := by
        rw [← rpow_half_mul_rpow_thirteen_twentyEight hyr]
        ring
  · have hcoeff := sqrt_const_mul_sqrt_logMass_le
      hy (pow_pos (by omega) j) (pow_pos (by omega) k) hprod hH (by
        simpa [orientedLargeScale, hjk] using hlogLarge)
    simp only [sigma22OrientedBlockMajorant, hjk, if_neg]
    have hf := hanalytic
    simp only [hjk, if_neg] at hf hf0
    calc
      Real.sqrt ((2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2) *
          dyadicAnalyticFactor x y y' j k 0 * Real.sqrt (2 ^ k : ℕ) =
          (Real.sqrt (2 ^ k : ℕ) *
            Real.sqrt ((2 ^ j : ℕ) * Real.log (2 * (2 ^ j : ℕ)) ^ 2)) *
              dyadicAnalyticFactor x y y' j k 0 := by ring
      _ ≤ (2 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) *
          (C * (y : ℝ) ^ (13 / 28 : ℝ) * H) :=
        mul_le_mul hcoeff hf hf0 (by positivity)
      _ = (2 * C) * (y : ℝ) ^ (27 / 28 : ℝ) * H ^ 4 := by
        rw [← rpow_half_mul_rpow_thirteen_twentyEight hyr]
        ring

/-- Coefficient collapse for an active `Σ₃` block. -/
theorem sigma3OrientedBlockMajorant_le_closed
    {x : ℝ} {y y' M j k : ℕ} {C H : ℝ}
    (hy : 0 < y) (hy' : y' ≤ 2 * y) (hM : 1 ≤ M)
    (hactive : blockActive y y' j k)
    (_hsupport : sigma3SupportActive M M j k)
    (_hC : 0 ≤ C) (hH : 1 ≤ H)
    (hlogLarge : Real.log (2 * (orientedLargeScale j k : ℝ)) ≤ H)
    (hlogSmall : Real.log (2 * (orientedSmallScale j k : ℝ)) ≤ H)
    (hlogM : Real.log M + 3 ≤ H)
    (hanalytic :
      (if j < k then dyadicAnalyticFactor x y y' k j 0
       else dyadicAnalyticFactor x y y' j k 0) ≤
        C * (y : ℝ) ^ (13 / 28 : ℝ) * H) :
    sigma3OrientedBlockMajorant x y y' M j k 0 ≤
      (4 * C) * (y : ℝ) ^ (27 / 28 : ℝ) * H ^ 4 := by
  have hprod : 2 ^ j * 2 ^ k ≤ 2 * y :=
    (blockActive_lower_product_le hactive).trans hy'
  have hf0 : 0 ≤
      (if j < k then dyadicAnalyticFactor x y y' k j 0
       else dyadicAnalyticFactor x y y' j k 0) := by
    split <;> unfold dyadicAnalyticFactor <;> positivity
  have hyr : 0 < (y : ℝ) := by exact_mod_cast hy
  by_cases hjk : j < k
  · have hcoeff := sqrt_lambdaMass_mul_sqrt_aMass_le
      hy hM (pow_pos (by omega) j) (pow_pos (by omega) k) hprod hH (by
        simpa [orientedLargeScale, hjk] using hlogLarge) hlogM
    simp only [sigma3OrientedBlockMajorant, hjk, if_pos]
    have hf := hanalytic
    simp only [hjk, if_pos] at hf hf0
    calc
      Real.sqrt ((2 ^ k : ℕ) * Real.log (2 * (2 ^ k : ℕ)) ^ 2) *
          dyadicAnalyticFactor x y y' k j 0 *
            Real.sqrt ((8 / 9 : ℝ) * (2 ^ j : ℕ) * (Real.log M + 3) ^ 3 + 1) =
          (Real.sqrt ((2 ^ k : ℕ) * Real.log (2 * (2 ^ k : ℕ)) ^ 2) *
            Real.sqrt ((8 / 9 : ℝ) * (2 ^ j : ℕ) *
              (Real.log M + 3) ^ 3 + 1)) *
                dyadicAnalyticFactor x y y' k j 0 := by ring
      _ ≤ (4 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) *
          (C * (y : ℝ) ^ (13 / 28 : ℝ) * H) :=
        mul_le_mul hcoeff hf hf0 (by positivity)
      _ = (4 * C) * (y : ℝ) ^ (27 / 28 : ℝ) * H ^ 4 := by
        rw [← rpow_half_mul_rpow_thirteen_twentyEight hyr]
        ring
  · have hcoeff := sqrt_lambdaMass_mul_sqrt_aMass_le
      hy hM (pow_pos (by omega) j) (pow_pos (by omega) k) hprod hH (by
        simpa [orientedSmallScale, hjk] using hlogSmall) hlogM
    simp only [sigma3OrientedBlockMajorant, hjk, if_neg]
    have hf := hanalytic
    simp only [hjk, if_neg] at hf hf0
    calc
      Real.sqrt ((8 / 9 : ℝ) * (2 ^ j : ℕ) * (Real.log M + 3) ^ 3 + 1) *
          dyadicAnalyticFactor x y y' j k 0 *
            Real.sqrt ((2 ^ k : ℕ) * Real.log (2 * (2 ^ k : ℕ)) ^ 2) =
          (Real.sqrt ((2 ^ k : ℕ) * Real.log (2 * (2 ^ k : ℕ)) ^ 2) *
            Real.sqrt ((8 / 9 : ℝ) * (2 ^ j : ℕ) *
              (Real.log M + 3) ^ 3 + 1)) *
                dyadicAnalyticFactor x y y' j k 0 := by ring
      _ ≤ (4 * (y : ℝ) ^ (1 / 2 : ℝ) * H ^ 3) *
          (C * (y : ℝ) ^ (13 / 28 : ℝ) * H) :=
        mul_le_mul hcoeff hf hf0 (by positivity)
      _ = (4 * C) * (y : ℝ) ^ (27 / 28 : ℝ) * H ^ 4 := by
        rw [← rpow_half_mul_rpow_thirteen_twentyEight hyr]
        ring

end TypeIICoefficientCollapse

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/TypeIIScalar.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Scalar simplification of the Type-II power-block bound

This file turns the three-branch closed correlation majorant into a single
power-saving estimate.  The hypotheses are precisely the scale information
available for an oriented active Vaughan block.  The lower frequency bound
`y^2 ≤ x` is essential: the direct summand of `orientedPowerBlockFarQ`
contains `1 / x`.
-/

noncomputable section

namespace TypeIIScalar

/-- The logarithmic envelope used for all three branches. -/
noncomputable def scalarLog (y : ℕ) : ℝ :=
  Real.log (256 * (y : ℝ) ^ 2)

lemma scalarLog_one_le {y : ℕ} (hy : 1 ≤ y) :
    1 ≤ scalarLog y := by
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have harg : (256 : ℝ) ≤ 256 * (y : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((y : ℝ) - 1)]
  have hlog256 : (1 : ℝ) ≤ Real.log 256 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    have hlog2 := Real.log_two_gt_d9
    norm_num at hlog2 ⊢
    nlinarith
  exact hlog256.trans (Real.log_le_log (by norm_num) harg)

/-- On an oriented block, the local logarithm is swallowed by twice the
global envelope. -/
lemma one_add_log_two_mul_le_two_scalarLog
    {y U V : ℕ} (hy : 1 ≤ y) (hU : 0 < U) (hV : 0 < V)
    (hproduct : U * V ≤ 2 * y) :
    1 + Real.log (2 * (U : ℝ)) ≤ 2 * scalarLog y := by
  have hUle : U ≤ 2 * y := by
    have hVU : U ≤ U * V := by
      calc U = U * 1 := by omega
        _ ≤ U * V := Nat.mul_le_mul_left U hV
    exact hVU.trans hproduct
  have harg : (2 : ℝ) * U ≤ 256 * (y : ℝ) ^ 2 := by
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
    have hUR : (U : ℝ) ≤ 2 * y := by exact_mod_cast hUle
    nlinarith [sq_nonneg ((y : ℝ) - 1)]
  have hlog : Real.log (2 * (U : ℝ)) ≤ scalarLog y := by
    unfold scalarLog
    apply Real.log_le_log
    · positivity
    · exact harg
  have hH := scalarLog_one_le hy
  linarith

/-- The support-scale cubic estimate gives the convenient real upper bound
`U ≤ 8 y^(2/3)`. -/
lemma upperScale_le_eight_rpow
    {y U : ℕ} (hy : 1 ≤ y) (hUcube : U ^ 3 ≤ 512 * y ^ 2) :
    (U : ℝ) ≤ 8 * (y : ℝ) ^ (2 / 3 : ℝ) := by
  have hy0 : 0 ≤ (y : ℝ) := by positivity
  have hpow : ((y : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (y : ℝ) ^ 2 := by
    rw [← Real.rpow_mul_natCast hy0]
    norm_num [Real.rpow_natCast]
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
  rw [mul_pow, hpow]
  norm_num
  exact_mod_cast hUcube

/-- The direct branch after multiplication by the second block length. -/
lemma directTerm_mul_smallScale_le
    {x : ℝ} {y U V : ℕ} (hy : 1 ≤ y) (hV : 0 < V)
    (hVU : V ≤ U) (hproduct : U * V ≤ 2 * y)
    (hxlower : (y : ℝ) ^ 2 ≤ x) :
    (16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x) * V ≤
      128 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hx : 0 < x := lt_of_lt_of_le (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hyR)) hxlower
  have hP : (U : ℝ) * V ≤ 2 * (y : ℝ) := by exact_mod_cast hproduct
  have hv2 : (V : ℝ) ^ 2 ≤ 2 * (y : ℝ) := by
    have hVU' : (V : ℝ) ≤ U := by exact_mod_cast hVU
    calc
      (V : ℝ) ^ 2 ≤ (U : ℝ) * V := by nlinarith
      _ ≤ 2 * (y : ℝ) := hP
  have hvroot : (V : ℝ) ≤ 2 * (y : ℝ) ^ (1 / 2 : ℝ) := by
    have hy0 : 0 ≤ (y : ℝ) := by positivity
    have hp : ((y : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (y : ℝ) := by
      rw [← Real.rpow_mul_natCast hy0]
      norm_num [Real.rpow_natCast]
    apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity)
    rw [mul_pow, hp]
    nlinarith
  have hdirect :
      (16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x) * V ≤ 64 * V := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hx]
    have hPsq : ((U : ℝ) * V) ^ 2 ≤ (2 * (y : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hP 2
    have hmul := mul_le_mul_of_nonneg_left hxlower (by positivity : (0 : ℝ) ≤ 64 * V)
    nlinarith [hPsq]
  have hexp : (y : ℝ) ^ (1 / 2 : ℝ) ≤
      (y : ℝ) ^ (13 / 14 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hyR (by norm_num)
  have hH := scalarLog_one_le hy
  have hHsq : 1 ≤ scalarLog y ^ 2 := by nlinarith
  calc
    (16 * (U : ℝ) ^ 2 * (V : ℝ) ^ 2 / x) * V ≤ 64 * V := hdirect
    _ ≤ 64 * (2 * (y : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hvroot (by norm_num)
    _ = 128 * (y : ℝ) ^ (1 / 2 : ℝ) := by ring
    _ ≤ 128 * (y : ℝ) ^ (13 / 14 : ℝ) := by gcongr
    _ ≤ 128 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
      exact le_mul_of_one_le_right (by positivity) hHsq

/-- A scale-free twelfth-power estimate for the sixth-root expression in
the two-step branch. -/
lemma sixthRoot_ratio_mul_rpow_le_three
    {x : ℝ} {y U V : ℕ} (hy : 1 ≤ y) (hU : 0 < U) (hV : 0 < V)
    (hVU : V ≤ U) (hactive : y < 4 * (U * V))
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) (hx : 0 ≤ x) :
    (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
        (y : ℝ) ^ (1 / 12 : ℝ) ≤ 3 := by
  let r : ℝ := x / ((V : ℝ) * (U : ℝ) ^ 4)
  have hy0 : 0 ≤ (y : ℝ) := by positivity
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hactiveR : (y : ℝ) ≤ 4 * ((U : ℝ) * V) := by
    have h : y ≤ 4 * (U * V) := hactive.le
    exact_mod_cast h
  have hx2 : x ^ 2 ≤ 144 * (y : ℝ) ^ 4 := by
    have := pow_le_pow_left₀ hx hxupper 2
    nlinarith
  have hy5 : (y : ℝ) ^ 5 ≤ 4 ^ 5 * (((U : ℝ) * V) ^ 5) := by
    have := pow_le_pow_left₀ hy0 hactiveR 5
    calc
      (y : ℝ) ^ 5 ≤ (4 * ((U : ℝ) * V)) ^ 5 := this
      _ = 4 ^ 5 * (((U : ℝ) * V) ^ 5) := by ring
  have hv3 : (V : ℝ) ^ 3 ≤ (U : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hVU) 3
  have hpoly : r ^ 2 * (y : ℝ) ≤ 147456 := by
    have hden : 0 < (((V : ℝ) * (U : ℝ) ^ 4) ^ 2) := by positivity
    dsimp only [r]
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ hden]
    calc
      x ^ 2 * (y : ℝ) ≤ (144 * (y : ℝ) ^ 4) * (y : ℝ) := by gcongr
      _ = 144 * (y : ℝ) ^ 5 := by ring
      _ ≤ 144 * (4 ^ 5 * (((U : ℝ) * V) ^ 5)) := by gcongr
      _ ≤ 147456 * (((V : ℝ) * (U : ℝ) ^ 4) ^ 2) := by
        have hcomp : (((U : ℝ) * V) ^ 5) ≤
            ((V : ℝ) * (U : ℝ) ^ 4) ^ 2 := by
          calc
            ((U : ℝ) * V) ^ 5 =
                (U : ℝ) ^ 5 * (V : ℝ) ^ 2 * (V : ℝ) ^ 3 := by ring
            _ ≤ (U : ℝ) ^ 5 * (V : ℝ) ^ 2 * (U : ℝ) ^ 3 := by gcongr
            _ = ((V : ℝ) * (U : ℝ) ^ 4) ^ 2 := by ring
        calc
          144 * (4 ^ 5 * (((U : ℝ) * V) ^ 5)) =
              147456 * (((U : ℝ) * V) ^ 5) := by ring_nf
          _ ≤ 147456 * (((V : ℝ) * (U : ℝ) ^ 4) ^ 2) :=
            mul_le_mul_of_nonneg_left hcomp (by norm_num)
  have hpow :
      (r ^ (1 / 6 : ℝ) * (y : ℝ) ^ (1 / 12 : ℝ)) ^ 12 =
        r ^ 2 * (y : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hr0,
      ← Real.rpow_mul_natCast hy0]
    norm_num [Real.rpow_natCast]
  apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by positivity)
  rw [hpow]
  norm_num
  exact hpoly.trans (by norm_num)

/-- The two-step sixth-root branch after multiplication by the small block
length. -/
lemma sixthRootTerm_mul_smallScale_le
    {x : ℝ} {y U V : ℕ} (hy : 1 ≤ y) (hU : 0 < U) (hV : 0 < V)
    (hVU : V ≤ U) (hactive : y < 4 * (U * V))
    (hproduct : U * V ≤ 2 * y)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) (hx : 0 ≤ x) :
    (128 * (U : ℝ) *
      (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
        Real.sqrt (1 + Real.log (2 * (U : ℝ)))) * V ≤
      1536 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
  let r : ℝ := x / ((V : ℝ) * (U : ℝ) ^ 4)
  let L : ℝ := 1 + Real.log (2 * (U : ℝ))
  let H : ℝ := scalarLog y
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hyp : 0 < (y : ℝ) := lt_of_lt_of_le zero_lt_one hyR
  have hy12pos : 0 < (y : ℝ) ^ (1 / 12 : ℝ) :=
    Real.rpow_pos_of_pos hyp _
  have hratio := sixthRoot_ratio_mul_rpow_le_three
    hy hU hV hVU hactive hxupper hx
  have hP : (U : ℝ) * V ≤ 2 * (y : ℝ) := by exact_mod_cast hproduct
  have hLone : 1 ≤ L := by
    dsimp only [L]
    have : 0 ≤ Real.log (2 * (U : ℝ)) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ 2 * U := by exact_mod_cast (show 1 ≤ 2 * U by omega)
      exact this
    linarith
  have hLH : L ≤ 2 * H := by
    simpa only [L, H] using
      one_add_log_two_mul_le_two_scalarLog hy hU hV hproduct
  have hsqrt : Real.sqrt L ≤ 2 * H := by
    calc
      Real.sqrt L ≤ L := Real.sqrt_le_self_iff.mpr (Or.inr hLone)
      _ ≤ 2 * H := hLH
  have hscaled :
      (128 * (U : ℝ) * r ^ (1 / 6 : ℝ) * Real.sqrt L * V) *
          (y : ℝ) ^ (1 / 12 : ℝ) ≤ 1536 * (y : ℝ) * H := by
    calc
      (128 * (U : ℝ) * r ^ (1 / 6 : ℝ) * Real.sqrt L * V) *
          (y : ℝ) ^ (1 / 12 : ℝ) =
          128 * ((U : ℝ) * V) *
            (r ^ (1 / 6 : ℝ) * (y : ℝ) ^ (1 / 12 : ℝ)) *
              Real.sqrt L := by ring
      _ ≤ 128 * (2 * (y : ℝ)) * 3 * (2 * H) := by gcongr
      _ = 1536 * (y : ℝ) * H := by ring
  have hroot :
      128 * (U : ℝ) * r ^ (1 / 6 : ℝ) * Real.sqrt L * V ≤
        1536 * (y : ℝ) ^ (11 / 12 : ℝ) * H := by
    apply le_of_mul_le_mul_right
    · calc
      (128 * (U : ℝ) * r ^ (1 / 6 : ℝ) * Real.sqrt L * V) *
          (y : ℝ) ^ (1 / 12 : ℝ) ≤ 1536 * (y : ℝ) * H := hscaled
      _ = (1536 * (y : ℝ) ^ (11 / 12 : ℝ) * H) *
          (y : ℝ) ^ (1 / 12 : ℝ) := by
        have hyadd :
            (y : ℝ) ^ (11 / 12 : ℝ) * (y : ℝ) ^ (1 / 12 : ℝ) =
              (y : ℝ) := by
          rw [← Real.rpow_add hyp]
          norm_num
        calc
          1536 * (y : ℝ) * H =
              1536 * ((y : ℝ) ^ (11 / 12 : ℝ) *
                (y : ℝ) ^ (1 / 12 : ℝ)) * H := by rw [hyadd]
          _ = (1536 * (y : ℝ) ^ (11 / 12 : ℝ) * H) *
              (y : ℝ) ^ (1 / 12 : ℝ) := by ring
    · exact hy12pos
  have hexp : (y : ℝ) ^ (11 / 12 : ℝ) ≤
      (y : ℝ) ^ (13 / 14 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hyR (by norm_num)
  have hH : 1 ≤ H := by simpa only [H] using scalarLog_one_le hy
  dsimp only [r, L, H] at hroot ⊢
  calc
    128 * (U : ℝ) *
        (x / ((V : ℝ) * (U : ℝ) ^ 4)) ^ (1 / 6 : ℝ) *
          Real.sqrt (1 + Real.log (2 * (U : ℝ))) * V ≤
        1536 * (y : ℝ) ^ (11 / 12 : ℝ) * scalarLog y := hroot
    _ ≤ 1536 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y := by gcongr
    _ ≤ 1536 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
      gcongr
      nlinarith

/-- The fractional-power factor in the interpolated branch. -/
lemma upperSixSevenths_mul_smallScale_le
    {y U V : ℕ} (hy : 1 ≤ y) (hV : 0 < V) (hVU : V ≤ U)
    (hproduct : U * V ≤ 2 * y) :
    (2 * (U : ℝ)) ^ (6 / 7 : ℝ) * V ≤
      8 * (y : ℝ) ^ (13 / 14 : ℝ) := by
  have hy0 : 0 ≤ (y : ℝ) := by positivity
  have hu0 : 0 ≤ (U : ℝ) := by positivity
  have htwo : (2 : ℝ) ^ (6 / 7 : ℝ) ≤ 2 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hmul : (2 * (U : ℝ)) ^ (6 / 7 : ℝ) ≤
      2 * (U : ℝ) ^ (6 / 7 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hu0]
    gcongr
  have hP : (U : ℝ) * V ≤ 2 * (y : ℝ) := by exact_mod_cast hproduct
  have hv2 : (V : ℝ) ^ 2 ≤ 2 * (y : ℝ) := by
    have hVU' : (V : ℝ) ≤ U := by exact_mod_cast hVU
    calc
      (V : ℝ) ^ 2 ≤ (U : ℝ) * V := by nlinarith
      _ ≤ 2 * (y : ℝ) := hP
  let D : ℝ := (U : ℝ) ^ (6 / 7 : ℝ) * V
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hDpow : D ^ 14 = (U : ℝ) ^ 12 * (V : ℝ) ^ 14 := by
    dsimp only [D]
    rw [mul_pow, ← Real.rpow_mul_natCast hu0]
    norm_num [Real.rpow_natCast]
  have hyPow : ((y : ℝ) ^ (13 / 14 : ℝ)) ^ 14 = (y : ℝ) ^ 13 := by
    rw [← Real.rpow_mul_natCast hy0]
    norm_num [Real.rpow_natCast]
  have hDbound : D ≤ 4 * (y : ℝ) ^ (13 / 14 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (14 : ℕ) ≠ 0) (by positivity)
    rw [hDpow, mul_pow, hyPow]
    have hPpow : ((U : ℝ) * V) ^ 12 ≤
        (2 * (y : ℝ)) ^ 12 := pow_le_pow_left₀ (by positivity) hP 12
    calc
      (U : ℝ) ^ 12 * (V : ℝ) ^ 14 =
          (((U : ℝ) * V) ^ 12) * (V : ℝ) ^ 2 := by ring
      _ ≤ (2 * (y : ℝ)) ^ 12 * (2 * (y : ℝ)) := by gcongr
      _ ≤ 4 ^ 14 * (y : ℝ) ^ 13 := by
        have : (0 : ℝ) ≤ (y : ℝ) ^ 13 := by positivity
        norm_num
        nlinarith
  calc
    (2 * (U : ℝ)) ^ (6 / 7 : ℝ) * V ≤
        (2 * (U : ℝ) ^ (6 / 7 : ℝ)) * V := by gcongr
    _ = 2 * D := by dsimp only [D]; ring
    _ ≤ 2 * (4 * (y : ℝ) ^ (13 / 14 : ℝ)) :=
      mul_le_mul_of_nonneg_left hDbound (by norm_num)
    _ = 8 * (y : ℝ) ^ (13 / 14 : ℝ) := by ring

/-- The interpolated seventh-root branch after multiplication by the small
block length. -/
lemma seventhRootTerm_mul_smallScale_le
    {y U V : ℕ} (hy : 1 ≤ y) (hV : 0 < V) (hVU : V ≤ U)
    (hproduct : U * V ≤ 2 * y) :
    (128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
      (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ)) * V ≤
      2048 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
  let L : ℝ := 1 + Real.log (2 * (U : ℝ))
  let H : ℝ := scalarLog y
  have hLone : 1 ≤ L := by
    dsimp only [L]
    have : 0 ≤ Real.log (2 * (U : ℝ)) := by
      apply Real.log_nonneg
      have hU : 0 < U := lt_of_lt_of_le hV (by omega)
      exact_mod_cast (show 1 ≤ 2 * U by omega)
    linarith
  have hLH : L ≤ 2 * H := by
    simpa only [L, H] using
      one_add_log_two_mul_le_two_scalarLog hy (lt_of_lt_of_le hV hVU) hV hproduct
  have hLpow : L ^ (2 / 7 : ℝ) ≤ 2 * H := by
    exact (Real.rpow_le_self_of_one_le hLone (by norm_num)).trans hLH
  have hscale := upperSixSevenths_mul_smallScale_le hy hV hVU hproduct
  have hH : 1 ≤ H := by simpa only [H] using scalarLog_one_le hy
  dsimp only [L, H] at hLpow hH ⊢
  calc
    (128 * (2 * (U : ℝ)) ^ (6 / 7 : ℝ) *
        (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ)) * V =
        128 * ((2 * (U : ℝ)) ^ (6 / 7 : ℝ) * V) *
          (1 + Real.log (2 * (U : ℝ))) ^ (2 / 7 : ℝ) := by ring
    _ ≤ 128 * (8 * (y : ℝ) ^ (13 / 14 : ℝ)) *
          (2 * scalarLog y) := by gcongr
    _ = 2048 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y := by ring
    _ ≤ 2048 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
      gcongr
      nlinarith

/-- The complete scalar estimate used for every oriented active Type-II
power block.  Its exponent `13/28` combines with the coefficient factor
`sqrt (UV)`, of size `y^(1/2)`, to give the final `y^(27/28)` bound. -/
theorem sqrt_two_mul_add_orientedPowerBlockFarQ_mul_le
    {x : ℝ} {y U V : ℕ}
    (hy : 1 ≤ y) (hU : 0 < U) (hV : 0 < V) (hVU : V ≤ U)
    (hactive : y < 4 * (U * V)) (hproduct : U * V ≤ 2 * y)
    (hUcube : U ^ 3 ≤ 512 * y ^ 2)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    Real.sqrt
        (2 * (U : ℝ) +
          TypeII.orientedPowerBlockFarQ x U V * (V : ℝ)) ≤
      64 * (y : ℝ) ^ (13 / 28 : ℝ) * scalarLog y := by
  have hx : 0 < x := by
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
    exact lt_of_lt_of_le (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hyR)) hxlower
  have hbase := upperScale_le_eight_rpow hy hUcube
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hbaseExp : (y : ℝ) ^ (2 / 3 : ℝ) ≤
      (y : ℝ) ^ (13 / 14 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hyR (by norm_num)
  have hH : 1 ≤ scalarLog y := scalarLog_one_le hy
  have hbaseTerm : 2 * (U : ℝ) ≤
      16 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
    calc
      2 * (U : ℝ) ≤ 2 * (8 * (y : ℝ) ^ (2 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ = 16 * (y : ℝ) ^ (2 / 3 : ℝ) := by ring
      _ ≤ 16 * (y : ℝ) ^ (13 / 14 : ℝ) := by gcongr
      _ ≤ 16 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
        exact le_mul_of_one_le_right (by positivity) (by nlinarith [hH])
  have hdirect := directTerm_mul_smallScale_le
    hy hV hVU hproduct hxlower
  have hsixth := sixthRootTerm_mul_smallScale_le
    hy hU hV hVU hactive hproduct hxupper hx.le
  have hseventh := seventhRootTerm_mul_smallScale_le
    hy hV hVU hproduct
  have hinside :
      2 * (U : ℝ) + TypeII.orientedPowerBlockFarQ x U V * (V : ℝ) ≤
        4096 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := by
    unfold TypeII.orientedPowerBlockFarQ
    nlinarith
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      2 * (U : ℝ) + TypeII.orientedPowerBlockFarQ x U V * (V : ℝ) ≤
          4096 * (y : ℝ) ^ (13 / 14 : ℝ) * scalarLog y ^ 2 := hinside
      _ = (64 * (y : ℝ) ^ (13 / 28 : ℝ) * scalarLog y) ^ 2 := by
        have hy0 : 0 ≤ (y : ℝ) := by positivity
        have hp : ((y : ℝ) ^ (13 / 28 : ℝ)) ^ 2 =
            (y : ℝ) ^ (13 / 14 : ℝ) := by
          rw [← Real.rpow_mul_natCast hy0]
          norm_num
        rw [mul_pow, mul_pow, hp]
        norm_num

end TypeIIScalar

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/TypeIIGlobal.lean` -/

section
/- leanprover/lean4:v4.33.0 -/

/-!
# Closed global estimates for the Vaughan Type-II sums

This file combines the zero-threshold reciprocal-sum estimate, the sharp
support-scale cube bounds, the explicit coefficient majorants, and the
dyadic block count.  The resulting exponent is `27/28` in the square-root
variable, hence `27/56` in the original variable.  All logarithmic losses
are absorbed into six powers of one common logarithm.
-/

noncomputable section

namespace TypeIIGlobal

open Erdos175.VaughanTypeIIDyadic
open Erdos175.VaughanTypeIICoefficients

private lemma three_le_scalarLog {y : ℕ} (hy : 1 ≤ y) :
    3 ≤ TypeIIScalar.scalarLog y := by
  have harg : (256 : ℝ) ≤ 256 * (y : ℝ) ^ 2 := by
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
    nlinarith [sq_nonneg ((y : ℝ) - 1)]
  have hlog256 : (3 : ℝ) ≤ Real.log 256 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    have hlog2 := Real.log_two_gt_d9
    norm_num at hlog2 ⊢
    nlinarith
  exact hlog256.trans (by
    unfold TypeIIScalar.scalarLog
    exact Real.log_le_log (by norm_num) harg)

/-- A dyadic count whose endpoint lies below `256 y²` is at most three
copies of the common logarithmic envelope. -/
lemma dyadicCount_cast_le_three_scalarLog
    {y N : ℕ} (hy : 1 ≤ y) (hN : N ≠ 0)
    (hNle : N ≤ 256 * y ^ 2) :
    (TypeI.dyadicCount N : ℝ) ≤ 3 * TypeIIScalar.scalarLog y := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hNpos
  have hlogNH : Real.log (N : ℝ) ≤ TypeIIScalar.scalarLog y := by
    unfold TypeIIScalar.scalarLog
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hNle
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : Real.log (N : ℝ) / Real.log 2 ≤
      2 * Real.log (N : ℝ) := by
    rw [div_le_iff₀ hlog2]
    nlinarith [Real.log_two_gt_d9]
  have hraw := TypeI.dyadicCount_cast_le_log_div_add_one hN
  have hH := TypeIIScalar.scalarLog_one_le hy
  calc
    (TypeI.dyadicCount N : ℝ) ≤
        Real.log N / Real.log 2 + 1 := hraw
    _ ≤ 2 * Real.log N + 1 := by linarith
    _ ≤ 3 * TypeIIScalar.scalarLog y := by linarith

/-- The oriented zero-threshold analytic factor has the uniform scalar
bound needed by both coefficient families. -/
lemma orientedDyadicAnalyticFactor_zero_le_closed
    {x : ℝ} {y y' j k : ℕ}
    (hy : 1 ≤ y) (hy' : y' ≤ 2 * y)
    (hactive : blockActive y y' j k)
    (hlarge : 2304 ≤ orientedLargeScale j k)
    (hcube : orientedLargeScale j k ^ 3 ≤ 512 * y ^ 2)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    (if j < k then dyadicAnalyticFactor x y y' k j 0
     else dyadicAnalyticFactor x y y' j k 0) ≤
      64 * (y : ℝ) ^ (13 / 28 : ℝ) * TypeIIScalar.scalarLog y := by
  let U := orientedLargeScale j k
  let V := orientedSmallScale j k
  have hU : 0 < U := by simp [U]
  have hV : 0 < V := by simp [V]
  have hVU : V ≤ U := by
    simpa only [U, V] using orientedSmallScale_le_orientedLargeScale j k
  have hproduct : U * V ≤ 2 * y := by
    dsimp only [U, V]
    rw [orientedLargeScale_mul_orientedSmallScale]
    exact (blockActive_lower_product_le hactive).trans hy'
  have hactive' : y < 4 * (U * V) := by
    dsimp only [U, V]
    rw [orientedLargeScale_mul_orientedSmallScale]
    exact blockActive_y_lt_four_mul_lower_product hactive
  have hhone : 12 * (x / (V : ℝ)) ≤ (U : ℝ) ^ 4 :=
    honeScale_of_active_oriented hxupper hlarge hV hVU hactive'
  have hx : 0 < x := by
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
    exact lt_of_lt_of_le (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hyR)) hxlower
  have hscalar :
      Real.sqrt
          (2 * (U : ℝ) +
            TypeII.orientedPowerBlockFarQ x U V * (V : ℝ)) ≤
        64 * (y : ℝ) ^ (13 / 28 : ℝ) * TypeIIScalar.scalarLog y :=
    TypeIIScalar.sqrt_two_mul_add_orientedPowerBlockFarQ_mul_le
      hy hU hV hVU hactive' hproduct hcube hxlower hxupper
  by_cases hjk : j < k
  · simp only [hjk, if_pos]
    have hfactor := dyadicAnalyticFactor_zero_le_orientedPowerBlockFarQ
      x y y' k j hx (by
        simpa [U, V, orientedLargeScale, orientedSmallScale, hjk] using hhone)
    exact hfactor.trans (by
      simpa [U, V, orientedLargeScale, orientedSmallScale, hjk] using hscalar)
  · simp only [hjk, if_neg]
    have hfactor := dyadicAnalyticFactor_zero_le_orientedPowerBlockFarQ
      x y y' j k hx (by
        simpa [U, V, orientedLargeScale, orientedSmallScale, hjk] using hhone)
    exact hfactor.trans (by
      simpa [U, V, orientedLargeScale, orientedSmallScale, hjk] using hscalar)

private lemma sigma22_largeScale_ge
    {M j k : ℕ} (hMlarge : 4608 ≤ M)
    (hs : sigma22SupportActive M j) :
    2304 ≤ orientedLargeScale j k := by
  have hsupport : M < 2 ^ j * 2 := by
    simpa only [sigma22SupportActive, pow_succ] using hs
  have hjbase : 2304 ≤ 2 ^ j := by omega
  by_cases hjk : j < k
  · have hjkpow : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hjk.le
    rw [orientedLargeScale, if_pos hjk]
    exact hjbase.trans hjkpow
  · rw [orientedLargeScale, if_neg hjk]
    exact hjbase

private lemma sigma3_largeScale_ge
    {M j k : ℕ} (hMlarge : 4608 ≤ M)
    (hs : sigma3SupportActive M M j k) :
    2304 ≤ orientedLargeScale j k := by
  have hsmall := sigma3SupportActive_lt_two_mul_orientedSmallScale
    (L := M) (M := M) (K := M) (j := j) (k := k) le_rfl le_rfl hs
  have hsmallLarge := orientedSmallScale_le_orientedLargeScale j k
  omega

private lemma log_scale_le_two_scalarLog
    {y U V : ℕ} (hy : 1 ≤ y) (hU : 0 < U) (hV : 0 < V)
    (hUV : U * V ≤ 2 * y) :
    Real.log (2 * (U : ℝ)) ≤ 2 * TypeIIScalar.scalarLog y := by
  have h := TypeIIScalar.one_add_log_two_mul_le_two_scalarLog hy hU hV hUV
  linarith

/-- Uniform closed bound for one supported active `Σ₂,₂` block. -/
lemma sigma22OrientedBlockMajorant_le_final
    {x : ℝ} {y y' M j k : ℕ}
    (hy : 1 ≤ y) (hy' : y' ≤ 2 * y)
    (hM3 : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hMlarge : 4608 ≤ M)
    (hj : j ∈ Finset.range (TypeI.dyadicCount (M * M)))
    (hactive : blockActive y y' j k)
    (hs : sigma22SupportActive M j)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    sigma22OrientedBlockMajorant x y y' j k 0 ≤
      2048 * (y : ℝ) ^ (27 / 28 : ℝ) * TypeIIScalar.scalarLog y ^ 4 := by
  have hy0 : 0 < y := by omega
  have hH := TypeIIScalar.scalarLog_one_le hy
  have hprod : orientedLargeScale j k * orientedSmallScale j k ≤ 2 * y := by
    rw [orientedLargeScale_mul_orientedSmallScale]
    exact (blockActive_lower_product_le hactive).trans hy'
  have hlogLarge := log_scale_le_two_scalarLog hy
    (orientedLargeScale_pos j k) (orientedSmallScale_pos j k) hprod
  have hlogSmall := log_scale_le_two_scalarLog hy
    (orientedSmallScale_pos j k) (orientedLargeScale_pos j k)
      (by simpa [Nat.mul_comm] using hprod)
  have hcube := sigma22_orientedLargeScale_cube_le_512
    hy0 hy' hM3 hyM hj hactive hs
  have hanalytic0 := orientedDyadicAnalyticFactor_zero_le_closed
    hy hy' hactive (sigma22_largeScale_ge hMlarge hs) hcube hxlower hxupper
  have hanalytic :
      (if j < k then dyadicAnalyticFactor x y y' k j 0
       else dyadicAnalyticFactor x y y' j k 0) ≤
        64 * (y : ℝ) ^ (13 / 28 : ℝ) *
          (2 * TypeIIScalar.scalarLog y) := by
    calc
      _ ≤ 64 * (y : ℝ) ^ (13 / 28 : ℝ) *
          TypeIIScalar.scalarLog y := hanalytic0
      _ ≤ 64 * (y : ℝ) ^ (13 / 28 : ℝ) *
          (2 * TypeIIScalar.scalarLog y) := by
        exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have hs1 : sigma22SupportActive 1 j := by
    unfold sigma22SupportActive at hs ⊢
    omega
  have hblock := TypeIICoefficientCollapse.sigma22OrientedBlockMajorant_le_closed
    (x := x) (y := y) (y' := y') (j := j) (k := k)
      (C := 64) (H := 2 * TypeIIScalar.scalarLog y)
      hy0 hy' hactive hs1 (by norm_num) (by nlinarith)
      hlogLarge hlogSmall hanalytic
  calc
    sigma22OrientedBlockMajorant x y y' j k 0 ≤
        (2 * 64 : ℝ) * (y : ℝ) ^ (27 / 28 : ℝ) *
          (2 * TypeIIScalar.scalarLog y) ^ 4 := hblock
    _ = 2048 * (y : ℝ) ^ (27 / 28 : ℝ) *
          TypeIIScalar.scalarLog y ^ 4 := by ring

/-- Uniform closed bound for one supported active `Σ₃` block. -/
lemma sigma3OrientedBlockMajorant_le_final
    {x : ℝ} {y y' M j k : ℕ}
    (hy : 1 ≤ y) (hy' : y' ≤ 2 * y)
    (hM : 1 ≤ M) (hM3 : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hMlarge : 4608 ≤ M)
    (hactive : blockActive y y' j k)
    (hs : sigma3SupportActive M M j k)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    sigma3OrientedBlockMajorant x y y' M j k 0 ≤
      4096 * (y : ℝ) ^ (27 / 28 : ℝ) * TypeIIScalar.scalarLog y ^ 4 := by
  have hy0 : 0 < y := by omega
  have hH := TypeIIScalar.scalarLog_one_le hy
  have hprod : orientedLargeScale j k * orientedSmallScale j k ≤ 2 * y := by
    rw [orientedLargeScale_mul_orientedSmallScale]
    exact (blockActive_lower_product_le hactive).trans hy'
  have hlogLarge := log_scale_le_two_scalarLog hy
    (orientedLargeScale_pos j k) (orientedSmallScale_pos j k) hprod
  have hlogSmall := log_scale_le_two_scalarLog hy
    (orientedSmallScale_pos j k) (orientedLargeScale_pos j k)
      (by simpa [Nat.mul_comm] using hprod)
  have hlogM0 : Real.log (M : ℝ) ≤ TypeIIScalar.scalarLog y := by
    unfold TypeIIScalar.scalarLog
    apply Real.log_le_log
    · positivity
    · have hMy : M ≤ y := by
        have hMM3 : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) M
        omega
      have hy256 : y ≤ 256 * y ^ 2 := by nlinarith
      exact_mod_cast hMy.trans hy256
  have hlogM : Real.log (M : ℝ) + 3 ≤
      2 * TypeIIScalar.scalarLog y := by
    linarith [three_le_scalarLog hy]
  have hcube := sigma3_orientedLargeScale_cube_le_512
    (show 0 < y by omega) hy' hyM hactive hs
  have hanalytic0 := orientedDyadicAnalyticFactor_zero_le_closed
    hy hy' hactive (sigma3_largeScale_ge hMlarge hs) hcube hxlower hxupper
  have hanalytic :
      (if j < k then dyadicAnalyticFactor x y y' k j 0
       else dyadicAnalyticFactor x y y' j k 0) ≤
        64 * (y : ℝ) ^ (13 / 28 : ℝ) *
          (2 * TypeIIScalar.scalarLog y) := by
    calc
      _ ≤ 64 * (y : ℝ) ^ (13 / 28 : ℝ) *
          TypeIIScalar.scalarLog y := hanalytic0
      _ ≤ 64 * (y : ℝ) ^ (13 / 28 : ℝ) *
          (2 * TypeIIScalar.scalarLog y) := by
        exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have hblock := TypeIICoefficientCollapse.sigma3OrientedBlockMajorant_le_closed
    (x := x) (y := y) (y' := y') (M := M) (j := j) (k := k)
      (C := 64) (H := 2 * TypeIIScalar.scalarLog y)
      hy0 hy' hM hactive hs (by norm_num) (by nlinarith)
      hlogLarge hlogSmall hlogM hanalytic
  calc
    sigma3OrientedBlockMajorant x y y' M j k 0 ≤
        (4 * 64 : ℝ) * (y : ℝ) ^ (27 / 28 : ℝ) *
          (2 * TypeIIScalar.scalarLog y) ^ 4 := hblock
    _ = 4096 * (y : ℝ) ^ (27 / 28 : ℝ) *
          TypeIIScalar.scalarLog y ^ 4 := by ring

private lemma endpoint_le_256_mul_sq {y N : ℕ}
    (hy : 1 ≤ y) (hN : N ≤ 2 * y) : N ≤ 256 * y ^ 2 := by
  have hy256 : 2 * y ≤ 256 * y ^ 2 := by nlinarith
  exact hN.trans hy256

/-- Closed global estimate for `Σ₂,₂` in the square-root variable. -/
theorem norm_sigma22_le_closed
    {x : ℝ} {y y' M : ℕ}
    (hy : 1 ≤ y) (hyy' : y ≤ y') (hy' : y' ≤ 2 * y)
    (hM : 1 ≤ M) (hM3 : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hMlarge : 4608 ≤ M)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤
      18432 * (y : ℝ) ^ (27 / 28 : ℝ) *
        TypeIIScalar.scalarLog y ^ 6 := by
  have hx : 0 < x := by
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
    exact lt_of_lt_of_le (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hyR)) hxlower
  have hraw := norm_sigma22_le_sum_dyadic_coefficient_majorant_supported
    y y' M M x hx
  let C : ℝ := 2048 * (y : ℝ) ^ (27 / 28 : ℝ) *
    TypeIIScalar.scalarLog y ^ 4
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hsum :
      (∑ j ∈ Finset.range (TypeI.dyadicCount (M * M)),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k ∧ sigma22SupportActive M j then
            sigma22OrientedBlockMajorant x y y' j k 0 else 0) ≤
        (TypeI.dyadicCount (M * M) : ℝ) *
          TypeI.dyadicCount y' * C := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (TypeI.dyadicCount (M * M)),
          ∑ _k ∈ Finset.range (TypeI.dyadicCount y'), C := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        by_cases hact : blockActive y y' j k ∧ sigma22SupportActive M j
        · simp only [hact, if_pos]
          exact sigma22OrientedBlockMajorant_le_final hy hy' hM3 hyM hMlarge
            hj hact.1 hact.2 hxlower hxupper
        · simp only [hact, if_neg]
          exact hC
      _ = (TypeI.dyadicCount (M * M) : ℝ) *
          TypeI.dyadicCount y' * C := by simp [mul_assoc]
  have hMMne : M * M ≠ 0 := mul_ne_zero (by omega) (by omega)
  have hMMle : M * M ≤ 256 * y ^ 2 := by
    have hMM3 : M * M ≤ M ^ 3 := by
      calc M * M = (M * M) * 1 := by ring
        _ ≤ (M * M) * M := Nat.mul_le_mul_left (M * M) hM
        _ = M ^ 3 := by ring
    exact hMM3.trans (hM3.trans (by nlinarith))
  have hy'ne : y' ≠ 0 := by omega
  have hcount1 := dyadicCount_cast_le_three_scalarLog hy hMMne hMMle
  have hcount2 := dyadicCount_cast_le_three_scalarLog hy hy'ne
    (endpoint_le_256_mul_sq hy hy')
  have hcountProd :
      (TypeI.dyadicCount (M * M) : ℝ) * TypeI.dyadicCount y' ≤
        9 * TypeIIScalar.scalarLog y ^ 2 := by
    calc
      (TypeI.dyadicCount (M * M) : ℝ) * TypeI.dyadicCount y' ≤
          (3 * TypeIIScalar.scalarLog y) *
            (3 * TypeIIScalar.scalarLog y) := by
              exact mul_le_mul hcount1 hcount2 (by positivity)
                (by have := TypeIIScalar.scalarLog_one_le hy; positivity)
      _ = 9 * TypeIIScalar.scalarLog y ^ 2 := by ring
  calc
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤ _ := hraw
    _ ≤ (TypeI.dyadicCount (M * M) : ℝ) *
          TypeI.dyadicCount y' * C := hsum
    _ ≤ (9 * TypeIIScalar.scalarLog y ^ 2) * C :=
      mul_le_mul_of_nonneg_right hcountProd hC
    _ = 18432 * (y : ℝ) ^ (27 / 28 : ℝ) *
          TypeIIScalar.scalarLog y ^ 6 := by simp only [C]; ring

/-- Closed global estimate for `Σ₃` in the square-root variable. -/
theorem norm_sigma3_le_closed
    {x : ℝ} {y y' M : ℕ}
    (hy : 1 ≤ y) (hyy' : y ≤ y') (hy' : y' ≤ 2 * y)
    (hM : 1 ≤ M) (hM3 : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hMlarge : 4608 ≤ M)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤
      36864 * (y : ℝ) ^ (27 / 28 : ℝ) *
        TypeIIScalar.scalarLog y ^ 6 := by
  have hx : 0 < x := by
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
    exact lt_of_lt_of_le (sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hyR)) hxlower
  have hraw := norm_sigma3_le_sum_dyadic_coefficient_majorant_supported
    y y' M M x hx hM
  let C : ℝ := 4096 * (y : ℝ) ^ (27 / 28 : ℝ) *
    TypeIIScalar.scalarLog y ^ 4
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hsum :
      (∑ j ∈ Finset.range (TypeI.dyadicCount y'),
        ∑ k ∈ Finset.range (TypeI.dyadicCount y'),
          if blockActive y y' j k ∧ sigma3SupportActive M M j k then
            sigma3OrientedBlockMajorant x y y' M j k 0 else 0) ≤
        (TypeI.dyadicCount y' : ℝ) * TypeI.dyadicCount y' * C := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (TypeI.dyadicCount y'),
          ∑ _k ∈ Finset.range (TypeI.dyadicCount y'), C := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        by_cases hact : blockActive y y' j k ∧ sigma3SupportActive M M j k
        · simp only [hact, if_pos]
          exact sigma3OrientedBlockMajorant_le_final hy hy' hM hM3 hyM hMlarge
            hact.1 hact.2 hxlower hxupper
        · simp only [hact, if_neg]
          exact hC
      _ = (TypeI.dyadicCount y' : ℝ) * TypeI.dyadicCount y' * C := by
        simp [mul_assoc]
  have hy'ne : y' ≠ 0 := by omega
  have hcount := dyadicCount_cast_le_three_scalarLog hy hy'ne
    (endpoint_le_256_mul_sq hy hy')
  have hcountProd :
      (TypeI.dyadicCount y' : ℝ) * TypeI.dyadicCount y' ≤
        9 * TypeIIScalar.scalarLog y ^ 2 := by
    calc
      (TypeI.dyadicCount y' : ℝ) * TypeI.dyadicCount y' ≤
          (3 * TypeIIScalar.scalarLog y) *
            (3 * TypeIIScalar.scalarLog y) := by
              exact mul_le_mul hcount hcount (by positivity)
                (by have := TypeIIScalar.scalarLog_one_le hy; positivity)
      _ = 9 * TypeIIScalar.scalarLog y ^ 2 := by ring
  calc
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤ _ := hraw
    _ ≤ (TypeI.dyadicCount y' : ℝ) * TypeI.dyadicCount y' * C := hsum
    _ ≤ (9 * TypeIIScalar.scalarLog y ^ 2) * C :=
      mul_le_mul_of_nonneg_right hcountProd hC
    _ = 36864 * (y : ℝ) ^ (27 / 28 : ℝ) *
          TypeIIScalar.scalarLog y ^ 6 := by simp only [C]; ring

private lemma sqrt_scale_rpow_le_original
    {y n : ℕ} (hy : 1 ≤ y) (hysq : y ^ 2 ≤ n) :
    (y : ℝ) ^ (27 / 28 : ℝ) ≤ (n : ℝ) ^ (27 / 56 : ℝ) := by
  have hyR : 0 ≤ (y : ℝ) := by positivity
  calc
    (y : ℝ) ^ (27 / 28 : ℝ) =
        ((y : ℝ) ^ 2) ^ (27 / 56 : ℝ) := by
      rw [show (27 / 28 : ℝ) = 2 * (27 / 56) by norm_num,
        Real.rpow_mul hyR]
      norm_num [Real.rpow_natCast]
    _ ≤ (n : ℝ) ^ (27 / 56 : ℝ) := by
      apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast hysq)
      norm_num

private lemma scalarLog_le_originalLog
    {y n : ℕ} (hy : 1 ≤ y) (hysq : y ^ 2 ≤ n) :
    TypeIIScalar.scalarLog y ≤ Real.log (256 * (n : ℝ)) := by
  unfold TypeIIScalar.scalarLog
  apply Real.log_le_log
  · positivity
  · exact_mod_cast Nat.mul_le_mul_left 256 hysq

/-- `Σ₂,₂` on the final `n^(27/56) log⁶` envelope. -/
theorem norm_sigma22_le_closed_original
    {x : ℝ} {n y y' M : ℕ}
    (hy : 1 ≤ y) (hyy' : y ≤ y') (hy' : y' ≤ 2 * y)
    (hM : 1 ≤ M) (hM3 : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hMlarge : 4608 ≤ M) (hysq : y ^ 2 ≤ n)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤
      18432 * (n : ℝ) ^ (27 / 56 : ℝ) *
        Real.log (256 * (n : ℝ)) ^ 6 := by
  have hraw := norm_sigma22_le_closed hy hyy' hy' hM hM3 hyM hMlarge
    hxlower hxupper
  have hp := sqrt_scale_rpow_le_original hy hysq
  have hlog := scalarLog_le_originalLog hy hysq
  have hlog0 : 0 ≤ TypeIIScalar.scalarLog y :=
    (TypeIIScalar.scalarLog_one_le hy).trans' (by norm_num)
  have hlogPow := pow_le_pow_left₀ hlog0 hlog 6
  calc
    ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤
        18432 * (y : ℝ) ^ (27 / 28 : ℝ) *
          TypeIIScalar.scalarLog y ^ 6 := hraw
    _ ≤ 18432 * (n : ℝ) ^ (27 / 56 : ℝ) *
          TypeIIScalar.scalarLog y ^ 6 := by gcongr
    _ ≤ 18432 * (n : ℝ) ^ (27 / 56 : ℝ) *
          Real.log (256 * (n : ℝ)) ^ 6 := by gcongr

/-- `Σ₃` on the final `n^(27/56) log⁶` envelope. -/
theorem norm_sigma3_le_closed_original
    {x : ℝ} {n y y' M : ℕ}
    (hy : 1 ≤ y) (hyy' : y ≤ y') (hy' : y' ≤ 2 * y)
    (hM : 1 ≤ M) (hM3 : M ^ 3 ≤ y) (hyM : y ≤ 8 * M ^ 3)
    (hMlarge : 4608 ≤ M) (hysq : y ^ 2 ≤ n)
    (hxlower : (y : ℝ) ^ 2 ≤ x)
    (hxupper : x ≤ 12 * (y : ℝ) ^ 2) :
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤
      36864 * (n : ℝ) ^ (27 / 56 : ℝ) *
        Real.log (256 * (n : ℝ)) ^ 6 := by
  have hraw := norm_sigma3_le_closed hy hyy' hy' hM hM3 hyM hMlarge
    hxlower hxupper
  have hp := sqrt_scale_rpow_le_original hy hysq
  have hlog := scalarLog_le_originalLog hy hysq
  have hlog0 : 0 ≤ TypeIIScalar.scalarLog y :=
    (TypeIIScalar.scalarLog_one_le hy).trans' (by norm_num)
  have hlogPow := pow_le_pow_left₀ hlog0 hlog 6
  calc
    ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
        (Vaughan.reciprocalPhase x) M M‖ ≤
        36864 * (y : ℝ) ^ (27 / 28 : ℝ) *
          TypeIIScalar.scalarLog y ^ 6 := hraw
    _ ≤ 36864 * (n : ℝ) ^ (27 / 56 : ℝ) *
          TypeIIScalar.scalarLog y ^ 6 := by gcongr
    _ ≤ 36864 * (n : ℝ) ^ (27 / 56 : ℝ) *
          Real.log (256 * (n : ℝ)) ^ 6 := by gcongr

end TypeIIGlobal

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/GranvilleRamare9.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Granville--Ramaré's reciprocal Mangoldt sum

This file fixes the exact finite sum occurring in the specialization of
Granville--Ramaré, Theorem 9, used for Erdős Problem 175.  It also records
the square-to-`L²` conversions and the numerical rounding steps used when the
two bilinear terms are assembled.

The interval is represented by
`Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n))`.  For an integer `d`, membership
in this interval is exactly `sqrt n < d ∧ d ≤ sqrt (2n)` in the real
sense, so no rounding error is introduced at either endpoint.
-/

namespace GranvilleRamare9

open scoped ArithmeticFunction BigOperators

/-- The reciprocal Mangoldt sum on the square-root interval used in Section 7. -/
noncomputable def mangoldtSum (n : ℕ) (x : ℝ) : ℂ :=
  Vaughan.reciprocalSum
    (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n))) x
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ)

/-- The phase convention in `Vaughan` agrees with the common `e(t)` notation. -/
lemma vaughan_reciprocalPhase_eq_e (x : ℝ) (d : ℕ) :
    Vaughan.reciprocalPhase x d = e (x / (d : ℝ)) := by
  unfold Vaughan.reciprocalPhase e
  congr 1

/-- Expanded finite-sum form of `mangoldtSum`. -/
lemma mangoldtSum_eq (n : ℕ) (x : ℝ) :
    mangoldtSum n x =
      ∑ d ∈ Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)),
        (ArithmeticFunction.vonMangoldt d : ℂ) * e (x / (d : ℝ)) := by
  unfold mangoldtSum Vaughan.reciprocalSum Vaughan.finiteWeightedSum
  apply Finset.sum_congr rfl
  intro d _hd
  rw [vaughan_reciprocalPhase_eq_e]

/-! ## The exact four-sum decomposition -/

/-- Vaughan's four-sum identity on the square-root interval, with the
reciprocal phase convention fixed above. -/
lemma mangoldtSum_four_sum
    (n M K : ℕ) (x : ℝ) (hM : 1 ≤ M) (hK : K ≤ Nat.sqrt n) :
    mangoldtSum n x =
      VaughanFourSums.sigma1
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M -
        VaughanFourSums.sigma21
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K -
        VaughanFourSums.sigma22
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K -
        VaughanFourSums.sigma3
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K := by
  unfold mangoldtSum
  exact VaughanFourSums.reciprocal_Ioc_four_sum_identity
    (Nat.sqrt n) (Nat.sqrt (2 * n)) M K x hM hK

/-- The triangle-inequality assembly corresponding to equation (9.2). -/
lemma norm_mangoldtSum_le_four_sums
    (n M K : ℕ) (x : ℝ) (hM : 1 ≤ M) (hK : K ≤ Nat.sqrt n) :
    ‖mangoldtSum n x‖ ≤
      ‖VaughanFourSums.sigma1
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M‖ +
        ‖VaughanFourSums.sigma21
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K‖ +
        ‖VaughanFourSums.sigma22
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K‖ +
        ‖VaughanFourSums.sigma3
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K‖ := by
  rw [mangoldtSum_four_sum n M K x hM hK]
  calc
    ‖VaughanFourSums.sigma1
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M -
        VaughanFourSums.sigma21
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K -
        VaughanFourSums.sigma22
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K -
        VaughanFourSums.sigma3
          (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
          (Vaughan.reciprocalPhase x) M K‖
        ≤
          ‖VaughanFourSums.sigma1
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M -
            VaughanFourSums.sigma21
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K -
            VaughanFourSums.sigma22
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖ +
          ‖VaughanFourSums.sigma3
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖ := norm_sub_le _ _
    _ ≤
          (‖VaughanFourSums.sigma1
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M -
            VaughanFourSums.sigma21
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖ +
          ‖VaughanFourSums.sigma22
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖) +
          ‖VaughanFourSums.sigma3
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤
          ((‖VaughanFourSums.sigma1
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M‖ +
            ‖VaughanFourSums.sigma21
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖) +
          ‖VaughanFourSums.sigma22
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖) +
          ‖VaughanFourSums.sigma3
              (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
              (Vaughan.reciprocalPhase x) M K‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = _ := by ring

/-! ## The closed Type-I contribution -/

/-- The natural square-root endpoints of the target interval lie in a
factor-two interval. -/
lemma sqrt_two_mul_le_two_sqrt (n : ℕ) (hn : 1 ≤ n) :
    Nat.sqrt (2 * n) ≤ 2 * Nat.sqrt n := by
  rw [← Nat.lt_succ_iff]
  apply Nat.sqrt_lt.mpr
  have hspos : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr (by omega)
  have hup := Nat.lt_succ_sqrt n
  nlinarith

/-! ## Converting squared coefficient estimates to `L²` estimates -/

/-- The `a_l` coefficient in Vaughan's identity is exactly the truncated
Möbius divisor sum appearing in Proposition 10.1. -/
lemma aCoeff_eq_truncatedMobiusDivisorSum
    (M : ℕ) {l : ℕ} (hl : l ≠ 0) :
    VaughanFourSums.aCoeff M l = truncatedMobiusDivisorSum M l := by
  rw [VaughanFourSums.aCoeff, ArithmeticFunction.coe_mul_zeta_apply,
    truncatedMobiusDivisorSum]
  change (∑ d ∈ l.divisors,
      (if d ≤ M then (ArithmeticFunction.moebius d : ℝ) else 0)) = _
  rw [← Finset.sum_filter]
  have hsets :
      l.divisors.filter (fun d => d ≤ M) =
        (Finset.Icc 1 M).filter (fun d => d ∣ l) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hdl, _⟩, hdM⟩
      have hd0 : d ≠ 0 := by
        intro hd
        subst d
        exact hl (Nat.eq_zero_of_zero_dvd hdl)
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hd0, hdM⟩, hdl⟩
    · rintro ⟨⟨hd1, hdM⟩, hdl⟩
      exact ⟨⟨hdl, hl⟩, hdM⟩
  rw [hsets]

/-! ## Shifted dyadic coefficient bounds

The exact Vaughan Type-II decomposition uses the half-open power block
`[2^j,2^(j+1))`, rather than the unshifted interval `(R,2R]`.  The bridge
module proves the corresponding squared estimates for the masked
coefficients.  The next elementary lemma turns each such estimate into the
square-root form consumed by the near--far bilinear bound. -/

/-- A support mask can only reduce the `L²` mass of the constant-one
coefficient on a shifted dyadic block. -/
lemma l2Norm_restrict_one_dyadicBlock_sq_le
    (support : Finset ℕ) (j : ℕ) :
    TypeII.l2Norm (TypeI.dyadicBlock j)
        (VaughanTypeIIDyadic.restrictCoeff support (fun _ => (1 : ℂ))) ^ 2 ≤
      (2 ^ j : ℕ) := by
  rw [TypeII.l2Norm_sq]
  calc
    (∑ n ∈ TypeI.dyadicBlock j,
        ‖VaughanTypeIIDyadic.restrictCoeff support
          (fun _ => (1 : ℂ)) n‖ ^ 2) ≤
        ∑ _n ∈ TypeI.dyadicBlock j, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hns : n ∈ support
      · simp [VaughanTypeIIDyadic.restrictCoeff, hns]
      · simp [VaughanTypeIIDyadic.restrictCoeff, hns]
    _ = (2 ^ j : ℕ) := by simp [TypeI.card_dyadicBlock]

/-! ## Premise-free Type-II block assembly -/

/-- The analytic square-root factor of the premise-free near--far bound,
with the two coefficient norms removed. -/
noncomputable def dyadicAnalyticFactor
    (x : ℝ) (y y' j k T : ℕ) : ℝ :=
  Real.sqrt
    (2 * (2 ^ j : ℕ) * (2 * T + 1) +
      TypeII.threeBranchFarQ x y y'
        (2 ^ j - 1) (2 ^ (j + 1) - 1)
        (2 ^ k - 1) (2 ^ (k + 1) - 1) T * (2 ^ k : ℕ))

/-! ### Coarse explicit specialization of the Type-I numerator -/

/-- The sixth-root Type-I contribution remains on the same power scale
when the Vaughan cutoff satisfies `M^3 ≤ y`. -/
lemma sixth_root_scale_with_M_le {x y m : ℝ}
    (hy : 1 ≤ y) (hx : 0 ≤ x) (hxy : x ≤ 24 * y ^ 2)
    (hm : 0 ≤ m) (hm3 : m ^ 3 ≤ y) :
    y * (x * m ^ 3 / y ^ 4) ^ (1 / 6 : ℝ) ≤
      24 * y ^ (23 / 24 : ℝ) := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hbase : 0 ≤ x * m ^ 3 / y ^ 4 := by positivity
  have hlpow :
      (y * (x * m ^ 3 / y ^ 4) ^ (1 / 6 : ℝ)) ^ 6 =
        x * m ^ 3 * y ^ 2 := by
    rw [mul_pow, ← Real.rpow_mul_natCast hbase]
    norm_num [Real.rpow_one]
    field_simp
  have hrpow :
      (24 * y ^ (23 / 24 : ℝ)) ^ 6 =
        24 ^ 6 * y ^ (23 / 4 : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hy0]
    norm_num
  have hyexp : y ^ 5 ≤ y ^ (23 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hy
      (show (5 : ℝ) ≤ 23 / 4 by norm_num)
    simpa [Real.rpow_natCast] using h
  apply le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) (by positivity)
  rw [hlpow, hrpow]
  calc
    x * m ^ 3 * y ^ 2 ≤ (24 * y ^ 2) * y * y ^ 2 := by gcongr
    _ = 24 * y ^ 5 := by ring
    _ ≤ 24 * y ^ (23 / 4 : ℝ) := by gcongr
    _ ≤ 24 ^ 6 * y ^ (23 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hy0 _)

/-- The nested-square-root Type-I contribution with a general cutoff
`M^3 ≤ y`.  Taking twelfth powers makes the fractional exponents exact. -/
lemma fourth_root_scale_with_M_le {y m L : ℝ}
    (hy : 1 ≤ y) (hm : 0 ≤ m) (hm3 : m ^ 3 ≤ y) (hL : 0 ≤ L) :
    Real.sqrt (Real.sqrt
        ((2 * y) ^ 3 * Real.sqrt (2 * y) * m * L ^ 2)) ≤
      2 * y ^ (23 / 24 : ℝ) * Real.sqrt L := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hyp : 0 < y := lt_of_lt_of_le zero_lt_one hy
  let X : ℝ := (2 * y) ^ 3 * Real.sqrt (2 * y) * m * L ^ 2
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hsqrt : Real.sqrt (2 * y) ≤ 2 * y ^ (1 / 2 : ℝ) := by
    calc
      Real.sqrt (2 * y) ≤ Real.sqrt (4 * y) :=
        Real.sqrt_le_sqrt (by nlinarith)
      _ = 2 * Real.sqrt y := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      _ = 2 * y ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
  have hpowadd : y ^ (7 / 2 : ℝ) = y ^ 3 * y ^ (1 / 2 : ℝ) := by
    rw [show (7 / 2 : ℝ) = 3 + 1 / 2 by norm_num, Real.rpow_add hyp]
    norm_num [Real.rpow_natCast]
  have hXupper : X ≤ 16 * y ^ (7 / 2 : ℝ) * m * L ^ 2 := by
    dsimp [X]
    calc
      (2 * y) ^ 3 * Real.sqrt (2 * y) * m * L ^ 2 ≤
          (2 * y) ^ 3 * (2 * y ^ (1 / 2 : ℝ)) * m * L ^ 2 := by
        gcongr
      _ = 16 * (y ^ 3 * y ^ (1 / 2 : ℝ)) * m * L ^ 2 := by ring
      _ = 16 * y ^ (7 / 2 : ℝ) * m * L ^ 2 := by rw [hpowadd]
  have hXpow : X ^ 3 ≤ 4096 * y ^ (23 / 2 : ℝ) * L ^ 6 := by
    calc
      X ^ 3 ≤ (16 * y ^ (7 / 2 : ℝ) * m * L ^ 2) ^ 3 := by gcongr
      _ = 4096 * y ^ (21 / 2 : ℝ) * m ^ 3 * L ^ 6 := by
        have hy3 : (y ^ (7 / 2 : ℝ)) ^ 3 = y ^ (21 / 2 : ℝ) := by
          rw [← Real.rpow_mul_natCast hy0]
          norm_num
        rw [mul_pow, mul_pow, mul_pow, hy3]
        ring
      _ ≤ 4096 * y ^ (21 / 2 : ℝ) * y * L ^ 6 := by gcongr
      _ = 4096 * y ^ (23 / 2 : ℝ) * L ^ 6 := by
        have hyadd : y ^ (23 / 2 : ℝ) = y ^ (21 / 2 : ℝ) * y := by
          rw [show (23 / 2 : ℝ) = 21 / 2 + 1 by norm_num,
            Real.rpow_add hyp]
          norm_num [Real.rpow_one]
        rw [hyadd]
        ring
  have hlpow : Real.sqrt (Real.sqrt X) ^ 12 = X ^ 3 := by
    calc
      Real.sqrt (Real.sqrt X) ^ 12 =
          (Real.sqrt (Real.sqrt X) ^ 4) ^ 3 := by ring
      _ = X ^ 3 := by
        rw [show Real.sqrt (Real.sqrt X) ^ 4 = X by
          calc
            Real.sqrt (Real.sqrt X) ^ 4 =
                (Real.sqrt (Real.sqrt X) ^ 2) ^ 2 := by ring
            _ = Real.sqrt X ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg X)]
            _ = X := Real.sq_sqrt hX]
  have hrpow :
      (2 * y ^ (23 / 24 : ℝ) * Real.sqrt L) ^ 12 =
        4096 * y ^ (23 / 2 : ℝ) * L ^ 6 := by
    have hypow : (y ^ (23 / 24 : ℝ)) ^ 12 = y ^ (23 / 2 : ℝ) := by
      rw [← Real.rpow_mul_natCast hy0]
      norm_num
    rw [mul_pow, mul_pow, hypow]
    rw [show Real.sqrt L ^ 12 = L ^ 6 by
      calc
        Real.sqrt L ^ 12 = (Real.sqrt L ^ 2) ^ 6 := by ring
        _ = L ^ 6 := by rw [Real.sq_sqrt hL]]
    norm_num
  apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by positivity)
  rw [hlpow, hrpow]
  exact hXpow

/-- The closed Type-I numerator with the standard cubic cutoff condition.
All three branches remain below `y^(23/24)`. -/
lemma threeBranchOuterNumerator_le
    (x : ℝ) (y M : ℕ) (hx : 0 < x) (hy : 1 ≤ y)
    (hM : 1 ≤ M) (hM3 : M ^ 3 ≤ y)
    (hylower : (y : ℝ) ^ 2 ≤ x)
    (hyupper : x ≤ 24 * (y : ℝ) ^ 2) :
    TypeI.threeBranchOuterNumerator x y M ≤
      6192 * (y : ℝ) ^ (23 / 24 : ℝ) *
        Real.sqrt (1 + Real.log (2 * y : ℕ)) := by
  let yr : ℝ := y
  let mr : ℝ := M
  let L : ℝ := 1 + Real.log (2 * y : ℕ)
  have hyr : 1 ≤ yr := by dsimp only [yr]; exact_mod_cast hy
  have hmr : 0 ≤ mr := by dsimp only [mr]; positivity
  have hm3r : mr ^ 3 ≤ yr := by
    dsimp only [mr, yr]
    exact_mod_cast hM3
  have hlog : 0 ≤ Real.log (2 * y : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * y by omega))
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hsqrtL : 1 ≤ Real.sqrt L := by rw [Real.one_le_sqrt]; exact hL
  have hpow : 1 ≤ yr ^ (23 / 24 : ℝ) := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hyr
      (by norm_num : (0 : ℝ) ≤ 23 / 24)
  have hfirst : 16 * yr ^ 2 / x ≤ 16 := by
    rw [div_le_iff₀ hx]
    nlinarith
  have hsixth :=
    sixth_root_scale_with_M_le hyr hx.le hyupper hmr hm3r
  have hfourth := fourth_root_scale_with_M_le hyr hmr hm3r hL0
  unfold TypeI.threeBranchOuterNumerator
  change 16 * yr ^ 2 / x +
      256 * yr * (x * mr ^ 3 / yr ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt L +
      16 * Real.sqrt (Real.sqrt
        ((2 * yr) ^ 3 * Real.sqrt (2 * yr) * mr * L ^ 2)) ≤ _
  have hfirst' : 16 * yr ^ 2 / x ≤
      16 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by
    calc
      16 * yr ^ 2 / x ≤ 16 := hfirst
      _ ≤ 16 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by
        have honeprod : 1 ≤ yr ^ (23 / 24 : ℝ) * Real.sqrt L := by
          simpa using (mul_le_mul hpow hsqrtL (by norm_num)
            (Real.rpow_nonneg (le_trans (by norm_num) hyr) _))
        nlinarith
  have hsixth' :
      256 * yr * (x * mr ^ 3 / yr ^ 4) ^ (1 / 6 : ℝ) * Real.sqrt L ≤
        6144 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by
    calc
      256 * yr * (x * mr ^ 3 / yr ^ 4) ^ (1 / 6 : ℝ) * Real.sqrt L =
          256 * (yr * (x * mr ^ 3 / yr ^ 4) ^ (1 / 6 : ℝ)) *
            Real.sqrt L := by ring
      _ ≤ 256 * (24 * yr ^ (23 / 24 : ℝ)) * Real.sqrt L := by gcongr
      _ = 6144 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by ring
  have hfourth' :
      16 * Real.sqrt (Real.sqrt
        ((2 * yr) ^ 3 * Real.sqrt (2 * yr) * mr * L ^ 2)) ≤
        32 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by
    calc
      16 * Real.sqrt (Real.sqrt
          ((2 * yr) ^ 3 * Real.sqrt (2 * yr) * mr * L ^ 2)) ≤
          16 * (2 * yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by gcongr
      _ = 32 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) := by ring
  calc
    16 * yr ^ 2 / x +
        256 * yr * (x * mr ^ 3 / yr ^ 4) ^ (1 / 6 : ℝ) *
          Real.sqrt L +
        16 * Real.sqrt (Real.sqrt
          ((2 * yr) ^ 3 * Real.sqrt (2 * yr) * mr * L ^ 2)) ≤
      16 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) +
        6144 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) +
        32 * (yr ^ (23 / 24 : ℝ) * Real.sqrt L) :=
      add_le_add (add_le_add hfirst' hsixth') hfourth'
    _ = 6192 * yr ^ (23 / 24 : ℝ) * Real.sqrt L := by ring

/-- Explicit Type-I estimate at the cubic Vaughan cutoff.  This is the
form used by the power-of-two specialization: `M^3 ≤ sqrt n` and
`sqrt n ≥ 144` imply the full scale condition in the closed Type-I theorem. -/
theorem norm_typeI_part_le_explicit_general
    (n M : ℕ) (x : ℝ) (hn : 1 ≤ n) (hM : 1 ≤ M)
    (hM3 : M ^ 3 ≤ Nat.sqrt n)
    (hxlower : (n : ℝ) ≤ x) (hxupper : x ≤ 6 * (n : ℝ))
    (hy : 144 ≤ Nat.sqrt n) :
    ‖VaughanFourSums.sigma1
        (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
        (Vaughan.reciprocalPhase x) M‖ +
      ‖VaughanFourSums.sigma21
        (Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)))
        (Vaughan.reciprocalPhase x) M M‖ ≤
      55728 * (n : ℝ) ^ (27 / 56 : ℝ) *
        Real.log (256 * (n : ℝ)) ^ 3 := by
  let y := Nat.sqrt n
  let y' := Nat.sqrt (2 * n)
  let L : ℝ := 1 + Real.log (2 * y : ℕ)
  let H : ℝ := Real.log (256 * (n : ℝ))
  have hx : 0 < x := lt_of_lt_of_le (by exact_mod_cast hn) hxlower
  have hyone : 1 ≤ y := by dsimp [y]; omega
  have hyy' : y ≤ y' := by
    dsimp [y, y']
    exact Nat.sqrt_le_sqrt (by omega)
  have hy' : y' ≤ 2 * y := by
    dsimp [y, y']
    exact sqrt_two_mul_le_two_sqrt n hn
  have hMy : M ≤ y := by
    dsimp [y]
    have hMM3 : M ≤ M ^ 3 := Nat.le_self_pow (by norm_num) M
    omega
  have hnupperNat := Nat.lt_succ_sqrt n
  have hnupper : (n : ℝ) < ((y + 1 : ℕ) : ℝ) ^ 2 := by
    norm_num [Nat.succ_eq_add_one, pow_two] at hnupperNat ⊢
    exact_mod_cast hnupperNat
  have hycast : (((y + 1 : ℕ) : ℝ)) = (y : ℝ) + 1 := by norm_num
  rw [hycast] at hnupper
  have hyR : (144 : ℝ) ≤ y := by exact_mod_cast hy
  have hn2 : (n : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by nlinarith
  have hysq : (y : ℝ) ^ 2 ≤ (n : ℝ) := by
    dsimp [y]
    norm_num [pow_two]
    exact_mod_cast Nat.sqrt_le n
  have hyx : (y : ℝ) ^ 2 ≤ x := hysq.trans hxlower
  have hxy : x ≤ 24 * (y : ℝ) ^ 2 := by linarith
  have hM3R : (M : ℝ) ^ 3 ≤ (y : ℝ) := by exact_mod_cast hM3
  have hglobal : 12 * x * (M : ℝ) ^ 3 ≤ (y : ℝ) ^ 4 := by
    calc
      12 * x * (M : ℝ) ^ 3 ≤ 12 * (12 * (y : ℝ) ^ 2) * (y : ℝ) := by
        gcongr
        linarith
      _ = 144 * (y : ℝ) ^ 3 := by ring
      _ ≤ (y : ℝ) * (y : ℝ) ^ 3 := by gcongr
      _ = (y : ℝ) ^ 4 := by ring
  have hraw := TypeI.norm_sigma1_add_sigma21_le_closed
    x y y' M M hx hM hMy hyy' hy' hglobal
  have hnum :=
    threeBranchOuterNumerator_le x y M hx hyone hM hM3 hyx hxy
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_two_gt_d9]
  have hLle8 : L ≤ Real.log (8 * y : ℕ) := by
    have hlogmul : Real.log (8 * y : ℕ) =
        Real.log 4 + Real.log (2 * y : ℕ) := by
      rw [show 8 * y = 4 * (2 * y) by omega]
      push_cast
      rw [Real.log_mul (by norm_num) (by positivity)]
    dsimp [L]
    rw [hlogmul]
    linarith
  have h8le : 8 * y ≤ 256 * n := by
    have hyn : y ≤ n := Nat.sqrt_le_self n
    omega
  have hlog8H : Real.log (8 * y : ℕ) ≤ H := by
    dsimp [H]
    apply Real.log_le_log
    · positivity
    · exact_mod_cast h8le
  have hLH : L ≤ H := hLle8.trans hlog8H
  have hLone : 1 ≤ L := by
    dsimp [L]
    have hlognonneg : 0 ≤ Real.log (2 * y : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * y by omega))
    linarith
  have hHone : 1 ≤ H := hLone.trans hLH
  have hsqrtLH : Real.sqrt L ≤ H := by
    calc
      Real.sqrt L ≤ Real.sqrt H := Real.sqrt_le_sqrt hLH
      _ ≤ H := Real.sqrt_le_self_iff.mpr (Or.inr hHone)
  have hlogyH : Real.log (2 * y : ℕ) ≤ H := by
    have : 2 * y ≤ 256 * n := by omega
    dsimp [H]
    apply Real.log_le_log
    · positivity
    · exact_mod_cast this
  have hlogMH : Real.log M ≤ H := by
    dsimp [H]
    apply Real.log_le_log
    · positivity
    · exact_mod_cast (show M ≤ 256 * n by omega)
  have houterCoeff :
      2 * Real.log (2 * y : ℕ) + Real.log M ≤ 3 * H := by
    linarith
  have hlogM0 : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hM)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : Real.log M / Real.log 2 ≤ 2 * Real.log M := by
    rw [div_le_iff₀ hlog2]
    nlinarith [Real.log_two_gt_d9]
  have hcountRaw := TypeI.dyadicCount_cast_le_log_div_add_one
    (show M ≠ 0 by omega)
  have hcount : (TypeI.dyadicCount M : ℝ) ≤ 3 * H := by
    calc
      (TypeI.dyadicCount M : ℝ) ≤ Real.log M / Real.log 2 + 1 := hcountRaw
      _ ≤ 2 * Real.log M + 1 := by linarith
      _ ≤ 3 * H := by linarith
  have hyPowEq : (y : ℝ) ^ (23 / 24 : ℝ) =
      ((y : ℝ) ^ 2) ^ (23 / 48 : ℝ) := by
    rw [show (23 / 24 : ℝ) = 2 * (23 / 48) by norm_num,
      Real.rpow_mul (by positivity)]
    norm_num [Real.rpow_natCast]
  have hyPow : (y : ℝ) ^ (23 / 24 : ℝ) ≤
      (n : ℝ) ^ (27 / 56 : ℝ) := by
    calc
      (y : ℝ) ^ (23 / 24 : ℝ) =
          ((y : ℝ) ^ 2) ^ (23 / 48 : ℝ) := hyPowEq
      _ ≤ (n : ℝ) ^ (23 / 48 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hysq (by norm_num)
      _ ≤ (n : ℝ) ^ (27 / 56 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast hn) (by norm_num)
  have hnum0 : 0 ≤ TypeI.threeBranchOuterNumerator x y M :=
    TypeI.threeBranchOuterNumerator_nonneg y M hx
  have houter :
      (2 * Real.log (2 * y : ℕ) + Real.log M) *
        (TypeI.threeBranchOuterNumerator x y M * TypeI.dyadicCount M) ≤
      55728 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 3 := by
    calc
      (2 * Real.log (2 * y : ℕ) + Real.log M) *
          (TypeI.threeBranchOuterNumerator x y M * TypeI.dyadicCount M) ≤
        (3 * H) *
          ((6192 * (y : ℝ) ^ (23 / 24 : ℝ) * Real.sqrt L) *
            (3 * H)) := by gcongr
      _ ≤ (3 * H) *
          ((6192 * (n : ℝ) ^ (27 / 56 : ℝ) * H) * (3 * H)) := by
        gcongr
      _ = 55728 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 3 := by ring
  exact hraw.trans (by simpa [y, y', L, H] using houter)

/-- The dyadic Vaughan cutoff used in the final power-of-two argument has
cube at most the square-root endpoint. -/
lemma vaughanCutoff_cube_le_sqrt (k : ℕ) :
    (2 ^ (k / 6)) ^ 3 ≤ Nat.sqrt (2 ^ k) := by
  rw [Nat.le_sqrt']
  calc
    ((2 ^ (k / 6)) ^ 3) ^ 2 = 2 ^ (6 * (k / 6)) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    _ ≤ 2 ^ k := by
      apply Nat.pow_le_pow_right (by norm_num)
      have := Nat.div_mul_le_self k 6
      omega

/-- The square-root endpoint is within the fixed factor `8` of the cube
of the dyadic Vaughan cutoff.  This is the complementary rounding estimate
to `vaughanCutoff_cube_le_sqrt`; its only loss is the residue of `k` modulo
six. -/
lemma sqrt_two_pow_le_eight_vaughanCutoff_cube (k : ℕ) :
    Nat.sqrt (2 ^ k) ≤ 8 * (2 ^ (k / 6)) ^ 3 := by
  have hkdiv : k ≤ 6 * (k / 6) + 6 := by
    omega
  have hp : 2 ^ k ≤ 2 ^ (6 * (k / 6) + 6) := by
    exact Nat.pow_le_pow_right (by norm_num) hkdiv
  calc
    Nat.sqrt (2 ^ k) ≤ Nat.sqrt ((8 * (2 ^ (k / 6)) ^ 3) ^ 2) := by
      apply Nat.sqrt_le_sqrt
      calc
        2 ^ k ≤ 2 ^ (6 * (k / 6) + 6) := hp
        _ = (8 * (2 ^ (k / 6)) ^ 3) ^ 2 := by
          have hcut : ((2 ^ (k / 6)) ^ 3) ^ 2 =
              2 ^ (6 * (k / 6)) := by
            rw [← pow_mul, ← pow_mul]
            congr 1
            omega
          rw [mul_pow, hcut, pow_add]
          norm_num
          simp [mul_comm]
    _ = 8 * (2 ^ (k / 6)) ^ 3 := Nat.sqrt_eq' _

lemma one_le_vaughanCutoff (k : ℕ) : 1 ≤ 2 ^ (k / 6) := by
  exact Nat.one_le_pow (k / 6) 2 (by norm_num)

lemma large_sqrt_two_pow (k : ℕ) (hk : 30 ≤ k) :
    144 ≤ Nat.sqrt (2 ^ k) := by
  rw [Nat.le_sqrt]
  calc
    144 * 144 ≤ 2 ^ 15 := by norm_num
    _ ≤ 2 ^ k := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega

/-- Above the final cutoff, the dyadic Vaughan parameter is large enough
for the uniform Type-II block estimate. -/
lemma large_vaughanCutoff (k : ℕ) (hk : 8192 ≤ k) :
    4608 ≤ 2 ^ (k / 6) := by
  calc
    4608 ≤ 2 ^ 13 := by norm_num
    _ ≤ 2 ^ (k / 6) := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega

/-- Power-of-two specialization of the explicit Type-I estimate, using
the dyadic cutoff `2^(k/6)`. -/
theorem norm_typeI_part_two_pow_le
    (k : ℕ) (x : ℝ) (hk : 30 ≤ k)
    (hxlower : ((2 ^ k : ℕ) : ℝ) ≤ x)
    (hxupper : x ≤ 6 * ((2 ^ k : ℕ) : ℝ)) :
    ‖VaughanFourSums.sigma1
        (Finset.Ioc (Nat.sqrt (2 ^ k)) (Nat.sqrt (2 * 2 ^ k)))
        (Vaughan.reciprocalPhase x) (2 ^ (k / 6))‖ +
      ‖VaughanFourSums.sigma21
        (Finset.Ioc (Nat.sqrt (2 ^ k)) (Nat.sqrt (2 * 2 ^ k)))
        (Vaughan.reciprocalPhase x) (2 ^ (k / 6)) (2 ^ (k / 6))‖ ≤
      55728 * (((2 ^ k : ℕ) : ℝ)) ^ (27 / 56 : ℝ) *
        Real.log (256 * (((2 ^ k : ℕ) : ℝ))) ^ 3 := by
  exact norm_typeI_part_le_explicit_general
    (2 ^ k) (2 ^ (k / 6)) x (Nat.one_le_pow k 2 (by norm_num))
      (one_le_vaughanCutoff k) (vaughanCutoff_cube_le_sqrt k)
      hxlower hxupper (large_sqrt_two_pow k hk)

/-- The complete Granville--Ramaré upper estimate on a power of two.
The deliberately generous coefficient `10^12` absorbs the three explicit
Vaughan contributions; the exponent and six logarithms are kept in the
exact form consumed by the final numerical cutoff. -/
theorem norm_mangoldtSum_two_pow_le_final
    (k : ℕ) (x : ℝ) (hk : 8192 ≤ k)
    (hxlower : (((2 : ℕ) ^ k : ℕ) : ℝ) ≤ x)
    (hxupper : x ≤ 6 * (((2 : ℕ) ^ k : ℕ) : ℝ)) :
    ‖mangoldtSum (2 ^ k) x‖ ≤
      (10 ^ 12 : ℝ) * (((2 : ℕ) ^ k : ℕ) : ℝ) ^ (27 / 56 : ℝ) *
        Real.log (256 * (((2 : ℕ) ^ k : ℕ) : ℝ)) ^ 6 := by
  let n : ℕ := 2 ^ k
  let y : ℕ := Nat.sqrt n
  let y' : ℕ := Nat.sqrt (2 * n)
  let M : ℕ := 2 ^ (k / 6)
  let H : ℝ := Real.log (256 * (n : ℝ))
  have hn : 1 ≤ n := by
    dsimp only [n]
    exact Nat.one_le_pow k 2 (by norm_num)
  have hy : 1 ≤ y := by
    dsimp only [y]
    exact Nat.sqrt_pos.mpr (by omega)
  have hyy' : y ≤ y' := by
    dsimp only [y, y', n]
    exact Nat.sqrt_le_sqrt (by omega)
  have hy' : y' ≤ 2 * y := by
    dsimp only [y, y']
    exact sqrt_two_mul_le_two_sqrt n hn
  have hM : 1 ≤ M := by
    dsimp only [M]
    exact one_le_vaughanCutoff k
  have hM3 : M ^ 3 ≤ y := by
    simpa only [M, y, n] using vaughanCutoff_cube_le_sqrt k
  have hyM : y ≤ 8 * M ^ 3 := by
    simpa only [M, y, n] using
      sqrt_two_pow_le_eight_vaughanCutoff_cube k
  have hMlarge : 4608 ≤ M := by
    simpa only [M] using large_vaughanCutoff k hk
  have hMy : M ≤ y := by
    exact (Nat.le_self_pow (by norm_num) M).trans hM3
  have hysq : y ^ 2 ≤ n := by
    dsimp only [y]
    exact Nat.sqrt_le' n
  have hysqR : (y : ℝ) ^ 2 ≤ (n : ℝ) := by
    exact_mod_cast hysq
  have hxYlower : (y : ℝ) ^ 2 ≤ x := hysqR.trans (by
    simpa only [n] using hxlower)
  have hy144 : 144 ≤ y := by
    simpa only [y, n] using large_sqrt_two_pow k (by omega)
  have hnupperNat : n < (y + 1) ^ 2 := by
    dsimp only [y]
    simpa only [pow_two] using Nat.lt_succ_sqrt n
  have hnupper : (n : ℝ) < (y + 1 : ℝ) ^ 2 := by
    have hycast : (((y + 1 : ℕ) : ℝ)) = (y : ℝ) + 1 := by norm_num
    rw [← hycast]
    exact_mod_cast hnupperNat
  have hyR : (144 : ℝ) ≤ y := by exact_mod_cast hy144
  have hn2 : (n : ℝ) ≤ 2 * (y : ℝ) ^ 2 := by
    nlinarith
  have hxYupper : x ≤ 12 * (y : ℝ) ^ 2 := by
    calc
      x ≤ 6 * (n : ℝ) := by simpa only [n] using hxupper
      _ ≤ 12 * (y : ℝ) ^ 2 := by nlinarith
  have hI :
      ‖VaughanFourSums.sigma1 (Finset.Ioc y y')
          (Vaughan.reciprocalPhase x) M‖ +
        ‖VaughanFourSums.sigma21 (Finset.Ioc y y')
          (Vaughan.reciprocalPhase x) M M‖ ≤
        55728 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 3 := by
    simpa only [n, y, y', M, H] using
      norm_typeI_part_two_pow_le k x (by omega) hxlower hxupper
  have h22 := TypeIIGlobal.norm_sigma22_le_closed_original
    (x := x) (n := n) (y := y) (y' := y') (M := M)
      hy hyy' hy' hM hM3 hyM hMlarge hysq hxYlower hxYupper
  have h3 := TypeIIGlobal.norm_sigma3_le_closed_original
    (x := x) (n := n) (y := y) (y' := y') (M := M)
      hy hyy' hy' hM hM3 hyM hMlarge hysq hxYlower hxYupper
  have hmain := norm_mangoldtSum_le_four_sums n M M x hM hMy
  have hlog256 : (1 : ℝ) ≤ Real.log 256 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    have hlog2 := Real.log_two_gt_d9
    norm_num at hlog2 ⊢
    nlinarith
  have harg : (256 : ℝ) ≤ 256 * (n : ℝ) := by
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hH : 1 ≤ H := by
    dsimp only [H]
    exact hlog256.trans (Real.log_le_log (by norm_num) harg)
  have hH36 : H ^ 3 ≤ H ^ 6 := by
    have hH3 : 1 ≤ H ^ 3 := one_le_pow₀ hH
    calc
      H ^ 3 = H ^ 3 * 1 := by ring
      _ ≤ H ^ 3 * H ^ 3 :=
        mul_le_mul_of_nonneg_left hH3 (by positivity)
      _ = H ^ 6 := by ring
  have hscale0 : 0 ≤ (n : ℝ) ^ (27 / 56 : ℝ) := by positivity
  have hH60 : 0 ≤ H ^ 6 := by positivity
  calc
    ‖mangoldtSum (2 ^ k) x‖ = ‖mangoldtSum n x‖ := by rfl
    _ ≤
        (‖VaughanFourSums.sigma1 (Finset.Ioc y y')
            (Vaughan.reciprocalPhase x) M‖ +
          ‖VaughanFourSums.sigma21 (Finset.Ioc y y')
            (Vaughan.reciprocalPhase x) M M‖) +
          ‖VaughanFourSums.sigma22 (Finset.Ioc y y')
            (Vaughan.reciprocalPhase x) M M‖ +
          ‖VaughanFourSums.sigma3 (Finset.Ioc y y')
            (Vaughan.reciprocalPhase x) M M‖ := hmain
    _ ≤ 55728 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 3 +
          18432 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 +
          36864 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 :=
      add_le_add (add_le_add hI h22) h3
    _ ≤ 55728 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 +
          18432 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 +
          36864 * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 := by
      gcongr
    _ = (111024 : ℝ) * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 := by ring
    _ ≤ (10 ^ 12 : ℝ) * (n : ℝ) ^ (27 / 56 : ℝ) * H ^ 6 := by
      gcongr <;> norm_num
    _ = (10 ^ 12 : ℝ) * (((2 : ℕ) ^ k : ℕ) : ℝ) ^ (27 / 56 : ℝ) *
        Real.log (256 * (((2 : ℕ) ^ k : ℕ) : ℝ)) ^ 6 := by rfl

/-! ## Norm assembly -/

end GranvilleRamare9

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/NumericCutoff.lean` -/

section
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The explicit numerical cutoff in the proof of Erdős Problem 175

This file proves the entirely real-variable calculation used after combining
the lower and upper estimates of Granville--Ramaré.  The key point is that the
endpoint is close, so the proof uses Mathlib's certified ten-decimal estimate
for `Real.log 2`, followed by an exact rational calculation.
-/

open Set

/-! ## A coarser lower-bound constant

The elementary Chebyshev argument used in an alternate assembly gives the
lower constant `1 / 50` instead of `2 / 35`.  The resulting exact cutoff is
slightly larger; `2 ^ 1728` is a convenient certified endpoint. -/

/-! ## Weakened analytic route

An intermediate version of the analytic estimate carries the larger
logarithmic exponent `13 / 4`, while the accompanying elementary lower bound
has constant `1 / 2000`.  The following exact calculation certifies the clean
power-of-two cutoff `2 ^ 2304`. -/

/-! ## Robust weakened route

The fully coarse form of the analytic argument has coefficient `100` and
logarithmic exponent `15 / 4`.  After division by the lower constant
`1 / 2000`, the logarithmic gap contains the ratio `200000`. -/

/-! ## Final coarse envelope

The last assembly uses the deliberately generous coefficient `10^12`, the
power `27 / 56`, and six powers of the logarithm.  Although the gap to the
square-root exponent is only `1 / 56`, the power-of-two endpoint `2 ^ 8192`
still leaves ample room.  Multiplying by the reciprocal of the lower-bound
constant `1 / 5000` gives the ratio `5 * 10^15` below.
-/

private noncomputable def finalCutoffGap (x : ℝ) : ℝ :=
  Real.log x / 56 - Real.log 5000000000000000 -
    6 * Real.log (Real.log (256 * x))

private lemma final_endpoint_integer_power_bound :
    (5000000000000000 : ℝ) ^ 56 * (6000 : ℝ) ^ 336 <
      (2 : ℝ) ^ 8192 := by
  have hnat :
      5000000000000000 ^ 56 * 6000 ^ 336 < (2 : ℕ) ^ 8192 := by
    calc
      5000000000000000 ^ 56 * 6000 ^ 336 <
          ((2 : ℕ) ^ 53) ^ 56 * ((2 : ℕ) ^ 13) ^ 336 := by
            gcongr <;> norm_num
      _ = (2 : ℕ) ^ 7336 := by
        rw [← pow_mul, ← pow_mul, ← pow_add]
      _ < (2 : ℕ) ^ 8192 :=
        Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  exact_mod_cast hnat

private lemma final_endpoint_power_bound :
    (5000000000000000 : ℝ) ^ 56 * (8200 * Real.log 2) ^ 336 <
      (2 : ℝ) ^ 8192 := by
  have hlog : 8200 * Real.log 2 < (6000 : ℝ) := by
    nlinarith [Real.log_two_lt_d9]
  have hpow : (8200 * Real.log 2) ^ 336 < (6000 : ℝ) ^ 336 := by
    exact pow_lt_pow_left₀ hlog (by positivity) (by norm_num)
  calc
    (5000000000000000 : ℝ) ^ 56 * (8200 * Real.log 2) ^ 336 <
        (5000000000000000 : ℝ) ^ 56 * (6000 : ℝ) ^ 336 := by
          exact mul_lt_mul_of_pos_left hpow (by positivity)
    _ < (2 : ℝ) ^ 8192 := final_endpoint_integer_power_bound

private lemma finalCutoffGap_endpoint_pos :
    0 < finalCutoffGap ((2 : ℝ) ^ 8192) := by
  have hp := final_endpoint_power_bound
  have hp' := Real.strictMonoOn_log (mem_Ioi.mpr (by positivity))
    (mem_Ioi.mpr (by positivity)) hp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at hp'
  have hlogPow : Real.log ((2 : ℝ) ^ 8192) = 8192 * Real.log 2 :=
    Real.log_pow 2 8192
  have harg : 256 * (2 : ℝ) ^ 8192 = (2 : ℝ) ^ 8200 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add]
  have hinner : Real.log (256 * (2 : ℝ) ^ 8192) = 8200 * Real.log 2 := by
    rw [harg, Real.log_pow]
    norm_num
  dsimp [finalCutoffGap]
  rw [hlogPow, hinner]
  norm_num at hp' ⊢
  linarith

private lemma finalCutoffGap_hasDerivAt {x : ℝ} (hxpos : 0 < x)
    (hinnerpos : 0 < Real.log (256 * x)) :
    HasDerivAt finalCutoffGap
      (x⁻¹ / 56 - 6 * (256 / (256 * x)) / Real.log (256 * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ ↦ 256 * y) 256 x := by
    simpa [mul_comm] using (hasDerivAt_id x).const_mul (256 : ℝ)
  have hloglin : HasDerivAt (fun y : ℝ ↦ Real.log (256 * y))
      (256 / (256 * x)) x := hlin.log (by positivity)
  have hloglog : HasDerivAt (fun y : ℝ ↦ Real.log (Real.log (256 * y)))
      ((256 / (256 * x)) / Real.log (256 * x)) x :=
    hloglin.log hinnerpos.ne'
  unfold finalCutoffGap
  have hfull := (((Real.hasDerivAt_log hxpos.ne').div_const 56).sub_const
    (Real.log 5000000000000000)).sub ((hasDerivAt_const x (6 : ℝ)).mul hloglog)
  refine (hfull.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards with y
  change Real.log y / 56 - Real.log 5000000000000000 -
      6 * Real.log (Real.log (256 * y)) =
    Real.log y / 56 - Real.log 5000000000000000 -
      6 * Real.log (Real.log (256 * y))
  rfl

private lemma finalCutoffGap_strictMonoOn :
    StrictMonoOn finalCutoffGap (Ici ((2 : ℝ) ^ 8192)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hxpos : 0 < x := (by positivity : 0 < (2 : ℝ) ^ 8192).trans_le hx
    have hxone : 1 < x := (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (8192 : ℕ) ≠ 0)).trans_le hx
    have hlogpos : 0 < Real.log (256 * x) := Real.log_pos (by nlinarith)
    exact (finalCutoffGap_hasDerivAt hxpos hlogpos).continuousAt)
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  have hxpos : 0 < x := (by positivity : 0 < (2 : ℝ) ^ 8192).trans hx
  have hlogarg : 336 < Real.log (256 * x) := by
    have hmono : Real.log (256 * (2 : ℝ) ^ 8192) < Real.log (256 * x) := by
      exact Real.strictMonoOn_log (mem_Ioi.mpr (by positivity))
        (mem_Ioi.mpr (by positivity)) (mul_lt_mul_of_pos_left hx (by norm_num))
    have hbase : 336 < Real.log (256 * (2 : ℝ) ^ 8192) := by
      rw [show 256 * (2 : ℝ) ^ 8192 = (2 : ℝ) ^ 8200 by
          rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add],
        Real.log_pow]
      norm_num
      nlinarith [Real.log_two_gt_d9]
    exact hbase.trans hmono
  have hinnerpos : 0 < Real.log (256 * x) := by linarith
  have hderiv := finalCutoffGap_hasDerivAt hxpos hinnerpos
  rw [hderiv.deriv]
  have hsimp : 256 / (256 * x) = x⁻¹ := by
    field_simp [hxpos.ne']
  rw [hsimp]
  have hxinv : 0 < x⁻¹ := inv_pos.mpr hxpos
  have hcoef : 0 < (1 / 56 : ℝ) - 6 / Real.log (256 * x) := by
    rw [sub_pos, div_lt_iff₀ hinnerpos]
    nlinarith
  have heq :
      x⁻¹ / 56 - 6 * x⁻¹ / Real.log (256 * x) =
        x⁻¹ * ((1 / 56 : ℝ) - 6 / Real.log (256 * x)) := by
    ring
  rw [heq]
  exact mul_pos hxinv hcoef

private lemma finalCutoffGap_pos_of_cutoff {x : ℝ}
    (hx : (2 : ℝ) ^ 8192 ≤ x) : 0 < finalCutoffGap x := by
  rcases hx.eq_or_lt with rfl | hxlt
  · exact finalCutoffGap_endpoint_pos
  · exact finalCutoffGap_endpoint_pos.trans
      (finalCutoffGap_strictMonoOn (mem_Ici.mpr (le_refl _)) (mem_Ici.mpr hx) hxlt)

/-- At `n ≥ 2 ^ 8192`, even the coefficient-`10^12`, exponent-`27 / 56`,
six-logarithm upper envelope is strictly below the elementary lower bound. -/
theorem granville_ramare_numeric_contradiction_final {n : ℕ}
    (hn : 2 ^ 8192 ≤ n) :
    (10 ^ 12 : ℝ) * (n : ℝ) ^ (27 / 56 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ 6 <
      (1 / 5000 : ℝ) * Real.sqrt n := by
  have hnreal : (2 : ℝ) ^ 8192 ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := (by positivity : 0 < (2 : ℝ) ^ 8192).trans_le hnreal
  have hlogpos : 0 < Real.log (256 * (n : ℝ)) := by
    apply Real.log_pos
    have hnNat : 0 < n := (by positivity : 0 < 2 ^ 8192).trans_le hn
    exact_mod_cast (show 1 < 256 * n by omega)
  have hgap := finalCutoffGap_pos_of_cutoff hnreal
  have hcore :
      (5000000000000000 : ℝ) * (n : ℝ) ^ (27 / 56 : ℝ) *
          (Real.log (256 * (n : ℝ))) ^ 6 < Real.sqrt n := by
    rw [← Real.log_lt_log_iff (by positivity) (Real.sqrt_pos.2 hnpos)]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hnpos,
      Real.log_pow, Real.sqrt_eq_rpow, Real.log_rpow hnpos]
    dsimp [finalCutoffGap] at hgap
    norm_num at hgap ⊢
    linarith
  nlinarith [mul_lt_mul_of_pos_left hcore (show (0 : ℝ) < 1 / 5000 by norm_num)]

theorem not_final_lower_le_upper_of_ge_cutoff {n : ℕ} (hn : 2 ^ 8192 ≤ n) :
    ¬ ((1 / 5000 : ℝ) * Real.sqrt n ≤
      (10 ^ 12 : ℝ) * (n : ℝ) ^ (27 / 56 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ 6) := by
  exact not_le_of_gt (granville_ramare_numeric_contradiction_final hn)

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/Detector.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
# The Granville--Ramaré prime-power detector

This file formalizes the arithmetic inequality (7.1) in Granville and
Ramaré, *Explicit bounds on exponential sums and the scarcity of squarefree
binomial coefficients* (Mathematika 43 (1996), 73--107).  The analytic
Fourier estimate which follows (7.1) is deliberately not part of this file.

For integral quotients the paper uses the sawtooth convention `ψ(x) = 0`,
not `-1/2`.  Since all arguments needed here are rational numbers `a / d`,
we use a division-free definition in terms of `a % d`.
-/

namespace Detector

open Nat Finset
open scoped BigOperators ArithmeticFunction.vonMangoldt

/-- The sawtooth value at the rational number `a / d`, with the convention
that it vanishes at integers. -/
noncomputable def sawtoothQuot (a d : ℕ) : ℝ :=
  if d ∣ a then 0 else ((a % d : ℕ) : ℝ) / d - 1 / 2

/-- The finite integer interval written in the paper as
`sqrt n < d ≤ sqrt (2n)`.  Describing it by squares avoids all rounding
choices at the two endpoints. -/
def squareRootInterval (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * n)).filter fun d => n < d ^ 2 ∧ d ^ 2 ≤ 2 * n

lemma mem_squareRootInterval {n d : ℕ} :
    d ∈ squareRootInterval n ↔ 1 ≤ d ∧ d ≤ 2 * n ∧ n < d ^ 2 ∧ d ^ 2 ≤ 2 * n := by
  simp [squareRootInterval, and_assoc]

/-- If adding the two residues of `n` modulo `d` creates no carry, the
sawtooth defect is zero when `d ∣ n` and `1/2` otherwise. -/
lemma sawtoothQuot_two_mul_of_no_carry {n d : ℕ} (hd : 0 < d)
    (hcarry : n % d + n % d < d) :
    sawtoothQuot (2 * n) d - 2 * sawtoothQuot n d =
      if d ∣ n then 0 else (1 / 2 : ℝ) := by
  have hmod : (2 * n) % d = n % d + n % d := by
    simpa [two_mul] using Nat.add_mod_of_add_mod_lt hcarry
  by_cases hdn : d ∣ n
  · have hd2n : d ∣ 2 * n := dvd_mul_of_dvd_right hdn 2
    simp [sawtoothQuot, hdn, hd2n]
  · have hd2n : ¬d ∣ 2 * n := by
      intro hd2n
      have hz : (2 * n) % d = 0 := Nat.mod_eq_zero_of_dvd hd2n
      have hnmod : n % d = 0 := by omega
      exact hdn (Nat.dvd_of_mod_eq_zero hnmod)
    rw [sawtoothQuot, if_neg hd2n, sawtoothQuot, if_neg hdn, if_neg hdn, hmod]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
    ring

/-- The square interval never contains `1`. -/
lemma one_lt_of_mem_squareRootInterval {n d : ℕ} (hd : d ∈ squareRootInterval n) : 1 < d := by
  rw [mem_squareRootInterval] at hd
  by_contra h
  have : d = 1 := by omega
  subst d
  norm_num at hd
  omega

/-- The Kummer step behind Corollary 3.2 and (7.1): a prime power `d` in
the square-root interval already forces a carry at the `d²` place.  If the
binomial coefficient is squarefree, there cannot also be a carry at the `d`
place. -/
lemma no_low_carry_of_primePow_interval {n d : ℕ}
    (hsq : Squarefree (Nat.choose (n + n) n))
    (hd : d ∈ squareRootInterval n) (hdpp : IsPrimePow d) :
    n % d + n % d < d := by
  obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff d).mp hdpp
  have hdmem := (mem_squareRootInterval.mp hd)
  have hdlo : n < d ^ 2 := hdmem.2.2.1
  have hdhi : d ^ 2 ≤ n + n := by simpa [two_mul] using hdmem.2.2.2
  have hpone : 1 < p := hp.one_lt
  let b := Nat.log p (n + n) + 1
  have hformula := Nat.factorization_choose' (n := n) (k := n) hp
    (b := b) (Nat.lt_succ_self _)
  have hsfac : (Nat.choose (n + n) n).factorization p ≤ 1 :=
    hsq.natFactorization_le_one p
  rw [hformula] at hsfac
  by_contra hnot
  have hlow : d ≤ n % d + n % d := by omega
  have hpow_a : p ^ a = d := hpa
  have hpow_two_a : p ^ (2 * a) = d ^ 2 := by
    rw [show 2 * a = a + a by omega, pow_add, hpa, pow_two]
  have hdle : d ≤ n + n := by
    have hdone : 1 ≤ d := hdmem.1
    calc
      d ≤ d ^ 2 := by nlinarith
      _ ≤ n + n := hdhi
  have ha_log : a < b := by
    dsimp [b]
    have := Nat.le_log_of_pow_le hpone (hpa ▸ hdle)
    omega
  have htwoa_log : 2 * a < b := by
    dsimp [b]
    have := Nat.le_log_of_pow_le hpone (hpow_two_a ▸ hdhi)
    omega
  let carries :=
    (Finset.Ico 1 b).filter fun i => p ^ i ≤ n % p ^ i + n % p ^ i
  have ha_mem : a ∈ carries := by
    simp only [carries, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨ha, ha_log⟩, by simpa [hpa] using hlow⟩
  have htwoa_mem : 2 * a ∈ carries := by
    simp only [carries, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, htwoa_log⟩, ?_⟩
    simpa [hpow_two_a, Nat.mod_eq_of_lt hdlo] using hdhi
  have hne : a ≠ 2 * a := by omega
  have : 1 < carries.card :=
    Finset.one_lt_card.mpr ⟨a, ha_mem, 2 * a, htwoa_mem, hne⟩
  exact (not_lt_of_ge hsfac) (by simpa [carries] using this)

/-- The pointwise summand obtained by moving the two sawtooth sums in (7.1)
to the same side. -/
noncomputable def weightedDefect (n d : ℕ) : ℝ :=
  (sawtoothQuot (2 * n) d - 2 * sawtoothQuot n d) *
    ArithmeticFunction.vonMangoldt d

/-- Every prime-power summand in the square-root interval has nonnegative
defect.  Non-prime-powers have zero von Mangoldt weight. -/
lemma weightedDefect_nonneg {n d : ℕ}
    (hsq : Squarefree (Nat.choose (n + n) n))
    (hd : d ∈ squareRootInterval n) : 0 ≤ weightedDefect n d := by
  by_cases hdpp : IsPrimePow d
  · have hcarry := no_low_carry_of_primePow_interval hsq hd hdpp
    rw [weightedDefect,
      sawtoothQuot_two_mul_of_no_carry (Nat.zero_lt_of_lt (one_lt_of_mem_squareRootInterval hd))
        hcarry]
    split_ifs <;> positivity
  · rw [weightedDefect, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hdpp, mul_zero]

/-- On terms coprime to `2n`, the defect is exactly half the von Mangoldt
weight. -/
lemma weightedDefect_eq_half {n d : ℕ}
    (hsq : Squarefree (Nat.choose (n + n) n))
    (hd : d ∈ squareRootInterval n) (hcop : Nat.Coprime d (2 * n)) :
    weightedDefect n d = (1 / 2 : ℝ) * ArithmeticFunction.vonMangoldt d := by
  by_cases hdpp : IsPrimePow d
  · have hcarry := no_low_carry_of_primePow_interval hsq hd hdpp
    have hdndvd : ¬d ∣ n := by
      intro hdn
      have hd2n : d ∣ 2 * n := dvd_mul_of_dvd_right hdn 2
      have hdgcd : d ∣ Nat.gcd d (2 * n) := Nat.dvd_gcd dvd_rfl hd2n
      have hd1 : d ∣ 1 := hcop ▸ hdgcd
      exact (one_lt_of_mem_squareRootInterval hd).ne' (Nat.dvd_one.mp hd1)
    rw [weightedDefect,
      sawtoothQuot_two_mul_of_no_carry (Nat.zero_lt_of_lt (one_lt_of_mem_squareRootInterval hd))
        hcarry,
      if_neg hdndvd]
  · rw [weightedDefect, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hdpp, mul_zero,
      mul_zero]

/-- Granville--Ramaré (7.1), in its exact prime-power/von-Mangoldt form.
The interval on the right is restricted by `(d,2n)=1`, as in the paper. -/
theorem sawtooth_mangoldt_detector (n : ℕ)
    (hsq : Squarefree (Nat.choose (n + n) n)) :
    (1 / 2 : ℝ) *
        (∑ d ∈ (squareRootInterval n).filter fun d => Nat.Coprime d (2 * n),
          ArithmeticFunction.vonMangoldt d) ≤
      |∑ d ∈ squareRootInterval n,
          sawtoothQuot (2 * n) d * ArithmeticFunction.vonMangoldt d| +
        2 * |∑ d ∈ squareRootInterval n,
          sawtoothQuot n d * ArithmeticFunction.vonMangoldt d| := by
  let good := (squareRootInterval n).filter fun d => Nat.Coprime d (2 * n)
  let allDefects := ∑ d ∈ squareRootInterval n, weightedDefect n d
  let firstSum := ∑ d ∈ squareRootInterval n,
    sawtoothQuot (2 * n) d * ArithmeticFunction.vonMangoldt d
  let secondSum := ∑ d ∈ squareRootInterval n,
    sawtoothQuot n d * ArithmeticFunction.vonMangoldt d
  have hgood :
      (1 / 2 : ℝ) *
          (∑ d ∈ good, ArithmeticFunction.vonMangoldt d) =
        ∑ d ∈ good, weightedDefect n d := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' := (Finset.mem_filter.mp hd)
    exact (weightedDefect_eq_half hsq hd'.1 hd'.2).symm
  have hsubset : good ⊆ squareRootInterval n := by
    exact Finset.filter_subset _ _
  have hsum : (∑ d ∈ good, weightedDefect n d) ≤ allDefects := by
    dsimp only [allDefects]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun d hd _ =>
      weightedDefect_nonneg hsq hd
  have hrewrite : allDefects = firstSum - 2 * secondSum := by
    simp only [allDefects, firstSum, secondSum, weightedDefect, sub_mul,
      Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  calc
    (1 / 2 : ℝ) *
          (∑ d ∈ (squareRootInterval n).filter fun d => Nat.Coprime d (2 * n),
            ArithmeticFunction.vonMangoldt d) =
        ∑ d ∈ good, weightedDefect n d := by simpa only [good] using hgood
    _ ≤ allDefects := hsum
    _ = firstSum - 2 * secondSum := hrewrite
    _ ≤ |firstSum - 2 * secondSum| := le_abs_self _
    _ ≤ |firstSum| + |2 * secondSum| := abs_sub _ _
    _ = |firstSum| + 2 * |secondSum| := by rw [abs_mul]; norm_num
    _ = |∑ d ∈ squareRootInterval n,
          sawtoothQuot (2 * n) d * ArithmeticFunction.vonMangoldt d| +
        2 * |∑ d ∈ squareRootInterval n,
          sawtoothQuot n d * ArithmeticFunction.vonMangoldt d| := rfl

end Detector

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/Sawtooth.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# The finite Fourier step in Granville--Ramaré, Section 7

This file isolates the finite-dimensional part of the argument leading to
equation (7.2).  The analytic input is expressed by a pair of pointwise
trigonometric majorants and by an `ℓ¹` bound for their coefficients.  The
lemmas below prove, without any asymptotic or measure-theoretic argument, how
these data control a nonnegative weighted sawtooth sum and how the constants
`43 / 6` and `11 / 8` follow from the degree-ten coefficient bound `86 / 99`.
-/

namespace Sawtooth

open scoped BigOperators

/-- The centered sawtooth function used in the Kummer detector.  Following
Granville--Ramaré's convention, its value at an integer is `0` rather than
the right-limit value `-1 / 2`. -/
noncomputable def psi (x : ℝ) : ℝ :=
  if x = (⌊x⌋ : ℝ) then 0 else Int.fract x - 1 / 2

/-- The standard additive character `e(x) = exp(2 π i x)`. -/
noncomputable def e (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

@[simp] lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  simp [e, Complex.norm_exp]

/-- Nonzero integral frequencies of absolute value at most `R`. -/
noncomputable def frequencies (R : ℕ) : Finset ℤ :=
  (Finset.Icc (-(R : ℤ)) (R : ℤ)).erase 0

/-- A finite trigonometric polynomial on the real line. -/
noncomputable def fourierPolynomial
    (F : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ r ∈ F, a r * e ((r : ℝ) * x)

/-- A pointwise upper Fourier majorant for a real-valued function. -/
def IsUpperMajorant
    (F : Finset ℤ) (f : ℝ → ℝ) (c : ℝ) (a : ℤ → ℂ) : Prop :=
  ∀ x, f x ≤ c + (fourierPolynomial F a x).re

/-- Weighted exponential sum at frequency `r`. -/
noncomputable def weightedPhaseSum { ι : Type* }
    (s : Finset ι) (w : ι → ℝ) (t : ι → ℝ) (r : ℤ) : ℂ :=
  ∑ i ∈ s, (w i : ℂ) * e ((r : ℝ) * t i)

/-- Distribute a weighted sum through a finite Fourier polynomial. -/
lemma weighted_fourierPolynomial_eq { ι : Type* }
    (s : Finset ι) (w : ι → ℝ) (t : ι → ℝ)
    (F : Finset ℤ) (a : ℤ → ℂ) :
    ∑ i ∈ s, (w i : ℂ) * fourierPolynomial F a (t i) =
      ∑ r ∈ F, a r * weightedPhaseSum s w t r := by
  simp only [fourierPolynomial, weightedPhaseSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Real-part version of `weighted_fourierPolynomial_eq`. -/
lemma weighted_fourierPolynomial_re_eq { ι : Type* }
    (s : Finset ι) (w : ι → ℝ) (t : ι → ℝ)
    (F : Finset ℤ) (a : ℤ → ℂ) :
    ∑ i ∈ s, w i * (fourierPolynomial F a (t i)).re =
      (∑ r ∈ F, a r * weightedPhaseSum s w t r).re := by
  rw [← weighted_fourierPolynomial_eq]
  simp

/-- A pointwise Fourier majorant gives a bound for every finite nonnegative
weighted sum.  This is the first displayed inequality after Lemma 7.1 in the
paper, stated in a form which does not assume a particular choice of phases. -/
lemma weighted_sum_le_of_upperMajorant { ι : Type* }
    (s : Finset ι) (w : ι → ℝ) (t : ι → ℝ)
    (F : Finset ℤ) (f : ℝ → ℝ) (c A M : ℝ) (a : ℤ → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hmajor : IsUpperMajorant F f c a)
    (hphase : ∀ r ∈ F, ‖weightedPhaseSum s w t r‖ ≤ M)
    (hcoeff : ∑ r ∈ F, ‖a r‖ ≤ A)
    (hM : 0 ≤ M) :
    ∑ i ∈ s, w i * f (t i) ≤
      c * ∑ i ∈ s, w i + A * M := by
  have hpoint : ∑ i ∈ s, w i * f (t i) ≤
      ∑ i ∈ s, w i * (c + (fourierPolynomial F a (t i)).re) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hmajor (t i)) (hw i hi)
  have hrearrange :
      ∑ i ∈ s, w i * (c + (fourierPolynomial F a (t i)).re) =
        c * ∑ i ∈ s, w i +
          (∑ r ∈ F, a r * weightedPhaseSum s w t r).re := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [weighted_fourierPolynomial_re_eq]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hrearrange] at hpoint
  have hfourier :
    (∑ r ∈ F, a r * weightedPhaseSum s w t r).re
        ≤ A * M := by
      calc
        (∑ r ∈ F, a r * weightedPhaseSum s w t r).re
            ≤ ‖∑ r ∈ F, a r * weightedPhaseSum s w t r‖ := Complex.re_le_norm _
        _ ≤ ∑ r ∈ F, ‖a r * weightedPhaseSum s w t r‖ :=
          norm_sum_le _ _
        _ = ∑ r ∈ F, ‖a r‖ * ‖weightedPhaseSum s w t r‖ := by
          simp only [norm_mul]
        _ ≤ ∑ r ∈ F, ‖a r‖ * M := by
          apply Finset.sum_le_sum
          intro r hr
          exact mul_le_mul_of_nonneg_left (hphase r hr) (norm_nonneg _)
        _ = (∑ r ∈ F, ‖a r‖) * M := by rw [Finset.sum_mul]
        _ ≤ A * M := mul_le_mul_of_nonneg_right hcoeff hM
  linarith

/-- Applying upper majorants to both `f` and `-f` bounds the absolute value
of the weighted sum. -/
lemma abs_weighted_sum_le_of_majorants { ι : Type* }
    (s : Finset ι) (w : ι → ℝ) (t : ι → ℝ)
    (F : Finset ℤ) (f : ℝ → ℝ) (c A M : ℝ)
    (aPlus aMinus : ℤ → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hplus : IsUpperMajorant F f c aPlus)
    (hminus : IsUpperMajorant F (fun x ↦ -f x) c aMinus)
    (hphase : ∀ r ∈ F, ‖weightedPhaseSum s w t r‖ ≤ M)
    (hcoeffPlus : ∑ r ∈ F, ‖aPlus r‖ ≤ A)
    (hcoeffMinus : ∑ r ∈ F, ‖aMinus r‖ ≤ A)
    (hM : 0 ≤ M) :
    |∑ i ∈ s, w i * f (t i)| ≤
      c * ∑ i ∈ s, w i + A * M := by
  rw [abs_le]
  constructor
  · have h := weighted_sum_le_of_upperMajorant s w t F (fun x ↦ -f x)
      c A M aMinus hw hminus hphase hcoeffMinus hM
    simpa only [mul_neg, Finset.sum_neg_distrib, neg_le] using h
  · exact weighted_sum_le_of_upperMajorant s w t F f c A M aPlus hw hplus
      hphase hcoeffPlus hM

end Sawtooth

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/FourierCoefficients.lean` -/

section
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# The degree-ten Vaaler coefficients used in Erdős problem 175

This file contains the finite numerical part of Granville--Ramaré's
degree-`10` sawtooth estimate.  In particular, it proves the sharp finite
coefficient bound which is responsible for the constants `43 / 6` and
`11 / 8` in their equation (7.2).
-/

noncomputable section

namespace FourierCoefficients

open Set

/-- The imaginary coordinate of either degree-ten majorant/minorant
coefficient at positive frequency `k`. -/
def imagAmplitude (k : ℕ) : ℝ :=
  (Real.pi * (1 - (k : ℝ) / 11) *
      Real.cot (Real.pi * (k : ℝ) / 11) + 1) / (22 * Real.pi)

/-- The absolute value of the real coordinate at positive frequency `k`. -/
def realAmplitude (k : ℕ) : ℝ := (1 - (k : ℝ) / 11) / 22

/-- A positive-frequency Vaaler coefficient.  `ε = 1` is the majorant and
`ε = -1` is the minorant. -/
def signedPositiveCoeff (ε : ℝ) (k : ℕ) : ℂ :=
  (ε * realAmplitude k : ℝ) + (imagAmplitude k : ℂ) * Complex.I

@[simp] lemma signedPositiveCoeff_re (ε : ℝ) (k : ℕ) :
    (signedPositiveCoeff ε k).re = ε * realAmplitude k := by
  simp [signedPositiveCoeff]

@[simp] lemma signedPositiveCoeff_im (ε : ℝ) (k : ℕ) :
    (signedPositiveCoeff ε k).im = imagAmplitude k := by
  simp [signedPositiveCoeff]

/-- Granville--Ramaré's coefficient `a_r^ε` for `R = 10`.  The value at
frequency zero is set to zero because the Fourier sum omits that frequency. -/
def degreeTenCoeff (ε : ℝ) (r : ℤ) : ℂ :=
  if r = 0 then 0 else
    ((ε * (1 - (r.natAbs : ℝ) / 11) / 22 : ℝ) : ℂ) +
      (((Real.pi * (1 - (r.natAbs : ℝ) / 11) *
          Real.cot (Real.pi * (r : ℝ) / 11) +
          (r.natAbs : ℝ) / (r : ℝ)) / (22 * Real.pi) : ℝ) : ℂ) * Complex.I

@[simp] lemma degreeTenCoeff_zero (ε : ℝ) : degreeTenCoeff ε 0 = 0 := by
  simp [degreeTenCoeff]

/-- The exact integer-frequency formula reduces to the positive-frequency
coordinate form. -/
lemma degreeTenCoeff_ofNat (ε : ℝ) {k : ℕ} (hk : k ≠ 0) :
    degreeTenCoeff ε (k : ℤ) = signedPositiveCoeff ε k := by
  rw [degreeTenCoeff, if_neg (by exact_mod_cast hk)]
  simp only [Int.natAbs_natCast, Int.cast_natCast]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  dsimp [signedPositiveCoeff, imagAmplitude, realAmplitude]
  field_simp [hkR, Real.pi_ne_zero]

/-- Negative-frequency coefficients are conjugates of the corresponding
positive-frequency coefficients. -/
lemma degreeTenCoeff_neg_ofNat (ε : ℝ) {k : ℕ} (hk : k ≠ 0) :
    degreeTenCoeff ε (-(k : ℤ)) =
      ((ε * realAmplitude k : ℝ) : ℂ) - (imagAmplitude k : ℂ) * Complex.I := by
  have hkz : -(k : ℤ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast hk)
  rw [degreeTenCoeff, if_neg hkz]
  simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast]
  have hcot : Real.cot (-(Real.pi * (k : ℝ) / 11)) =
      -Real.cot (Real.pi * (k : ℝ) / 11) := by
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
      Real.sin_neg, Real.cos_neg]
    ring
  rw [show Real.pi * (-(k : ℝ)) / 11 =
    -(Real.pi * (k : ℝ) / 11) by ring, hcot]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hscalar :
      (Real.pi * (1 - (k : ℝ) / 11) *
          (-Real.cot (Real.pi * (k : ℝ) / 11)) +
          (k : ℝ) / (-(k : ℝ))) / (22 * Real.pi) =
        -imagAmplitude k := by
    dsimp [imagAmplitude]
    field_simp [hkR, Real.pi_ne_zero]
    ring
  rw [hscalar]
  dsimp [realAmplitude]
  push_cast
  ring

@[simp] lemma norm_degreeTenCoeff_ofNat (ε : ℝ) {k : ℕ} (hk : k ≠ 0) :
    ‖degreeTenCoeff ε (k : ℤ)‖ = ‖signedPositiveCoeff ε k‖ := by
  rw [degreeTenCoeff_ofNat ε hk]

@[simp] lemma norm_degreeTenCoeff_neg_ofNat (ε : ℝ) {k : ℕ} (hk : k ≠ 0) :
    ‖degreeTenCoeff ε (-(k : ℤ))‖ = ‖signedPositiveCoeff ε k‖ := by
  rw [degreeTenCoeff_neg_ofNat ε hk]
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [RCLike.norm_sq_eq_def, RCLike.norm_sq_eq_def]
  simp [signedPositiveCoeff]

/-! ### Identification with the sawtooth module -/

/-! ### The degree-eleven Fejér square -/

lemma e_add (x y : ℝ) :
    Sawtooth.e (x + y) = Sawtooth.e x * Sawtooth.e y := by
  unfold Sawtooth.e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end FourierCoefficients

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/ExplicitChebyshev.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Explicit elementary Chebyshev estimates for Erdős 175

This file develops the five-term Chebyshev weight

`⌊t⌋ - ⌊t/2⌋ - ⌊t/3⌋ - ⌊t/5⌋ + ⌊t/30⌋`.

The weight is nonnegative, is at least one on `[1,6)`, and is at most one.
Together with the exact von Mangoldt--factorial convolution and explicit
Stirling remainders, these facts give effective lower and upper estimates for
`Chebyshev.psi`.  The constants are intentionally coarser than the best known
ones; the cutoff in Erdős 175 is so large that these bounds are ample.
-/

namespace ExplicitChebyshev

open ArithmeticFunction Finset Real
open scoped Chebyshev

noncomputable section

/-- The floor-weight used in Chebyshev's five-term approximation. -/
def chi (n : ℕ) : ℤ :=
  (n : ℤ) - (n / 2 : ℕ) - (n / 3 : ℕ) - (n / 5 : ℕ) + (n / 30 : ℕ)

lemma chi_add_thirty (n : ℕ) : chi (n + 30) = chi n := by
  unfold chi
  norm_num [Nat.add_div_of_dvd_left]
  omega

lemma chi_nonneg (n : ℕ) : 0 ≤ chi n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 30
      · interval_cases n <;> norm_num [chi]
      · have hsub : n - 30 < n := by omega
        have hadd : n - 30 + 30 = n := by omega
        rw [← hadd, chi_add_thirty]
        exact ih (n - 30) hsub

lemma chi_le_one (n : ℕ) : chi n ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 30
      · interval_cases n <;> norm_num [chi]
      · have hsub : n - 30 < n := by omega
        have hadd : n - 30 + 30 = n := by omega
        rw [← hadd, chi_add_thirty]
        exact ih (n - 30) hsub

lemma one_le_chi_of_lt_six {n : ℕ} (hn1 : 1 ≤ n) (hn6 : n < 6) :
    1 ≤ chi n := by
  interval_cases n <;> norm_num [chi]

/-- The floor-weighted von Mangoldt convolution. -/
def mangoldtFloorConvolution (n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 n, Λ d * (n / d : ℕ)

/-- Exact factorial convolution for von Mangoldt's function. -/
lemma mangoldtFloorConvolution_eq_log_factorial (n : ℕ) :
    mangoldtFloorConvolution n = Real.log (n.factorial : ℝ) := by
  induction n with
  | zero => simp [mangoldtFloorConvolution]
  | succ n ih =>
      have hdivisors :
          (n + 1).divisors =
            insert (n + 1) ((Icc 1 n).filter (· ∣ n + 1)) := by
        ext d
        simp only [Nat.mem_divisors, mem_insert, mem_filter, mem_Icc]
        constructor
        · rintro ⟨hd, hn⟩
          by_cases heq : d = n + 1
          · exact Or.inl heq
          · right
            have hd0 : d ≠ 0 := by rintro rfl; simp at hd
            exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hd0,
              by have := Nat.le_of_dvd (by omega : 0 < n + 1) hd; omega⟩, hd⟩
        · rintro (rfl | ⟨hdI, hd⟩)
          · exact ⟨dvd_rfl, by omega⟩
          · exact ⟨hd, by omega⟩
      have hnot : n + 1 ∉ (Icc 1 n).filter (· ∣ n + 1) := by simp
      have hcorrection :
          (∑ d ∈ Icc 1 n, if d ∣ n + 1 then Λ d else 0) + Λ (n + 1) =
            Real.log (n + 1) := by
        rw [← sum_filter, add_comm, ← sum_insert hnot, ← hdivisors]
        simpa only [Nat.cast_add, Nat.cast_one] using
          (ArithmeticFunction.vonMangoldt_sum (n := n + 1))
      calc
        mangoldtFloorConvolution (n + 1) =
            (∑ d ∈ Icc 1 n,
              Λ d * ((n / d : ℕ) + if d ∣ n + 1 then 1 else 0)) + Λ (n + 1) := by
          rw [mangoldtFloorConvolution,
            sum_Icc_succ_top (show 1 ≤ n + 1 by omega)]
          simp only [Nat.succ_div, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
            Nat.cast_zero]
          congr 1
          simp [Nat.div_eq_of_lt (Nat.lt_succ_self n)]
        _ = mangoldtFloorConvolution n +
            ((∑ d ∈ Icc 1 n, if d ∣ n + 1 then Λ d else 0) + Λ (n + 1)) := by
          rw [mangoldtFloorConvolution]
          simp_rw [mul_add]
          rw [sum_add_distrib]
          simp only [mul_ite, mul_one, mul_zero]
          ring_nf
        _ = Real.log (n.factorial : ℝ) + Real.log (n + 1) := by rw [ih, hcorrection]
        _ = Real.log ((n + 1).factorial : ℝ) := by
          rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul]
          · norm_num [add_comm]
          · positivity
          · positivity

/-- A convenient elementary upper half of Stirling's estimate. -/
lemma log_factorial_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      n * Real.log n - n + 1 + Real.log n := by
  induction hn <;> simp_all +decide [Nat.factorial_succ]
  rw [Real.log_mul (by positivity) (by positivity), add_comm]
  have h := Real.log_le_sub_one_of_pos
    (by positivity : 0 < (↑‹ℕ› : ℝ) / (↑‹ℕ› + 1))
  rw [Real.log_div] at h <;>
    first | positivity |
      nlinarith [mul_div_cancel₀ ((↑‹ℕ› : ℝ) : ℝ)
        (by positivity : (↑‹ℕ› + 1 : ℝ) ≠ 0)]

/-- The continuous main term in Stirling's formula. -/
def stirlingMain (x : ℝ) : ℝ := x * Real.log x - x

/-- Error made when `log (⌊x⌋₊!)` is compared with its continuous main term. -/
def factorialRemainder (x : ℝ) : ℝ :=
  Real.log (⌊x⌋₊.factorial : ℝ) - stirlingMain x

lemma stirlingMain_floor_le {x : ℝ} (hx : 3 ≤ x) :
    stirlingMain ⌊x⌋₊ ≤ stirlingMain x := by
  have hx0 : 0 ≤ x := by linarith
  have hn3 : 3 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 hx
  have hnle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have hn0 : (0 : ℝ) ≤ ⌊x⌋₊ := by positivity
  have hlogmono : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < ⌊x⌋₊ by omega))
    exact hnle
  have hlogone : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact Real.exp_one_lt_three.le.trans hx
  unfold stirlingMain
  calc
    (⌊x⌋₊ : ℝ) * Real.log ⌊x⌋₊ - ⌊x⌋₊ ≤
        (⌊x⌋₊ : ℝ) * Real.log x - ⌊x⌋₊ := by gcongr
    _ ≤ x * Real.log x - x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hnle) (sub_nonneg.mpr hlogone)]

lemma stirlingMain_sub_floor_le_log {x : ℝ} (hx : 3 ≤ x) :
    stirlingMain x - stirlingMain ⌊x⌋₊ ≤ Real.log x := by
  have hnpos : (0 : ℝ) < ⌊x⌋₊ := by
    exact_mod_cast (show 0 < ⌊x⌋₊ from by
      have : 3 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).2 hx
      omega)
  have hxpos : 0 < x := by positivity
  have hnle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hgap : x - (⌊x⌋₊ : ℝ) ≤ 1 := (Nat.self_sub_floor_lt_one x).le
  have hratio := Real.log_le_sub_one_of_pos (div_pos hxpos hnpos)
  rw [Real.log_div hxpos.ne' hnpos.ne'] at hratio
  have hmul := mul_le_mul_of_nonneg_left hratio hnpos.le
  have hquot : (⌊x⌋₊ : ℝ) * (x / ⌊x⌋₊ - 1) = x - ⌊x⌋₊ := by
    field_simp
  rw [hquot] at hmul
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  unfold stirlingMain
  calc
    x * Real.log x - x -
        ((⌊x⌋₊ : ℝ) * Real.log ⌊x⌋₊ - ⌊x⌋₊) =
        (x - ⌊x⌋₊) * Real.log x +
          (⌊x⌋₊ : ℝ) * (Real.log x - Real.log ⌊x⌋₊) -
            (x - ⌊x⌋₊) := by ring
    _ ≤ (x - ⌊x⌋₊) * Real.log x := by linarith
    _ ≤ 1 * Real.log x := by gcongr
    _ = Real.log x := one_mul _

lemma factorialRemainder_abs_le {x : ℝ} (hx : 3 ≤ x) :
    |factorialRemainder x| ≤ Real.log x + 1 := by
  have hn : 1 ≤ ⌊x⌋₊ := by
    have : 3 ≤ ⌊x⌋₊ := (Nat.le_floor_iff (by linarith)).2 hx
    omega
  have hupper := log_factorial_le ⌊x⌋₊ hn
  have hlower := Stirling.le_log_factorial_stirling (n := ⌊x⌋₊) (by omega)
  have hlogfloor_nonneg : 0 ≤ Real.log (⌊x⌋₊ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by
    have := Real.pi_gt_three
    nlinarith)
  have hnatlower : stirlingMain ⌊x⌋₊ ≤ Real.log (⌊x⌋₊.factorial : ℝ) := by
    unfold stirlingMain
    linarith
  have hremLower : -(Real.log x) ≤ factorialRemainder x := by
    unfold factorialRemainder
    linarith [stirlingMain_sub_floor_le_log hx]
  have hremUpper : factorialRemainder x ≤ Real.log x + 1 := by
    have hlogmono : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := by
      apply Real.log_le_log (by exact_mod_cast (show 0 < ⌊x⌋₊ by omega))
      exact Nat.floor_le (by linarith)
    have hupper' : Real.log (⌊x⌋₊.factorial : ℝ) ≤
        stirlingMain ⌊x⌋₊ + 1 + Real.log ⌊x⌋₊ := by
      simpa [stirlingMain] using hupper
    unfold factorialRemainder
    linarith [stirlingMain_floor_le hx]
  rw [abs_le]
  constructor
  · have hlog0 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ x)
    linarith
  · exact hremUpper

/-- Chebyshev's five-term constant, written using only `log 2`, `log 3`,
and `log 5`.  It is approximately `0.92129`. -/
def alpha : ℝ :=
  (7 / 15 : ℝ) * Real.log 2 + (3 / 10 : ℝ) * Real.log 3 +
    (1 / 6 : ℝ) * Real.log 5

lemma nine_tenths_le_alpha : (9 / 10 : ℝ) ≤ alpha := by
  unfold alpha
  nlinarith [Real.log_two_gt_d9, Real.log_three_gt_d9,
    Real.log_five_gt_d9]

lemma alpha_le_fourteen_fifteenths : alpha ≤ (14 / 15 : ℝ) := by
  unfold alpha
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9]

/-- The five-term logarithmic factorial combination. -/
def weightedFactorial (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) - Real.log ((n / 2).factorial : ℝ) -
    Real.log ((n / 3).factorial : ℝ) - Real.log ((n / 5).factorial : ℝ) +
      Real.log ((n / 30).factorial : ℝ)

lemma mangoldtFloorConvolution_div (n k : ℕ) (hk : 0 < k) :
    Real.log ((n / k).factorial : ℝ) =
      ∑ d ∈ Icc 1 n, Λ d * ((n / k) / d : ℕ) := by
  rw [← mangoldtFloorConvolution_eq_log_factorial, mangoldtFloorConvolution]
  apply sum_subset
  · intro d hd
    simp only [mem_Icc] at hd ⊢
    exact ⟨hd.1, hd.2.trans (Nat.div_le_self n k)⟩
  · intro d hd hdnot
    simp only [mem_Icc] at hd hdnot
    have hlt : n / k < d := by
      by_contra h
      apply hdnot
      exact ⟨hd.1, by omega⟩
    rw [Nat.div_eq_of_lt hlt, Nat.cast_zero, mul_zero]

lemma weightedFactorial_eq_sum_chi (n : ℕ) :
    weightedFactorial n =
      ∑ d ∈ Icc 1 n, Λ d * (chi (n / d) : ℤ) := by
  have h1 : Real.log (n.factorial : ℝ) =
      ∑ d ∈ Icc 1 n, Λ d * (n / d : ℕ) := by
    simpa using mangoldtFloorConvolution_div n 1 (by norm_num)
  rw [weightedFactorial,
    h1,
    mangoldtFloorConvolution_div n 2 (by norm_num),
    mangoldtFloorConvolution_div n 3 (by norm_num),
    mangoldtFloorConvolution_div n 5 (by norm_num),
    mangoldtFloorConvolution_div n 30 (by norm_num)]
  rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib,
    ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  have hdpos : 0 < d := (mem_Icc.mp hd).1
  simp only [chi]
  simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast]
  simp only [Nat.div_div_eq_div_mul]
  rw [mul_comm 2 d, mul_comm 3 d, mul_comm 5 d, mul_comm 30 d]
  ring

lemma sum_vonMangoldt_Icc_eq_psi (n : ℕ) :
    (∑ d ∈ Icc 1 n, Λ d) = Chebyshev.psi n := by
  symm
  simp [Chebyshev.psi, ← Icc_add_one_left_eq_Ioc]

/-- The weighted factorial is bounded above by `psi`. -/
lemma weightedFactorial_le_psi (n : ℕ) :
    weightedFactorial n ≤ Chebyshev.psi n := by
  rw [weightedFactorial_eq_sum_chi, ← sum_vonMangoldt_Icc_eq_psi]
  apply sum_le_sum
  intro d hd
  have hchi : ((chi (n / d) : ℤ) : ℝ) ≤ 1 := by
    exact_mod_cast chi_le_one (n / d)
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hchi (ArithmeticFunction.vonMangoldt_nonneg)

/-- The weighted factorial dominates the von Mangoldt mass in `(n/6,n]`. -/
lemma interval_mangoldt_le_weightedFactorial (n : ℕ) :
    (∑ d ∈ Ioc (n / 6) n, Λ d) ≤ weightedFactorial n := by
  rw [weightedFactorial_eq_sum_chi]
  calc
    (∑ d ∈ Ioc (n / 6) n, Λ d) ≤
        ∑ d ∈ Ioc (n / 6) n, Λ d * (chi (n / d) : ℤ) := by
      apply sum_le_sum
      intro d hd
      have hd' := mem_Ioc.mp hd
      have hdpos : 0 < d := by
        have : n / 6 < d := hd'.1
        omega
      have hone : 1 ≤ n / d := (Nat.one_le_div_iff hdpos).2 hd'.2
      have hsix : n / d < 6 := by
        rw [Nat.div_lt_iff_lt_mul hdpos]
        omega
      have hchi : (1 : ℝ) ≤ (chi (n / d) : ℤ) := by
        exact_mod_cast one_le_chi_of_lt_six hone hsix
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hchi ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ d ∈ Icc 1 n, Λ d * (chi (n / d) : ℤ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        simp only [mem_Ioc] at hd
        exact mem_Icc.mpr ⟨by omega, hd.2⟩
      · intro d hd _
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by
          exact_mod_cast chi_nonneg (n / d))

lemma stirlingMain_five_term {n : ℕ} (hn : 0 < n) :
    stirlingMain n - stirlingMain ((n : ℝ) / 2) -
        stirlingMain ((n : ℝ) / 3) - stirlingMain ((n : ℝ) / 5) +
          stirlingMain ((n : ℝ) / 30) = alpha * n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog30 : Real.log (30 : ℝ) =
      Real.log 2 + Real.log 3 + Real.log 5 := by
    calc
      Real.log (30 : ℝ) = Real.log ((2 : ℝ) * (3 * 5)) := by norm_num
      _ = Real.log 2 + Real.log (3 * 5) := by rw [Real.log_mul] <;> norm_num
      _ = Real.log 2 + (Real.log 3 + Real.log 5) := by
        rw [Real.log_mul] <;> norm_num
      _ = _ := by ring
  unfold stirlingMain alpha
  rw [Real.log_div hnR.ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hnR.ne' (by norm_num : (3 : ℝ) ≠ 0),
    Real.log_div hnR.ne' (by norm_num : (5 : ℝ) ≠ 0),
    Real.log_div hnR.ne' (by norm_num : (30 : ℝ) ≠ 0), hlog30]
  ring

lemma weightedFactorial_eq_alpha_add_remainders {n : ℕ} (hn : 0 < n) :
    weightedFactorial n = alpha * n + factorialRemainder n -
        factorialRemainder ((n : ℝ) / 2) -
        factorialRemainder ((n : ℝ) / 3) -
        factorialRemainder ((n : ℝ) / 5) +
        factorialRemainder ((n : ℝ) / 30) := by
  have hmain := stirlingMain_five_term hn
  unfold weightedFactorial factorialRemainder
  simp only [Nat.floor_natCast, Nat.floor_div_ofNat]
  linarith

lemma log_div_le_log {x c : ℝ} (hx : 1 ≤ x) (hc : 1 ≤ c) :
    Real.log (x / c) ≤ Real.log x := by
  apply Real.log_le_log (by positivity)
  exact div_le_self (by positivity) hc

/-- Effective lower bound needed for the square-root interval in the
Granville--Ramaré argument. -/
lemma psi_lower_nat (n : ℕ) (hn : 90 ≤ n) :
    (9 / 10 : ℝ) * n - (5 * Real.log n + 5) ≤ Chebyshev.psi n := by
  have hnpos : 0 < n := by omega
  have hnR : (90 : ℝ) ≤ n := by exact_mod_cast hn
  have hargs :
      (3 : ℝ) ≤ n ∧ (3 : ℝ) ≤ n / 2 ∧ (3 : ℝ) ≤ n / 3 ∧
        (3 : ℝ) ≤ n / 5 ∧ (3 : ℝ) ≤ n / 30 := by
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith
  rcases hargs with ⟨hn3, hn2, hn3', hn5, hn30⟩
  have hrn := factorialRemainder_abs_le hn3
  have hr2 := factorialRemainder_abs_le hn2
  have hr3 := factorialRemainder_abs_le hn3'
  have hr5 := factorialRemainder_abs_le hn5
  have hr30 := factorialRemainder_abs_le hn30
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by nlinarith [hnR])
  have hl2 : Real.log ((n : ℝ) / 2) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hl3 : Real.log ((n : ℝ) / 3) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hl5 : Real.log ((n : ℝ) / 5) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hl30 : Real.log ((n : ℝ) / 30) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hw : alpha * n - (5 * Real.log n + 5) ≤ weightedFactorial n := by
    rw [weightedFactorial_eq_alpha_add_remainders hnpos]
    rw [abs_le] at hrn hr2 hr3 hr5 hr30
    linarith
  exact (by
    calc
      (9 / 10 : ℝ) * n - (5 * Real.log n + 5) ≤
          alpha * n - (5 * Real.log n + 5) := by
        gcongr
        exact nine_tenths_le_alpha
      _ ≤ weightedFactorial n := hw
      _ ≤ Chebyshev.psi n := weightedFactorial_le_psi n)

lemma weightedFactorial_upper (n : ℕ) (hn : 90 ≤ n) :
    weightedFactorial n ≤ alpha * n + (5 * Real.log n + 5) := by
  have hnpos : 0 < n := by omega
  have hnR : (90 : ℝ) ≤ n := by exact_mod_cast hn
  have hn3 : (3 : ℝ) ≤ n := by nlinarith
  have hn2 : (3 : ℝ) ≤ n / 2 := by nlinarith
  have hn3' : (3 : ℝ) ≤ n / 3 := by nlinarith
  have hn5 : (3 : ℝ) ≤ n / 5 := by nlinarith
  have hn30 : (3 : ℝ) ≤ n / 30 := by nlinarith
  have hrn := factorialRemainder_abs_le hn3
  have hr2 := factorialRemainder_abs_le hn2
  have hr3 := factorialRemainder_abs_le hn3'
  have hr5 := factorialRemainder_abs_le hn5
  have hr30 := factorialRemainder_abs_le hn30
  have hl2 : Real.log ((n : ℝ) / 2) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hl3 : Real.log ((n : ℝ) / 3) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hl5 : Real.log ((n : ℝ) / 5) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  have hl30 : Real.log ((n : ℝ) / 30) ≤ Real.log n :=
    log_div_le_log (by nlinarith [hnR]) (by norm_num)
  rw [weightedFactorial_eq_alpha_add_remainders hnpos]
  rw [abs_le] at hrn hr2 hr3 hr5 hr30
  linarith

lemma psi_eq_psi_div_six_add_interval (n : ℕ) :
    Chebyshev.psi n = Chebyshev.psi ((n / 6 : ℕ) : ℝ) +
      ∑ d ∈ Ioc (n / 6) n, Λ d := by
  simp only [Chebyshev.psi, Nat.floor_natCast]
  have hsets : Ioc 0 n = Ioc 0 (n / 6) ∪ Ioc (n / 6) n := by
    ext d
    simp only [mem_Ioc, mem_union]
    omega
  rw [hsets, sum_union]
  apply Finset.disjoint_left.mpr
  intro d hd1 hd2
  simp only [mem_Ioc] at hd1 hd2
  omega

lemma psi_rec (n : ℕ) (hn : 90 ≤ n) :
    Chebyshev.psi n ≤
      Chebyshev.psi ((n / 6 : ℕ) : ℝ) + alpha * n +
        (5 * Real.log n + 5) := by
  rw [psi_eq_psi_div_six_add_interval]
  have hi := (interval_mangoldt_le_weightedFactorial n).trans
    (weightedFactorial_upper n hn)
  linarith

/-- A global effective upper bound.  Its leading coefficient `28/25 = 1.12`
is small enough, together with `psi_lower_nat`, to leave a positive amount of
von Mangoldt mass in a square-root interval. -/
lemma psi_upper_nat (n : ℕ) :
    Chebyshev.psi n ≤
      (28 / 25 : ℝ) * n + 20 * Real.log n ^ 2 + 20000 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 1980
      · have hpsi := Chebyshev.psi_le_const_mul_self (x := (n : ℝ)) (by positivity)
        have hlog4 : Real.log 4 ≤ 3 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
          norm_num at this ⊢
          exact this
        have hnR : (n : ℝ) ≤ 1980 := by exact_mod_cast hn.le
        have hlogsq : 0 ≤ Real.log (n : ℝ) ^ 2 := sq_nonneg _
        nlinarith
      · have hn1980 : 1980 ≤ n := by omega
        have hn90 : 90 ≤ n := by omega
        let m := n / 6
        have hm_lt : m < n := by
          dsimp [m]
          omega
        have hm330 : 330 ≤ m := by
          dsimp [m]
          omega
        have hih := ih m hm_lt
        have hrec := psi_rec n hn90
        have hnR : (1980 : ℝ) ≤ n := by exact_mod_cast hn1980
        have hmR : (330 : ℝ) ≤ m := by exact_mod_cast hm330
        have hm_le : (m : ℝ) ≤ (n : ℝ) / 6 := by
          dsimp [m]
          exact Nat.cast_div_le
        have hlogn1 : 1 ≤ Real.log (n : ℝ) := by
          rw [Real.le_log_iff_exp_le (by positivity)]
          exact Real.exp_one_lt_three.le.trans (by nlinarith [hnR])
        have hlogm0 : 0 ≤ Real.log (m : ℝ) :=
          Real.log_nonneg (by nlinarith [hmR])
        have hlog3 : 1 ≤ Real.log (3 : ℝ) := by
          rw [Real.le_log_iff_exp_le (by norm_num)]
          exact Real.exp_one_lt_three.le
        have hm_le_third : (m : ℝ) ≤ (n : ℝ) / 3 := by nlinarith [hm_le]
        have hlogm_le : Real.log (m : ℝ) ≤ Real.log (n : ℝ) - 1 := by
          have h := Real.log_le_log (by nlinarith [hmR]) hm_le_third
          rw [Real.log_div (by positivity : (n : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at h
          linarith
        have hsq : Real.log (m : ℝ) ^ 2 ≤
            (Real.log (n : ℝ) - 1) ^ 2 := by
          exact (sq_le_sq₀ hlogm0 (by linarith)).2 hlogm_le
        have herror :
            20 * Real.log (m : ℝ) ^ 2 + (5 * Real.log n + 5) ≤
              20 * Real.log n ^ 2 := by
          nlinarith
        have hlin :
            (28 / 25 : ℝ) * m + alpha * n ≤ (28 / 25 : ℝ) * n := by
          have ha := alpha_le_fourteen_fifteenths
          nlinarith
        calc
          Chebyshev.psi n ≤ Chebyshev.psi m + alpha * n +
              (5 * Real.log n + 5) := by simpa [m] using hrec
          _ ≤ ((28 / 25 : ℝ) * m + 20 * Real.log m ^ 2 + 20000) +
              alpha * n + (5 * Real.log n + 5) := by gcongr
          _ ≤ (28 / 25 : ℝ) * n + 20 * Real.log n ^ 2 + 20000 := by
            nlinarith

lemma psi_eq_psi_add_interval {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.psi b = Chebyshev.psi a + ∑ d ∈ Ioc a b, Λ d := by
  simp only [Chebyshev.psi, Nat.floor_natCast]
  have hsets : Ioc 0 b = Ioc 0 a ∪ Ioc a b := by
    ext d
    simp only [mem_Ioc, mem_union]
    omega
  rw [hsets, sum_union]
  apply Finset.disjoint_left.mpr
  intro d hd1 hd2
  simp only [mem_Ioc] at hd1 hd2
  omega

/-- The fully explicit form of the square-root interval estimate.  Unlike the
very sharp estimate of Dusart used in the printed proof, this only uses the
elementary five-term Chebyshev weight above.  The leading constant is still
large enough for the later Fourier argument; the logarithmic error is made
negligible by the (very large) cutoff in that argument. -/
lemma sqrtInterval_mangoldt_lower_with_error (n : ℕ) (hn : 4050 ≤ n) :
    (763 / 5000 : ℝ) * Real.sqrt n -
          (20 * Real.log n ^ 2 + 5 * Real.log (2 * n) + 20006) ≤
      ∑ d ∈ Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)), Λ d := by
  let a := Nat.sqrt n
  let b := Nat.sqrt (2 * n)
  have hnpos : 0 < n := by omega
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Nat.sqrt_le_sqrt (by omega)
  have hb90 : 90 ≤ b := by
    dsimp [b]
    rw [Nat.le_sqrt]
    omega
  have hlower := psi_lower_nat b hb90
  have hupper := psi_upper_nat a
  have hpsi := psi_eq_psi_add_interval hab
  have ha_sqrt : (a : ℝ) ≤ Real.sqrt n := by
    dsimp [a]
    exact Real.nat_sqrt_le_real_sqrt
  have hb_sqrt : Real.sqrt (2 * (n : ℝ)) - 1 ≤ (b : ℝ) := by
    dsimp [b]
    have h := Real.real_sqrt_lt_nat_sqrt_succ (a := 2 * n)
    norm_num [Nat.cast_mul] at h ⊢
    linarith
  have hsqrt2 : (707 / 500 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    norm_num
  have hsqrt_mul : Real.sqrt (2 * (n : ℝ)) =
      Real.sqrt 2 * Real.sqrt n := Real.sqrt_mul (by norm_num) _
  have hsqrtn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have ha_le_n : a ≤ n := by
    dsimp [a]
    exact Nat.sqrt_le_self n
  have hb_le_two_n : b ≤ 2 * n := by
    dsimp [b]
    exact Nat.sqrt_le_self (2 * n)
  have hloga : Real.log (a : ℝ) ≤ Real.log n := by
    by_cases ha0 : a = 0
    · simp [ha0, Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hnpos)]
    · apply Real.log_le_log
      · exact_mod_cast (Nat.pos_of_ne_zero ha0)
      · exact_mod_cast ha_le_n
  have hlogb : Real.log (b : ℝ) ≤ Real.log (2 * n) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < b by omega)
    · exact_mod_cast hb_le_two_n
  have hloga0 : 0 ≤ Real.log (a : ℝ) := by
    have ha90 : 1 ≤ a := by
      dsimp [a]
      rw [Nat.le_sqrt]
      omega
    exact Real.log_nonneg (by exact_mod_cast ha90)
  have hlogsq : Real.log (a : ℝ) ^ 2 ≤ Real.log n ^ 2 := by
    exact (sq_le_sq₀ hloga0 (Real.log_nonneg (by exact_mod_cast hnpos))).2 hloga
  rw [hsqrt_mul] at hb_sqrt
  rw [hpsi] at hlower
  nlinarith

private lemma log_sq_le_quarter_power (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ^ 2 ≤ 64 * Real.sqrt (Real.sqrt x) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hlog := Real.log_le_rpow_div hx0 (show (0 : ℝ) < 1 / 8 by norm_num)
  have hu : 0 ≤ x ^ (1 / 8 : ℝ) := Real.rpow_nonneg hx0 _
  have hu2 : (x ^ (1 / 8 : ℝ)) ^ 2 = Real.sqrt (Real.sqrt x) := by
    calc
      (x ^ (1 / 8 : ℝ)) ^ 2 = (x ^ (1 / 8 : ℝ)) ^ (2 : ℝ) := by
        exact (Real.rpow_natCast (x ^ (1 / 8 : ℝ)) 2).symm
      _ = x ^ ((1 / 8 : ℝ) * 2) := (Real.rpow_mul hx0 _ _).symm
      _ = x ^ ((1 / 2 : ℝ) * (1 / 2 : ℝ)) := by
        norm_num
      _ = (x ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := Real.rpow_mul hx0 _ _
      _ = Real.sqrt (Real.sqrt x) := by simp [Real.sqrt_eq_rpow]
  have hlog' : Real.log x ≤ 8 * x ^ (1 / 8 : ℝ) := by
    convert hlog using 1 <;> ring
  have hsq := (sq_le_sq₀ (Real.log_nonneg hx) (by positivity : 0 ≤ 8 * x ^ (1 / 8 : ℝ))).2 hlog'
  nlinarith [hu2]

private lemma explicit_error_le_margin (n : ℕ) (hn : 2 ^ 1728 ≤ n) :
    20 * Real.log n ^ 2 + 5 * Real.log (2 * n) + 20006 ≤
      (13 / 5000 : ℝ) * Real.sqrt n := by
  have hnpos : 0 < n := (by positivity : 0 < 2 ^ 1728).trans_le hn
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hlargeCutoff : 10 ^ 24 ≤ 2 ^ 1728 := by
    calc
      10 ^ 24 ≤ 16 ^ 24 := Nat.pow_le_pow_left (by norm_num) 24
      _ = 2 ^ 96 := by norm_num [← pow_mul]
      _ ≤ 2 ^ 1728 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hnlargeNat : 10 ^ 24 ≤ n := hlargeCutoff.trans hn
  have hnlarge : (10 : ℝ) ^ 24 ≤ n := by exact_mod_cast hnlargeNat
  have hsqrt1 := Real.sqrt_le_sqrt hnlarge
  have hsqrt2 := Real.sqrt_le_sqrt hsqrt1
  have hbase : Real.sqrt (Real.sqrt ((10 : ℝ) ^ 24)) = 10 ^ 6 := by
    rw [show (24 : ℕ) = 12 * 2 by norm_num, pow_mul,
      Real.sqrt_sq (by positivity)]
    rw [show (12 : ℕ) = 6 * 2 by norm_num, pow_mul,
      Real.sqrt_sq (by positivity)]
  rw [hbase] at hsqrt2
  have hq : (1000000 : ℝ) ≤ Real.sqrt (Real.sqrt n) := by
    norm_num at hsqrt2 ⊢
    exact hsqrt2
  clear hn hlargeCutoff hnlargeNat hnlarge hsqrt1 hsqrt2 hbase
  have hq0 : 0 ≤ Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_nonneg _
  have hq_sq : Real.sqrt (Real.sqrt (n : ℝ)) ^ 2 = Real.sqrt n :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hlogsq := log_sq_le_quarter_power (n : ℝ) hnone
  have hlogn_linear : Real.log (n : ℝ) ≤ Real.log n ^ 2 + 1 := by
    nlinarith [sq_nonneg (Real.log (n : ℝ) - 1 / 2)]
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlogmul : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast hnpos.ne')]
  have herr : 20 * Real.log n ^ 2 + 5 * Real.log (2 * n) + 20006 ≤
      1600 * Real.sqrt (Real.sqrt n) + 20016 := by
    rw [hlogmul]
    nlinarith
  have hqmul : 1000000 * Real.sqrt (Real.sqrt (n : ℝ)) ≤
      Real.sqrt (Real.sqrt n) ^ 2 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
  rw [hq_sq] at hqmul
  nlinarith

/-- A clean square-root interval lower bound at the cutoff used by the coarse
Granville--Ramaré assembly. -/
theorem sqrtInterval_mangoldt_lower (n : ℕ) (hn : 2 ^ 1728 ≤ n) :
    (3 / 20 : ℝ) * Real.sqrt n ≤
      ∑ d ∈ Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)), Λ d := by
  have hsmallCutoff : 4050 ≤ 2 ^ 1728 := by
    calc
      4050 ≤ 2 ^ 12 := by norm_num
      _ ≤ 2 ^ 1728 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hn4050 : 4050 ≤ n := hsmallCutoff.trans hn
  have hmain := sqrtInterval_mangoldt_lower_with_error n hn4050
  have herr := explicit_error_le_margin n hn
  linarith

/-- Numerical bridge for the final degree-three constants
`c = 33 / 200`, `A = 3 / 4`.  In the normalization used by Section 7 these
constants give the loss `S ≤ 450 M + 100 log (2n)`. -/
theorem sqrtInterval_numeric_degree_three_450 (n : ℕ)
    (hn : 2 ^ 1728 ≤ n) :
    (1 / 5000 : ℝ) * Real.sqrt n <
      (1 / 450 : ℝ) *
        ((3 / 20 : ℝ) * Real.sqrt n - 100 * Real.log (2 * n)) := by
  have herr := explicit_error_le_margin n hn
  have hnpos : 0 < n := (by positivity : 0 < 2 ^ 1728).trans_le hn
  have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hnpos)
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  have hsmallLog : 5 * Real.log (2 * (n : ℝ)) ≤
      (13 / 5000 : ℝ) * Real.sqrt n := by
    nlinarith [sq_nonneg (Real.log (n : ℝ))]
  clear hn
  nlinarith

/-- Direct Mangoldt interval-sum version of
`sqrtInterval_numeric_degree_three_450`. -/
theorem sqrtInterval_mangoldt_degree_three_450 (n : ℕ)
    (hn : 2 ^ 1728 ≤ n) :
    (1 / 5000 : ℝ) * Real.sqrt n <
      (1 / 450 : ℝ) *
        ((∑ d ∈ Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)), Λ d) -
          100 * Real.log (2 * n)) := by
  have hnum := sqrtInterval_numeric_degree_three_450 n hn
  have hsum := sqrtInterval_mangoldt_lower n hn
  nlinarith

end

end ExplicitChebyshev

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/VaalerDegreeTen.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# An unconditional small Fourier majorant for the centered sawtooth

This file proves the pointwise analytic input needed in Section 7 of
Granville--Ramaré.  We use the order-three Vaaler polynomial and allow the
constant `13 / 80`, slightly larger than its optimal constant `1 / 8` but
still strictly smaller than `1 / 6`.  The slack makes the verification a
short, completely algebraic argument after the tangent half-angle
substitution.
-/

namespace VaalerDegreeTen

open scoped BigOperators

open Erdos175.Sawtooth

private lemma deriv_cubicPartialSum (y : ℝ) :
    deriv (fun z : ℝ ↦ z - z ^ 3 / 3) y = 1 - y ^ 2 := by
  change deriv ((fun z : ℝ ↦ z) - (fun z : ℝ ↦ z ^ 3 / 3)) y = _
  rw [deriv_sub (by fun_prop) (by fun_prop)]
  have hpow := (((hasDerivAt_id y : HasDerivAt (fun z : ℝ ↦ z) 1 y).pow 3).div_const 3).deriv
  change deriv (fun z : ℝ ↦ z ^ 3 / 3) y = _ at hpow
  rw [show deriv (fun z : ℝ ↦ z) y = 1 from congrFun deriv_id'' y, hpow]
  norm_num

private lemma deriv_quinticPartialSum (y : ℝ) :
    deriv (fun z : ℝ ↦ z - z ^ 3 / 3 + z ^ 5 / 5) y =
      1 - y ^ 2 + y ^ 4 := by
  change deriv ((fun z : ℝ ↦ z - z ^ 3 / 3) +
    (fun z : ℝ ↦ z ^ 5 / 5)) y = _
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_cubicPartialSum]
  have hpow := (((hasDerivAt_id y : HasDerivAt (fun z : ℝ ↦ z) 1 y).pow 5).div_const 5).deriv
  change deriv (fun z : ℝ ↦ z ^ 5 / 5) y = _ at hpow
  rw [hpow]
  norm_num

private lemma deriv_septicPartialSum (y : ℝ) :
    deriv (fun z : ℝ ↦ z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7) y =
      1 - y ^ 2 + y ^ 4 - y ^ 6 := by
  change deriv ((fun z : ℝ ↦ z - z ^ 3 / 3 + z ^ 5 / 5) -
    (fun z : ℝ ↦ z ^ 7 / 7)) y = _
  rw [deriv_sub (by fun_prop) (by fun_prop), deriv_quinticPartialSum]
  have hpow := (((hasDerivAt_id y : HasDerivAt (fun z : ℝ ↦ z) 1 y).pow 7).div_const 7).deriv
  change deriv (fun z : ℝ ↦ z ^ 7 / 7) y = _ at hpow
  rw [hpow]
  norm_num

private lemma arctan_lower_cubic (x : ℝ) (hx : 0 ≤ x) :
    x - x ^ 3 / 3 ≤ Real.arctan x := by
  let f : ℝ → ℝ := fun y ↦ Real.arctan y - (y - y ^ 3 / 3)
  have hf : Differentiable ℝ f := by
    exact Real.differentiable_arctan.sub (by fun_prop)
  have hmono : Monotone f := by
    apply monotone_of_deriv_nonneg hf
    intro y
    have hden : 0 < 1 + y ^ 2 := by positivity
    have hderiv : deriv f y = y ^ 4 / (1 + y ^ 2) := by
      change deriv (Real.arctan - (fun z : ℝ ↦ z - z ^ 3 / 3)) y = _
      rw [deriv_sub (Real.differentiableAt_arctan y) (by fun_prop),
        Real.deriv_arctan, deriv_cubicPartialSum]
      field_simp
      ring
    rw [hderiv]
    positivity
  have h := hmono hx
  simpa [f] using h

private lemma arctan_upper_quintic (x : ℝ) (hx : 0 ≤ x) :
    Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  let f : ℝ → ℝ := fun y ↦
    (y - y ^ 3 / 3 + y ^ 5 / 5) - Real.arctan y
  have hf : Differentiable ℝ f := by
    exact (by fun_prop : Differentiable ℝ (fun y : ℝ ↦
      y - y ^ 3 / 3 + y ^ 5 / 5)).sub Real.differentiable_arctan
  have hmono : Monotone f := by
    apply monotone_of_deriv_nonneg hf
    intro y
    have hden : 0 < 1 + y ^ 2 := by positivity
    have hderiv : deriv f y = y ^ 6 / (1 + y ^ 2) := by
      change deriv ((fun z : ℝ ↦ z - z ^ 3 / 3 + z ^ 5 / 5) -
        Real.arctan) y = _
      rw [deriv_sub (by fun_prop) (Real.differentiableAt_arctan y),
        Real.deriv_arctan, deriv_quinticPartialSum]
      field_simp
      ring
    rw [hderiv]
    positivity
  have h := hmono hx
  simpa [f] using h

private lemma arctan_lower_septic (x : ℝ) (hx : 0 ≤ x) :
    x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7 ≤ Real.arctan x := by
  let f : ℝ → ℝ := fun y ↦
    Real.arctan y - (y - y ^ 3 / 3 + y ^ 5 / 5 - y ^ 7 / 7)
  have hf : Differentiable ℝ f := by
    exact Real.differentiable_arctan.sub (by fun_prop)
  have hmono : Monotone f := by
    apply monotone_of_deriv_nonneg hf
    intro y
    have hden : 0 < 1 + y ^ 2 := by positivity
    have hderiv : deriv f y = y ^ 8 / (1 + y ^ 2) := by
      change deriv (Real.arctan -
        (fun z : ℝ ↦ z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7)) y = _
      rw [deriv_sub (Real.differentiableAt_arctan y) (by fun_prop),
        Real.deriv_arctan, deriv_septicPartialSum]
      field_simp
      ring
    rw [hderiv]
    positivity
  have h := hmono hx
  simpa [f] using h

private noncomputable def c1 : ℂ :=
  ⟨3 / 32, 3 / 32 + 1 / (8 * Real.pi)⟩

private noncomputable def c2 : ℂ :=
  ⟨1 / 16, 1 / (8 * Real.pi)⟩

private noncomputable def c3 : ℂ :=
  ⟨1 / 32, 1 / (8 * Real.pi) - 1 / 32⟩

/-- The order-three upper Vaaler coefficients.  They are written out
explicitly so that neither the pointwise theorem nor its coefficient bound
depends on a numerical oracle. -/
noncomputable def degreeThreePlusCoefficient (r : ℤ) : ℂ :=
  if r = 1 then c1
  else if r = -1 then starRingEnd ℂ c1
  else if r = 2 then c2
  else if r = -2 then starRingEnd ℂ c2
  else if r = 3 then c3
  else if r = -3 then starRingEnd ℂ c3
  else 0

/-- Reflection of the upper coefficients; this majorizes `-psi`. -/
noncomputable def degreeThreeMinusCoefficient (r : ℤ) : ℂ :=
  degreeThreePlusCoefficient (-r)

/-- The real trigonometric polynomial represented by
`degreeThreePlusCoefficient`. -/
noncomputable def degreeThreePolynomial (x : ℝ) : ℝ :=
  (3 / 16 : ℝ) * Real.cos (2 * Real.pi * x) +
    (1 / 8 : ℝ) * Real.cos (4 * Real.pi * x) +
    (1 / 16 : ℝ) * Real.cos (6 * Real.pi * x) -
    (3 / 16 + 1 / (4 * Real.pi) : ℝ) * Real.sin (2 * Real.pi * x) -
    (1 / (4 * Real.pi) : ℝ) * Real.sin (4 * Real.pi * x) -
    (1 / (4 * Real.pi) - 1 / 16 : ℝ) * Real.sin (6 * Real.pi * x)

private lemma frequencies_three : frequencies 3 = {-3, -2, -1, 1, 2, 3} := by
  change (Finset.Icc (-3 : ℤ) 3).erase 0 = _
  decide

private lemma e_eq_cos_add_sin (x : ℝ) : Sawtooth.e x =
    (Real.cos (2 * Real.pi * x) : ℂ) +
      Real.sin (2 * Real.pi * x) * Complex.I := by
  exact Complex.exp_ofReal_mul_I _

private lemma degreeThreePolynomial_eq (x : ℝ) :
    (fourierPolynomial (frequencies 3) degreeThreePlusCoefficient x).re =
      degreeThreePolynomial x := by
  rw [frequencies_three]
  simp only [fourierPolynomial, Finset.sum_insert, Finset.mem_insert,
    Finset.mem_singleton, reduceCtorEq, or_false, not_false_eq_true,
    Finset.sum_singleton]
  simp only [degreeThreePlusCoefficient]
  norm_num
  simp only [c1, c2, c3, e_eq_cos_add_sin]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero, zero_mul, Real.cos_neg, Real.sin_neg,
    map_neg, Complex.conj_re, Complex.conj_im]
  simp only [degreeThreePolynomial]
  ring_nf
  simp only [Real.cos_neg, Real.sin_neg]
  ring

private lemma degreeThreeMinusPolynomial_eq (x : ℝ) :
    (fourierPolynomial (frequencies 3) degreeThreeMinusCoefficient x).re =
      degreeThreePolynomial (-x) := by
  rw [frequencies_three]
  simp only [fourierPolynomial, Finset.sum_insert, Finset.mem_insert,
    Finset.mem_singleton, reduceCtorEq, or_false, not_false_eq_true,
    Finset.sum_singleton]
  simp only [degreeThreeMinusCoefficient, degreeThreePlusCoefficient]
  norm_num
  simp only [c1, c2, c3, e_eq_cos_add_sin]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero, zero_mul, Real.cos_neg, Real.sin_neg,
    degreeThreePolynomial, map_neg, Complex.conj_re, Complex.conj_im]
  ring_nf
  simp only [Real.cos_neg, Real.sin_neg]
  ring

private lemma degreeThreePolynomial_compressed (x : ℝ) :
    degreeThreePolynomial x =
      (-2 * Real.pi * (Real.sin (2 * Real.pi * x)) ^ 3 +
        2 * Real.pi * (Real.cos (2 * Real.pi * x)) ^ 3 +
        2 * Real.pi * (Real.cos (2 * Real.pi * x)) ^ 2 - Real.pi +
        8 * (Real.sin (2 * Real.pi * x)) ^ 3 -
        4 * Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x) -
        8 * Real.sin (2 * Real.pi * x)) / (8 * Real.pi) := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [degreeThreePolynomial]
  have h4 : 4 * Real.pi * x = 2 * (2 * Real.pi * x) := by ring
  have h6 : 6 * Real.pi * x = 3 * (2 * Real.pi * x) := by ring
  rw [h4, h6, Real.sin_two_mul, Real.cos_two_mul,
    Real.sin_three_mul, Real.cos_three_mul]
  have hs := Real.sin_sq_add_cos_sq (2 * Real.pi * x)
  field_simp
  nlinarith

private lemma sin_two_arctan (u : ℝ) :
    Real.sin (2 * Real.arctan u) = 2 * u / (1 + u ^ 2) := by
  rw [Real.sin_two_mul]
  have hc : Real.cos (Real.arctan u) ≠ 0 := (Real.cos_arctan_pos u).ne'
  have ht := Real.tan_arctan u
  rw [Real.tan_eq_sin_div_cos] at ht
  have hs : Real.sin (Real.arctan u) = u * Real.cos (Real.arctan u) := by
    apply (div_eq_iff hc).mp
    simpa [mul_comm] using ht
  rw [hs]
  calc
    2 * (u * Real.cos (Real.arctan u)) * Real.cos (Real.arctan u) =
        2 * u * Real.cos (Real.arctan u) ^ 2 := by ring
    _ = 2 * u / (1 + u ^ 2) := by rw [Real.cos_sq_arctan]; ring

private lemma cos_two_arctan (u : ℝ) :
    Real.cos (2 * Real.arctan u) = (1 - u ^ 2) / (1 + u ^ 2) := by
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  have h : 1 + u ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma psi_eq_sub_half {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    psi x = x - 1 / 2 := by
  have hf : ⌊x⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hx0.le, hx1⟩
  rw [psi, if_neg]
  · simp [Int.fract, hf]
  · simpa [hf] using hx0.ne'

private lemma lowPolynomial_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ 129 * Real.pi * u ^ 6 + 507 * Real.pi * u ^ 4 -
      480 * Real.pi * u ^ 3 + 147 * Real.pi * u ^ 2 + 249 * Real.pi -
      48 * u ^ 11 - 64 * u ^ 9 - 144 * u ^ 7 - 768 * u ^ 5 +
      320 * u ^ 3 - 960 * u := by
  have hv : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hc0 : 0 ≤ 249 * Real.pi := by positivity
  have hc1 : 0 ≤ 3 * (913 * Real.pi - 320) := by nlinarith [Real.pi_gt_d2]
  have hc2 : 0 ≤ 6 * (2307 * Real.pi - 1600) := by nlinarith [Real.pi_gt_d2]
  have hc3 : 0 ≤ 8 * (5241 * Real.pi - 5360) := by nlinarith [Real.pi_gt_d2]
  have hc4 : 0 ≤ 84129 * Real.pi - 112640 := by nlinarith [Real.pi_gt_d2]
  have hc5 : 0 ≤ 117495 * Real.pi - 193408 := by nlinarith [Real.pi_gt_d2]
  have hc6 : 0 ≤ 16 * (7341 * Real.pi - 14288) := by nlinarith [Real.pi_gt_d2]
  have hc7 : 0 ≤ 2 * (42741 * Real.pi - 95432) := by nlinarith [Real.pi_gt_d2]
  have hc8 : 0 ≤ 116 * (393 * Real.pi - 976) := by nlinarith [Real.pi_gt_d2]
  have hc9 : 0 ≤ 4 * (4371 * Real.pi - 11672) := by nlinarith [Real.pi_gt_d2]
  have hc10 : 0 ≤ 64 * (69 * Real.pi - 193) := by nlinarith [Real.pi_gt_d2]
  have hc11 : 0 ≤ 8 * (69 * Real.pi - 208) := by nlinarith [Real.pi_gt_d2]
  have hB : 0 ≤
      (249 * Real.pi) * (1 - u) ^ 11 +
      (3 * (913 * Real.pi - 320)) * u * (1 - u) ^ 10 +
      (6 * (2307 * Real.pi - 1600)) * u ^ 2 * (1 - u) ^ 9 +
      (8 * (5241 * Real.pi - 5360)) * u ^ 3 * (1 - u) ^ 8 +
      (84129 * Real.pi - 112640) * u ^ 4 * (1 - u) ^ 7 +
      (117495 * Real.pi - 193408) * u ^ 5 * (1 - u) ^ 6 +
      (16 * (7341 * Real.pi - 14288)) * u ^ 6 * (1 - u) ^ 5 +
      (2 * (42741 * Real.pi - 95432)) * u ^ 7 * (1 - u) ^ 4 +
      (116 * (393 * Real.pi - 976)) * u ^ 8 * (1 - u) ^ 3 +
      (4 * (4371 * Real.pi - 11672)) * u ^ 9 * (1 - u) ^ 2 +
      (64 * (69 * Real.pi - 193)) * u ^ 10 * (1 - u) +
      (8 * (69 * Real.pi - 208)) * u ^ 11 := by positivity
  have hid :
      (249 * Real.pi) * (1 - u) ^ 11 +
      (3 * (913 * Real.pi - 320)) * u * (1 - u) ^ 10 +
      (6 * (2307 * Real.pi - 1600)) * u ^ 2 * (1 - u) ^ 9 +
      (8 * (5241 * Real.pi - 5360)) * u ^ 3 * (1 - u) ^ 8 +
      (84129 * Real.pi - 112640) * u ^ 4 * (1 - u) ^ 7 +
      (117495 * Real.pi - 193408) * u ^ 5 * (1 - u) ^ 6 +
      (16 * (7341 * Real.pi - 14288)) * u ^ 6 * (1 - u) ^ 5 +
      (2 * (42741 * Real.pi - 95432)) * u ^ 7 * (1 - u) ^ 4 +
      (116 * (393 * Real.pi - 976)) * u ^ 8 * (1 - u) ^ 3 +
      (4 * (4371 * Real.pi - 11672)) * u ^ 9 * (1 - u) ^ 2 +
      (64 * (69 * Real.pi - 193)) * u ^ 10 * (1 - u) +
      (8 * (69 * Real.pi - 208)) * u ^ 11 =
      129 * Real.pi * u ^ 6 + 507 * Real.pi * u ^ 4 -
        480 * Real.pi * u ^ 3 + 147 * Real.pi * u ^ 2 + 249 * Real.pi -
        48 * u ^ 11 - 64 * u ^ 9 - 144 * u ^ 7 - 768 * u ^ 5 +
        320 * u ^ 3 - 960 * u := by ring
  linarith

private lemma highPolynomial_nonneg {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ 903 * Real.pi * v ^ 6 - 1491 * Real.pi * v ^ 4 -
      3360 * Real.pi * v ^ 3 + 1029 * Real.pi * v ^ 2 + 63 * Real.pi -
      240 * v ^ 13 - 384 * v ^ 11 - 272 * v ^ 9 + 768 * v ^ 7 -
      1344 * v ^ 5 + 11200 * v ^ 3 := by
  have hw : 0 ≤ 1 - v := sub_nonneg.mpr hv1
  have hc0 : 0 ≤ 63 * Real.pi := by positivity
  have hc1 : 0 ≤ 819 * Real.pi := by positivity
  have hc2 : 0 ≤ 5943 * Real.pi := by positivity
  have hc3 : 0 ≤ 7 * (3711 * Real.pi + 1600) := by positivity
  have hc4 : 0 ≤ 7 * (9507 * Real.pi + 16000) := by positivity
  have hc5 : 0 ≤ 21 * (4107 * Real.pi + 23936) := by positivity
  have hc6 : 0 ≤ 21 * (63488 - 395 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc7 : 0 ≤ 3 * (771712 - 80339 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc8 : 0 ≤ 24 * (114656 - 19131 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc9 : 0 ≤ 22 * (103144 - 21693 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc10 : 0 ≤ 4 * (320752 - 77259 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc11 : 0 ≤ 12 * (39656 - 10367 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc12 : 0 ≤ 80 * (1300 - 357 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc13 : 0 ≤ 8 * (1216 - 357 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hB : 0 ≤
      (63 * Real.pi) * (1 - v) ^ 13 +
      (819 * Real.pi) * v * (1 - v) ^ 12 +
      (5943 * Real.pi) * v ^ 2 * (1 - v) ^ 11 +
      (7 * (3711 * Real.pi + 1600)) * v ^ 3 * (1 - v) ^ 10 +
      (7 * (9507 * Real.pi + 16000)) * v ^ 4 * (1 - v) ^ 9 +
      (21 * (4107 * Real.pi + 23936)) * v ^ 5 * (1 - v) ^ 8 +
      (21 * (63488 - 395 * Real.pi)) * v ^ 6 * (1 - v) ^ 7 +
      (3 * (771712 - 80339 * Real.pi)) * v ^ 7 * (1 - v) ^ 6 +
      (24 * (114656 - 19131 * Real.pi)) * v ^ 8 * (1 - v) ^ 5 +
      (22 * (103144 - 21693 * Real.pi)) * v ^ 9 * (1 - v) ^ 4 +
      (4 * (320752 - 77259 * Real.pi)) * v ^ 10 * (1 - v) ^ 3 +
      (12 * (39656 - 10367 * Real.pi)) * v ^ 11 * (1 - v) ^ 2 +
      (80 * (1300 - 357 * Real.pi)) * v ^ 12 * (1 - v) +
      (8 * (1216 - 357 * Real.pi)) * v ^ 13 := by positivity
  have hid :
      (63 * Real.pi) * (1 - v) ^ 13 +
      (819 * Real.pi) * v * (1 - v) ^ 12 +
      (5943 * Real.pi) * v ^ 2 * (1 - v) ^ 11 +
      (7 * (3711 * Real.pi + 1600)) * v ^ 3 * (1 - v) ^ 10 +
      (7 * (9507 * Real.pi + 16000)) * v ^ 4 * (1 - v) ^ 9 +
      (21 * (4107 * Real.pi + 23936)) * v ^ 5 * (1 - v) ^ 8 +
      (21 * (63488 - 395 * Real.pi)) * v ^ 6 * (1 - v) ^ 7 +
      (3 * (771712 - 80339 * Real.pi)) * v ^ 7 * (1 - v) ^ 6 +
      (24 * (114656 - 19131 * Real.pi)) * v ^ 8 * (1 - v) ^ 5 +
      (22 * (103144 - 21693 * Real.pi)) * v ^ 9 * (1 - v) ^ 4 +
      (4 * (320752 - 77259 * Real.pi)) * v ^ 10 * (1 - v) ^ 3 +
      (12 * (39656 - 10367 * Real.pi)) * v ^ 11 * (1 - v) ^ 2 +
      (80 * (1300 - 357 * Real.pi)) * v ^ 12 * (1 - v) +
      (8 * (1216 - 357 * Real.pi)) * v ^ 13 =
      903 * Real.pi * v ^ 6 - 1491 * Real.pi * v ^ 4 -
        3360 * Real.pi * v ^ 3 + 1029 * Real.pi * v ^ 2 + 63 * Real.pi -
        240 * v ^ 13 - 384 * v ^ 11 - 272 * v ^ 9 + 768 * v ^ 7 -
        1344 * v ^ 5 + 11200 * v ^ 3 := by ring
  linarith

private noncomputable def tangentBase (u : ℝ) : ℝ :=
  let s := 2 * u / (1 + u ^ 2);
  let z := (1 - u ^ 2) / (1 + u ^ 2);
  -s ^ 3 / 4 + z ^ 3 / 4 + z ^ 2 / 4 + 1 / 2 +
    (s ^ 3 - s * z / 2 - s) / Real.pi

private lemma tangent_error_identity {x u : ℝ}
    (hangle : Real.pi * x = Real.arctan u) :
    (13 / 80 : ℝ) + degreeThreePolynomial x - (x - 1 / 2) =
      tangentBase u - Real.arctan u / Real.pi + 3 / 80 := by
  rw [degreeThreePolynomial_compressed]
  have ht : 2 * Real.pi * x = 2 * Real.arctan u := by linarith
  rw [ht, sin_two_arctan, cos_two_arctan]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [show x = Real.arctan u / Real.pi by
    exact (eq_div_iff hpi).mpr (by simpa [mul_comm] using hangle)]
  simp only [tangentBase]
  have hd : 1 + u ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma tangent_error_nonneg_of_le_one {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ tangentBase u - Real.arctan u / Real.pi + 3 / 80 := by
  let U : ℝ := u - u ^ 3 / 3 + u ^ 5 / 5
  have hatan : Real.arctan u ≤ U := arctan_upper_quintic u hu0
  have hpi : 0 < Real.pi := Real.pi_pos
  have hq := lowPolynomial_nonneg hu0 hu1
  have hd : 0 < 1 + u ^ 2 := by positivity
  have hid :
      (tangentBase u - U / Real.pi + 3 / 80) *
          ((1 + u ^ 2) ^ 3 * (240 * Real.pi)) =
        129 * Real.pi * u ^ 6 + 507 * Real.pi * u ^ 4 -
          480 * Real.pi * u ^ 3 + 147 * Real.pi * u ^ 2 + 249 * Real.pi -
          48 * u ^ 11 - 64 * u ^ 9 - 144 * u ^ 7 - 768 * u ^ 5 +
          320 * u ^ 3 - 960 * u := by
    simp only [tangentBase, U]
    field_simp
    ring
  have hfactor : 0 < (1 + u ^ 2) ^ 3 * (240 * Real.pi) := by positivity
  have happ : 0 ≤ tangentBase u - U / Real.pi + 3 / 80 := by
    apply nonneg_of_mul_nonneg_left
    · rw [hid]
      exact hq
    · exact hfactor
  have hdiv : Real.arctan u / Real.pi ≤ U / Real.pi :=
    div_le_div_of_nonneg_right hatan hpi.le
  linarith

private lemma tangent_error_nonneg_of_one_le {u : ℝ}
    (hu1 : 1 ≤ u) :
    0 ≤ tangentBase u - Real.arctan u / Real.pi + 3 / 80 := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  let v : ℝ := u⁻¹
  have hv0 : 0 ≤ v := inv_nonneg.mpr hu0.le
  have hv1 : v ≤ 1 := (inv_le_one₀ hu0).mpr hu1
  have hvpos : 0 < v := inv_pos.mpr hu0
  have hvu : v = u⁻¹ := rfl
  have huv : u = v⁻¹ := by simp [v, hu0.ne']
  let L : ℝ := v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7
  have hL : L ≤ Real.arctan v := arctan_lower_septic v hv0
  have hatanv : Real.arctan v = Real.pi / 2 - Real.arctan u := by
    simpa [v] using Real.arctan_inv_of_pos hu0
  have hatan : Real.arctan u ≤ Real.pi / 2 - L := by linarith
  have hq := highPolynomial_nonneg hv0 hv1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hd : 0 < 1 + v ^ 2 := by positivity
  have hid :
      (tangentBase (v⁻¹) - (Real.pi / 2 - L) / Real.pi + 3 / 80) *
          ((1 + v ^ 2) ^ 3 * (1680 * Real.pi)) =
        903 * Real.pi * v ^ 6 - 1491 * Real.pi * v ^ 4 -
          3360 * Real.pi * v ^ 3 + 1029 * Real.pi * v ^ 2 + 63 * Real.pi -
          240 * v ^ 13 - 384 * v ^ 11 - 272 * v ^ 9 + 768 * v ^ 7 -
          1344 * v ^ 5 + 11200 * v ^ 3 := by
    simp only [tangentBase, L]
    field_simp
    ring
  have hfactor : 0 < (1 + v ^ 2) ^ 3 * (1680 * Real.pi) := by positivity
  have happ : 0 ≤ tangentBase (v⁻¹) -
      (Real.pi / 2 - L) / Real.pi + 3 / 80 := by
    apply nonneg_of_mul_nonneg_left
    · rw [hid]
      exact hq
    · exact hfactor
  have hdiv : Real.arctan u / Real.pi ≤
      (Real.pi / 2 - L) / Real.pi := div_le_div_of_nonneg_right hatan hpi.le
  rw [huv] at hdiv ⊢
  linarith

private lemma lowMinusPolynomial_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ -4 * (69 * Real.pi * u ^ 6 + 132 * Real.pi * u ^ 4 -
      300 * Real.pi * u ^ 3 + 357 * Real.pi * u ^ 2 - 6 * Real.pi +
      50 * u ^ 9 - 450 * u ^ 5 + 200 * u ^ 3 - 600 * u) := by
  have hv : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hc0 : 0 ≤ 24 * Real.pi := by positivity
  have hc1 : 0 ≤ 24 * (9 * Real.pi + 100) := by positivity
  have hc2 : 0 ≤ 12 * (1600 - 47 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc3 : 0 ≤ 20 * (3320 - 339 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc4 : 0 ≤ 12 * (10800 - 1691 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc5 : 0 ≤ 12 * (13150 - 2633 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc6 : 0 ≤ 80 * (1570 - 369 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc7 : 0 ≤ 48 * (1375 - 359 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc8 : 0 ≤ 864 * (25 - 7 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hc9 : 0 ≤ 16 * (200 - 63 * Real.pi) := by nlinarith [Real.pi_lt_d2]
  have hB : 0 ≤
      (24 * Real.pi) * (1 - u) ^ 9 +
      (24 * (9 * Real.pi + 100)) * u * (1 - u) ^ 8 +
      (12 * (1600 - 47 * Real.pi)) * u ^ 2 * (1 - u) ^ 7 +
      (20 * (3320 - 339 * Real.pi)) * u ^ 3 * (1 - u) ^ 6 +
      (12 * (10800 - 1691 * Real.pi)) * u ^ 4 * (1 - u) ^ 5 +
      (12 * (13150 - 2633 * Real.pi)) * u ^ 5 * (1 - u) ^ 4 +
      (80 * (1570 - 369 * Real.pi)) * u ^ 6 * (1 - u) ^ 3 +
      (48 * (1375 - 359 * Real.pi)) * u ^ 7 * (1 - u) ^ 2 +
      (864 * (25 - 7 * Real.pi)) * u ^ 8 * (1 - u) +
      (16 * (200 - 63 * Real.pi)) * u ^ 9 := by positivity
  have hid :
      (24 * Real.pi) * (1 - u) ^ 9 +
      (24 * (9 * Real.pi + 100)) * u * (1 - u) ^ 8 +
      (12 * (1600 - 47 * Real.pi)) * u ^ 2 * (1 - u) ^ 7 +
      (20 * (3320 - 339 * Real.pi)) * u ^ 3 * (1 - u) ^ 6 +
      (12 * (10800 - 1691 * Real.pi)) * u ^ 4 * (1 - u) ^ 5 +
      (12 * (13150 - 2633 * Real.pi)) * u ^ 5 * (1 - u) ^ 4 +
      (80 * (1570 - 369 * Real.pi)) * u ^ 6 * (1 - u) ^ 3 +
      (48 * (1375 - 359 * Real.pi)) * u ^ 7 * (1 - u) ^ 2 +
      (864 * (25 - 7 * Real.pi)) * u ^ 8 * (1 - u) +
      (16 * (200 - 63 * Real.pi)) * u ^ 9 =
      -4 * (69 * Real.pi * u ^ 6 + 132 * Real.pi * u ^ 4 -
        300 * Real.pi * u ^ 3 + 357 * Real.pi * u ^ 2 - 6 * Real.pi +
        50 * u ^ 9 - 450 * u ^ 5 + 200 * u ^ 3 - 600 * u) := by ring
  linarith

private lemma highMinusPolynomial_nonneg {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ 4 * (81 * Real.pi * v ^ 6 - 132 * Real.pi * v ^ 4 +
      300 * Real.pi * v ^ 3 + 93 * Real.pi * v ^ 2 + 6 * Real.pi -
      30 * v ^ 11 - 40 * v ^ 9 - 90 * v ^ 7 + 120 * v ^ 5 -
      1000 * v ^ 3) := by
  have hw : 0 ≤ 1 - v := sub_nonneg.mpr hv1
  have hc0 : 0 ≤ 24 * Real.pi := by positivity
  have hc1 : 0 ≤ 264 * Real.pi := by positivity
  have hc2 : 0 ≤ 1692 * Real.pi := by positivity
  have hc3 : 0 ≤ 4 * (2127 * Real.pi - 1000) := by nlinarith [Real.pi_gt_three]
  have hc4 : 0 ≤ 16 * (1899 * Real.pi - 2000) := by nlinarith [Real.pi_gt_three]
  have hc5 : 0 ≤ 80 * (903 * Real.pi - 1394) := by nlinarith [Real.pi_gt_three]
  have hc6 : 0 ≤ 4 * (28599 * Real.pi - 55280) := by nlinarith [Real.pi_gt_three]
  have hc7 : 0 ≤ 4 * (30483 * Real.pi - 68290) := by nlinarith [Real.pi_gt_three]
  have hc8 : 0 ≤ 32 * (2724 * Real.pi - 6745) := by nlinarith [Real.pi_gt_three]
  have hc9 : 0 ≤ 16 * (2529 * Real.pi - 6695) := by nlinarith [Real.pi_gt_three]
  have hc10 : 0 ≤ 32 * (348 * Real.pi - 965) := by nlinarith [Real.pi_gt_three]
  have hc11 : 0 ≤ 16 * (87 * Real.pi - 260) := by nlinarith [Real.pi_gt_three]
  have hB : 0 ≤
      (24 * Real.pi) * (1 - v) ^ 11 +
      (264 * Real.pi) * v * (1 - v) ^ 10 +
      (1692 * Real.pi) * v ^ 2 * (1 - v) ^ 9 +
      (4 * (2127 * Real.pi - 1000)) * v ^ 3 * (1 - v) ^ 8 +
      (16 * (1899 * Real.pi - 2000)) * v ^ 4 * (1 - v) ^ 7 +
      (80 * (903 * Real.pi - 1394)) * v ^ 5 * (1 - v) ^ 6 +
      (4 * (28599 * Real.pi - 55280)) * v ^ 6 * (1 - v) ^ 5 +
      (4 * (30483 * Real.pi - 68290)) * v ^ 7 * (1 - v) ^ 4 +
      (32 * (2724 * Real.pi - 6745)) * v ^ 8 * (1 - v) ^ 3 +
      (16 * (2529 * Real.pi - 6695)) * v ^ 9 * (1 - v) ^ 2 +
      (32 * (348 * Real.pi - 965)) * v ^ 10 * (1 - v) +
      (16 * (87 * Real.pi - 260)) * v ^ 11 := by positivity
  have hid :
      (24 * Real.pi) * (1 - v) ^ 11 +
      (264 * Real.pi) * v * (1 - v) ^ 10 +
      (1692 * Real.pi) * v ^ 2 * (1 - v) ^ 9 +
      (4 * (2127 * Real.pi - 1000)) * v ^ 3 * (1 - v) ^ 8 +
      (16 * (1899 * Real.pi - 2000)) * v ^ 4 * (1 - v) ^ 7 +
      (80 * (903 * Real.pi - 1394)) * v ^ 5 * (1 - v) ^ 6 +
      (4 * (28599 * Real.pi - 55280)) * v ^ 6 * (1 - v) ^ 5 +
      (4 * (30483 * Real.pi - 68290)) * v ^ 7 * (1 - v) ^ 4 +
      (32 * (2724 * Real.pi - 6745)) * v ^ 8 * (1 - v) ^ 3 +
      (16 * (2529 * Real.pi - 6695)) * v ^ 9 * (1 - v) ^ 2 +
      (32 * (348 * Real.pi - 965)) * v ^ 10 * (1 - v) +
      (16 * (87 * Real.pi - 260)) * v ^ 11 =
      4 * (81 * Real.pi * v ^ 6 - 132 * Real.pi * v ^ 4 +
        300 * Real.pi * v ^ 3 + 93 * Real.pi * v ^ 2 + 6 * Real.pi -
        30 * v ^ 11 - 40 * v ^ 9 - 90 * v ^ 7 + 120 * v ^ 5 -
        1000 * v ^ 3) := by ring
  linarith

private noncomputable def tangentMinusBase (u : ℝ) : ℝ :=
  let s := 2 * u / (1 + u ^ 2);
  let z := (1 - u ^ 2) / (1 + u ^ 2);
  s ^ 3 / 4 + z ^ 3 / 4 + z ^ 2 / 4 - 1 / 2 +
    (-s ^ 3 + s * z / 2 + s) / Real.pi

private lemma tangent_minus_error_identity {x u : ℝ}
    (hangle : Real.pi * x = Real.arctan u) :
    (33 / 200 : ℝ) + degreeThreePolynomial (-x) + (x - 1 / 2) =
      tangentMinusBase u + Real.arctan u / Real.pi + 1 / 25 := by
  rw [degreeThreePolynomial_compressed]
  have ht : 2 * Real.pi * (-x) = -(2 * Real.arctan u) := by linarith
  rw [ht, Real.sin_neg, Real.cos_neg, sin_two_arctan, cos_two_arctan]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [show x = Real.arctan u / Real.pi by
    exact (eq_div_iff hpi).mpr (by simpa [mul_comm] using hangle)]
  simp only [tangentMinusBase]
  have hd : 1 + u ^ 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma tangent_minus_error_nonneg_of_le_one {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ tangentMinusBase u + Real.arctan u / Real.pi + 1 / 25 := by
  let L : ℝ := u - u ^ 3 / 3
  have hL : L ≤ Real.arctan u := arctan_lower_cubic u hu0
  have hpi : 0 < Real.pi := Real.pi_pos
  have hq := lowMinusPolynomial_nonneg hu0 hu1
  have hid :
      (tangentMinusBase u + L / Real.pi + 1 / 25) *
          ((1 + u ^ 2) ^ 3 * (600 * Real.pi)) =
        -4 * (69 * Real.pi * u ^ 6 + 132 * Real.pi * u ^ 4 -
          300 * Real.pi * u ^ 3 + 357 * Real.pi * u ^ 2 - 6 * Real.pi +
          50 * u ^ 9 - 450 * u ^ 5 + 200 * u ^ 3 - 600 * u) := by
    simp only [tangentMinusBase, L]
    field_simp
    ring
  have hfactor : 0 < (1 + u ^ 2) ^ 3 * (600 * Real.pi) := by positivity
  have happ : 0 ≤ tangentMinusBase u + L / Real.pi + 1 / 25 := by
    apply nonneg_of_mul_nonneg_left
    · rw [hid]
      exact hq
    · exact hfactor
  have hdiv : L / Real.pi ≤ Real.arctan u / Real.pi :=
    div_le_div_of_nonneg_right hL hpi.le
  linarith

private lemma tangent_minus_error_nonneg_of_one_le {u : ℝ}
    (hu1 : 1 ≤ u) :
    0 ≤ tangentMinusBase u + Real.arctan u / Real.pi + 1 / 25 := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  let v : ℝ := u⁻¹
  have hv0 : 0 ≤ v := inv_nonneg.mpr hu0.le
  have hv1 : v ≤ 1 := (inv_le_one₀ hu0).mpr hu1
  have hvpos : 0 < v := inv_pos.mpr hu0
  have huv : u = v⁻¹ := by simp [v]
  let U : ℝ := v - v ^ 3 / 3 + v ^ 5 / 5
  have hU : Real.arctan v ≤ U := arctan_upper_quintic v hv0
  have hatanv : Real.arctan v = Real.pi / 2 - Real.arctan u := by
    simpa [v] using Real.arctan_inv_of_pos hu0
  have hatan : Real.pi / 2 - U ≤ Real.arctan u := by linarith
  have hq := highMinusPolynomial_nonneg hv0 hv1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hid :
      (tangentMinusBase (v⁻¹) + (Real.pi / 2 - U) / Real.pi + 1 / 25) *
          ((1 + v ^ 2) ^ 3 * (600 * Real.pi)) =
        4 * (81 * Real.pi * v ^ 6 - 132 * Real.pi * v ^ 4 +
          300 * Real.pi * v ^ 3 + 93 * Real.pi * v ^ 2 + 6 * Real.pi -
          30 * v ^ 11 - 40 * v ^ 9 - 90 * v ^ 7 + 120 * v ^ 5 -
          1000 * v ^ 3) := by
    simp only [tangentMinusBase, U]
    field_simp [hvpos.ne']
    ring
  have hfactor : 0 < (1 + v ^ 2) ^ 3 * (600 * Real.pi) := by positivity
  have happ : 0 ≤ tangentMinusBase (v⁻¹) +
      (Real.pi / 2 - U) / Real.pi + 1 / 25 := by
    apply nonneg_of_mul_nonneg_left
    · rw [hid]
      exact hq
    · exact hfactor
  have hdiv : (Real.pi / 2 - U) / Real.pi ≤
      Real.arctan u / Real.pi := div_le_div_of_nonneg_right hatan hpi.le
  rw [huv] at hdiv ⊢
  linarith

private lemma degreeThreePlus_on_half (x : ℝ) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    psi x ≤ (33 / 200 : ℝ) + degreeThreePolynomial x := by
  rcases hx0.eq_or_lt with rfl | hx0
  · norm_num [psi, degreeThreePolynomial]
  rcases hxhalf.eq_or_lt with hx | hxhalf
  · subst x
    rw [psi_eq_sub_half (by norm_num) (by norm_num)]
    rw [degreeThreePolynomial]
    ring_nf
    rw [show Real.pi * 2 = (2 : ℕ) * Real.pi by ring,
      show Real.pi * 3 = (3 : ℕ) * Real.pi by ring,
      Real.sin_nat_mul_pi 2, Real.sin_nat_mul_pi 3,
      Real.cos_nat_mul_pi 2, Real.cos_nat_mul_pi 3]
    norm_num
  · let u := Real.tan (Real.pi * x)
    have hy0 : 0 ≤ Real.pi * x := mul_nonneg Real.pi_pos.le hx0.le
    have hyhalf : Real.pi * x < Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have hu0 : 0 ≤ u := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hy0 hyhalf.le
    have hangle : Real.pi * x = Real.arctan u := by
      symm
      exact Real.arctan_tan (by nlinarith [Real.pi_pos]) hyhalf
    have hid := tangent_error_identity hangle
    have herr : 0 ≤ tangentBase u - Real.arctan u / Real.pi + 3 / 80 := by
      rcases le_total u 1 with hu1 | h1u
      · exact tangent_error_nonneg_of_le_one hu0 hu1
      · exact tangent_error_nonneg_of_one_le h1u
    rw [psi_eq_sub_half hx0 (by linarith)]
    linarith

private lemma degreeThreeMinus_on_half (x : ℝ) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    -psi x ≤ (33 / 200 : ℝ) + degreeThreePolynomial (-x) := by
  rcases hx0.eq_or_lt with rfl | hx0
  · norm_num [psi, degreeThreePolynomial]
  rcases hxhalf.eq_or_lt with hx | hxhalf
  · subst x
    rw [psi_eq_sub_half (by norm_num) (by norm_num)]
    rw [degreeThreePolynomial]
    ring_nf
    rw [show Real.pi * 2 = (2 : ℕ) * Real.pi by ring,
      show Real.pi * 3 = (3 : ℕ) * Real.pi by ring]
    simp only [Real.sin_neg, Real.cos_neg, Real.sin_pi, Real.cos_pi,
      Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    norm_num
  · let u := Real.tan (Real.pi * x)
    have hy0 : 0 ≤ Real.pi * x := mul_nonneg Real.pi_pos.le hx0.le
    have hyhalf : Real.pi * x < Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have hu0 : 0 ≤ u := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hy0 hyhalf.le
    have hangle : Real.pi * x = Real.arctan u := by
      symm
      exact Real.arctan_tan (by nlinarith [Real.pi_pos]) hyhalf
    have hid := tangent_minus_error_identity hangle
    have herr : 0 ≤ tangentMinusBase u + Real.arctan u / Real.pi + 1 / 25 := by
      rcases le_total u 1 with hu1 | h1u
      · exact tangent_minus_error_nonneg_of_le_one hu0 hu1
      · exact tangent_minus_error_nonneg_of_one_le h1u
    rw [psi_eq_sub_half hx0 (by linarith)]
    linarith

private lemma sin_harmonic_fract (k : ℤ) (x : ℝ) :
    Real.sin (2 * (k : ℝ) * Real.pi * x) =
      Real.sin (2 * (k : ℝ) * Real.pi * Int.fract x) := by
  have hx := Int.floor_add_fract x
  have hang : 2 * (k : ℝ) * Real.pi * x =
      2 * (k : ℝ) * Real.pi * Int.fract x +
        (k * ⌊x⌋ : ℤ) * (2 * Real.pi) := by
    calc
      2 * (k : ℝ) * Real.pi * x =
          2 * (k : ℝ) * Real.pi * ((⌊x⌋ : ℤ) + Int.fract x) := by rw [hx]
      _ = _ := by push_cast; ring
  calc
    Real.sin (2 * (k : ℝ) * Real.pi * x) =
        Real.sin (2 * (k : ℝ) * Real.pi * Int.fract x +
          (k * ⌊x⌋ : ℤ) * (2 * Real.pi)) := by
            rw [hang]
    _ = _ := Real.sin_add_int_mul_two_pi _ _

private lemma cos_harmonic_fract (k : ℤ) (x : ℝ) :
    Real.cos (2 * (k : ℝ) * Real.pi * x) =
      Real.cos (2 * (k : ℝ) * Real.pi * Int.fract x) := by
  have hx := Int.floor_add_fract x
  have hang : 2 * (k : ℝ) * Real.pi * x =
      2 * (k : ℝ) * Real.pi * Int.fract x +
        (k * ⌊x⌋ : ℤ) * (2 * Real.pi) := by
    calc
      2 * (k : ℝ) * Real.pi * x =
          2 * (k : ℝ) * Real.pi * ((⌊x⌋ : ℤ) + Int.fract x) := by rw [hx]
      _ = _ := by push_cast; ring
  calc
    Real.cos (2 * (k : ℝ) * Real.pi * x) =
        Real.cos (2 * (k : ℝ) * Real.pi * Int.fract x +
          (k * ⌊x⌋ : ℤ) * (2 * Real.pi)) := by
            rw [hang]
    _ = _ := Real.cos_add_int_mul_two_pi _ _

private lemma degreeThreePolynomial_fract (x : ℝ) :
    degreeThreePolynomial x = degreeThreePolynomial (Int.fract x) := by
  rw [degreeThreePolynomial, degreeThreePolynomial]
  have hs1 := sin_harmonic_fract 1 x
  have hs2 := sin_harmonic_fract 2 x
  have hs3 := sin_harmonic_fract 3 x
  have hc1 := cos_harmonic_fract 1 x
  have hc2 := cos_harmonic_fract 2 x
  have hc3 := cos_harmonic_fract 3 x
  norm_num at hs1 hs2 hs3 hc1 hc2 hc3
  rw [hs1, hs2, hs3, hc1, hc2, hc3]

private lemma psi_eq_fract_sub_half {x : ℝ} (hx : Int.fract x ≠ 0) :
    psi x = Int.fract x - 1 / 2 := by
  rw [psi, if_neg]
  intro h
  apply hx
  calc
    Int.fract x = Int.fract (⌊x⌋ : ℝ) := congrArg Int.fract h
    _ = 0 := Int.fract_floor x

private lemma degreeThreePlus_global (x : ℝ) :
    psi x ≤ (33 / 200 : ℝ) + degreeThreePolynomial x := by
  let t := Int.fract x
  have ht0 : 0 ≤ t := Int.fract_nonneg x
  have ht1 : t < 1 := Int.fract_lt_one x
  have hperiod := degreeThreePolynomial_fract x
  change degreeThreePolynomial x = degreeThreePolynomial t at hperiod
  by_cases ht : t = 0
  · have hxint : x = (⌊x⌋ : ℝ) := by
      have h := Int.floor_add_fract x
      change (⌊x⌋ : ℝ) + t = x at h
      linarith
    have hzero := degreeThreePlus_on_half 0 (by norm_num) (by norm_num)
    rw [psi, if_pos hxint, hperiod, ht]
    simpa [psi] using hzero
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hpsi := psi_eq_fract_sub_half ht
    change psi x = t - 1 / 2 at hpsi
    rcases le_total t (1 / 2) with hthalf | hhalft
    · have h := degreeThreePlus_on_half t ht0 hthalf
      rw [psi_eq_sub_half htpos ht1] at h
      rw [hpsi, hperiod]
      exact h
    · let y := 1 - t
      have hy0 : 0 ≤ y := by dsimp [y]; linarith
      have hyhalf : y ≤ 1 / 2 := by dsimp [y]; linarith
      have hypos : 0 < y := by dsimp [y]; linarith
      have hy1 : y < 1 := by dsimp [y]; linarith
      have hfy : Int.fract y = y := Int.fract_eq_self.mpr ⟨hy0, hy1⟩
      have hfny : Int.fract (-y) = t := by
        have hn := Int.fract_neg (show Int.fract y ≠ 0 by simpa [hfy] using hypos.ne')
        rw [hfy] at hn
        dsimp [y] at hn ⊢
        linarith
      have hpny := degreeThreePolynomial_fract (-y)
      rw [hfny] at hpny
      have h := degreeThreeMinus_on_half y hy0 hyhalf
      rw [psi_eq_sub_half hypos hy1, hpny] at h
      rw [hpsi, hperiod]
      dsimp [y] at h
      linarith

private lemma degreeThreeMinus_global (x : ℝ) :
    -psi x ≤ (33 / 200 : ℝ) + degreeThreePolynomial (-x) := by
  let t := Int.fract x
  have ht0 : 0 ≤ t := Int.fract_nonneg x
  have ht1 : t < 1 := Int.fract_lt_one x
  have hperiod := degreeThreePolynomial_fract (-x)
  by_cases ht : t = 0
  · have hxint : x = (⌊x⌋ : ℝ) := by
      have h := Int.floor_add_fract x
      change (⌊x⌋ : ℝ) + t = x at h
      linarith
    have hzero := degreeThreeMinus_on_half 0 (by norm_num) (by norm_num)
    have hfx : Int.fract (-x) = 0 := by
      rw [Int.fract_neg_eq_zero]
      exact ht
    rw [hfx] at hperiod
    rw [psi, if_pos hxint, hperiod]
    simpa [psi] using hzero
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hpsi := psi_eq_fract_sub_half ht
    change psi x = t - 1 / 2 at hpsi
    rcases le_total t (1 / 2) with hthalf | hhalft
    · have hft : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht0, ht1⟩
      have hfnt : Int.fract (-t) = 1 - t := by
        simpa [hft] using Int.fract_neg (show Int.fract t ≠ 0 by simpa [hft])
      have hpx : degreeThreePolynomial (-x) = degreeThreePolynomial (-t) := by
        rw [degreeThreePolynomial_fract (-x), degreeThreePolynomial_fract (-t), hfnt]
        have hfnx : Int.fract (-x) = 1 - t := by
          simpa [t] using Int.fract_neg (show Int.fract x ≠ 0 by simpa [t])
        rw [hfnx]
      have h := degreeThreeMinus_on_half t ht0 hthalf
      rw [psi_eq_sub_half htpos ht1] at h
      rw [hpsi, hpx]
      exact h
    · let y := 1 - t
      have hy0 : 0 ≤ y := by dsimp [y]; linarith
      have hyhalf : y ≤ 1 / 2 := by dsimp [y]; linarith
      have hypos : 0 < y := by dsimp [y]; linarith
      have hy1 : y < 1 := by dsimp [y]; linarith
      have hfnx : Int.fract (-x) = y := by
        have hn := Int.fract_neg (show Int.fract x ≠ 0 by simpa [t])
        change Int.fract (-x) = 1 - t at hn
        exact hn
      rw [degreeThreePolynomial_fract (-x), hfnx]
      have h := degreeThreePlus_on_half y hy0 hyhalf
      rw [psi_eq_sub_half hypos hy1] at h
      rw [hpsi]
      dsimp [y] at h ⊢
      linarith

/-- The unconditional order-three upper Fourier majorant for `psi`. -/
theorem degreeThreePlus_majorant :
    IsUpperMajorant (frequencies 3) psi (33 / 200) degreeThreePlusCoefficient := by
  intro x
  rw [degreeThreePolynomial_eq]
  exact degreeThreePlus_global x

/-- The reflected unconditional order-three upper Fourier majorant for
`-psi`. -/
theorem degreeThreeMinus_majorant :
    IsUpperMajorant (frequencies 3) (fun x ↦ -psi x) (33 / 200)
      degreeThreeMinusCoefficient := by
  intro x
  rw [degreeThreeMinusPolynomial_eq]
  exact degreeThreeMinus_global x

private lemma inverse_eight_pi_bounds :
    (1 / 32 : ℝ) ≤ 1 / (8 * Real.pi) ∧ 1 / (8 * Real.pi) ≤ 1 / 24 := by
  constructor
  · apply one_div_le_one_div_of_le (by positivity)
    nlinarith [Real.pi_lt_four]
  · apply one_div_le_one_div_of_le (by norm_num)
    nlinarith [Real.pi_gt_three]

private lemma norm_c1_le : ‖c1‖ ≤ (11 / 48 : ℝ) := by
  have hq := inverse_eight_pi_bounds
  calc
    ‖c1‖ ≤ |c1.re| + |c1.im| := Complex.norm_le_abs_re_add_abs_im c1
    _ = 3 / 32 + (3 / 32 + 1 / (8 * Real.pi)) := by
      rw [c1]
      rw [abs_of_nonneg (by norm_num), abs_of_nonneg (by positivity)]
    _ ≤ 11 / 48 := by linarith

private lemma norm_c2_le : ‖c2‖ ≤ (5 / 48 : ℝ) := by
  have hq := inverse_eight_pi_bounds
  calc
    ‖c2‖ ≤ |c2.re| + |c2.im| := Complex.norm_le_abs_re_add_abs_im c2
    _ = 1 / 16 + 1 / (8 * Real.pi) := by
      rw [c2]
      rw [abs_of_nonneg (by norm_num), abs_of_nonneg (by positivity)]
    _ ≤ 5 / 48 := by linarith

private lemma norm_c3_le : ‖c3‖ ≤ (2 / 48 : ℝ) := by
  have hq := inverse_eight_pi_bounds
  calc
    ‖c3‖ ≤ |c3.re| + |c3.im| := Complex.norm_le_abs_re_add_abs_im c3
    _ = 1 / 32 + (1 / (8 * Real.pi) - 1 / 32) := by
      rw [c3]
      rw [abs_of_nonneg (by norm_num), abs_of_nonneg (by linarith [hq.1])]
    _ ≤ 2 / 48 := by linarith

/-- The explicit `ℓ¹` norm bound for the upper coefficients. -/
theorem sum_norm_degreeThreePlusCoefficient_le :
    (∑ r ∈ frequencies 3, ‖degreeThreePlusCoefficient r‖) ≤ (3 / 4 : ℝ) := by
  rw [frequencies_three]
  norm_num [degreeThreePlusCoefficient]
  nlinarith [norm_c1_le, norm_c2_le, norm_c3_le]

/-- The reflected coefficients have the same `ℓ¹` bound. -/
theorem sum_norm_degreeThreeMinusCoefficient_le :
    (∑ r ∈ frequencies 3, ‖degreeThreeMinusCoefficient r‖) ≤ (3 / 4 : ℝ) := by
  rw [frequencies_three]
  norm_num [degreeThreeMinusCoefficient, degreeThreePlusCoefficient]
  nlinarith [norm_c1_le, norm_c2_le, norm_c3_le]

end VaalerDegreeTen

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/Section7.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Granville--Ramaré, Section 7: the concrete lower bound for a reciprocal
von Mangoldt exponential sum.
-/

noncomputable section

namespace Section7

open Nat Finset
open scoped BigOperators ArithmeticFunction.vonMangoldt

alias I := Detector.squareRootInterval
/-- The square-description of the summation interval agrees exactly with
the half-open integer interval used by the analytic estimates. -/
lemma squareRootInterval_eq_Ioc (n : ℕ) :
    I n = Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)) := by
  ext d
  simp only [I, Detector.squareRootInterval, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_Ioc, Nat.sqrt_lt', Nat.le_sqrt']
  constructor
  · rintro ⟨⟨hd1, hd2n⟩, hn, h2n⟩
    exact ⟨hn, h2n⟩
  · rintro ⟨hn, h2n⟩
    have hd1 : 1 ≤ d := by
      by_contra h
      have : d = 0 := by omega
      subst d
      simp at hn
    have hd2n : d ≤ 2 * n := by
      calc
        d ≤ d ^ 2 := by nlinarith
        _ ≤ 2 * n := h2n
    exact ⟨⟨hd1, hd2n⟩, hn, h2n⟩

/-- The discrete detector's sawtooth is the value of the real sawtooth at
the corresponding rational number. -/
lemma psi_natCast_div (a d : ℕ) (hd : 0 < d) :
    Sawtooth.psi ((a : ℝ) / d) = Detector.sawtoothQuot a d := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hfract : Int.fract ((a : ℝ) / d) = ((a % d : ℕ) : ℝ) / d := by
    exact Int.fract_div_natCast_eq_div_natCast_mod
  by_cases hda : d ∣ a
  · have hmod : a % d = 0 := Nat.mod_eq_zero_of_dvd hda
    have hfrac0 : Int.fract ((a : ℝ) / d) = 0 := by simp [hfract, hmod]
    have hfloor : (a : ℝ) / d = (⌊(a : ℝ) / d⌋ : ℝ) := by
      rw [Int.fract] at hfrac0
      linarith
    rw [Sawtooth.psi, if_pos hfloor, Detector.sawtoothQuot, if_pos hda]
  · have hmod : a % d ≠ 0 := by
      exact fun h => hda (Nat.dvd_of_mod_eq_zero h)
    have hfrac_ne : Int.fract ((a : ℝ) / d) ≠ 0 := by
      rw [hfract]
      exact div_ne_zero (by exact_mod_cast hmod) hdR
    have hfloor : (a : ℝ) / d ≠ (⌊(a : ℝ) / d⌋ : ℝ) := by
      intro h
      apply hfrac_ne
      rw [Int.fract]
      linarith
    rw [Sawtooth.psi, if_neg hfloor, Detector.sawtoothQuot, if_neg hda, hfract]

/-- The reciprocal von Mangoldt exponential sum on the Section 7 interval. -/
def mangoldtSum (n : ℕ) (x : ℝ) : ℂ :=
  ∑ d ∈ Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)),
    (ArithmeticFunction.vonMangoldt d : ℂ) * Sawtooth.e (x / (d : ℝ))

/-- Two prime powers in the short interval with the same underlying prime
are equal.  The point is that two distinct consecutive powers differ by a
factor at least two, whereas the squared endpoints differ by only a factor
two. -/
lemma minFac_injective_on_interval_primePowers {n d e : ℕ}
    (hd : d ∈ I n) (he : e ∈ I n)
    (hdpp : IsPrimePow d) (hepp : IsPrimePow e)
    (hmin : Nat.minFac d = Nat.minFac e) : d = e := by
  obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff d).mp hdpp
  obtain ⟨q, b, hq, hb, rfl⟩ := (isPrimePow_nat_iff e).mp hepp
  have hpq : p = q := by
    simpa [Nat.pow_minFac ha.ne', Nat.pow_minFac hb.ne', hp.minFac_eq,
      hq.minFac_eq] using hmin
  subst q
  have hdmem := Detector.mem_squareRootInterval.mp hd
  have hemel := Detector.mem_squareRootInterval.mp he
  by_contra hab
  have habexp : a ≠ b := by
    intro h
    exact hab (congrArg (p ^ ·) h)
  rcases lt_or_gt_of_ne habexp with hab | hba
  · have hpow : 2 * p ^ a ≤ p ^ b := by
      calc
        2 * p ^ a ≤ p * p ^ a := Nat.mul_le_mul_right _ hp.two_le
        _ = p ^ (a + 1) := by rw [pow_succ']
        _ ≤ p ^ b := Nat.pow_le_pow_right hp.pos (by omega)
    have hsquare := Nat.pow_le_pow_left hpow 2
    nlinarith [hdmem.2.2.1, hemel.2.2.2]
  · have hpow : 2 * p ^ b ≤ p ^ a := by
      calc
        2 * p ^ b ≤ p * p ^ b := Nat.mul_le_mul_right _ hp.two_le
        _ = p ^ (b + 1) := by rw [pow_succ']
        _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos (by omega)
    have hsquare := Nat.pow_le_pow_left hpow 2
    nlinarith [hemel.2.2.1, hdmem.2.2.2]

/-- The von Mangoldt mass of interval terms sharing a prime factor with
`2n` is at most `log (2n)`.  Each nonzero term is a prime power; the short
interval contains at most one power of each base prime, and those base
primes are distinct divisors of `2n`. -/
lemma bad_mangoldt_mass_le_log_two_mul (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ (I n).filter fun d => ¬Nat.Coprime d (2 * n),
      ArithmeticFunction.vonMangoldt d) ≤ Real.log (2 * n) := by
  let bad := (I n).filter fun d => ¬Nat.Coprime d (2 * n)
  let badPP := bad.filter IsPrimePow
  have hbad_eq :
      (∑ d ∈ bad, ArithmeticFunction.vonMangoldt d) =
        ∑ d ∈ badPP, ArithmeticFunction.vonMangoldt d := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    simpa [badPP, hd] using hnot
  have hinj : Set.InjOn Nat.minFac (badPP : Set ℕ) := by
    intro d hd e he hde
    have hd' := Finset.mem_filter.mp hd
    have he' := Finset.mem_filter.mp he
    have hdbad := Finset.mem_filter.mp hd'.1
    have hebad := Finset.mem_filter.mp he'.1
    exact minFac_injective_on_interval_primePowers hdbad.1 hebad.1 hd'.2 he'.2 hde
  have hterm (d : ℕ) (hd : d ∈ badPP) :
      ArithmeticFunction.vonMangoldt d =
        ArithmeticFunction.vonMangoldt (Nat.minFac d) := by
    have hdpp := (Finset.mem_filter.mp hd).2
    obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff d).mp hdpp
    rw [ArithmeticFunction.vonMangoldt_apply_pow ha.ne']
    simp [Nat.pow_minFac ha.ne', hp.minFac_eq]
  have hbase_mem : badPP.image Nat.minFac ⊆ (2 * n).divisors := by
    intro p hp
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hp
    have hd' := Finset.mem_filter.mp hd
    have hdbad := Finset.mem_filter.mp hd'.1
    have hdpp := hd'.2
    obtain ⟨q, a, hq, ha, hqa⟩ := (isPrimePow_nat_iff d).mp hdpp
    have hmin : Nat.minFac d = q := by
      rw [← hqa, Nat.pow_minFac ha.ne', hq.minFac_eq]
    rw [hmin]
    have hqdvd : q ∣ 2 * n := by
      by_contra hqnot
      have hcop : Nat.Coprime q (2 * n) := hq.coprime_iff_not_dvd.mpr hqnot
      apply hdbad.2
      rw [← hqa]
      exact hcop.pow_left a
    exact Nat.mem_divisors.mpr ⟨hqdvd, by positivity⟩
  calc
    (∑ d ∈ (I n).filter fun d => ¬Nat.Coprime d (2 * n),
        ArithmeticFunction.vonMangoldt d) =
        ∑ d ∈ badPP, ArithmeticFunction.vonMangoldt d := by
          simpa only [bad] using hbad_eq
    _ = ∑ d ∈ badPP, ArithmeticFunction.vonMangoldt (Nat.minFac d) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = ∑ p ∈ badPP.image Nat.minFac, ArithmeticFunction.vonMangoldt p := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ (2 * n).divisors, ArithmeticFunction.vonMangoldt p := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hbase_mem fun p _ _ =>
        ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log (2 * n) := by
      rw [ArithmeticFunction.vonMangoldt_sum]
      norm_num [Nat.cast_mul]

/-- The discrete Kummer detector rewritten with the real sawtooth and the
standard half-open square-root interval. -/
lemma sawtooth_mangoldt_detector_psi (n : ℕ)
    (hsq : Squarefree (Nat.choose (n + n) n)) :
    (1 / 2 : ℝ) *
        (∑ d ∈ (I n).filter fun d => Nat.Coprime d (2 * n),
          ArithmeticFunction.vonMangoldt d) ≤
      |∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
          Sawtooth.psi ((2 * n : ℕ) / (d : ℝ))| +
        2 * |∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
          Sawtooth.psi ((n : ℝ) / (d : ℝ))| := by
  have h := Detector.sawtooth_mangoldt_detector n hsq
  change (1 / 2 : ℝ) *
      (∑ d ∈ (I n).filter fun d => Nat.Coprime d (2 * n),
        ArithmeticFunction.vonMangoldt d) ≤
    |∑ d ∈ I n, Detector.sawtoothQuot (2 * n) d *
        ArithmeticFunction.vonMangoldt d| +
      2 * |∑ d ∈ I n, Detector.sawtoothQuot n d *
        ArithmeticFunction.vonMangoldt d| at h
  have htwo :
      (∑ d ∈ I n, Detector.sawtoothQuot (2 * n) d *
          ArithmeticFunction.vonMangoldt d) =
        ∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
          Sawtooth.psi ((2 * n : ℕ) / (d : ℝ)) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : 0 < d := lt_trans Nat.zero_lt_one
      (Detector.one_lt_of_mem_squareRootInterval hd)
    rw [psi_natCast_div _ _ hd0]
    ring
  have hone :
      (∑ d ∈ I n, Detector.sawtoothQuot n d *
          ArithmeticFunction.vonMangoldt d) =
        ∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
          Sawtooth.psi ((n : ℝ) / (d : ℝ)) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : 0 < d := lt_trans Nat.zero_lt_one
      (Detector.one_lt_of_mem_squareRootInterval hd)
    rw [psi_natCast_div _ _ hd0]
    ring
  rw [htwo, hone] at h
  simpa only [Nat.mul_comm] using h

/-- The form of (7.1) used by the Fourier step: the coprime restriction is
replaced by subtracting the complementary nonnegative mass. -/
lemma sawtooth_mangoldt_detector_sub_bad (n : ℕ)
    (hsq : Squarefree (Nat.choose (n + n) n)) :
    ((∑ d ∈ I n, ArithmeticFunction.vonMangoldt d) -
        ∑ d ∈ (I n).filter (fun d => ¬Nat.Coprime d (2 * n)),
          ArithmeticFunction.vonMangoldt d) / 2 ≤
      |∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
          Sawtooth.psi ((2 * n : ℕ) / (d : ℝ))| +
        2 * |∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
          Sawtooth.psi ((n : ℝ) / (d : ℝ))| := by
  have h := sawtooth_mangoldt_detector_psi n hsq
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := I n)
    (p := fun d => Nat.Coprime d (2 * n))
    (f := fun d => ArithmeticFunction.vonMangoldt d)
  have hid :
      (∑ d ∈ I n, ArithmeticFunction.vonMangoldt d) -
          ∑ d ∈ (I n).filter (fun d => ¬Nat.Coprime d (2 * n)),
            ArithmeticFunction.vonMangoldt d =
        ∑ d ∈ (I n).filter (fun d => Nat.Coprime d (2 * n)),
          ArithmeticFunction.vonMangoldt d := by
    linarith
  rw [hid]
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

/-- Negating the phase conjugates the standard additive character. -/
lemma e_neg (x : ℝ) : Sawtooth.e (-x) = (starRingEnd ℂ) (Sawtooth.e x) := by
  rw [Sawtooth.e, Sawtooth.e, ← Complex.exp_conj]
  apply congrArg Complex.exp
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Every signed degree-ten Fourier phase has the norm of the actual
reciprocal Mangoldt sum at the corresponding positive frequency. -/
lemma weightedPhaseSum_norm_eq_mangoldtSum (n c : ℕ) (r : ℤ) :
    ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => ((c * n : ℕ) : ℝ) / d) r‖ =
      ‖mangoldtSum n ((r.natAbs : ℝ) * c * n)‖ := by
  rcases le_total 0 r with hr | hr
  · have hrcast : (r : ℝ) = r.natAbs := by
      simpa using congrArg (fun z : ℤ => (z : ℝ))
        (Int.eq_natAbs_of_nonneg hr)
    apply congrArg norm
    rw [Sawtooth.weightedPhaseSum, mangoldtSum, ← squareRootInterval_eq_Ioc]
    apply Finset.sum_congr rfl
    intro d hd
    congr 1
    apply congrArg Sawtooth.e
    rw [hrcast]
    push_cast
    ring
  · have hrcast : (r : ℝ) = -(r.natAbs : ℝ) := by
      simpa using congrArg (fun z : ℤ => (z : ℝ))
        (Int.eq_neg_natAbs_of_nonpos hr)
    have hsum :
        Sawtooth.weightedPhaseSum (I n)
            (fun d => ArithmeticFunction.vonMangoldt d)
            (fun d => ((c * n : ℕ) : ℝ) / d) r =
          (starRingEnd ℂ) (mangoldtSum n ((r.natAbs : ℝ) * c * n)) := by
      rw [Sawtooth.weightedPhaseSum, mangoldtSum, ← squareRootInterval_eq_Ioc,
        map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [map_mul, Complex.conj_ofReal]
      congr 1
      rw [← e_neg]
      apply congrArg Sawtooth.e
      rw [hrcast]
      push_cast
      ring
    rw [hsum, Complex.norm_conj]

/-- The nonzero order-three Fourier frequencies have absolute value between
one and three. -/
lemma natAbs_bounds_of_mem_frequencies_three {r : ℤ}
    (hr : r ∈ Sawtooth.frequencies 3) : 1 ≤ r.natAbs ∧ r.natAbs ≤ 3 := by
  simp only [Sawtooth.frequencies, Finset.mem_erase, Finset.mem_Icc] at hr
  rcases hr with ⟨hr0, hrlo, hrhi⟩
  interval_cases r <;> norm_num at *

/-- If the reciprocal Mangoldt sum is smaller than `M` throughout
`[n,6n]`, then both families of order-three Fourier phases used by the
detector are bounded by `M`. -/
lemma degreeThree_phase_bounds_of_forall_lt (n : ℕ) (M : ℝ)
    (hsmall : ∀ x : ℝ, (n : ℝ) ≤ x → x ≤ 6 * n → ‖mangoldtSum n x‖ < M) :
    (∀ r ∈ Sawtooth.frequencies 3,
      ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => ((2 * n : ℕ) : ℝ) / d) r‖ ≤ M) ∧
    (∀ r ∈ Sawtooth.frequencies 3,
      ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => (n : ℝ) / d) r‖ ≤ M) := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  constructor
  · intro r hr
    obtain ⟨hr1, hr3⟩ := natAbs_bounds_of_mem_frequencies_three hr
    have hr1R : (1 : ℝ) ≤ r.natAbs := by exact_mod_cast hr1
    have hr3R : (r.natAbs : ℝ) ≤ 3 := by exact_mod_cast hr3
    rw [weightedPhaseSum_norm_eq_mangoldtSum n 2 r]
    apply (hsmall ((r.natAbs : ℝ) * 2 * n) (by nlinarith) (by nlinarith)).le
  · intro r hr
    obtain ⟨hr1, hr3⟩ := natAbs_bounds_of_mem_frequencies_three hr
    have hr1R : (1 : ℝ) ≤ r.natAbs := by exact_mod_cast hr1
    have hr3R : (r.natAbs : ℝ) ≤ 3 := by exact_mod_cast hr3
    have hmap := weightedPhaseSum_norm_eq_mangoldtSum n 1 r
    simp only [one_mul, mul_one, Nat.cast_one] at hmap
    rw [hmap]
    exact (hsmall ((r.natAbs : ℝ) * n) (by nlinarith) (by nlinarith)).le

/-- Generic finite-Fourier form of the Section 7 argument.  If `psi` and
`-psi` have trigonometric upper majorants with mean `c` and coefficient
`ℓ¹` norm at most `A`, and every relevant reciprocal phase sum has norm at
most `M`, then the Kummer detector and the discarded-prime estimate give
this inequality.  Keeping `c` and `A` explicit lets us use any fully
verified finite majorant. -/
lemma generic_section7_inequality (n : ℕ) (hn : 0 < n)
    (hsq : Squarefree (Nat.choose (n + n) n))
    (F : Finset ℤ) (c A M : ℝ) (aPlus aMinus : ℤ → ℂ)
    (hplus : Sawtooth.IsUpperMajorant F Sawtooth.psi c aPlus)
    (hminus : Sawtooth.IsUpperMajorant F (fun x => -Sawtooth.psi x) c aMinus)
    (hcoeffPlus : (∑ r ∈ F, ‖aPlus r‖) ≤ A)
    (hcoeffMinus : (∑ r ∈ F, ‖aMinus r‖) ≤ A)
    (hphaseTwo : ∀ r ∈ F,
      ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => ((2 * n : ℕ) : ℝ) / d) r‖ ≤ M)
    (hphaseOne : ∀ r ∈ F,
      ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => (n : ℝ) / d) r‖ ≤ M)
    (hM : 0 ≤ M) :
    (1 / 2 - 3 * c) *
        (∑ d ∈ I n, ArithmeticFunction.vonMangoldt d) ≤
      3 * A * M + (1 / 2) * Real.log (2 * n) := by
  let S : ℝ := ∑ d ∈ I n, ArithmeticFunction.vonMangoldt d
  let bad : ℝ :=
    ∑ d ∈ (I n).filter (fun d => ¬Nat.Coprime d (2 * n)),
      ArithmeticFunction.vonMangoldt d
  let U : ℝ :=
    |∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
      Sawtooth.psi ((2 * n : ℕ) / (d : ℝ))|
  let V : ℝ :=
    |∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
      Sawtooth.psi ((n : ℝ) / (d : ℝ))|
  have hw : ∀ d ∈ I n, 0 ≤ ArithmeticFunction.vonMangoldt d := by
    intro d hd
    exact ArithmeticFunction.vonMangoldt_nonneg
  have hU : U ≤ c * S + A * M := by
    exact Sawtooth.abs_weighted_sum_le_of_majorants
      (I n) (fun d => ArithmeticFunction.vonMangoldt d)
      (fun d => ((2 * n : ℕ) : ℝ) / d) F Sawtooth.psi c A M
      aPlus aMinus hw hplus hminus hphaseTwo hcoeffPlus hcoeffMinus hM
  have hV : V ≤ c * S + A * M := by
    exact Sawtooth.abs_weighted_sum_le_of_majorants
      (I n) (fun d => ArithmeticFunction.vonMangoldt d)
      (fun d => (n : ℝ) / d) F Sawtooth.psi c A M
      aPlus aMinus hw hplus hminus hphaseOne hcoeffPlus hcoeffMinus hM
  have hdetector : (S - bad) / 2 ≤ U + 2 * V := by
    exact sawtooth_mangoldt_detector_sub_bad n hsq
  have hbad : bad ≤ Real.log (2 * n) := bad_mangoldt_mass_le_log_two_mul n hn
  dsimp only [S, bad, U, V] at hU hV hdetector hbad ⊢
  linarith

/-- The generic inequality specialized to the explicit order-three
constants `c = 33/200` and `A = 3/4`. -/
lemma degreeThree_section7_upper_of_data (n : ℕ) (hn : 0 < n)
    (hsq : Squarefree (Nat.choose (n + n) n)) (M : ℝ)
    (aPlus aMinus : ℤ → ℂ)
    (hplus : Sawtooth.IsUpperMajorant (Sawtooth.frequencies 3)
      Sawtooth.psi (33 / 200) aPlus)
    (hminus : Sawtooth.IsUpperMajorant (Sawtooth.frequencies 3)
      (fun x => -Sawtooth.psi x) (33 / 200) aMinus)
    (hcoeffPlus : (∑ r ∈ Sawtooth.frequencies 3, ‖aPlus r‖) ≤ 3 / 4)
    (hcoeffMinus : (∑ r ∈ Sawtooth.frequencies 3, ‖aMinus r‖) ≤ 3 / 4)
    (hphaseTwo : ∀ r ∈ Sawtooth.frequencies 3,
      ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => ((2 * n : ℕ) : ℝ) / d) r‖ ≤ M)
    (hphaseOne : ∀ r ∈ Sawtooth.frequencies 3,
      ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => (n : ℝ) / d) r‖ ≤ M)
    (hM : 0 ≤ M) :
    (∑ d ∈ I n, ArithmeticFunction.vonMangoldt d) ≤
      450 * M + 100 * Real.log (2 * n) := by
  have h := generic_section7_inequality n hn hsq
    (Sawtooth.frequencies 3) (33 / 200) (3 / 4) M aPlus aMinus
    hplus hminus hcoeffPlus hcoeffMinus hphaseTwo hphaseOne hM
  norm_num at h ⊢
  linarith

/-- Once the explicit order-three majorants are known, any strict numerical
lower bound beyond the Section 7 loss forces a genuinely large reciprocal
Mangoldt sum at one of the finitely many frequencies in `[n,6n]`. -/
lemma exists_large_mangoldtSum_of_degreeThree_data (n : ℕ) (hn : 0 < n)
    (hsq : Squarefree (Nat.choose (n + n) n)) (M : ℝ)
    (aPlus aMinus : ℤ → ℂ)
    (hplus : Sawtooth.IsUpperMajorant (Sawtooth.frequencies 3)
      Sawtooth.psi (33 / 200) aPlus)
    (hminus : Sawtooth.IsUpperMajorant (Sawtooth.frequencies 3)
      (fun x => -Sawtooth.psi x) (33 / 200) aMinus)
    (hcoeffPlus : (∑ r ∈ Sawtooth.frequencies 3, ‖aPlus r‖) ≤ 3 / 4)
    (hcoeffMinus : (∑ r ∈ Sawtooth.frequencies 3, ‖aMinus r‖) ≤ 3 / 4)
    (hM : 0 ≤ M)
    (hnumeric : M <
      ((∑ d ∈ I n, ArithmeticFunction.vonMangoldt d) -
        100 * Real.log (2 * n)) / 450) :
    ∃ x : ℝ, (n : ℝ) ≤ x ∧ x ≤ 6 * n ∧ M ≤ ‖mangoldtSum n x‖ := by
  by_contra hlarge
  push Not at hlarge
  have hsmall : ∀ x : ℝ, (n : ℝ) ≤ x → x ≤ 6 * n →
      ‖mangoldtSum n x‖ < M := by
    intro x hnx hx6
    exact hlarge x hnx hx6
  obtain ⟨hphaseTwo, hphaseOne⟩ :=
    degreeThree_phase_bounds_of_forall_lt n M hsmall
  have hupper := degreeThree_section7_upper_of_data n hn hsq M aPlus aMinus
    hplus hminus hcoeffPlus hcoeffMinus hphaseTwo hphaseOne hM
  linarith

/-- The fully numerical Section 7 conclusion at the global analytic cutoff,
conditional only on the four finite order-three majorant certificates. -/
lemma exists_large_mangoldtSum_at_cutoff_of_degreeThree_data
    (n : ℕ) (hn : 2 ^ 1728 ≤ n)
    (hsq : Squarefree (Nat.choose (n + n) n))
    (aPlus aMinus : ℤ → ℂ)
    (hplus : Sawtooth.IsUpperMajorant (Sawtooth.frequencies 3)
      Sawtooth.psi (33 / 200) aPlus)
    (hminus : Sawtooth.IsUpperMajorant (Sawtooth.frequencies 3)
      (fun x => -Sawtooth.psi x) (33 / 200) aMinus)
    (hcoeffPlus : (∑ r ∈ Sawtooth.frequencies 3, ‖aPlus r‖) ≤ 3 / 4)
    (hcoeffMinus : (∑ r ∈ Sawtooth.frequencies 3, ‖aMinus r‖) ≤ 3 / 4) :
    ∃ x : ℝ, (n : ℝ) ≤ x ∧ x ≤ 6 * n ∧
      (1 / 5000 : ℝ) * Real.sqrt n ≤ ‖mangoldtSum n x‖ := by
  have hnpos : 0 < n := (by positivity : 0 < 2 ^ 1728).trans_le hn
  have hnumeric := ExplicitChebyshev.sqrtInterval_mangoldt_degree_three_450 n hn
  rw [← squareRootInterval_eq_Ioc] at hnumeric
  have hnumeric' :
      (1 / 5000 : ℝ) * Real.sqrt n <
        ((∑ d ∈ I n, ArithmeticFunction.vonMangoldt d) -
          100 * Real.log (2 * n)) / 450 := by
    convert hnumeric using 1
    ring
  apply exists_large_mangoldtSum_of_degreeThree_data n hnpos hsq
    ((1 / 5000 : ℝ) * Real.sqrt n) aPlus aMinus
    hplus hminus hcoeffPlus hcoeffMinus
  · positivity
  · exact hnumeric'

/-- Unconditional Section 7 lower bound.  Under squarefreeness of the
central binomial coefficient, one of the six reciprocal frequencies in
`[n,6n]` has von Mangoldt exponential sum at least `sqrt n / 5000`. -/
theorem exists_large_reciprocal_mangoldt_sum (n : ℕ)
    (hn : 2 ^ 1728 ≤ n)
    (hsq : Squarefree (Nat.choose (2 * n) n)) :
    ∃ x : ℝ, (n : ℝ) ≤ x ∧ x ≤ 6 * n ∧
      (1 / 5000 : ℝ) * Real.sqrt n ≤ ‖mangoldtSum n x‖ := by
  have hsq' : Squarefree (Nat.choose (n + n) n) := by
    simpa [two_mul] using hsq
  exact exists_large_mangoldtSum_at_cutoff_of_degreeThree_data n hn hsq'
    VaalerDegreeTen.degreeThreePlusCoefficient
    VaalerDegreeTen.degreeThreeMinusCoefficient
    VaalerDegreeTen.degreeThreePlus_majorant
    VaalerDegreeTen.degreeThreeMinus_majorant
    VaalerDegreeTen.sum_norm_degreeThreePlusCoefficient_le
    VaalerDegreeTen.sum_norm_degreeThreeMinusCoefficient_le

end Section7

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175/FinalLarge.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Final large-power assembly for Erdős Problem 175

This module isolates the last logical step of the proof.  Section 7 gives a
large reciprocal Mangoldt sum under the squarefreeness assumption, the
Granville--Ramaré estimate gives the opposite upper bound, and the explicit
cutoff calculation shows that the two inequalities are incompatible.
-/

namespace FinalLarge

/-- A nonsquarefree natural has a prime-square divisor. -/
lemma exists_prime_sq_dvd_of_not_squarefree {m : ℕ} (hm : ¬ Squarefree m) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ m := by
  by_contra h
  push Not at h
  apply hm
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp
  simpa [pow_two] using h p hp

/-- The Section 7 and Section 9 definitions describe exactly the same finite
reciprocal von Mangoldt sum. -/
lemma section7_mangoldtSum_eq_granvilleRamare9 (n : ℕ) (x : ℝ) :
    Section7.mangoldtSum n x = GranvilleRamare9.mangoldtSum n x := by
  rw [GranvilleRamare9.mangoldtSum_eq]
  unfold Section7.mangoldtSum
  apply Finset.sum_congr rfl
  intro d _hd
  congr 1
  unfold Sawtooth.e e
  congr 1
  push_cast
  ring

/-- Once the reciprocal-sum upper bound has been established, the large
power-of-two case follows solely from Section 7 and the checked numerical
cutoff. -/
theorem large_power_witness_of_upper
    (hupper : ∀ k : ℕ, 8192 ≤ k → ∀ x : ℝ,
      (((2 : ℕ) ^ k : ℕ) : ℝ) ≤ x →
      x ≤ 6 * (((2 : ℕ) ^ k : ℕ) : ℝ) →
      ‖GranvilleRamare9.mangoldtSum (2 ^ k) x‖ ≤
        (10 ^ 12 : ℝ) * (((2 : ℕ) ^ k : ℕ) : ℝ) ^ (27 / 56 : ℝ) *
          Real.log (256 * (((2 : ℕ) ^ k : ℕ) : ℝ)) ^ 6) :
    ∀ k : ℕ, 8192 ≤ k →
      ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ Nat.choose (2 * 2 ^ k) (2 ^ k) := by
  intro k hk
  apply exists_prime_sq_dvd_of_not_squarefree
  intro hsq
  have hcut : 2 ^ 1728 ≤ (2 : ℕ) ^ k :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨x, hxlo, hxhi, hlower⟩ :=
    Section7.exists_large_reciprocal_mangoldt_sum (2 ^ k) hcut hsq
  have hlower' :
      (1 / 5000 : ℝ) * Real.sqrt (2 ^ k : ℕ) ≤
        ‖GranvilleRamare9.mangoldtSum (2 ^ k) x‖ := by
    simpa only [section7_mangoldtSum_eq_granvilleRamare9] using hlower
  have hpow : 2 ^ 8192 ≤ (2 : ℕ) ^ k :=
    Nat.pow_le_pow_right (by norm_num) hk
  exact not_final_lower_le_upper_of_ge_cutoff hpow
    (hlower'.trans (hupper k hk x hxlo hxhi))

/-- The unconditional large-power case, obtained from the fully explicit
Granville--Ramaré bound proved in `GranvilleRamare9`. -/
theorem large_power_witness (k : ℕ) (hk : 8192 ≤ k) :
    ∃ p : ℕ, p.Prime ∧
      p ^ 2 ∣ Nat.choose (2 * 2 ^ k) (2 ^ k) := by
  exact large_power_witness_of_upper
    (fun k hk x hxlo hxhi =>
      GranvilleRamare9.norm_mangoldtSum_two_pow_le_final
        k x hk hxlo hxhi) k hk

end FinalLarge

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos175.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 175.
https://www.erdosproblems.com/forum/thread/175

Informal authors:
- Andrew Granville
- Olivier Ramaré

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos175.md
-/
/-
This file formalizes the resolution of Erdős Problem 175.

Mathematical sources:
* A. Granville and O. Ramaré, "Explicit bounds on exponential sums and the
  scarcity of squarefree binomial coefficients", Mathematika 43 (1996),
  73--107.
* G. Velammal, "Is the binomial coefficient (2n choose n) squarefree?",
  Hardy--Ramanujan Journal 18 (1995), 23--45.

The detailed reconstruction and declaration map are in `tex/175.tex`.

Progress log:
* Phase 1 complete: the Granville--Ramaré argument and all formal dependencies
  are recorded in `tex/175.tex`.
* Phase 2 verified here: Kummer's binary reduction and a kernel-checked carry
  certificate for every `3 ≤ k < 8192`.
* The companion modules in `Erdos175/` formalize the explicit large-`n`
  estimates from Sections 7--10 of Granville--Ramaré.
-/

open Nat

/-- The central binomial coefficient. -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- Every central binomial coefficient is positive. -/
lemma centralBinom_pos (n : ℕ) : 0 < centralBinom n := by
  exact Nat.choose_pos (by omega)

/-- The base-two digit sum of a positive natural number is positive. -/
lemma digitSum_two_pos {n : ℕ} (hn : n ≠ 0) : 0 < (Nat.digits 2 n).sum := by
  have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hlast : (Nat.digits 2 n).getLast hnil ≠ 0 := Nat.getLast_digit_ne_zero 2 hn
  have hmem : (Nat.digits 2 n).getLast hnil ∈ Nat.digits 2 n := List.getLast_mem hnil
  have hle := List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
  omega

/-- Kummer's identity at two: the two-adic valuation of the central binomial
coefficient is the binary digit sum of its index. -/
lemma padicValNat_two_centralBinom (n : ℕ) :
    padicValNat 2 (centralBinom n) = (Nat.digits 2 n).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcb : centralBinom n = Nat.choose (n + n) n := by
    rw [centralBinom, two_mul]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [centralBinom]
  have hdd : (Nat.digits 2 (n + n)).sum = (Nat.digits 2 n).sum := by
    have h2 : n + n = 2 ^ 1 * n := by ring
    rw [h2, Nat.digits_base_pow_mul (by norm_num) hn]
    simp
  have key :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits' (p := 2) (k := n) (n := n)
  rw [hcb]
  rw [hdd] at key
  simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at key
  omega

/-- A positive natural has binary digit sum one exactly when it is a power of
two. -/
lemma digitSum_two_eq_one_iff {n : ℕ} (hn : 0 < n) :
    (Nat.digits 2 n).sum = 1 ↔ ∃ k, n = 2 ^ k := by
  constructor
  · intro hs
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
    have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    rw [Nat.digits_base_pow_mul (by norm_num) hmpos] at hs
    simp only [List.sum_append, List.sum_replicate, smul_eq_mul, Nat.mul_zero,
      zero_add] at hs
    have hmod : m % 2 = 1 := Nat.odd_iff.mp hm
    rw [Nat.digits_of_two_le_of_pos (by norm_num) hmpos, hmod, List.sum_cons] at hs
    have hzero : (Nat.digits 2 (m / 2)).sum = 0 := by omega
    have hm2 : m / 2 = 0 := by
      by_contra h
      exact absurd hzero (digitSum_two_pos h).ne'
    have hm1 : m = 1 := by omega
    exact ⟨k, by rw [hm1, mul_one]⟩
  · rintro ⟨k, rfl⟩
    rw [show (2 : ℕ) ^ k = 2 ^ k * 1 from (mul_one _).symm,
      Nat.digits_base_pow_mul (by norm_num) one_pos,
      Nat.digits_of_two_le_of_pos (by norm_num) one_pos]
    simp

/-- Except at powers of two, the central binomial coefficient is divisible by
four. -/
lemma four_dvd_centralBinom_iff (n : ℕ) (hn : 2 ≤ n) :
    4 ∣ centralBinom n ↔ ¬ ∃ k : ℕ, n = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < n := by omega
  have hcb0 : centralBinom n ≠ 0 := (centralBinom_pos n).ne'
  have hdvd : 4 ∣ centralBinom n ↔ 2 ≤ padicValNat 2 (centralBinom n) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact padicValNat_dvd_iff_le hcb0
  rw [hdvd, padicValNat_two_centralBinom]
  have hs1 : 0 < (Nat.digits 2 n).sum := digitSum_two_pos hpos.ne'
  rw [show (¬ ∃ k, n = 2 ^ k) ↔ (Nat.digits 2 n).sum ≠ 1 from
    (digitSum_two_eq_one_iff hpos).not.symm]
  omega

/-- The number of carries in the base-`p` addition `n + n`.  This is written
in exactly the finite form used by Mathlib's Kummer theorem. -/
def centralCarryCount (p n : ℕ) : ℕ :=
  ((Finset.Ico 1 (Nat.log p (n + n) + 1)).filter fun i =>
    p ^ i ≤ n % p ^ i + n % p ^ i).card

/-- Kummer identifies `centralCarryCount` with the valuation of the central
binomial coefficient. -/
lemma padicValNat_centralBinom_eq_centralCarryCount
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    padicValNat p (centralBinom n) = centralCarryCount p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [centralBinom, show 2 * n = n + n by omega]
  exact padicValNat_choose' (Nat.lt_succ_self _)

/-- The small prime used by the finite Granville--Ramaré certificate. -/
def finitePrime (k : ℕ) : ℕ :=
  if k = 6 then 5 else if k = 8 then 7 else 3

lemma finitePrime_prime (k : ℕ) : (finitePrime k).Prime := by
  simp only [finitePrime]
  split_ifs <;> norm_num

/-- A bounded carry count used to make the finite certificate kernel-checkable.
The first twenty-eight digit positions suffice throughout the certified range. -/
def lowCarryCount (p n : ℕ) : ℕ :=
  ((Finset.Icc 1 28).filter fun i =>
    p ^ i ≤ n % p ^ i + n % p ^ i).card

/-- Every carry detected in the first twenty-eight positions is one of the
carries counted by Kummer's full formula. -/
lemma lowCarryCount_le_centralCarryCount {p n : ℕ} (hp : 2 ≤ p) (hn : n ≠ 0) :
    lowCarryCount p n ≤ centralCarryCount p n := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_Icc] at hi
  simp only [Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨hi.1.1, ?_⟩, hi.2⟩
  have hpow : p ^ i ≤ n + n := by
    calc
      p ^ i ≤ n % p ^ i + n % p ^ i := hi.2
      _ ≤ n + n := Nat.add_le_add (Nat.mod_le _ _) (Nat.mod_le _ _)
  have hlog : i ≤ Nat.log p (n + n) :=
    (Nat.le_log_iff_pow_le (by omega) (by omega)).2 hpow
  omega

/-- The repeated-squaring evaluator used by the certificate agrees with
ordinary natural exponentiation. -/
lemma npowBinRecAuto_two_eq (k : ℕ) : npowBinRecAuto k (2 : ℕ) = 2 ^ k := by
  rw [← npowRec_eq_npowBinRec]
  induction k with
  | zero => rfl
  | succ k ih =>
      change npowRec k 2 * 2 = Nat.pow 2 k * 2
      exact congrArg (fun x : ℕ => x * 2) ih

/- The final finite certificate is split into eight independent blocks of
`1024 = 4 * 4 * 64` exponents.  Keeping each reflected proposition this small
lets ordinary `decide` construct a proof term under Lean's default limits. -/
lemma finite_low_carry_check_8192_0 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_1 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 1024 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_2 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 2048 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_3 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 3072 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_4 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 4096 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_5 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 5120 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_6 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 6144 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_7 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 7168 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192 :
    ∀ q : Fin 8, ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 1024 * (q : ℕ) + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  intro q a b j
  fin_cases q <;>
    simp only [Nat.mul_zero, zero_add, Nat.reduceMul] <;>
    first
    | exact finite_low_carry_check_8192_0 a b j
    | exact finite_low_carry_check_8192_1 a b j
    | exact finite_low_carry_check_8192_2 a b j
    | exact finite_low_carry_check_8192_3 a b j
    | exact finite_low_carry_check_8192_4 a b j
    | exact finite_low_carry_check_8192_5 a b j
    | exact finite_low_carry_check_8192_6 a b j
    | exact finite_low_carry_check_8192_7 a b j

/-- Every exponent below `8192` has at least two certified carries. -/
lemma finite_carry_check_8192 :
    ∀ k : Fin 8192, 3 ≤ (k : ℕ) →
      2 ≤ centralCarryCount (finitePrime k) (2 ^ (k : ℕ)) := by
  intro k hk3
  let q : Fin 8 := ⟨(k : ℕ) / 1024, by omega⟩
  let a : Fin 4 := ⟨((k : ℕ) % 1024) / 256, by omega⟩
  let b : Fin 4 := ⟨((k : ℕ) % 256) / 64, by omega⟩
  let j : Fin 64 := ⟨(k : ℕ) % 64, Nat.mod_lt _ (by norm_num)⟩
  have hkdecomp :
      1024 * (q : ℕ) + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ) = (k : ℕ) := by
    dsimp [q, a, b, j]
    omega
  have hlow : 2 ≤ lowCarryCount (finitePrime k) (2 ^ (k : ℕ)) := by
    simpa only [hkdecomp, npowBinRecAuto_two_eq] using
      finite_low_carry_check_8192 q a b j (by omega)
  exact hlow.trans (lowCarryCount_le_centralCarryCount (by
    simp only [finitePrime]
    split_ifs <;> omega) (by positivity))

/-- The finite conclusion through the final coarse analytic cutoff `8192`. -/
lemma exists_prime_sq_dvd_centralBinom_two_pow_of_lt_8192
    {k : ℕ} (hk3 : 3 ≤ k) (hk : k < 8192) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ centralBinom (2 ^ k) := by
  let k' : Fin 8192 := ⟨k, hk⟩
  let p := finitePrime k
  have hp : p.Prime := finitePrime_prime k
  letI : Fact p.Prime := ⟨hp⟩
  have hcarry : 2 ≤ centralCarryCount p (2 ^ k) := by
    simpa [k', p] using finite_carry_check_8192 k' hk3
  have hval : 2 ≤ padicValNat p (centralBinom (2 ^ k)) := by
    simpa [padicValNat_centralBinom_eq_centralCarryCount hp] using hcarry
  have hdvd : p ^ 2 ∣ centralBinom (2 ^ k) :=
    (padicValNat_dvd_iff_le (centralBinom_pos (2 ^ k)).ne').mpr hval
  exact ⟨p, hp, hdvd⟩

/-- A prime-square divisor contradicts Mathlib's `Squarefree` predicate. -/
lemma not_squarefree_of_prime_sq_dvd {m p : ℕ} (hp : p.Prime)
    (hdvd : p ^ 2 ∣ m) : ¬ Squarefree m := by
  intro hm
  exact (Nat.squarefree_iff_prime_squarefree.mp hm p hp) (by
    simpa [pow_two] using hdvd)

/-- Final elementary assembly at the coarse explicit cutoff `8192`. -/
lemma erdos_175_of_large_two_pow_8192
    (hlarge : ∀ k : ℕ, 2 ^ 8192 ≤ 2 ^ k →
      ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ centralBinom (2 ^ k)) :
    ∀ n : ℕ, 5 ≤ n → ¬ Squarefree (Nat.choose (2 * n) n) := by
  intro n hn
  change ¬ Squarefree (centralBinom n)
  by_cases hpow : ∃ k : ℕ, n = 2 ^ k
  · obtain ⟨k, rfl⟩ := hpow
    have hk3 : 3 ≤ k := by
      by_contra hk
      have hk' : k ≤ 2 := by omega
      interval_cases k <;> norm_num at hn
    by_cases hk : k < 8192
    · obtain ⟨p, hp, hdvd⟩ :=
        exists_prime_sq_dvd_centralBinom_two_pow_of_lt_8192 hk3 hk
      exact not_squarefree_of_prime_sq_dvd hp hdvd
    · obtain ⟨p, hp, hdvd⟩ := hlarge k (by
        exact Nat.pow_le_pow_right (by norm_num) (by omega))
      exact not_squarefree_of_prime_sq_dvd hp hdvd
  · exact not_squarefree_of_prime_sq_dvd Nat.prime_two (by
      simpa using (four_dvd_centralBinom_iff n (by omega)).mpr hpow)

/-- Erdős Problem 175: for every `n ≥ 5`, the central binomial coefficient
is not squarefree. -/
theorem erdos_175 {n : ℕ} (hn : 5 ≤ n) :
    ¬ Squarefree (Nat.choose (2 * n) n) := by
  apply erdos_175_of_large_two_pow_8192
    (fun k hkpow => ?_)
    n hn
  have hk : 8192 ≤ k :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hkpow
  simpa only [centralBinom] using FinalLarge.large_power_witness k hk

end

#print axioms erdos_175
-- 'Erdos175.erdos_175' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos175
