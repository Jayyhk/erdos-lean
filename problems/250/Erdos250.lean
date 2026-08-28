import Mathlib

namespace Erdos250

/-
# Problem Description

Erdős Problem 250. Is `∑ σ(n)/2ⁿ` irrational, where `σ` is the sum-of-divisors function?
`erdos_250` proves that it is.

The question appears in [ErGr80, p.61] and [Er88c, p.102]. The affirmative answer is due to
Nesterenko [Ne96]. The statement below is that of the Formal Conjectures entry: for every real
`x`, if the series has sum `x` then `x` is irrational. That form is not vacuous -- convergence
is established inside this file by `sigmaTerm_summable`, which bounds `σ(n) ≤ n²` against a
geometric series, so such an `x` exists. Mathlib's `σ 1 0 = 0`, so summing from `n = 0` agrees
with the sum over positive integers that Erdős writes.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos250.lean` together with the thirteen modules of
`src/latest/ErdosProblems/Erdos250/`. The fourteen files are concatenated here in dependency
order, with their project-internal imports removed so that `Mathlib` is the only import, each
module's contents kept in a `section` carrying its own `open` lines, one unclosed upstream
scope closed explicitly, and the whole wrapped once in `namespace Erdos250` with the upstream
trust-base print line removed. No mathematical content is changed.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250/Erdos250RatFrac.lean` -/

section
open scoped BigOperators

noncomputable section

namespace DoublePartialFraction

open Polynomial

variable {K ι : Type*} [Field K] [DecidableEq ι]

def lin (r : ι → K) (i : ι) : K[X] := X - C (r i)

def rest (s : Finset ι) (r : ι → K) (i : ι) : K[X] :=
  ∏ k ∈ s.erase i, (lin r k) ^ 2

def den (s : Finset ι) (r : ι → K) : K[X] :=
  ∏ k ∈ s, (lin r k) ^ 2

def B (s : Finset ι) (r : ι → K) (P : K[X]) (i : ι) : K :=
  P.eval (r i) / (rest s r i).eval (r i)

def A (s : Finset ι) (r : ι → K) (P : K[X]) (i : ι) : K :=
  (P.derivative.eval (r i) - B s r P i * (rest s r i).derivative.eval (r i)) /
    (rest s r i).eval (r i)

def numerator (s : Finset ι) (r : ι → K) (P : K[X]) : K[X] :=
  ∑ i ∈ s, (C (A s r P i) * lin r i + C (B s r P i)) * rest s r i

@[simp] lemma eval_lin (r : ι → K) (i : ι) (x : K) :
    (lin r i).eval x = x - r i := by simp [lin]

@[simp] lemma derivative_lin (r : ι → K) (i : ι) :
    (lin r i).derivative = 1 := by simp [lin]

lemma rest_eval_ne_zero {s : Finset ι} {r : ι → K}
    (hr : Set.InjOn r s) {i : ι} (hi : i ∈ s) :
    (rest s r i).eval (r i) ≠ 0 := by
  rw [rest, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  simp only [eval_pow, eval_lin]
  apply pow_ne_zero
  exact sub_ne_zero.mpr fun h ↦
    (Finset.ne_of_mem_erase hk).symm (hr hi (Finset.mem_of_mem_erase hk) h)

lemma rest_eval_eq_zero {s : Finset ι} {r : ι → K}
    {i k : ι} (hi : i ∈ s) (hik : i ≠ k) :
    (rest s r k).eval (r i) = 0 := by
  rw [rest, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik, hi⟩)
  simp

lemma sq_dvd_rest {s : Finset ι} {r : ι → K}
    {i k : ι} (hi : i ∈ s) (hik : i ≠ k) :
    (lin r i) ^ 2 ∣ rest s r k := by
  exact Finset.dvd_prod_of_mem (fun j ↦ (lin r j) ^ 2)
    (Finset.mem_erase.mpr ⟨hik, hi⟩)

lemma eval_derivative_eq_zero_of_sq_dvd {p : K[X]} {x : K}
    (h : (X - C x) ^ 2 ∣ p) : p.derivative.eval x = 0 := by
  rcases h with ⟨q, rfl⟩
  simp [derivative_mul, derivative_pow]

lemma rest_derivative_eval_eq_zero {s : Finset ι} {r : ι → K}
    {i k : ι} (hi : i ∈ s) (hik : i ≠ k) :
    (rest s r k).derivative.eval (r i) = 0 := by
  apply eval_derivative_eq_zero_of_sq_dvd
  simpa [lin] using sq_dvd_rest (r := r) hi hik

lemma numerator_eval {s : Finset ι} {r : ι → K} {P : K[X]}
    (hr : Set.InjOn r s) {i : ι} (hi : i ∈ s) :
    (numerator s r P).eval (r i) = P.eval (r i) := by
  rw [numerator, eval_finsetSum]
  simp_rw [eval_mul, eval_add, eval_C, eval_mul, eval_C, eval_lin]
  rw [Finset.sum_eq_single i]
  · simp [B, rest_eval_ne_zero hr hi]
  · intro k hk hki
    rw [rest_eval_eq_zero hi hki.symm, mul_zero]
  · exact fun h ↦ (h hi).elim

lemma numerator_derivative_eval {s : Finset ι} {r : ι → K} {P : K[X]}
    (hr : Set.InjOn r s) {i : ι} (hi : i ∈ s) :
    (numerator s r P).derivative.eval (r i) = P.derivative.eval (r i) := by
  rw [numerator, derivative_sum, eval_finsetSum]
  rw [Finset.sum_eq_single i]
  · simp only [derivative_mul, derivative_add, derivative_C, zero_mul, derivative_lin,
      mul_one, zero_add, eval_add, eval_mul, eval_C, eval_lin]
    simp [A, rest_eval_ne_zero hr hi]
  · intro k hk hki
    simp only [derivative_mul, derivative_add, derivative_C, zero_mul, derivative_lin,
      mul_one, zero_add, eval_add, eval_mul, eval_C, eval_lin]
    rw [rest_eval_eq_zero hi hki.symm, rest_derivative_eval_eq_zero hi hki.symm]
    ring
  · exact fun h ↦ (h hi).elim

lemma sq_dvd_of_eval_derivative_eq_zero {p : K[X]} {x : K}
    (h0 : p.eval x = 0) (h1 : p.derivative.eval x = 0) :
    (X - C x) ^ 2 ∣ p := by
  have hlin : X - C x ∣ p := (dvd_iff_isRoot).mpr h0
  rcases hlin with ⟨q, hq⟩
  subst p
  have hq0 : q.eval x = 0 := by
    simpa [derivative_mul] using h1
  rcases (dvd_iff_isRoot).mpr hq0 with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  rw [hu]
  ring

lemma den_dvd_sub_numerator {s : Finset ι} {r : ι → K} {P : K[X]}
    (hr : Set.InjOn r s) : den s r ∣ P - numerator s r P := by
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    apply IsCoprime.pow
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr fun h ↦ hij (hr hi hj h)).isUnit
  · intro i hi
    apply sq_dvd_of_eval_derivative_eq_zero
    · simp [numerator_eval hr hi]
    · simp [numerator_derivative_eval hr hi]

lemma natDegree_rest {s : Finset ι} {r : ι → K} {i : ι} :
    (rest s r i).natDegree = 2 * (s.erase i).card := by
  rw [rest, Polynomial.natDegree_prod_of_monic]
  · simp [lin, Nat.mul_comm]
  · intro k hk
    exact (Polynomial.monic_X_sub_C (r k)).pow 2

lemma natDegree_den {s : Finset ι} {r : ι → K} :
    (den s r).natDegree = 2 * s.card := by
  rw [den, Polynomial.natDegree_prod_of_monic]
  · simp [lin, Nat.mul_comm]
  · intro k hk
    exact (Polynomial.monic_X_sub_C (r k)).pow 2

lemma natDegree_numerator_lt {s : Finset ι} {r : ι → K} {P : K[X]}
    (hs : s.Nonempty) : (numerator s r P).natDegree < 2 * s.card := by
  have hterm : ∀ i ∈ s,
      ((C (A s r P i) * lin r i + C (B s r P i)) * rest s r i).natDegree ≤
        2 * s.card - 1 := by
    intro i hi
    have herase : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
    have hcard : 1 ≤ s.card := Finset.one_le_card.mpr ⟨i, hi⟩
    have hlin : (C (A s r P i) * lin r i + C (B s r P i)).natDegree ≤ 1 := by
      have hmul : (C (A s r P i) * lin r i).natDegree ≤ 1 :=
        (Polynomial.natDegree_mul_le).trans (by simp [lin])
      exact (Polynomial.natDegree_add_le _ _).trans (max_le hmul (by simp))
    calc
      _ ≤ (C (A s r P i) * lin r i + C (B s r P i)).natDegree +
          (rest s r i).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1 + 2 * (s.card - 1) := by rw [natDegree_rest, herase]; omega
      _ ≤ 2 * s.card - 1 := by omega
  have hsum : (numerator s r P).natDegree ≤ 2 * s.card - 1 := by
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ hterm
  exact hsum.trans_lt (Nat.sub_lt (by positivity) (by omega))

theorem polynomial_identity {s : Finset ι} {r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hr : Set.InjOn r s)
    (hP : P.natDegree < 2 * s.card) :
    P = numerator s r P := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_dvd_of_natDegree_lt (den_dvd_sub_numerator hr)
  rw [natDegree_den]
  exact (Polynomial.natDegree_sub_le _ _).trans_lt (max_lt hP (natDegree_numerator_lt hs))

lemma den_eq_mul_rest {s : Finset ι} {r : ι → K} {i : ι} (hi : i ∈ s) :
    den s r = (lin r i) ^ 2 * rest s r i := by
  rw [den, rest, Finset.mul_prod_erase s (fun k ↦ (lin r k) ^ 2) hi]

lemma rest_eval_ne_zero_at {s : Finset ι} {r : ι → K} {i : ι} {t : K}
    (ht : ∀ k ∈ s, t ≠ r k) : (rest s r i).eval t ≠ 0 := by
  rw [rest, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  simp only [eval_pow, eval_lin]
  exact pow_ne_zero 2 (sub_ne_zero.mpr (ht k (Finset.mem_of_mem_erase hk)))

theorem partial_fraction {s : Finset ι} {r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hr : Set.InjOn r s)
    (hP : P.natDegree < 2 * s.card) (t : K)
    (ht : ∀ i ∈ s, t ≠ r i) :
    P.eval t / (den s r).eval t =
      ∑ i ∈ s, (A s r P i / (t - r i) + B s r P i / (t - r i) ^ 2) := by
  calc
    P.eval t / (den s r).eval t =
        (numerator s r P).eval t / (den s r).eval t := by
          exact congrArg (fun Q : K[X] ↦ Q.eval t / (den s r).eval t)
            (polynomial_identity hs hr hP)
    _ = ∑ i ∈ s, (A s r P i / (t - r i) + B s r P i / (t - r i) ^ 2) := by
      rw [numerator, eval_finsetSum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rw [den_eq_mul_rest hi]
      simp only [eval_mul, eval_pow, eval_add, eval_C, eval_lin]
      field_simp [ht i hi, rest_eval_ne_zero_at ht]

namespace Scaled

def lin (c r : ι → K) (i : ι) : K[X] :=
  C (c i) * DoublePartialFraction.lin r i

def rest (s : Finset ι) (c r : ι → K) (i : ι) : K[X] :=
  ∏ k ∈ s.erase i, (lin c r k) ^ 2

def den (s : Finset ι) (c r : ι → K) : K[X] :=
  ∏ k ∈ s, (lin c r k) ^ 2

def V (s : Finset ι) (c r : ι → K) (P : K[X]) (i : ι) : K :=
  P.eval (r i) / (rest s c r i).eval (r i)

def U (s : Finset ι) (c r : ι → K) (P : K[X]) (i : ι) : K :=
  (P.derivative.eval (r i) - V s c r P i * (rest s c r i).derivative.eval (r i)) /
    (c i * (rest s c r i).eval (r i))

def numerator (s : Finset ι) (c r : ι → K) (P : K[X]) : K[X] :=
  ∑ i ∈ s, (C (U s c r P i) * lin c r i + C (V s c r P i)) * rest s c r i

@[simp] lemma eval_lin (c r : ι → K) (i : ι) (x : K) :
    (lin c r i).eval x = c i * (x - r i) := by simp [lin]

@[simp] lemma derivative_lin (c r : ι → K) (i : ι) :
    (lin c r i).derivative = C (c i) := by simp [lin]

lemma rest_eval_ne_zero {s : Finset ι} {c r : ι → K}
    (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s) {i : ι} (hi : i ∈ s) :
    (rest s c r i).eval (r i) ≠ 0 := by
  rw [rest, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  simp only [eval_pow, eval_lin]
  apply pow_ne_zero
  apply mul_ne_zero (hc k (Finset.mem_of_mem_erase hk))
  exact sub_ne_zero.mpr fun h ↦
    (Finset.ne_of_mem_erase hk).symm (hr hi (Finset.mem_of_mem_erase hk) h)

lemma rest_eval_eq_zero {s : Finset ι} {c r : ι → K}
    {i k : ι} (hi : i ∈ s) (hik : i ≠ k) :
    (rest s c r k).eval (r i) = 0 := by
  rw [rest, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik, hi⟩)
  simp

lemma root_sq_dvd_rest {s : Finset ι} {c r : ι → K}
    {i k : ι} (hi : i ∈ s) (hik : i ≠ k) :
    (X - C (r i)) ^ 2 ∣ rest s c r k := by
  apply dvd_trans (b := (lin c r i) ^ 2)
  · refine ⟨C (c i) ^ 2, ?_⟩
    simp [lin, DoublePartialFraction.lin]
    ring
  · exact Finset.dvd_prod_of_mem (fun j ↦ (lin c r j) ^ 2)
      (Finset.mem_erase.mpr ⟨hik, hi⟩)

lemma rest_derivative_eval_eq_zero {s : Finset ι} {c r : ι → K}
    {i k : ι} (hi : i ∈ s) (hik : i ≠ k) :
    (rest s c r k).derivative.eval (r i) = 0 :=
  eval_derivative_eq_zero_of_sq_dvd (root_sq_dvd_rest hi hik)

lemma numerator_eval {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s) {i : ι} (hi : i ∈ s) :
    (numerator s c r P).eval (r i) = P.eval (r i) := by
  rw [numerator, eval_finsetSum]
  simp_rw [eval_mul, eval_add, eval_C, eval_mul, eval_C, eval_lin]
  rw [Finset.sum_eq_single i]
  · simp [V, rest_eval_ne_zero hc hr hi]
  · intro k hk hki
    rw [rest_eval_eq_zero hi hki.symm, mul_zero]
  · exact fun h ↦ (h hi).elim

lemma numerator_derivative_eval {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s) {i : ι} (hi : i ∈ s) :
    (numerator s c r P).derivative.eval (r i) = P.derivative.eval (r i) := by
  rw [numerator, derivative_sum, eval_finsetSum]
  rw [Finset.sum_eq_single i]
  · simp only [derivative_mul, derivative_add, derivative_C, zero_mul, derivative_lin,
      zero_add, eval_add, eval_mul, eval_C, eval_lin]
    rw [U]
    field_simp [rest_eval_ne_zero hc hr hi, hc i hi]
    simp
    ring
  · intro k hk hki
    simp only [derivative_mul, derivative_add, derivative_C, zero_mul, derivative_lin,
      zero_add, eval_add, eval_mul, eval_C, eval_lin]
    rw [rest_eval_eq_zero hi hki.symm, rest_derivative_eval_eq_zero hi hki.symm]
    ring
  · exact fun h ↦ (h hi).elim

lemma root_den_dvd_sub_numerator {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s) :
    DoublePartialFraction.den s r ∣ P - numerator s c r P := by
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    apply IsCoprime.pow
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr fun h ↦ hij (hr hi hj h)).isUnit
  · intro i hi
    apply sq_dvd_of_eval_derivative_eq_zero
    · simp [numerator_eval hc hr hi]
    · simp [numerator_derivative_eval hc hr hi]

lemma natDegree_rest_le {s : Finset ι} {c r : ι → K}
    (hc : ∀ i ∈ s, c i ≠ 0) {i : ι} :
    (rest s c r i).natDegree ≤ 2 * (s.erase i).card := by
  calc
    _ ≤ ∑ k ∈ s.erase i, ((lin c r k) ^ 2).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ = ∑ _k ∈ s.erase i, 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Polynomial.natDegree_pow]
      have hck : c k ≠ 0 := hc k (Finset.mem_of_mem_erase hk)
      simp [lin, DoublePartialFraction.lin, Polynomial.natDegree_C_mul hck]
    _ = 2 * (s.erase i).card := by simp [Nat.mul_comm]

lemma natDegree_numerator_lt {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hc : ∀ i ∈ s, c i ≠ 0) :
    (numerator s c r P).natDegree < 2 * s.card := by
  have hterm : ∀ i ∈ s,
      ((C (U s c r P i) * lin c r i + C (V s c r P i)) * rest s c r i).natDegree ≤
        2 * s.card - 1 := by
    intro i hi
    have herase : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
    have hcard : 1 ≤ s.card := Finset.one_le_card.mpr ⟨i, hi⟩
    have hsline : (lin c r i).natDegree = 1 := by
      simp [lin, DoublePartialFraction.lin, Polynomial.natDegree_C_mul (hc i hi)]
    have hlin : (C (U s c r P i) * lin c r i + C (V s c r P i)).natDegree ≤ 1 := by
      have hmul : (C (U s c r P i) * lin c r i).natDegree ≤ 1 := by
        exact (Polynomial.natDegree_mul_le).trans (by simp [hsline])
      exact (Polynomial.natDegree_add_le _ _).trans (max_le hmul (by simp))
    calc
      _ ≤ (C (U s c r P i) * lin c r i + C (V s c r P i)).natDegree +
          (rest s c r i).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1 + 2 * (s.card - 1) := by
        exact Nat.add_le_add hlin ((natDegree_rest_le hc).trans_eq (by rw [herase]))
      _ ≤ 2 * s.card - 1 := by omega
  have hsum : (numerator s c r P).natDegree ≤ 2 * s.card - 1 :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ hterm
  exact hsum.trans_lt (Nat.sub_lt (by positivity) (by omega))

theorem polynomial_identity {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s)
    (hP : P.natDegree < 2 * s.card) :
    P = numerator s c r P := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_dvd_of_natDegree_lt (root_den_dvd_sub_numerator hc hr)
  rw [DoublePartialFraction.natDegree_den]
  exact (Polynomial.natDegree_sub_le _ _).trans_lt
    (max_lt hP (natDegree_numerator_lt hs hc))

lemma den_eq_mul_rest {s : Finset ι} {c r : ι → K} {i : ι} (hi : i ∈ s) :
    den s c r = (lin c r i) ^ 2 * rest s c r i := by
  rw [den, rest, Finset.mul_prod_erase s (fun k ↦ (lin c r k) ^ 2) hi]

lemma rest_eval_ne_zero_at {s : Finset ι} {c r : ι → K} {i : ι} {t : K}
    (hc : ∀ k ∈ s, c k ≠ 0) (ht : ∀ k ∈ s, t ≠ r k) :
    (rest s c r i).eval t ≠ 0 := by
  rw [rest, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  simp only [eval_pow, eval_lin]
  exact pow_ne_zero 2 (mul_ne_zero (hc k (Finset.mem_of_mem_erase hk))
    (sub_ne_zero.mpr (ht k (Finset.mem_of_mem_erase hk))))

theorem partial_fraction {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s)
    (hP : P.natDegree < 2 * s.card) (t : K)
    (ht : ∀ i ∈ s, t ≠ r i) :
    P.eval t / (den s c r).eval t =
      ∑ i ∈ s, (U s c r P i / (lin c r i).eval t + V s c r P i / ((lin c r i).eval t) ^ 2) := by
  calc
    P.eval t / (den s c r).eval t =
        (numerator s c r P).eval t / (den s c r).eval t := by
          exact congrArg (fun Q : K[X] ↦ Q.eval t / (den s c r).eval t)
            (polynomial_identity hs hc hr hP)
    _ = ∑ i ∈ s, (U s c r P i / (lin c r i).eval t +
          V s c r P i / ((lin c r i).eval t) ^ 2) := by
      rw [numerator, eval_finsetSum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rw [den_eq_mul_rest hi]
      simp only [eval_mul, eval_pow, eval_add, eval_C]
      field_simp [eval_lin, hc i hi, ht i hi, rest_eval_ne_zero_at hc ht]

end Scaled

namespace Scaled

lemma natDegree_rest_eq {s : Finset ι} {c r : ι → K}
    (hc : ∀ i ∈ s, c i ≠ 0) (i : ι) :
    (rest s c r i).natDegree = 2 * (s.erase i).card := by
  rw [rest, Polynomial.natDegree_prod]
  · calc
      ∑ j ∈ s.erase i, (lin c r j ^ 2).natDegree =
          ∑ _j ∈ s.erase i, 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Polynomial.natDegree_pow]
        have hcj : c j ≠ 0 := hc j (Finset.mem_of_mem_erase hj)
        simp [lin, DoublePartialFraction.lin, Polynomial.natDegree_C_mul hcj]
      _ = 2 * (s.erase i).card := by simp [Nat.mul_comm]
  · intro j hj
    apply pow_ne_zero
    apply mul_ne_zero
    · simp [hc j (Finset.mem_of_mem_erase hj)]
    · exact Polynomial.X_sub_C_ne_zero (r j)

lemma leadingCoeff_rest {s : Finset ι} {c r : ι → K}
    (hc : ∀ i ∈ s, c i ≠ 0) (i : ι) :
    (rest s c r i).leadingCoeff = ∏ j ∈ s.erase i, (c j) ^ 2 := by
  rw [rest, Polynomial.leadingCoeff_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.leadingCoeff_pow]
  have hcj : c j ≠ 0 := hc j (Finset.mem_of_mem_erase hj)
  simp [lin, DoublePartialFraction.lin, Polynomial.leadingCoeff_mul, hcj]

lemma coeff_affine_mul_rest_top {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hc : ∀ i ∈ s, c i ≠ 0) {i : ι} (hi : i ∈ s) :
    (((C (U s c r P i) * lin c r i + C (V s c r P i)) * rest s c r i).coeff
      (2 * s.card - 1)) =
      U s c r P i * c i * ∏ j ∈ s.erase i, (c j) ^ 2 := by
  have hcard : 1 ≤ s.card := Finset.one_le_card.mpr ⟨i, hi⟩
  have herase : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
  have hdeg : (rest s c r i).natDegree = 2 * (s.card - 1) := by
    rw [natDegree_rest_eq hc, herase]
  have htop : 2 * s.card - 1 = 1 + 2 * (s.card - 1) := by omega
  rw [htop, Polynomial.coeff_mul_add_eq_of_natDegree_le]
  · rw [← hdeg, Polynomial.coeff_natDegree, leadingCoeff_rest hc]
    simp [lin, DoublePartialFraction.lin]
  · have hlin : (lin c r i).natDegree = 1 := by
      simp [lin, DoublePartialFraction.lin, Polynomial.natDegree_C_mul (hc i hi)]
    have hmul : (C (U s c r P i) * lin c r i).natDegree ≤ 1 :=
      Polynomial.natDegree_mul_le.trans (by simp [hlin])
    exact (Polynomial.natDegree_add_le _ _).trans (max_le hmul (by simp))
  · exact hdeg.le

/-- In a scaled double-pole basis `c i * (X - r i)`, degree gap two forces
the weighted simple-pole cancellation `Σ U_i / c_i = 0`. -/
theorem sum_U_div_scale_eq_zero {s : Finset ι} {c r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hc : ∀ i ∈ s, c i ≠ 0) (hr : Set.InjOn r s)
    (hP : P.natDegree < 2 * s.card - 1) :
    ∑ i ∈ s, U s c r P i / c i = 0 := by
  have hP' : P.natDegree < 2 * s.card := hP.trans_le (Nat.sub_le _ _)
  have hid := polynomial_identity hs hc hr hP'
  have hcoeff := congrArg (fun Q : K[X] ↦ Q.coeff (2 * s.card - 1)) hid
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hP] at hcoeff
  change 0 = (∑ i ∈ s,
    (C (U s c r P i) * lin c r i + C (V s c r P i)) * rest s c r i).coeff
      (2 * s.card - 1) at hcoeff
  rw [finsetSum_coeff] at hcoeff
  have hweighted :
      ∑ i ∈ s, U s c r P i * c i * ∏ j ∈ s.erase i, (c j) ^ 2 = 0 := by
    calc
      _ = ∑ i ∈ s,
          ((C (U s c r P i) * lin c r i + C (V s c r P i)) * rest s c r i).coeff
            (2 * s.card - 1) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [coeff_affine_mul_rest_top hc hi]
      _ = 0 := hcoeff.symm
  let Ctot : K := ∏ i ∈ s, (c i) ^ 2
  have hCtot : Ctot ≠ 0 := by
    dsimp [Ctot]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero 2 (hc i hi)
  apply mul_left_cancel₀ hCtot
  rw [mul_zero, Finset.mul_sum]
  calc
    ∑ i ∈ s, Ctot * (U s c r P i / c i) =
        ∑ i ∈ s, U s c r P i * c i * ∏ j ∈ s.erase i, (c j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show Ctot = c i ^ 2 * ∏ j ∈ s.erase i, (c j) ^ 2 by
        exact (Finset.mul_prod_erase s (fun j ↦ c j ^ 2) hi).symm]
      field_simp [hc i hi]
    _ = 0 := hweighted

end Scaled

lemma rest_monic (s : Finset ι) (r : ι → K) (i : ι) :
    (rest s r i).Monic := by
  rw [rest]
  exact monic_prod_of_monic _ _ fun j _ ↦ (monic_X_sub_C (r j)).pow 2

lemma coeff_affine_mul_rest_top {s : Finset ι} {r : ι → K} {P : K[X]}
    {i : ι} (hi : i ∈ s) :
    (((C (A s r P i) * lin r i + C (B s r P i)) * rest s r i).coeff
      (2 * s.card - 1)) = A s r P i := by
  have hcard : 1 ≤ s.card := Finset.one_le_card.mpr ⟨i, hi⟩
  have herase : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
  have hdeg : (rest s r i).natDegree = 2 * (s.card - 1) := by
    rw [natDegree_rest, herase]
  have htop : 2 * s.card - 1 = 1 + 2 * (s.card - 1) := by omega
  rw [htop, coeff_mul_add_eq_of_natDegree_le]
  · rw [← hdeg, coeff_natDegree, (rest_monic s r i).leadingCoeff]
    simp [lin]
  · have hmul : (C (A s r P i) * lin r i).natDegree ≤ 1 :=
      (natDegree_mul_le).trans (by simp [lin])
    exact (natDegree_add_le _ _).trans (max_le hmul (by simp))
  · exact hdeg.le

/-- The sum of the simple-pole coefficients vanishes when the rational
function has a gap of at least two between denominator and numerator degree. -/
theorem sum_A_eq_zero {s : Finset ι} {r : ι → K} {P : K[X]}
    (hs : s.Nonempty) (hr : Set.InjOn r s)
    (hP : P.natDegree < 2 * s.card - 1) :
    ∑ i ∈ s, A s r P i = 0 := by
  have hP' : P.natDegree < 2 * s.card := hP.trans_le (Nat.sub_le _ _)
  have hid := polynomial_identity hs hr hP'
  have hcoeff := congrArg (fun Q : K[X] ↦ Q.coeff (2 * s.card - 1)) hid
  rw [coeff_eq_zero_of_natDegree_lt hP] at hcoeff
  change 0 = (∑ i ∈ s,
    (C (A s r P i) * lin r i + C (B s r P i)) * rest s r i).coeff
      (2 * s.card - 1) at hcoeff
  rw [finsetSum_coeff] at hcoeff
  calc
    ∑ i ∈ s, A s r P i = ∑ i ∈ s,
        ((C (A s r P i) * lin r i + C (B s r P i)) * rest s r i).coeff
          (2 * s.card - 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [coeff_affine_mul_rest_top hi]
    _ = 0 := hcoeff.symm

namespace OldRational

def root (j : ℕ) : ℚ := (2 : ℚ) ^ (j + 1)

def scale (j : ℕ) : ℚ := -(root j)⁻¹

def numeratorFactor (n j : ℕ) : ℚ[X] :=
  1 - C ((2 : ℚ) ^ (n - 1 - j)) * X

def P (n : ℕ) : ℚ[X] :=
  X ^ n * ∏ j ∈ Finset.range n, numeratorFactor n j

def poleFactor (j : ℕ) : ℚ[X] := Scaled.lin scale root j

def D (n : ℕ) : ℚ[X] := Scaled.den (Finset.range (n + 1)) scale root

def G (n j : ℕ) : ℚ[X] := Scaled.rest (Finset.range (n + 1)) scale root j

/-- The coefficient of the double pole `j`. -/
def vCoeff (n j : ℕ) : ℚ :=
  Scaled.V (Finset.range (n + 1)) scale root (P n) j

/-- The coefficient of the simple pole `j`.  Since `scale j = -1 / root j`,
this is `-root j` times the derivative at `root j` of `(poleFactor j)^2 R`. -/
def uCoeff (n j : ℕ) : ℚ :=
  Scaled.U (Finset.range (n + 1)) scale root (P n) j

def R (n : ℕ) (T : ℚ) : ℚ := (P n).eval T / (D n).eval T

lemma root_ne_zero (j : ℕ) : root j ≠ 0 := by
  norm_num [root]

lemma scale_ne_zero (j : ℕ) : scale j ≠ 0 := by
  simp [scale, root_ne_zero]

lemma root_injective : Function.Injective root := by
  intro i j h
  have he : i + 1 = j + 1 :=
    (pow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num : (2 : ℚ) ≠ 1)) h
  omega

lemma root_injOn (n : ℕ) : Set.InjOn root (Finset.range (n + 1)) :=
  root_injective.injOn

lemma scale_mul_root (j : ℕ) : scale j * root j = -1 := by
  rw [scale]
  field_simp [root_ne_zero]

lemma poleFactor_eval (j : ℕ) (T : ℚ) :
    (poleFactor j).eval T = 1 - T / root j := by
  rw [poleFactor, Scaled.eval_lin]
  rw [scale]
  field_simp [root_ne_zero]
  ring

lemma P_eval (n : ℕ) (T : ℚ) :
    (P n).eval T = T ^ n *
      ∏ j ∈ Finset.range n, (1 - (2 : ℚ) ^ (n - 1 - j) * T) := by
  rw [P, eval_mul, eval_pow, eval_X, eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [numeratorFactor]

lemma D_eval (n : ℕ) (T : ℚ) :
    (D n).eval T = ∏ j ∈ Finset.range (n + 1), (1 - T / root j) ^ 2 := by
  rw [D, Scaled.den, eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [eval_pow]
  change (poleFactor j).eval T ^ 2 = _
  rw [poleFactor_eval]

lemma R_eq_products (n : ℕ) (T : ℚ) :
    R n T = T ^ n *
      (∏ j ∈ Finset.range n, (1 - (2 : ℚ) ^ (n - 1 - j) * T)) *
      (∏ j ∈ Finset.range (n + 1), (1 - T / (2 : ℚ) ^ (j + 1))⁻¹ ^ 2) := by
  rw [R, P_eval, D_eval]
  simp only [root]
  rw [div_eq_mul_inv, ← Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [inv_pow]

lemma natDegree_numeratorFactor_le (n j : ℕ) :
    (numeratorFactor n j).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by simp)

lemma natDegree_P_lt (n : ℕ) :
    (P n).natDegree < 2 * (Finset.range (n + 1)).card := by
  have hprod : (∏ j ∈ Finset.range n, numeratorFactor n j).natDegree ≤ n := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, (numeratorFactor n j).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _j ∈ Finset.range n, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        exact natDegree_numeratorFactor_le n j
      _ = n := by simp
  rw [P]
  refine Polynomial.natDegree_mul_le.trans_lt ?_
  simp only [Polynomial.natDegree_pow, natDegree_X, one_mul]
  simp only [Finset.card_range]
  omega

lemma natDegree_P_lt_gap (n : ℕ) :
    (P n).natDegree < 2 * (Finset.range (n + 1)).card - 1 := by
  have hprod : (∏ j ∈ Finset.range n, numeratorFactor n j).natDegree ≤ n := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, (numeratorFactor n j).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _j ∈ Finset.range n, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        exact natDegree_numeratorFactor_le n j
      _ = n := by simp
  rw [P]
  refine Polynomial.natDegree_mul_le.trans_lt ?_
  simp only [Polynomial.natDegree_pow, natDegree_X, one_mul, Finset.card_range]
  omega

/-- Degree gap at infinity cancels the simple-pole part. -/
theorem sum_root_mul_uCoeff_eq_zero (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), root j * uCoeff n j = 0 := by
  have h := Scaled.sum_U_div_scale_eq_zero
    (K := ℚ) (s := Finset.range (n + 1)) (c := scale) (r := root) (P := P n)
    (by simp) (fun j _hj ↦ scale_ne_zero j) (root_injOn n) (natDegree_P_lt_gap n)
  change ∑ j ∈ Finset.range (n + 1), uCoeff n j / scale j = 0 at h
  have hneg := congrArg Neg.neg h
  simpa [scale, root_ne_zero, div_eq_mul_inv, mul_comm] using hneg

lemma G_eval_ne_zero {n j : ℕ} (hj : j < n + 1) :
    (G n j).eval (root j) ≠ 0 := by
  exact Scaled.rest_eval_ne_zero
    (fun k _hk ↦ scale_ne_zero k) (root_injOn n) (Finset.mem_range.mpr hj)

lemma vCoeff_eq_eval (n j : ℕ) :
    vCoeff n j = (P n).eval (root j) / (G n j).eval (root j) := rfl

lemma G_eval_products (n k : ℕ) :
    (G n k).eval (root k) =
      ∏ j ∈ (Finset.range (n + 1)).erase k,
        (1 - root k / root j) ^ 2 := by
  rw [G, Scaled.rest, eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [eval_pow]
  change (poleFactor j).eval (root k) ^ 2 = _
  rw [poleFactor_eval]

lemma vCoeff_eq_products (n k : ℕ) :
    vCoeff n k =
      ((root k) ^ n *
        ∏ i ∈ Finset.range n,
          (1 - (2 : ℚ) ^ (n - 1 - i) * root k)) /
        (∏ j ∈ (Finset.range (n + 1)).erase k,
          (1 - root k / root j) ^ 2) := by
  rw [vCoeff_eq_eval, P_eval, G_eval_products]

lemma P_eval_root_ne_zero {n k : ℕ} : (P n).eval (root k) ≠ 0 := by
  rw [P_eval]
  apply mul_ne_zero (pow_ne_zero _ (root_ne_zero k))
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  rw [root, ← pow_add]
  have he : 0 < (n - 1 - i) + (k + 1) := by omega
  exact sub_ne_zero.mpr (ne_of_lt (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) he.ne'))

/-- The logarithmic derivative which appears in the simple-pole coefficient. -/
def rawLogDeriv (n k : ℕ) : ℚ :=
  root k * ((P n).derivative.eval (root k) / (P n).eval (root k) -
    (G n k).derivative.eval (root k) / (G n k).eval (root k))

lemma eval_derivative_mul_div (A B : ℚ[X]) (x : ℚ)
    (hA : A.eval x ≠ 0) (hB : B.eval x ≠ 0) :
    (A * B).derivative.eval x / (A * B).eval x =
      A.derivative.eval x / A.eval x + B.derivative.eval x / B.eval x := by
  simp only [derivative_mul, eval_add, eval_mul]
  field_simp

lemma eval_derivative_prod_div {s : Finset ℕ} (f : ℕ → ℚ[X]) (x : ℚ)
    (hf : ∀ i ∈ s, (f i).eval x ≠ 0) :
    (∏ i ∈ s, f i).derivative.eval x / (∏ i ∈ s, f i).eval x =
      ∑ i ∈ s, (f i).derivative.eval x / (f i).eval x := by
  rw [derivative_prod_finset, eval_finsetSum, eval_prod, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [eval_mul, eval_prod]
  rw [← Finset.mul_prod_erase s (fun j ↦ (f j).eval x) hi]
  have hrest : ∏ j ∈ s.erase i, (f j).eval x ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact hf j (Finset.mem_of_mem_erase hj)
  field_simp [hf i hi, hrest]

lemma numeratorFactor_eval_root_ne_zero {n k i : ℕ} (hi : i < n) :
    (numeratorFactor n i).eval (root k) ≠ 0 := by
  simp only [numeratorFactor, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  rw [root, ← pow_add]
  have he : 0 < (n - 1 - i) + (k + 1) := by omega
  exact sub_ne_zero.mpr (ne_of_lt (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) he.ne'))

lemma logDeriv_P (n k : ℕ) :
    (P n).derivative.eval (root k) / (P n).eval (root k) =
      (n : ℚ) / root k +
        ∑ i ∈ Finset.range n,
          (-(2 : ℚ) ^ (n - 1 - i)) /
            (1 - (2 : ℚ) ^ (n - 1 - i) * root k) := by
  rw [P, eval_derivative_mul_div]
  · congr 1
    · by_cases hn : n = 0
      · simp [hn]
      · simp only [derivative_pow, derivative_X, eval_mul, eval_C, eval_pow, eval_X,
          eval_one, mul_one]
        field_simp [root_ne_zero]
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
    · rw [eval_derivative_prod_div (fun i ↦ numeratorFactor n i) (root k)
          (fun i hi ↦ numeratorFactor_eval_root_ne_zero (Finset.mem_range.mp hi))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [numeratorFactor]
      simp [derivative_mul, derivative_pow]
  · simpa using pow_ne_zero n (root_ne_zero k)
  · rw [eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i hi ↦
      numeratorFactor_eval_root_ne_zero (Finset.mem_range.mp hi)

lemma poleFactor_eval_root_ne_zero {n k j : ℕ}
    (hj : j ∈ (Finset.range (n + 1)).erase k) :
    (poleFactor j).eval (root k) ≠ 0 := by
  rw [poleFactor_eval]
  apply sub_ne_zero.mpr
  intro h
  have hroot : root k = root j := by
    apply (div_eq_one_iff_eq (root_ne_zero j)).mp
    linarith
  exact (Finset.ne_of_mem_erase hj).symm (root_injective hroot)

lemma logDeriv_G (n k : ℕ) :
    (G n k).derivative.eval (root k) / (G n k).eval (root k) =
      ∑ j ∈ (Finset.range (n + 1)).erase k,
        (2 * scale j) / (1 - root k / root j) := by
  rw [G, Scaled.rest,
    eval_derivative_prod_div (fun j ↦ Scaled.lin scale root j ^ 2) (root k)
      (fun j hj ↦ by
        rw [eval_pow]
        change (poleFactor j).eval (root k) ^ 2 ≠ 0
        exact pow_ne_zero 2 (poleFactor_eval_root_ne_zero hj))]
  apply Finset.sum_congr rfl
  intro j hj
  change (poleFactor j ^ 2).derivative.eval (root k) /
      (poleFactor j ^ 2).eval (root k) = _
  rw [eval_pow, poleFactor_eval]
  simp only [derivative_pow, Nat.cast_ofNat, eval_mul, eval_C, eval_natCast,
    eval_one]
  have hpderiv : (poleFactor j).derivative = C (scale j) := by
    exact Scaled.derivative_lin scale root j
  rw [hpderiv, eval_C]
  norm_num [poleFactor_eval]
  change (2 * (1 - root k / root j) * scale j) /
      (1 - root k / root j) ^ 2 = _
  field_simp [poleFactor_eval_root_ne_zero hj]

lemma rawLogDeriv_eq_index_sums (n k : ℕ) :
    rawLogDeriv n k =
      root k * ((n : ℚ) / root k +
        ∑ i ∈ Finset.range n,
          (-(2 : ℚ) ^ (n - 1 - i)) /
            (1 - (2 : ℚ) ^ (n - 1 - i) * root k) -
        ∑ j ∈ (Finset.range (n + 1)).erase k,
          (2 * scale j) / (1 - root k / root j)) := by
  rw [rawLogDeriv, logDeriv_P, logDeriv_G]

def oddFactorQ (d : ℕ) : ℚ := (2 : ℚ) ^ d - 1

lemma oddFactorQ_ne_zero {d : ℕ} (hd : 1 ≤ d) : oddFactorQ d ≠ 0 := by
  exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) (by omega)))

lemma numerator_log_term (n k i : ℕ) (hi : i < n) :
    root k * ((-(2 : ℚ) ^ (n - 1 - i)) /
      (1 - (2 : ℚ) ^ (n - 1 - i) * root k)) =
      (2 : ℚ) ^ (n + k - i) / oddFactorQ (n + k - i) := by
  have he : (n - 1 - i) + (k + 1) = n + k - i := by omega
  have hd : 1 ≤ n + k - i := by omega
  have hmul : root k * (2 : ℚ) ^ (n - 1 - i) = (2 : ℚ) ^ (n + k - i) := by
    rw [root, ← pow_add]
    congr 1
    omega
  have hone : 1 - (2 : ℚ) ^ (n + k - i) ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_lt (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) (by omega)))
  have hodd : -1 + (2 : ℚ) ^ (n + k - i) ≠ 0 := by
    intro h
    apply hone
    linarith
  calc
    root k * ((-(2 : ℚ) ^ (n - 1 - i)) /
        (1 - (2 : ℚ) ^ (n - 1 - i) * root k)) =
        (root k * (-(2 : ℚ) ^ (n - 1 - i))) /
          (1 - (2 : ℚ) ^ (n - 1 - i) * root k) := by ring
    _ = (-(2 : ℚ) ^ (n + k - i)) / (1 - (2 : ℚ) ^ (n + k - i)) := by
      rw [mul_neg, hmul]
      rw [show (2 : ℚ) ^ (n - 1 - i) * root k = (2 : ℚ) ^ (n + k - i) by
        rw [mul_comm, hmul]]
    _ = (2 : ℚ) ^ (n + k - i) / oddFactorQ (n + k - i) := by
      simp only [oddFactorQ]
      rw [show 1 - (2 : ℚ) ^ (n + k - i) =
        -((2 : ℚ) ^ (n + k - i) - 1) by ring]
      rw [neg_div_neg_eq]

lemma lower_pole_log_term (k j : ℕ) (hj : j < k) :
    root k * ((2 * scale j) / (1 - root k / root j)) =
      2 * (2 : ℚ) ^ (k - j) / oddFactorQ (k - j) := by
  have hd : 1 ≤ k - j := by omega
  have he : (j + 1) + (k - j) = k + 1 := by omega
  have hroot : root k = root j * (2 : ℚ) ^ (k - j) := by
    simp only [root, ← pow_add, he]
  have hratio : root k / root j = (2 : ℚ) ^ (k - j) := by
    rw [hroot]
    field_simp [root_ne_zero j]
  have hscale : root k * (2 * scale j) = -2 * (2 : ℚ) ^ (k - j) := by
    rw [scale, hroot]
    field_simp [root_ne_zero j]
  have hone : 1 - (2 : ℚ) ^ (k - j) ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_lt (one_lt_pow₀ (by norm_num : (1 : ℚ) < 2) (by omega)))
  have hodd : -1 + (2 : ℚ) ^ (k - j) ≠ 0 := by
    intro h
    apply hone
    linarith
  calc
    root k * ((2 * scale j) / (1 - root k / root j)) =
        (root k * (2 * scale j)) / (1 - root k / root j) := by ring
    _ = (-2 * (2 : ℚ) ^ (k - j)) / (1 - (2 : ℚ) ^ (k - j)) := by
      rw [hscale, hratio]
    _ = 2 * (2 : ℚ) ^ (k - j) / oddFactorQ (k - j) := by
      simp only [oddFactorQ]
      rw [show -2 * (2 : ℚ) ^ (k - j) =
        -(2 * (2 : ℚ) ^ (k - j)) by ring]
      rw [show 1 - (2 : ℚ) ^ (k - j) =
        -((2 : ℚ) ^ (k - j) - 1) by ring]
      rw [neg_div_neg_eq]

lemma upper_pole_log_term (k j : ℕ) (hj : k < j) :
    root k * ((2 * scale j) / (1 - root k / root j)) =
      -2 / oddFactorQ (j - k) := by
  have hd : 1 ≤ j - k := by omega
  have he : (k + 1) + (j - k) = j + 1 := by omega
  have hroot : root j = root k * (2 : ℚ) ^ (j - k) := by
    simp only [root, ← pow_add, he]
  have hratio : root k / root j = 1 / (2 : ℚ) ^ (j - k) := by
    rw [hroot]
    field_simp [root_ne_zero k]
  have hscale : root k * (2 * scale j) = -2 / (2 : ℚ) ^ (j - k) := by
    rw [scale, hroot]
    field_simp [root_ne_zero k]
  have hone : (2 : ℚ) ^ (j - k) - 1 ≠ 0 := oddFactorQ_ne_zero hd
  calc
    root k * ((2 * scale j) / (1 - root k / root j)) =
        (root k * (2 * scale j)) / (1 - root k / root j) := by ring
    _ = (-2 / (2 : ℚ) ^ (j - k)) /
        (1 - 1 / (2 : ℚ) ^ (j - k)) := by rw [hscale, hratio]
    _ = -2 / oddFactorQ (j - k) := by
      simp only [oddFactorQ]
      field_simp [hone] <;> ring

lemma sum_range_reverse (n k : ℕ) (F : ℕ → ℚ) :
    ∑ i ∈ Finset.range n, F (n + k - i) =
      ∑ d ∈ Finset.Icc (k + 1) (n + k), F d := by
  apply Finset.sum_bij (fun i _hi ↦ n + k - i)
  · intro i hi
    simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    simp only [Finset.mem_range] at hi₁ hi₂
    omega
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    refine ⟨n + k - d, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro i hi
    rfl

lemma sum_range_reverse_from_one (k : ℕ) (F : ℕ → ℚ) :
    ∑ j ∈ Finset.range k, F (k - j) =
      ∑ d ∈ Finset.Icc 1 k, F d := by
  simpa using sum_range_reverse k 0 F

lemma sum_Icc_sub (n k : ℕ) (hkn : k ≤ n) (F : ℕ → ℚ) :
    ∑ j ∈ Finset.Icc (k + 1) n, F (j - k) =
      ∑ d ∈ Finset.Icc 1 (n - k), F d := by
  apply Finset.sum_bij (fun j _hj ↦ j - k)
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [Finset.mem_Icc] at hj₁ hj₂
    omega
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    refine ⟨d + k, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro j hj
    rfl

def targetLogDeriv (n k : ℕ) : ℚ :=
  n +
    ∑ d ∈ Finset.Icc (k + 1) (n + k),
      (2 : ℚ) ^ d / oddFactorQ d -
    2 * ∑ d ∈ Finset.Icc 1 k,
      (2 : ℚ) ^ d / oddFactorQ d +
    2 * ∑ d ∈ Finset.Icc 1 (n - k),
      (1 : ℚ) / oddFactorQ d

theorem rawLogDeriv_eq_targetLogDeriv (n k : ℕ) (hkn : k ≤ n) :
    rawLogDeriv n k = targetLogDeriv n k := by
  let high : ℕ → ℚ := fun d ↦ (2 : ℚ) ^ d / oddFactorQ d
  let low : ℕ → ℚ := fun d ↦ (1 : ℚ) / oddFactorQ d
  have hnterm : root k * ((n : ℚ) / root k) = n := by
    field_simp [root_ne_zero]
  have hPsum :
      root k * (∑ i ∈ Finset.range n,
        (-(2 : ℚ) ^ (n - 1 - i)) /
          (1 - (2 : ℚ) ^ (n - 1 - i) * root k)) =
        ∑ d ∈ Finset.Icc (k + 1) (n + k), high d := by
    calc
      _ = ∑ i ∈ Finset.range n,
          root k * ((-(2 : ℚ) ^ (n - 1 - i)) /
            (1 - (2 : ℚ) ^ (n - 1 - i) * root k)) := by
              rw [Finset.mul_sum]
      _ = ∑ i ∈ Finset.range n, high (n + k - i) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact numerator_log_term n k i (Finset.mem_range.mp hi)
      _ = ∑ d ∈ Finset.Icc (k + 1) (n + k), high d :=
              sum_range_reverse n k high
  have herase : (Finset.range (n + 1)).erase k =
      Finset.range k ∪ Finset.Icc (k + 1) n := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdis : Disjoint (Finset.range k) (Finset.Icc (k + 1) n) := by
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    simp only [Finset.mem_range] at hj₁
    simp only [Finset.mem_Icc] at hj₂
    omega
  have hpoles :
      root k * (∑ j ∈ (Finset.range (n + 1)).erase k,
        (2 * scale j) / (1 - root k / root j)) =
        2 * (∑ d ∈ Finset.Icc 1 k, high d) -
        2 * (∑ d ∈ Finset.Icc 1 (n - k), low d) := by
    calc
      _ = root k * ((∑ j ∈ Finset.range k,
            (2 * scale j) / (1 - root k / root j)) +
          (∑ j ∈ Finset.Icc (k + 1) n,
            (2 * scale j) / (1 - root k / root j))) := by
              rw [herase, Finset.sum_union hdis]
      _ = (∑ j ∈ Finset.range k,
            root k * ((2 * scale j) / (1 - root k / root j))) +
          (∑ j ∈ Finset.Icc (k + 1) n,
            root k * ((2 * scale j) / (1 - root k / root j))) := by
              rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      _ = (∑ j ∈ Finset.range k, 2 * high (k - j)) +
          (∑ j ∈ Finset.Icc (k + 1) n, -2 * low (j - k)) := by
              apply congrArg₂ (.+.)
              · apply Finset.sum_congr rfl
                intro j hj
                simpa [high, mul_div_assoc] using
                  lower_pole_log_term k j (Finset.mem_range.mp hj)
              · apply Finset.sum_congr rfl
                intro j hj
                have hj' : k < j := by
                  exact Nat.lt_of_succ_le (Finset.mem_Icc.mp hj).1
                simpa [low, div_eq_mul_inv] using upper_pole_log_term k j hj'
      _ = (∑ d ∈ Finset.Icc 1 k, 2 * high d) +
          (∑ d ∈ Finset.Icc 1 (n - k), -2 * low d) := by
              rw [sum_range_reverse_from_one k (fun d ↦ 2 * high d)]
              rw [sum_Icc_sub n k hkn (fun d ↦ -2 * low d)]
      _ = 2 * (∑ d ∈ Finset.Icc 1 k, high d) -
          2 * (∑ d ∈ Finset.Icc 1 (n - k), low d) := by
              rw [Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg]
              congr 1
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro d hd
              ring
  calc
    rawLogDeriv n k = root k * ((n : ℚ) / root k +
        ∑ i ∈ Finset.range n,
          (-(2 : ℚ) ^ (n - 1 - i)) /
            (1 - (2 : ℚ) ^ (n - 1 - i) * root k) -
        ∑ j ∈ (Finset.range (n + 1)).erase k,
          (2 * scale j) / (1 - root k / root j)) := rawLogDeriv_eq_index_sums n k
    _ = root k * ((n : ℚ) / root k) +
        root k * (∑ i ∈ Finset.range n,
          (-(2 : ℚ) ^ (n - 1 - i)) /
            (1 - (2 : ℚ) ^ (n - 1 - i) * root k)) -
        root k * (∑ j ∈ (Finset.range (n + 1)).erase k,
          (2 * scale j) / (1 - root k / root j)) := by ring
    _ = (n : ℚ) +
        (∑ d ∈ Finset.Icc (k + 1) (n + k), high d) -
        (2 * (∑ d ∈ Finset.Icc 1 k, high d) -
          2 * (∑ d ∈ Finset.Icc 1 (n - k), low d)) := by
            rw [hnterm, hPsum, hpoles]
    _ = targetLogDeriv n k := by
      simp only [targetLogDeriv, high, low]
      ring

lemma uCoeff_eq_eval_derivative (n j : ℕ) :
    uCoeff n j = -root j *
      ((P n).derivative.eval (root j) -
        vCoeff n j * (G n j).derivative.eval (root j)) /
        (G n j).eval (root j) := by
  rw [uCoeff, Scaled.U, vCoeff, G]
  rw [scale]
  field_simp [root_ne_zero]

lemma uCoeff_eq_neg_vCoeff_mul_rawLogDeriv {n k : ℕ} (hk : k < n + 1) :
    uCoeff n k = -vCoeff n k * rawLogDeriv n k := by
  rw [uCoeff_eq_eval_derivative, rawLogDeriv, vCoeff_eq_eval]
  field_simp [P_eval_root_ne_zero (n := n) (k := k), G_eval_ne_zero hk]

theorem partial_fraction (n : ℕ) (T : ℚ)
    (hT : ∀ j < n + 1, T ≠ root j) :
    R n T = ∑ j ∈ Finset.range (n + 1),
      (uCoeff n j / (1 - T / root j) + vCoeff n j / (1 - T / root j) ^ 2) := by
  rw [R]
  have h := Scaled.partial_fraction (K := ℚ)
      (s := Finset.range (n + 1)) (c := scale) (r := root) (P := P n)
      (by simp) (fun j _hj ↦ scale_ne_zero j) (root_injOn n) (natDegree_P_lt n) T
      (fun j hj ↦ hT j (Finset.mem_range.mp hj))
  change (P n).eval T /
      (Scaled.den (Finset.range (n + 1)) scale root).eval T = _
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  change Scaled.U (Finset.range (n + 1)) scale root (P n) j /
      (poleFactor j).eval T +
      Scaled.V (Finset.range (n + 1)) scale root (P n) j /
        ((poleFactor j).eval T) ^ 2 = _
  rw [poleFactor_eval]
  rfl

/-- The same rational function with real coefficients, in exactly the product form
used by the analytic q-Apéry development. -/
def Rreal (n : ℕ) (T : ℝ) : ℝ :=
  T ^ n *
    (∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * T)) *
    (∏ j ∈ Finset.range (n + 1), (1 - T / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2)

lemma cast_root (j : ℕ) : ((root j : ℚ) : ℝ) = (2 : ℝ) ^ (j + 1) := by
  simp [root]

lemma cast_R (n : ℕ) (T : ℚ) : ((R n T : ℚ) : ℝ) = Rreal n (T : ℝ) := by
  rw [R_eq_products, Rreal]
  push_cast
  norm_num

theorem partial_fraction_real (n : ℕ) (T : ℚ)
    (hT : ∀ j < n + 1, T ≠ root j) :
    Rreal n (T : ℝ) = ∑ j ∈ Finset.range (n + 1),
      (((uCoeff n j : ℚ) : ℝ) / (1 - (T : ℝ) / (2 : ℝ) ^ (j + 1)) +
        ((vCoeff n j : ℚ) : ℝ) / (1 - (T : ℝ) / (2 : ℝ) ^ (j + 1)) ^ 2) := by
  rw [← cast_R]
  rw [partial_fraction n T hT]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [cast_root]

end OldRational

end DoublePartialFraction

end
end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250/Erdos250ZPF.lean` -/

section
open Filter
open scoped BigOperators Topology

namespace ZPF

noncomputable def q : ℝ := 1 / 2

noncomputable def lambert1 : ℝ :=
  ∑' m : ℕ, q ^ (m + 1) / (1 - q ^ (m + 1))

noncomputable def lambert2 : ℝ :=
  ∑' m : ℕ, q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2

noncomputable def eta (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range j, q ^ (m + 1) / (1 - q ^ (m + 1))

noncomputable def theta (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range j, q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2

lemma q_norm_lt_one : ‖q‖ < 1 := by norm_num [q]

lemma summable_lambert1 :
    Summable (fun m : ℕ ↦ q ^ (m + 1) / (1 - q ^ (m + 1))) := by
  have h := summable_norm_pow_mul_geometric_div_one_sub (k := 0) q_norm_lt_one
  simp only [pow_zero, one_mul] at h
  exact (summable_nat_add_iff 1).2 h

lemma summable_lambert2 :
    Summable (fun m : ℕ ↦ q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2) := by
  rw [← summable_pnat_iff_summable_succ
    (f := fun m : ℕ ↦ q ^ m / (1 - q ^ m) ^ 2)]
  apply (summable_prod_mul_pow (k := 1) q_norm_lt_one).prod.congr
  intro d
  have hqd : ‖q ^ (d : ℕ)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) q_norm_lt_one d.ne_zero
  have hg := hasSum_coe_mul_geometric_of_norm_lt_one (r := q ^ (d : ℕ)) hqd
  calc
    (∑' c : ℕ+, (c : ℝ) ^ 1 * q ^ ((d : ℕ) * (c : ℕ))) =
        ∑' c : ℕ+, (c : ℝ) * (q ^ (d : ℕ)) ^ (c : ℕ) := by
      apply tsum_congr
      intro c
      simp [pow_mul]
    _ = ∑' c : ℕ, (c : ℝ) * (q ^ (d : ℕ)) ^ c := by
      simpa using tsum_zero_pnat_eq_tsum_nat hg.summable
    _ = q ^ (d : ℕ) / (1 - q ^ (d : ℕ)) ^ 2 := hg.tsum_eq

lemma shifted_lambert1_term (j l : ℕ) :
    q ^ l / (1 - q ^ (j + 1 + l)) =
      q ^ (-(j + 1 : ℤ)) *
        (q ^ (l + j + 1) / (1 - q ^ (l + j + 1))) := by
  rw [zpow_neg]
  rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by omega, zpow_natCast]
  have he : j + 1 + l = l + j + 1 := by omega
  rw [he]
  have hp : q ^ (l + j + 1) = q ^ l * q ^ (j + 1) := by
    simpa [Nat.add_assoc] using pow_add q l (j + 1)
  rw [hp]
  field_simp [q]

lemma shifted_lambert2_term (j l : ℕ) :
    q ^ l / (1 - q ^ (j + 1 + l)) ^ 2 =
      q ^ (-(j + 1 : ℤ)) *
        (q ^ (l + j + 1) / (1 - q ^ (l + j + 1)) ^ 2) := by
  rw [zpow_neg]
  rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by omega, zpow_natCast]
  have he : j + 1 + l = l + j + 1 := by omega
  rw [he]
  have hp : q ^ (l + j + 1) = q ^ l * q ^ (j + 1) := by
    simpa [Nat.add_assoc] using pow_add q l (j + 1)
  rw [hp]
  field_simp [q]

lemma summable_shifted_lambert1 (j : ℕ) :
    Summable (fun l : ℕ ↦ q ^ l / (1 - q ^ (j + 1 + l))) := by
  have hf : Summable (fun l : ℕ ↦
      q ^ (l + j + 1) / (1 - q ^ (l + j + 1))) := by
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff j).2 summable_lambert1
  exact (hf.mul_left (q ^ (-(j + 1 : ℤ)))).congr
    (fun l ↦ (shifted_lambert1_term j l).symm)

lemma summable_shifted_lambert2 (j : ℕ) :
    Summable (fun l : ℕ ↦ q ^ l / (1 - q ^ (j + 1 + l)) ^ 2) := by
  have hf : Summable (fun l : ℕ ↦
      q ^ (l + j + 1) / (1 - q ^ (l + j + 1)) ^ 2) := by
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff j).2 summable_lambert2
  exact (hf.mul_left (q ^ (-(j + 1 : ℤ)))).congr
    (fun l ↦ (shifted_lambert2_term j l).symm)

lemma shifted_lambert1 (j : ℕ) :
    ∑' l : ℕ, q ^ l / (1 - q ^ (j + 1 + l)) =
      q ^ (-(j + 1 : ℤ)) * (lambert1 - eta j) := by
  let f : ℕ → ℝ := fun m ↦ q ^ (m + 1) / (1 - q ^ (m + 1))
  have hf : Summable f := summable_lambert1
  have htail : ∑' l : ℕ, f (l + j) = lambert1 - eta j := by
    rw [eq_sub_iff_add_eq]
    simpa [f, lambert1, eta, add_comm] using hf.sum_add_tsum_nat_add j
  calc
    ∑' l : ℕ, q ^ l / (1 - q ^ (j + 1 + l)) =
        ∑' l : ℕ, q ^ (-(j + 1 : ℤ)) * f (l + j) := by
          apply tsum_congr
          intro l
          simp only [f]
          exact shifted_lambert1_term j l
    _ = q ^ (-(j + 1 : ℤ)) * ∑' l : ℕ, f (l + j) := by
      rw [tsum_mul_left]
    _ = _ := by rw [htail]

lemma shifted_lambert2 (j : ℕ) :
    ∑' l : ℕ, q ^ l / (1 - q ^ (j + 1 + l)) ^ 2 =
      q ^ (-(j + 1 : ℤ)) * (lambert2 - theta j) := by
  let f : ℕ → ℝ := fun m ↦ q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2
  have hf : Summable f := summable_lambert2
  have htail : ∑' l : ℕ, f (l + j) = lambert2 - theta j := by
    rw [eq_sub_iff_add_eq]
    simpa [f, lambert2, theta, add_comm] using hf.sum_add_tsum_nat_add j
  calc
    ∑' l : ℕ, q ^ l / (1 - q ^ (j + 1 + l)) ^ 2 =
        ∑' l : ℕ, q ^ (-(j + 1 : ℤ)) * f (l + j) := by
          apply tsum_congr
          intro l
          simp only [f]
          exact shifted_lambert2_term j l
    _ = q ^ (-(j + 1 : ℤ)) * ∑' l : ℕ, f (l + j) := by
      rw [tsum_mul_left]
    _ = _ := by rw [htail]

noncomputable def coeffC (N : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * v j

noncomputable def coeffA (N : ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) *
    (u j * eta j + v j * theta j)

/-- Summing a finite partial-fraction decomposition whose total simple-pole
coefficient vanishes leaves a linear form in the double-pole Lambert sum. -/
theorem partialFractions_tsum (N : ℕ) (R : ℝ → ℝ) (u v : ℕ → ℝ)
    (hR : ∀ l : ℕ, q ^ l * R (q ^ l) =
      ∑ j ∈ Finset.range N,
        ((u j * (q ^ l / (1 - q ^ (j + 1 + l)))) +
        (v j * (q ^ l / (1 - q ^ (j + 1 + l)) ^ 2))))
    (hcancel : ∑ j ∈ Finset.range N,
      q ^ (-(j + 1 : ℤ)) * u j = 0) :
    ∑' l : ℕ, q ^ l * R (q ^ l) =
      coeffC N v * lambert2 - coeffA N u v := by
  rw [tsum_congr hR]
  have hs (j : ℕ) : Summable (fun l : ℕ ↦
      u j * (q ^ l / (1 - q ^ (j + 1 + l))) +
      v j * (q ^ l / (1 - q ^ (j + 1 + l)) ^ 2)) :=
    ((summable_shifted_lambert1 j).mul_left (u j)).add
      ((summable_shifted_lambert2 j).mul_left (v j))
  let F : ℕ → ℕ → ℝ := fun j l ↦
    u j * (q ^ l / (1 - q ^ (j + 1 + l))) +
    v j * (q ^ l / (1 - q ^ (j + 1 + l)) ^ 2)
  have hswap : (∑' l : ℕ, ∑ j ∈ Finset.range N, F j l) =
      ∑ j ∈ Finset.range N, ∑' l : ℕ, F j l :=
    Summable.tsum_finsetSum (fun j _ ↦ hs j)
  dsimp only [F] at hswap
  rw [hswap]
  trans ∑ j ∈ Finset.range N,
      (u j * (q ^ (-(j + 1 : ℤ)) * (lambert1 - eta j)) +
       v j * (q ^ (-(j + 1 : ℤ)) * (lambert2 - theta j)))
  · apply Finset.sum_congr rfl
    intro j hj
    rw [(summable_shifted_lambert1 j).mul_left (u j) |>.tsum_add
        ((summable_shifted_lambert2 j).mul_left (v j)),
      tsum_mul_left, tsum_mul_left, shifted_lambert1, shifted_lambert2]
  · rw [Finset.sum_add_distrib]
    have hu : (∑ j ∈ Finset.range N,
        u j * (q ^ (-(j + 1 : ℤ)) * (lambert1 - eta j))) =
        (∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * u j) * lambert1 -
        ∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * u j * eta j := by
      calc
        _ = ∑ j ∈ Finset.range N,
            ((q ^ (-(j + 1 : ℤ)) * u j) * lambert1 -
             (q ^ (-(j + 1 : ℤ)) * u j) * eta j) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_mul]
    have hv : (∑ j ∈ Finset.range N,
        v j * (q ^ (-(j + 1 : ℤ)) * (lambert2 - theta j))) =
        (∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * v j) * lambert2 -
        ∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * v j * theta j := by
      calc
        _ = ∑ j ∈ Finset.range N,
            ((q ^ (-(j + 1 : ℤ)) * v j) * lambert2 -
             (q ^ (-(j + 1 : ℤ)) * v j) * theta j) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_mul]
    rw [hu, hv, hcancel, zero_mul, zero_sub]
    simp only [coeffC, coeffA]
    have hA : (∑ j ∈ Finset.range N,
        q ^ (-(j + 1 : ℤ)) * (u j * eta j + v j * theta j)) =
        (∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * u j * eta j) +
        (∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * v j * theta j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hA]
    ring

end ZPF

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250/Erdos250QApery.lean` -/

section
open scoped BigOperators Topology

namespace QApery

noncomputable section

/-- The specialization `q = 1/2`. -/
def q : ℝ := 1 / 2

/-- The finite `q`-Pochhammer symbol. -/
def qPochhammer (a : ℝ) (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m, (1 - a * q ^ j)

/-- Nesterenko--Duverney rational function specialized at `q = 1/2`.
The use of powers of `2` avoids integer exponents in Lean. -/
def R (n : ℕ) (T : ℝ) : ℝ :=
  T ^ n *
    (∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * T)) *
    (∏ j ∈ Finset.range (n + 1), (1 - T / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2)

def term (n l : ℕ) : ℝ := q ^ l * R n (q ^ l)

lemma q_pos : 0 < q := by norm_num [q]
lemma q_lt_one : q < 1 := by norm_num [q]

lemma pow_two_mul_q_pow (k : ℕ) :
    (2 : ℝ) ^ k * q ^ k = 1 := by
  rw [← mul_pow]
  norm_num [q]

lemma numerator_zero {n l : ℕ} (hl : l < n) :
    (∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l)) = 0 := by
  let j := n - 1 - l
  have hj : j < n := by omega
  have hexp : n - 1 - j = l := by
    dsimp [j]
    omega
  apply Finset.prod_eq_zero (Finset.mem_range.2 hj)
  rw [hexp, pow_two_mul_q_pow]
  norm_num

lemma R_pow_zero {n l : ℕ} (hl : l < n) : R n (q ^ l) = 0 := by
  simp [R, numerator_zero hl]

lemma term_zero {n l : ℕ} (hl : l < n) : term n l = 0 := by
  simp [term, R_pow_zero hl]

lemma numerator_factor_pos {n l j : ℕ} (_hn : 1 ≤ n) (hnl : n ≤ l) (hj : j < n) :
    0 < 1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l := by
  have he : n - 1 - j < l := by omega
  have hp : (2 : ℝ) ^ (n - 1 - j) < 2 ^ l :=
    pow_lt_pow_right₀ (by norm_num) he
  rw [show q ^ l = 1 / (2 : ℝ) ^ l by simp [q]]
  rw [sub_pos, mul_one_div]
  exact (div_lt_one (by positivity)).2 hp

lemma numerator_prod_pos {n l : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    0 < ∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l) := by
  exact Finset.prod_pos fun j hj ↦
    numerator_factor_pos hn hnl (Finset.mem_range.1 hj)

lemma denominator_factor_pos {l j : ℕ} :
    0 < 1 - q ^ l / (2 : ℝ) ^ (j + 1) := by
  rw [sub_pos]
  have hq : q ^ l ≤ 1 := (pow_le_one₀ (le_of_lt q_pos) (le_of_lt q_lt_one))
  have ht : (1 : ℝ) < 2 ^ (j + 1) := by
    exact one_lt_pow₀ (by norm_num) (by omega)
  exact (div_lt_one (by positivity)).2 (hq.trans_lt ht)

lemma denominator_ratio_eq (l j : ℕ) :
    q ^ l / (2 : ℝ) ^ (j + 1) = 1 / (2 : ℝ) ^ (l + j + 1) := by
  rw [show q ^ l = 1 / (2 : ℝ) ^ l by simp [q]]
  rw [div_div, ← pow_add]
  congr 2

lemma denominator_factor_ge_three_quarters {n l j : ℕ}
    (hn : 1 ≤ n) (hnl : n ≤ l) :
    (3 : ℝ) / 4 ≤ 1 - q ^ l / (2 : ℝ) ^ (j + 1) := by
  have hexp : 2 ≤ l + j + 1 := by omega
  have hratio : q ^ l / (2 : ℝ) ^ (j + 1) ≤ (1 : ℝ) / 2 ^ 2 := by
    rw [denominator_ratio_eq]
    exact one_div_pow_le_one_div_pow_of_le (by norm_num) hexp
  norm_num at hratio ⊢
  linarith

lemma denominator_inv_sq_le {n l j : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2 ≤ ((4 : ℝ) / 3) ^ 2 := by
  have hpos := denominator_factor_pos (l := l) (j := j)
  have hge := denominator_factor_ge_three_quarters (j := j) hn hnl
  have hinv : (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ≤ (4 : ℝ) / 3 := by
    have := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 3 / 4)).2 hge
    norm_num at this ⊢
    exact this
  exact pow_le_pow_left₀ (le_of_lt (inv_pos.2 hpos)) hinv _

lemma denominator_prod_le {n l : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    (∏ j ∈ Finset.range (n + 1),
        (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2)
      ≤ ((4 : ℝ) / 3) ^ (2 * n + 2) := by
  calc
    (∏ j ∈ Finset.range (n + 1),
        (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2)
        ≤ ∏ _j ∈ Finset.range (n + 1), ((4 : ℝ) / 3) ^ 2 := by
          apply Finset.prod_le_prod
          · intro j hj
            positivity
          · intro j hj
            exact denominator_inv_sq_le hn hnl
    _ = (((4 : ℝ) / 3) ^ 2) ^ (n + 1) := by simp
    _ = ((4 : ℝ) / 3) ^ (2 * n + 2) := by
      rw [← pow_mul]
      congr 2

lemma numerator_prod_le_one {n l : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    (∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l)) ≤ 1 := by
  apply Finset.prod_le_one
  · intro j hj
    exact (numerator_factor_pos hn hnl (Finset.mem_range.1 hj)).le
  · intro j hj
    have : 0 ≤ (2 : ℝ) ^ (n - 1 - j) * q ^ l :=
      mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg q_pos.le _)
    linarith

lemma term_eq_products (n l : ℕ) : term n l =
    q ^ ((n + 1) * l) *
      (∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l)) *
      (∏ j ∈ Finset.range (n + 1),
        (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2) := by
  unfold term R
  rw [← pow_mul]
  have hp : q ^ l * q ^ (l * n) = q ^ ((n + 1) * l) := by
    rw [← pow_add]
    congr 2
    simp [Nat.mul_add, Nat.mul_comm, Nat.add_comm]
  rw [← hp]
  ring

lemma term_le_geometric {n l : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    term n l ≤ ((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * l) := by
  rw [term_eq_products]
  have hq0 : 0 ≤ q ^ ((n + 1) * l) := pow_nonneg q_pos.le _
  have hnum0 : 0 ≤ ∏ j ∈ Finset.range n,
      (1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l) :=
    (numerator_prod_pos hn hnl).le
  have hden0 : 0 ≤ ∏ j ∈ Finset.range (n + 1),
      (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2 := by positivity
  have hnum := numerator_prod_le_one hn hnl
  have hden := denominator_prod_le hn hnl
  calc
    q ^ ((n + 1) * l) *
          (∏ j ∈ Finset.range n, (1 - (2 : ℝ) ^ (n - 1 - j) * q ^ l)) *
          (∏ j ∈ Finset.range (n + 1),
            (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2)
        ≤ q ^ ((n + 1) * l) * 1 *
          (∏ j ∈ Finset.range (n + 1),
            (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hnum hq0) hden0
    _ ≤ q ^ ((n + 1) * l) * 1 * ((4 : ℝ) / 3) ^ (2 * n + 2) := by
          exact mul_le_mul_of_nonneg_left hden (mul_nonneg hq0 zero_le_one)
    _ = ((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * l) := by ring

lemma R_pow_pos {n l : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    0 < R n (q ^ l) := by
  have hqpow : 0 < q ^ l := pow_pos q_pos _
  have hnum := numerator_prod_pos hn hnl
  have hden : 0 < ∏ j ∈ Finset.range (n + 1),
      (1 - q ^ l / (2 : ℝ) ^ (j + 1))⁻¹ ^ 2 := by
    exact Finset.prod_pos fun j hj ↦
      pow_pos (inv_pos.2 denominator_factor_pos) _
  exact mul_pos (mul_pos (pow_pos hqpow _) hnum) hden

lemma term_pos {n l : ℕ} (hn : 1 ≤ n) (hnl : n ≤ l) :
    0 < term n l := by
  exact mul_pos (pow_pos q_pos _) (R_pow_pos hn hnl)

lemma geom_ratio_nonneg (n : ℕ) : 0 ≤ q ^ (n + 1) := pow_nonneg q_pos.le _

lemma geom_ratio_lt_one (n : ℕ) : q ^ (n + 1) < 1 :=
  pow_lt_one₀ q_pos.le q_lt_one (by omega)

lemma summable_term {n : ℕ} (hn : 1 ≤ n) : Summable (term n) := by
  have hgeom : Summable (fun l : ℕ ↦
      ((4 : ℝ) / 3) ^ (2 * n + 2) * (q ^ (n + 1)) ^ l) :=
    Summable.mul_left _
      (summable_geometric_of_lt_one (geom_ratio_nonneg n) (geom_ratio_lt_one n))
  refine Summable.of_nonneg_of_le ?_ ?_ hgeom
  · intro l
    by_cases hl : l < n
    · rw [term_zero hl]
    · exact (term_pos hn (Nat.le_of_not_gt hl)).le
  · intro l
    by_cases hl : l < n
    · rw [term_zero hl]
      exact mul_nonneg (pow_nonneg (by norm_num) _)
        (pow_nonneg (geom_ratio_nonneg n) _)
    · simpa only [pow_mul] using term_le_geometric hn (Nat.le_of_not_gt hl)

/-- The positive q-Apéry remainder. -/
def S (n : ℕ) : ℝ := ∑' l : ℕ, term n l

lemma term_nonneg {n : ℕ} (hn : 1 ≤ n) (l : ℕ) : 0 ≤ term n l := by
  by_cases hl : l < n
  · rw [term_zero hl]
  · exact (term_pos hn (Nat.le_of_not_gt hl)).le

lemma S_pos {n : ℕ} (hn : 1 ≤ n) : 0 < S n := by
  exact (summable_term hn).tsum_pos (term_nonneg hn) n (term_pos hn le_rfl)

lemma S_eq_shift {n : ℕ} (hn : 1 ≤ n) :
    S n = ∑' k : ℕ, term n (n + k) := by
  unfold S
  rw [← (summable_term hn).sum_add_tsum_nat_add n]
  have hprefix : ∑ i ∈ Finset.range n, term n i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact term_zero (Finset.mem_range.1 hi)
  rw [hprefix, zero_add]
  congr 1
  funext k
  rw [Nat.add_comm]

def tailMajor (n k : ℕ) : ℝ :=
  ((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * (n + k))

lemma tailMajor_eq (n k : ℕ) : tailMajor n k =
    (((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * n)) *
      (q ^ (n + 1)) ^ k := by
  simp only [tailMajor, Nat.mul_add, pow_add, pow_mul]
  ring

lemma summable_tailMajor (n : ℕ) : Summable (tailMajor n) := by
  have hgeom := summable_geometric_of_lt_one (geom_ratio_nonneg n) (geom_ratio_lt_one n)
  exact (Summable.mul_left
    (((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * n)) hgeom).congr
      fun k ↦ (tailMajor_eq n k).symm

lemma tsum_tailMajor (n : ℕ) :
    ∑' k : ℕ, tailMajor n k =
      (((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * n)) *
        (1 - q ^ (n + 1))⁻¹ := by
  simp_rw [tailMajor_eq]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (geom_ratio_nonneg n) (geom_ratio_lt_one n)]

lemma geom_inv_le_four_thirds {n : ℕ} (hn : 1 ≤ n) :
    (1 - q ^ (n + 1))⁻¹ ≤ (4 : ℝ) / 3 := by
  have hpow : q ^ (n + 1) ≤ (1 : ℝ) / 2 ^ 2 := by
    rw [show q ^ (n + 1) = 1 / (2 : ℝ) ^ (n + 1) by simp [q]]
    exact one_div_pow_le_one_div_pow_of_le (by norm_num) (by omega)
  have hsub : (3 : ℝ) / 4 ≤ 1 - q ^ (n + 1) := by
    norm_num at hpow ⊢
    linarith
  have hpos : 0 < 1 - q ^ (n + 1) := sub_pos.2 (geom_ratio_lt_one n)
  have := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 3 / 4)).2 hsub
  norm_num at this ⊢
  exact this

lemma S_le_explicit {n : ℕ} (hn : 1 ≤ n) :
    S n ≤ ((4 : ℝ) / 3) ^ (2 * n + 3) * q ^ (n * (n + 1)) := by
  rw [S_eq_shift hn]
  calc
    (∑' k : ℕ, term n (n + k)) ≤ ∑' k : ℕ, tailMajor n k := by
      apply Summable.tsum_le_tsum
      · intro k
        exact term_le_geometric hn (Nat.le_add_right n k)
      · exact (summable_term hn).comp_injective (add_right_injective n)
      · exact summable_tailMajor n
    _ = (((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * n)) *
        (1 - q ^ (n + 1))⁻¹ := tsum_tailMajor n
    _ ≤ (((4 : ℝ) / 3) ^ (2 * n + 2) * q ^ ((n + 1) * n)) *
        ((4 : ℝ) / 3) := by
      exact mul_le_mul_of_nonneg_left (geom_inv_le_four_thirds hn)
        (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg q_pos.le _))
    _ = ((4 : ℝ) / 3) ^ (2 * n + 3) * q ^ (n * (n + 1)) := by
      rw [show 2 * n + 3 = (2 * n + 2) + 1 by omega, pow_add]
      rw [Nat.mul_comm (n + 1) n]
      ring

end

end QApery

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250/Erdos250Arithmetic.lean` -/

section
namespace Erdos250Arithmetic

def gauss2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => gauss2 n k + 2 ^ (k + 1) * gauss2 n (k + 1)

@[simp] lemma gauss2_zero_zero : gauss2 0 0 = 1 := rfl
@[simp] lemma gauss2_zero_succ (k : ℕ) : gauss2 0 (k + 1) = 0 := rfl
@[simp] lemma gauss2_succ_zero (n : ℕ) : gauss2 (n + 1) 0 = 1 := rfl
@[simp] lemma gauss2_zero_right (n : ℕ) : gauss2 n 0 = 1 := by cases n <;> rfl
@[simp] lemma gauss2_succ_succ (n k : ℕ) :
    gauss2 (n + 1) (k + 1) = gauss2 n k + 2 ^ (k + 1) * gauss2 n (k + 1) := rfl

@[simp] lemma gauss2_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → gauss2 n k = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => by omega
  | n + 1, k + 1, h => by
      rw [gauss2_succ_succ, gauss2_eq_zero_of_lt (by omega),
        gauss2_eq_zero_of_lt (by omega)]
      simp

@[simp] lemma gauss2_self : ∀ n : ℕ, gauss2 n n = 1
  | 0 => rfl
  | n + 1 => by rw [gauss2_succ_succ, gauss2_self, gauss2_eq_zero_of_lt (by omega)]; simp

lemma gauss2_pos_of_le : ∀ {n k : ℕ}, k ≤ n → 0 < gauss2 n k
  | 0, 0, _ => by simp
  | 0, _ + 1, h => by omega
  | _ + 1, 0, _ => by simp
  | n + 1, k + 1, h => by
      rw [gauss2_succ_succ]
      exact Nat.add_pos_left (gauss2_pos_of_le (by omega)) _

lemma exponent_le_quarter (n k : ℕ) : k * (n - k) ≤ n ^ 2 / 4 := by
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 4)]
  by_cases hk : k ≤ n
  · simpa [Nat.add_sub_of_le hk, mul_assoc, mul_left_comm, mul_comm] using
      (four_mul_le_sq_add k (n - k))
  · simp [Nat.sub_eq_zero_of_le (le_of_not_ge hk)]

lemma rat_mul_div_eq_intCast_of_dvd {D d : ℕ} (z : ℤ)
    (hd : d ∣ D) (hd0 : d ≠ 0) :
    ∃ w : ℤ, (D : ℚ) * ((z : ℚ) / (d : ℚ)) = (w : ℚ) := by
  obtain ⟨c, rfl⟩ := hd
  refine ⟨(c : ℤ) * z, ?_⟩
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
  push_cast
  field_simp [hdq]

lemma sum_eq_intCast_of_each_eq_intCast {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, ∃ z : ℤ, f i = (z : ℚ)) :
    ∃ z : ℤ, ∑ i ∈ s, f i = (z : ℚ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨za, hza⟩ := hf a (by simp)
      obtain ⟨zs, hzs⟩ := ih fun i hi ↦ hf i (by simp [hi])
      exact ⟨za + zs, by simp [ha, hza, hzs]⟩

def oddFactor (d : ℕ) : ℕ := 2 ^ d - 1

/-- The exact finite sum displayed in the writeup for `b_n^*`. -/
def bStar (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    (((gauss2 n k) ^ 2 * gauss2 (n + k) k : ℕ) : ℚ) /
      ((2 : ℕ) ^ (k * (n - k)) : ℕ)

/-- `h₁(k)` after specializing `p = 2`. -/
def hOne (k : ℕ) : ℚ :=
  ∑ d ∈ Finset.Icc 1 k, (1 : ℚ) / (oddFactor d : ℕ)

/-- `h₂(k)` after specializing `p = 2`. -/
def hTwo (k : ℕ) : ℚ :=
  ∑ d ∈ Finset.Icc 1 k, ((2 ^ d : ℕ) : ℚ) / ((oddFactor d : ℕ) ^ 2 : ℕ)

/-- The logarithmic-derivative factor in the cancellation-aware simple-pole coefficient.
For pole `j=k+1`, one has `u_{n,j} = -v_{n,j} * logDerivCoeff n k`. -/
def logDerivCoeff (n k : ℕ) : ℚ :=
  n +
    ∑ d ∈ Finset.Icc (k + 1) (n + k),
      ((2 ^ d : ℕ) : ℚ) / (oddFactor d : ℕ) -
    2 * ∑ d ∈ Finset.Icc 1 k,
      ((2 ^ d : ℕ) : ℚ) / (oddFactor d : ℕ) +
    2 * ∑ d ∈ Finset.Icc 1 (n - k),
      (1 : ℚ) / (oddFactor d : ℕ)

/-- The common coefficient `λ_n 2^(k+1) v_{n,k+1}`. -/
def cCoeff (n k : ℕ) : ℚ :=
  (((gauss2 n k) ^ 2 * gauss2 (n + k) k : ℕ) : ℚ) /
    ((2 : ℕ) ^ (k * (n - k)) : ℕ)

/-- The finite, cancellation-aware expansion of `a_n^*`. -/
def aStarRegrouped (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    cCoeff n k * (hTwo k - logDerivCoeff n k * hOne k)

lemma bStar_eq_sum_cCoeff (n : ℕ) :
    bStar n = ∑ k ∈ Finset.range (n + 1), cCoeff n k := rfl

/-- The power of two `2^{⌊n²/4⌋}` clears the displayed `b_n^*` expansion. -/
lemma powTwo_mul_bStar_eq_intCast (n : ℕ) :
    ∃ z : ℤ, (((2 : ℕ) ^ (n ^ 2 / 4) : ℕ) : ℚ) * bStar n = (z : ℚ) := by
  classical
  rw [bStar, Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro k hk
  rw [Finset.mem_range] at hk
  apply rat_mul_div_eq_intCast_of_dvd
  · exact Nat.pow_dvd_pow 2 (exponent_le_quarter n k)
  · positivity

def denProd (n : ℕ) : ℕ := ∏ d ∈ Finset.Icc 1 n, oddFactor d

lemma oddFactor_dvd_denProd {d n : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    oddFactor d ∣ denProd n := by
  exact Finset.dvd_prod_of_mem oddFactor (Finset.mem_Icc.mpr ⟨hd, hdn⟩)

lemma denProd_dvd_denProd {k n : ℕ} (hkn : k ≤ n) : denProd k ∣ denProd n := by
  apply Finset.prod_dvd_prod_of_subset (Finset.Icc 1 k) (Finset.Icc 1 n) oddFactor
  intro d hd
  simp only [Finset.mem_Icc] at hd ⊢
  exact ⟨hd.1, hd.2.trans hkn⟩

def highProd (n k : ℕ) : ℕ := ∏ r ∈ Finset.Icc 1 k, oddFactor (n + r)

lemma denProd_succ (k : ℕ) :
    denProd (k + 1) = denProd k * oddFactor (k + 1) := by
  rw [denProd, denProd, Finset.prod_Icc_succ_top]
  omega

lemma highProd_succ_right (n k : ℕ) :
    highProd n (k + 1) = highProd n k * oddFactor (n + k + 1) := by
  rw [highProd, highProd, Finset.prod_Icc_succ_top]
  · congr 2
  · omega

lemma highProd_succ_left (n k : ℕ) :
    highProd n (k + 1) = oddFactor (n + 1) * highProd (n + 1) k := by
  induction k with
  | zero => simp [highProd, oddFactor]
  | succ k ih =>
      rw [highProd_succ_right n (k + 1), highProd_succ_right (n + 1) k, ih]
      have hlast : oddFactor (n + (k + 1) + 1) =
          oddFactor (n + 1 + k + 1) := by
        congr 1
        omega
      rw [hlast]
      ring

theorem gauss2_mul_denProd_eq_highProd (n k : ℕ) :
    gauss2 (n + k) k * denProd k = highProd n k := by
  induction k generalizing n with
  | zero => simp [denProd, highProd]
  | succ k ih =>
      induction n with
      | zero => simp [denProd, highProd]
      | succ n hn =>
          rw [show (n + 1) + (k + 1) = (n + k + 1) + 1 by omega,
            gauss2_succ_succ, denProd_succ]
          calc
            (gauss2 (n + k + 1) k + 2 ^ (k + 1) * gauss2 (n + k + 1) (k + 1)) *
                  (denProd k * oddFactor (k + 1)) =
                (gauss2 ((n + 1) + k) k * denProd k) * oddFactor (k + 1) +
                  2 ^ (k + 1) *
                    ((gauss2 (n + (k + 1)) (k + 1) * denProd (k + 1))) := by
                      rw [denProd_succ]
                      congr 1 <;> ring
            _ = highProd (n + 1) k * oddFactor (k + 1) +
                  2 ^ (k + 1) * highProd n (k + 1) := by
                    rw [ih (n + 1), hn]
            _ = highProd (n + 1) k * oddFactor (k + 1) +
                  2 ^ (k + 1) *
                    (oddFactor (n + 1) * highProd (n + 1) k) := by
                      rw [highProd_succ_left]
            _ = highProd (n + 1) k * oddFactor (n + k + 2) := by
              have hp : 2 ^ (n + k + 2) = 2 ^ (k + 1) * 2 ^ (n + 1) := by
                rw [← pow_add]
                congr 1
                omega
              have hA : 1 ≤ 2 ^ (k + 1) := one_le_pow₀ (by omega)
              have hB : 1 ≤ 2 ^ (n + 1) := one_le_pow₀ (by omega)
              have hAB : 1 ≤ 2 ^ (k + 1) * 2 ^ (n + 1) :=
                Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num))
                  (pow_ne_zero _ (by norm_num)))
              have hodd : oddFactor (k + 1) +
                    2 ^ (k + 1) * oddFactor (n + 1) = oddFactor (n + k + 2) := by
                simp only [oddFactor]
                rw [hp]
                nlinarith [Nat.sub_add_cancel hA, Nat.sub_add_cancel hB,
                  Nat.sub_add_cancel hAB]
              rw [← hodd]
              ring
            _ = highProd (n + 1) (k + 1) := by
              rw [highProd_succ_right]
              congr 2
              omega

lemma oddFactor_dvd_highProd {n k r : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    oddFactor (n + r) ∣ highProd n k := by
  exact Finset.dvd_prod_of_mem (fun r ↦ oddFactor (n + r))
    (Finset.mem_Icc.mpr ⟨hr, hrk⟩)

/-- Once the Gaussian product identity is available, every apparent denominator
`2^(n+r)-1` in `L_{n,k}` is absorbed by the Gaussian coefficient and one copy of `D_n`. -/
lemma high_oddFactor_dvd_gauss2_mul_denProd {n k r : ℕ} (hkn : k ≤ n)
    (hr : 1 ≤ r) (hrk : r ≤ k)
    (hprod : gauss2 (n + k) k * denProd k = highProd n k) :
    oddFactor (n + r) ∣ gauss2 (n + k) k * denProd n := by
  apply (oddFactor_dvd_highProd hr hrk).trans
  rw [← hprod]
  exact Nat.mul_dvd_mul_left _ (denProd_dvd_denProd hkn)

lemma mul_dvd_mul_denProd_sq_of_dvd_mul_denProd {a b g D : ℕ}
    (ha : a ∣ g * D) (hb : b ∣ D) : a * b ∣ g * D ^ 2 := by
  simpa [pow_two, mul_assoc] using Nat.mul_dvd_mul ha hb

/-- Divisibility needed for a high-index summand of `c_{n,k} L_{n,k} h1_k`.
The Gaussian coefficient absorbs `2^(n+r)-1`; the two copies of `D_n` absorb
the product-formula denominator and the factor from `h1_k`. -/
lemma high_mixed_denominator_dvd_scaled_gauss {n k r d e M : ℕ}
    (hkn : k ≤ n) (hr : 1 ≤ r) (hrk : r ≤ k)
    (hd : 1 ≤ d) (hdk : d ≤ k) (he : e ≤ M)
    (hprod : gauss2 (n + k) k * denProd k = highProd n k) :
    2 ^ e * (oddFactor (n + r) * oddFactor d) ∣
      (2 ^ M * denProd n ^ 2) * gauss2 (n + k) k := by
  have hhigh := high_oddFactor_dvd_gauss2_mul_denProd hkn hr hrk hprod
  have hlow := oddFactor_dvd_denProd hd (hdk.trans hkn)
  have hodd : oddFactor (n + r) * oddFactor d ∣
      denProd n ^ 2 * gauss2 (n + k) k := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using Nat.mul_dvd_mul hhigh hlow
  simpa [mul_assoc] using Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 he) hodd

lemma rat_mul_mul_div_eq_intCast_of_dvd {E c d : ℕ} (z : ℤ)
    (hd : d ∣ E * c) (hd0 : d ≠ 0) :
    ∃ w : ℤ, (E : ℚ) * (((c : ℚ) * (z : ℚ)) / (d : ℚ)) = (w : ℚ) := by
  obtain ⟨w, hw⟩ := rat_mul_div_eq_intCast_of_dvd z hd hd0
  refine ⟨w, ?_⟩
  rw [← hw]
  push_cast
  ring

def RatIntegral (x : ℚ) : Prop := ∃ z : ℤ, x = (z : ℚ)

lemma RatIntegral.add {x y : ℚ} (hx : RatIntegral x) (hy : RatIntegral y) :
    RatIntegral (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩

lemma RatIntegral.sub {x y : ℚ} (hx : RatIntegral x) (hy : RatIntegral y) :
    RatIntegral (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by push_cast; rfl⟩

lemma RatIntegral.mul {x y : ℚ} (hx : RatIntegral x) (hy : RatIntegral y) :
    RatIntegral (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by push_cast; rfl⟩

lemma RatIntegral.intCast (z : ℤ) : RatIntegral (z : ℚ) := ⟨z, rfl⟩

lemma RatIntegral.natCast_mul (m : ℕ) {x : ℚ} (hx : RatIntegral x) :
    RatIntegral ((m : ℚ) * x) :=
  (RatIntegral.intCast (m : ℤ)).mul hx

lemma oddFactor_ne_zero {d : ℕ} (hd : 1 ≤ d) : oddFactor d ≠ 0 := by
  exact Nat.sub_ne_zero_of_lt (one_lt_pow' (by decide : (1 : ℕ) < 2) (by omega))

lemma two_oddFactors_dvd_denProd_sq {d₁ d₂ n : ℕ}
    (hd₁ : 1 ≤ d₁) (hd₁n : d₁ ≤ n) (hd₂ : 1 ≤ d₂) (hd₂n : d₂ ≤ n) :
    oddFactor d₁ * oddFactor d₂ ∣ denProd n ^ 2 := by
  simpa [pow_two] using Nat.mul_dvd_mul
    (oddFactor_dvd_denProd hd₁ hd₁n) (oddFactor_dvd_denProd hd₂ hd₂n)

/-- The full `E_n = 2^{⌊n²/4⌋} D_n²` used in the writeup clears `b_n^*`.
The `D_n²` factor is not actually needed for this coefficient. -/
lemma E_mul_bStar_eq_intCast (n : ℕ) :
    ∃ z : ℤ,
      ((((2 : ℕ) ^ (n ^ 2 / 4)) * denProd n ^ 2 : ℕ) : ℚ) * bStar n = (z : ℚ) := by
  obtain ⟨z, hz⟩ := powTwo_mul_bStar_eq_intCast n
  refine ⟨(denProd n ^ 2 : ℕ) * z, ?_⟩
  push_cast at hz ⊢
  calc
    (2 : ℚ) ^ (n ^ 2 / 4) * (denProd n : ℚ) ^ 2 * bStar n =
        (denProd n : ℚ) ^ 2 * ((2 : ℚ) ^ (n ^ 2 / 4) * bStar n) := by ring
    _ = (denProd n : ℚ) ^ 2 * (z : ℚ) := by rw [hz]

lemma mixed_denominator_dvd {e M d₁ d₂ n : ℕ} (he : e ≤ M)
    (hd₁ : 1 ≤ d₁) (hd₁n : d₁ ≤ n) (hd₂ : 1 ≤ d₂) (hd₂n : d₂ ≤ n) :
    2 ^ e * (oddFactor d₁ * oddFactor d₂) ∣ 2 ^ M * denProd n ^ 2 := by
  exact Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 he)
    (two_oddFactors_dvd_denProd_sq hd₁ hd₁n hd₂ hd₂n)

/-- Uniform divisibility for the long interval `k+1 ≤ a ≤ n+k` occurring in
`logDerivCoeff`: low `a` is handled by `D_n`, while high `a=n+r` is absorbed
by `gauss2 (n+k) k` through the product identity. -/
lemma long_range_denominator_dvd {n k a d e M : ℕ}
    (hkn : k ≤ n) (haL : k + 1 ≤ a) (haU : a ≤ n + k)
    (hd : 1 ≤ d) (hdk : d ≤ k) (he : e ≤ M)
    (hprod : gauss2 (n + k) k * denProd k = highProd n k) :
    2 ^ e * (oddFactor a * oddFactor d) ∣
      (2 ^ M * denProd n ^ 2) *
        ((gauss2 n k) ^ 2 * gauss2 (n + k) k) := by
  by_cases han : a ≤ n
  · have hbase := mixed_denominator_dvd he (by omega : 1 ≤ a) han
        hd (hdk.trans hkn)
    exact dvd_mul_of_dvd_left hbase _
  · let r := a - n
    have hr : 1 ≤ r := by dsimp [r]; omega
    have hrk : r ≤ k := by dsimp [r]; omega
    have har : a = n + r := by dsimp [r]; omega
    have hbase := high_mixed_denominator_dvd_scaled_gauss hkn hr hrk hd hdk he hprod
    rw [har]
    convert (dvd_mul_of_dvd_left hbase ((gauss2 n k) ^ 2)) using 1 <;> ac_rfl

lemma long_odd_denominator_dvd {n k a d : ℕ}
    (hkn : k ≤ n) (haL : k + 1 ≤ a) (haU : a ≤ n + k)
    (hd : 1 ≤ d) (hdk : d ≤ k) :
    oddFactor a * oddFactor d ∣ denProd n ^ 2 * gauss2 (n + k) k := by
  by_cases han : a ≤ n
  · exact dvd_mul_of_dvd_left
      (two_oddFactors_dvd_denProd_sq (by omega : 1 ≤ a) han hd (hdk.trans hkn)) _
  · let r := a - n
    have hr : 1 ≤ r := by dsimp [r]; omega
    have hrk : r ≤ k := by dsimp [r]; omega
    have har : a = n + r := by dsimp [r]; omega
    rw [har]
    have hhigh := high_oddFactor_dvd_gauss2_mul_denProd hkn hr hrk
      (gauss2_mul_denProd_eq_highProd n k)
    have hlow := oddFactor_dvd_denProd hd (hdk.trans hkn)
    convert Nat.mul_dvd_mul hhigh hlow using 1 <;> simp [pow_two] <;> ac_rfl

lemma oddScale_mul_hTwo_integral {n k : ℕ} (hkn : k ≤ n) :
    RatIntegral
      ((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) * hTwo k) := by
  classical
  rw [hTwo, Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hdiv : oddFactor d ^ 2 ∣ denProd n ^ 2 * gauss2 (n + k) k := by
    have h0 := two_oddFactors_dvd_denProd_sq hd.1 (hd.2.trans hkn)
      hd.1 (hd.2.trans hkn)
    exact dvd_mul_of_dvd_left (by simpa [pow_two] using h0) _
  apply rat_mul_div_eq_intCast_of_dvd (z := (2 ^ d : ℕ)) hdiv
  exact pow_ne_zero 2 (oddFactor_ne_zero hd.1)

lemma oddScale_mul_hOne_integral {n k : ℕ} (hkn : k ≤ n) :
    RatIntegral
      ((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) * hOne k) := by
  classical
  rw [hOne, Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hdiv : oddFactor d ∣ denProd n ^ 2 * gauss2 (n + k) k := by
    exact (oddFactor_dvd_denProd hd.1 (hd.2.trans hkn)).trans
      (by exact dvd_mul_of_dvd_left (dvd_pow_self _ (by decide : 2 ≠ 0)) _)
  apply rat_mul_div_eq_intCast_of_dvd (z := (1 : ℤ)) hdiv
  exact oddFactor_ne_zero hd.1

lemma denProdSq_mul_two_ratSums_integral
    {ι κ : Type*} (n : ℕ) (s : Finset ι) (t : Finset κ)
    (z₁ : ι → ℤ) (z₂ : κ → ℤ) (d₁ : ι → ℕ) (d₂ : κ → ℕ)
    (hd₁ : ∀ i ∈ s, 1 ≤ d₁ i ∧ d₁ i ≤ n)
    (hd₂ : ∀ j ∈ t, 1 ≤ d₂ j ∧ d₂ j ≤ n) :
    RatIntegral
      (((denProd n ^ 2 : ℕ) : ℚ) *
        (∑ i ∈ s, (z₁ i : ℚ) / (oddFactor (d₁ i) : ℕ)) *
        (∑ j ∈ t, (z₂ j : ℚ) / (oddFactor (d₂ j) : ℕ))) := by
  classical
  rw [Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro j hj
  have hexpand :
      (((denProd n ^ 2 : ℕ) : ℚ) *
          (∑ i ∈ s, (z₁ i : ℚ) / (oddFactor (d₁ i) : ℕ))) *
          ((z₂ j : ℚ) / (oddFactor (d₂ j) : ℕ)) =
        ∑ i ∈ s,
          (((denProd n ^ 2 : ℕ) : ℚ) *
            ((z₁ i : ℚ) / (oddFactor (d₁ i) : ℕ))) *
            ((z₂ j : ℚ) / (oddFactor (d₂ j) : ℕ)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hexpand]
  apply sum_eq_intCast_of_each_eq_intCast
  intro i hi
  have hdiv := two_oddFactors_dvd_denProd_sq
    (hd₁ i hi).1 (hd₁ i hi).2 (hd₂ j hj).1 (hd₂ j hj).2
  obtain ⟨w, hw⟩ := rat_mul_div_eq_intCast_of_dvd (z₁ i * z₂ j) hdiv
    (mul_ne_zero (oddFactor_ne_zero (hd₁ i hi).1) (oddFactor_ne_zero (hd₂ j hj).1))
  refine ⟨w, ?_⟩
  rw [← hw]
  push_cast
  field_simp [oddFactor_ne_zero (hd₁ i hi).1, oddFactor_ne_zero (hd₂ j hj).1]

lemma oddScale_mul_longSum_mul_hOne_integral {n k : ℕ} (hkn : k ≤ n) :
    RatIntegral
      ((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) *
        (∑ a ∈ Finset.Icc (k + 1) (n + k),
          ((2 ^ a : ℕ) : ℚ) / (oddFactor a : ℕ)) * hOne k) := by
  classical
  rw [hOne, Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro d hd
  rw [Finset.mem_Icc] at hd
  have hexpand :
      ((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) *
          (∑ a ∈ Finset.Icc (k + 1) (n + k),
            ((2 ^ a : ℕ) : ℚ) / (oddFactor a : ℕ))) *
          ((1 : ℚ) / (oddFactor d : ℕ)) =
        ∑ a ∈ Finset.Icc (k + 1) (n + k),
          (((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) *
            (((2 ^ a : ℕ) : ℚ) / (oddFactor a : ℕ))) *
            ((1 : ℚ) / (oddFactor d : ℕ))) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hexpand]
  apply sum_eq_intCast_of_each_eq_intCast
  intro a ha
  rw [Finset.mem_Icc] at ha
  have hdiv := long_odd_denominator_dvd hkn ha.1 ha.2 hd.1 hd.2
  obtain ⟨w, hw⟩ := rat_mul_div_eq_intCast_of_dvd (2 ^ a : ℕ) hdiv
    (mul_ne_zero (oddFactor_ne_zero (by omega)) (oddFactor_ne_zero hd.1))
  refine ⟨w, ?_⟩
  rw [← hw]
  push_cast
  field_simp [oddFactor_ne_zero (by omega : 1 ≤ a), oddFactor_ne_zero hd.1]

lemma oddScale_mul_logDeriv_mul_hOne_integral {n k : ℕ} (hkn : k ≤ n) :
    RatIntegral
      ((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) *
        logDerivCoeff n k * hOne k) := by
  let G : ℕ := gauss2 (n + k) k
  let scale : ℕ := denProd n ^ 2 * G
  have hconst : RatIntegral (((n : ℚ) * ((scale : ℕ) : ℚ)) * hOne k) := by
    have h := oddScale_mul_hOne_integral hkn
    have hm := RatIntegral.natCast_mul n h
    convert hm using 1 <;> dsimp [scale, G] <;> push_cast <;> ring
  have hlong : RatIntegral
      (((scale : ℕ) : ℚ) *
        (∑ a ∈ Finset.Icc (k + 1) (n + k),
          ((2 ^ a : ℕ) : ℚ) / (oddFactor a : ℕ)) * hOne k) := by
    exact oddScale_mul_longSum_mul_hOne_integral hkn
  have hlow₁base : RatIntegral
      (((denProd n ^ 2 : ℕ) : ℚ) *
        (∑ a ∈ Finset.Icc 1 k, ((2 ^ a : ℕ) : ℚ) / (oddFactor a : ℕ)) *
        (∑ d ∈ Finset.Icc 1 k, (1 : ℚ) / (oddFactor d : ℕ))) := by
    apply denProdSq_mul_two_ratSums_integral n
    · intro a ha
      rw [Finset.mem_Icc] at ha
      exact ⟨ha.1, ha.2.trans hkn⟩
    · intro d hd
      rw [Finset.mem_Icc] at hd
      exact ⟨hd.1, hd.2.trans hkn⟩
  have hlow₁ : RatIntegral
      (((scale : ℕ) : ℚ) *
        (∑ a ∈ Finset.Icc 1 k, ((2 ^ a : ℕ) : ℚ) / (oddFactor a : ℕ)) * hOne k) := by
    have hmul := (RatIntegral.intCast (G : ℤ)).mul hlow₁base
    convert hmul using 1 <;> simp only [scale, G, hOne] <;> push_cast <;> ring
  have hlow₂base : RatIntegral
      (((denProd n ^ 2 : ℕ) : ℚ) *
        (∑ a ∈ Finset.Icc 1 (n - k), (1 : ℚ) / (oddFactor a : ℕ)) *
        (∑ d ∈ Finset.Icc 1 k, (1 : ℚ) / (oddFactor d : ℕ))) := by
    apply denProdSq_mul_two_ratSums_integral n
    · intro a ha
      rw [Finset.mem_Icc] at ha
      exact ⟨ha.1, by omega⟩
    · intro d hd
      rw [Finset.mem_Icc] at hd
      exact ⟨hd.1, hd.2.trans hkn⟩
  have hlow₂ : RatIntegral
      (((scale : ℕ) : ℚ) *
        (∑ a ∈ Finset.Icc 1 (n - k), (1 : ℚ) / (oddFactor a : ℕ)) * hOne k) := by
    have hmul := (RatIntegral.intCast (G : ℤ)).mul hlow₂base
    convert hmul using 1 <;> simp only [scale, G, hOne] <;> push_cast <;> ring
  have hall := ((hconst.add hlong).sub (RatIntegral.natCast_mul 2 hlow₁)).add
    (RatIntegral.natCast_mul 2 hlow₂)
  convert hall using 1 <;> simp only [scale, G, logDerivCoeff] <;> push_cast <;> ring

lemma oddScale_mul_aBracket_integral {n k : ℕ} (hkn : k ≤ n) :
    RatIntegral
      ((((denProd n ^ 2) * gauss2 (n + k) k : ℕ) : ℚ) *
        (hTwo k - logDerivCoeff n k * hOne k)) := by
  have h₂ := oddScale_mul_hTwo_integral hkn
  have h₁ := oddScale_mul_logDeriv_mul_hOne_integral hkn
  convert h₂.sub h₁ using 1 <;> ring

lemma E_mul_cCoeff_aBracket_integral {n k : ℕ} (hkn : k ≤ n) :
    RatIntegral
      (((((2 : ℕ) ^ (n ^ 2 / 4)) * denProd n ^ 2 : ℕ) : ℚ) *
        (cCoeff n k * (hTwo k - logDerivCoeff n k * hOne k))) := by
  let M := n ^ 2 / 4
  let e := k * (n - k)
  let G₁ := gauss2 n k
  let G₂ := gauss2 (n + k) k
  let bracket := hTwo k - logDerivCoeff n k * hOne k
  have he : e ≤ M := exponent_le_quarter n k
  have hodd : RatIntegral ((((denProd n ^ 2) * G₂ : ℕ) : ℚ) * bracket) := by
    exact oddScale_mul_aBracket_integral hkn
  have hmul := RatIntegral.natCast_mul ((2 ^ (M - e)) * G₁ ^ 2) hodd
  convert hmul using 1
  simp only [M, e, G₁, G₂, bracket, cCoeff]
  push_cast
  have hpow : (2 : ℚ) ^ (n ^ 2 / 4) =
      (2 : ℚ) ^ (n ^ 2 / 4 - k * (n - k)) * (2 : ℚ) ^ (k * (n - k)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  field_simp

/-- Full denominator clearing for the cancellation-aware expansion of `a_n^*`. -/
lemma E_mul_aStarRegrouped_eq_intCast (n : ℕ) :
    ∃ z : ℤ,
      (((((2 : ℕ) ^ (n ^ 2 / 4)) * denProd n ^ 2 : ℕ) : ℚ) *
        aStarRegrouped n) = (z : ℚ) := by
  classical
  rw [aStarRegrouped, Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro k hk
  exact E_mul_cCoeff_aBracket_integral (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

/-- Generic termwise denominator clearing for a finite sum whose denominators have
one power of two and at most two odd factors `2^d-1`. -/
lemma mixed_denominator_sum_clearing {ι : Type*} (s : Finset ι) (n M : ℕ)
    (z : ι → ℤ) (e d₁ d₂ : ι → ℕ)
    (he : ∀ i ∈ s, e i ≤ M)
    (hd₁ : ∀ i ∈ s, 1 ≤ d₁ i ∧ d₁ i ≤ n)
    (hd₂ : ∀ i ∈ s, 1 ≤ d₂ i ∧ d₂ i ≤ n) :
    ∃ Z : ℤ,
      ((((2 ^ M : ℕ) * denProd n ^ 2 : ℕ) : ℚ) *
        ∑ i ∈ s, (z i : ℚ) /
          (((2 ^ e i : ℕ) * (oddFactor (d₁ i) * oddFactor (d₂ i)) : ℕ) : ℕ) =
        (Z : ℚ)) := by
  classical
  rw [Finset.mul_sum]
  apply sum_eq_intCast_of_each_eq_intCast
  intro i hi
  apply rat_mul_div_eq_intCast_of_dvd
  · exact mixed_denominator_dvd (he i hi)
      (hd₁ i hi).1 (hd₁ i hi).2 (hd₂ i hi).1 (hd₂ i hi).2
  · have h1 := oddFactor_ne_zero (hd₁ i hi).1
    have h2 := oddFactor_ne_zero (hd₂ i hi).1
    positivity

end Erdos250Arithmetic

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250/Erdos250ZV.lean` -/

section
open scoped BigOperators

namespace ZV

lemma prod_range_reverse_Icc {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∏ i ∈ Finset.range n, f (n - i) = ∏ r ∈ Finset.Icc 1 n, f r := by
  apply Finset.prod_bij (fun i _ ↦ n - i)
  · intro i hi
    rw [Finset.mem_Icc]
    have hil : i < n := Finset.mem_range.mp hi
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    have h₁ : i₁ < n := Finset.mem_range.mp hi₁
    have h₂ : i₂ < n := Finset.mem_range.mp hi₂
    omega
  · intro r hr
    rw [Finset.mem_Icc] at hr
    refine ⟨n - r, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro i hi
    rfl

lemma numerator_prod_closed (n k : ℕ) :
    (∏ i ∈ Finset.range n,
      (1 - (2 : ℚ) ^ (n - 1 - i) * DoublePartialFraction.OldRational.root k)) =
      (-1 : ℚ) ^ n * (Erdos250Arithmetic.highProd k n : ℚ) := by
  calc
    _ = ∏ i ∈ Finset.range n,
        (-((Erdos250Arithmetic.oddFactor (k + (n - i)) : ℕ) : ℚ)) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hin : i < n := Finset.mem_range.mp hi
          rw [DoublePartialFraction.OldRational.root, ← pow_add]
          have he : n - 1 - i + (k + 1) = k + (n - i) := by omega
          rw [he]
          simp only [Erdos250Arithmetic.oddFactor]
          have hp : 1 ≤ 2 ^ (k + (n - i)) := one_le_pow₀ (by omega)
          push_cast
          rw [Nat.cast_sub hp]
          norm_num only [Nat.cast_pow, Nat.cast_ofNat]
          ring
    _ = (-1 : ℚ) ^ n *
        ∏ i ∈ Finset.range n, (Erdos250Arithmetic.oddFactor (k + (n - i)) : ℚ) := by
          rw [Finset.prod_neg, Finset.card_range]
    _ = (-1 : ℚ) ^ n *
        ∏ r ∈ Finset.Icc 1 n, (Erdos250Arithmetic.oddFactor (k + r) : ℚ) := by
          rw [prod_range_reverse_Icc (fun r ↦ (Erdos250Arithmetic.oddFactor (k + r) : ℚ)) n]
    _ = _ := by simp only [Erdos250Arithmetic.highProd, Nat.cast_prod]

lemma denProd_add (a b : ℕ) :
    Erdos250Arithmetic.denProd (a + b) = Erdos250Arithmetic.denProd a * Erdos250Arithmetic.highProd a b := by
  induction b with
  | zero => simp [Erdos250Arithmetic.denProd, Erdos250Arithmetic.highProd]
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega, Erdos250Arithmetic.denProd_succ,
        Erdos250Arithmetic.highProd_succ_right, ih]
      ring

lemma denProd_pos (n : ℕ) : 0 < Erdos250Arithmetic.denProd n := by
  apply Finset.prod_pos
  intro d hd
  rw [Finset.mem_Icc] at hd
  exact Nat.sub_pos_of_lt (one_lt_pow' (by omega) (by omega))

lemma gauss2_cast_eq_ratio {n k : ℕ} (hk : k ≤ n) :
    (Erdos250Arithmetic.gauss2 n k : ℚ) =
      (Erdos250Arithmetic.denProd n : ℚ) /
        ((Erdos250Arithmetic.denProd (n - k) : ℚ) * (Erdos250Arithmetic.denProd k : ℚ)) := by
  have hp := Erdos250Arithmetic.gauss2_mul_denProd_eq_highProd (n - k) k
  have hadd : n - k + k = n := Nat.sub_add_cancel hk
  rw [hadd] at hp
  have hden := denProd_add (n - k) k
  rw [hadd] at hden
  have hdk : (Erdos250Arithmetic.denProd k : ℚ) ≠ 0 := by exact_mod_cast (denProd_pos k).ne'
  have hdsub : (Erdos250Arithmetic.denProd (n - k) : ℚ) ≠ 0 := by
    exact_mod_cast (denProd_pos (n - k)).ne'
  have hpq : (Erdos250Arithmetic.gauss2 n k : ℚ) * Erdos250Arithmetic.denProd k =
      Erdos250Arithmetic.highProd (n - k) k := by exact_mod_cast hp
  have hdenq : (Erdos250Arithmetic.denProd n : ℚ) =
      Erdos250Arithmetic.denProd (n - k) * Erdos250Arithmetic.highProd (n - k) k := by
    exact_mod_cast hden
  rw [hdenq]
  field_simp [hdk, hdsub]
  nlinarith

lemma gauss2_add_cast_eq_ratio (n k : ℕ) :
    (Erdos250Arithmetic.gauss2 (n + k) k : ℚ) =
      (Erdos250Arithmetic.denProd (n + k) : ℚ) /
        ((Erdos250Arithmetic.denProd n : ℚ) * (Erdos250Arithmetic.denProd k : ℚ)) := by
  simpa using gauss2_cast_eq_ratio (n := n + k) (k := k) (by omega)

/-- The odd-product part of the double-pole residue is the Gaussian product. -/
lemma gaussian_odd_identity {n k : ℕ} (hk : k ≤ n) :
    (Erdos250Arithmetic.denProd n : ℚ) * (Erdos250Arithmetic.highProd k n : ℚ) /
        ((Erdos250Arithmetic.denProd k : ℚ) ^ 2 * (Erdos250Arithmetic.denProd (n - k) : ℚ) ^ 2) =
      (Erdos250Arithmetic.gauss2 n k : ℚ) ^ 2 * Erdos250Arithmetic.gauss2 (n + k) k := by
  have hdk : (Erdos250Arithmetic.denProd k : ℚ) ≠ 0 := by exact_mod_cast (denProd_pos k).ne'
  have hdn : (Erdos250Arithmetic.denProd n : ℚ) ≠ 0 := by exact_mod_cast (denProd_pos n).ne'
  have hdsub : (Erdos250Arithmetic.denProd (n - k) : ℚ) ≠ 0 := by
    exact_mod_cast (denProd_pos (n - k)).ne'
  have hhigh : (Erdos250Arithmetic.highProd k n : ℚ) =
      Erdos250Arithmetic.denProd (k + n) / Erdos250Arithmetic.denProd k := by
    have h := denProd_add k n
    have hq : (Erdos250Arithmetic.denProd k : ℚ) *
        Erdos250Arithmetic.highProd k n = Erdos250Arithmetic.denProd (k + n) := by
      exact_mod_cast h.symm
    exact (eq_div_iff hdk).2 (by simpa [mul_comm] using hq)
  rw [hhigh, gauss2_cast_eq_ratio hk, gauss2_add_cast_eq_ratio]
  rw [show k + n = n + k by omega]
  field_simp

end ZV

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250/Erdos250VNormalization.lean` -/

section
open scoped BigOperators

namespace VNormalization

open DoublePartialFraction.OldRational
open Erdos250Arithmetic

lemma erased_range_eq_union {n k : ℕ} (hk : k ≤ n) :
    (Finset.range (n + 1)).erase k =
      Finset.range k ∪ Finset.Icc (k + 1) n := by
  ext j
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
  omega

lemma lower_factor {k j : ℕ} (hj : j < k) :
    (1 - root k / root j) ^ 2 =
      ((oddFactor (k - j) : ℕ) : ℚ) ^ 2 := by
  have he : (j + 1) + (k - j) = k + 1 := by omega
  have hr : root k / root j = (2 : ℚ) ^ (k - j) := by
    rw [root, root]
    calc
      (2 : ℚ) ^ (k + 1) / (2 : ℚ) ^ (j + 1) =
          ((2 : ℚ) ^ (j + 1) * (2 : ℚ) ^ (k - j)) /
            (2 : ℚ) ^ (j + 1) := by rw [← pow_add, he]
      _ = (2 : ℚ) ^ (k - j) := by field_simp
  rw [hr]
  simp only [oddFactor]
  have hp : 1 ≤ 2 ^ (k - j) := one_le_pow₀ (by omega)
  rw [Nat.cast_sub hp]
  push_cast
  ring

lemma lower_product (k : ℕ) :
    (∏ j ∈ Finset.range k, (1 - root k / root j) ^ 2) =
      (denProd k : ℚ) ^ 2 := by
  calc
    _ = ∏ j ∈ Finset.range k, (((oddFactor (k - j) : ℕ) : ℚ) ^ 2) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact lower_factor (Finset.mem_range.mp hj)
    _ = ∏ d ∈ Finset.Icc 1 k, (((oddFactor d : ℕ) : ℚ) ^ 2) := by
      simpa only using
        (ZV.prod_range_reverse_Icc (fun d ↦ (((oddFactor d : ℕ) : ℚ) ^ 2)) k)
    _ = (denProd k : ℚ) ^ 2 := by
      simp only [denProd, Nat.cast_prod, Finset.prod_pow]

lemma upper_factor {k j : ℕ} (hkj : k < j) :
    (1 - root k / root j) ^ 2 =
      (((oddFactor (j - k) : ℕ) : ℚ) ^ 2) /
        (2 : ℚ) ^ (2 * (j - k)) := by
  have he : (k + 1) + (j - k) = j + 1 := by omega
  have hpow : (2 : ℚ) ^ (j + 1) =
      (2 : ℚ) ^ (k + 1) * (2 : ℚ) ^ (j - k) := by
    rw [← pow_add, he]
  have hr : root k / root j = 1 / (2 : ℚ) ^ (j - k) := by
    rw [root, root, hpow]
    field_simp
  rw [hr]
  simp only [oddFactor]
  have hp : 1 ≤ 2 ^ (j - k) := one_le_pow₀ (by omega)
  rw [Nat.cast_sub hp]
  push_cast
  have hpow2 : (2 : ℚ) ^ (2 * (j - k)) = ((2 : ℚ) ^ (j - k)) ^ 2 := by
    rw [show 2 * (j - k) = (j - k) + (j - k) by omega, pow_add, pow_two]
  rw [hpow2]
  field_simp [pow_ne_zero]

lemma prod_Icc_sub {M : Type*} [CommMonoid M] (f : ℕ → M) (n k : ℕ)
    (hk : k ≤ n) :
    ∏ j ∈ Finset.Icc (k + 1) n, f (j - k) =
      ∏ d ∈ Finset.Icc 1 (n - k), f d := by
  apply Finset.prod_bij (fun j _hj ↦ j - k)
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [Finset.mem_Icc] at hj₁ hj₂
    omega
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    refine ⟨d + k, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro j hj
    rfl

lemma sum_Icc_id (m : ℕ) :
    ∑ d ∈ Finset.Icc 1 m, d = m * (m + 1) / 2 := by
  have hs : ∑ d ∈ Finset.Icc 1 m, d = ∑ d ∈ Finset.range (m + 1), d := by
    apply Finset.sum_subset
    · intro d hd
      simp only [Finset.mem_Icc, Finset.mem_range] at hd ⊢
      omega
    · intro d hd hnot
      simp only [Finset.mem_range] at hd
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
      have : d = 0 := by omega
      simp [this]
  rw [hs]
  simpa [Nat.mul_comm] using (Finset.sum_range_id (n := m + 1))

lemma sum_Icc_twice (m : ℕ) :
    ∑ d ∈ Finset.Icc 1 m, 2 * d = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
      ring

lemma upper_product {n k : ℕ} (hk : k ≤ n) :
    (∏ j ∈ Finset.Icc (k + 1) n, (1 - root k / root j) ^ 2) =
      (denProd (n - k) : ℚ) ^ 2 /
        (2 : ℚ) ^ ((n - k) * (n - k + 1)) := by
  calc
    _ = ∏ j ∈ Finset.Icc (k + 1) n,
        (((oddFactor (j - k) : ℕ) : ℚ) ^ 2 /
          (2 : ℚ) ^ (2 * (j - k))) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      exact upper_factor (by omega : k < j)
    _ = ∏ d ∈ Finset.Icc 1 (n - k),
        (((oddFactor d : ℕ) : ℚ) ^ 2 / (2 : ℚ) ^ (2 * d)) := by
      simpa only using
        (prod_Icc_sub
          (fun d ↦ (((oddFactor d : ℕ) : ℚ) ^ 2 / (2 : ℚ) ^ (2 * d))) n k hk)
    _ = (∏ d ∈ Finset.Icc 1 (n - k), (((oddFactor d : ℕ) : ℚ) ^ 2)) /
        (∏ d ∈ Finset.Icc 1 (n - k), (2 : ℚ) ^ (2 * d)) := by
      rw [Finset.prod_div_distrib]
    _ = (denProd (n - k) : ℚ) ^ 2 /
        (2 : ℚ) ^ (∑ d ∈ Finset.Icc 1 (n - k), 2 * d) := by
      congr 1
      · simp only [denProd, Nat.cast_prod, Finset.prod_pow]
      · rw [Finset.prod_pow_eq_pow_sum]
    _ = _ := by
      congr 2
      rw [sum_Icc_twice]

lemma denominator_product {n k : ℕ} (hk : k ≤ n) :
    (∏ j ∈ (Finset.range (n + 1)).erase k,
        (1 - root k / root j) ^ 2) =
      (denProd k : ℚ) ^ 2 * (denProd (n - k) : ℚ) ^ 2 /
        (2 : ℚ) ^ ((n - k) * (n - k + 1)) := by
  rw [erased_range_eq_union hk, Finset.prod_union]
  · rw [lower_product, upper_product hk]
    ring
  · exact Finset.disjoint_left.mpr fun j hj₁ hj₂ ↦ by
      simp only [Finset.mem_range] at hj₁
      simp only [Finset.mem_Icc] at hj₂
      omega

def lambda (n : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * (denProd n : ℚ) /
    (2 : ℚ) ^ (n ^ 2 + 2 * n + 1)

theorem lambda_root_mul_vCoeff_eq_cCoeff {n k : ℕ} (hk : k ≤ n) :
    lambda n * root k * vCoeff n k = cCoeff n k := by
  rw [lambda, vCoeff_eq_products, ZV.numerator_prod_closed, denominator_product hk]
  simp only [cCoeff]
  push_cast
  have hdk : (denProd k : ℚ) ≠ 0 := by exact_mod_cast (ZV.denProd_pos k).ne'
  have hdnk : (denProd (n - k) : ℚ) ≠ 0 := by
    exact_mod_cast (ZV.denProd_pos (n - k)).ne'
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hgauss :
      (denProd n : ℚ) * (highProd k n : ℚ) =
        ((gauss2 n k : ℚ) ^ 2 * (gauss2 (n + k) k : ℚ)) *
          ((denProd k : ℚ) ^ 2 * (denProd (n - k) : ℚ) ^ 2) := by
    have h := ZV.gaussian_odd_identity hk
    field_simp [hdk, hdnk] at h
    nlinarith
  field_simp [root, hdk, hdnk, h2]
  have hsign : ((-1 : ℚ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  rw [hsign, one_mul]
  have hpower :
      root k * root k ^ n *
          (2 : ℚ) ^ ((n - k) * (n - k + 1)) *
          (2 : ℚ) ^ (k * (n - k)) =
        (2 : ℚ) ^ (n ^ 2 + 2 * n + 1) := by
    rw [root, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    have hn : n = k + (n - k) := by omega
    rw [hn]
    simp only [Nat.add_sub_cancel_left]
    ring
  calc
    (denProd n : ℚ) * root k * root k ^ n * (highProd k n : ℚ) *
          (2 : ℚ) ^ ((n - k) * (n - k + 1)) *
          (2 : ℚ) ^ (k * (n - k)) =
        ((denProd n : ℚ) * (highProd k n : ℚ)) *
          (root k * root k ^ n *
            (2 : ℚ) ^ ((n - k) * (n - k + 1)) *
            (2 : ℚ) ^ (k * (n - k))) := by ring
    _ = (((gauss2 n k : ℚ) ^ 2 * (gauss2 (n + k) k : ℚ)) *
          ((denProd k : ℚ) ^ 2 * (denProd (n - k) : ℚ) ^ 2)) *
          (root k * root k ^ n *
            (2 : ℚ) ^ ((n - k) * (n - k + 1)) *
            (2 : ℚ) ^ (k * (n - k))) := by rw [hgauss]
    _ = (2 : ℚ) ^ (n ^ 2 + 2 * n + 1) * (denProd k : ℚ) ^ 2 *
          (denProd (n - k) : ℚ) ^ 2 * (gauss2 n k : ℚ) ^ 2 *
          (gauss2 (n + k) k : ℚ) := by rw [hpower]; ring

end VNormalization

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250/Erdos250RawLogDeriv.lean` -/

section
open scoped BigOperators

namespace DoublePartialFraction.OldRational

lemma oddFactorQ_eq_arithmetic_cast (d : ℕ) (hd : 1 ≤ d) :
    oddFactorQ d = (Erdos250Arithmetic.oddFactor d : ℕ) := by
  rw [oddFactorQ, Erdos250Arithmetic.oddFactor, Nat.cast_sub]
  · norm_num
  · exact one_le_pow₀ (by omega)

theorem rawLogDeriv_eq_arithmetic_logDerivCoeff
    (n k : ℕ) (hk : k ≤ n) :
    rawLogDeriv n k = Erdos250Arithmetic.logDerivCoeff n k := by
  rw [rawLogDeriv_eq_targetLogDeriv n k hk]
  have hhigh :
      (∑ d ∈ Finset.Icc (k + 1) (n + k),
          (2 : ℚ) ^ d / oddFactorQ d) =
        ∑ d ∈ Finset.Icc (k + 1) (n + k),
          ((2 ^ d : ℕ) : ℚ) / (Erdos250Arithmetic.oddFactor d : ℕ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [oddFactorQ_eq_arithmetic_cast d (by
      have hd' := (Finset.mem_Icc.mp hd).1
      omega)]
    norm_num
  have hlowHigh :
      (∑ d ∈ Finset.Icc 1 k, (2 : ℚ) ^ d / oddFactorQ d) =
        ∑ d ∈ Finset.Icc 1 k,
          ((2 ^ d : ℕ) : ℚ) / (Erdos250Arithmetic.oddFactor d : ℕ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [oddFactorQ_eq_arithmetic_cast d (Finset.mem_Icc.mp hd).1]
    norm_num
  have hlow :
      (∑ d ∈ Finset.Icc 1 (n - k), (1 : ℚ) / oddFactorQ d) =
        ∑ d ∈ Finset.Icc 1 (n - k),
          (1 : ℚ) / (Erdos250Arithmetic.oddFactor d : ℕ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [oddFactorQ_eq_arithmetic_cast d (Finset.mem_Icc.mp hd).1]
  rw [targetLogDeriv, Erdos250Arithmetic.logDerivCoeff, hhigh, hlowHigh, hlow]

end DoublePartialFraction.OldRational

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250/Erdos250ShiftedSums.lean` -/

section
open scoped BigOperators Topology

namespace ShiftedSums

noncomputable def q : ℝ := 1 / 2

noncomputable def zetaQ1 : ℝ :=
  ∑' m : ℕ, q ^ (m + 1) / (1 - q ^ (m + 1))

noncomputable def zetaQ2sq : ℝ :=
  ∑' m : ℕ, q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2

/-- The convention used by the main Erdős 250 file. -/
noncomputable def zetaQ2 : ℝ :=
  ∑' n : ℕ+, (n : ℝ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))

noncomputable def h1 (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (j - 1), q ^ (m + 1) / (1 - q ^ (m + 1))

noncomputable def h2 (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (j - 1), q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2

lemma q_pos : 0 < q := by norm_num [q]
lemma q_le_one : q ≤ 1 := by norm_num [q]
lemma q_ne_zero : q ≠ 0 := ne_of_gt q_pos

lemma q_pow_succ_le (m : ℕ) : q ^ (m + 1) ≤ q := by
  simpa [pow_succ] using mul_le_of_le_one_left (le_of_lt q_pos) (pow_le_one₀ (le_of_lt q_pos) q_le_one)

lemma half_le_one_sub_q_pow_succ (m : ℕ) : (1 / 2 : ℝ) ≤ 1 - q ^ (m + 1) := by
  have := q_pow_succ_le m
  norm_num [q] at this ⊢
  linarith

lemma base1_nonneg (m : ℕ) :
    0 ≤ q ^ (m + 1) / (1 - q ^ (m + 1)) := by
  exact div_nonneg (pow_nonneg (le_of_lt q_pos) _) (by linarith [half_le_one_sub_q_pow_succ m])

lemma base1_le (m : ℕ) :
    q ^ (m + 1) / (1 - q ^ (m + 1)) ≤ 2 * q ^ (m + 1) := by
  have hp : 0 ≤ q ^ (m + 1) := pow_nonneg (le_of_lt q_pos) _
  have hd := half_le_one_sub_q_pow_succ m
  apply (div_le_iff₀ (by linarith : 0 < 1 - q ^ (m + 1))).2
  nlinarith

lemma base2_nonneg (m : ℕ) :
    0 ≤ q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2 := by
  exact div_nonneg (pow_nonneg (le_of_lt q_pos) _) (sq_nonneg _)

lemma base2_le (m : ℕ) :
    q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2 ≤ 4 * q ^ (m + 1) := by
  have hp : 0 ≤ q ^ (m + 1) := pow_nonneg (le_of_lt q_pos) _
  have hd := half_le_one_sub_q_pow_succ m
  have hsq : (1 / 4 : ℝ) ≤ (1 - q ^ (m + 1)) ^ 2 := by nlinarith
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 - q ^ (m + 1)))).2
  nlinarith

lemma summable_base1 :
    Summable (fun m : ℕ => q ^ (m + 1) / (1 - q ^ (m + 1))) := by
  apply Summable.of_nonneg_of_le base1_nonneg base1_le
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
    (summable_geometric_of_norm_lt_one (K := ℝ) (x := q) (by norm_num [q])).mul_left (2 * q)

lemma summable_base2 :
    Summable (fun m : ℕ => q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2) := by
  apply Summable.of_nonneg_of_le base2_nonneg base2_le
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
    (summable_geometric_of_norm_lt_one (K := ℝ) (x := q) (by norm_num [q])).mul_left (4 * q)

lemma tsum_pnat_mul_pow (d : ℕ+) :
    (∑' c : ℕ+, (c : ℝ) * q ^ ((d : ℕ) * (c : ℕ))) =
      q ^ (d : ℕ) / (1 - q ^ (d : ℕ)) ^ 2 := by
  let r : ℝ := q ^ (d : ℕ)
  have hr : ‖r‖ < 1 := by
    dsimp [r]
    simpa [Real.norm_eq_abs, abs_of_pos q_pos] using
      pow_lt_one₀ (le_of_lt q_pos) (by norm_num [q] : q < 1) d.ne_zero
  have hs : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have hpnat := tsum_zero_pnat_eq_tsum_nat hs
  simp only [Nat.cast_zero, zero_mul, zero_add] at hpnat
  calc
    (∑' c : ℕ+, (c : ℝ) * q ^ ((d : ℕ) * (c : ℕ))) =
        ∑' c : ℕ+, (c : ℝ) * r ^ (c : ℕ) := by
          apply tsum_congr
          intro c
          simp [r, pow_mul]
    _ = ∑' n : ℕ, (n : ℝ) * r ^ n := hpnat
    _ = r / (1 - r) ^ 2 := tsum_coe_mul_geometric_of_norm_lt_one hr
    _ = q ^ (d : ℕ) / (1 - q ^ (d : ℕ)) ^ 2 := by rfl

/-- Euler symmetry in the two indices: the square-denominator convention for
`ζ_q(2)` agrees with the convention carrying a factor `n`. -/
lemma zetaQ2sq_eq_zetaQ2 : zetaQ2sq = zetaQ2 := by
  have hq : ‖q‖ < 1 := by norm_num [q]
  calc
    zetaQ2sq = ∑' d : ℕ+, q ^ (d : ℕ) / (1 - q ^ (d : ℕ)) ^ 2 := by
      rw [zetaQ2sq]
      symm
      exact (tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => q ^ n / (1 - q ^ n) ^ 2))
    _ = ∑' d : ℕ+, ∑' c : ℕ+,
          (c : ℝ) ^ (1 : ℕ) * q ^ ((d : ℕ) * (c : ℕ)) := by
      apply tsum_congr
      intro d
      simpa using (tsum_pnat_mul_pow d).symm
    _ = ∑' e : ℕ+, (ArithmeticFunction.sigma 1 e : ℝ) * q ^ (e : ℕ) :=
      tsum_prod_pow_eq_tsum_sigma 1 hq
    _ = zetaQ2 := by
      rw [zetaQ2]
      symm
      simpa using tsum_pow_div_one_sub_eq_tsum_sigma hq 1

lemma shifted_one (j : ℕ) (hj : 1 ≤ j) :
    (∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell))) =
      (zetaQ1 - h1 j) / q ^ j := by
  let f : ℕ → ℝ := fun m => q ^ (m + 1) / (1 - q ^ (m + 1))
  have htail := summable_base1.sum_add_tsum_nat_add (j - 1)
  have hj' : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have hpoint : ∀ ell : ℕ,
      f (ell + (j - 1)) = q ^ j * (q ^ ell / (1 - q ^ (j + ell))) := by
    intro ell
    simp only [f]
    rw [show ell + (j - 1) + 1 = ell + j by omega]
    rw [show j + ell = ell + j by omega, pow_add]
    ring
  have hqpow : q ^ j ≠ 0 := pow_ne_zero _ q_ne_zero
  rw [show (∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell))) =
      (∑' ell : ℕ, f (ell + (j - 1))) / q ^ j by
        rw [show (∑' ell : ℕ, f (ell + (j - 1))) =
            q ^ j * ∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell)) by
          simp_rw [hpoint]
          exact tsum_mul_left]
        field_simp]
  have htail' : (∑' i : ℕ, f (i + (j - 1))) = zetaQ1 - h1 j := by
    dsimp [f, zetaQ1, h1]
    linarith
  rw [htail']

lemma shifted_two (j : ℕ) (hj : 1 ≤ j) :
    (∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell)) ^ 2) =
      (zetaQ2sq - h2 j) / q ^ j := by
  let f : ℕ → ℝ := fun m => q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2
  have htail := summable_base2.sum_add_tsum_nat_add (j - 1)
  have hpoint : ∀ ell : ℕ,
      f (ell + (j - 1)) = q ^ j * (q ^ ell / (1 - q ^ (j + ell)) ^ 2) := by
    intro ell
    simp only [f]
    rw [show ell + (j - 1) + 1 = ell + j by omega]
    rw [show j + ell = ell + j by omega, pow_add]
    ring
  have hqpow : q ^ j ≠ 0 := pow_ne_zero _ q_ne_zero
  rw [show (∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell)) ^ 2) =
      (∑' ell : ℕ, f (ell + (j - 1))) / q ^ j by
        rw [show (∑' ell : ℕ, f (ell + (j - 1))) =
            q ^ j * ∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell)) ^ 2 by
          simp_rw [hpoint]
          exact tsum_mul_left]
        field_simp]
  have htail' : (∑' i : ℕ, f (i + (j - 1))) = zetaQ2sq - h2 j := by
    dsimp [f, zetaQ2sq, h2]
    linarith
  rw [htail']

/-- The second shifted identity stated using the main file's convention for
`zetaQ2`. -/
lemma shifted_two_zetaQ2 (j : ℕ) (hj : 1 ≤ j) :
    (∑' ell : ℕ, q ^ ell / (1 - q ^ (j + ell)) ^ 2) =
      (zetaQ2 - h2 j) / q ^ j := by
  rw [← zetaQ2sq_eq_zetaQ2]
  exact shifted_two j hj

end ShiftedSums

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250/Erdos250ScaledDecay.lean` -/

section
open Filter
open scoped Topology

lemma half_quadratic_exponent (n : ℕ) (hn : 8 ≤ n) :
    n + 2 + n / 2 ≤ (n / 2) * (n / 2 + 1) := by
  have hfloor : n ≤ 2 * (n / 2) + 1 := by omega
  have hhalf : 4 ≤ n / 2 := by omega
  nlinarith

lemma scaled_decay_le (n : ℕ) (hn : 8 ≤ n) :
    (2 : ℝ) ^ (n + 2) / (2 : ℝ) ^ ((n / 2) * (n / 2 + 1)) ≤
      ((1 : ℝ) / 2) ^ (n / 2) := by
  rw [one_div_pow]
  apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ ((n / 2) * (n / 2 + 1)))
    (by positivity : 0 < (2 : ℝ) ^ (n / 2))).2
  rw [one_mul, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (half_quadratic_exponent n hn)

lemma tendsto_half_scaled_decay :
    Tendsto
      (fun n : ℕ ↦
        (2 : ℝ) ^ (n + 2) / (2 : ℝ) ^ ((n / 2) * (n / 2 + 1)))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun n ↦ by positivity)
  · filter_upwards [eventually_ge_atTop 8] with n hn
    exact scaled_decay_le n hn
  · simpa [Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)).comp
          (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))

lemma tendsto_half_scaled_decay_zpow :
    Tendsto
      (fun n : ℕ ↦
        (2 : ℝ) ^
          (((n + 2 : ℕ) : ℤ) - (((n / 2) * (n / 2 + 1) : ℕ) : ℤ)))
      atTop (nhds 0) := by
  convert tendsto_half_scaled_decay using 1
  ext n
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]

lemma old_quadratic_exponent (n : ℕ) (hn : 12 ≤ n) :
    2 * n + 3 + n / 2 ≤ (n / 2) * (n / 2 + 1) := by
  have hfloor : n ≤ 2 * (n / 2) + 1 := by omega
  have hhalf : 6 ≤ n / 2 := by omega
  nlinarith

lemma old_scaled_decay_le (n : ℕ) (hn : 12 ≤ n) :
    ((4 : ℝ) / 3) ^ (2 * n + 3) *
        (2 : ℝ) ^ (-(((n / 2) * (n / 2 + 1) : ℕ) : ℤ)) ≤
      ((1 : ℝ) / 2) ^ (n / 2) := by
  rw [zpow_neg, zpow_natCast, inv_eq_one_div, one_div_pow]
  calc
    ((4 : ℝ) / 3) ^ (2 * n + 3) *
          (1 / (2 : ℝ) ^ ((n / 2) * (n / 2 + 1)))
        ≤ (2 : ℝ) ^ (2 * n + 3) *
          (1 / (2 : ℝ) ^ ((n / 2) * (n / 2 + 1))) := by
            gcongr
            norm_num
    _ = (2 : ℝ) ^ (2 * n + 3) /
          (2 : ℝ) ^ ((n / 2) * (n / 2 + 1)) := by ring
    _ ≤ 1 / (2 : ℝ) ^ (n / 2) := by
      apply (div_le_div_iff₀
        (by positivity : 0 < (2 : ℝ) ^ ((n / 2) * (n / 2 + 1)))
        (by positivity : 0 < (2 : ℝ) ^ (n / 2))).2
      rw [one_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (old_quadratic_exponent n hn)

lemma tendsto_old_scaled_decay :
    Tendsto
      (fun n : ℕ ↦
        ((4 : ℝ) / 3) ^ (2 * n + 3) *
          (2 : ℝ) ^ (-(((n / 2) * (n / 2 + 1) : ℕ) : ℤ)))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun n ↦ by positivity)
  · filter_upwards [eventually_ge_atTop 12] with n hn
    exact old_scaled_decay_le n hn
  · simpa [Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)).comp
          (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250/Erdos250Core.lean` -/

section
open scoped ArithmeticFunction.sigma

namespace Erdos250Scratch

noncomputable section

def sigmaTerm (n : ℕ) : ℝ := (ArithmeticFunction.sigma 1 n : ℝ) / (2 : ℝ) ^ n

def lambertTerm (n : ℕ+) : ℝ := (n : ℝ) / ((2 : ℝ) ^ (n : ℕ) - 1)

lemma raw_eq_lambert (n : ℕ+) :
    (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ (n : ℕ) /
        (1 - (1 / 2 : ℝ) ^ (n : ℕ)) = lambertTerm n := by
  rw [pow_one, one_div_pow]
  simp only [lambertTerm]
  have hn : (n : ℕ) ≠ 0 := n.ne_zero
  have hpow : (2 : ℝ) ^ (n : ℕ) ≠ 1 :=
    (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hn).ne'
  field_simp

lemma raw_sigma_eq_sigmaTerm (n : ℕ+) :
    (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (n : ℕ) =
      sigmaTerm n := by
  simp [sigmaTerm, div_eq_mul_inv]

lemma sigmaTerm_nonneg (n : ℕ) : 0 ≤ sigmaTerm n := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

lemma sigmaTerm_summable : Summable sigmaTerm := by
  have hpoly : Summable (fun n : ℕ => (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ n) := by
    simpa [Real.norm_of_nonneg] using
      (summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
        (r := (1 / 2 : ℝ)) (by norm_num))
  refine hpoly.of_nonneg_of_le sigmaTerm_nonneg (fun n => ?_)
  rw [sigmaTerm, div_eq_mul_inv, ← inv_pow]
  have hs : (ArithmeticFunction.sigma 1 n : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 n
  norm_num at hs ⊢
  exact hs

lemma lambertTerm_summable : Summable lambertTerm := by
  have hraw : Summable (fun n : ℕ =>
      (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ n / (1 - (1 / 2 : ℝ) ^ n)) :=
    summable_norm_pow_mul_geometric_div_one_sub 1 (by norm_num)
  have hsub : Summable (fun n : ℕ+ =>
      (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ (n : ℕ) /
        (1 - (1 / 2 : ℝ) ^ (n : ℕ))) := hraw.subtype _
  exact hsub.congr raw_eq_lambert

lemma tsum_lambert_eq_tsum_sigma_pnat :
    (∑' n : ℕ+, lambertTerm n) =
      ∑' n : ℕ+, sigmaTerm n := by
  calc
    (∑' n : ℕ+, lambertTerm n) =
        ∑' n : ℕ+, (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ (n : ℕ) /
          (1 - (1 / 2 : ℝ) ^ (n : ℕ)) :=
      tsum_congr fun n => (raw_eq_lambert n).symm
    _ = ∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) *
          (1 / 2 : ℝ) ^ (n : ℕ) :=
      tsum_pow_div_one_sub_eq_tsum_sigma (𝕜 := ℝ) (r := (1 / 2 : ℝ))
        (by norm_num) 1
    _ = ∑' n : ℕ+, sigmaTerm n :=
      tsum_congr raw_sigma_eq_sigmaTerm

lemma tsum_sigma_pnat_eq_tsum_nat :
    (∑' n : ℕ+, sigmaTerm n) = ∑' n : ℕ, sigmaTerm n := by
  have h := tsum_zero_pnat_eq_tsum_nat sigmaTerm_summable
  simpa [sigmaTerm] using h

theorem tsum_lambert_eq_tsum_sigma :
    (∑' n : ℕ+, lambertTerm n) = ∑' n : ℕ, sigmaTerm n :=
  tsum_lambert_eq_tsum_sigma_pnat.trans tsum_sigma_pnat_eq_tsum_nat

theorem hasSum_sigma_to_lambert {x : ℝ} (hx : HasSum sigmaTerm x) :
    HasSum lambertTerm x := by
  rw [← hx.tsum_eq, ← tsum_lambert_eq_tsum_sigma]
  exact lambertTerm_summable.hasSum

theorem hasSum_sigma_iff_lambert {x : ℝ} :
    HasSum sigmaTerm x ↔ HasSum lambertTerm x := by
  constructor
  · exact hasSum_sigma_to_lambert
  · intro hx
    rw [← hx.tsum_eq, tsum_lambert_eq_tsum_sigma]
    exact sigmaTerm_summable.hasSum

/-- Directly usable with the function in the formal-conjectures statement. -/
theorem hasSum_erdos250_to_lambert {x : ℝ}
    (hx : HasSum (fun n : ℕ =>
      (ArithmeticFunction.sigma 1 n : ℝ) / (2 : ℝ) ^ n) x) :
    HasSum (fun n : ℕ+ =>
      (n : ℝ) / ((2 : ℝ) ^ (n : ℕ) - 1)) x := by
  change HasSum sigmaTerm x at hx
  change HasSum lambertTerm x
  exact hasSum_sigma_to_lambert hx

theorem hasSum_erdos250_iff_lambert {x : ℝ} :
    HasSum (fun n : ℕ =>
      (ArithmeticFunction.sigma 1 n : ℝ) / (2 : ℝ) ^ n) x ↔
    HasSum (fun n : ℕ+ =>
      (n : ℝ) / ((2 : ℝ) ^ (n : ℕ) - 1)) x := by
  change HasSum sigmaTerm x ↔ HasSum lambertTerm x
  exact hasSum_sigma_iff_lambert

/-! A denominator-sensitive irrationality criterion for integer linear forms. -/

theorem irrational_of_arbitrarily_small_integer_linear_forms (x : ℝ)
    (hsmall : ∀ d : ℕ, 0 < d → ∃ a b : ℤ,
      0 < |(a : ℝ) * x + (b : ℝ)| ∧
        |(a : ℝ) * x + (b : ℝ)| < 1 / (d : ℝ)) :
    Irrational x := by
  by_contra hx
  obtain ⟨r : ℚ, hr⟩ := exists_rat_of_not_irrational hx
  obtain ⟨a, b, hpos, hlt⟩ := hsmall r.den r.den_pos
  let z : ℤ := a * r.num + b * (r.den : ℤ)
  have hform : (a : ℝ) * x + (b : ℝ) = (z : ℝ) / (r.den : ℝ) := by
    rw [hr, Rat.cast_def]
    simp only [z, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    field_simp [r.den_nz]
  have hz : z ≠ 0 := by
    intro hz
    rw [hform, hz] at hpos
    norm_num at hpos
  have hzabs : (1 : ℝ) ≤ |(z : ℝ)| := by
    exact_mod_cast Int.one_le_abs hz
  have hdpos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hlower : 1 / (r.den : ℝ) ≤ |(a : ℝ) * x + (b : ℝ)| := by
    rw [hform, abs_div, abs_of_pos hdpos]
    exact (div_le_div_iff_of_pos_right hdpos).2 hzabs
  exact (not_lt_of_ge hlower) hlt

theorem irrational_of_integer_linear_forms_tendsto_zero (x : ℝ)
    (a b : ℕ → ℤ)
    (hne : ∀ᶠ n in Filter.atTop, (a n : ℝ) * x + (b n : ℝ) ≠ 0)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ) * x + (b n : ℝ))
      Filter.atTop (nhds 0)) :
    Irrational x := by
  apply irrational_of_arbitrarily_small_integer_linear_forms x
  intro d hd
  have hdreal : (0 : ℝ) < 1 / (d : ℝ) := by positivity
  have hevent : ∀ᶠ n in Filter.atTop,
      |(a n : ℝ) * x + (b n : ℝ)| < 1 / (d : ℝ) := by
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨N, hN⟩ := hlim (1 / (d : ℝ)) hdreal
    exact Filter.eventually_atTop.2 ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hne.and hevent)
  have hN' := hN N le_rfl
  exact ⟨a N, b N, abs_pos.2 hN'.1, hN'.2⟩

end

end Erdos250Scratch

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250/Erdos250OldDecay.lean` -/

section
open scoped BigOperators

namespace OldDecayFull

open Erdos250Arithmetic VNormalization

lemma denProd_le_pow_two_tri (n : ℕ) :
    denProd n ≤ 2 ^ (n * (n + 1) / 2) := by
  rw [denProd]
  calc
    ∏ d ∈ Finset.Icc 1 n, oddFactor d ≤
        ∏ d ∈ Finset.Icc 1 n, 2 ^ d := by
      apply Finset.prod_le_prod'
      intro d hd
      exact Nat.sub_le _ _
    _ = 2 ^ (∑ d ∈ Finset.Icc 1 n, d) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = 2 ^ (n * (n + 1) / 2) := by
      rw [VNormalization.sum_Icc_id]

end OldDecayFull

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250/Erdos250OldScaledLinearForm.lean` -/

section
open Filter
open scoped Topology

namespace OldScaledLinearForm

open Erdos250Arithmetic

noncomputable def E (n : ℕ) : ℕ :=
  2 ^ (n ^ 2 / 4) * denProd n ^ 2

def tri (n : ℕ) : ℕ := n * (n + 1) / 2

def halfSquare (n : ℕ) : ℕ := (n / 2) * (n / 2 + 1)

lemma twice_tri (n : ℕ) : 2 * tri n = n * (n + 1) := by
  exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)

lemma E_cast_le (n : ℕ) :
    (E n : ℝ) ≤ (2 : ℝ) ^ (n ^ 2 / 4 + 2 * tri n) := by
  have hd : (denProd n : ℝ) ≤ (2 : ℝ) ^ tri n := by
    exact_mod_cast OldDecayFull.denProd_le_pow_two_tri n
  rw [E]
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc
    (2 : ℝ) ^ (n ^ 2 / 4) * (denProd n : ℝ) ^ 2 ≤
        (2 : ℝ) ^ (n ^ 2 / 4) * ((2 : ℝ) ^ tri n) ^ 2 := by
      gcongr
    _ = (2 : ℝ) ^ (n ^ 2 / 4 + 2 * tri n) := by
      rw [← pow_mul, ← pow_add]
      congr 2 <;> omega

lemma abs_cast_lambda (n : ℕ) :
    |((VNormalization.lambda n : ℚ) : ℝ)| =
      (denProd n : ℝ) / (2 : ℝ) ^ (n ^ 2 + 2 * n + 1) := by
  rw [VNormalization.lambda]
  push_cast
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _), abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

lemma abs_cast_lambda_le (n : ℕ) :
    |((VNormalization.lambda n : ℚ) : ℝ)| ≤
      (2 : ℝ) ^ (((tri n : ℕ) : ℤ) - ((n ^ 2 + 2 * n + 1 : ℕ) : ℤ)) := by
  rw [abs_cast_lambda]
  have hd : (denProd n : ℝ) ≤ (2 : ℝ) ^ tri n := by
    exact_mod_cast OldDecayFull.denProd_le_pow_two_tri n
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]
  exact div_le_div_of_nonneg_right hd (by positivity)

lemma exponent_le (n : ℕ) :
    (((n ^ 2 / 4 + 2 * tri n : ℕ) : ℤ) +
          ((tri n : ℕ) : ℤ) - ((n ^ 2 + 2 * n + 1 : ℕ) : ℤ) -
          ((n * (n + 1) : ℕ) : ℤ)) ≤
      -((halfSquare n : ℕ) : ℤ) := by
  have hsq : 4 * (n ^ 2 / 4) ≤ n ^ 2 := Nat.mul_div_le _ _
  have ht := twice_tri n
  have hn : n ≤ 2 * (n / 2) + 1 := by omega
  have hn' : 2 * (n / 2) ≤ n := by omega
  have hnat : n ^ 2 / 4 + 2 * tri n + tri n + halfSquare n ≤
      n ^ 2 + 2 * n + 1 + n * (n + 1) := by
    simp only [tri, halfSquare] at ht ⊢
    nlinarith
  have hnatZ :
      ((n ^ 2 / 4 + 2 * tri n + tri n + halfSquare n : ℕ) : ℤ) ≤
        ((n ^ 2 + 2 * n + 1 + n * (n + 1) : ℕ) : ℤ) := by
    exact_mod_cast hnat
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hnatZ ⊢
  omega

lemma scaled_abs_le {n : ℕ} (hn : 1 ≤ n) :
    (E n : ℝ) * |((VNormalization.lambda n : ℚ) : ℝ)| * QApery.S n ≤
      ((4 : ℝ) / 3) ^ (2 * n + 3) *
        (2 : ℝ) ^ (-((halfSquare n : ℕ) : ℤ)) := by
  have hE := E_cast_le n
  have hl := abs_cast_lambda_le n
  have hS := QApery.S_le_explicit hn
  have hS' : QApery.S n ≤
      ((4 : ℝ) / 3) ^ (2 * n + 3) *
        (2 : ℝ) ^ (-((n * (n + 1) : ℕ) : ℤ)) := by
    rw [show (2 : ℝ) ^ (-((n * (n + 1) : ℕ) : ℤ)) =
        QApery.q ^ (n * (n + 1)) by
          rw [show QApery.q = (2 : ℝ)⁻¹ by norm_num [QApery.q], inv_pow,
            zpow_neg, zpow_natCast]]
    exact hS
  calc
    (E n : ℝ) * |((VNormalization.lambda n : ℚ) : ℝ)| * QApery.S n ≤
        (2 : ℝ) ^ (n ^ 2 / 4 + 2 * tri n) *
          (2 : ℝ) ^ (((tri n : ℕ) : ℤ) - ((n ^ 2 + 2 * n + 1 : ℕ) : ℤ)) *
          (((4 : ℝ) / 3) ^ (2 * n + 3) *
            (2 : ℝ) ^ (-((n * (n + 1) : ℕ) : ℤ))) := by
      have hleft := mul_le_mul hE hl (abs_nonneg _)
        (by positivity : 0 ≤ (2 : ℝ) ^ (n ^ 2 / 4 + 2 * tri n))
      exact mul_le_mul hleft hS' (le_of_lt (QApery.S_pos hn))
        (mul_nonneg (by positivity) (by positivity))
    _ = ((4 : ℝ) / 3) ^ (2 * n + 3) *
          (2 : ℝ) ^
            (((n ^ 2 / 4 + 2 * tri n : ℕ) : ℤ) +
              ((tri n : ℕ) : ℤ) - ((n ^ 2 + 2 * n + 1 : ℕ) : ℤ) -
              ((n * (n + 1) : ℕ) : ℤ)) := by
      rw [show (2 : ℝ) ^ (n ^ 2 / 4 + 2 * tri n) =
          (2 : ℝ) ^ ((n ^ 2 / 4 + 2 * tri n : ℕ) : ℤ) by
            exact (zpow_natCast _ _).symm]
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [show (2 : ℝ) ^
          (((n ^ 2 / 4 + 2 * tri n : ℕ) : ℤ) +
            (((tri n : ℕ) : ℤ) - ((n ^ 2 + 2 * n + 1 : ℕ) : ℤ))) *
          (((4 : ℝ) / 3) ^ (2 * n + 3) *
            (2 : ℝ) ^ (-((n * (n + 1) : ℕ) : ℤ))) =
          ((4 : ℝ) / 3) ^ (2 * n + 3) *
            ((2 : ℝ) ^
              (((n ^ 2 / 4 + 2 * tri n : ℕ) : ℤ) +
                (((tri n : ℕ) : ℤ) - ((n ^ 2 + 2 * n + 1 : ℕ) : ℤ))) *
              (2 : ℝ) ^ (-((n * (n + 1) : ℕ) : ℤ))) by ring]
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 2 <;> ring
    _ ≤ ((4 : ℝ) / 3) ^ (2 * n + 3) *
          (2 : ℝ) ^ (-((halfSquare n : ℕ) : ℤ)) := by
      exact mul_le_mul_of_nonneg_left
        (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (exponent_le n))
        (by positivity)

theorem scaled_linear_form_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (E n : ℝ) * |((VNormalization.lambda n : ℚ) : ℝ)| * QApery.S n)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
      (le_of_lt (QApery.S_pos hn))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact scaled_abs_le hn
  · simpa [halfSquare] using tendsto_old_scaled_decay

end OldScaledLinearForm

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250/Erdos250Assemble.lean` -/

section
open Filter
open scoped BigOperators Topology



lemma ratCast_R (n : ℕ) (T : ℚ) :
    ((DoublePartialFraction.OldRational.R n T : ℚ) : ℝ) = QApery.R n (T : ℝ) := by
  simpa [DoublePartialFraction.OldRational.Rreal, QApery.R] using
    DoublePartialFraction.OldRational.cast_R n T

lemma q_real_eq_cast : ZPF.q = ((1 / 2 : ℚ) : ℝ) := by
  norm_num [ZPF.q]

lemma q_QApery_eq : QApery.q = ZPF.q := by
  norm_num [QApery.q, ZPF.q]

lemma qpow_rat_not_root (l j : ℕ) :
    (1 / 2 : ℚ) ^ l ≠ DoublePartialFraction.OldRational.root j := by
  have hleft : (1 / 2 : ℚ) ^ l ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hright : (1 : ℚ) < DoublePartialFraction.OldRational.root j := by
    rw [DoublePartialFraction.OldRational.root]
    exact one_lt_pow₀ (by norm_num) (by omega)
  exact ne_of_lt (hleft.trans_lt hright)

lemma partial_fraction_real (n l : ℕ) :
    QApery.R n (ZPF.q ^ l) =
      ∑ j ∈ Finset.range (n + 1),
        (((DoublePartialFraction.OldRational.uCoeff n j : ℚ) : ℝ) /
            (1 - ZPF.q ^ (j + 1 + l)) +
          ((DoublePartialFraction.OldRational.vCoeff n j : ℚ) : ℝ) /
            (1 - ZPF.q ^ (j + 1 + l)) ^ 2) := by
  have hpf := DoublePartialFraction.OldRational.partial_fraction_real n ((1 / 2 : ℚ) ^ l)
    (fun j _hj ↦ qpow_rat_not_root l j)
  rw [show DoublePartialFraction.OldRational.Rreal n
      (((1 / 2 : ℚ) ^ l : ℚ) : ℝ) = QApery.R n (ZPF.q ^ l) by
        congr 2
        push_cast
        norm_num [ZPF.q]] at hpf
  apply hpf.trans
  apply Finset.sum_congr rfl
  intro j hj
  have hratio : ZPF.q ^ l / (2 : ℝ) ^ (j + 1) =
      ZPF.q ^ (j + 1 + l) := by
    rw [show ZPF.q ^ l = 1 / (2 : ℝ) ^ l by simp [ZPF.q]]
    rw [show ZPF.q ^ (j + 1 + l) = 1 / (2 : ℝ) ^ (j + 1 + l) by
      simp [ZPF.q]]
    rw [div_div, ← pow_add]
    congr 2
    omega
  have hcastq : (((1 / 2 : ℚ) ^ l : ℚ) : ℝ) = ZPF.q ^ l := by
    push_cast
    norm_num [ZPF.q]
  rw [hcastq, hratio]

lemma partial_fraction_term (n l : ℕ) :
    ZPF.q ^ l * QApery.R n (ZPF.q ^ l) =
      ∑ j ∈ Finset.range (n + 1),
        ((((DoublePartialFraction.OldRational.uCoeff n j : ℚ) : ℝ) *
            (ZPF.q ^ l / (1 - ZPF.q ^ (j + 1 + l)))) +
          (((DoublePartialFraction.OldRational.vCoeff n j : ℚ) : ℝ) *
            (ZPF.q ^ l / (1 - ZPF.q ^ (j + 1 + l)) ^ 2))) := by
  rw [partial_fraction_real]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma q_zpow_neg_eq_root_cast (j : ℕ) :
    ZPF.q ^ (-(j + 1 : ℤ)) =
      ((DoublePartialFraction.OldRational.root j : ℚ) : ℝ) := by
  rw [show -(j + 1 : ℤ) = -((j + 1 : ℕ) : ℤ) by omega]
  rw [zpow_neg, zpow_natCast]
  simp [ZPF.q, DoublePartialFraction.OldRational.root]

lemma simple_pole_cancel_real (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
      ZPF.q ^ (-(j + 1 : ℤ)) *
        ((DoublePartialFraction.OldRational.uCoeff n j : ℚ) : ℝ) = 0 := by
  have h := congrArg (fun x : ℚ ↦ (x : ℝ))
    (DoublePartialFraction.OldRational.sum_root_mul_uCoeff_eq_zero n)
  push_cast at h
  simpa only [q_zpow_neg_eq_root_cast] using h

noncomputable def coeffC (n : ℕ) : ℝ :=
  ZPF.coeffC (n + 1)
    (fun j ↦ ((DoublePartialFraction.OldRational.vCoeff n j : ℚ) : ℝ))

noncomputable def coeffA (n : ℕ) : ℝ :=
  ZPF.coeffA (n + 1)
    (fun j ↦ ((DoublePartialFraction.OldRational.uCoeff n j : ℚ) : ℝ))
    (fun j ↦ ((DoublePartialFraction.OldRational.vCoeff n j : ℚ) : ℝ))

lemma S_eq_linear_form (n : ℕ) :
    QApery.S n = coeffC n * ZPF.lambert2 - coeffA n := by
  rw [QApery.S]
  change (∑' l : ℕ, ZPF.q ^ l * QApery.R n (ZPF.q ^ l)) = _
  exact ZPF.partialFractions_tsum (n + 1) (QApery.R n)
    (fun j ↦ ((DoublePartialFraction.OldRational.uCoeff n j : ℚ) : ℝ))
    (fun j ↦ ((DoublePartialFraction.OldRational.vCoeff n j : ℚ) : ℝ))
    (partial_fraction_term n) (simple_pole_cancel_real n)

noncomputable def lambda (n : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * (Erdos250Arithmetic.denProd n : ℚ) /
    (2 : ℚ) ^ (n ^ 2 + 2 * n + 1)

noncomputable def coeffCQ (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    DoublePartialFraction.OldRational.root j *
      DoublePartialFraction.OldRational.vCoeff n j

noncomputable def coeffAQ (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    DoublePartialFraction.OldRational.root j *
      (DoublePartialFraction.OldRational.uCoeff n j *
          Erdos250Arithmetic.hOne j +
        DoublePartialFraction.OldRational.vCoeff n j *
          Erdos250Arithmetic.hTwo j)

lemma cast_hOne_eq_eta (k : ℕ) :
    ((Erdos250Arithmetic.hOne k : ℚ) : ℝ) = ZPF.eta k := by
  induction k with
  | zero => simp [Erdos250Arithmetic.hOne, ZPF.eta]
  | succ k ih =>
      have hrec : Erdos250Arithmetic.hOne (k + 1) =
          Erdos250Arithmetic.hOne k +
            (1 : ℚ) / (Erdos250Arithmetic.oddFactor (k + 1) : ℕ) := by
        rw [Erdos250Arithmetic.hOne, Finset.sum_Icc_succ_top (by omega)]
        rfl
      have hrecEta : ZPF.eta (k + 1) = ZPF.eta k +
          ZPF.q ^ (k + 1) / (1 - ZPF.q ^ (k + 1)) := by
        rw [ZPF.eta, Finset.sum_range_succ]
        rfl
      rw [hrec, hrecEta, Rat.cast_add, ih]
      congr 1
      push_cast
      rw [show ZPF.q ^ (k + 1) = 1 / (2 : ℝ) ^ (k + 1) by simp [ZPF.q]]
      simp only [Erdos250Arithmetic.oddFactor]
      have hnat : 1 ≤ (2 : ℕ) ^ (k + 1) := one_le_pow₀ (by omega)
      rw [Nat.cast_sub hnat]
      push_cast
      have hp : (1 : ℝ) < (2 : ℝ) ^ (k + 1) :=
        one_lt_pow₀ (by norm_num) (by omega)
      field_simp [ne_of_gt hp]

lemma cast_hTwo_eq_theta (k : ℕ) :
    ((Erdos250Arithmetic.hTwo k : ℚ) : ℝ) = ZPF.theta k := by
  induction k with
  | zero => simp [Erdos250Arithmetic.hTwo, ZPF.theta]
  | succ k ih =>
      have hrec : Erdos250Arithmetic.hTwo (k + 1) =
          Erdos250Arithmetic.hTwo k +
            ((2 ^ (k + 1) : ℕ) : ℚ) /
              ((Erdos250Arithmetic.oddFactor (k + 1) : ℕ) ^ 2 : ℕ) := by
        rw [Erdos250Arithmetic.hTwo, Finset.sum_Icc_succ_top (by omega)]
        rfl
      have hrecTheta : ZPF.theta (k + 1) = ZPF.theta k +
          ZPF.q ^ (k + 1) / (1 - ZPF.q ^ (k + 1)) ^ 2 := by
        rw [ZPF.theta, Finset.sum_range_succ]
        rfl
      rw [hrec, hrecTheta, Rat.cast_add, ih]
      congr 1
      push_cast
      rw [show ZPF.q ^ (k + 1) = 1 / (2 : ℝ) ^ (k + 1) by simp [ZPF.q]]
      simp only [Erdos250Arithmetic.oddFactor]
      have hnat : 1 ≤ (2 : ℕ) ^ (k + 1) := one_le_pow₀ (by omega)
      rw [Nat.cast_sub hnat]
      push_cast
      have hp : (1 : ℝ) < (2 : ℝ) ^ (k + 1) :=
        one_lt_pow₀ (by norm_num) (by omega)
      field_simp [ne_of_gt hp]

lemma coeffC_eq_cast (n : ℕ) : coeffC n = ((coeffCQ n : ℚ) : ℝ) := by
  simp only [coeffC, ZPF.coeffC, coeffCQ]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [q_zpow_neg_eq_root_cast]

lemma coeffA_eq_cast (n : ℕ) : coeffA n = ((coeffAQ n : ℚ) : ℝ) := by
  simp only [coeffA, ZPF.coeffA, coeffAQ]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [q_zpow_neg_eq_root_cast, cast_hOne_eq_eta, cast_hTwo_eq_theta]

lemma cast_oddFactor_eq_oddFactorQ {d : ℕ} (hd : 1 ≤ d) :
    ((Erdos250Arithmetic.oddFactor d : ℕ) : ℚ) =
      DoublePartialFraction.OldRational.oddFactorQ d := by
  rw [Erdos250Arithmetic.oddFactor,
    DoublePartialFraction.OldRational.oddFactorQ, Nat.cast_sub]
  · norm_num
  · exact one_le_pow₀ (by omega)

lemma rawLogDeriv_eq_logDerivCoeff {n k : ℕ} (hk : k ≤ n) :
    DoublePartialFraction.OldRational.rawLogDeriv n k =
      Erdos250Arithmetic.logDerivCoeff n k := by
  rw [DoublePartialFraction.OldRational.rawLogDeriv_eq_targetLogDeriv n k hk]
  rw [DoublePartialFraction.OldRational.targetLogDeriv,
    Erdos250Arithmetic.logDerivCoeff]
  have hhigh :
      (∑ d ∈ Finset.Icc (k + 1) (n + k),
        (2 : ℚ) ^ d / DoublePartialFraction.OldRational.oddFactorQ d) =
      ∑ d ∈ Finset.Icc (k + 1) (n + k),
        ((2 ^ d : ℕ) : ℚ) / (Erdos250Arithmetic.oddFactor d : ℕ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [cast_oddFactor_eq_oddFactorQ (by
      have := (Finset.mem_Icc.mp hd).1
      omega)]
    norm_num
  have hmid :
      (∑ d ∈ Finset.Icc 1 k,
        (2 : ℚ) ^ d / DoublePartialFraction.OldRational.oddFactorQ d) =
      ∑ d ∈ Finset.Icc 1 k,
        ((2 ^ d : ℕ) : ℚ) / (Erdos250Arithmetic.oddFactor d : ℕ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [cast_oddFactor_eq_oddFactorQ (Finset.mem_Icc.mp hd).1]
    norm_num
  have hlow :
      (∑ d ∈ Finset.Icc 1 (n - k),
        (1 : ℚ) / DoublePartialFraction.OldRational.oddFactorQ d) =
      ∑ d ∈ Finset.Icc 1 (n - k),
        (1 : ℚ) / (Erdos250Arithmetic.oddFactor d : ℕ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [cast_oddFactor_eq_oddFactorQ (Finset.mem_Icc.mp hd).1]
  rw [hhigh, hmid, hlow]

lemma lambda_mul_coeffCQ (n : ℕ) :
    lambda n * coeffCQ n = Erdos250Arithmetic.bStar n := by
  rw [coeffCQ, Finset.mul_sum, Erdos250Arithmetic.bStar_eq_sum_cCoeff]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simpa only [lambda, VNormalization.lambda, mul_assoc] using
    (VNormalization.lambda_root_mul_vCoeff_eq_cCoeff hkn)

lemma lambda_mul_coeffAQ (n : ℕ) :
    lambda n * coeffAQ n = Erdos250Arithmetic.aStarRegrouped n := by
  rw [coeffAQ, Finset.mul_sum, Erdos250Arithmetic.aStarRegrouped]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [DoublePartialFraction.OldRational.uCoeff_eq_neg_vCoeff_mul_rawLogDeriv
    (Finset.mem_range.mp hk)]
  rw [DoublePartialFraction.OldRational.rawLogDeriv_eq_arithmetic_logDerivCoeff n k hkn]
  rw [show lambda n *
      (DoublePartialFraction.OldRational.root k *
        (-DoublePartialFraction.OldRational.vCoeff n k *
            Erdos250Arithmetic.logDerivCoeff n k * Erdos250Arithmetic.hOne k +
          DoublePartialFraction.OldRational.vCoeff n k * Erdos250Arithmetic.hTwo k)) =
      (lambda n * DoublePartialFraction.OldRational.root k *
          DoublePartialFraction.OldRational.vCoeff n k) *
        (Erdos250Arithmetic.hTwo k -
          Erdos250Arithmetic.logDerivCoeff n k * Erdos250Arithmetic.hOne k) by ring]
  rw [show lambda n * DoublePartialFraction.OldRational.root k *
      DoublePartialFraction.OldRational.vCoeff n k =
      Erdos250Arithmetic.cCoeff n k by
    simpa only [lambda, VNormalization.lambda] using
      (VNormalization.lambda_root_mul_vCoeff_eq_cCoeff hkn)]

lemma lambda_mul_S_eq_integer_form (n : ℕ) :
    ((lambda n : ℚ) : ℝ) * QApery.S n =
      ((Erdos250Arithmetic.bStar n : ℚ) : ℝ) * ZPF.lambert2 -
        ((Erdos250Arithmetic.aStarRegrouped n : ℚ) : ℝ) := by
  rw [S_eq_linear_form, coeffC_eq_cast, coeffA_eq_cast]
  have hb := congrArg (fun x : ℚ ↦ (x : ℝ)) (lambda_mul_coeffCQ n)
  have ha := congrArg (fun x : ℚ ↦ (x : ℝ)) (lambda_mul_coeffAQ n)
  push_cast at hb ha
  calc
    ((lambda n : ℚ) : ℝ) *
        (((coeffCQ n : ℚ) : ℝ) * ZPF.lambert2 - ((coeffAQ n : ℚ) : ℝ)) =
      (((lambda n : ℚ) : ℝ) * ((coeffCQ n : ℚ) : ℝ)) * ZPF.lambert2 -
        (((lambda n : ℚ) : ℝ) * ((coeffAQ n : ℚ) : ℝ)) := by ring
    _ = _ := by rw [hb, ha]

lemma lambert2_eq_zetaQ2 : ZPF.lambert2 = ShiftedSums.zetaQ2 := by
  change ShiftedSums.zetaQ2sq = ShiftedSums.zetaQ2
  exact ShiftedSums.zetaQ2sq_eq_zetaQ2

def intScale (n : ℕ) : ℕ :=
  2 ^ (n ^ 2 / 4) * Erdos250Arithmetic.denProd n ^ 2

noncomputable def bInt (n : ℕ) : ℤ :=
  Classical.choose (Erdos250Arithmetic.E_mul_bStar_eq_intCast n)

noncomputable def aInt (n : ℕ) : ℤ :=
  Classical.choose (Erdos250Arithmetic.E_mul_aStarRegrouped_eq_intCast n)

lemma bInt_spec (n : ℕ) :
    ((intScale n : ℕ) : ℚ) * Erdos250Arithmetic.bStar n = (bInt n : ℚ) := by
  exact Classical.choose_spec (Erdos250Arithmetic.E_mul_bStar_eq_intCast n)

lemma aInt_spec (n : ℕ) :
    ((intScale n : ℕ) : ℚ) * Erdos250Arithmetic.aStarRegrouped n = (aInt n : ℚ) := by
  exact Classical.choose_spec
    (Erdos250Arithmetic.E_mul_aStarRegrouped_eq_intCast n)

lemma integer_form_eq_scaled_S (n : ℕ) :
    (bInt n : ℝ) * ZPF.lambert2 + ((-aInt n : ℤ) : ℝ) =
      (intScale n : ℝ) * ((lambda n : ℚ) : ℝ) * QApery.S n := by
  have hb := congrArg (fun x : ℚ ↦ (x : ℝ)) (bInt_spec n)
  have ha := congrArg (fun x : ℚ ↦ (x : ℝ)) (aInt_spec n)
  push_cast at hb ha
  have hlin := lambda_mul_S_eq_integer_form n
  calc
    (bInt n : ℝ) * ZPF.lambert2 + ((-aInt n : ℤ) : ℝ) =
        (intScale n : ℝ) *
          (((Erdos250Arithmetic.bStar n : ℚ) : ℝ) * ZPF.lambert2 -
            ((Erdos250Arithmetic.aStarRegrouped n : ℚ) : ℝ)) := by
      push_cast
      rw [mul_sub, ← mul_assoc, hb, ← ha]
      ring
    _ = (intScale n : ℝ) *
        (((lambda n : ℚ) : ℝ) * QApery.S n) := by rw [hlin]
    _ = _ := by ring

lemma lambda_ne_zero (n : ℕ) : lambda n ≠ 0 := by
  rw [lambda]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact_mod_cast (ZV.denProd_pos n).ne'
  · positivity

lemma integer_form_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    (bInt n : ℝ) * ZPF.lambert2 + ((-aInt n : ℤ) : ℝ) ≠ 0 := by
  rw [integer_form_eq_scaled_S]
  apply mul_ne_zero
  · apply mul_ne_zero
    · have hscale : 0 < intScale n := by
        exact mul_pos (pow_pos (by omega) _) (pow_pos (ZV.denProd_pos n) _)
      exact_mod_cast hscale.ne'
    · exact_mod_cast lambda_ne_zero n
  · exact ne_of_gt (QApery.S_pos hn)

lemma scaled_S_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (intScale n : ℝ) * |((lambda n : ℚ) : ℝ)| * QApery.S n)
      atTop (𝓝 0) := by
  simpa only [intScale, OldScaledLinearForm.E, lambda, VNormalization.lambda] using
    OldScaledLinearForm.scaled_linear_form_tendsto_zero

lemma integer_form_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (bInt n : ℝ) * ZPF.lambert2 + ((-aInt n : ℤ) : ℝ))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply scaled_S_tendsto_zero.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  change (intScale n : ℝ) * |((lambda n : ℚ) : ℝ)| * QApery.S n =
    |(bInt n : ℝ) * ZPF.lambert2 + ((-aInt n : ℤ) : ℝ)|
  rw [integer_form_eq_scaled_S]
  symm
  calc
    |(intScale n : ℝ) * ((lambda n : ℚ) : ℝ) * QApery.S n| =
        |(intScale n : ℝ)| * |((lambda n : ℚ) : ℝ)| * |QApery.S n| := by
      rw [abs_mul, abs_mul]
    _ = _ := by
      rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (QApery.S_pos hn)]

theorem irrational_lambert2 : Irrational ZPF.lambert2 := by
  apply Erdos250Scratch.irrational_of_integer_linear_forms_tendsto_zero
    ZPF.lambert2 bInt (fun n ↦ -aInt n)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact integer_form_ne_zero hn
  · exact integer_form_tendsto_zero

theorem irrational_zetaQ2 : Irrational ShiftedSums.zetaQ2 := by
  rw [← lambert2_eq_zetaQ2]
  exact irrational_lambert2

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos250.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 250.
https://www.erdosproblems.com/forum/thread/250

Informal authors:
- Yuri Nesterenko

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos250.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/250.lean
-/
/-
Erdős Problem 250: irrationality of the sum-of-divisors Lambert series.

The mathematical proof and the implementation plan are documented in
`tex/250.tex` at the repository root.
-/


open Filter
open scoped ArithmeticFunction.sigma BigOperators Topology



/-- The `q = 1/2` value of the Lambert series usually denoted `ζ_q(2)`. -/
noncomputable def zetaQ2 : ℝ :=
  ∑' n : ℕ+, (n : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ) /
    (1 - ((1 : ℝ) / 2) ^ (n : ℕ))

/-- The series in the problem is the Lambert-series value `zetaQ2`. -/
lemma hasSum_eq_zetaQ2 (x : ℝ)
    (h : HasSum (fun n : ℕ => σ 1 n / (2 : ℝ) ^ n) x) :
    x = zetaQ2 := by
  calc
    x = ∑' n : ℕ, (σ 1 n : ℝ) / (2 : ℝ) ^ n := h.tsum_eq.symm
    _ = ∑' n : ℕ+, (σ 1 (n : ℕ) : ℝ) / (2 : ℝ) ^ (n : ℕ) := by
      simpa using (tsum_zero_pnat_eq_tsum_nat h.summable).symm
    _ = ∑' n : ℕ+, (σ 1 (n : ℕ) : ℝ) *
          ((1 : ℝ) / 2) ^ (n : ℕ) := by
      congr 1
      ext n
      rw [one_div_pow]
      ring
    _ = zetaQ2 := by
      rw [zetaQ2]
      symm
      simpa using
        (tsum_pow_div_one_sub_eq_tsum_sigma
          (r := (1 : ℝ) / 2) (by norm_num) 1)

/-- An integer-valued sequence converging to zero is eventually zero. -/
lemma int_tendsto_zero_eventually_zero (f : ℕ → ℤ)
    (htend : Tendsto (fun n => (f n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, f n = 0 := by
  norm_num [Metric.tendsto_nhds] at htend
  exact eventually_atTop.mpr (by
    rcases htend 1 zero_lt_one with ⟨N, hN⟩
    exact ⟨N, fun n hn => by
      norm_cast at hN
      simpa [sub_eq_iff_eq_add] using hN n hn⟩)

/-- Nonzero integer linear forms tending to zero certify irrationality. -/
lemma irrational_of_integer_linear_forms (x : ℝ) (a b : ℕ → ℤ)
    (hne : ∀ n, (b n : ℝ) * x - a n ≠ 0)
    (htend : Tendsto (fun n => (b n : ℝ) * x - a n) atTop (𝓝 0)) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  let F : ℕ → ℤ := fun n => b n * r.num - a n * r.den
  have hcast : ∀ n, (F n : ℝ) = (r.den : ℝ) *
      ((b n : ℝ) * (r : ℝ) - a n) := by
    intro n
    change (((b n * r.num - a n * (r.den : ℤ) : ℤ) : ℤ) : ℝ) = _
    push_cast
    rw [Rat.cast_def]
    field_simp [Rat.den_ne_zero]
  have hFtend : Tendsto (fun n => (F n : ℝ)) atTop (𝓝 0) := by
    simpa only [hcast, mul_zero] using htend.const_mul (r.den : ℝ)
  rcases eventually_atTop.mp (int_tendsto_zero_eventually_zero F hFtend) with ⟨N, hN⟩
  apply hne N
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hmul : (r.den : ℝ) * ((b N : ℝ) * (r : ℝ) - a N) = 0 := by
    simpa [hN N le_rfl] using (hcast N).symm
  exact (mul_eq_zero.mp hmul).resolve_left hden

/-- Erdős Problem 250: the sum of the divisors series at `1 / 2` is
irrational.  The term at `n = 0` vanishes, so this is the stated sum over
positive integers. -/
theorem erdos_250 :
    ∀ x : ℝ, HasSum (fun n : ℕ => σ 1 n / (2 : ℝ) ^ n) x → Irrational x := by
  intro x hx
  rw [hasSum_eq_zetaQ2 x hx]
  have hzeta : zetaQ2 = ShiftedSums.zetaQ2 := by
    simp only [zetaQ2, ShiftedSums.zetaQ2, ShiftedSums.q]
  rw [hzeta]
  exact irrational_zetaQ2

end

#print axioms erdos_250
-- 'Erdos250.erdos_250' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos250
