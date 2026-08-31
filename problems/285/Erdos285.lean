import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos285

/-
# Problem Description

Erdős Problem 285. Let `f(k)` be the least possible value of the largest denominator `n_k` in
a representation `1 = 1/n₁ + ⋯ + 1/n_k` with `n₁ < ⋯ < n_k`. Is it true that
`f(k) = (1 + o(1)) · e/(e−1) · k`? `erdos_285` proves that it is.

The question is from [ErGr80, p.33]; the lower bound `f(k) ≥ (1 + o(1)) e/(e−1) k` is easy,
and the matching upper bound is due to Martin [Ma00]. Below, `S` is the set of `k` admitting
such a representation, `IsLeast` expresses that `f k` is the minimal largest denominator, and
the denominators are indexed by `Fin k.succ` (so a `k` here carries `k + 1` terms, which is
why the asymptotic is stated as `(1 + o k) * e/(e−1) * (k + 1)`).

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos285.lean` together with the modules of
`src/latest/ErdosProblems/Erdos285/`. Those files are concatenated here in dependency order,
with their project-internal imports removed so that `Mathlib` is the only import, each
module's contents kept in a `section` carrying its own `open` lines, and the whole wrapped
once in `namespace Erdos285` with the upstream trust-base print line removed. No mathematical
content is changed.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Analytic.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Analytic infrastructure for Erdős Problem 285

This file records the elementary harmonic-interval estimate, algebraic facts
about the constant `e / (e - 1)`, and generic ratio/error-term conversions used
in the proof of the formal-conjectures statement.
-/

namespace Analytic

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

/-! ## The constant `e / (e - 1)` -/

/-- The density constant occurring in Erdős Problem 285. -/
def densityConstant : ℝ := Real.exp 1 / (Real.exp 1 - 1)

lemma one_lt_exp_one : (1 : ℝ) < Real.exp 1 :=
  Real.one_lt_exp_iff.mpr zero_lt_one

lemma exp_one_sub_one_pos : (0 : ℝ) < Real.exp 1 - 1 :=
  sub_pos.mpr one_lt_exp_one

lemma densityConstant_pos : 0 < densityConstant := by
  exact div_pos (Real.exp_pos 1) exp_one_sub_one_pos

lemma densityConstant_eq_inv_one_sub_exp_neg :
    densityConstant = (1 - Real.exp (-1))⁻¹ := by
  have he : Real.exp (1 : ℝ) ≠ 0 := ne_of_gt (Real.exp_pos 1)
  rw [Real.exp_neg]
  simp only [densityConstant]
  field_simp

lemma densityConstant_inv : densityConstant⁻¹ = 1 - Real.exp (-1) := by
  rw [densityConstant_eq_inv_one_sub_exp_neg, inv_inv]

/-! ## Terminal intervals of the harmonic series -/

/-- A single logarithmic increment is at most the corresponding reciprocal. -/
lemma log_succ_ratio_le_reciprocal {a : ℕ} (ha : 0 < a) :
    Real.log (((a + 1 : ℕ) : ℝ) / a) ≤ (1 : ℝ) / a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hratio : (0 : ℝ) < (((a + 1 : ℕ) : ℝ) / a) := by positivity
  calc
    Real.log (((a + 1 : ℕ) : ℝ) / a)
        ≤ (((a + 1 : ℕ) : ℝ) / a) - 1 :=
      Real.log_le_sub_one_of_pos hratio
    _ = (1 : ℝ) / a := by
      field_simp
      norm_num [Nat.cast_add]

/-! ## Little-error and ratio packaging -/

end

end Analytic

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/UnitFractions/Definitions.lean` -/

section
namespace UnitFractions

open scoped BigOperators ArithmeticFunction.omega
open Filter Real Finset Nat
open _root_.Finset

noncomputable section
attribute [local instance] Classical.propDecidable

section

variable (A : Set ℕ)

variable {A}

end

-- This is R(A) in the paper.
def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

lemma rec_sum_disjoint {A B : Finset ℕ} (h : Disjoint A B) :
    rec_sum (A ∪ B) = rec_sum A + rec_sum B := by
  simpa [rec_sum] using (Finset.sum_union h (f := fun n : ℕ ↦ (1 : ℚ) / n))

@[simp] lemma rec_sum_empty : rec_sum ∅ = 0 := by simp [rec_sum]

lemma rec_sum_nonneg {A : Finset ℕ} : 0 ≤ rec_sum A :=
  by
    simpa [rec_sum] using
      (sum_nonneg fun i (_hi : i ∈ A) ↦
        div_nonneg zero_le_one (show 0 ≤ (i : ℚ) by exact_mod_cast Nat.zero_le i))

-- can make this stronger without 0 ∉ A but we never care about that case

/--
This is A_q in the paper.
-/
def local_part (A : Finset ℕ) (q : ℕ) : Finset ℕ :=
  A.filter fun n ↦ q ∣ n ∧ Nat.Coprime q (n / q)

lemma mem_local_part {A : Finset ℕ} {q : ℕ} (n : ℕ) :
    n ∈ local_part A q ↔ n ∈ A ∧ q ∣ n ∧ Nat.Coprime q (n / q) := by
  rw [local_part, mem_filter]

/--
This is Q_A in the paper. The definition looks a bit different, but `mem_ppowers_in_set` shows
it's the same thing.
-/
def ppowers_in_set (A : Finset ℕ) : Finset ℕ :=
  A.biUnion fun n ↦ n.divisors.filter fun q ↦ IsPrimePow q ∧ Nat.Coprime q (n / q)

@[simp] lemma ppowers_in_set_empty : ppowers_in_set ∅ = ∅ := Finset.biUnion_empty

lemma ppowers_in_set_insert_zero (A : Finset ℕ) :
    ppowers_in_set (insert 0 A) = ppowers_in_set A := by
  rw [ppowers_in_set, ppowers_in_set, Finset.biUnion_insert, Nat.divisors_zero, filter_empty,
    empty_union]

lemma mem_ppowers_in_set {A : Finset ℕ} {q : ℕ} :
    q ∈ ppowers_in_set A ↔ IsPrimePow q ∧ (local_part A q).Nonempty := by
  constructor
  · intro h
    rcases mem_biUnion.mp h with ⟨n, hnA, hq⟩
    rw [mem_filter, Nat.mem_divisors] at hq
    rcases hq with ⟨⟨hqdiv, _hn0⟩, hpp, hcop⟩
    exact ⟨hpp, ⟨n, by simpa [local_part, hnA, hqdiv, hcop]⟩⟩
  · rintro ⟨hpp, ⟨n, hnlocal⟩⟩
    rcases (mem_local_part (A := A) (q := q) n).mp hnlocal with ⟨hnA, hqdiv, hcop⟩
    have hn0 : n ≠ 0 := by
      intro hn0
      have : q = 1 := by simpa [hn0] using hcop
      exact hpp.ne_one this
    refine mem_biUnion.mpr ⟨n, hnA, ?_⟩
    rw [mem_filter, Nat.mem_divisors]
    exact ⟨⟨hqdiv, hn0⟩, hpp, hcop⟩

section
open Nat

private lemma _root_.Nat.pow_eq_one_iff {n k : ℕ} : n ^ k = 1 ↔ n = 1 ∨ k = 0 := by
  exact _root_.pow_eq_one_iff

end

lemma factorization_disjoint_iff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Disjoint a.factorization.support b.factorization.support ↔ a.Coprime b := by
  simpa [Nat.support_factorization] using (Nat.disjoint_primeFactors ha hb)

lemma factorization_eq_iff {n p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    p ^ k ∣ n ∧ (p ^ k).Coprime (n / p ^ k) ↔ n.factorization p = k := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases eq_or_ne n 0 with rfl | hn
    · have hpow : p ^ k = 1 := by simpa using h₂
      exact (hk ((Nat.pow_eq_one_iff.mp hpow).resolve_left hp.ne_one)).elim
    have hp_mem : p ∈ (p ^ k).primeFactorsList := by
      rw [Nat.mem_primeFactorsList_iff_dvd (pow_ne_zero _ hp.ne_zero) hp]
      exact dvd_pow_self _ hk
    have hfac :=
      Nat.factorization_eq_of_coprime_left (a := p ^ k) (b := n / p ^ k) h₂ hp_mem
    rw [Nat.mul_div_cancel' h₁] at hfac
    rw [hfac, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
  · intro hk'
    have hn : n ≠ 0 := by
      intro hn0
      simp [hn0] at hk'
      exact hk hk'.symm
    have hdvd : p ^ k ∣ n := by
      have hkle : k ≤ n.factorization p := hk'.ge
      exact (hp.pow_dvd_iff_le_factorization hn).2 hkle
    refine ⟨hdvd, ?_⟩
    have hdiv0 : n / p ^ k ≠ 0 := by
      exact Nat.ne_of_gt <| Nat.div_pos (Nat.le_of_dvd hn.bot_lt hdvd) (pow_pos hp.pos _)
    rw [← factorization_disjoint_iff (pow_ne_zero _ hp.ne_zero) hdiv0]
    rw [Nat.factorization_div hdvd, Nat.Prime.factorization_pow hp,
      Finsupp.support_single _ hk,
      disjoint_singleton_left, Finsupp.mem_support_iff, Finsupp.coe_tsub, Pi.sub_apply, ne_eq,
      tsub_eq_zero_iff_le, not_not, Finsupp.single_eq_same, hk']

lemma mem_ppowers_in_set' {A : Finset ℕ} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    p ^ k ∈ ppowers_in_set A ↔ ∃ n ∈ A, n.factorization p = k := by
  rw [mem_ppowers_in_set, and_iff_right (hp.isPrimePow.pow hk)]
  constructor
  · rintro ⟨n, hnlocal⟩
    rcases (mem_local_part (A := A) (q := p ^ k) n).mp hnlocal with ⟨hnA, hdvd, hcop⟩
    exact ⟨n, hnA, (factorization_eq_iff hp hk).1 ⟨hdvd, hcop⟩⟩
  · rintro ⟨n, hnA, hfac⟩
    have hq := (factorization_eq_iff hp hk).2 hfac
    exact ⟨n, (mem_local_part (A := A) (q := p ^ k) n).2 ⟨hnA, hq.1, hq.2⟩⟩

lemma ppowers_in_set_nonempty {A : Finset ℕ} (hA : ∃ n ∈ A, 2 ≤ n) :
    (ppowers_in_set A).Nonempty := by
  obtain ⟨n, hn, hn'⟩ := hA
  have hne : n ≠ 1 := by linarith
  have hn0 : n ≠ 0 := by linarith
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hpk : n.factorization p ≠ 0 := (hp.factorization_pos_of_dvd hn0 hpdvd).ne'
  exact ⟨p ^ n.factorization p, (mem_ppowers_in_set' hp hpk).2 ⟨n, hn, rfl⟩⟩

-- This is R(A;q) in the paper.

def is_smooth (y : ℝ) (n : ℕ) : Prop := ∀ q : ℕ, IsPrimePow q → q ∣ n → (q : ℝ) ≤ y

def arith_regular (N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ n ∈ A, ((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log N)

lemma arith_regular.subset {N : ℕ} {A A' : Finset ℕ} (hA : arith_regular N A) (hA' : A' ⊆ A) :
    arith_regular N A' :=
  fun n hn ↦ hA n (hA' hn)

-- This is the set D_I

-- This is the awkward condition that 'bridges' the hypothesis of the Fourier stuff
-- with the conclusion of the combinatorial bits

end

end UnitFractions

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Approximation.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős 285: Martin's approximate-representation interface

This file isolates the finite bookkeeping in Proposition 6 of Greg Martin's
*Denser Egyptian fractions*.  The analytic and modular-number-theory inputs are
represented by hypotheses of the theorems which use them; no global assumption
is introduced here.

There are three layers.

* `ApproximationState` and `ApproximationStep` implement Martin's recursion.  A
  state remembers both the currently selected denominators and every denominator
  that has ever been used.  A valid step may remove selected terms and may add
  only terms which have never been used.
* `ApproximationCertificate` is a finite, quantitative version of Proposition 6.
  The condition `q ^ 5 ≤ x` is the integral form of `q ≤ x^(1/5)` and avoids
  rounding ambiguity.
* `HasMartinApproximation` is the epsilon form of the cardinality asymptotic.

The actual construction of the blocks used in a valid step is the deep part of
Martin's argument (modular subset sums and smooth-number estimates).  Once those
blocks are supplied, all cardinality, reciprocal-sum, interval, and non-reuse
claims are proved below.
-/

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The exact finite certificate -/

/-- The reciprocal sum of a finite set, regarded as a real number. -/
def realRecSum (A : Finset ℕ) : ℝ := ∑ n ∈ A, (1 : ℝ) / n

lemma realRecSum_eq_ratCast (A : Finset ℕ) :
    realRecSum A = (UnitFractions.rec_sum A : ℝ) := by
  simp only [realRecSum, UnitFractions.rec_sum, Rat.cast_sum, Rat.cast_div,
    Rat.cast_one, Rat.cast_natCast]

/-- The integer fifth-root scale passed from Proposition 6 to the exact
small-denominator correction in Proposition 7. -/
def approximationCorrectionScale (x : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊

/--
A finite certificate for Martin's Proposition 6 at scale `x` and target
cardinality `R`.

The interval starts at `exp (-r) * x / 2`, because the smooth reservoir used for
cardinality adjustment lies immediately below the main interval.  The main
interval itself begins at `exp (-r) * x` up to the quantified error.
-/
structure ApproximationCertificate (r : ℚ) (x R : ℕ) where
  denominators : Finset ℕ
  numerator : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator
  numerator_pos : 0 < numerator
  reduced : Nat.Coprime numerator denominator
  card_eq : denominators.card = R
  zero_not_mem : 0 ∉ denominators
  interval : ∀ n ∈ denominators,
    Real.exp (-(r : ℝ)) * (x : ℝ) / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ x
  sum_add_residual :
    UnitFractions.rec_sum denominators + (numerator : ℚ) / denominator = r
  residual_lower :
    (Real.log (x : ℝ))⁻¹ < (numerator : ℝ) / denominator
  residual_upper : (numerator : ℝ) / denominator < 1
  denominator_primePower_bound :
    ∀ q : ℕ, IsPrimePow q → q ∣ denominator → q ^ 5 ≤ x

/-- The residual rational represented by an approximation certificate. -/
def ApproximationCertificate.residual {r : ℚ} {x R : ℕ}
    (C : ApproximationCertificate r x R) : ℚ :=
  (C.numerator : ℚ) / C.denominator

lemma ApproximationCertificate.reciprocal_sum_eq_sub_residual
    {r : ℚ} {x R : ℕ} (C : ApproximationCertificate r x R) :
    UnitFractions.rec_sum C.denominators = r - C.residual := by
  rw [eq_sub_iff_add_eq, ApproximationCertificate.residual]
  exact C.sum_add_residual

/-! ## Removal/addition recursion with a no-reuse invariant -/

/--
A state in the prime-power elimination recursion.  `selected` is the current
Egyptian-fraction set; `used` additionally retains terms removed at earlier
stages, so they cannot be selected again.
-/
structure ApproximationState where
  selected : Finset ℕ
  used : Finset ℕ

/-- A stage removes some current terms and inserts a fresh correction block. -/
structure ApproximationStep where
  remove : Finset ℕ
  add : Finset ℕ

/-- Execute one removal/addition stage. -/
def ApproximationState.applyStep (s : ApproximationState) (d : ApproximationStep) :
    ApproximationState where
  selected := (s.selected \ d.remove) ∪ d.add
  used := s.used ∪ d.add

/--
Validity of one stage.  The old selected set must already lie in `used`; removed
terms must actually be selected; and new terms must be disjoint from all terms
ever used.
-/
def ApproximationStep.Valid (s : ApproximationState) (d : ApproximationStep) : Prop :=
  s.selected ⊆ s.used ∧ d.remove ⊆ s.selected ∧ Disjoint d.add s.used

lemma ApproximationStep.Valid.add_disjoint_selected
    {s : ApproximationState} {d : ApproximationStep} (h : d.Valid s) :
    Disjoint d.add s.selected :=
  h.2.2.mono_right h.1

lemma ApproximationStep.Valid.add_disjoint_remaining
    {s : ApproximationState} {d : ApproximationStep} (h : d.Valid s) :
    Disjoint (s.selected \ d.remove) d.add := by
  exact h.add_disjoint_selected.symm.mono_left (Finset.sdiff_subset)

lemma ApproximationStep.Valid.selected_subset_used_after
    {s : ApproximationState} {d : ApproximationStep} (h : d.Valid s) :
    (s.applyStep d).selected ⊆ (s.applyStep d).used := by
  intro n hn
  rw [ApproximationState.applyStep, Finset.mem_union] at hn ⊢
  rcases hn with hn | hn
  · exact Or.inl (h.1 (Finset.sdiff_subset hn))
  · exact Or.inr hn

/-- Exact reciprocal-sum balance for one recursion stage. -/
lemma ApproximationStep.Valid.rec_sum_balance
    {s : ApproximationState} {d : ApproximationStep} (h : d.Valid s) :
    UnitFractions.rec_sum (s.applyStep d).selected + UnitFractions.rec_sum d.remove =
      UnitFractions.rec_sum s.selected + UnitFractions.rec_sum d.add := by
  have hnew := UnitFractions.rec_sum_disjoint h.add_disjoint_remaining
  have hold := UnitFractions.rec_sum_disjoint
    (Finset.sdiff_disjoint : Disjoint (s.selected \ d.remove) d.remove)
  rw [Finset.sdiff_union_of_subset h.2.1] at hold
  rw [ApproximationState.applyStep, hnew, hold]
  ring

/-! ## Exact-cardinality selection from the smooth reservoir -/

/-! ## Finite epsilon/asymptotic interface -/

/-- The expected density of denominators in Martin's theorem. -/
def martinDensity (r : ℚ) : ℝ := 1 - Real.exp (-(r : ℝ))

/-- Proposition 6 at one finite scale, with an epsilon cardinality error. -/
def MartinApproximationAt (r : ℚ) (x : ℕ) (eps : ℝ) : Prop :=
  ∃ R : ℕ, Nonempty (ApproximationCertificate r x R) ∧
    |(R : ℝ) / x - martinDensity r| < eps

/-- The epsilon form of Martin's approximate-representation proposition. -/
def HasMartinApproximation (r : ℚ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
    MartinApproximationAt r x eps

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/UnitFractions/ForMathlib/IntegralRPow.lean` -/

section
noncomputable section

open Filter MeasureTheory Set

/-!
This file is mostly a compatibility layer for the old Lean 3 `for_mathlib/integral_rpow` file.
All of the main half-line `rpow` lemmas are now available in Mathlib 4 under standard names.
-/

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/UnitFractions/ForMathlib/Misc.lean` -/

section
open scoped BigOperators

/-!
This file only reintroduces the pieces of `src/for_mathlib/misc.lean` that are not already
available in Mathlib4 under the same names.

In particular, Mathlib4 already provides results such as:
* `Rat.cast_sum`
* `Finset.filter_comm`
* `Finset.one_le_prod`
* `Real.finsetProd_rpow`
* `Real.self_le_rpow_of_one_le`
* `Real.self_le_rpow_of_le_one`
* the add-one interval lemmas in `Finset` and `Set`
-/

section
open Int

end

section
open Finset

end

@[simp] theorem Ico_inter_Icc_consecutive {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    (a b c : α) : Finset.Ico a b ∩ Finset.Icc b c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hx₁, hx₂⟩
  exact (not_lt_of_ge (Finset.mem_Icc.mp hx₂).1) (Finset.mem_Ico.mp hx₁).2

theorem one_le_prod {ι R : Type*} [CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R]
    [PosMulMono R] {f : ι → R} {s : Finset ι}
    (h1 : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ (∏ i ∈ s, f i) := by
  simpa using (Finset.one_le_prod (s := s) (f := f) h1)

section
open Real

end

@[to_additive]
theorem prod_powerset_compl {α β : Type*} [DecidableEq α] [CommMonoid β]
    (s : Finset α) (f : Finset α → β) :
    (∏ x ∈ s.powerset, f (s \ x)) = ∏ x ∈ s.powerset, f x := by
  refine Finset.prod_bij' (fun x _ ↦ s \ x) (fun x _ ↦ s \ x) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_powerset.2 Finset.sdiff_subset
  · intro x hx
    exact Finset.mem_powerset.2 Finset.sdiff_subset
  · intro x hx
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hx)
  · intro x hx
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hx)
  · intro x hx
    rfl

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/UnitFractions/ForMathlib/BasicEstimates.lean` -/

section
noncomputable section

open Asymptotics Filter Finset MeasureTheory Real Set
open scoped ArithmeticFunction ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators
open scoped Chebyshev Nat.Prime Topology

/-!
This file contains the Lean 4 statement port of the old Lean 3
`for_mathlib/basic_estimates` file.

When a result already exists upstream in Mathlib 4, this file prefers the
Mathlib version instead of reintroducing a duplicate local theorem.
-/

theorem tendsto_log_coe_at_top : Tendsto (fun x : ℕ => log (x : ℝ)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

section Summatory

variable {M : Type*} [AddCommMonoid M]

/--
Given a function `a : ℕ → M`, this is the sum `∑ k ≤ n ≤ x, a n`.
-/
def summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n ∈ Finset.Icc k ⌊x⌋₊, a n

theorem summatory_nat (a : ℕ → M) (k n : ℕ) :
    summatory a k n = ∑ i ∈ Finset.Icc k n, a i := by
  simp [summatory]

theorem summatory_eq_floor (a : ℕ → M) {k : ℕ} (x : ℝ) :
    summatory a k x = summatory a k ⌊x⌋₊ := by
  rw [summatory, summatory, Nat.floor_natCast]

end Summatory

section PrimeSummatory

variable {M : Type*} [AddCommMonoid M]

/--
Given a function `a : ℕ → M`, this is the sum `∑ k ≤ p ≤ x, a p`
where `p` ranges over primes.
-/
def prime_summatory (a : ℕ → M) (k : ℕ) (x : ℝ) : M :=
  ∑ n ∈ (Finset.Icc k ⌊x⌋₊).filter Nat.Prime, a n

theorem prime_summatory_eq_summatory (a : ℕ → M) :
    prime_summatory a = summatory (fun n => if n.Prime then a n else 0) := by
  ext k x
  simp [prime_summatory, summatory, Finset.sum_filter]

end PrimeSummatory

section
open Nat

private theorem _root_.Nat.cast_floor_eq_cast_int_floor {a : ℝ} (ha : 0 ≤ a) : (⌊a⌋₊ : ℝ) = ⌊a⌋ := by
  exact natCast_floor_eq_intCast_floor ha

end

theorem log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
  Real.strictMonoOn_log.monotoneOn (by simpa) (by simpa using lt_of_lt_of_le hx hxy) hxy

theorem von_mangoldt_upper {n : ℕ} : Λ n ≤ log (n : ℝ) :=
  ArithmeticFunction.vonMangoldt_le_log

abbrev chebyshev_first : ℝ → ℝ := Chebyshev.theta
abbrev chebyshev_second : ℝ → ℝ := Chebyshev.psi

scoped[Chebyshev] notation "ϑ" => Erdos285.chebyshev_first

theorem prime_counting_eq_card_primes {x : ℕ} :
    π x = ((Finset.Icc 1 x).filter Nat.Prime).card := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting' (x + 1)]
  congr 1
  ext p
  simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
    Nat.lt_succ_iff, and_assoc]
  constructor
  · rintro ⟨hp1, hp2⟩
    exact ⟨hp2.one_le, hp1, hp2⟩
  · rintro ⟨hp1, hp2, hp3⟩
    exact ⟨hp2, hp3⟩

def partial_euler_product (n : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 1 n).filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹

@[simp] theorem partial_euler_product_zero : partial_euler_product 0 = 1 := by
  simp [partial_euler_product]

theorem my_mul_thing : ∀ {n : ℕ}, (0 : ℝ) ≤ (n - 1) * n
  | 0 => by norm_num
  | n + 1 => by
      simpa using (show (0 : ℝ) ≤ (n : ℝ) * (n + 1) by positivity)

section SummatoryExtra

variable {M : Type*} [AddCommMonoid M] (a : ℕ → M)

lemma summatory_eq_of_lt_one {k : ℕ} {x : ℝ} (hk : k ≠ 0) (hx : x < k) :
  summatory a k x = 0 := by
  rw [summatory, Finset.Icc_eq_empty_of_lt, Finset.sum_empty]
  exact (Nat.floor_lt' hk).2 hx

@[simp] lemma summatory_zero {k : ℕ} (hk : k ≠ 0) : summatory a k 0 = 0 := by
  have hk' : (0 : ℝ) < k := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr hk
  exact summatory_eq_of_lt_one (a := a) hk hk'

@[simp] lemma summatory_self {k : ℕ} : summatory a k k = a k := by
  simp [summatory]

@[simp] lemma summatory_one : summatory a 1 1 = a 1 := by
  simp [summatory]

lemma abs_summatory_le_sum {M : Type*} [SeminormedAddCommGroup M] (a : ℕ → M)
    {k : ℕ} {x : ℝ} :
  ‖summatory a k x‖ ≤ ∑ i ∈ Finset.Icc k (⌊x⌋₊), ‖a i‖ := by
  simpa [summatory] using
    (norm_sum_le (s := Finset.Icc k (⌊x⌋₊)) (f := fun i => a i))

lemma summatory_const_one {x : ℝ} :
  summatory (fun _ ↦ (1 : ℝ)) 1 x = (⌊x⌋₊ : ℝ) := by
  simp [summatory]

lemma summatory_nonneg {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M] (a : ℕ → M)
    (x : ℝ) (k : ℕ) (ha : ∀ (i : ℕ), 0 ≤ a i) :
  0 ≤ summatory a k x := by
  rw [summatory]
  exact Finset.sum_nonneg (fun i _ ↦ ha i)

lemma summatory_monotone_of_nonneg {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M]
    (a : ℕ → M)
  (k : ℕ)
  (ha : ∀ (i : ℕ), 0 ≤ a i) :
  Monotone (summatory a k) := by
  intro i j hij
  rw [summatory, summatory]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hij)
  · intro n _ _; exact ha n

lemma abs_summatory_bound {M : Type*} [SeminormedAddCommGroup M] (a : ℕ → M) (k z : ℕ)
  {x : ℝ} (hx : x ≤ z) :
  ‖summatory a k x‖ ≤ ∑ i ∈ Finset.Icc k z, ‖a i‖ := by
  exact (abs_summatory_le_sum a).trans <|
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_of_le hx))
      (by intro i _ _; exact norm_nonneg _)

@[fun_prop] lemma measurable_summatory {M : Type*} [AddCommMonoid M] [MeasurableSpace M]
  {k : ℕ} {a : ℕ → M} :
  Measurable (summatory a k) := by
  change Measurable ((fun y ↦ ∑ i ∈ Finset.Icc k y, a i) ∘ Nat.floor)
  exact measurable_from_nat.comp Nat.measurable_floor

end SummatoryExtra

section
open ArithmeticFunction

end

section
open Finset

private lemma _root_.Finset.Icc_eq_insert_Icc_succ {a b : ℕ} (h : a ≤ b) :
    Finset.Icc a b = insert a (Finset.Icc (a + 1) b) := by
  simpa using (Finset.insert_Icc_succ_left_eq_Icc h).symm

end

section
open Nat

@[simp] private lemma _root_.Nat.floor_two {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]
    [IsStrictOrderedRing R] :
  ⌊(2 : R)⌋₊ = 2 := by
  simp

end

lemma partial_summation_integrable {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜)
    {f : ℝ → 𝕜} {x y : ℝ} {k : ℕ} (hf' : IntegrableOn f (Icc x y)) :
  IntegrableOn (summatory a k * f) (Icc x y) := by
  let b := ∑ i ∈ Finset.Icc k ⌈y⌉₊, ‖a i‖
  have hsmul : IntegrableOn (b • f) (Icc x y) := Integrable.smul b hf'
  refine hsmul.integrable.mono ?_ ?_
  · exact measurable_summatory.aestronglyMeasurable.mul hf'.1
  · rw [ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall (fun z hz => ?_)
    rw [Pi.mul_apply, norm_mul, Pi.smul_apply, norm_smul]
    refine mul_le_mul_of_nonneg_right ((abs_summatory_bound _ _ ⌈y⌉₊ ?_).trans ?_)
      (norm_nonneg _)
    · exact hz.2.trans (Nat.le_ceil y)
    · rw [Real.norm_eq_abs]
      exact le_abs_self b

theorem partial_summation {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {x : ℝ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Icc (k : ℝ) x, HasDerivAt f (f' i) i)
    (hf' : IntegrableOn f' (Icc k x)) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  by_cases h : x < k
  · rw [Icc_eq_empty_of_lt h, Measure.restrict_empty, integral_zero_measure, sub_zero,
      summatory_eq_of_lt_one (a := fun n ↦ a n * f n) hk h,
      summatory_eq_of_lt_one (a := a) hk h, zero_mul]
  · have hle : (k : ℝ) ≤ x := le_of_not_gt h
    have hx : k ≤ ⌊x⌋₊ := by rwa [Nat.le_floor_iff' hk]
    let c : ℕ → 𝕜 := fun n => if k ≤ n then a n else 0
    have hderiv_eq : f' =ᵐ[volume.restrict (Set.Icc (k : ℝ) x)] deriv f := by
      change ∀ᵐ t ∂(volume.restrict (Set.Icc (k : ℝ) x)), f' t = deriv f t
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall ?_
      intro t ht
      exact (hf t ht).deriv.symm
    have habel := sum_mul_eq_sub_sub_integral_mul (c := c) (f := f)
      (show 0 ≤ (k : ℝ) by exact_mod_cast Nat.zero_le k) hle
      (fun t ht => (hf t ht).differentiableAt) (hf'.congr_fun_ae hderiv_eq)
    rw [Nat.floor_natCast] at habel
    have hc_partial : ∀ t : ℝ, (∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) = summatory a k t := by
      intro t
      calc
        ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = ∑ i ∈ Finset.Icc k ⌊t⌋₊, c i := by
          symm
          refine Finset.sum_subset ?_ ?_
          · intro i hi
            simp only [Finset.mem_Icc] at hi ⊢
            exact ⟨Nat.zero_le _, hi.2⟩
          · intro i hi0 hi
            have hi0' := Finset.mem_Icc.mp hi0
            have hki : ¬ k ≤ i := by
              intro hk
              exact hi (Finset.mem_Icc.mpr ⟨hk, hi0'.2⟩)
            simp [c, hki]
        _ = ∑ i ∈ Finset.Icc k ⌊t⌋₊, a i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hk : k ≤ i := (Finset.mem_Icc.mp hi).1
          simp [c, hk]
        _ = summatory a k t := by rw [summatory]
    have hsum :
        ∑ n ∈ Finset.Icc k ⌊x⌋₊, a n * f n = f k * c k + ∑ n ∈ Finset.Ioc k ⌊x⌋₊, f n * c n := by
      rw [show Finset.Icc k ⌊x⌋₊ = (Finset.Ioc k ⌊x⌋₊).cons k Finset.left_notMem_Ioc by
        simpa using (Finset.Icc_eq_cons_Ioc hx)]
      rw [Finset.sum_cons]
      have htail :
          ∑ n ∈ Finset.Ioc k ⌊x⌋₊, a n * f n =
            ∑ n ∈ Finset.Ioc k ⌊x⌋₊, if k ≤ n then a n * f n else 0 := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        have hk : k ≤ n := (Finset.mem_Ioc.mp hn).1.le
        simp [hk]
      simp [c, mul_comm, htail]
    have hcongr :
        ∀ᵐ t ∂volume,
          t ∈ Set.Ioc (k : ℝ) x →
            deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i = summatory a k t * f' t := by
      refine Filter.Eventually.of_forall ?_
      intro t ht
      rw [(hf t ⟨ht.1.le, ht.2⟩).deriv, hc_partial, mul_comm]
    have hIocIcc :
        (∫ t in Set.Ioc (k : ℝ) x, deriv f t * ∑ i ∈ Finset.Icc 0 ⌊t⌋₊, c i) =
          ∫ t in Set.Icc (k : ℝ) x, summatory a k t * f' t := by
      rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc hcongr,
        setIntegral_congr_set Ioc_ae_eq_Icc]
    have hc_k : ∑ i ∈ Finset.Icc 0 k, c i = summatory a k k := by
      simpa using hc_partial (k : ℝ)
    rw [summatory, hsum, habel, hc_partial x, hc_k, summatory_self, hIocIcc]
    simp [c, mul_comm]
    ring

theorem partial_summation_cont {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (f f' : ℝ → 𝕜)
    {k : ℕ} {x : ℝ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Icc (k : ℝ) x, HasDerivAt f (f' i) i)
    (hf' : ContinuousOn f' (Icc k x)) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation _ _ _ hk hf hf'.integrableOn_Icc

theorem partial_summation_cont' {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜)
    (f f' : ℝ → 𝕜) {k : ℕ} (hk : k ≠ 0)
    (hf : ∀ i ∈ Ici (k : ℝ), HasDerivAt f (f' i) i)
    (hf' : ContinuousOn f' (Ici k)) (x : ℝ) :
  summatory (fun n ↦ a n * f n) k x =
    summatory a k x * f x - ∫ t in Icc (k : ℝ) x, summatory a k t * f' t := by
  exact partial_summation_cont _ _ _ hk (fun i hi => hf i hi.1) (hf'.mono Icc_subset_Ici_self)

lemma fract_mul_integrable {f : ℝ → ℝ} (s : Set ℝ)
  (hf' : IntegrableOn f s) :
  IntegrableOn (Int.fract * f) s := by
  refine Integrable.mono hf' ?_ (Filter.Eventually.of_forall ?_)
  · exact measurable_fract.aestronglyMeasurable.mul hf'.1
  · intro x
    simp only [norm_mul, Pi.mul_apply, norm_of_nonneg (Int.fract_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le

lemma is_O_with_one_fract_mul (f : ℝ → ℝ) :
  Asymptotics.IsBigOWith 1 atTop (fun (x : ℝ) ↦ Int.fract x * f x) f := by
  apply Asymptotics.IsBigOWith.of_bound (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [one_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Real.norm_of_nonneg (Int.fract_nonneg _)]
  exact (Int.fract_lt_one x).le

lemma summatory_log_aux {x : ℝ} (hx : 1 ≤ x) :
  summatory (fun i ↦ log i) 1 x - (x * log x - x) =
    1 + ((∫ t in 1..x, Int.fract t * t⁻¹) - Int.fract x * log x) := by
  rw [intervalIntegral.integral_of_le hx]
  have diff : ∀ i ∈ Ici (1 : ℝ), HasDerivAt log (i⁻¹) i := by
    intro i hi
    exact Real.hasDerivAt_log (show i ≠ 0 by exact (zero_lt_one.trans_le hi).ne')
  have cont : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Ici 1) := by
    refine ContinuousOn.inv₀ (f := fun x : ℝ ↦ x) (s := Ici 1) continuousOn_id ?_
    intro x hx
    exact (zero_lt_one.trans_le hx).ne'
  have ps := partial_summation_cont' (fun _ ↦ (1 : ℝ)) _ _ one_ne_zero
    (by exact_mod_cast diff) (by exact_mod_cast cont) x
  simp only [one_mul] at ps
  simp only [ps, integral_Icc_eq_integral_Ioc]
  clear ps
  rw [summatory_const_one, Nat.cast_floor_eq_cast_int_floor (zero_le_one.trans hx),
    ← Int.self_sub_fract, sub_mul, sub_sub (x * log x), sub_sub_sub_cancel_left,
    sub_eq_iff_eq_add, add_assoc, ← sub_eq_iff_eq_add', ← add_assoc, sub_add_cancel, Nat.cast_one,
    ← integral_add]
  · have hEqOn :
        EqOn (fun _ : ℝ ↦ (1 : ℝ))
          (fun y : ℝ ↦ Int.fract y * y⁻¹ + summatory (fun _ ↦ (1 : ℝ)) 1 y * y⁻¹) (Ioc 1 x) := by
      intro y hy
      have hy' : 0 < y := zero_lt_one.trans hy.1
      have hs : summatory (fun _ ↦ (1 : ℝ)) 1 y = (⌊y⌋ : ℝ) := by
        simpa [Nat.cast_floor_eq_cast_int_floor hy'.le] using (summatory_const_one (x := y))
      dsimp
      rw [hs]
      have hyinv : y * y⁻¹ = (1 : ℝ) := by
        field_simp [hy'.ne']
      calc
        (1 : ℝ) = y * y⁻¹ := by simpa using hyinv.symm
        _ = (Int.fract y + (⌊y⌋ : ℝ)) * y⁻¹ := by
          rw [Int.fract_add_floor]
        _ = Int.fract y * y⁻¹ + (⌊y⌋ : ℝ) * y⁻¹ := by ring
    rw [← integral_one, intervalIntegral.integral_of_le hx,
      setIntegral_congr_fun measurableSet_Ioc hEqOn]
  · refine fract_mul_integrable _ ?_
    exact (cont.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact
      (partial_summation_integrable _ ((cont.mono Icc_subset_Ici_self).integrableOn_Icc)).mono_set
        Ioc_subset_Icc_self

lemma is_o_const_of_tendsto_at_top (f : ℝ → ℝ) (l : Filter ℝ) (h : Tendsto f l atTop)
    (c : ℝ) :
  Asymptotics.IsLittleO l (fun _ : ℝ ↦ c) f := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hbound : ∀ᶠ x : ℝ in atTop, ‖c‖ ≤ ε * ‖x‖ := by
    filter_upwards [eventually_ge_atTop (‖c‖ * ε⁻¹), eventually_ge_atTop (0 : ℝ)] with x hx₁ hx₂
    rw [norm_of_nonneg hx₂]
    calc
      ‖c‖ = ε * (‖c‖ * ε⁻¹) := by
        field_simp [hε.ne']
      _ ≤ ε * x := mul_le_mul_of_nonneg_left hx₁ hε.le
  exact h.eventually hbound

lemma is_o_one_log (c : ℝ) : Asymptotics.IsLittleO atTop (fun _ : ℝ ↦ c) log := by
  exact is_o_const_of_tendsto_at_top _ _ Real.tendsto_log_atTop _

lemma summatory_log {c : ℝ} (hc : 2 < c) :
  Asymptotics.IsBigOWith c atTop
    (fun x ↦ summatory (fun i ↦ log i) 1 x - (x * log x - x))
    (fun x ↦ log x) := by
  have f₁ : Asymptotics.IsBigOWith 1 atTop (fun x : ℝ ↦ Int.fract x * log x) log :=
    is_O_with_one_fract_mul _
  have f₂ : Asymptotics.IsLittleO atTop (fun x : ℝ ↦ (1 : ℝ)) log := is_o_one_log _
  have f₃ : Asymptotics.IsBigOWith 1 atTop (fun x : ℝ ↦ ∫ t in 1..x, Int.fract t * t⁻¹) log := by
    simp only [Asymptotics.isBigOWith_iff, eventually_atTop, one_mul]
    refine ⟨1, ?_⟩
    intro x hx
    rw [norm_of_nonneg (Real.log_nonneg hx), norm_of_nonneg, ← div_one x,
      ← integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx), div_one]
    · have h₁ : IntervalIntegrable (fun u : ℝ ↦ u⁻¹) volume 1 x := by
        simpa [one_div] using
          (intervalIntegral.intervalIntegrable_one_div (μ := volume)
            (fun y hy => by
              rw [uIcc_of_le hx] at hy
              exact (zero_lt_one.trans_le hy.1).ne')
            continuousOn_id)
      have hInvOn : IntegrableOn (fun u : ℝ ↦ u⁻¹) (Icc 1 x) := by
        rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        exact h₁
      have hfract :
          IntervalIntegrable (fun y : ℝ ↦ Int.fract y * y⁻¹) volume 1 x := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
        change IntegrableOn (Int.fract * fun y : ℝ ↦ y⁻¹) (Icc 1 x)
        exact fract_mul_integrable (s := Icc 1 x) hInvOn
      have h₂ : ∀ y ∈ Icc 1 x, Int.fract y * y⁻¹ ≤ y⁻¹ := by
        intro y hy
        refine mul_le_of_le_one_left (inv_nonneg.2 (zero_le_one.trans hy.1)) (Int.fract_lt_one _).le
      exact intervalIntegral.integral_mono_on (μ := volume) hx hfract h₁ h₂
    · refine intervalIntegral.integral_nonneg hx ?_
      intro y hy
      exact mul_nonneg (Int.fract_nonneg _) (inv_nonneg.2 (zero_le_one.trans hy.1))
  refine (f₂.add_isBigOWith (f₃.sub f₁) ?_).congr' rfl ?_ Filter.EventuallyEq.rfl
  · norm_num [hc]
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simpa using (summatory_log_aux hx).symm

lemma summatory_mul_floor_eq_summatory_sum_divisors {x y : ℝ}
  (hy : 0 ≤ x) (xy : x ≤ y) (f : ℕ → ℝ) :
  summatory (fun n ↦ f n * ⌊x / n⌋) 1 y =
    summatory (fun n ↦ ∑ i ∈ n.divisors, f i) 1 x := by
  simp_rw [summatory, ← Nat.cast_floor_eq_cast_int_floor (div_nonneg hy (Nat.cast_nonneg _)),
    ← summatory_const_one, summatory, Finset.mul_sum, mul_one]
  calc
    ∑ i ∈ Finset.Icc 1 ⌊y⌋₊, ∑ j ∈ Finset.Icc 1 ⌊x / i⌋₊, f i
      = ∑ i ∈ Finset.Icc 1 ⌊y⌋₊,
          ∑ n ∈ (Finset.Icc 1 ⌊x / i⌋₊).image (fun j => i * j), f i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            symm
            refine Finset.sum_image ?_
            intro a ha b hb hab
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            exact Nat.eq_of_mul_eq_mul_left (Nat.succ_le_iff.mp hi1) hab
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ i ∈ n.divisors, f i := by
          refine Finset.sum_comm'
            (t := fun i : ℕ => (Finset.Icc 1 ⌊x / i⌋₊).image fun j : ℕ => i * j)
            (t' := (Finset.Icc 1 ⌊x⌋₊ : Finset ℕ)) (s' := fun n : ℕ => n.divisors)
            (f := fun i (_n : ℕ) => f i) ?_
          intro i n
          constructor
          · rintro ⟨hi, hn⟩
            rw [Finset.mem_image] at hn
            rcases hn with ⟨j, hj, rfl⟩
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
            have hjx : (j : ℝ) ≤ x / i := by
              exact
                (Nat.le_floor_iff (div_nonneg hy (Nat.cast_nonneg i))).1
                  ((Finset.mem_Icc.mp hj).2)
            have hxij : ((i * j : ℕ) : ℝ) ≤ x := by
              have hmul : (i : ℝ) * j ≤ (i : ℝ) * (x / i) :=
                mul_le_mul_of_nonneg_left hjx (show 0 ≤ (i : ℝ) by positivity)
              have hdiv : (i : ℝ) * (x / i) = x := by
                field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.succ_le_iff.mp hi1))]
              simpa [Nat.cast_mul, hdiv] using hmul
            have hi_ne : i ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hi1)
            have hj_ne : j ≠ 0 := Nat.ne_of_gt (Nat.succ_le_iff.mp hj1)
            have hij_ne : i * j ≠ 0 := Nat.mul_ne_zero hi_ne hj_ne
            refine ⟨?_, ?_⟩
            · rw [Nat.mem_divisors]
              exact ⟨dvd_mul_right i j, hij_ne⟩
            · rw [Finset.mem_Icc]
              exact ⟨Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hij_ne),
                (Nat.le_floor_iff hy).2 hxij⟩
          · rintro ⟨hin, hn⟩
            rw [Nat.mem_divisors] at hin
            rcases hin with ⟨⟨j, rfl⟩, hij_ne⟩
            have hi_ne : i ≠ 0 := by
              intro hi0
              exact hij_ne (by simp [hi0])
            have hj_ne : j ≠ 0 := by
              intro hj0
              exact hij_ne (by simp [hj0])
            have hi1 : 1 ≤ i := Nat.succ_le_iff.mpr (Nat.pos_iff_ne_zero.mpr hi_ne)
            have hj1 : 1 ≤ j := Nat.succ_le_iff.mpr (Nat.pos_iff_ne_zero.mpr hj_ne)
            have hxij : ((i * j : ℕ) : ℝ) ≤ x := (Nat.le_floor_iff hy).1 (Finset.mem_Icc.mp hn).2
            have hix : (i : ℝ) ≤ x := by
              exact
                le_trans
                  (by
                    exact_mod_cast Nat.le_mul_of_pos_right i
                      (Nat.pos_iff_ne_zero.mpr hj_ne))
                  hxij
            have hiy : (i : ℝ) ≤ y := le_trans hix xy
            have hjx : (j : ℝ) ≤ x / i := by
              exact
                (le_div_iff₀ (Nat.cast_pos.2 hi1)).2
                  (by simpa [Nat.cast_mul, mul_comm] using hxij)
            refine ⟨Finset.mem_Icc.mpr ⟨hi1, (Nat.le_floor_iff (hy.trans xy)).2 hiy⟩, ?_⟩
            rw [Finset.mem_image]
            exact ⟨j, Finset.mem_Icc.mpr ⟨hj1,
              (Nat.le_floor_iff (div_nonneg hy (Nat.cast_nonneg i))).2 hjx⟩, rfl⟩

lemma von_mangoldt_summatory {x y : ℝ} (hx : 0 ≤ x) (xy : x ≤ y) :
  summatory (fun n ↦ Λ n * ⌊x / n⌋) 1 y = summatory (fun n ↦ Real.log n) 1 x := by
  simpa using
    (summatory_mul_floor_eq_summatory_sum_divisors hx xy (fun n => Λ n)).trans <| by
      simp_rw [ArithmeticFunction.vonMangoldt_sum]

lemma helpful_floor_identity2 {x : ℝ} (hx₁ : 1 ≤ x) (hx₂ : x < 2) :
  ⌊x⌋ - 2 * ⌊x/2⌋ = 1 := by
  have h₁ : ⌊x⌋ = 1 := by
    rw [Int.floor_eq_iff]
    exact ⟨by simpa using hx₁, by simpa [one_add_one_eq_two] using hx₂⟩
  have h₂ : ⌊x / 2⌋ = 0 := by
    rw [Int.floor_eq_iff]
    norm_num
    constructor <;> linarith
  rw [h₁, h₂]
  simp

lemma helpful_floor_identity3 {x : ℝ} :
  2 * ⌊x/2⌋ ≤ ⌊x⌋ := by
  have h₄ : (2 * ⌊x / 2⌋ : Int) - 1 < ⌊x⌋ := by
    exact_mod_cast (show (2 : ℝ) * ⌊x / 2⌋ - 1 < ⌊x⌋ by
      linarith [Int.floor_le (x / 2), Int.sub_one_lt_floor x])
  exact Int.sub_one_lt_iff.mp h₄

def chebyshev_error (x : ℝ) : ℝ := by
  exact
    (summatory (fun i ↦ Real.log i) 1 x - (x * log x - x)) -
      2 * (summatory (fun i ↦ Real.log i) 1 (x / 2) - (x / 2 * log (x / 2) - x / 2))

lemma von_mangoldt_floor_sum {x : ℝ} (hx₀ : 0 < x) :
  summatory (fun n ↦ Λ n * (⌊x / n⌋ - 2 * ⌊x / n / 2⌋)) 1 x =
    Real.log 2 * x + chebyshev_error x := by
  have hhalf :
      summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x =
        summatory (fun n ↦ Real.log n) 1 (x / 2) := by
    rw [show summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x =
        summatory (fun n ↦ Λ n * ⌊(x / 2) / n⌋) 1 x by
          rw [summatory]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [div_right_comm]]
    exact von_mangoldt_summatory (div_nonneg hx₀.le zero_le_two) (half_le_self hx₀.le)
  have hx2 : (2 : ℝ) * (x / 2) = x := by
    simpa using (mul_div_cancel₀ x two_ne_zero)
  calc
    summatory (fun n ↦ Λ n * (⌊x / n⌋ - 2 * ⌊x / n / 2⌋)) 1 x
      = summatory (fun n ↦ Λ n * ⌊x / n⌋) 1 x -
          2 * summatory (fun n ↦ Λ n * ⌊x / n / 2⌋) 1 x := by
            rw [summatory, summatory, summatory, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
    _ = summatory (fun n ↦ Real.log n) 1 x - 2 * summatory (fun n ↦ Real.log n) 1 (x / 2) := by
          rw [von_mangoldt_summatory hx₀.le le_rfl, hhalf]
    _ = Real.log 2 * x + chebyshev_error x := by
          rw [chebyshev_error, mul_sub, Real.log_div hx₀.ne' two_ne_zero, mul_sub, hx2]
          ring

def chebyshev_first' (x : ℝ) : ℝ := by
  exact ∑ n ∈ (Finset.range ⌊x⌋₊).filter Nat.Prime, Real.log n

def chebyshev_second' (x : ℝ) : ℝ := by
  exact Finset.sum (Finset.range ⌊x⌋₊) fun n => Λ n

lemma chebyshev_first_le_chebyshev_second : chebyshev_first ≤ chebyshev_second := by
  intro x
  exact Chebyshev.theta_le_psi x

lemma chebyshev_first_nonneg : 0 ≤ chebyshev_first := by
  intro x
  exact Chebyshev.theta_nonneg x

lemma chebyshev_second_nonneg : 0 ≤ chebyshev_second := by
  intro x
  exact Chebyshev.psi_nonneg x

lemma is_O_chebyshev_first_chebyshev_second :
    Asymptotics.IsBigO atTop chebyshev_first chebyshev_second := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards with x
  rw [one_mul, norm_of_nonneg (chebyshev_first_nonneg x),
    norm_of_nonneg (chebyshev_second_nonneg x)]
  exact chebyshev_first_le_chebyshev_second x

lemma chebyshev_second_eq_summatory : chebyshev_second = summatory Λ 1 := by
  ext x
  change Chebyshev.psi x = summatory (⇑Λ) 1 x
  rw [Chebyshev.psi_eq_sum_Icc, summatory]
  rw [Finset.Icc_eq_insert_Icc_succ (Nat.zero_le _), Finset.sum_insert]
  · simp
  · simp

@[simp] lemma chebyshev_first_zero : chebyshev_first 0 = 0 := by
  exact Chebyshev.theta_eq_zero_of_lt_two (show (0 : ℝ) < 2 by norm_num)

@[simp] lemma chebyshev_second_zero : chebyshev_second 0 = 0 := by
  exact Chebyshev.psi_eq_zero_of_lt_two (show (0 : ℝ) < 2 by norm_num)

@[simp] lemma chebyshev_first'_zero : chebyshev_first' 0 = 0 := by
  simp [chebyshev_first']

@[simp] lemma chebyshev_second'_zero : chebyshev_second' 0 = 0 := by
  simp [chebyshev_second']

lemma chebyshev_upper_aux {x : ℝ} (hx : 0 < x) :
  chebyshev_second x - chebyshev_second (x / 2) - Real.log 2 * x ≤ chebyshev_error x := by
  rw [sub_le_iff_le_add', ← von_mangoldt_floor_sum hx, chebyshev_second_eq_summatory, summatory]
  have hs : Finset.Icc 1 ⌊x / 2⌋₊ ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    exact Finset.Icc_subset_Icc le_rfl (Nat.floor_mono (half_le_self hx.le))
  rw [summatory, ← Finset.sum_sdiff hs, add_sub_cancel_right]
  refine (Finset.sum_le_sum ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_)
  · simp_rw [Finset.mem_sdiff, Finset.mem_Icc, and_imp, not_and, not_le, Nat.le_floor_iff hx.le,
      Nat.floor_lt (div_nonneg hx.le zero_le_two), Nat.succ_le_iff]
    intro i hi₁ hi₂ hi₃
    replace hi₃ := hi₃ hi₁
    have hge1 : 1 ≤ x / i := by
      refine (one_le_div₀ ?_).2 hi₂
      exact_mod_cast hi₁
    have hlt2 : x / i < 2 := by
      have hi_pos : (0 : ℝ) < i := by
        exact_mod_cast hi₁
      have hmul : x < 2 * i := by
        linarith
      exact (div_lt_iff₀ hi_pos).2 (by simpa [mul_comm] using hmul)
    have hEq : (↑⌊x / ↑i⌋ - 2 * ↑⌊x / ↑i / 2⌋ : ℝ) = 1 := by
      exact_mod_cast (helpful_floor_identity2 (x := x / i) hge1 hlt2)
    rw [hEq, mul_one]
  · intro i _ _
    have hcoeff' : (2 : ℝ) * ↑⌊x / ↑i / 2⌋ ≤ ↑⌊x / ↑i⌋ := by
      exact_mod_cast (helpful_floor_identity3 (x := x / i))
    have hcoeff : 0 ≤ (↑⌊x / ↑i⌋ - 2 * ↑⌊x / ↑i / 2⌋ : ℝ) := by
      linarith
    simpa [mul_sub, mul_assoc, mul_left_comm, mul_comm] using
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hcoeff)

lemma chebyshev_error_O :
  Asymptotics.IsBigO atTop chebyshev_error log := by
  have h23 : (2 : ℝ) < 3 := by norm_num
  refine (summatory_log h23).isBigO.sub ?_
  refine (((summatory_log h23).isBigO.comp_tendsto
    (tendsto_id.atTop_div_const zero_lt_two)).const_mul_left 2).trans ?_
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hxhalf : 1 ≤ x / 2 := by linarith
  have hxlog : log (x / 2) ≤ log x := log_le_log_of_le (by linarith) (by linarith)
  simpa [Function.comp_apply, one_mul, norm_of_nonneg (log_nonneg hxhalf),
    norm_of_nonneg (log_nonneg (one_le_two.trans hx))] using hxlog

lemma chebyshev_trivial_upper_nat (n : ℕ) :
  chebyshev_second n ≤ n * Real.log n := by
  rw [chebyshev_second_eq_summatory, summatory_nat, ← nsmul_eq_mul]
  refine (Finset.sum_le_card_nsmul _ _ (Real.log n) ?_).trans ?_
  · intro i hi
    apply von_mangoldt_upper.trans
    simp only [Finset.mem_Icc] at hi
    exact log_le_log_of_le (by exact_mod_cast hi.1) (by exact_mod_cast hi.2)
  · simp

lemma chebyshev_trivial_upper {x : ℝ} (hx : 1 ≤ x) :
  chebyshev_second x ≤ x * log x := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  rw [chebyshev_second_eq_summatory, summatory_eq_floor, ← chebyshev_second_eq_summatory]
  refine (chebyshev_trivial_upper_nat _).trans ?_
  refine mul_le_mul (Nat.floor_le hx₀.le)
    ?_ (log_nonneg (by
      have : (1 : ℝ) ≤ ⌊x⌋₊ := by
        exact_mod_cast (Nat.one_le_floor_iff x).2 hx
      exact this)) hx₀.le
  · exact log_le_log_of_le (by
      have hfloorpos : 0 < (⌊x⌋₊ : ℝ) := by
        exact_mod_cast (Nat.floor_pos.mpr hx)
      exact hfloorpos) (Nat.floor_le hx₀.le)

lemma chebyshev_upper_inductive {c : ℝ} (hc : Real.log 2 < c) :
  ∃ C, 1 ≤ C ∧ ∀ x : ℕ, chebyshev_second x ≤ 2 * c * x + C * log C := by
  have h₁ := (chebyshev_error_O.trans_isLittleO isLittleO_log_id_atTop).bound (sub_pos_of_lt hc)
  obtain ⟨C₀, hC₀⟩ := Filter.eventually_atTop.mp h₁
  let C : ℝ := max 1 C₀
  refine ⟨C, le_max_left _ _, ?_⟩
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  by_cases hn : (n : ℝ) ≤ C
  · rw [chebyshev_second_eq_summatory]
    refine
      (summatory_monotone_of_nonneg _ _ (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg) hn).trans
        ?_
    rw [← chebyshev_second_eq_summatory]
    refine (chebyshev_trivial_upper (le_max_left _ _)).trans ?_
    refine le_add_of_nonneg_left (mul_nonneg ?_ (Nat.cast_nonneg _))
    exact mul_nonneg zero_le_two ((Real.log_nonneg one_le_two).trans hc.le)
  · have hn : C < n := lt_of_not_ge hn
    have hn' : 0 < n := by
      refine Nat.succ_le_iff.mp ?_
      exact Nat.one_le_cast.mp ((le_max_left _ _).trans hn.le)
    have h₁ := chebyshev_upper_aux (Nat.cast_pos.mpr hn')
    rw [sub_sub, sub_le_iff_le_add] at h₁
    apply h₁.trans
    rw [chebyshev_second_eq_summatory, summatory_eq_floor, ← Nat.cast_two,
      Nat.floor_div_eq_div, Nat.cast_two, ← add_assoc]
    have h₃ := hC₀ (n : ℝ) ((le_max_right _ _).trans hn.le)
    rw [Real.norm_eq_abs] at h₃
    replace h₃ := le_of_abs_le h₃
    have h₂ := ih (n / 2) (Nat.div_lt_self hn' one_lt_two)
    rw [← chebyshev_second_eq_summatory]
    have hsum :
        chebyshev_error (n : ℝ) + chebyshev_second (n / 2 : ℕ) + Real.log 2 * (n : ℝ) ≤
          (c - Real.log 2) * ‖(n : ℝ)‖ + (2 * c * (n / 2 : ℕ) + C * log C) +
            Real.log 2 * (n : ℝ) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_right (add_le_add h₃ h₂) (Real.log 2 * (n : ℝ))
    refine hsum.trans ?_
    have hc0 : 0 ≤ c := (Real.log_nonneg one_le_two).trans hc.le
    have hdiv : ((n / 2 : ℕ) : ℝ) ≤ n / 2 := Nat.cast_div_le
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    nlinarith

lemma chebyshev_upper_real {c : ℝ} (hc : 2 * Real.log 2 < c) :
  ∃ C, 1 ≤ C ∧
    Asymptotics.IsBigOWith 1 atTop chebyshev_second (fun x ↦ c * x + C * log C) := by
  have hc' : Real.log 2 < c / 2 := by
    nlinarith
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_inductive hc'
  refine ⟨C, hC₁, ?_⟩
  apply Asymptotics.IsBigOWith.of_bound
  rw [eventually_atTop]
  refine ⟨0, ?_⟩
  intro x hx
  rw [Real.norm_of_nonneg (chebyshev_second_nonneg x), chebyshev_second_eq_summatory,
    summatory_eq_floor, ← chebyshev_second_eq_summatory, one_mul]
  refine (hC ⌊x⌋₊).trans (le_trans ?_ (le_abs_self _))
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc0 : 0 ≤ c := by nlinarith
  have hmul : c * (⌊x⌋₊ : ℝ) ≤ c * x := mul_le_mul_of_nonneg_left hfloor hc0
  have hEq : 2 * (c / 2) * (⌊x⌋₊ : ℝ) = c * (⌊x⌋₊ : ℝ) := by ring
  simpa [hEq, add_assoc, add_left_comm, add_comm] using add_le_add_right hmul (C * log C)

lemma chebyshev_upper_explicit {c : ℝ} (hc : 2 * Real.log 2 < c) :
  Asymptotics.IsBigOWith c atTop chebyshev_second id := by
  let c' : ℝ := Real.log 2 + c / 2
  have hc'₁ : c' < c := by
    dsimp [c']
    nlinarith
  have hc'₂ : 2 * Real.log 2 < c' := by
    dsimp [c']
    nlinarith
  have hc'₀ : 0 ≤ c' := by
    dsimp [c']
    nlinarith [Real.log_nonneg one_le_two, hc]
  obtain ⟨C, hC₁, hC⟩ := chebyshev_upper_real hc'₂
  have hconst : (fun _ : ℝ ↦ C * log C) =o[atTop] id := by
    exact (isLittleO_const_left.2 <| Or.inr tendsto_abs_atTop_atTop)
  have hmain : Asymptotics.IsBigOWith c atTop (fun x ↦ c' * x + C * log C) id := by
    have hc'₁' : ‖c'‖ < c := by
      simpa [Real.norm_of_nonneg hc'₀] using hc'₁
    simpa [c'] using
      (Asymptotics.isBigOWith_const_mul_self c' id atTop).add_isLittleO hconst hc'₁'
  exact (hC.trans hmain zero_le_one).congr_const (one_mul c)

lemma chebyshev_upper : Asymptotics.IsBigO atTop chebyshev_second id := by
  exact (chebyshev_upper_explicit (lt_add_one _)).isBigO

lemma chebyshev_first_upper : Asymptotics.IsBigO atTop chebyshev_first id := by
  exact is_O_chebyshev_first_chebyshev_second.trans chebyshev_upper

lemma is_O_sum_one_of_summable {f : ℕ → ℝ} (hf : Summable f) :
  Asymptotics.IsBigO atTop (fun (n : ℕ) ↦ ∑ i ∈ Finset.range n, f i)
    (fun _ ↦ (1 : ℝ)) := by
  simpa using hf.hasSum.tendsto_sum_nat.isBigO_one ℝ

lemma log_le_thing {x : ℝ} (hx : 1 ≤ x) :
  log x ≤ x^(1/2 : ℝ) - x^(-1/2 : ℝ) := by
  set f : ℝ → ℝ := log
  set g : ℝ → ℝ := fun x ↦ x^(1 / 2 : ℝ) - x^(-1 / 2 : ℝ)
  set f' : ℝ → ℝ := Inv.inv
  set g' : ℝ → ℝ := fun x ↦ 1 / 2 * x^(-3 / 2 : ℝ) + 1 / 2 * x^(-1 / 2 : ℝ)
  suffices h : ∀ y ∈ Icc (1 : ℝ) x, f y ≤ g y by
    exact h x ⟨hx, le_rfl⟩
  have f_deriv : ∀ y ∈ Ico (1 : ℝ) x, HasDerivWithinAt f (f' y) (Ici y) y := by
    intro y hy
    exact (hasDerivAt_log (zero_lt_one.trans_le hy.1).ne').hasDerivWithinAt
  have g_deriv : ∀ y ∈ Ico (1 : ℝ) x, HasDerivWithinAt g (g' y) (Ici y) y := by
    intro y hy
    have hy' : 0 < y := zero_lt_one.trans_le hy.1
    change HasDerivWithinAt _ (_ + _) _ _
    rw [add_comm, ← sub_neg_eq_add, neg_mul_eq_neg_mul]
    refine HasDerivWithinAt.sub ?_ ?_
    · have hpow : (2⁻¹ : ℝ) - 1 = -1 / 2 := by norm_num
      simpa [Set.Ici, id, one_mul, hpow] using
        ((hasDerivWithinAt_id y (Set.Ici y)).rpow_const
          (p := (1 / 2 : ℝ)) (Or.inl hy'.ne'))
    · have hpow : (-1 / 2 : ℝ) - 1 = -3 / 2 := by norm_num
      have hpow' : (-2⁻¹ : ℝ) - 1 = -3 / 2 := by norm_num
      have hcoef : (-1 / 2 : ℝ) = -2⁻¹ := by norm_num
      have hderiv :=
        ((hasDerivWithinAt_id y (Set.Ici y)).rpow_const
          (p := (-1 / 2 : ℝ)) (Or.inl hy'.ne'))
      simpa [Set.Ici, id, one_mul, hpow, hpow', hcoef, neg_mul, mul_assoc] using hderiv
  have hmain :=
    image_le_of_deriv_right_le_deriv_boundary
      (f := f) (f' := f') (a := 1) (b := x)
      (continuousOn_log.mono fun y hy ↦ (zero_lt_one.trans_le hy.1).ne')
      f_deriv
      (by simp [f])
      ((continuousOn_id.rpow_const (by simp)).sub
        (continuousOn_id.rpow_const fun y hy ↦ Or.inl (zero_lt_one.trans_le hy.1).ne'))
      g_deriv
      (by
        intro y hy
        dsimp [f', g']
        rw [← mul_add, mul_comm, ← div_eq_mul_one_div,
          le_div_iff₀ (show (0 : ℝ) < 2 by norm_num), ← sub_nonneg, ← Real.rpow_neg_one]
        convert sq_nonneg (y^(-1 / 4 : ℝ) - y^(-3 / 4 : ℝ)) using 1
        have hy' : 0 < y := zero_lt_one.trans_le hy.1
        rw [sub_sq, ← Real.rpow_natCast, ← Real.rpow_natCast, Nat.cast_two,
          ← Real.rpow_mul hy'.le, mul_assoc, ← Real.rpow_add hy', ← Real.rpow_mul hy'.le]
        norm_num
        ring)
  intro y hy
  exact hmain hy

lemma log_div_sq_sub_le {x : ℝ} (hx : 1 < x) :
  log x * ((x⁻¹)^2 / (1 - x⁻¹)) ≤ x^(-3/2 : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hx' : x ≠ 0 := hx0.ne'
  have hden : 0 < x * (x - 1) := by nlinarith
  have hrewrite : (x⁻¹)^2 / (1 - x⁻¹) = 1 / (x * (x - 1)) := by
    field_simp [hx']
  rw [hrewrite, ← div_eq_mul_one_div]
  rw [div_le_iff₀ hden]
  calc
    log x ≤ x ^ (1 / 2 : ℝ) - x ^ (-1 / 2 : ℝ) := log_le_thing hx.le
    _ = x ^ (-3 / 2 : ℝ) * (x * (x - 1)) := by
      have hx1 : x ^ (-3 / 2 : ℝ) * x = x ^ (-1 / 2 : ℝ) := by
        calc
          x ^ (-3 / 2 : ℝ) * x = x ^ (-3 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ (-1 / 2 : ℝ) := by rw [← Real.rpow_add hx0 (-3 / 2 : ℝ) 1]; norm_num
      have hx2 : x ^ (-1 / 2 : ℝ) * x = x ^ (1 / 2 : ℝ) := by
        calc
          x ^ (-1 / 2 : ℝ) * x = x ^ (-1 / 2 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hx0 (-1 / 2 : ℝ) 1]; norm_num
      calc
        x ^ (1 / 2 : ℝ) - x ^ (-1 / 2 : ℝ)
            = x ^ (-1 / 2 : ℝ) * x - x ^ (-1 / 2 : ℝ) := by rw [hx2]
        _ = x ^ (-1 / 2 : ℝ) * (x - 1) := by ring
        _ = (x ^ (-3 / 2 : ℝ) * x) * (x - 1) := by rw [hx1]
        _ = x ^ (-3 / 2 : ℝ) * (x * (x - 1)) := by ring

@[to_additive]
lemma prod_prime_powers' {M : Type*} [CommMonoid M] {x : ℕ} {f : ℕ → M} :
  ∏ n ∈ (Finset.Icc 1 x).filter IsPrimePow, f n =
    ∏ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
      ∏ k ∈ (Finset.Icc 1 x).filter (fun k ↦ p ^ k ≤ x), f (p ^ k) := by
  rw [Finset.prod_sigma', eq_comm]
  refine Finset.prod_bij (fun pk _ ↦ pk.1 ^ pk.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ hpk
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hpk
    simp only [Finset.mem_filter, Finset.mem_Icc, isPrimePow_nat_iff]
    exact ⟨⟨Nat.one_le_pow _ _ hpk.1.1.1, hpk.2.2⟩, p, k, hpk.1.2, hpk.2.1.1, rfl⟩
  · intro a₁ h₁ a₂ h₂ h
    rcases a₁ with ⟨p₁, k₁⟩
    rcases a₂ with ⟨p₂, k₂⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at h₁ h₂
    have hp : p₁ = p₂ := eq_of_prime_pow_eq (Nat.prime_iff.mp h₁.1.2) (Nat.prime_iff.mp h₂.1.2)
      h₁.2.1.1 h
    subst hp
    have hk : k₁ = k₂ := Nat.pow_right_injective h₂.1.2.two_le h
    subst hk
    rfl
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases (isPrimePow_nat_iff n).1 hn.2 with ⟨p, k, hp, hk, rfl⟩
    have hpkx : p ^ k ≤ x := hn.1.2
    have hpk : p ≤ x := (Nat.le_self_pow hk.ne' p).trans hpkx
    have hkx : k ≤ x := by
      exact (Nat.le_of_lt k.lt_two_pow_self).trans <|
        (Nat.pow_le_pow_left hp.two_le k).trans hpkx
    exact ⟨⟨p, k⟩, by
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hp.one_le, hpk⟩, hp⟩, ⟨⟨hk, hkx⟩, hpkx⟩⟩, rfl⟩
  · simp

@[to_additive]
lemma prod_prime_powers {M : Type*} [CommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∏ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∏ k ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun k ↦ (p ^ k : ℝ) ≤ x), f (p ^ k) := by
  rw [prod_prime_powers']
  refine Finset.prod_congr rfl ?_
  intro p hp
  refine Finset.prod_congr (Finset.filter_congr fun k _ ↦ ?_) fun _ _ ↦ rfl
  rw [Nat.le_floor_iff']
  · simp [Nat.cast_pow]
  · rw [Finset.mem_filter] at hp
    exact pow_ne_zero _ hp.2.ne_zero

lemma sum_prime_powers' {M : Type*} [AddCommMonoid M] {x : ℕ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 x).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 x).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 x).filter (fun k ↦ p ^ k ≤ x), f (p ^ k) := by
  rw [Finset.sum_sigma', eq_comm]
  refine Finset.sum_bij (fun pk _ ↦ pk.1 ^ pk.2) ?_ ?_ ?_ ?_
  · rintro ⟨p, k⟩ hpk
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hpk
    simp only [Finset.mem_filter, Finset.mem_Icc, isPrimePow_nat_iff]
    exact ⟨⟨Nat.one_le_pow _ _ hpk.1.1.1, hpk.2.2⟩, p, k, hpk.1.2, hpk.2.1.1, rfl⟩
  · intro a₁ h₁ a₂ h₂ h
    rcases a₁ with ⟨p₁, k₁⟩
    rcases a₂ with ⟨p₂, k₂⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at h₁ h₂
    have hp : p₁ = p₂ := eq_of_prime_pow_eq (Nat.prime_iff.mp h₁.1.2) (Nat.prime_iff.mp h₂.1.2)
      h₁.2.1.1 h
    subst hp
    have hk : k₁ = k₂ := Nat.pow_right_injective h₂.1.2.two_le h
    subst hk
    rfl
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases (isPrimePow_nat_iff n).1 hn.2 with ⟨p, k, hp, hk, rfl⟩
    have hpkx : p ^ k ≤ x := hn.1.2
    have hpk : p ≤ x := (Nat.le_self_pow hk.ne' p).trans hpkx
    have hkx : k ≤ x := by
      exact (Nat.le_of_lt k.lt_two_pow_self).trans <|
        (Nat.pow_le_pow_left hp.two_le k).trans hpkx
    exact ⟨⟨p, k⟩, by
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨hp.one_le, hpk⟩, hp⟩, ⟨⟨hk, hkx⟩, hpkx⟩⟩, rfl⟩
  · simp

lemma sum_prime_powers {M : Type*} [AddCommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun k ↦ (p ^ k : ℝ) ≤ x), f (p ^ k) := by
  rw [sum_prime_powers']
  refine Finset.sum_congr rfl ?_
  intro p hp
  refine Finset.sum_congr (Finset.filter_congr fun k _ ↦ ?_) fun _ _ ↦ rfl
  rw [Nat.le_floor_iff']
  · simp [Nat.cast_pow]
  · rw [Finset.mem_filter] at hp
    exact pow_ne_zero _ hp.2.ne_zero

@[to_additive]
lemma exact_prod_prime_powers {M : Type*} [CommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∏ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∏ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∏ k ∈ (Finset.Icc 1 ⌊log x / Real.log p⌋₊), f (p ^ k) := by
  refine prod_prime_powers.trans (Finset.prod_congr rfl fun p hp ↦ ?_)
  rw [Finset.mem_filter, Finset.mem_Icc, and_assoc] at hp
  rcases hp with ⟨hp₁, hp₂, hpPrime⟩
  have hp2' : (p : ℝ) ≤ x := (Nat.le_floor_iff' hpPrime.ne_zero).1 hp₂
  have hx : 0 < x := zero_lt_one.trans_le ((Nat.one_le_cast.2 hp₁).trans hp2')
  refine Finset.prod_congr (Finset.ext fun k ↦ ?_) fun _ _ ↦ rfl
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, Nat.le_floor_iff hx.le, and_assoc,
    and_congr_right fun hk ↦ ?_]
  rw [Nat.le_floor_iff' (Nat.succ_le_iff.1 hk).ne', Real.log_div_log,
    Real.le_logb_iff_rpow_le (by exact_mod_cast hpPrime.one_lt) hx, Real.rpow_natCast,
    and_iff_right_iff_imp]
  intro hk'
  apply le_trans _ hk'
  exact_mod_cast (Nat.lt_pow_self hpPrime.one_lt).le

lemma exact_sum_prime_powers {M : Type*} [AddCommMonoid M] {x : ℝ} {f : ℕ → M} :
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f n =
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 1 ⌊log x / Real.log p⌋₊), f (p ^ k) := by
  refine sum_prime_powers.trans (Finset.sum_congr rfl fun p hp ↦ ?_)
  rw [Finset.mem_filter, Finset.mem_Icc, and_assoc] at hp
  rcases hp with ⟨hp₁, hp₂, hpPrime⟩
  have hp2' : (p : ℝ) ≤ x := (Nat.le_floor_iff' hpPrime.ne_zero).1 hp₂
  have hx : 0 < x := zero_lt_one.trans_le ((Nat.one_le_cast.2 hp₁).trans hp2')
  refine Finset.sum_congr (Finset.ext fun k ↦ ?_) fun _ _ ↦ rfl
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, Nat.le_floor_iff hx.le, and_assoc,
    and_congr_right fun hk ↦ ?_]
  rw [Nat.le_floor_iff' (Nat.succ_le_iff.1 hk).ne', Real.log_div_log,
    Real.le_logb_iff_rpow_le (by exact_mod_cast hpPrime.one_lt) hx, Real.rpow_natCast,
    and_iff_right_iff_imp]
  intro hk'
  apply le_trans _ hk'
  exact_mod_cast (Nat.lt_pow_self hpPrime.one_lt).le

theorem geom_sum_Ico'_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α} (hx₀ : 0 ≤ x) (hx₁ : x < 1) {m n : ℕ} (_hmn : m ≤ n) :
  ∑ i ∈ Finset.Ico m n, x ^ i ≤ x ^ m / (1 - x) := by
  exact geom_sum_Ico_le_of_lt_one hx₀ hx₁

lemma abs_von_mangoldt_div_self_sub_log_div_self_le {x : ℝ} :
  |∑ n ∈ Icc 1 (⌊x⌋₊), Λ n / (n : ℝ) -
      ∑ p ∈ filter Nat.Prime (Icc 1 (⌊x⌋₊)), Real.log p / (p : ℝ)| ≤
    ∑ n ∈ Icc 1 (⌊x⌋₊), (n : ℝ) ^ (-3 / 2 : ℝ) := by
  have h₁ : ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ) =
      ∑ n ∈ filter IsPrimePow (Icc 1 ⌊x⌋₊), Λ n / (n : ℝ) := by
    symm
    refine Finset.sum_filter_of_ne ?_
    intro n hn hne
    exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp <| by
      intro hΛ
      exact hne (by simp [hΛ])
  have h₂ : ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p / (p : ℝ) =
      ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Λ p / (p : ℝ) := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]
  rw [h₁, h₂, sum_prime_powers, ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum ?_
  simp only [Finset.mem_Icc, Nat.cast_pow, and_imp]
  intro p hp₁ hp₂
  split_ifs with hp
  · have hp₃ : (p : ℝ) ≤ x := (Nat.le_floor_iff' hp.ne_zero).1 hp₂
    have hInsert :
        insert 1 (filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊)) =
          filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 1 ⌊x⌋₊) := by
      rw [Finset.Icc_eq_insert_Icc_succ (hp₁.trans hp₂), filter_insert, pow_one, if_pos]
      exact hp₃
    have hnotmem : 1 ∉ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊) := by
      simp
    rw [← hInsert, Finset.sum_insert hnotmem, add_comm, pow_one, pow_one]
    have hcancel :
        (∑ x ∈ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊), Λ (p ^ x) / (p ^ x : ℝ)) +
            Λ p / (p : ℝ) - Λ p / (p : ℝ) =
          ∑ x ∈ filter (fun k ↦ (p ^ k : ℝ) ≤ x) (Icc 2 ⌊x⌋₊), Λ (p ^ x) / (p ^ x : ℝ) := by
      ring
    rw [hcancel]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_).trans ?_
    · intro i hi hmem
      exact abs_nonneg _
    have hsum :
        (∑ i ∈ Icc 2 ⌊x⌋₊, |Λ (p ^ i) / (p ^ i : ℝ)|) =
          ∑ i ∈ Icc 2 ⌊x⌋₊, Λ p / (p ^ i : ℝ) := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [ArithmeticFunction.vonMangoldt_apply_pow
          ((zero_lt_two.trans_le (Finset.mem_Icc.mp hk).1).ne'), abs_div,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_pow, Nat.abs_cast]
    rw [hsum, ArithmeticFunction.vonMangoldt_apply_prime hp]
    simp only [div_eq_mul_inv, ← mul_sum, ← inv_pow]
    refine le_trans ?_ (log_div_sq_sub_le (by exact_mod_cast hp.one_lt))
    rw [show Finset.Icc 2 ⌊x⌋₊ = Finset.Ico 2 (⌊x⌋₊ + 1) by
      ext i
      simp]
    refine mul_le_mul_of_nonneg_left (geom_sum_Ico'_le ?_ ?_ ?_) ?_
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
    · exact Nat.succ_le_succ (hp₁.trans hp₂)
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · rw [abs_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma is_O_von_mangoldt_div_self_sub_log_div_self :
  Asymptotics.IsBigO atTop
    (fun x ↦
      ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹ -
        ∑ p ∈ filter Nat.Prime (Icc 1 (⌊x⌋₊)), Real.log p * (p : ℝ)⁻¹)
    (fun _ : ℝ ↦ (1 : ℝ)) := by
  let g : ℝ → ℝ := fun x ↦ Finset.sum (range (⌊x⌋₊ + 1)) (fun n ↦ (n : ℝ) ^ (-3 / 2 : ℝ))
  have hbound : ∀ x : ℝ,
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ) -
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p / (p : ℝ)‖ ≤ ‖g x‖ := by
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (abs_von_mangoldt_div_self_sub_log_div_self_le (x := x)).trans ?_
    refine le_trans ?_ (le_abs_self _)
    dsimp [g]
    rw [range_eq_Ico]
    exact Finset.sum_mono_set_of_nonneg (fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (Icc_subset_Icc_left zero_le_one)
  have hbound' : ∀ x : ℝ,
      ‖∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ -
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Real.log p * (p : ℝ)⁻¹‖ ≤ 1 * ‖g x‖ := by
    intro x
    simpa [g, div_eq_mul_inv, one_mul] using hbound x
  refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall hbound')).trans ?_
  refine (is_O_sum_one_of_summable ((Real.summable_nat_rpow).2 (by norm_num))).comp_tendsto ?_
  exact (tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop

lemma summatory_log_sub :
  Asymptotics.IsBigO atTop
    (fun x ↦
      (∑ n ∈ Icc 1 (⌊x⌋₊), log (n : ℝ)) -
        x * ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹)
    (fun x ↦ x) := by
  have hbound : ∀ x : ℝ, 0 ≤ x →
      |(∑ n ∈ Icc 1 ⌊x⌋₊, log (n : ℝ)) - x * ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n / (n : ℝ)| ≤
        ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n := by
    intro x hx
    rw [← summatory, ← von_mangoldt_summatory hx le_rfl, mul_sum, summatory,
      ← Finset.sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simp only [mul_div_left_comm x, abs_sub_comm, ← mul_sub, abs_mul,
      ArithmeticFunction.vonMangoldt_nonneg, abs_of_nonneg, Int.self_sub_floor, Int.fract_nonneg]
    refine Finset.sum_le_sum fun n hn ↦ ?_
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (Int.fract_lt_one _).le
  refine Asymptotics.IsBigO.trans ?_ chebyshev_upper
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [one_mul, norm_eq_abs, chebyshev_second_eq_summatory,
    norm_of_nonneg (summatory_nonneg _ _ _ (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg))]
  exact hbound x hx

lemma is_O_von_mangoldt_div_self :
  Asymptotics.IsBigO atTop
    (fun x : ℝ ↦ ∑ n ∈ Icc 1 (⌊x⌋₊), Λ n * (n : ℝ)⁻¹ - log x)
    (fun _ ↦ (1 : ℝ)) := by
  suffices h :
      Asymptotics.IsBigO atTop
        (fun x : ℝ ↦ x * ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * (n : ℝ)⁻¹ - x * log x)
        (fun x ↦ x) by
    refine ((isBigO_refl (fun x : ℝ ↦ x⁻¹) atTop).mul h).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← mul_sub, inv_mul_cancel_left₀ hx.ne']
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [inv_mul_cancel₀ hx.ne']
  refine summatory_log_sub.symm.triangle ?_
  have h₁ := (summatory_log (lt_add_one 2)).isBigO
  refine ((h₁.trans isLittleO_log_id_atTop.isBigO).sub (isBigO_refl _ _)).congr_left ?_
  intro x
  dsimp [summatory]
  ring

lemma prime_summatory_one_eq_prime_summatory_two {M : Type*} [AddCommMonoid M] (a : ℕ → M) :
  prime_summatory a 1 = prime_summatory a 2 := by
  ext x
  rw [prime_summatory, prime_summatory]
  refine (Finset.sum_subset_zero_on_sdiff
    (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_left one_le_two))
    (fun y hy => ?_) (fun _ _ => rfl)).symm
  rcases Finset.mem_sdiff.mp hy with ⟨hy1, hy2⟩
  rcases Finset.mem_filter.mp hy1 with ⟨hyIcc, hyPrime⟩
  exact False.elim <| hy2 <|
    Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hyPrime.two_le, (Finset.mem_Icc.mp hyIcc).2⟩, hyPrime⟩

lemma log_reciprocal :
  Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ Real.log p / p) 1 x - log x)
    (fun _ ↦ (1 : ℝ)) := by
  exact is_O_von_mangoldt_div_self_sub_log_div_self.symm.triangle is_O_von_mangoldt_div_self

lemma prime_counting_le_self (x : ℕ) : π x ≤ x := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have :
      (Finset.range (x + 1)).filter Nat.Prime ⊆ Finset.Ioc 0 x := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact Finset.mem_Ioc.mpr ⟨hn.2.pos, Nat.lt_succ_iff.mp hn.1⟩
  exact (Finset.card_le_card this).trans (by simp)

lemma chebyshev_first_eq_prime_summatory :
  chebyshev_first = prime_summatory (fun n ↦ Real.log n) 1 := by
  ext x
  change Chebyshev.theta x = prime_summatory (fun n ↦ Real.log n) 1 x
  rw [Chebyshev.theta_eq_sum_Icc, prime_summatory]
  congr 1

@[simp] lemma prime_counting'_zero : π' 0 = 0 := by
  rfl

@[simp] lemma prime_counting'_one : π' 1 = 0 := by
  rfl

@[simp] lemma prime_counting'_two : π' 2 = 0 := by
  rfl

lemma prime_counting_eq_prime_summatory {x : ℕ} :
  π x = prime_summatory (fun _ ↦ 1) 1 x := by
  simp [prime_summatory, prime_counting_eq_card_primes]

lemma prime_counting_eq_prime_summatory' {x : ℝ} :
  (π ⌊x⌋₊ : ℝ) = prime_summatory (fun _ ↦ (1 : ℝ)) 1 x := by
  rw [prime_counting_eq_prime_summatory]
  simp [prime_summatory]

lemma chebyshev_first_sub_prime_counting_mul_log_eq {x : ℝ} :
  (π ⌊x⌋₊ : ℝ) * log x - chebyshev_first x = ∫ t in Icc 1 x, π ⌊t⌋₊ * t⁻¹ := by
  have hmul :
      (fun n : ℕ ↦ ite (Nat.Prime n) (Real.log n : ℝ) 0) =
        fun n : ℕ ↦ ite (Nat.Prime n) (1 : ℝ) 0 * Real.log n := by
    funext n
    rw [boole_mul]
  simp only [chebyshev_first_eq_prime_summatory, prime_summatory_eq_summatory,
    prime_counting_eq_prime_summatory']
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', hmul,
    partial_summation_cont' (fun n ↦ ite (Nat.Prime n) (1 : ℝ) 0) Real.log (fun y ↦ y⁻¹)
      one_ne_zero (fun y hy ↦ hasDerivAt_log <| by
        have hy' : (1 : ℝ) ≤ y := by simpa using hy
        intro hzero
        rw [hzero] at hy'
        norm_num at hy')
      (by
        refine ContinuousOn.inv₀ continuousOn_id ?_
        intro y hy hzero
        have hy' : (1 : ℝ) ≤ y := by simpa using hy
        rw [hzero] at hy'
        norm_num at hy') x, Nat.cast_one]

lemma is_O_chebyshev_first_sub_prime_counting_mul_log :
  Asymptotics.IsBigO atTop
    (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x - chebyshev_first x) id := by
  simp only [chebyshev_first_sub_prime_counting_mul_log_eq]
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx.le
  change ‖∫ t in Icc 1 x, (π ⌊t⌋₊ : ℝ) * t⁻¹‖ ≤ 1 * ‖x‖
  rw [one_mul, Real.norm_of_nonneg hx0]
  have b₁ : ∀ y : ℝ, 1 ≤ y → 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹ := by
    intro y hy
    exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 (by linarith))
  have b₃ :
      (fun a : ℝ ↦ (π ⌊a⌋₊ : ℝ) * a⁻¹) ≤ᵐ[volume.restrict (Icc 1 x)] fun _ : ℝ ↦ (1 : ℝ) := by
    change ∀ᵐ y ∂ volume.restrict (Icc 1 x), (π ⌊y⌋₊ : ℝ) * y⁻¹ ≤ 1
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ by
      rw [← div_eq_mul_inv]
      have hy0 : 0 < y := by linarith [hy.1]
      rw [div_le_one hy0]
      simpa using
        le_trans (Nat.cast_le.2 (prime_counting_le_self _))
          (Nat.floor_le (zero_le_one.trans hy.1))
  have hnonneg :
      0 ≤ ∫ t in Icc 1 x, (π ⌊t⌋₊ : ℝ) * t⁻¹ := by
    refine integral_nonneg_of_ae ?_
    change ∀ᵐ y ∂ volume.restrict (Icc 1 x), 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ b₁ y hy.1
  rw [norm_eq_abs, abs_of_nonneg hnonneg]
  refine (integral_mono_of_nonneg ?_ (by simp) b₃).trans ?_
  · change ∀ᵐ y ∂ volume.restrict (Icc 1 x), 0 ≤ (π ⌊y⌋₊ : ℝ) * y⁻¹
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy ↦ b₁ y hy.1
  · have hconst : ∫ _ in Icc 1 x, (1 : ℝ) = x - 1 := by
      simp [hx.le]
    rw [hconst]
    linarith

lemma is_O_prime_counting_div_log :
  Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ : ℝ)) (fun x ↦ x / log x) := by
  have h :
      Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ : ℝ) * Real.log x) id := by
    refine (is_O_chebyshev_first_sub_prime_counting_mul_log.add chebyshev_first_upper).congr_left ?_
    intro x
    ring
  refine (Asymptotics.IsBigO.mul h (isBigO_refl (fun x ↦ (Real.log x)⁻¹) atTop)).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [mul_assoc, mul_inv_cancel₀ (Real.log_pos hx).ne', mul_one]
  · filter_upwards with x
    simp [div_eq_mul_inv]

def prime_log_div_sum_error (x : ℝ) : ℝ := by
  exact prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 1 x - log x

lemma prime_summatory_log_mul_inv_eq :
  prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 2 = log + prime_log_div_sum_error := by
  ext x
  rw [Pi.add_apply, prime_log_div_sum_error, prime_summatory_one_eq_prime_summatory_two]
  ring

lemma is_O_prime_log_div_sum_error :
    Asymptotics.IsBigO atTop prime_log_div_sum_error (fun _ ↦ (1 : ℝ)) := by
  exact log_reciprocal

@[fun_prop] lemma measurable_prime_log_div_sum_error :
  Measurable prime_log_div_sum_error := by
  change Measurable fun x ↦ prime_summatory (fun p ↦ Real.log p * (p : ℝ)⁻¹) 1 x - log x
  simp only [prime_summatory_one_eq_prime_summatory_two, prime_summatory_eq_summatory]
  measurability

def prime_reciprocal_integral : ℝ := by
  exact ∫ x in Ioi 2, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹

lemma my_func_continuous_on : ContinuousOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ioi 1) := by
  refine (continuousOn_id.mul ((Real.continuousOn_log.mono ?_).pow 2)).inv₀ ?_
  · intro x hx hzero
    rw [hzero] at hx
    norm_num at hx
  · intro x hx
    have hx' : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero] at hx'
      norm_num at hx'
    exact mul_ne_zero hx0 (pow_ne_zero 2 (Real.log_pos hx').ne')

lemma integral_inv_self_mul_log_sq {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x ^ 2)⁻¹ = (log a)⁻¹ - (log b)⁻¹ := by
  have hderiv :
      ∀ y ∈ Set.uIcc a b, HasDerivAt (fun x ↦ - (log x)⁻¹) ((y * log y ^ 2)⁻¹) y := by
    intro y hy
    have hy1 : 1 < y := (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
    have hrewrite : (y * log y ^ 2)⁻¹ = -((-y⁻¹) / (log y)^2) := by
      rw [neg_div, neg_neg, div_eq_mul_inv, mul_inv]
    rw [hrewrite]
    exact ((Real.hasDerivAt_log (by linarith)).inv (Real.log_pos hy1).ne').neg
  have hcont : ContinuousOn (fun x ↦ (x * log x ^ 2)⁻¹) (Set.uIcc a b) := by
    exact my_func_continuous_on.mono fun y hy ↦ (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (ContinuousOn.intervalIntegrable hcont),
    neg_sub_neg]

lemma integral_Ioi_my_func_tendsto_aux {a : ℝ} (ha : 1 < a)
  {ι : Type*} {b : ι → ℝ} {l : Filter ι} (hb : Tendsto b l atTop) :
  Tendsto (fun i ↦ ∫ x in a..b i, (x * log x ^ 2)⁻¹) l (𝓝 (log a)⁻¹) := by
  suffices h :
      Tendsto (fun i ↦ ∫ x in a..b i, (x * log x ^ 2)⁻¹) l (𝓝 ((log a)⁻¹ - 0)) by
    simpa using h
  have hEq :
      ∀ᶠ i in l, ∫ x in a..b i, (x * log x ^ 2)⁻¹ = (log a)⁻¹ - (log (b i))⁻¹ := by
    filter_upwards [hb.eventually (eventually_ge_atTop a)] with i hi
    rw [integral_inv_self_mul_log_sq ha (ha.trans_le hi)]
  rw [tendsto_congr' hEq]
  exact (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hb)).const_sub _

lemma integrable_on_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ioi a) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto (log a)⁻¹ a (fun x ↦ ?_) tendsto_id ?_
  · by_cases hx : a ≤ x
    · refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
      exact my_func_continuous_on.mono fun y hy ↦ ha.trans_le hy.1
    · simp [Set.Ioc_eq_empty_of_le (le_of_not_ge hx)]
  · refine (integral_Ioi_my_func_tendsto_aux ha tendsto_id).congr' ?_
    filter_upwards [eventually_gt_atTop a] with x hx
    have hax : a ≤ x := le_of_lt hx
    refine intervalIntegral.integral_congr fun y hy ↦ ?_
    have hy' : y ∈ Set.Icc a x := by simpa [Set.uIcc_of_le hax] using hy
    rw [Real.norm_of_nonneg]
    exact inv_nonneg.2 (mul_nonneg (le_trans (by linarith) hy'.1) (sq_nonneg _))

lemma integral_my_func_Ioi {a : ℝ} (ha : 1 < a) :
  ∫ x in Ioi a, (x * log x ^ 2)⁻¹ = (log a)⁻¹ := by
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi a (integrable_on_my_func_Ioi ha) tendsto_id)
    (integral_Ioi_my_func_tendsto_aux ha tendsto_id)

lemma my_func2_continuous_on : ContinuousOn (fun x ↦ (x * log x)⁻¹) (Ioi 1) := by
  refine (continuousOn_id.mul (Real.continuousOn_log.mono ?_)).inv₀ ?_
  · intro x hx hzero
    rw [hzero] at hx
    norm_num at hx
  · intro x hx
    have hx' : 1 < x := by simpa using hx
    have hx0 : x ≠ 0 := by
      intro hzero
      rw [hzero] at hx'
      norm_num at hx'
    exact mul_ne_zero hx0 (Real.log_pos hx').ne'

lemma integral_inv_self_mul_log {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
  ∫ x in a..b, (x * log x)⁻¹ = log (log b) - log (log a) := by
  have hderiv :
      ∀ y ∈ Set.uIcc a b, HasDerivAt (fun x ↦ log (log x)) ((y * log y)⁻¹) y := by
    intro y hy
    have hy1 : 1 < y := (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
    rw [mul_inv, ← div_eq_mul_inv]
    exact (Real.hasDerivAt_log (by linarith)).log (Real.log_pos hy1).ne'
  have hcont : ContinuousOn (fun x ↦ (x * log x)⁻¹) (Set.uIcc a b) := by
    exact my_func2_continuous_on.mono fun y hy ↦ (lt_min_iff.mpr ⟨ha, hb⟩).trans_le hy.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (ContinuousOn.intervalIntegrable hcont)]

lemma integrable_on_prime_log_div_sum_error :
  IntegrableOn (fun x ↦ prime_log_div_sum_error x * (x * log x ^ 2)⁻¹) (Ici 2) := by
  obtain ⟨c, hcpos, hcO⟩ := is_O_prime_log_div_sum_error.exists_pos
  obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → ‖prime_log_div_sum_error y‖ ≤ c * ‖(1 : ℝ)‖⟩ :=
    (atTop_basis' 2).mem_iff.1 hcO.bound
  have hsplit : Ici (2 : ℝ) = Ico 2 k ∪ Ici k := by
    rw [Ico_union_Ici_eq_Ici hk₂]
  rw [hsplit]
  have hlog : ContinuousOn log (Icc 2 k) := by
    refine Real.continuousOn_log.mono ?_
    intro y hy hy0
    rw [hy0] at hy
    norm_num at hy
  have hlog' : ContinuousOn (fun i : ℝ ↦ (i * log i ^ 2)⁻¹) (Icc 2 k) := by
    refine (continuousOn_id.mul (hlog.pow 2)).inv₀ ?_
    intro y hy
    have hy2 : 2 ≤ y := hy.1
    have hy0 : 0 < y := by linarith
    exact mul_ne_zero hy0.ne' (pow_ne_zero _ (Real.log_pos (by linarith)).ne')
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_congr_set_ae Ico_ae_eq_Icc).2 ?_
    simp only [prime_log_div_sum_error, prime_summatory_one_eq_prime_summatory_two,
      prime_summatory_eq_summatory, sub_mul]
    refine (partial_summation_integrable _ (ContinuousOn.integrableOn_Icc hlog')).sub ?_
    exact (hlog.mul hlog').integrableOn_Icc
  · have hbound :
        ∀ᵐ x : ℝ ∂volume.restrict (Ici k),
          ‖prime_log_div_sum_error x * (x * log x ^ 2)⁻¹‖ ≤ ‖c * (x * log x ^ 2)⁻¹‖ := by
      rw [ae_restrict_iff' measurableSet_Ici]
      filter_upwards with x hx
      rw [norm_mul, norm_mul]
      refine (mul_le_mul_of_nonneg_right (hk _ hx) (norm_nonneg _)).trans ?_
      have hcnorm : c * |(1 : ℝ)| ≤ ‖c‖ := by
        simp [Real.norm_eq_abs, abs_of_pos hcpos]
      exact mul_le_mul_of_nonneg_right hcnorm (norm_nonneg _)
    refine Integrable.mono (g := fun x ↦ c * (x * log x ^ 2)⁻¹) ?_
      (Measurable.aestronglyMeasurable <| by measurability) hbound
    have hbase : IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ici k) := by
      refine (integrableOn_congr_set_ae Ioi_ae_eq_Ici).1 ?_
      exact integrable_on_my_func_Ioi (one_lt_two.trans_le hk₂)
    exact hbase.const_mul c

lemma prime_reciprocal_eq {x : ℝ} (hx : 2 ≤ x) :
  prime_summatory (fun p ↦ (p : ℝ)⁻¹) 2 x -
    (log (log x) + (1 - log (Real.log 2) + prime_reciprocal_integral))
    = prime_log_div_sum_error x / log x -
      ∫ t in Ici x, prime_log_div_sum_error t / (t * log t ^ 2) := by
  let a : ℕ → ℝ := fun n ↦ if n.Prime then Real.log n * (n : ℝ)⁻¹ else 0
  let f : ℝ → ℝ := fun x ↦ (log x)⁻¹
  let f' : ℝ → ℝ := fun x ↦ (-x⁻¹) / log x ^ 2
  have hdiff : ∀ i ∈ Ici (2 : ℝ), HasDerivAt f (f' i) i := by
    intro i hi
    rw [show f = fun x ↦ (Real.log x)⁻¹ by rfl, show f' i = (-i⁻¹) / log i ^ 2 by rfl]
    have hi2 : (2 : ℝ) ≤ i := hi
    have hi0 : i ≠ 0 := by linarith
    have hi1 : 1 < i := by linarith
    exact (Real.hasDerivAt_log hi0).inv (ne_of_gt (Real.log_pos hi1))
  have hne : ∀ y : ℝ, y ∈ Ici (2 : ℝ) → y ≠ 0 := by
    intro y hy hy0
    rw [hy0] at hy
    norm_num at hy
  have hcont : ContinuousOn f' (Ici (2 : ℝ)) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuousOn_inv₀.mono hne).neg
    · exact (Real.continuousOn_log.mono hne).pow _
    · intro y hy
      exact pow_ne_zero _ (Real.log_pos (one_lt_two.trans_le hy)).ne'
  have hps := partial_summation_cont' a f f' two_ne_zero hdiff hcont x
  rw [sub_eq_iff_eq_add]
  convert hps using 1
  · rw [prime_summatory_eq_summatory]
    refine Finset.sum_congr rfl ?_
    intro y hy
    by_cases hpy : y.Prime
    · have hy1 : (1 : ℝ) < y := by
        rw [Nat.one_lt_cast, ← Nat.succ_le_iff]
        exact (Finset.mem_Icc.mp hy).1
      simp [a, f, hpy]
      field_simp [(show (y : ℝ) ≠ 0 by positivity), (Real.log_pos hy1).ne']
    · simp [a, hpy]
  · rw [← prime_summatory_eq_summatory, prime_summatory_log_mul_inv_eq]
    rw [prime_reciprocal_integral]
    simp only [div_eq_mul_inv, Pi.add_apply, add_mul, f', f, neg_mul, mul_neg, integral_neg,
      sub_neg_eq_add, ← mul_inv]
    have h₁ :
        Integrable (fun a ↦ (a * Real.log a)⁻¹)
          (volume.restrict (Icc (((2 : ℕ) : ℝ)) x)) := by
      exact (my_func2_continuous_on.mono fun y hy ↦ one_lt_two.trans_le hy.1).integrableOn_Icc
    have hEq :
        ∫ a in Icc (((2 : ℕ) : ℝ)) x, Real.log a * (a * Real.log a ^ 2)⁻¹ +
            prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ =
          ∫ a in Icc (((2 : ℕ) : ℝ)) x, (a * Real.log a)⁻¹ +
            prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ := by
      refine setIntegral_congr_fun measurableSet_Icc ?_
      intro y hy
      dsimp
      rw [mul_inv, mul_inv, mul_left_comm, ← div_eq_mul_inv, sq, div_self_mul_self']
    have hErrIcc :
        ∫ a in Icc (((2 : ℕ) : ℝ)) x, prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ =
          ∫ a in Ioc (((2 : ℕ) : ℝ)) x, prime_log_div_sum_error a * (a * log a ^ 2)⁻¹ := by
      convert
        (integral_Icc_eq_integral_Ioc
          (f := fun a : ℝ ↦ prime_log_div_sum_error a * (a * log a ^ 2)⁻¹)
          (x := (((2 : ℕ) : ℝ))) (y := x) (μ := volume))
        using 1
    have hErrTail :
        ∫ t in Ici x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
          ∫ t in Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ := by
      convert
        (integral_Ici_eq_integral_Ioi
          (f := fun t : ℝ ↦ prime_log_div_sum_error t * (t * log t ^ 2)⁻¹)
          (x := x) (μ := volume))
        using 1
    have hInvIcc :
        ∫ t in Icc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ =
          ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ := by
      simpa using
        (integral_Icc_eq_integral_Ioc (f := fun t : ℝ ↦ (t * log t)⁻¹)
          (x := (((2 : ℕ) : ℝ))) (y := x) (μ := volume))
    have hInv :
        ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ = log (log x) - log (log 2) := by
      calc
        ∫ t in Ioc (((2 : ℕ) : ℝ)) x, (t * log t)⁻¹ = ∫ t in (2 : ℝ)..x, (t * log t)⁻¹ := by
          symm
          exact intervalIntegral.integral_of_le (f := fun t : ℝ ↦ (t * log t)⁻¹) hx
        _ = log (log x) - log (log 2) := by
          simpa using integral_inv_self_mul_log one_lt_two (one_lt_two.trans_le hx)
    have hUnion :
        ∫ t in Ioi (2 : ℝ), prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
          (∫ t in Ioc (2 : ℝ) x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹) +
            ∫ t in Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ := by
      simpa [Ioc_union_Ioi_eq_Ioi hx, add_assoc] using
        (setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
          (integrable_on_prime_log_div_sum_error.mono_set
            (Set.Ioc_subset_Ioi_self.trans Set.Ioi_subset_Ici_self))
          (integrable_on_prime_log_div_sum_error.mono_set <| by
            intro y hy
            exact hx.trans hy.le) :
          ∫ t in Set.Ioc (2 : ℝ) x ∪ Set.Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹ =
            (∫ t in Set.Ioc (2 : ℝ) x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹) +
              ∫ t in Set.Ioi x, prime_log_div_sum_error t * (t * log t ^ 2)⁻¹)
    rw [mul_inv_cancel₀ (Real.log_pos (one_lt_two.trans_le hx)).ne', hEq,
      integral_add h₁ (integrable_on_prime_log_div_sum_error.mono_set Icc_subset_Ici_self),
      hInvIcc, hInv, hErrIcc, hErrTail, hUnion]
    ring_nf

lemma prime_reciprocal_error :
  Asymptotics.IsBigO atTop (fun x ↦ prime_log_div_sum_error x / log x -
      ∫ t in Ici x, prime_log_div_sum_error t / (t * log t ^ 2)) (fun x ↦ (log x)⁻¹) := by
  simp only [div_eq_mul_inv]
  refine Asymptotics.IsBigO.sub ?_ ?_
  · refine (is_O_prime_log_div_sum_error.mul (isBigO_refl _ _)).trans ?_
    simpa using isBigO_refl (fun x : ℝ ↦ (log x)⁻¹) atTop
  · obtain ⟨c, hc⟩ := is_O_prime_log_div_sum_error.bound
    obtain ⟨k, hk₂, hk : ∀ y, k ≤ y → ‖prime_log_div_sum_error y‖ ≤ c * ‖(1 : ℝ)‖⟩ :=
      (atTop_basis' 2).mem_iff.1 hc
    have hbound :
        ∀ y, k ≤ y → ∀ᵐ x : ℝ ∂volume.restrict (Ici y),
          ‖prime_log_div_sum_error x * (x * log x ^ 2)⁻¹‖ ≤ c * (x * log x ^ 2)⁻¹ := by
      intro y hy
      rw [ae_restrict_iff' measurableSet_Ici]
      filter_upwards with x hx
      rw [norm_mul]
      refine (mul_le_mul_of_nonneg_right (hk _ (hy.trans hx)) (norm_nonneg _)).trans ?_
      rw [norm_eq_abs, abs_one, mul_one, norm_eq_abs, abs_inv, abs_mul, abs_sq, abs_of_nonneg]
      exact zero_le_two.trans (hk₂.trans (hy.trans hx))
    have hI :
        Asymptotics.IsBigO atTop
          (fun y ↦ ∫ x in Ici y, prime_log_div_sum_error x * (x * log x ^ 2)⁻¹)
          (fun y ↦ ∫ x in Ici y, c * (x * log x ^ 2)⁻¹) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop k] with y hy
      apply (norm_integral_le_integral_norm _).trans
      rw [norm_eq_abs, one_mul]
      refine le_trans ?_ (le_abs_self _)
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x ↦ norm_nonneg _)
        ?_ (hbound _ hy)
      have hbase : IntegrableOn (fun x ↦ (x * log x ^ 2)⁻¹) (Ici y) := by
        refine (integrableOn_congr_set_ae Ioi_ae_eq_Ici).1 ?_
        exact integrable_on_my_func_Ioi (one_lt_two.trans_le (hk₂.trans hy))
      exact hbase.const_mul c
    have hEq :
        (fun y ↦ ∫ x in Ici y, c * (x * log x ^ 2)⁻¹) =ᶠ[atTop] fun y ↦ c * (log y)⁻¹ := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
      rw [integral_Ici_eq_integral_Ioi, integral_const_mul, integral_my_func_Ioi hy]
    exact hI.trans_eventuallyEq hEq |>.trans (Asymptotics.isBigO_const_mul_self c _ _)

def meissel_mertens : ℝ := by
  exact 1 - log (Real.log 2) + prime_reciprocal_integral

lemma prime_reciprocal :
  Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x - (log (log x) + meissel_mertens))
    (fun x ↦ (log x)⁻¹) := by
  refine prime_reciprocal_error.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [prime_summatory_one_eq_prime_summatory_two, meissel_mertens, ← prime_reciprocal_eq hx]

lemma mul_add_one_inv (x : ℝ) (hx₀ : x ≠ 0) (hx₁ : x + 1 ≠ 0) :
  (x * (x + 1))⁻¹ = x⁻¹ - (x + 1)⁻¹ := by
  field_simp [hx₀, hx₁]
  ring

lemma sum_thing_has_sum (k : ℕ) :
    HasSum (fun n : ℕ ↦ ((n + k + 1) * (n + k + 2) : ℝ)⁻¹) ((k + 1 : ℝ)⁻¹) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => inv_nonneg.2 (by positivity))]
  have htel :
      ∀ i : ℕ,
        ((i + k + 1 : ℝ) * (i + k + 2))⁻¹ =
          (↑(i + (k + 1)) : ℝ)⁻¹ - (↑(i + 1 + (k + 1)) : ℝ)⁻¹ := by
    intro i
    simp only [Nat.cast_add_one, Nat.cast_add, add_right_comm (i : ℝ) 1, ← add_assoc]
    convert mul_add_one_inv (i + k + 1) ?_ ?_ using 2
    · norm_num [add_assoc]
    · exact_mod_cast Nat.succ_ne_zero (i + k)
    · exact_mod_cast Nat.succ_ne_zero (i + k + 1)
  simp only [htel, Finset.sum_range_sub', zero_add, Nat.cast_add_one]
  simpa using
    (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat (k + 1))).const_sub
      ((k + 1 : ℝ)⁻¹)

lemma sum_thing'_has_sum : HasSum (fun n : ℕ ↦ ((n - 1) * n : ℝ)⁻¹) 1 := by
  refine (hasSum_nat_add_iff' 2).1 ?_
  have hzero :
      (∑ i ∈ Finset.range 2, (((i : ℝ) - 1) * (i : ℝ))⁻¹) = 0 := by
    norm_num [Finset.sum_range_succ]
  rw [hzero]
  norm_num
  have hbase :
      HasSum (fun n : ℕ ↦ ((↑n + ↑0 + 1) * (↑n + ↑0 + 2) : ℝ)⁻¹) 1 := by
    simpa using sum_thing_has_sum 0
  refine HasSum.congr_fun hbase ?_
  intro n
  have hn2 : (↑n + 2 : ℝ) ≠ 0 := by positivity
  have hn1 : (↑n + 2 - 1 : ℝ) ≠ 0 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  field_simp [hn1, hn2, Nat.cast_add]
  ring

lemma sum_thing'''_has_sum {k : ℕ} (hk : 1 ≤ k) :
  HasSum (fun n : ℕ ↦ ((n + k) * (n + k + 1) : ℝ)⁻¹) ((k : ℝ)⁻¹) := by
  convert sum_thing_has_sum (k - 1) using 1
  · ext n
    rw [add_assoc, add_assoc, Nat.cast_sub hk, Nat.cast_one, sub_add_cancel, add_sub, sub_add]
    norm_num [add_assoc]
  · simp [hk]

lemma my_mul_thing' : ∀ {n : ℕ}, (0 : ℝ) ≤ (((n - 1) * n : ℝ)⁻¹) := by
  intro n
  exact inv_nonneg.2 my_mul_thing

lemma is_O_partial_of_bound {f : ℕ → ℝ} (hf : ∀ n, f n ≤ (((n - 1) * n : ℝ)⁻¹))
    (hf' : ∀ n, 0 ≤ f n) :
  ∃ c, Asymptotics.IsBigO atTop (fun x : ℝ ↦ ∑ i ∈ range (⌊x⌋₊ + 1), f i - c)
    (fun x ↦ x⁻¹) := by
  have hf'' : Summable f := (sum_thing'_has_sum.summable).of_nonneg_of_le hf' hf
  refine ⟨tsum f, (Asymptotics.IsBigO.of_bound 2 ?_).symm⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx' : 1 ≤ ⌊x⌋₊ := by
    rwa [Nat.le_floor_iff' one_ne_zero, Nat.cast_one]
  have hx'' : (1 : ℝ) ≤ ⌊x⌋₊ := by simpa
  rw [← Summable.sum_add_tsum_nat_add _ hf'', add_tsub_cancel_left, norm_inv,
    norm_of_nonneg (tsum_nonneg fun i ↦ hf' (i + _)), norm_of_nonneg (zero_le_one.trans hx)]
  transitivity (⌊x⌋₊ : ℝ)⁻¹
  · refine hasSum_le (fun n ↦ ?_) ((summable_nat_add_iff _).2 hf'').hasSum
      (sum_thing'''_has_sum hx')
    have hsub : (↑n : ℝ) + (↑⌊x⌋₊ + 1) - 1 = ↑n + ↑⌊x⌋₊ := by ring
    simpa [Nat.cast_add, Nat.cast_add_one, add_assoc, add_left_comm, add_comm, mul_comm,
      mul_left_comm, mul_assoc, hsub] using hf (n + (⌊x⌋₊ + 1))
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hfloorpos : 0 < (⌊x⌋₊ : ℝ) := zero_lt_one.trans_le hx''
  field_simp [hxpos.ne', hfloorpos.ne']
  nlinarith [Nat.lt_floor_add_one x]

lemma is_O_partial_of_bound' {f : ℕ → ℝ} (hf : ∀ n, f n ≤ (((n - 1) * n : ℝ)⁻¹))
    (hf' : ∀ n, 0 ≤ f n) :
  ∃ c, Asymptotics.IsBigO atTop (fun x : ℝ ↦ ∑ i ∈ Icc 1 ⌊x⌋₊, f i - c)
    (fun x ↦ x⁻¹) := by
  obtain ⟨c, hc⟩ := is_O_partial_of_bound hf hf'
  refine ⟨c, hc.congr_left ?_⟩
  intro x
  have hIco : Finset.Ico 0 (⌊x⌋₊ + 1) = Finset.Icc 0 ⌊x⌋₊ := by
    simpa using (Finset.Ico_succ_right_eq_Icc 0 ⌊x⌋₊)
  rw [Finset.range_eq_Ico, hIco, Finset.Icc_eq_insert_Icc_succ (Nat.zero_le _), Finset.sum_insert]
  · have h0 : f 0 = 0 := ((hf' 0).antisymm (by simpa using hf 0)).symm
    simp [h0]
  · simp

lemma intermediate_bound :
  ∃ c, Asymptotics.IsBigO atTop
    (fun x ↦ prime_summatory (fun p ↦ ((p - 1) * p : ℝ)⁻¹) 1 x - c)
    (fun x ↦ x⁻¹) := by
  simp only [prime_summatory, Finset.sum_filter]
  refine is_O_partial_of_bound' (fun n ↦ ?_) (fun n ↦ ?_)
  · split_ifs with h
    · rfl
    · exact my_mul_thing'
  · split_ifs with h
    · exact my_mul_thing'
    · simp

lemma prime_proper_powers {x : ℝ} {f : ℕ → ℝ} :
  (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, f q) - prime_summatory f 1 x =
    ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      ∑ k ∈ (Finset.Icc 2 ⌊log x / Real.log p⌋₊), f (p ^ k) := by
  rw [exact_sum_prime_powers, prime_summatory, sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  have hp0 : 0 < p := hp.1.1
  rw [Nat.le_floor_iff' hp0.ne'] at hp
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.2.one_lt
  have hx : 0 < x := hp0'.trans_le hp.1.2
  have hk : 1 ≤ ⌊log x / Real.log p⌋₊ := by
    rw [Nat.le_floor_iff' one_ne_zero, Nat.cast_one, Real.log_div_log, ← Real.logb_self_eq_one hp1]
    exact (Real.logb_le_logb hp1 hp0' hx).2 hp.1.2
  rw [Finset.Icc_eq_insert_Icc_succ hk, Finset.sum_insert, pow_one, add_comm]
  · rw [Finset.mem_Icc]
    norm_num

lemma is_O_reciprocal_difference_aux {x : ℝ} :
  |(∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) -
      prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x -
      prime_summatory (fun p ↦ (((p - 1) * p : ℝ)⁻¹)) 1 x| ≤
    ∑ _p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) := by
  rw [prime_proper_powers, prime_summatory, ← Finset.sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  have hp0 : 0 < p := hp.1.1
  rw [Nat.le_floor_iff' hp0.ne'] at hp
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1 : (1 : ℝ) < p := by simpa using hp.2.one_lt
  have hx : 0 < x := hp0'.trans_le hp.1.2
  let N : ℕ := ⌊log x / Real.log p⌋₊
  have hk : 1 ≤ N := by
    dsimp [N]
    rw [Nat.le_floor_iff' one_ne_zero, Nat.cast_one, Real.log_div_log, ← Real.logb_self_eq_one hp1]
    exact (Real.logb_le_logb hp1 hp0' hx).2 hp.1.2
  have hgeom :
      ∑ k ∈ Finset.Icc 2 N, (p ^ k : ℝ)⁻¹ =
        (((p : ℝ)⁻¹) ^ 2 - ((p : ℝ)⁻¹) ^ (N + 1)) / (1 - (p : ℝ)⁻¹) := by
    simpa only [← Finset.Ico_succ_right_eq_Icc, inv_pow, Nat.succ_eq_add_one,
      Nat.succ_eq_succ] using
      (geom_sum_Ico' (x := (p : ℝ)⁻¹)
        (by simpa using (inv_ne_one.mpr hp1.ne'))
        (Nat.succ_le_succ hk))
  have hdiff :
      |(∑ k ∈ Finset.Icc 2 N, (p ^ k : ℝ)⁻¹) - (((p - 1) * p : ℝ)⁻¹)| =
        ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) := by
    rw [hgeom]
    have hpne1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
    have hstep :
        (((p : ℝ)⁻¹) ^ 2 - ((p : ℝ)⁻¹) ^ (N + 1)) / (1 - (p : ℝ)⁻¹) -
            (((p - 1) * p : ℝ)⁻¹) =
          -(((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1)) := by
      field_simp [hp0'.ne', hpne1, pow_ne_zero N hp0'.ne', pow_ne_zero (N + 1) hp0'.ne']
      have haux : (p : ℝ) ^ 2 * (p : ℝ) ^ N * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ N = p := by
        rw [inv_pow]
        field_simp [hp0'.ne', pow_ne_zero N hp0'.ne']
      have hrewrite :
          (1 - (p : ℝ) ^ 2 * (1 / (p : ℝ)) ^ (N + 1) - 1) * (p : ℝ) ^ N =
            -((p : ℝ) ^ 2 * (p : ℝ) ^ N * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ N) := by
        ring_nf
      rw [hrewrite, haux]
    rw [hstep, abs_neg, abs_of_nonneg]
    exact div_nonneg (inv_nonneg.2 (pow_nonneg hp0'.le _)) (sub_nonneg.2 hp1.le)
  have hdiff' :
      |(∑ k ∈ Finset.Icc 2 ⌊log x / Real.log p⌋₊, (↑(p ^ k) : ℝ)⁻¹) -
          (((p - 1) * p : ℝ)⁻¹)| =
        ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) := by
    simpa [N, Nat.cast_pow] using hdiff
  rw [hdiff']
  have hratio :
      ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) ≤ 2 * ((p : ℝ) ^ (N + 1))⁻¹ := by
    have hpne1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
    have hstep :
        ((p : ℝ) ^ N)⁻¹ / ((p : ℝ) - 1) =
          ((p : ℝ) / ((p : ℝ) - 1)) * ((p : ℝ) ^ (N + 1))⁻¹ := by
      field_simp [hp0'.ne', hpne1, pow_ne_zero N hp0'.ne', pow_ne_zero (N + 1) hp0'.ne']
      ring_nf
    rw [hstep]
    have hp_ratio : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
      have hp_sub : 0 < (p : ℝ) - 1 := sub_pos_of_lt hp1
      rw [div_le_iff₀ hp_sub]
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
      nlinarith
    exact mul_le_mul_of_nonneg_right hp_ratio (inv_nonneg.2 (pow_nonneg hp0'.le _))
  have hxp : x < (p : ℝ) ^ (N + 1) := by
    have hlogb : Real.logb p x < (N + 1 : ℝ) := by
      dsimp [N]
      simpa [Real.log_div_log] using Nat.lt_floor_add_one (log x / Real.log p)
    have hxpow : x < (p : ℝ) ^ ((N + 1 : ℕ) : ℝ) := by
      convert (Real.logb_lt_iff_lt_rpow hp1 hx).1 hlogb using 1
      norm_num
    rwa [Real.rpow_natCast] at hxpow
  have hinv : ((p : ℝ) ^ (N + 1))⁻¹ ≤ x⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hx hxp.le)
  exact hratio.trans (mul_le_mul_of_nonneg_left hinv (by positivity))

lemma is_O_reciprocal_difference : ∃ c,
  Asymptotics.IsBigO atTop
    (fun x : ℝ ↦
      (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) -
        prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x - c)
    (fun x ↦ (log x)⁻¹) := by
  obtain ⟨c, hc⟩ := intermediate_bound
  refine ⟨c, ?_⟩
  have hc' : Asymptotics.IsBigO atTop
      (fun x ↦ prime_summatory (fun p ↦ ((p - 1) * p : ℝ)⁻¹) 1 x - c)
      (fun x ↦ (log x)⁻¹) := by
    refine hc.trans (isLittleO_log_id_atTop.isBigO.inv_rev ?_)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx i using ((Real.log_pos hx).ne' i).elim
  refine Asymptotics.IsBigO.triangle ?_ hc'
  have haux0 : Asymptotics.IsBigO atTop (fun x : ℝ ↦ (π ⌊x⌋₊ : ℝ) * x⁻¹)
      (fun x ↦ (log x)⁻¹) := by
    refine (is_O_prime_counting_div_log.mul (isBigO_refl _ _)).congr' Filter.EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hx.ne', one_mul]
  have haux : Asymptotics.IsBigO atTop (fun x ↦ (π ⌊x⌋₊ * (2 * x⁻¹) : ℝ))
      (fun x ↦ (log x)⁻¹) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (haux0.const_mul_left 2)
  have hbound :
      Asymptotics.IsBigO atTop
        (fun x : ℝ ↦
          (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) -
            prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 x -
            prime_summatory (fun p ↦ ((p - 1) * p : ℝ)⁻¹) 1 x)
        (fun x ↦ (π ⌊x⌋₊ * (2 * x⁻¹) : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [one_mul, norm_eq_abs, norm_eq_abs]
    have hcard :
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) =
          (π ⌊x⌋₊ : ℝ) * (2 * x⁻¹) := by
      have hcard' :
          ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) =
            (π ⌊x⌋₊) • (2 * x⁻¹) := by
        rw [Finset.sum_const, prime_counting_eq_card_primes]
      calc
        ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (2 * x⁻¹) =
            (π ⌊x⌋₊) • (2 * x⁻¹) := hcard'
        _ = (π ⌊x⌋₊ : ℝ) * (2 * x⁻¹) := by
          exact nsmul_eq_mul (π ⌊x⌋₊) (2 * x⁻¹)
    exact (is_O_reciprocal_difference_aux).trans (le_trans (le_of_eq hcard) (le_abs_self _))
  exact hbound.trans haux

lemma prime_power_reciprocal : ∃ b,
  Asymptotics.IsBigO atTop
    (fun x : ℝ ↦
      (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊).filter IsPrimePow, (q : ℝ)⁻¹) - (log (log x) + b))
    (fun x ↦ (log x)⁻¹) := by
  obtain ⟨c, hc⟩ := is_O_reciprocal_difference
  refine ⟨meissel_mertens + c, ?_⟩
  exact (hc.add prime_reciprocal).congr_left fun x ↦ by ring_nf

@[simp] lemma to_finset_filter
  {α : Type*} {l : List α} (p : α → Prop) [DecidableEq α] [DecidablePred p] :
  (l.filter p).toFinset = l.toFinset.filter p := by
  ext x
  simp

@[simp] lemma to_finset_range {n : ℕ} : (List.range n).toFinset = Finset.range n := by
  simpa using List.toFinset_range n

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/UnitFractions/AuxiliaryLemmas.lean` -/

section
namespace UnitFractions

open Filter Finset Real
open _root_.Finset
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators Nat.Prime Topology

noncomputable section

/-!
This file ports the statement surface of the old `src/aux_lemmas.lean`.

Several results from the Lean 3 file are now available directly in Mathlib 4, sometimes under
slightly different names. In particular, this file mainly re-exports or lightly repackages:

* `tendsto_mul_exp_add_div_pow_atTop`
* `tendsto_nat_ceil_atTop`
* `Nat.dvd_iff_prime_pow_dvd_dvd`
* `ArithmeticFunction.sigma_zero_apply`
* the harmonic-series asymptotics around `Real.eulerMascheroniConstant`

The remaining declarations below are included for API coverage.
-/

theorem tendsto_mul_add_div_pow_log_at_top (b c : ℝ) (n : ℕ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (b * x + c) / log x ^ n) atTop atTop :=
  ((tendsto_mul_exp_add_div_pow_atTop b c n hb).comp tendsto_log_atTop).congr' <| by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [Real.exp_log hx]

section

variable {M : Type*} [AddCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]

end

theorem sum_le_card_mul_real {A : Finset ℕ} {M : ℝ} {f : ℕ → ℝ}
    (h : ∀ n ∈ A, f n ≤ M) :
    A.sum f ≤ A.card * M := by
  simpa [nsmul_eq_mul] using (Finset.sum_le_card_nsmul A f M h)

theorem rec_sum_le_card_div {A : Finset ℕ} {M : ℝ} (hM : 0 < M) (h : ∀ n ∈ A, M ≤ (n : ℝ)) :
    (rec_sum A : ℝ) ≤ A.card / M := by
  have hsum : (rec_sum A : ℝ) = Finset.sum A (fun n => (1 : ℝ) / n) := by
    simp [rec_sum]
  calc
    (rec_sum A : ℝ) = Finset.sum A (fun n => (1 : ℝ) / n) := hsum
    _ ≤ A.card * (1 / M) := sum_le_card_mul_real fun n hn => by
      exact one_div_le_one_div_of_le hM (h n hn)
    _ = A.card / M := by simp [div_eq_mul_inv]

/-!
Compatibility declarations from the remainder of `src/aux_lemmas.lean`.

Theorems already available directly from Mathlib, such as `sum_pow`, `sum_pow'`, and
`sum_add_sum`, are not duplicated here.
-/

private theorem _root_.ArithmeticFunction.IsMultiplicative.prod {ι : Type*} (g : ι → ℕ) {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (s : Finset ι)
    (hs : (s : Set ι).Pairwise fun i j ↦ Nat.Coprime (g i) (g j)) :
    s.prod (fun i ↦ f (g i)) = f (s.prod g) := by
  simpa using (hf.map_prod g s hs).symm

@[simp] theorem card_distinct_factors_apply_is_prime_pow {q : ℕ} (hq : IsPrimePow q) : ω q = 1 := by
  exact ArithmeticFunction.cardDistinctFactors_eq_one_iff.mpr hq

end

end UnitFractions

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/UnitFractions/Fourier.lean` -/

section
namespace UnitFractions

open scoped BigOperators
open Real Finset
open _root_.Finset

noncomputable section
attribute [local instance] Classical.propDecidable

/-!
This file ports the declaration surface of `src/fourier.lean`.

Mathlib 4 already provides much of the analytic API used here, especially the complex
exponential/trigonometric identities around:

* `Complex.exp_int_mul_two_pi_mul_I`
* `Complex.exp_ofReal_mul_I_re`
* `Complex.norm_exp_ofReal_mul_I`
* `Complex.two_cos`
-/

/-- Lean 3 used a local notation `[A]` for `A.lcm id`; we use an explicit alias in Lean 4. -/
abbrev lcmA (A : Finset ℕ) : ℕ := A.lcm id

/-- Useful for def 4.2 and in other statements. -/
def valid_sum_range (t : ℕ) : Finset ℤ :=
  Finset.Ioc ((-(t : ℤ)) / 2) ((t : ℤ) / 2)

lemma lcm_ne_zero_of_zero_not_mem {A : Finset ℕ} (hA : 0 ∉ A) : A.lcm id ≠ 0 := by
  intro h
  rw [Finset.lcm_eq_zero_iff] at h
  rcases h with ⟨x, hx, hx0⟩
  subst hx0
  exact hA hx

/-- Def 4.2. -/
def j (A : Finset ℕ) : Finset ℤ :=
  (valid_sum_range (A.lcm id)).erase 0

def e (x : ℝ) : ℂ :=
  Complex.exp (x * (2 * Real.pi * Complex.I))

lemma e_int (z : ℤ) : e z = 1 := by
  simpa [e, mul_assoc, mul_left_comm, mul_comm] using Complex.exp_int_mul_two_pi_mul_I z

@[simp] lemma e_nat (n : ℕ) : e n = 1 := by
  simpa using e_int (n : ℤ)

@[simp] lemma e_zero : e 0 = 1 := by
  simpa using e_nat 0

/-- Centred at `x`, width `2 * y`. -/
def integer_range (x y : ℝ) : Finset ℤ := Finset.Icc ⌈x - y⌉ ⌊x + y⌋

def I (h : ℤ) (K : ℝ) (k : ℕ) : Finset ℤ := integer_range (h * k) (K / 2)

lemma factorization_lcm {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x.lcm y).factorization = x.factorization ⊔ y.factorization := by
  exact Nat.factorization_lcm hx hy

private lemma _root_.Finset.sup_eq_mem {α β : Type*} {s : Finset α} (f : α → β)
    [LinearOrder β] [OrderBot β] (hs : s.Nonempty) :
    ∃ x ∈ s, s.sup f = f x := by
  classical
  refine Finset.induction_on s ?_ ?_ hs
  · intro hs
    cases hs.ne_empty rfl
  · intro a s ha ih hs
    by_cases hs' : s.Nonempty
    · rcases ih hs' with ⟨x, hx, hsup⟩
      by_cases hax : f a ≤ f x
      · refine ⟨x, Finset.mem_insert_of_mem hx, ?_⟩
        rw [Finset.sup_insert, hsup, sup_eq_right.2 hax]
      · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
        rw [Finset.sup_insert, hsup, sup_eq_left.2 (le_of_not_ge hax)]
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      rw [hs0]
      refine ⟨a, by simp, ?_⟩
      simp

/-- Lemma 4.9. -/
lemma cos_bound {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    |cos (π * x)| ≤ exp (-(2 * x ^ 2)) := by
  have hcos_nonneg : 0 ≤ cos (π * x) := by
    refine Real.cos_nonneg_of_mem_Icc ?_
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [hx', Real.pi_pos]
  rw [abs_of_nonneg hcos_nonneg]
  have hπx : |π * x| ≤ π := by
    rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le hx)]
    nlinarith [hx', Real.pi_pos]
  have hcos :
      cos (π * x) ≤ 1 - 2 * x ^ 2 := by
    calc
      cos (π * x) ≤ 1 - 2 / π ^ 2 * (π * x) ^ 2 := Real.cos_le_one_sub_mul_cos_sq hπx
      _ = 1 - 2 * x ^ 2 := by
        field_simp [pow_two, Real.pi_ne_zero]
  have hexp : 1 - 2 * x ^ 2 ≤ exp (-(2 * x ^ 2)) := by
    simpa using Real.one_sub_le_exp_neg (2 * x ^ 2)
  exact hcos.trans hexp

lemma cos_bound_abs {x : ℝ} (hx' : |x| ≤ 1 / 2) :
    |cos (π * x)| ≤ exp (-(2 * x ^ 2)) := by
  rcases le_or_gt 0 x with hx | hx
  · exact cos_bound hx (by simpa [abs_of_nonneg hx] using hx')
  · have hxneg : 0 ≤ -x := by linarith
    have hxneg' : -x ≤ 1 / 2 := by
      have hxabs : |-x| ≤ 1 / 2 := by simpa [abs_neg] using hx'
      simpa [abs_of_nonneg hxneg] using hxabs
    have h := cos_bound hxneg hxneg'
    simpa [neg_mul, Real.cos_neg, pow_two] using h

lemma sum_powerset_prod {ι : Type*} (I : Finset ι) (x : ι → ℂ) :
    I.powerset.sum (fun J => J.prod x) = I.prod (fun i => 1 + x i) := by
  simpa using (Finset.prod_one_add (s := I) (f := x)).symm

lemma lcm_Q {A : Finset ℕ} (hA : 0 ∉ A) : lcmA (ppowers_in_set A) = lcmA A := by
  apply Nat.dvd_antisymm
  · refine Finset.lcm_dvd_iff.2 ?_
    intro i hi
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff i).1 (mem_ppowers_in_set.1 hi).1
    rw [mem_ppowers_in_set' hp hk.ne'] at hi
    obtain ⟨n, hn, rfl⟩ := hi
    exact (Nat.ordProj_dvd _ _).trans (Finset.dvd_lcm hn)
  · refine Finset.lcm_dvd_iff.2 ?_
    intro n hn
    have hn' : n ≠ 0 := ne_of_mem_of_not_mem hn hA
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    have hpow : p ^ n.factorization p ∣ lcmA (ppowers_in_set A) := by
      by_cases hnp : n.factorization p = 0
      · simp [hnp]
      · apply Finset.dvd_lcm
        rw [mem_ppowers_in_set' hp hnp]
        exact ⟨n, hn, rfl⟩
    by_cases hk : k = 0
    · simp [hk]
    · exact (pow_dvd_pow _ ((hp.pow_dvd_iff_le_factorization hn').1 hpk)).trans hpow

lemma count_multiples {m n : ℕ} (hm : 1 ≤ m) :
    ((Finset.Icc 1 n).filter fun k => m ∣ k).card = n / m := by
  have hcard : (Finset.Icc 1 (n / m)).card = n / m := by
    simp [Nat.card_Icc]
  rw [← hcard]
  refine (Finset.card_bij (fun i _ => i * m) ?_ ?_ ?_).symm
  · intro i hi
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ?_, dvd_mul_left _ _⟩
    constructor
    · exact one_le_mul (Finset.mem_Icc.1 hi).1 hm
    · exact (Nat.le_div_iff_mul_le (lt_of_lt_of_le Nat.zero_lt_one hm)).1
        (Finset.mem_Icc.1 hi).2
  · intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_right (lt_of_lt_of_le Nat.zero_lt_one hm)
      (by simpa [Nat.mul_comm] using hij)
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxIcc, hxdiv⟩
    rcases Finset.mem_Icc.mp hxIcc with ⟨hx1, hx2⟩
    rcases hxdiv with ⟨z, rfl⟩
    refine ⟨z, Finset.mem_Icc.2 ?_, by simp [Nat.mul_comm]⟩
    constructor
    · exact Nat.succ_le_of_lt <|
        Nat.pos_of_mul_pos_left (lt_of_lt_of_le Nat.zero_lt_one hx1)
    · exact (Nat.le_div_iff_mul_le (lt_of_lt_of_le Nat.zero_lt_one hm)).2
        (by simpa [Nat.mul_comm] using hx2)

end

end UnitFractions

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/PrimePowers.lean` -/

section
/-!
# Prime-power infrastructure for Erdős Problem 285

Martin's denominator-elimination argument measures an integer by its largest
*exact* prime-power part: if `p ^ e ∣ n` but `p ^ (e + 1) ∤ n`, the relevant
part is `p ^ e`.  Equivalently, it is a prime power `q ∣ n` for which
`q` is coprime to `n / q`.

This file packages that notion, the counting function `π⋆`, elementary linear
bounds for `π⋆`, reduced-rational denominator descent, and the exponential LCM
bound already available in the unit-fractions development.
-/

namespace PrimePowers

open Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- The exact prime-power parts of `n`.  For example, the parts of
`12 = 2^2 * 3` are `4` and `3`, rather than `2`, `4`, and `3`. -/
def primePowerParts (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun q ↦ IsPrimePow q ∧ Nat.Coprime q (n / q)

/-- Martin's `P*(n)`, with the harmless convention `P*(0) = P*(1) = 0`. -/
def largestPrimePowerPart (n : ℕ) : ℕ :=
  (primePowerParts n).sup id

/-- A natural-number formulation of smoothness in terms of exact prime-power
parts. -/
def PrimePowerSmooth (y n : ℕ) : Prop :=
  ∀ q ∈ primePowerParts n, q ≤ y

/-- The finite set of prime powers in `[2,y]`. -/
def primePowersUpTo (y : ℕ) : Finset ℕ :=
  (Icc 2 y).filter IsPrimePow

/-- Martin's prime-power counting function `π*(y)`. -/
def piStar (y : ℕ) : ℕ :=
  (primePowersUpTo y).card

/-- `lcm(1,2,...,y)`. -/
def initialLcm (y : ℕ) : ℕ :=
  (Icc 1 y).lcm id

lemma mem_primePowerParts {n q : ℕ} (hn : n ≠ 0) :
    q ∈ primePowerParts n ↔
      IsPrimePow q ∧ q ∣ n ∧ Nat.Coprime q (n / q) := by
  simp [primePowerParts, Nat.mem_divisors, hn, and_left_comm]

lemma primePowerParts_eq_ppowers_in_singleton (n : ℕ) :
    primePowerParts n = UnitFractions.ppowers_in_set {n} := by
  ext q
  by_cases hn : n = 0
  · subst n
    have hzero : UnitFractions.ppowers_in_set ({0} : Finset ℕ) = ∅ := by
      simpa using UnitFractions.ppowers_in_set_insert_zero (∅ : Finset ℕ)
    rw [hzero]
    simp [primePowerParts]
  · constructor
    · intro hq
      rcases (mem_primePowerParts hn).mp hq with ⟨hqpp, hqdiv, hqcop⟩
      rw [UnitFractions.mem_ppowers_in_set]
      refine ⟨hqpp, ⟨n, ?_⟩⟩
      exact (UnitFractions.mem_local_part n).mpr ⟨by simp, hqdiv, hqcop⟩
    · intro hq
      rcases UnitFractions.mem_ppowers_in_set.mp hq with ⟨hqpp, ⟨m, hm⟩⟩
      rcases (UnitFractions.mem_local_part m).mp hm with ⟨hm, hqdiv, hqcop⟩
      simp only [Finset.mem_singleton] at hm
      subst m
      exact (mem_primePowerParts hn).mpr ⟨hqpp, hqdiv, hqcop⟩

lemma primePowerParts_nonempty {n : ℕ} (hn : 2 ≤ n) :
    (primePowerParts n).Nonempty := by
  rw [primePowerParts_eq_ppowers_in_singleton]
  exact UnitFractions.ppowers_in_set_nonempty ⟨n, by simp, hn⟩

lemma primePowerParts_empty_iff {n : ℕ} :
    primePowerParts n = ∅ ↔ n < 2 := by
  constructor
  · intro h
    by_contra hn
    exact (primePowerParts_nonempty (Nat.le_of_not_gt hn)).ne_empty h
  · intro hn
    interval_cases n <;> simp [primePowerParts, not_isPrimePow_one]

lemma le_largestPrimePowerPart {n q : ℕ} (hq : q ∈ primePowerParts n) :
    q ≤ largestPrimePowerPart n := by
  exact Finset.le_sup (f := id) hq

lemma largestPrimePowerPart_le_iff {n y : ℕ} :
    largestPrimePowerPart n ≤ y ↔ PrimePowerSmooth y n := by
  simp [largestPrimePowerPart, PrimePowerSmooth, Finset.sup_le_iff]

lemma largestPrimePowerPart_mem {n : ℕ} (hn : 2 ≤ n) :
    largestPrimePowerPart n ∈ primePowerParts n := by
  have hs : (primePowerParts n).sup id ∈ id '' (primePowerParts n : Set ℕ) :=
    Finset.sup_mem_of_nonempty (f := id) (primePowerParts_nonempty hn)
  rcases hs with ⟨q, hq, hqeq⟩
  simpa [largestPrimePowerPart] using hqeq ▸ hq

lemma largestPrimePowerPart_spec {n : ℕ} (hn : 2 ≤ n) :
    IsPrimePow (largestPrimePowerPart n) ∧
      largestPrimePowerPart n ∣ n ∧
      Nat.Coprime (largestPrimePowerPart n) (n / largestPrimePowerPart n) := by
  exact (mem_primePowerParts (by omega)).mp (largestPrimePowerPart_mem hn)

lemma largestPrimePowerPart_le {n : ℕ} : largestPrimePowerPart n ≤ n := by
  rw [largestPrimePowerPart_le_iff]
  intro q hq
  by_cases hn : n = 0
  · subst n
    simp [primePowerParts] at hq
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ((mem_primePowerParts hn).mp hq).2.1

@[simp] lemma mem_primePowersUpTo {y q : ℕ} :
    q ∈ primePowersUpTo y ↔ IsPrimePow q ∧ q ≤ y := by
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hqIcc, hqpp⟩
    exact ⟨hqpp, (Finset.mem_Icc.mp hqIcc).2⟩
  · rintro ⟨hqpp, hqy⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hqpp.one_lt, hqy⟩, hqpp⟩

lemma primePowersUpTo_mono : Monotone primePowersUpTo := by
  intro x y hxy q hq
  rw [mem_primePowersUpTo] at hq ⊢
  exact ⟨hq.1, hq.2.trans hxy⟩

lemma piStar_mono : Monotone piStar := by
  intro x y hxy
  exact Finset.card_le_card (primePowersUpTo_mono hxy)

lemma piStar_le (y : ℕ) : piStar y ≤ y := by
  calc
    piStar y ≤ (Icc 2 y).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ y := by simp

lemma den_pos (r : ℚ) : 0 < r.den := r.den_pos

lemma den_eq_one_iff_primePowerParts_empty (r : ℚ) :
    r.den = 1 ↔ primePowerParts r.den = ∅ := by
  rw [primePowerParts_empty_iff]
  have := r.den_pos
  omega

/-- If no exact prime-power part remains, the reduced rational is an integer. -/
lemma isInt_of_primePowerParts_empty {r : ℚ}
    (h : primePowerParts r.den = ∅) : ∃ z : ℤ, r = z := by
  have hden : r.den = 1 := (den_eq_one_iff_primePowerParts_empty r).2 h
  exact ⟨r.num, (Rat.den_eq_one_iff r).mp hden |>.symm⟩

/-- The reduced denominator of a finite unit-fraction sum divides the LCM of
its displayed denominators. -/
lemma recSum_den_dvd_lcm (A : Finset ℕ) :
    (UnitFractions.rec_sum A).den ∣ A.lcm id := by
  refine (Rat.den_sum_dvd_lcm_den A (fun n ↦ (1 : ℚ) / n)).trans ?_
  apply Finset.lcm_dvd
  intro n hn
  have hden : ((1 : ℚ) / n).den ∣ n := by
    have hdenZ : ((Rat.divInt 1 (n : ℤ)).den : ℤ) ∣ (n : ℤ) :=
      Rat.den_dvd 1 (n : ℤ)
    have heq : Rat.divInt 1 (n : ℤ) = (1 : ℚ) / n := by
      rw [Rat.divInt_eq_div]
      norm_num
    rw [heq] at hdenZ
    exact_mod_cast hdenZ
  exact hden.trans (Finset.dvd_lcm hn)

end

end PrimePowers

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Modular.lean` -/

section
/-!
# The modular subset-sum core of Martin's construction

This file isolates the finite cyclic-group argument used when eliminating a
prime-power factor from the denominator of a residual rational number.  The
objects being added are the inverses of the auxiliary denominators modulo the
prime power.

The first result below is the Cauchy--Davenport--Chowla branch of Martin's
subset-sum lemma: at least `n - 1` invertible residues modulo `n`, with the
choices indexed separately even when residues repeat, represent every residue
as a subset sum.  Keeping the indices separate is essential in the application
to distinct Egyptian-fraction denominators.
-/

namespace Modular

open scoped BigOperators
open Finset

noncomputable section

/-- The least-absolute-value representative of `h / m (mod n)`. -/
def centeredInverse (n h m : ℕ) : ℤ :=
  ((h : ZMod n) * (m : ZMod n)⁻¹).valMinAbs

/-- Multiplicity of a residue among all indexed inverse subset sums, embedded
in `ℂ` for Fourier inversion. -/
def inverseSubsetMass (n : ℕ) (M : Finset ℕ) (a : ZMod n) : ℂ :=
  ∑ K ∈ M.powerset,
    if K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a then 1 else 0

theorem inverseSubsetMass_eq_card (n : ℕ) (M : Finset ℕ) (a : ZMod n) :
    inverseSubsetMass n M a =
      ((M.powerset.filter fun K ↦
        K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a).card : ℂ) := by
  rw [inverseSubsetMass, ← sum_filter]
  simp

theorem inverseSubsetMass_ne_zero_iff (n : ℕ) (M : Finset ℕ) (a : ZMod n) :
    inverseSubsetMass n M a ≠ 0 ↔
      ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  rw [inverseSubsetMass_eq_card]
  simp

/-- The Fourier transform of the inverse-subset multiplicity is Martin's
product `∏ (1 + e_n(-h / m))`. -/
theorem dft_inverseSubsetMass {n : ℕ} [NeZero n] (M : Finset ℕ) (h : ZMod n) :
    ZMod.dft (inverseSubsetMass n M) h =
      M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, inverseSubsetMass]
  simp_rw [Finset.mul_sum]
  rw [sum_comm]
  simp only [mul_ite, mul_one, mul_zero]
  have hinner (K : Finset ℕ) :
      (∑ j : ZMod n, if K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = j then
        ZMod.stdAddChar (-(j * h)) else 0) =
          ZMod.stdAddChar (-(K.sum (fun m ↦ ((m : ZMod n)⁻¹)) * h)) := by
    let s := K.sum (fun m ↦ ((m : ZMod n)⁻¹))
    change (∑ j : ZMod n, if s = j then ZMod.stdAddChar (-(j * h)) else 0) = _
    have hfun :
        (fun j : ZMod n ↦ if s = j then ZMod.stdAddChar (-(j * h)) else 0) =
          fun j ↦ if j = s then ZMod.stdAddChar (-(j * h)) else 0 := by
      funext j
      by_cases heq : s = j
      · rw [if_pos heq, if_pos heq.symm]
      · rw [if_neg heq, if_neg (fun hjs ↦ heq hjs.symm)]
    rw [hfun]
    simp [s]
  have hchar (K : Finset ℕ) :
      ZMod.stdAddChar (-(K.sum (fun m ↦ ((m : ZMod n)⁻¹)) * h)) =
        K.prod fun m ↦ ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)) := by
    induction K using Finset.induction with
    | empty => simp
    | @insert m K hm ih =>
        rw [sum_insert hm, prod_insert hm, ← ih, ← AddChar.map_add_eq_mul]
        congr 1
        ring
  simp_rw [hinner, hchar]
  exact UnitFractions.sum_powerset_prod M _

/-- Fourier inversion formula for the exact subset count. -/
theorem inverseSubsetMass_fourier {n : ℕ} [NeZero n] (M : Finset ℕ) (a : ZMod n) :
    inverseSubsetMass n M a =
      (n : ℂ)⁻¹ * ∑ h : ZMod n,
        ZMod.stdAddChar (h * a) *
          (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))) := by
  have hinv := congr_fun (ZMod.dft.symm_apply_apply (inverseSubsetMass n M)) a
  rw [ZMod.invDFT_apply] at hinv
  simp only [smul_eq_mul, dft_inverseSubsetMass] at hinv
  exact hinv.symm

/-- Contribution of all nonzero frequencies in the inverse-subset Fourier
formula. -/
def inverseSubsetFourierError (n : ℕ) [NeZero n] (M : Finset ℕ) (a : ZMod n) : ℂ :=
  ∑ h ∈ (univ.erase 0 : Finset (ZMod n)),
    ZMod.stdAddChar (h * a) *
      (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))

/-- If the nonzero Fourier modes have total norm smaller than the zero mode,
then every prescribed residue has an inverse subset-sum representation. -/
theorem inverse_subset_sum_surjective_of_fourier_error {n : ℕ} [NeZero n]
    (M : Finset ℕ) (a : ZMod n)
    (herror : ‖inverseSubsetFourierError n M a‖ < (2 : ℝ) ^ M.card) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  apply (inverseSubsetMass_ne_zero_iff n M a).mp
  rw [inverseSubsetMass_fourier]
  apply mul_ne_zero
  · exact inv_ne_zero (by exact_mod_cast NeZero.ne n)
  · have hsplit :
        (∑ h : ZMod n,
          ZMod.stdAddChar (h * a) *
            (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))) =
          (2 : ℂ) ^ M.card + inverseSubsetFourierError n M a := by
        change (∑ h : ZMod n,
          ZMod.stdAddChar (h * a) *
            (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))) =
          (2 : ℂ) ^ M.card +
            ∑ h ∈ (univ.erase 0 : Finset (ZMod n)),
              ZMod.stdAddChar (h * a) *
                (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))
        rw [← sum_erase_add _ _ (mem_univ (0 : ZMod n))]
        rw [add_comm]
        congr 1
        simp
        norm_num
    rw [hsplit]
    intro hzero
    have herr_eq : inverseSubsetFourierError n M a = -((2 : ℂ) ^ M.card) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_comm] using hzero
    have hnorm : ‖inverseSubsetFourierError n M a‖ = (2 : ℝ) ^ M.card := by
      rw [herr_eq, norm_neg, norm_pow]
      norm_num
    linarith

/-- Pointwise Fourier coefficient control implies the total-error hypothesis.
This is the exact analytic interface used after Martin's inverse-dispersion
estimate bounds each nonzero product. -/
theorem inverse_subset_sum_surjective_of_fourier_bound {n : ℕ} [NeZero n]
    (M : Finset ℕ) (a : ZMod n) (E : ℝ)
    (hcoeff : ∀ h : ZMod n, h ≠ 0 →
      ‖M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤ E)
    (hdom : ((n - 1 : ℕ) : ℝ) * E < (2 : ℝ) ^ M.card) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  apply inverse_subset_sum_surjective_of_fourier_error M a
  calc
    ‖inverseSubsetFourierError n M a‖
        ≤ ∑ h ∈ (univ.erase 0 : Finset (ZMod n)),
            ‖ZMod.stdAddChar (h * a) *
              (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))‖ :=
          by
            simpa only [inverseSubsetFourierError] using
              norm_sum_le (univ.erase 0 : Finset (ZMod n)) (fun h ↦
                ZMod.stdAddChar (h * a) *
                  (M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))))
    _ ≤ ∑ _h ∈ (univ.erase 0 : Finset (ZMod n)), E := by
          apply sum_le_sum
          intro h hh
          rw [norm_mul, AddChar.norm_apply, one_mul]
          exact hcoeff h (ne_of_mem_erase hh)
    _ = ((n - 1 : ℕ) : ℝ) * E := by
          rw [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ (0 : ZMod n)), card_univ,
            ZMod.card]
    _ < (2 : ℝ) ^ M.card := hdom

/-- Residues obtained by summing inverses of a subset of the indexed integers. -/
def inverseSubsetSums (n : ℕ) (M : Finset ℕ) : Finset (ZMod n) :=
  M.powerset.image fun K : Finset ℕ ↦ K.sum fun m ↦ ((m : ZMod n)⁻¹)

@[simp] theorem inverseSubsetSums_empty (n : ℕ) : inverseSubsetSums n ∅ = {0} := by
  simp [inverseSubsetSums]

theorem mem_inverseSubsetSums_iff {n : ℕ} {M : Finset ℕ} {a : ZMod n} :
    a ∈ inverseSubsetSums n M ↔
      ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  simp [inverseSubsetSums]

theorem inverseSubsetSums_insert {n m : ℕ} {M : Finset ℕ} (hm : m ∉ M) :
    inverseSubsetSums n (insert m M) =
      inverseSubsetSums n M ∪
        (inverseSubsetSums n M).image (fun x ↦ ((m : ZMod n)⁻¹) + x) := by
  ext a
  constructor
  · intro ha
    obtain ⟨K, hK, rfl⟩ := mem_inverseSubsetSums_iff.mp ha
    by_cases hmem : m ∈ K
    · rw [mem_union]
      right
      refine mem_image.mpr ⟨(K.erase m).sum (fun x ↦ ((x : ZMod n)⁻¹)), ?_, ?_⟩
      · apply mem_inverseSubsetSums_iff.mpr
        refine ⟨K.erase m, ?_, rfl⟩
        intro x hx
        have hxK : x ∈ K := mem_of_mem_erase hx
        have hxInsert := hK hxK
        rcases mem_insert.mp hxInsert with hxm | hxM
        · exact False.elim ((ne_of_mem_erase hx) hxm)
        · exact hxM
      · simpa [add_comm] using sum_erase_add K (fun x ↦ ((x : ZMod n)⁻¹)) hmem
    · rw [mem_union]
      left
      apply mem_inverseSubsetSums_iff.mpr
      refine ⟨K, ?_, rfl⟩
      intro x hx
      rcases mem_insert.mp (hK hx) with hxm | hxM
      · exact False.elim (hmem (hxm ▸ hx))
      · exact hxM
  · intro ha
    rw [mem_union] at ha
    rcases ha with ha | ha
    · obtain ⟨K, hK, rfl⟩ := mem_inverseSubsetSums_iff.mp ha
      apply mem_inverseSubsetSums_iff.mpr
      exact ⟨K, hK.trans (subset_insert m M), rfl⟩
    · obtain ⟨x, hx, hxa⟩ := mem_image.mp ha
      obtain ⟨K, hK, hxK⟩ := mem_inverseSubsetSums_iff.mp hx
      apply mem_inverseSubsetSums_iff.mpr
      refine ⟨insert m K, ?_, ?_⟩
      · exact insert_subset_insert m hK
      · rw [sum_insert]
        · rw [hxK, hxa]
        · exact fun h ↦ hm (hK h)

/-- An invertible residue additively generates the cyclic group `ZMod n`. -/
theorem nsmul_unit_hits {n : ℕ} [NeZero n] {u y : ZMod n} (hu : IsUnit u) :
    ∃ k : ℕ, k • u = y := by
  let k : ℕ := (y * u⁻¹).val
  refine ⟨k, ?_⟩
  simp only [nsmul_eq_mul]
  rw [show (k : ZMod n) = y * u⁻¹ by simp [k]]
  rw [mul_assoc, ZMod.inv_mul_of_unit u hu, mul_one]

/-- A nonempty proper subset cannot be stable under translation by a unit. -/
theorem unit_translate_not_subset {n : ℕ} [NeZero n] {u : ZMod n}
    (hu : IsUnit u) {A : Finset (ZMod n)} (hzero : 0 ∈ A) (hproper : A ≠ univ) :
    ¬ A.image (fun x ↦ u + x) ⊆ A := by
  intro hstable
  have hnsmul : ∀ k : ℕ, k • u ∈ A := by
    intro k
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
        apply hstable
        exact mem_image.mpr ⟨k • u, ih, by
          simp only [nsmul_eq_mul, Nat.cast_succ]
          ring⟩
  apply hproper
  apply eq_univ_of_forall
  intro y
  obtain ⟨k, hk⟩ := nsmul_unit_hits (y := y) hu
  rw [← hk]
  exact hnsmul k

theorem card_lt_card_union_unit_translate {n : ℕ} [NeZero n] {u : ZMod n}
    (hu : IsUnit u) {A : Finset (ZMod n)} (hzero : 0 ∈ A)
    (hcard : A.card < n) :
    A.card < (A ∪ A.image (fun x ↦ u + x)).card := by
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, ?_⟩
  intro heq
  have hproper : A ≠ univ := by
    intro hA
    have : A.card = n := by simp [hA]
    omega
  exact unit_translate_not_subset hu hzero hproper (by
    intro x hx
    have hx' : x ∈ A ∪ A.image (fun z ↦ u + z) := mem_union_right A hx
    rw [← heq] at hx'
    exact hx')

/-- Quantitative Chowla growth for the indexed inverse subset sums. -/
theorem min_card_succ_le_card_inverseSubsetSums (n : ℕ) [NeZero n]
    (M : Finset ℕ) (hcoprime : ∀ m ∈ M, Nat.Coprime m n) :
    min (M.card + 1) n ≤ (inverseSubsetSums n M).card := by
  induction M using Finset.induction with
  | empty => simp
  | @insert m M hm ih =>
      have hcoprimeM : ∀ x ∈ M, Nat.Coprime x n :=
        fun x hx ↦ hcoprime x (mem_insert_of_mem hx)
      have hcm := ih hcoprimeM
      rw [inverseSubsetSums_insert hm]
      have hunit0 : IsUnit (m : ZMod n) :=
        (ZMod.isUnit_iff_coprime m n).mpr (hcoprime m (mem_insert_self m M))
      have hunit : IsUnit ((m : ZMod n)⁻¹) :=
        isUnit_of_dvd_one ⟨(m : ZMod n), (ZMod.inv_mul_of_unit (m : ZMod n) hunit0).symm⟩
      have hzero : 0 ∈ inverseSubsetSums n M := by
        apply mem_inverseSubsetSums_iff.mpr
        exact ⟨∅, empty_subset _, by simp⟩
      by_cases hfull : n ≤ (inverseSubsetSums n M).card
      · have heq : (inverseSubsetSums n M).card = n := by
          apply le_antisymm
          · simpa [ZMod.card] using card_le_univ (inverseSubsetSums n M)
          · exact hfull
        have hset : inverseSubsetSums n M = univ := by
          apply eq_univ_of_card
          simpa [ZMod.card] using heq
        rw [hset, Finset.union_eq_left.mpr (subset_univ _), card_univ, ZMod.card]
        simp only [card_insert_of_notMem hm]
        omega
      · have hlt : (inverseSubsetSums n M).card < n := Nat.lt_of_not_ge hfull
        have hgrowth := card_lt_card_union_unit_translate hunit hzero hlt
        simp only [card_insert_of_notMem hm]
        omega

/-- If the indexed set has at least `n - 1` elements, every residue modulo
`n` is a sum of inverses of a subset.  Martin invokes the slightly weaker
hypothesis `n ≤ M.card` in this branch. -/
theorem inverse_subset_sum_surjective (n : ℕ) [NeZero n]
    (M : Finset ℕ) (hcoprime : ∀ m ∈ M, Nat.Coprime m n)
    (hcard : n ≤ M.card + 1) (a : ZMod n) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  have hle := min_card_succ_le_card_inverseSubsetSums n M hcoprime
  have hcount : n ≤ (inverseSubsetSums n M).card := by
    simpa [min_eq_right hcard] using hle
  have hall : inverseSubsetSums n M = univ := by
    apply eq_univ_of_card
    apply le_antisymm
    · simpa [ZMod.card] using card_le_univ (inverseSubsetSums n M)
    · rw [ZMod.card]
      exact hcount
  apply mem_inverseSubsetSums_iff.mp
  simp [hall]

/-- Martin's stated large-cardinality branch, with the paper's hypothesis
`n ≤ |M|` rather than the slightly sharper cutoff proved above. -/
theorem inverse_subset_sum_surjective_of_card (n : ℕ) [NeZero n]
    (M : Finset ℕ) (hcoprime : ∀ m ∈ M, Nat.Coprime m n)
    (hcard : n ≤ M.card) (a : ZMod n) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  apply inverse_subset_sum_surjective n M hcoprime (a := a)
  omega

end

end Modular

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Dispersion.lean` -/

section
/-!
# Martin's modular-inverse dispersion lemma

This file formalizes the modular inverse dispersion estimate used in Greg
Martin's proof of Erdős Problem 285.  The formulation follows Lemma 10 of the
published version of *Denser Egyptian fractions* (Lemma 11 in the arXiv
version).  The distance to the nearest integer is represented by the absolute
value of `ZMod.valMinAbs`.
-/

namespace Dispersion

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

/-- `m` is a product of exactly `k` distinct primes, none dividing `n`. -/
def IsKPrimeProductAway (k n m : ℕ) : Prop :=
  ∃ P : Finset ℕ, P.card = k ∧
    (∀ p ∈ P, p.Prime ∧ ¬ p ∣ n) ∧ m = P.prod id

/-- Martin's distance `‖h m̅/n‖`, where `m̅` denotes the inverse modulo `n`. -/
def centeredInverse (n h m : ℕ) : ℤ :=
  ((h : ZMod n) * (m : ZMod n)⁻¹).valMinAbs

/-- Martin's distance `‖h m̅/n‖`, where `m̅` denotes the inverse modulo `n`. -/
def inverseDistance (n h m : ℕ) : ℝ :=
  (centeredInverse n h m).natAbs / n

/-- The right-hand side in Martin's inverse-dispersion inequality. -/
def dispersionThreshold (n k : ℕ) (B C : ℝ) : ℝ :=
  C * Real.log (Real.log n) ^ k / (200 * B * Real.log n ^ k)

lemma factorial_card_le_prod_of_one_le (s : Finset ℕ)
    (hs : ∀ x ∈ s, 1 ≤ x) :
    Nat.factorial s.card ≤ ∏ x ∈ s, x := by
  let f : Fin s.card ↪o ℕ := s.orderEmbOfFin rfl
  have hidx : ∀ i : ℕ, ∀ hi : i < s.card, i + 1 ≤ f ⟨i, hi⟩ := by
    intro i hi
    induction i with
    | zero =>
        have hmem : f ⟨0, hi⟩ ∈ s := by simp [f]
        simpa [f] using hs (f ⟨0, hi⟩) hmem
    | succ i ih =>
        have hi' : i < s.card := Nat.lt_of_succ_lt hi
        have hprev : i + 1 ≤ f ⟨i, hi'⟩ := ih hi'
        have hlt : f ⟨i, hi'⟩ < f ⟨i + 1, hi⟩ :=
          f.strictMono (Nat.lt_succ_self i)
        exact le_trans (Nat.succ_le_succ hprev) (Nat.succ_le_of_lt hlt)
  have hprod : (∏ i : Fin s.card, (i.1 + 1)) ≤ ∏ i : Fin s.card, f i := by
    exact Finset.prod_le_prod' fun i _ ↦ hidx i.1 i.2
  have hleft : (∏ i : Fin s.card, (i.1 + 1)) = Nat.factorial s.card := by
    calc
      (∏ i : Fin s.card, (i.1 + 1)) = ∏ i ∈ Finset.range s.card, (i + 1) := by
        simpa using (Fin.prod_univ_eq_prod_range (fun i : ℕ ↦ i + 1) s.card)
      _ = Nat.factorial s.card := Finset.prod_range_add_one_eq_factorial s.card
  have hright : (∏ i : Fin s.card, f i) = ∏ x ∈ s, x := by
    calc
      (∏ i : Fin s.card, f i) =
          ∏ x ∈ Finset.map (s.orderEmbOfFin rfl).toEmbedding Finset.univ, x := by
        symm
        simpa [f] using
          (Finset.prod_map (s := Finset.univ)
            (e := (s.orderEmbOfFin rfl).toEmbedding) (f := fun x : ℕ ↦ x))
      _ = ∏ x ∈ s, x := by rw [Finset.map_orderEmbOfFin_univ (s := s) (h := rfl)]
  exact hleft ▸ hright ▸ hprod

lemma factorial_card_primeFactors_le (m : ℕ) (hm : m ≠ 0) :
    Nat.factorial m.primeFactors.card ≤ m := by
  refine (factorial_card_le_prod_of_one_le m.primeFactors ?_).trans ?_
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).one_le
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

/-- The elementary maximal-order estimate for the number of distinct prime
factors, in precisely the uniform form used by Martin. -/
lemma eventually_primeFactors_card_lt_four_log_div_loglog :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → m < n ^ 2 →
      (m.primeFactors.card : ℝ) <
        4 * Real.log n / Real.log (Real.log n) := by
  have hloglog : Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hloglog.eventually (eventually_gt_atTop (16 : ℝ))] with n hn
  intro m hm hm_lt
  let r := m.primeFactors.card
  have hn2 : 2 ≤ n := by
    by_contra h
    have hnle : n ≤ 1 := by omega
    interval_cases n <;> norm_num at hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn2
  have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hll_pos : 0 < Real.log (Real.log (n : ℝ)) := lt_trans (by norm_num) hn
  by_contra hbound
  have hr_lower : 4 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ≤ (r : ℝ) :=
    le_of_not_gt hbound
  have hr_pos : 0 < (r : ℝ) := lt_of_lt_of_le (by positivity) hr_lower
  have hlogll_le_half :
      Real.log (Real.log (Real.log (n : ℝ))) ≤
        Real.log (Real.log (n : ℝ)) / 2 := by
    let u := Real.log (Real.log (n : ℝ))
    have hu : 16 ≤ u := hn.le
    have hlogu : Real.log u ≤ u ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) :=
      Real.log_le_rpow_div (by positivity) (by norm_num)
    have hsqrt : u ^ ((1 : ℝ) / 2) = Real.sqrt u := by
      rw [Real.sqrt_eq_rpow]
    have hsqrt_le : Real.sqrt u ≤ u / 4 := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have hu0 : 0 ≤ u := le_trans (by norm_num) hu
        nlinarith [sq_sqrt hu0]
    dsimp [u] at hlogu hsqrt hsqrt_le ⊢
    rw [hsqrt] at hlogu
    nlinarith
  have hlogr_lower :
      Real.log (Real.log (n : ℝ)) / 2 + 1 < Real.log (r : ℝ) := by
    have hfour_pos : (0 : ℝ) < 4 := by norm_num
    have hquot_pos : 0 < Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) :=
      div_pos hlogn_pos hll_pos
    have hlog_mono :
        Real.log (4 * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))) ≤
          Real.log (r : ℝ) :=
      Real.log_le_log (mul_pos hfour_pos hquot_pos) (by
        simpa [mul_div_assoc] using hr_lower)
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hquot_pos),
      Real.log_div (ne_of_gt hlogn_pos) (ne_of_gt hll_pos)] at hlog_mono
    have hlogfour : (1 : ℝ) < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact (Real.exp_one_lt_d9).trans_le (by norm_num)
    linarith
  have hstirling :
      (r : ℝ) * Real.log r - r ≤ Real.log (Nat.factorial r : ℝ) := by
    have hr_nat : 0 < r := by exact_mod_cast hr_pos
    have h := Stirling.le_log_factorial_stirling hr_nat.ne'
    have hlogr_nonneg : 0 ≤ Real.log (r : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hr_nat)
    have hlogtwopi_nonneg : 0 ≤ Real.log (2 * Real.pi) :=
      Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    nlinarith
  have hfact_le : Nat.factorial r ≤ m := factorial_card_primeFactors_le m hm.ne'
  have hlogfact_lt : Real.log (Nat.factorial r : ℝ) < 2 * Real.log n := by
    have hcast_fact : (Nat.factorial r : ℝ) ≤ m := by exact_mod_cast hfact_le
    have hcast_m : (m : ℝ) < (n : ℝ) ^ 2 := by exact_mod_cast hm_lt
    have hposfact : (0 : ℝ) < Nat.factorial r := by positivity
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hnpowR : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    calc
      Real.log (Nat.factorial r : ℝ) ≤ Real.log (m : ℝ) :=
        Real.log_le_log hposfact hcast_fact
      _ < Real.log ((n : ℝ) ^ 2) := Real.strictMonoOn_log hmR hnpowR hcast_m
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
  have hmain : 2 * Real.log (n : ℝ) < (r : ℝ) * Real.log r - r := by
    have hdiff : Real.log (Real.log (n : ℝ)) / 2 < Real.log (r : ℝ) - 1 := by
      linarith
    have := mul_lt_mul_of_pos_left hdiff hr_pos
    have hcancel :
        (r : ℝ) * (Real.log (Real.log (n : ℝ)) / 2) ≥
          2 * Real.log (n : ℝ) := by
      have := mul_le_mul_of_nonneg_right hr_lower (le_of_lt (half_pos hll_pos))
      field_simp [hll_pos.ne'] at this ⊢
      nlinarith
    nlinarith
  linarith

lemma primeFactors_eq_of_isKPrimeProductAway {k n m : ℕ}
    (hm : IsKPrimeProductAway k n m) :
    ∃ P : Finset ℕ, P.card = k ∧ m.primeFactors = P ∧
      (∀ p ∈ P, p.Prime ∧ ¬ p ∣ n) := by
  obtain ⟨P, hPk, hP, rfl⟩ := hm
  refine ⟨P, hPk, Nat.primeFactors_prod (fun p hp ↦ (hP p hp).1), hP⟩

lemma isKPrimeProductAway_pos {k n m : ℕ} (hm : IsKPrimeProductAway k n m) :
    0 < m := by
  obtain ⟨P, -, hP, rfl⟩ := hm
  exact Finset.prod_pos fun p hp ↦ (hP p hp).1.pos

lemma isKPrimeProductAway_coprime {k n m : ℕ} (hm : IsKPrimeProductAway k n m) :
    Nat.Coprime m n := by
  obtain ⟨P, -, hP, rfl⟩ := hm
  rw [Nat.coprime_prod_left_iff]
  intro p hp
  exact (hP p hp).1.coprime_iff_not_dvd.mpr (hP p hp).2

lemma isKPrimeProductAway_primeFactors_card {k n m : ℕ}
    (hm : IsKPrimeProductAway k n m) : m.primeFactors.card = k := by
  obtain ⟨P, hPk, hprime, -⟩ := primeFactors_eq_of_isKPrimeProductAway hm
  rw [hprime, hPk]

/-- The integer `s_m = (m r_m - h)/n` in Martin's proof. -/
def quotientIndex (n h m : ℕ) : ℤ :=
  ((m : ℤ) * centeredInverse n h m - h) / n

lemma centeredInverse_mul_sub_dvd {n h m : ℕ} (hn : n ≠ 0)
    (hcop : Nat.Coprime m n) :
    (n : ℤ) ∣ (m : ℤ) * centeredInverse n h m - h := by
  let _ : NeZero n := ⟨hn⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, centeredInverse,
    ZMod.coe_valMinAbs]
  have hu : IsUnit (m : ZMod n) := (ZMod.isUnit_iff_coprime m n).mpr hcop
  calc
    (m : ZMod n) * ((h : ZMod n) * (m : ZMod n)⁻¹) - h =
        (h : ZMod n) * ((m : ZMod n) * (m : ZMod n)⁻¹) - h := by ring
    _ = 0 := by rw [ZMod.mul_inv_of_unit (m : ZMod n) hu, mul_one, sub_self]

lemma quotientIndex_spec {n h m : ℕ} (hn : n ≠ 0)
    (hcop : Nat.Coprime m n) :
    (n : ℤ) * quotientIndex n h m =
      (m : ℤ) * centeredInverse n h m - h := by
  rw [quotientIndex, mul_comm]
  exact Int.ediv_mul_cancel (centeredInverse_mul_sub_dvd hn hcop)

lemma centeredInverse_ne_zero {n h m : ℕ} (hn : n ≠ 0)
    (hhpos : 0 < h) (hhlt : h < n) (hcop : Nat.Coprime m n) :
    centeredInverse n h m ≠ 0 := by
  let _ : NeZero n := ⟨hn⟩
  simp only [centeredInverse, ne_eq, ZMod.valMinAbs_eq_zero]
  have hh : (h : ZMod n) ≠ 0 := by
    intro hzero
    have hdvd : n ∣ h := (ZMod.natCast_eq_zero_iff h n).mp hzero
    have := Nat.le_of_dvd hhpos hdvd
    omega
  have hu : IsUnit (m : ZMod n) := (ZMod.isUnit_iff_coprime m n).mpr hcop
  intro hz
  have hz' := congrArg (fun x : ZMod n ↦ x * (m : ZMod n)) hz
  rw [zero_mul, mul_assoc, ZMod.inv_mul_of_unit (m : ZMod n) hu, mul_one] at hz'
  exact hh hz'

lemma four_pow_lt_twenty_mul_factorial (k : ℕ) :
    4 ^ k < 20 * Nat.factorial k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      by_cases hk : k < 3
      · interval_cases k <;> norm_num [Nat.factorial]
      · have hk4 : 4 ≤ k + 1 := by omega
        rw [pow_succ, Nat.factorial_succ]
        calc
          4 ^ k * 4 < (20 * Nat.factorial k) * 4 :=
            Nat.mul_lt_mul_of_pos_right ih (by norm_num)
          _ ≤ 20 * ((k + 1) * Nat.factorial k) := by
            nlinarith [Nat.factorial_pos k]

lemma four_pow_div_factorial_lt_twenty (k : ℕ) :
    (4 : ℝ) ^ k / Nat.factorial k < 20 := by
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < Nat.factorial k)]
  exact_mod_cast four_pow_lt_twenty_mul_factorial k

/-- A fiber of Martin's integer `s_m` injects into the `k`-element subsets
of the prime divisors of `|nz+h|`. -/
lemma quotientIndex_fiber_card_le_choose
    {k n h : ℕ} (hn : n ≠ 0) (hhpos : 0 < h) (hhlt : h < n)
    (M : Finset ℕ) (hM : ∀ m ∈ M, IsKPrimeProductAway k n m) (z : ℤ) :
    ((M.filter fun m ↦ quotientIndex n h m = z).card : ℕ) ≤
      (n * z + h).natAbs.primeFactors.card.choose k := by
  let F := M.filter fun m ↦ quotientIndex n h m = z
  let q := (n * z + h).natAbs
  have hinj : Set.InjOn Nat.primeFactors F := by
    intro a ha b hb hab
    have haM : a ∈ M := (Finset.mem_filter.mp ha).1
    have hbM : b ∈ M := (Finset.mem_filter.mp hb).1
    obtain ⟨Pa, -, hPa, haeq⟩ := hM a haM
    obtain ⟨Pb, -, hPb, hbeq⟩ := hM b hbM
    have hpfa : a.primeFactors = Pa := by
      rw [haeq]
      exact Nat.primeFactors_prod fun p hp ↦ (hPa p hp).1
    have hpfb : b.primeFactors = Pb := by
      rw [hbeq]
      exact Nat.primeFactors_prod fun p hp ↦ (hPb p hp).1
    have hPP : Pa = Pb := hpfa.symm.trans (hab.trans hpfb)
    rw [haeq, hbeq, hPP]
  have hsub : F.image Nat.primeFactors ⊆ q.primeFactors.powersetCard k := by
    intro P hP
    obtain ⟨m, hmF, rfl⟩ := Finset.mem_image.mp hP
    have hmM : m ∈ M := (Finset.mem_filter.mp hmF).1
    have hmz : quotientIndex n h m = z := (Finset.mem_filter.mp hmF).2
    have hmprop := hM m hmM
    have hmpos := isKPrimeProductAway_pos hmprop
    have hmcop := isKPrimeProductAway_coprime hmprop
    have hrne := centeredInverse_ne_zero hn hhpos hhlt hmcop
    have hspec := quotientIndex_spec (n := n) (h := h) (m := m) hn hmcop
    rw [hmz] at hspec
    have heq : (n : ℤ) * z + h = (m : ℤ) * centeredInverse n h m := by
      linarith
    have hqeq : q = m * (centeredInverse n h m).natAbs := by
      dsimp [q]
      rw [heq, Int.natAbs_mul, Int.natAbs_natCast]
    have hqne : q ≠ 0 := by
      rw [hqeq]
      exact Nat.mul_ne_zero hmpos.ne' (Int.natAbs_ne_zero.mpr hrne)
    rw [Finset.mem_powersetCard]
    constructor
    · apply Nat.primeFactors_mono
      · rw [hqeq]
        exact dvd_mul_right m _
      · exact hqne
    · exact isKPrimeProductAway_primeFactors_card hmprop
  calc
    F.card = (F.image Nat.primeFactors).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (q.primeFactors.powersetCard k).card := Finset.card_le_card hsub
    _ = q.primeFactors.card.choose k := Finset.card_powersetCard k q.primeFactors

lemma choose_primeFactors_lt_twenty_ratio_pow
    {k n q : ℕ} (hk : 0 < k)
    (hlog : 0 < Real.log (n : ℝ))
    (hloglog : 0 < Real.log (Real.log (n : ℝ)))
    (homega : ∀ m : ℕ, 0 < m → m < n ^ 2 →
      (m.primeFactors.card : ℝ) <
        4 * Real.log n / Real.log (Real.log n))
    (hqpos : 0 < q) (hqlt : q < n ^ 2) :
    (q.primeFactors.card.choose k : ℝ) <
      20 * (Real.log n / Real.log (Real.log n)) ^ k := by
  let L := Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))
  have hL : 0 < L := div_pos hlog hloglog
  have hw := homega q hqpos hqlt
  have hpow : (q.primeFactors.card : ℝ) ^ k < (4 * L) ^ k := by
    apply pow_lt_pow_left₀
    · simpa [L, mul_div_assoc] using hw
    · positivity
    · exact hk.ne'
  calc
    (q.primeFactors.card.choose k : ℝ)
        ≤ (q.primeFactors.card : ℝ) ^ k / Nat.factorial k :=
      Nat.choose_le_pow_div k q.primeFactors.card
    _ < (4 * L) ^ k / Nat.factorial k :=
      div_lt_div_of_pos_right hpow (by positivity)
    _ = ((4 : ℝ) ^ k / Nat.factorial k) * L ^ k := by
      rw [mul_pow]
      ring
    _ < 20 * L ^ k :=
      mul_lt_mul_of_pos_right (four_pow_div_factorial_lt_twenty k) (pow_pos hL k)
    _ = 20 * (Real.log n / Real.log (Real.log n)) ^ k := rfl

/-- **Martin's modular-inverse dispersion lemma** (published Lemma 10).

For all sufficiently large moduli `n`, if `M` has more than `C` elements,
each below `B` and each a product of `k` distinct primes avoiding `n`, then
for every nonzero residue `h`, at least `C / 2` of their inverse residues are
farther from zero than Martin's stated threshold. -/
theorem martin_inverse_dispersion (k : ℕ) (hk : 0 < k) :
    ∀ᶠ n : ℕ in atTop, ∀ (B C : ℝ) (M : Finset ℕ),
      0 < B → 0 < C →
      200 * (Real.log n / Real.log (Real.log n)) ^ k < C →
      C < n → C < M.card →
      (∀ m ∈ M, (m : ℝ) < B ∧ IsKPrimeProductAway k n m) →
      ∀ h : ℕ, 0 < h → h < n →
        C / 2 ≤
          ((M.filter fun m ↦
            dispersionThreshold n k B C < inverseDistance n h m).card : ℝ) := by
  have hllTop : Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_primeFactors_card_lt_four_log_div_loglog,
    hllTop.eventually (eventually_gt_atTop (16 : ℝ))] with n homega hnll
  intro B C M hB hCpos hC hCn hCM hM h hhpos hhlt
  have hnpos : 0 < n := lt_trans hhpos hhlt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlog : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    have hn2 : 2 ≤ n := by omega
    exact_mod_cast hn2
  have hll : 0 < Real.log (Real.log (n : ℝ)) := lt_trans (by norm_num) hnll
  let L := Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))
  let X := C / (100 * L ^ k)
  let T := dispersionThreshold n k B C
  have hL : 0 < L := div_pos hlog hll
  have hLpow : 0 < L ^ k := pow_pos hL k
  have hC' : 200 * L ^ k < C := by simpa [L] using hC
  have hX : 2 < X := by
    change 2 < C / (100 * L ^ k)
    rw [lt_div_iff₀ (mul_pos (by norm_num) hLpow)]
    nlinarith
  have hlog_lt : Real.log (Real.log (n : ℝ)) < Real.log (n : ℝ) := by
    have hlog_ne_one : Real.log (n : ℝ) ≠ 1 := by
      intro heq
      rw [heq, Real.log_one] at hnll
      norm_num at hnll
    have := Real.log_lt_sub_one_of_pos hlog hlog_ne_one
    linarith
  have hLone : 1 < L := by
    change 1 < Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))
    rw [lt_div_iff₀ hll]
    simpa using hlog_lt
  have hden : 1 < 100 * L ^ k := by
    have hpowone : 1 ≤ L ^ k := one_le_pow₀ hLone.le
    nlinarith
  have hXltC : X < C := by
    simpa [X] using (div_lt_self hCpos hden)
  have hXltn : X < (n : ℝ) := hXltC.trans hCn
  have hTeq : T = X / (2 * B) := by
    dsimp [T, X, L, dispersionThreshold]
    rw [div_pow]
    field_simp [hB.ne', hlog.ne', hll.ne']
    norm_num
  let bad := M.filter fun m ↦ inverseDistance n h m ≤ T
  let good := M.filter fun m ↦ T < inverseDistance n h m
  by_contra hgoal
  have hgoodlt : (good.card : ℝ) < C / 2 := by
    have : ¬ C / 2 ≤ (good.card : ℝ) := by
      simpa [good, T] using hgoal
    exact lt_of_not_ge this
  have hpartition : bad.card + good.card = M.card := by
    have hp := Finset.card_filter_add_card_filter_not
      (s := M) (p := fun m ↦ inverseDistance n h m ≤ T)
    have hcomp :
        (M.filter fun m ↦ ¬ inverseDistance n h m ≤ T) = good := by
      ext m
      simp [good]
    simpa [bad, hcomp] using hp
  have hbadlarge : C / 2 < (bad.card : ℝ) := by
    have hpartR : (bad.card : ℝ) + good.card = M.card := by exact_mod_cast hpartition
    nlinarith
  have hbad_nonempty : bad.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he] at hbadlarge
    simp at hbadlarge
    linarith
  have hquotient_bound : ∀ m ∈ bad, |(quotientIndex n h m : ℝ)| < X := by
    intro m hmbad
    have hmM : m ∈ M := (Finset.mem_filter.mp hmbad).1
    have hmdist : inverseDistance n h m ≤ T := (Finset.mem_filter.mp hmbad).2
    have hmB := (hM m hmM).1
    have hmprop := (hM m hmM).2
    have hmpos := isKPrimeProductAway_pos hmprop
    have hmcop := isKPrimeProductAway_coprime hmprop
    have hrne := centeredInverse_ne_zero hnpos.ne' hhpos hhlt hmcop
    let R : ℝ := (centeredInverse n h m).natAbs
    have hRpos : 0 < R := by
      dsimp [R]
      exact_mod_cast Int.natAbs_pos.mpr hrne
    have hRle : R ≤ (n : ℝ) * T := by
      have := hmdist
      rw [inverseDistance, div_le_iff₀ hnR] at this
      simpa [R, mul_comm] using this
    have hmR : (m : ℝ) * R < (n : ℝ) * X / 2 := by
      calc
        (m : ℝ) * R < B * R := mul_lt_mul_of_pos_right hmB hRpos
        _ ≤ B * ((n : ℝ) * T) := mul_le_mul_of_nonneg_left hRle hB.le
        _ = (n : ℝ) * X / 2 := by rw [hTeq]; field_simp [hB.ne']
    have hspec := quotientIndex_spec (n := n) (h := h) (m := m) hnpos.ne' hmcop
    have hspecR :
        (n : ℝ) * (quotientIndex n h m : ℝ) =
          (m : ℝ) * (centeredInverse n h m : ℝ) - h := by
      exact_mod_cast hspec
    have habs : |(centeredInverse n h m : ℝ)| = R := by
      dsimp [R]
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hrupper : (centeredInverse n h m : ℝ) ≤ R := by
      rw [← habs]
      exact le_abs_self _
    have hrlower : -R ≤ (centeredInverse n h m : ℝ) := by
      rw [← habs]
      exact neg_abs_le _
    have hhR : (h : ℝ) < n := by exact_mod_cast hhlt
    have hsupper : (quotientIndex n h m : ℝ) < X := by
      have hmposR : (0 : ℝ) ≤ m := by positivity
      nlinarith
    have hslower : -X < (quotientIndex n h m : ℝ) := by
      have hmposR : (0 : ℝ) ≤ m := by positivity
      nlinarith
    rw [abs_lt]
    exact ⟨hslower, hsupper⟩
  let Zs := bad.image (quotientIndex n h)
  let A : ℤ := ⌊X⌋
  have hA0 : 0 ≤ A := by
    change 0 ≤ ⌊X⌋
    rw [Int.floor_nonneg]
    linarith
  have hZsubset : Zs ⊆ Finset.Icc (-A) A := by
    intro z hz
    obtain ⟨m, hmbad, rfl⟩ := Finset.mem_image.mp hz
    have hs := hquotient_bound m hmbad
    rw [abs_lt] at hs
    rw [Finset.mem_Icc]
    constructor
    · by_contra hnot
      have hzInt : (quotientIndex n h m : ℤ) ≤ -A - 1 := by omega
      have hfloorlt : X < (A : ℝ) + 1 := by simpa [A] using Int.lt_floor_add_one X
      have hzReal : (quotientIndex n h m : ℝ) ≤ (-A - 1 : ℤ) := by exact_mod_cast hzInt
      push_cast at hzReal
      linarith
    · by_contra hnot
      have hzInt : A + 1 ≤ (quotientIndex n h m : ℤ) := by omega
      have hfloorle : (A : ℝ) ≤ X := by simpa [A] using Int.floor_le X
      have hzReal : ((A + 1 : ℤ) : ℝ) ≤ quotientIndex n h m := by exact_mod_cast hzInt
      push_cast at hzReal
      have hfloorlt : X < (A : ℝ) + 1 := by simpa [A] using Int.lt_floor_add_one X
      linarith
  have hZcard : (Zs.card : ℝ) < (5 / 2 : ℝ) * X := by
    have hcardle := Finset.card_le_card hZsubset
    have hcardInt := Int.card_Icc_of_le (-A) A (by omega)
    have hcardReal : ((Finset.Icc (-A) A).card : ℝ) = 2 * (A : ℝ) + 1 := by
      have hcardInt' : ((Finset.Icc (-A) A).card : ℤ) = 2 * A + 1 := by
        linarith
      exact_mod_cast hcardInt'
    have hfloorle : (A : ℝ) ≤ X := by simpa [A] using Int.floor_le X
    have hZle : (Zs.card : ℝ) ≤ 2 * (A : ℝ) + 1 := by
      rw [← hcardReal]
      exact_mod_cast hcardle
    nlinarith
  have hZnonempty : Zs.Nonempty := hbad_nonempty.image _
  have hfiber : ∀ z ∈ Zs,
      (((bad.filter fun m ↦ quotientIndex n h m = z).card : ℕ) : ℝ) <
        20 * L ^ k := by
    intro z hz
    obtain ⟨m, hmbad, hmz⟩ := Finset.mem_image.mp hz
    have hmM : m ∈ M := (Finset.mem_filter.mp hmbad).1
    have hmprop := (hM m hmM).2
    have hmpos := isKPrimeProductAway_pos hmprop
    have hmcop := isKPrimeProductAway_coprime hmprop
    have hrne := centeredInverse_ne_zero hnpos.ne' hhpos hhlt hmcop
    let q := (n * z + h).natAbs
    have hspec := quotientIndex_spec (n := n) (h := h) (m := m) hnpos.ne' hmcop
    rw [hmz] at hspec
    have heq : (n : ℤ) * z + h = (m : ℤ) * centeredInverse n h m := by linarith
    have hqeq : q = m * (centeredInverse n h m).natAbs := by
      dsimp [q]
      rw [heq, Int.natAbs_mul, Int.natAbs_natCast]
    have hqpos : 0 < q := by
      rw [hqeq]
      exact Nat.mul_pos hmpos (Int.natAbs_pos.mpr hrne)
    have hq_lt : q < n ^ 2 := by
      have hqm : (q : ℝ) = (m : ℝ) * (centeredInverse n h m).natAbs := by
        exact_mod_cast hqeq
      have hmB := (hM m hmM).1
      have hmdist : inverseDistance n h m ≤ T := (Finset.mem_filter.mp hmbad).2
      have hRle : ((centeredInverse n h m).natAbs : ℝ) ≤ (n : ℝ) * T := by
        rw [inverseDistance, div_le_iff₀ hnR] at hmdist
        simpa [mul_comm] using hmdist
      have hRpos : (0 : ℝ) < (centeredInverse n h m).natAbs := by
        exact_mod_cast Int.natAbs_pos.mpr hrne
      have hqbound : (q : ℝ) < (n : ℝ) * X / 2 := by
        rw [hqm]
        calc
          (m : ℝ) * (centeredInverse n h m).natAbs <
              B * (centeredInverse n h m).natAbs :=
            mul_lt_mul_of_pos_right hmB hRpos
          _ ≤ B * ((n : ℝ) * T) := mul_le_mul_of_nonneg_left hRle hB.le
          _ = (n : ℝ) * X / 2 := by rw [hTeq]; field_simp [hB.ne']
      have hnpow : (n : ℝ) * X / 2 < (n : ℝ) ^ 2 := by
        nlinarith
      exact_mod_cast hqbound.trans hnpow
    have hbadM : ∀ a ∈ bad, IsKPrimeProductAway k n a := by
      intro a ha
      exact (hM a (Finset.mem_filter.mp ha).1).2
    have hcardchoose := quotientIndex_fiber_card_le_choose hnpos.ne' hhpos hhlt bad hbadM z
    have hchoose := choose_primeFactors_lt_twenty_ratio_pow hk hlog hll homega hqpos hq_lt
    have hcardchooseR :
        ((bad.filter fun m ↦ quotientIndex n h m = z).card : ℝ) ≤
          (q.primeFactors.card.choose k : ℝ) := by
      exact_mod_cast hcardchoose
    exact lt_of_le_of_lt hcardchooseR (by simpa [L, q] using hchoose)
  have hdecomp :
      (bad.card : ℝ) =
        ∑ z ∈ Zs, ((bad.filter fun m ↦ quotientIndex n h m = z).card : ℝ) := by
    have hnat := Finset.card_eq_sum_card_fiberwise
      (s := bad) (t := Zs) (f := quotientIndex n h) (by
        intro m hm
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m, Finset.mem_coe.mp hm, rfl⟩))
    exact_mod_cast hnat
  have hbadupp : (bad.card : ℝ) < (Zs.card : ℝ) * (20 * L ^ k) := by
    rw [hdecomp]
    calc
      ∑ z ∈ Zs, ((bad.filter fun m ↦ quotientIndex n h m = z).card : ℝ)
          < ∑ _z ∈ Zs, 20 * L ^ k := by
        exact Finset.sum_lt_sum_of_nonempty hZnonempty hfiber
      _ = (Zs.card : ℝ) * (20 * L ^ k) := by simp
  have hfinal : (bad.card : ℝ) < C / 2 := by
    calc
      (bad.card : ℝ) < (Zs.card : ℝ) * (20 * L ^ k) := hbadupp
      _ < ((5 / 2 : ℝ) * X) * (20 * L ^ k) :=
        mul_lt_mul_of_pos_right hZcard (mul_pos (by norm_num) hLpow)
      _ = C / 2 := by
        dsimp [X]
        field_simp [hLpow.ne']
        ring
  linarith

end

end Dispersion

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/FourierBound.lean` -/

section
/-!
# Exponential tail estimates for Martin's modular Fourier argument

The character-product estimate produces a bound of the shape
`2^C * exp (-X / 2)`.  This file records the exact elementary inequality
turning `2 * log n < X` into domination of all `n - 1` nonzero Fourier
frequencies by the zero frequency.
-/

namespace FourierBound

open scoped BigOperators
open Finset Real

noncomputable section

/-- Exponential loss stronger than `exp (-2 log n)` makes the sum of the
`n - 1` nonzero Fourier modes strictly smaller than the zero mode. -/
theorem exp_half_tail_dominates {n C : ℕ} {X : ℝ} (hn : 1 < n)
    (hX : 2 * Real.log n < X) :
    ((n - 1 : ℕ) : ℝ) *
        ((2 : ℝ) ^ C * Real.exp (-X / 2)) < (2 : ℝ) ^ C := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hpred : (((n - 1 : ℕ) : ℝ)) < n := by
    exact_mod_cast Nat.pred_lt (Nat.ne_zero_of_lt hn)
  have hlog : Real.log n < X / 2 := by linarith
  have hexp : (n : ℝ) * Real.exp (-X / 2) < 1 := by
    rw [← Real.exp_log hnpos, ← Real.exp_add, ← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    linarith
  have hpredexp : (((n - 1 : ℕ) : ℝ)) * Real.exp (-X / 2) < 1 := by
    exact (mul_lt_mul_of_pos_right hpred (Real.exp_pos _)).trans hexp
  calc
    (((n - 1 : ℕ) : ℝ)) * ((2 : ℝ) ^ C * Real.exp (-X / 2)) =
        (2 : ℝ) ^ C *
          ((((n - 1 : ℕ) : ℝ)) * Real.exp (-X / 2)) := by ring
    _ < (2 : ℝ) ^ C * 1 :=
      mul_lt_mul_of_pos_left hpredexp (pow_pos (by norm_num) C)
    _ = (2 : ℝ) ^ C := mul_one _

/-- A pointwise character-product decay estimate with exponent `X / 2`
implies inverse subset-sum surjectivity. -/
theorem inverse_subset_sum_surjective_of_exp_decay {n : ℕ} [NeZero n]
    (hn : 1 < n) (M : Finset ℕ) (a : ZMod n) (X : ℝ)
    (hcoeff : ∀ h : ZMod n, h ≠ 0 →
      ‖M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤
        (2 : ℝ) ^ M.card * Real.exp (-X / 2))
    (hX : 2 * Real.log n < X) :
    ∃ K ⊆ M, K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  apply Erdos285.Modular.inverse_subset_sum_surjective_of_fourier_bound
    M a ((2 : ℝ) ^ M.card * Real.exp (-X / 2)) hcoeff
  exact exp_half_tail_dominates hn hX

/-- Algebraic core of Martin's numerical estimate.  The left side is the
quantity obtained by clearing denominators from
`2L < C * (C * LL^k / (200 B L^k))^2`. -/
theorem martin_cubic_implies_threshold {C B L LL : ℝ} {k : ℕ}
    (hB : 0 < B) (hL : 0 < L)
    (hcubic :
      80000 * B ^ 2 * L ^ (2 * k + 1) < C ^ 3 * LL ^ (2 * k)) :
    2 * L < C * (C * LL ^ k / (200 * B * L ^ k)) ^ 2 := by
  have hden : 0 < (200 * B * L ^ k) ^ 2 := by positivity
  rw [div_pow]
  rw [show C * ((C * LL ^ k) ^ 2 / (200 * B * L ^ k) ^ 2) =
    (C * (C * LL ^ k) ^ 2) / (200 * B * L ^ k) ^ 2 by ring]
  rw [lt_div_iff₀ hden]
  calc
    2 * L * (200 * B * L ^ k) ^ 2 =
        80000 * B ^ 2 * L ^ (2 * k + 1) := by ring
    _ < C ^ 3 * LL ^ (2 * k) := hcubic
    _ = C * (C * LL ^ k) ^ 2 := by ring

/-- Martin's published cardinality lower bound, written as a cube root of
one positive expression, implies the exponent needed by the Fourier tail.
This cube-root form is algebraically equal to
`200 B^(2/3) L^((2k+1)/3) / LL^(2k/3) < C`. -/
theorem martin_cardinality_bound_implies_threshold {C B L LL : ℝ} {k : ℕ}
    (hB : 0 < B) (hL : 0 < L) (hLL : 0 < LL)
    (hC :
      200 * (B ^ 2 * L ^ (2 * k + 1) / LL ^ (2 * k)) ^ (1 / 3 : ℝ) < C) :
    2 * L < C * (C * LL ^ k / (200 * B * L ^ k)) ^ 2 := by
  let Q : ℝ := B ^ 2 * L ^ (2 * k + 1) / LL ^ (2 * k)
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  have hbase : 0 ≤ 200 * Q ^ (1 / 3 : ℝ) := by positivity
  have hcubed : (200 * Q ^ (1 / 3 : ℝ)) ^ 3 < C ^ 3 :=
    pow_lt_pow_left₀ hC hbase (by norm_num)
  have hroot : (Q ^ (1 / 3 : ℝ)) ^ 3 = Q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    norm_num
  have hcubed' : 8000000 * Q < C ^ 3 := by
    rw [mul_pow, hroot] at hcubed
    norm_num at hcubed ⊢
    exact hcubed
  have hLLpow : 0 < LL ^ (2 * k) := by positivity
  have hstrong :
      8000000 * B ^ 2 * L ^ (2 * k + 1) < C ^ 3 * LL ^ (2 * k) := by
    rw [show Q = B ^ 2 * L ^ (2 * k + 1) / LL ^ (2 * k) by rfl] at hcubed'
    rw [show 8000000 * (B ^ 2 * L ^ (2 * k + 1) / LL ^ (2 * k)) =
      (8000000 * B ^ 2 * L ^ (2 * k + 1)) / LL ^ (2 * k) by ring,
      div_lt_iff₀ hLLpow] at hcubed'
    exact hcubed'
  apply martin_cubic_implies_threshold hB hL
  have hleft : 0 < B ^ 2 * L ^ (2 * k + 1) := by positivity
  nlinarith

/-- The cube-root normalization used above is exactly Martin's displayed
product of fractional powers. -/
theorem martin_cube_root_eq_factor_form {B L LL : ℝ} {k : ℕ}
    (hB : 0 < B) (hL : 0 < L) (hLL : 0 < LL) :
    (B ^ 2 * L ^ (2 * k + 1) / LL ^ (2 * k)) ^ (1 / 3 : ℝ) =
      B ^ (2 / 3 : ℝ) * L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
        LL ^ (((2 * k : ℕ) : ℝ) / 3) := by
  rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast]
  rw [← Real.rpow_mul hB.le, ← Real.rpow_mul hL.le, ← Real.rpow_mul hLL.le]
  congr 2 <;> norm_num <;> ring_nf

/-- The published fractional-power cardinality condition directly yields
the exponent required for the Fourier tail. -/
theorem martin_published_cardinality_bound_implies_threshold
    {C B L LL : ℝ} {k : ℕ}
    (hB : 0 < B) (hL : 0 < L) (hLL : 0 < LL)
    (hC :
      200 * (B ^ (2 / 3 : ℝ) * L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
        LL ^ (((2 * k : ℕ) : ℝ) / 3)) < C) :
    2 * L < C * (C * LL ^ k / (200 * B * L ^ k)) ^ 2 := by
  apply martin_cardinality_bound_implies_threshold hB hL hLL
  rwa [martin_cube_root_eq_factor_form hB hL hLL]

end

end FourierBound

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/SubsetSum.lean` -/

section
/-!
# Martin's sparse modular subset-sum lemma

This file supplies the analytic bridge between Martin's centered-inverse
dispersion lemma and the exact finite-Fourier counting formula in
`Erdos285.Modular`.  If at least half of the indexed inverse residues stay a
scaled distance `δ` from zero at every nonzero frequency, then the associated
character product is at most

`2 ^ |M| * exp (-δ² |M|)`.

Martin's published lower bound on `|M|` makes this decay stronger than all
`n - 1` nonzero Fourier frequencies combined.  Consequently every residue
modulo `n` is a sum of inverses of a subset of `M`.
-/

namespace SubsetSum

open scoped BigOperators Real
open Finset
open Filter

noncomputable section

/-- Least absolute integer representative of the character argument used in
Martin's Fourier product. -/
def characterDistance (n : ℕ) (h : ZMod n) (m : ℕ) : ℕ :=
  (-((m : ZMod n)⁻¹ * h)).valMinAbs.natAbs

/-- The same identity, stated with the centered representative used by the
unconditional dispersion theorem. -/
theorem characterDistance_eq_dispersion_centeredInverse {n : ℕ} [NeZero n]
    (h : ZMod n) (m : ℕ) :
    characterDistance n h m =
      (Erdos285.Dispersion.centeredInverse n h.val m).natAbs := by
  rw [characterDistance, Erdos285.Dispersion.centeredInverse]
  rw [show ((h.val : ℕ) : ZMod n) = h by simp]
  rw [mul_comm]
  exact ZMod.natAbs_valMinAbs_neg _

/-- Half-angle identity for a point on the complex unit circle. -/
theorem norm_one_add_exp_two_pi (x : ℝ) :
    ‖1 + Complex.exp (2 * Real.pi * Complex.I * x)‖ =
      2 * |Real.cos (Real.pi * x)| := by
  have hid :
      (1 : ℂ) + Complex.exp (2 * Real.pi * Complex.I * x) =
        Complex.exp (Real.pi * x * Complex.I) *
          (Complex.exp (-(Real.pi * x) * Complex.I) +
            Complex.exp (Real.pi * x * Complex.I)) := by
    rw [mul_add, ← Complex.exp_add, ← Complex.exp_add]
    ring_nf
    simp [add_comm]
  rw [hid, norm_mul, Complex.norm_exp]
  have htwo :
      Complex.exp (-(Real.pi * x) * Complex.I) +
          Complex.exp (Real.pi * x * Complex.I) =
        2 * Complex.cos (Real.pi * x) := by
    rw [add_comm, ← Complex.two_cos]
  rw [htwo]
  norm_num [Complex.mul_re]
  have harg : (Real.pi : ℂ) * x = ((Real.pi * x : ℝ) : ℂ) := by norm_num
  have hcos : Complex.cos ((Real.pi : ℂ) * x) =
      (Real.cos (Real.pi * x) : ℂ) :=
    (congrArg Complex.cos harg).trans (Complex.ofReal_cos _).symm
  have hncos := congrArg (fun z : ℂ ↦ ‖z‖) hcos
  rw [Complex.norm_real, Real.norm_eq_abs] at hncos
  exact hncos

/-- A standard additive-character factor is exponentially smaller than two
in terms of its centered distance from zero. -/
theorem norm_one_add_stdAddChar_le (n : ℕ) [NeZero n] (z : ZMod n) :
    ‖1 + ZMod.stdAddChar z‖ ≤
      2 * Real.exp (-(2 * (((z.valMinAbs : ℝ) / n) ^ 2))) := by
  conv_lhs => rw [← z.coe_valMinAbs]
  rw [ZMod.stdAddChar_coe]
  have hid :
      (2 * Real.pi * Complex.I * (z.valMinAbs : ℂ) / (n : ℂ)) =
        2 * Real.pi * Complex.I * ((z.valMinAbs : ℝ) / n) := by
    push_cast
    ring
  rw [hid]
  calc
    ‖1 + Complex.exp (2 * Real.pi * Complex.I * ((z.valMinAbs : ℝ) / n))‖ =
        2 * |Real.cos (Real.pi * ((z.valMinAbs : ℝ) / n))| := by
      have hcast : ((((z.valMinAbs : ℝ) / (n : ℝ) : ℝ) : ℂ)) =
          (z.valMinAbs : ℂ) / (n : ℂ) := by
        push_cast
        norm_cast
      have hnorm := norm_one_add_exp_two_pi ((z.valMinAbs : ℝ) / n)
      rw [hcast] at hnorm
      exact hnorm
    _ ≤ 2 * Real.exp (-(2 * (((z.valMinAbs : ℝ) / n) ^ 2))) := by
      gcongr
      apply UnitFractions.cos_bound_abs
      have hle := z.natAbs_valMinAbs_le
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
      rw [show |(z.valMinAbs : ℝ)| = (z.valMinAbs.natAbs : ℝ) by simp]
      have hn : 0 < (n : ℝ) := by exact_mod_cast (NeZero.pos n)
      rw [div_le_iff₀ hn]
      calc
        (z.valMinAbs.natAbs : ℝ) ≤ (n / 2 : ℕ) := by exact_mod_cast hle
        _ ≤ (n : ℝ) / 2 := Nat.cast_div_le
        _ = 1 / 2 * (n : ℝ) := by ring

/-- Uniform trivial bound for a standard character factor. -/
theorem norm_one_add_stdAddChar_le_two {n : ℕ} [NeZero n] (z : ZMod n) :
    ‖1 + ZMod.stdAddChar z‖ ≤ 2 := by
  calc
    ‖1 + ZMod.stdAddChar z‖ ≤ ‖(1 : ℂ)‖ + ‖ZMod.stdAddChar z‖ := norm_add_le _ _
    _ = 2 := by rw [norm_one, AddChar.norm_apply]; norm_num

/-- Product estimate when a designated subset of factors has an additional
multiplicative saving `rho`. -/
theorem norm_prod_le_two_pow_mul {M G : Finset ℕ} (f : ℕ → ℂ) (rho : ℝ)
    (hG : G ⊆ M) (hrho : 0 ≤ rho)
    (hall : ∀ m ∈ M, ‖f m‖ ≤ 2)
    (hgood : ∀ m ∈ G, ‖f m‖ ≤ 2 * rho) :
    ‖M.prod f‖ ≤ (2 : ℝ) ^ M.card * rho ^ G.card := by
  have hsplit : G.prod f * (M \ G).prod f = M.prod f := by
    simpa [mul_comm] using (Finset.prod_sdiff (f := f) hG)
  rw [← hsplit, norm_mul]
  calc
    ‖G.prod f‖ * ‖(M \ G).prod f‖ ≤
        ((G.prod fun _ ↦ (2 : ℝ) * rho) * ((M \ G).prod fun _ ↦ (2 : ℝ))) := by
      gcongr
      · simpa only [norm_prod] using
          Finset.prod_le_prod (fun _ _ ↦ by positivity) hgood
      · simpa only [norm_prod] using
          Finset.prod_le_prod (fun _ _ ↦ by positivity)
            (fun m hm ↦ hall m (Finset.mem_sdiff.mp hm).1)
    _ = ((2 : ℝ) * rho) ^ G.card * (2 : ℝ) ^ (M \ G).card := by simp
    _ = (2 : ℝ) ^ M.card * rho ^ G.card := by
      rw [mul_pow]
      rw [show (2 : ℝ) ^ G.card * rho ^ G.card * 2 ^ (M \ G).card =
          (2 ^ G.card * 2 ^ (M \ G).card) * rho ^ G.card by ring]
      congr 1
      rw [← pow_add]
      congr 1
      have hcard := Finset.card_sdiff_add_card_eq_card hG
      omega

/-- Real-cardinality version of the product estimate.  This is the form
needed to apply `Dispersion.martin_inverse_dispersion`, whose parameter `C`
may be any real number strictly below `M.card`. -/
theorem characterProduct_le_of_real_scaled_dispersion {n : ℕ} [NeZero n]
    (M : Finset ℕ) (h : ZMod n) (delta C : ℝ) (hdelta : 0 ≤ delta)
    (hdisp : C ≤
      2 * ((M.filter fun m ↦
        delta ≤ (characterDistance n h m : ℝ) / n).card : ℝ)) :
    ‖M.prod fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤
      (2 : ℝ) ^ M.card * Real.exp (-(delta ^ 2 * C)) := by
  let G := M.filter fun m ↦ delta ≤ (characterDistance n h m : ℝ) / n
  have hG : G ⊆ M := filter_subset _ _
  have hall : ∀ m ∈ M,
      ‖1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤ 2 := by
    intro m _
    exact norm_one_add_stdAddChar_le_two _
  have hgood : ∀ m ∈ G,
      ‖1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h))‖ ≤
        2 * Real.exp (-(2 * delta ^ 2)) := by
    intro m hm
    have hmScale : delta ≤ (characterDistance n h m : ℝ) / n :=
      (mem_filter.mp hm).2
    let z : ZMod n := -((m : ZMod n)⁻¹ * h)
    have hbase := norm_one_add_stdAddChar_le n z
    have habs : |((z.valMinAbs : ℝ) / n)| =
        (characterDistance n h m : ℝ) / n := by
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
      rw [show |(z.valMinAbs : ℝ)| = (z.valMinAbs.natAbs : ℝ) by simp]
      rfl
    have hsq : delta ^ 2 ≤ ((z.valMinAbs : ℝ) / n) ^ 2 := by
      have hxabs : delta ≤ |((z.valMinAbs : ℝ) / n)| := by
        rw [habs]
        exact hmScale
      simpa only [sq_abs] using
        (sq_le_sq₀ hdelta (abs_nonneg ((z.valMinAbs : ℝ) / n))).2 hxabs
    exact hbase.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num))
  have hbase := norm_prod_le_two_pow_mul
    (M := M) (G := G)
    (fun m ↦ 1 + ZMod.stdAddChar (-((m : ZMod n)⁻¹ * h)))
    (Real.exp (-(2 * delta ^ 2))) hG (Real.exp_pos _).le hall hgood
  refine hbase.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hhalf : C ≤ 2 * (G.card : ℝ) := by
    simpa [G] using hdisp
  nlinarith [sq_nonneg delta]

/-- Sparse Fourier branch with a real lower bound `C` for twice the number
of dispersed factors. -/
theorem inverse_subset_sum_surjective_of_real_scaled_dispersion
    {n : ℕ} [NeZero n]
    (hn : 1 < n) (M : Finset ℕ) (delta C : ℝ) (hdelta : 0 ≤ delta)
    (hdisp : ∀ h : ZMod n, h ≠ 0 → C ≤
      2 * ((M.filter fun m ↦
        delta ≤ (characterDistance n h m : ℝ) / n).card : ℝ))
    (hdecay : 2 * Real.log n < delta ^ 2 * C) :
    ∀ a : ZMod n, ∃ K ⊆ M,
      K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  intro a
  apply Erdos285.FourierBound.inverse_subset_sum_surjective_of_exp_decay
    hn M a (2 * (delta ^ 2 * C))
  · intro h hh
    have hexp : -(2 * (delta ^ 2 * C)) / 2 = -(delta ^ 2 * C) := by ring
    rw [hexp]
    exact characterProduct_le_of_real_scaled_dispersion
      M h delta C hdelta (hdisp h hh)
  · have hpos : 0 < delta ^ 2 * C :=
      lt_trans (mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))) hdecay
    nlinarith

/-- The lower bound on `B` in Martin's subset-sum lemma makes its displayed
cardinality expression strictly larger than the cardinality threshold in
the preceding dispersion lemma. -/
theorem martin_source_factor_gt_dispersion_factor
    {B L LL : ℝ} {k : ℕ} (hk : 0 < k)
    (hL : 0 < L) (hLL : 0 < LL)
    (hBsource :
      L ^ (((k - 1 : ℕ) : ℝ) / 2) /
          LL ^ ((k : ℝ) / 2) < B) :
    (L / LL) ^ k <
      B ^ (2 / 3 : ℝ) * L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
        LL ^ (((2 * k : ℕ) : ℝ) / 3) := by
  let A := L ^ (((k - 1 : ℕ) : ℝ) / 2) / LL ^ ((k : ℝ) / 2)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hpow : A ^ (2 / 3 : ℝ) < B ^ (2 / 3 : ℝ) :=
    Real.rpow_lt_rpow hA.le hBsource (by norm_num)
  have hrest : 0 < L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
      LL ^ (((2 * k : ℕ) : ℝ) / 3) := by positivity
  have heq : (L / LL) ^ k = A ^ (2 / 3 : ℝ) *
      (L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
        LL ^ (((2 * k : ℕ) : ℝ) / 3)) := by
    dsimp [A]
    rw [← Real.rpow_natCast]
    rw [Real.div_rpow hL.le hLL.le,
      Real.div_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_mul hL.le, ← Real.rpow_mul hLL.le]
    rw [div_mul_div_comm]
    rw [← Real.rpow_add hL, ← Real.rpow_add hLL]
    congr 2 <;>
      push_cast [Nat.cast_sub hk] <;>
      norm_num <;> ring
  calc
    (L / LL) ^ k = A ^ (2 / 3 : ℝ) *
        (L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
          LL ^ (((2 * k : ℕ) : ℝ) / 3)) := heq
    _ < B ^ (2 / 3 : ℝ) *
        (L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
          LL ^ (((2 * k : ℕ) : ℝ) / 3)) :=
      mul_lt_mul_of_pos_right hpow hrest
    _ = B ^ (2 / 3 : ℝ) * L ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
        LL ^ (((2 * k : ℕ) : ℝ) / 3) := by ring

/-- Dense Cauchy--Davenport--Chowla branch, with the same bounded output
shape as the sparse theorem. -/
theorem bounded_inverse_subset_sum_of_card {n C : ℕ} [NeZero n]
    (M : Finset ℕ) (hcoprime : ∀ m ∈ M, Nat.Coprime m n)
    (hdense : n ≤ M.card) (hcard : M.card ≤ C) (a : ZMod n) :
    ∃ K ⊆ M, K.card ≤ C ∧
      K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  obtain ⟨K, hKM, hsum⟩ :=
    Erdos285.Modular.inverse_subset_sum_surjective_of_card n M hcoprime hdense a
  exact ⟨K, hKM, (card_le_card hKM).trans hcard, hsum⟩

/-- **Martin's prescribed inverse subset-sum lemma** (published Lemma 11).

For every fixed positive `k` and all sufficiently large moduli `n`, a set
`M` satisfying Martin's displayed lower bounds and whose elements are
products of `k` distinct primes avoiding `n` represents every residue as a
sum of inverses of a subset.  The subset cardinality is bounded by any
given `D` bounding `M.card`.

The proof uses Chowla's dense branch when `n ≤ M.card`.  Otherwise it
instantiates `Dispersion.martin_inverse_dispersion` at a real number strictly
between Martin's cardinality bound and `M.card`, then applies the finite
Fourier product estimate above. -/
theorem eventually_bounded_inverse_subset_sum_of_martin_hypotheses
    (k : ℕ) (hk : 0 < k) :
    ∀ᶠ n : ℕ in atTop, ∀ (D : ℕ) (B : ℝ) (M : Finset ℕ),
      M.card ≤ D →
      0 < B →
      Real.log n ^ (((k - 1 : ℕ) : ℝ) / 2) /
          Real.log (Real.log n) ^ ((k : ℝ) / 2) < B →
      200 *
          (B ^ (2 / 3 : ℝ) *
              Real.log n ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
            Real.log (Real.log n) ^ (((2 * k : ℕ) : ℝ) / 3)) <
        M.card →
      (∀ m ∈ M, (m : ℝ) < B ∧
        Erdos285.Dispersion.IsKPrimeProductAway k n m) →
      ∀ a : ZMod n, ∃ K : Finset ℕ, K ⊆ M ∧ K.card ≤ D ∧
        K.sum (fun m ↦ ((m : ZMod n)⁻¹)) = a := by
  have hllTop : Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [Erdos285.Dispersion.martin_inverse_dispersion k hk,
    eventually_gt_atTop (1 : ℕ),
    hllTop.eventually (eventually_gt_atTop (0 : ℝ))] with n hMartin hn hnll
  intro D B M hMD hB hBsource hcardSource hM a
  have : NeZero n := ⟨Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)⟩
  by_cases hdense : n ≤ M.card
  · have hcoprime : ∀ m ∈ M, Nat.Coprime m n := by
      intro m hm
      exact Erdos285.Dispersion.isKPrimeProductAway_coprime (hM m hm).2
    exact bounded_inverse_subset_sum_of_card M hcoprime hdense hMD a
  · have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hn)
    let S : ℝ :=
      200 *
        (B ^ (2 / 3 : ℝ) *
            Real.log n ^ (((2 * k + 1 : ℕ) : ℝ) / 3) /
          Real.log (Real.log n) ^ (((2 * k : ℕ) : ℝ) / 3))
    let C : ℝ := (S + M.card) / 2
    have hSM : S < (M.card : ℝ) := by
      simpa [S] using hcardSource
    have hSC : S < C := by
      dsimp [C]
      linarith
    have hCM : C < (M.card : ℝ) := by
      dsimp [C]
      linarith
    have hSpos : 0 < S := by
      dsimp [S]
      positivity
    have hCpos : 0 < C := hSpos.trans hSC
    have hfactor := martin_source_factor_gt_dispersion_factor
      hk hlog hnll hBsource
    have hdispCard :
        200 * (Real.log n / Real.log (Real.log n)) ^ k < C := by
      calc
        200 * (Real.log n / Real.log (Real.log n)) ^ k < S := by
          dsimp [S]
          exact mul_lt_mul_of_pos_left hfactor (by norm_num)
        _ < C := hSC
    have hMlt : M.card < n := Nat.lt_of_not_ge hdense
    have hCn : C < (n : ℝ) := by
      have hMltR : (M.card : ℝ) < n := by exact_mod_cast hMlt
      exact hCM.trans hMltR
    have hDispersion := hMartin B C M hB hCpos hdispCard hCn hCM hM
    let delta : ℝ := Erdos285.Dispersion.dispersionThreshold n k B C
    have hdelta : 0 ≤ delta := by
      dsimp [delta, Erdos285.Dispersion.dispersionThreshold]
      positivity
    have hdecay : 2 * Real.log n < delta ^ 2 * C := by
      have hthreshold :=
        Erdos285.FourierBound.martin_published_cardinality_bound_implies_threshold
          hB hlog hnll hSC
      simpa [delta, S, Erdos285.Dispersion.dispersionThreshold, mul_comm] using
        hthreshold
    have hscaled : ∀ h : ZMod n, h ≠ 0 → C ≤
        2 * ((M.filter fun m ↦
          delta ≤ (characterDistance n h m : ℝ) / n).card : ℝ) := by
      intro h hh
      have hhpos : 0 < h.val := ZMod.val_pos.mpr hh
      have hfar := hDispersion h.val hhpos (ZMod.val_lt h)
      let far := M.filter fun m ↦
        Erdos285.Dispersion.dispersionThreshold n k B C <
          Erdos285.Dispersion.inverseDistance n h.val m
      let scaled := M.filter fun m ↦
        delta ≤ (characterDistance n h m : ℝ) / n
      have hsub : far ⊆ scaled := by
        intro m hm
        have hm' := mem_filter.mp hm
        apply mem_filter.mpr
        refine ⟨hm'.1, ?_⟩
        have hle := le_of_lt hm'.2
        simpa [far, scaled, delta, Erdos285.Dispersion.inverseDistance,
          characterDistance_eq_dispersion_centeredInverse] using hle
      have hcards : far.card ≤ scaled.card := card_le_card hsub
      have hfarC : C ≤ 2 * (far.card : ℝ) := by
        have hfar' : C / 2 ≤ (far.card : ℝ) := by
          simpa [far] using hfar
        linarith
      calc
        C ≤ 2 * (far.card : ℝ) := hfarC
        _ ≤ 2 * (scaled.card : ℝ) := by
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcards) (by norm_num)
        _ = 2 * ((M.filter fun m ↦
            delta ≤ (characterDistance n h m : ℝ) / n).card : ℝ) := by
          rfl
    obtain ⟨K, hKM, hsum⟩ :=
      inverse_subset_sum_surjective_of_real_scaled_dispersion
        hn M delta C hdelta hscaled hdecay a
    exact ⟨K, hKM, (card_le_card hKM).trans hMD, hsum⟩

end

end SubsetSum

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` -/

section

open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
private theorem _root_.Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Sobolev.lean` -/

section

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2

instance : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

lemma continuous (f : CS n E) : Continuous f := f.h1.continuous

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  ext x ; exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  ext v ; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • f.deriv (R⁻¹ • x)) x := by
  simpa [deriv_scale'] using hasDerivAt (f.scale R) x

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih =>
      have hderiv : ⇑(SchwartzMap.derivCLM ℝ ℂ f) = _root_.deriv (f : ℝ → ℂ) := by
        funext x
        exact SchwartzMap.derivCLM_apply (𝕜 := ℝ) (F := ℂ) f x
      simpa [iteratedDeriv_succ', hderiv] using
        ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

lemma hf (f : W21) : Integrable f := f.integrable zero_le_two

lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

end W21

set_option maxHeartbeats 800000 in
-- The dominated-convergence proof below needs more heartbeats in Lean 4.32.
theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by

  -- Definitions
  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv

  -- Properties of h
  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    simpa [h, h', CS.deriv_scale'] using
      (CS.hasDerivAt_scale (g : CS 2 ℝ) R v).const_sub 1
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v

  -- Proof
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)

  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4

  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v :
        deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1]
        convert (l5.add l7).deriv using 1
        · congr 1
        · ring
      simp_rw [this, F]

    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by
        change _root_.deriv g.toFun =ᶠ[𝓝 0] 0
        refine g.zero.deriv.trans ?_
        simp
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by
        change _root_.deriv g'.toFun =ᶠ[𝓝 0] 0
        refine evg'.deriv.trans ?_
        simp
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · rw [Filter.ZeroAtFilter]
        simpa [h] using ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Fourier.lean` -/

section

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp z.norm_coe

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by
      simp only [Circle.norm_coe, one_add_one_eq_two]
      exact le_rfl)⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by
    simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  simpa [Function.comp_def, e, mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_fourierChar (-x * u)).scomp x l2

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  simp [fourier_real_eq, ← integral_const_mul, Real.fourierChar, Circle.exp,
    ← smul_mul_assoc, mul_smul_comm]

end lemmas

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Defs.lean` -/

section

open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Asymptotics
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev

noncomputable abbrev Psi (x : ℝ) : ℝ := ψ x

noncomputable def M (x : ℝ) : ℝ :=
  ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ)

noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊

noncomputable def pi_star (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊, (Λ n : ℝ) / n

noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t

noncomputable def Eψ (x : ℝ) : ℝ := |ψ x - x| / x

noncomputable def admissible_bound (A B C R : ℝ) (x : ℝ) :=
  A * (log x / R) ^ B * exp (-C * (log x / R) ^ ((1 : ℝ) / (2 : ℝ)))

def Eψ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ ε

noncomputable def Eπ (x : ℝ) : ℝ :=
  |pi x - Li x| / (x / log x)

noncomputable def Eπ_star (x : ℝ) : ℝ :=
  |pi_star x - Li x| / (x / log x)

def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε

def Eπ_star.bound (ε x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ ε

lemma admissible_bound.mono
    (A B C R : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R) :
    AntitoneOn (admissible_bound A B C R)
      (Set.Ici (exp (R * (2 * B / C) ^ 2))) := by
  intro a ha b _ hab
  simp only [admissible_bound, mul_assoc]
  have hua : (2 * B / C) ^ 2 ≤ log a / R := by
    rw [le_div_iff₀ hR, mul_comm ((2 * B / C) ^ 2), ← log_exp (R * (2 * B / C) ^ 2)]
    exact log_le_log (exp_pos _) (Set.mem_Ici.mp ha)
  have huab : log a / R ≤ log b / R :=
    div_le_div_of_nonneg_right
      (log_le_log ((exp_pos _).trans_le (Set.mem_Ici.mp ha)) hab) hR.le
  have hua₀ : 0 < log a / R :=
    lt_of_lt_of_le (by positivity) hua
  apply mul_le_mul_of_nonneg_left _ hA.le
  rw [rpow_def_of_pos (hua₀.trans_le huab), rpow_def_of_pos hua₀,
    ← exp_add, ← exp_add, exp_le_exp]
  let sa := (log a / R) ^ ((1 : ℝ) / 2)
  let sb := (log b / R) ^ ((1 : ℝ) / 2)
  rw [show log (log b / R) = 2 * log sb from by
      grind [log_rpow (hua₀.trans_le huab) ((1 : ℝ) / 2)],
    show log (log a / R) = 2 * log sa from by
      grind [log_rpow hua₀ ((1 : ℝ) / 2)]]
  have hsab : sa ≤ sb :=
    rpow_le_rpow (le_trans (by positivity) hua) huab (by positivity)
  have : 2 * B / C ≤ sa := by
    rw [show (2 * B / C : ℝ) = ((2 * B / C) ^ 2) ^ ((1 : ℝ) / 2) from by
      rw [← rpow_natCast _ 2, ← rpow_mul (by positivity)]
      norm_num [rpow_one]]
    exact rpow_le_rpow (by positivity) hua (by positivity)
  suffices h : AntitoneOn (fun t ↦ 2 * B * log t - C * t) (Set.Ici (2 * B / C)) by
    grind [h (Set.mem_Ici.mpr this) (Set.mem_Ici.mpr (this.trans hsab)) hsab]
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact ((continuousOn_const.mul (continuousOn_log.mono fun t ht ↦
        ne_of_gt ((div_pos (by positivity) hC).trans_le ht))).sub
      (continuousOn_const.mul continuousOn_id))
  · intro t ht
    rw [interior_Ici] at ht
    exact (((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
      ((hasDerivAt_id t).const_mul C)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hdt : HasDerivAt (fun t ↦ 2 * B * log t - C * t) (2 * B * t⁻¹ - C * 1) t :=
      ((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
        ((hasDerivAt_id t).const_mul C)
    rw [hdt.deriv, mul_one, sub_nonpos, ← div_eq_mul_inv,
      div_le_iff₀ ((div_pos (by positivity) hC).trans ht)]
    linarith [(div_lt_iff₀ hC).mp ht, mul_comm C t]

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean` -/

section

open Filter Topology

section
open Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']

-- to replace existing `isLittleO_const_id_atTop`

-- to replace existing `isLittleO_const_id_atBot`

private theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf

private theorem _root_.Asymptotics.IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean` -/

section

section
open Function

variable {α : Type*} [Zero α]

private theorem _root_.Function.support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

private theorem _root_.Function.support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/SmoothExistence.lean` -/

section
set_option lang.lemmaCmd true

open MeasureTheory Set Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]

lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Wiener.lean` -/

section
set_option lang.lemmaCmd true
set_option backward.isDefEq.respectTransparency false

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]

@[simp] lemma W21.ofCS2_toFun (ψ : CS 2 ℂ) : (W21.ofCS2 ψ).toFun = ψ.toFun := rfl

@[simp] lemma W21.ofCS2_apply (ψ : CS 2 ℂ) (x : ℝ) : (W21.ofCS2 ψ : W21) x = ψ x := rfl

@[simp] lemma W21.sub_toFun (f g : W21) : (f - g).toFun = f.toFun - g.toFun := rfl

noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'

lemma nterm_eq_norm_term {f : ℕ → ℂ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]

theorem norm_term_eq_nterm_re (s : ℂ) :
    ‖term f s n‖ = nterm f (s.re) n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ ↦ rfl)
  intro h
  congr
  refine norm_natCast_cpow_of_pos (by omega) s

lemma hf_coe1 (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hσ : 1 < σ') :
    ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]

instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

-- TODO - add to mathlib
attribute [fun_prop] Real.continuous_fourierChar

lemma first_fourier_aux1 (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  fun_prop

lemma first_fourier_aux2a :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]

lemma first_fourier_aux2 (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 (-(y * (1 / (2 * π) * Real.log (n / x)))) • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [term, hn]
  simp only [term, hn, ↓reduceIte]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ σ'))) • ψ y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by norm_num)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_inv,
        neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group

set_option backward.isDefEq.respectTransparency false in
lemma first_fourier (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by

  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ AEMeasurable.aestronglyMeasurable ?_
        have := hsupp.aemeasurable
        fun_prop
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp

@[continuity]
lemma continuous_multiplicative_ofAdd : Continuous (⇑Multiplicative.ofAdd : ℝ → ℝ) := ⟨fun _ ↦ id⟩

attribute [fun_prop] measurable_coe_nnreal_ennreal

lemma second_fourier_integrable_aux1a (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_integrable_aux1 (hcont : Measurable ψ) (hsupp : Integrable ψ) (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
    (𝐞 (Multiplicative.ofAdd (-(a * (u / (2 * π))))) : ℂ) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    -- TODO: find out why fun_prop does not play well with Multiplicative.ofAdd
    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one,
      Multiplicative.ofAdd, Equiv.coe_fn_mk, smul_eq_mul]
    fun_prop
  · let f1 : ℝ → ENNReal := fun a1 ↦ ‖cexp (-(↑a1 * (↑σ' - 1)))‖ₑ
    let f2 : ℝ → ENNReal := fun a2 ↦ ‖ψ a2‖ₑ
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (second_fourier_integrable_aux1a hσ).2 hsupp.2

lemma second_fourier_integrable_aux2 (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.norm_exp]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_aux (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring

set_option backward.isDefEq.respectTransparency false in
lemma second_fourier (hcont : Measurable ψ) (hsupp : Integrable ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by

  conv in ↑(rexp _) * _ => { rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact second_fourier_integrable_aux1 hcont hsupp hσ
  rw [← integral_const_mul]
  congr 1; ext t
  dsimp [Real.fourierChar, Circle.exp]

  simp_rw [mul_smul_comm, ← smul_mul_assoc, integral_mul_const]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  congr 1
  conv =>
    lhs
    enter [2]
    ext a
    rw [AddChar.coe_mk, Submonoid.mk_smul, smul_eq_mul]
  push_cast
  simp_rw [← Complex.exp_add]
  have (u : ℝ) :
      2 * ↑π * -(↑t * (↑u / (2 * ↑π))) * I + -↑u * (↑σ' - 1) = (1 - σ' - t * I) * u := calc
    _ = -↑u * (↑σ' - 1) + (2 * ↑π) / (2 * ↑π) * -(↑t * ↑u) * I := by ring
    _ = -↑u * (↑σ' - 1) + 1 * -(↑t * ↑u) * I := by rw [div_self (by norm_num)]
    _ = _ := by ring
  simp_rw [this]
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c, sub_ne_zero.mpr hσ.ne]
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by simp only [f']; field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ ‖cexp (c * ↑x)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (· * (1 - σ')) atTop atBot by simpa [Complex.norm_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx

lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)

lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, F_mul, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm

lemma decay_bounds_cor (ψ : W21) :
    ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  simpa only [div_eq_mul_inv] using ⟨_, decay_bounds_key ψ⟩

set_option backward.isDefEq.respectTransparency false in
@[continuity, fun_prop] lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf

lemma W21.integrable_fourier (ψ : W21) (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  have l1 (C) : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa [div_eq_mul_inv] using (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    apply Continuous.aestronglyMeasurable ; fun_prop
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)

lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by

  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simp only [LSeries.term, h, ↓reduceIte]
      exact continuous_const.div₀
        (continuous_const.cpow (by fun_prop) (fun x => by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))

-- Here compact support is used but perhaps it is not necessary
set_option backward.isDefEq.respectTransparency false in
lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) (σ' : ℝ)
    (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ)
      (u / (2 * π)) = ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hint l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier ψ.h1.continuous.measurable hint l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    exact l6.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul ψ.h1.continuous).mul l8
    fun_prop
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact ψ.h2.mul_left.mul_right.mul_left.mul_left

  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_const_mul, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  left ; left
  field_simp [e2]
  norm_cast
  simp [mul_assoc, ← rpow_add l3]

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i

def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n

/- TODO nnabla is redundant -/
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)

def shift (u : α → E) (n : α) : E := u (n + 1)

@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]

lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]

@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]

lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])

lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)

omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]

omit [Sub α] in
@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

end nabla

private lemma _root_.Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, Finset.sum_range_add, Finset.sum_range_one, add_comm 1] ; rfl

private lemma _root_.Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]

lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 -
    cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x ∈ Finset.range (n + 1), A (x + 1) * b x = ∑ x ∈ Finset.range n,
      A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x ∈ Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x ∈ Finset.range n,
      A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp only [cumsum, ha, Pi.mul_apply, nabla, sub_mul, Finset.sum_sub_distrib, l1, l2, shift,
    mul_sub]
  abel

lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  change cumsum (a * b) (n + 1) =
    cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * (fun i => b (i + 1) - b i)) n
  simpa using summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)

lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'

lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1

private lemma _root_.Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]

lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply, one_mem,
    CStarRing.norm_of_mem_unitary, mul_one, eventually_atTop]
  constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (m := N) (n := n) (by grind)
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by grind)⟩

lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]

lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := Nat.le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := by omega
  simpa [r2] using hC (n - 1) r1

lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift, cumsum] using Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla]
    using hAb.add h

lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp only [this, ↓reduceIte, h, ge_iff_le, v] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]

lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by
    filter_upwards [l7, l8] with n l2 l8; dsimp [u]; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) :=
    l3.comp_tendsto <| tendsto_pow_atTop_atTop_of_one_lt Nat.le.refl
  filter_upwards [l5, l8] with k l5 l8
  simp only [l5, mul_inv_rev, Nat.cast_pow, Nat.cast_ofNat, log_pow, u]
  field_simp

lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)

lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]

lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)

lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1

lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  · ext x
    simp only [Function.comp_apply]
    congr
    field_simp
    simp
  · rfl

lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1; simp only [add_zero]; field_simp

private lemma _root_.Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff'']
  refine ⟨2⁻¹, by norm_num, ?_⟩
  filter_upwards [h] with x h
  simp only [norm_eq_abs, Pi.add_apply] at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)

private lemma _root_.Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h

lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 ; ring

lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp only [add_sub_cancel_left, div_one] at htx
  rw [nabla, ← htx, inv_le_inv₀ (by linarith) hx]
  exact ht1.le

lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using
    log_add_one_sub_log_le l1

lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring

lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by

  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 +
        (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by
        simpa [Function.comp_def] using
          (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)

  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))

lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)

private lemma _root_.Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)

/-- Should this be a gcongr lemma? -/
@[local gcongr]
theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith

lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by

  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _

  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop,
      nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv,
      mul_assoc]

  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul hx)
    · filter_upwards [Real.log_eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hx'
      rw [← not_imp_not]
      intro _
      positivity
  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff]; use 1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      filter_upwards [eventually_ge_atTop x] with n hn
      have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
      have : 0 ≤ n := hx.le.trans hn
      simp only [d]
      gcongr <;> simp [Real.log_nonneg, *]
    filter_upwards [l2, l3, e3] with n e1 e2 e3
    simp_rw [one_mul]
    gcongr

  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    change nabla d =O[atTop] (fun n => (Real.log n) ^ 2)
    simpa [d] using (nnabla_mul_log_sq ((2 * π) ^ 2) hx)

  apply EventuallyEq.trans_isBigO l1

  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  filter_upwards [eventually_ge_atTop 2, Real.log_eventually_gt_atTop 0] with n hn hn'
  field_simp

lemma nnabla_bound (C : ℝ) {x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp only [div_eq_mul_inv, mul_inv, nnabla_mul, one_mul]
  apply IsBigO.const_mul_left
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using nnabla_bound_aux hx

def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n

def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f

lemma cheby.bigO (h : cheby f) : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n

lemma limiting_fourier_lim1_aux (hcheby : cheby f) (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by

  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)
  replace hcheby := hcheby.bigO

  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) :=
    l1.trans
      (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    simp only [BoundedAtFilter]
    field_simp
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ 2 ^ 2 * π ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp only [norm_div, norm_mul, norm_eq_abs, abs_eq_self.mpr hC, norm_pow,
      abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this, Pi.one_apply, one_mem,
      CStarRing.norm_of_mem_unitary, mul_one, ge_iff_le, Nat.abs_ofNat]
    apply div_le_of_le_mul₀ this hC
    rw [mul_add, ← mul_assoc]
    apply le_add_of_le_of_nonneg le_rfl
    positivity
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a, div_eq_mul_inv] using IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).natCast ; simp [nnabla, a]

  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp
      grind
    field_simp

theorem limiting_fourier_lim1 (hcheby : cheby f) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦
        ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence
    (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, CharP.cast_eq_zero, div_zero,
      tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    by_cases h : n = 0 <;> simp only [nterm, h, ↓reduceIte, CharP.cast_eq_zero, div_zero, le_refl]
    have : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.pos_iff_ne_zero.mpr h
    refine div_le_div₀ (norm_nonneg _) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le

theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict

theorem limiting_fourier_lim2 (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity

theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by

  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh

  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖

  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous
    · apply Continuous.const_cpow (by fun_prop) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
    intro u hu
    apply Eventually.of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [norm_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]

  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport ψ.h2.norm.mul_left
    have := ψ.h1.continuous ; fun_prop
  · apply Eventually.of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])

lemma limiting_fourier (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l1 := limiting_fourier_lim1 hcheby ψ (by linarith)
  have l2 := limiting_fourier_lim2 A ψ hx
  have l3 := limiting_fourier_lim3 hG ψ hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)

set_option backward.isDefEq.respectTransparency false in
lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by

  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf

  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))

  simp_rw [tendsto_congr' l2]
  convert_to Tendsto (fun x => 𝓕 f (-Real.log x / (2 * π))) atTop (𝓝 0)
  · ext ; congr ; ext
    simp only [← ofReal_mul, mul_comm (f _), fourierChar, Circle.exp, ContinuousMap.coe_mk,
      innerₗ_apply_apply, RCLike.inner_apply, conj_trivial, AddChar.coe_mk, mul_neg, ofReal_neg,
      neg_mul]
    congr
    rw [← neg_mul] ; congr ; norm_cast ; field_simp
  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)

lemma limiting_cor (ψ : CS 2 ℂ) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  apply limiting_cor_aux.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx using
    limiting_fourier hcheby hG hG' hf ψ hx |>.symm

lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by

  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩

noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity

lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    have hpow := l4.pow 2
    have hpow' : HasDerivAt ((fun t : ℝ => a * log t) ^ 2)
        (2 * a ^ 2 * t⁻¹ * log t) t := hpow.congr_deriv (by ring)
    exact hpow'.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [Pi.pow_apply])
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    have hprod := (hasDerivAt_id' t).mul l2
    have hprod' : HasDerivAt (((fun x : ℝ => x) * fun t => 1 + (a * Real.log t) ^ 2))
        (pp a (log t)) t := by
      apply hprod.congr_deriv
      rw [show t * (2 * a ^ 2 * t⁻¹ * log t) = 2 * a ^ 2 * log t by
        rw [show t * (2 * a ^ 2 * t⁻¹ * log t) = (t * t⁻¹) * (2 * a ^ 2 * log t) by ring]
        rw [mul_inv_cancel₀ ht, one_mul]]
      simp only [pp]
      ring
    have hprod'' : HasDerivAt (fun t : ℝ => t * (1 + (a * Real.log t) ^ 2))
        (pp a (log t)) t :=
      hprod'.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [Pi.mul_apply])
    exact hprod''.congr_deriv (by
      simp only [pp]
      ring)
  change HasDerivAt (fun t : ℝ => (t * (1 + (a * log t) ^ 2))⁻¹) (hh' a t) t
  apply (l1.inv e1).congr_deriv
  simp only [hh', pp, hh]
  field_simp [inv_eq_one_div, e1, ht]
  ring

lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt

lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity

lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹

lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp

lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)

lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · have : 0 < 1 / (2 * π) := by positivity
    linarith
  · rw [div_lt_iff₀ (by positivity : 0 < 2 * π)]
    have hπ : (2 : ℝ) ≤ π := two_le_pi
    nlinarith

lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by

  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa [cumsum] using hf' (n + 1)) (Finset.sum_nonneg' hf) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg' hf

  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    have hcomm :
        (∑ i ∈ Finset.range (n - 1), (g i - g (i + 1)) * (C * (↑i + 1))) =
          ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) := by
      simp [smul_eq_mul, mul_comm, mul_left_comm]
    rw [hcomm]
    refine le_of_eq ?_
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]

lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring

lemma cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1)
      := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 ; unfold cumsum ; ring

lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  match n with
  | 0 => simp [cumsum]
  | 1 => specialize hg 0 ; specialize hf' 1 ; simp only [cumsum, Finset.range_one,
    Finset.sum_singleton, hf0, Nat.cast_one, mul_one, Pi.zero_apply, Pi.mul_apply, zero_mul,
    ge_iff_le] at hf' hg ⊢ ; positivity
  | n + 2 =>
      convert cancel_aux' hf hg hf' hg' (n + 2) using 1
      · simp [cumsum, Finset.sum_range_succ, add_comm, add_left_comm]
      · simp [cumsum_succ, Nat.cast_add, Nat.cast_ofNat, add_assoc, add_comm]
        ring

theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by

  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]

  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp

  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by
      simp [← sdiff_eq_compl_inter]
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp

  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)

  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  rw [← intervalIntegral.integral_add_adjacent_intervals]
  · exact _root_.add_le_add l1 l3
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp

lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by

  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]

  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹

  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have hder :
        HasDerivAt (fun t => log (t / c)) ((x / c)⁻¹ * (1 / c)) x :=
      @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _
        (l3 (x / c) (by positivity)) (l4 x)
    have heq : c / x * c⁻¹ = x⁻¹ := by
      field_simp [hc.ne', hx.ne']
    simpa [heq] using hder
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    have hder := (l1 x hx).const_mul (a * c / b)
    have heq :
        (a * c / b) * ((1 + (b * log (x / c)) ^ 2)⁻¹ * (b * x⁻¹)) = g' x := by
      simp only [g']
      field_simp [inv_eq_one_div, hb.ne', hc.ne', hx.ne']
    simpa [g, heq] using hder
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]

  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id

  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [_root_.dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]

  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    peel k2 with ε hε δ hδ x h
    intro (hx : 0 ≤ x)
    have := le_iff_lt_or_eq.mp hx
    cases this with
    | inl hx => exact h hx
    | inr hx => simp [g₀, hx.symm, hε]

  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity

  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 ; field_simp ; ring

lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1

lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2

lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert this using 1 <;> simp ; ring

lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i

  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1

  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))

  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv

  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self

  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp

  refine (cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n).trans ?_
  apply mul_le_mul_of_nonneg_left ?_ l3
  simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]

  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  have hsum_ico :
      (∑ x_1 ∈ Finset.Ico 1 n,
          if x_1 = 0 then 1 else x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x)) =
        ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Ico] at hi
    have : i ≠ 0 := by omega
    simp [this]
  rw [hsum_ico]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    simpa [one_div, mul_inv_rev] using (this.mono_set Ioi_subset_Ici_self).integrable

lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx

lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx

variable (f x) in
lemma summable_fourier_aux (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  calc
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖
        = ‖f i / i‖ * ‖𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ := by
          rw [norm_mul]
    _ ≤ ‖f i / i‖ * (W21.norm ψ * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
            (norm_nonneg (f i / i))
    _ = W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
          simp only [Complex.norm_div, RCLike.norm_natCast]
          ring

lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6
    (by simpa using l5.const_smul (W21.norm ψ))

lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by

  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  calc
    (∑' (i : ℕ), ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖)
        ≤ ∑' (i : ℕ),
            W21.norm ψ * (‖f i‖ / ↑i * (1 + (1 / (2 * π) * Real.log (↑i / x)) ^ 2)⁻¹) :=
          Summable.tsum_mono l1 (by simpa [smul_eq_mul] using l5.const_smul (W21.norm ψ)) l6
    _ = W21.norm ψ *
          ∑' (i : ℕ), ‖f i‖ / ↑i * (1 + (1 / (2 * π) * Real.log (↑i / x)) ^ 2)⁻¹ := by
          simpa [smul_eq_mul] using Summable.tsum_const_smul (W21.norm ψ) l5

lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by

  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)

lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by

  have key a : ‖𝓕 (ψ : ℝ → ℂ) (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ :=
    decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 (ψ : ℝ → ℂ) (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · apply Continuous.aestronglyMeasurable ; fun_prop
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by
    apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr
  · apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl

lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by

  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert _root_.add_le_add l1 l2 using 1 ; ring

set_option backward.isDefEq.respectTransparency false in
lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  -- Shorter notation for clarity
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)

  -- Build the truncation
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'

  -- Choose the truncation radius
  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [_root_.dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key

  -- Apply the compact support case
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key

  -- Control the tail term
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    change ‖S x (ψ - W21.ofCS2 (Ψ R)).toFun‖ < ε / 2
    have : 0 < 1 + M := by positivity
    have hbound :
        ‖S x (ψ - W21.ofCS2 (Ψ R)).toFun‖ ≤
          W21.norm (ψ - W21.ofCS2 (Ψ R)).toFun * M := by
      simpa [S, S1, S2, M] using @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply hbound.trans_lt
    have hnorm :
        W21.norm (ψ - W21.ofCS2 (Ψ R)).toFun = W21.norm (ψ.toFun - (Ψ R).toFun) := by
      simp [W21.ofCS2]
    rw [hnorm]
    have hMle : M ≤ 1 + M := by linarith
    apply (mul_le_mul_of_nonneg_left hMle W21.norm_nonneg).trans_lt
    calc
      W21.norm (ψ.toFun - (Ψ R).toFun) * (1 + M)
          < (ε / 2 / (1 + M)) * (1 + M) := mul_lt_mul_of_pos_right hRψ this
      _ = ε / 2 := by field_simp [this.ne']

  -- Conclude the proof
  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 (ψ : ℝ → ℂ) x - 𝓕 ⇑(Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [Real.fourier_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · apply ψ.hf.bdd_mul (c := 1) l1 ; simp [Complex.norm_exp]
    · apply (Ψ R : W21) |>.hf |>.bdd_mul (c := 1) l1
      simp [Complex.norm_exp]

  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp only [one_div, mul_inv_rev, S1_sub_1, mul_sub, S1] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this

  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp only [S1_sub_1, S2] ; rw [integral_sub]
    · ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict

  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)

lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'

-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead

lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f

noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2

@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))

lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus

lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2

theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩

set_option backward.isDefEq.respectTransparency false in
lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by

  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this

theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε

  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi

  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]

  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε

  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, _root_.dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]

lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    have hprod : HasCompactSupport
        (((fun x : ℝ => cexp (2 * ↑π * ↑x)) * fun x => Ψ (rexp (2 * π * x)))) :=
      (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
    rw [hasCompactSupport_iff_eventuallyEq] at hprod ⊢
    exact hprod.mono fun x hx => by
      simpa [h, Pi.mul_apply] using hx
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)

  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    simp only [one_div, mul_inv_rev, hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat,
      toSchwartz_apply, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]

  have key := limiting_cor_schwartz g hf hcheby hG hG'

  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp

  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat, toSchwartz_apply,
      ofReal_div, h]
    norm_cast ; field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx

  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus

  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4

lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

@[norm_cast]
theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal

lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ}
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by

  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp
    (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key

lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by

  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by

  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)

lemma WI_sum_Iab_le {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := hcheby ⌈b * x⌉₊ ; simp only [norm_real, norm_eq_abs] at this ; apply this.trans
  have : 0 ≤ C := by have := hcheby 1 ; simp only [cumsum, Finset.range_one, norm_real,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this ; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith

lemma WI_sum_Iab_le' {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hpos hcheby hb hx

lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, _root_.dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]

lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, _root_.dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]

theorem residue_nonneg {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ ↑(f n)) σ')) (hcheby : cheby fun n ↦ ↑(f n))
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (hG' : EqOn G (fun s ↦ LSeries (fun n ↦ ↑(f n)) s - ↑A / (s - 1)) {s | 1 < s.re}) : 0 ≤ A := by
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact div_nonneg (tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))) hx
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have key := @wiener_ikehara_smooth_real A G f ψ hf hcheby hG hG' h1 h2 h3
  have l2 : 0 ≤ ψ := by apply le_trans _ h4 ; apply indicator_nonneg ; simp
  have l1 : ∀ᶠ x in atTop, 0 ≤ S ψ x := hSnonneg l2
  have l3 : 0 ≤ A * ∫ (y : ℝ) in Ioi 0, ψ y := ge_of_tendsto key l1
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have r1 : 0 ≤ᵐ[Measure.restrict volume (Ioi 0)] ψ := Eventually.of_forall l2
    have r2 : IntegrableOn (fun y ↦ ψ y) (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    have r3 : Ico 1 2 ⊆ Function.support ψ := by intro x hx ; have := h4 x ; simp [hx] at this ⊢ ; linarith
    have r4 : Ico 1 2 ⊆ Function.support ψ ∩ Ioi 0 := by
      simp only [subset_inter_iff, r3, true_and] ; apply Ico_subset_Icc_self.trans ; rw [Icc_subset_Ioi_iff] <;> linarith
    have r5 : 1 ≤ volume (Function.support ψ ∩ Ioi 0) := by
      calc
        (1 : ENNReal) = volume (Ico (1 : ℝ) 2) := by
          simp [Real.volume_Ico]
          norm_num
        _ ≤ volume (Function.support ψ ∩ Ioi 0) := volume.mono r4
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this

lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by

  -- Take care of the trivial case `a = b`
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab

  -- Notation to make the proof more readable
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'

  -- A few facts about the indicator function of `Icc a b`
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le

  -- Bound from above by a smooth function
  have sup_le : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans ; rw [l1.limsup_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Bound from below by a smooth function
  have le_inf : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3 ; rw [l1.liminf_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Combine the two bounds
  have : liminf (S Iab) atTop ≤ limsup (S Iab) atTop := liminf_le_limsup Iab2 Iab3
  refine tendsto_of_liminf_eq_limsup ?_ ?_ Iab2 Iab3 <;> linarith

lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]

lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]

lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]

lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]

lemma WienerIkeharaInterval_discrete {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval hpos hf hcheby hG hG' ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]

lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete hpos hf hcheby hG hG' ha hb |>.comp tendsto_natCast_atTop_atTop

-- TODO with `Ico`

/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/

lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [_root_.dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring

noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N

lemma S_sub_S {f : ℕ → 𝕜} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) : S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    rw [Finset.range_eq_Ico] ; symm ; rw [Finset.range_eq_Ico]
    exact Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _)
      (Nat.ceil_le.mpr (mul_le_of_le_one_left N.cast_nonneg hε))
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]

lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [Real.dist_eq, ← S_sub_S h2.2] using l2.trans_lt h1

set_option maxHeartbeats 1000000 in
-- The Wiener-Ikehara argument below combines several long asymptotic estimates,
-- and the final proof search exceeds Lean's default heartbeat limit.
theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by

  have h_event : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Tendsto (S f ε) atTop (𝓝 (A * (1 - ε))) := by
    have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    intro ε hε
    have hdisc := WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
    exact hdisc.congr' (Eventually.of_forall fun N => by simp [S])
  have hlim : Tendsto (fun ε : ℝ => A * (1 - ε)) (𝓝[>] 0) (𝓝 A) := by
    have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (hε.const_sub 1).const_mul A
  have hmain : Tendsto (S f 0) atTop (𝓝 A) :=
    (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto h_event hlim
  exact hmain.congr' (Eventually.of_forall fun N => by simp [S, cumsum])

theorem vonMangoldt_cheby : cheby Λ := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith

-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)

theorem WeakPNT : Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) := by
  let F := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hnv := riemannZeta_ne_zero_of_one_le_re
  have l1 (n : ℕ) : 0 ≤ Λ n := vonMangoldt_nonneg
  have l2 s (hs : 1 < s.re) : F s = LSeries Λ s - 1 / (s - 1) := by
    have := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
    simp only [F, this, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one, one_div, sub_left_inj]
    apply LSeries_congr
    intro n _
    simp only [ofReal_inj, indicator_apply_eq_self, mem_ofPred_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have l3 : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have l4 : cheby Λ := vonMangoldt_cheby
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm Λ σ') := by
    simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ').norm
  apply WienerIkeharaTheorem' l1 l5 l4 l3 l2

section auto_cheby

variable {f : ℕ → ℝ}

lemma norm_x_cpow_it (x t : ℝ) (hx : 0 < x) : ‖(x : ℂ) ^ (t * I)‖ = 1 := by
  rw [cpow_def_of_ne_zero <| ofReal_ne_zero.mpr hx.ne', ← ofReal_log hx.le]
  convert norm_exp_ofReal_mul_I (t * x.log) using 2
  push_cast; ring_nf

set_option backward.isDefEq.respectTransparency false in
lemma limiting_fourier_aux_gt_zero (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 0 < x) (σ' : ℝ) (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) :=
    (((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8).integrable_of_hasCompactSupport
      ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := fun h ↦ by
    have := congrArg Complex.re (sub_eq_zero.mp h); simp at this; linarith
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) *
      (↑(x ^ (σ' - 1)) * (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    have : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) *
        (↑(x ^ (σ' - 1)) * (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
      simp only [one_div, ← mul_assoc]
      exact ((continuous_const.mul (Continuous.inv₀ (by fun_prop) e2)).mul ψ.h1.continuous).mul l8
    exact this.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right.mul_left.mul_left
  simp_rw [first_fourier hf hint hx hσ', second_fourier ψ.h1.continuous.measurable hint hx hσ',
    ← integral_const_mul, ← integral_sub l4 l5]
  refine integral_congr_ae (.of_forall fun u ↦ ?_)
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  field_simp [e2]; norm_cast; simp [mul_assoc, ← rpow_add hx]

theorem limiting_fourier_lim2_gt_zero (A : ℝ) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
      ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
        (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by
  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  refine Tendsto.mul ?_ (tendsto_integral_filter_of_dominated_convergence _
    (.of_forall fun _ ↦ (by continuity : Continuous _).aestronglyMeasurable) ?_
    (limiting_fourier_lim2_aux x C) (.of_forall fun u ↦ ?_))
  · suffices Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) by
      simpa using ((continuous_ofReal.tendsto 1).comp this).const_mul ↑A
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using (continuous_id.tendsto (1 : ℝ)).const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl hx.ne')
  · refine eventually_of_mem (Ioo_mem_nhdsGT_of_mem (by norm_num : (1 : ℝ) ∈ Set.Ico 1 2)) fun σ' hσ' ↦ ?_
    obtain ⟨h1, h2⟩ := hσ'
    rw [ae_restrict_iff' measurableSet_Ici]
    refine .of_forall fun t ht ↦ ?_
    simp only [norm_mul, neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one,
      norm_exp, neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im,
      sub_self, mul_zero, sub_zero]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) ((abs_nonneg x).trans (le_max_left _ _))
    have hα0 : 0 ≤ σ' - 1 := by linarith
    have hα1 : σ' - 1 ≤ 1 := by linarith
    have hmul1 : (-x.log) * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht hα0
    calc Real.exp (-(t * (σ' - 1)))
        ≤ Real.exp (x.log * (σ' - 1)) := Real.exp_monotone (by linarith)
      _ ≤ max |x| 1 := by
          by_cases hx1 : 1 ≤ x
          · calc _ ≤ Real.exp x.log :=
                Real.exp_monotone (mul_le_of_le_one_right (Real.log_nonneg hx1) hα1)
              _ = |x| := by rw [Real.exp_log hx, abs_of_pos hx]
              _ ≤ _ := le_max_left _ _
          · calc _ ≤ 1 := (Real.exp_monotone (mul_nonpos_of_nonpos_of_nonneg
                  ((Real.log_neg_iff hx).2 (by linarith)).le hα0)).trans_eq Real.exp_zero
              _ ≤ _ := le_max_right _ _
  · suffices Tendsto (fun n ↦ ((rexp (-u * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by simpa using this.mul_const _
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    have : Continuous (fun n ↦ ((rexp (-u * (n - 1))) : ℂ)) := by continuity
    simpa using this.tendsto 1

theorem limiting_fourier_lim3_gt_zero
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by
  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh
  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_Icc.reProdIm (isClosed_tsupport ψ), (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded⟩
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩ (hG.mono l2).norm
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  refine tendsto_integral_filter_of_dominated_convergence (bound := fun a ↦ ‖G z‖ * ‖ψ a‖)
    (eventually_of_mem (Icc_mem_nhdsGT_of_mem (by norm_num : (1 : ℝ) ∈ Set.Ico 1 2)) fun u hu ↦
      ((hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous).mul
        (by simpa using Continuous.const_cpow (by fun_prop) (Or.inl hxC)) |>.aestronglyMeasurable)
    (eventually_of_mem (Icc_mem_nhdsGT_of_mem (by norm_num : (1 : ℝ) ∈ Set.Ico 1 2)) fun u hu ↦
      .of_forall fun v ↦ ?_)
    ((continuous_const.mul ψ.h1.continuous.norm).integrable_of_hasCompactSupport ψ.h2.norm.mul_left)
    (.of_forall fun t ↦ ?_)
  · by_cases h : v ∈ tsupport ψ
    · simp_rw [norm_mul, norm_x_cpow_it x v hx, mul_one]
      exact mul_le_mul_of_nonneg_right (isMaxOn_iff.mp hmax _ (by simp [S, mem_reProdIm, hu.1, hu.2, h])) (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp [Function.notMem_support.mp this]
  · exact ((hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr
      ⟨((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds,
       eventually_nhdsWithin_of_forall fun _ hx' ↦ by simp [(Set.mem_Ioi.mp hx').le]⟩).mul_const _ |>.mul_const _

lemma tendsto_tsum_of_monotone_convergence
    {β : Type*} {f : ℕ → β → ENNReal} {g : β → ENNReal}
    (hmono : ∀ k, Monotone (fun n => f n k))
    (hlim : ∀ k, Tendsto (fun n => f n k) atTop (𝓝 (g k))) :
    Tendsto (fun n => ∑' k, f n k) atTop (𝓝 (∑' k, g k)) := by
  let : MeasurableSpace β := ⊤
  let μ : Measure β := Measure.count
  have hg_iSup (k : β) : (⨆ n : ℕ, f n k) = g k := iSup_eq_of_tendsto (hmono k) (hlim k)
  have h_tend_lint : Tendsto (fun n => ∫⁻ k, f n k ∂μ) atTop (𝓝 (∫⁻ k, (⨆ n, f n k) ∂μ)) := by
    have hmeas : ∀ n, Measurable fun k : β => f n k := fun _ _ _ ↦ trivial
    have hmono_fn : Monotone (fun n => fun k : β => f n k) := fun _ _ hnm k ↦ hmono k hnm
    simpa [lintegral_iSup hmeas hmono_fn] using
      tendsto_atTop_iSup fun _ _ hmn ↦ lintegral_mono fun k ↦ hmono k hmn
  simpa [μ, lintegral_count, hg_iSup] using h_tend_lint

lemma tendsto_tsum_of_monotone_convergence_nhdsGT_one
    {F : ℝ → ℕ → ℝ}
    (hF_nonneg : ∀ σ n, 0 ≤ F σ n)
    (hF_antitone : ∀ n, AntitoneOn (fun σ : ℝ => F σ n) (Set.Ioi (1 : ℝ)))
    (hF_tend : ∀ n, Tendsto (fun σ : ℝ => F σ n) (𝓝[>] (1 : ℝ)) (𝓝 (F 1 n)))
    (hSumm : ∀ σ, 1 < σ → Summable (fun n : ℕ => F σ n))
    (hbounded :
      BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ : ℝ => (∑' n : ℕ, F σ n))) :
    Tendsto (fun σ : ℝ => ∑' n : ℕ, F σ n) (𝓝[>] (1 : ℝ)) (𝓝 (∑' n : ℕ, F 1 n)) := by
  let T : ℝ → ℝ := fun σ => ∑' n : ℕ, F σ n
  have hT_antitone : AntitoneOn T (Set.Ioi (1 : ℝ)) := fun a ha b hb hab ↦
    (hSumm b hb).tsum_le_tsum_of_inj (fun n ↦ n) (fun _ _ h ↦ h) (fun c hc ↦ (hc ⟨c, rfl⟩).elim)
      (fun n ↦ hF_antitone n ha hb hab) (hSumm a ha)
  have hT_bdd : BddAbove (T '' Set.Ioi (1 : ℝ)) := by
    obtain ⟨C, hC⟩ := isBigO_iff.1 hbounded
    have hC' : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), T σ ≤ C := by
      filter_upwards [hC] with σ hσ
      calc T σ ≤ |T σ| := le_abs_self _
        _ = ‖T σ‖ := (Real.norm_eq_abs _).symm
        _ ≤ C * ‖(1 : ℝ → ℝ) σ‖ := hσ
        _ = C := by simp
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_inf_iff_superset.1 hC'
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    have hIoi_sub : Set.Ioi (1 : ℝ) ⊆ V := Filter.mem_principal.mp hV
    have hUsub : U ∩ Set.Ioi (1 : ℝ) ⊆ {σ : ℝ | T σ ≤ C} := fun σ hσ ↦ hUV ⟨hσ.1, hIoi_sub hσ.2⟩
    have hσ0_Ioi : 1 + ε / 2 ∈ Set.Ioi (1 : ℝ) := by simp [half_pos hε]
    have hσ0_leC : T (1 + ε / 2) ≤ C :=
      hUsub ⟨hball (by simp only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left,
        abs_of_pos (half_pos hε)]; exact half_lt_self hε), hσ0_Ioi⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨σ, hσIoi, rfl⟩
    by_cases hσlt : σ < 1 + ε / 2
    · exact hUsub ⟨hball (by
        simp only [Metric.mem_ball, Real.dist_eq]
        rw [abs_of_pos (sub_pos.2 (Set.mem_Ioi.mp hσIoi))]
        linarith [half_lt_self hε]), hσIoi⟩
    · exact (hT_antitone hσ0_Ioi hσIoi (le_of_not_gt hσlt)).trans hσ0_leC
  have hT_tend_sup : Tendsto T (𝓝[>] (1 : ℝ)) (𝓝 (sSup (T '' Set.Ioi (1 : ℝ)))) :=
    hT_antitone.tendsto_nhdsGT hT_bdd
  let σseq : ℕ → ℝ := fun k => 1 + 1 / (k + 1 : ℝ)
  have hσseq_mem (k) : σseq k ∈ Set.Ioi (1 : ℝ) := by
    simp only [σseq, Set.mem_Ioi, lt_add_iff_pos_right]
    positivity
  have hσseq_tend_nhds : Tendsto σseq atTop (𝓝 (1 : ℝ)) := by
    have : Tendsto (fun k : ℕ => (1 : ℝ) + ((k + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1))
    simp only [add_zero] at this
    convert this using 1; ext k; simp [σseq, one_div]
  have hσseq_tend_nhdsWithin : Tendsto σseq atTop (𝓝[>] (1 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hσseq_tend_nhds
      (.of_forall hσseq_mem)
  have hσseq_antitone : Antitone σseq := fun k₁ k₂ hk ↦ by simp only [σseq]; gcongr
  have hmono_seq (n) : Monotone (fun k => F (σseq k) n) := fun k₁ k₂ hk ↦
    hF_antitone n (hσseq_mem k₂) (hσseq_mem k₁) (hσseq_antitone hk)
  have htend_seq (n) : Tendsto (fun k => F (σseq k) n) atTop (𝓝 (F 1 n)) :=
    (hF_tend n).comp hσseq_tend_nhdsWithin
  have hTseq : Tendsto (fun k : ℕ => T (σseq k)) atTop (𝓝 (T 1)) := by
    have hsum1 : Summable (fun n : ℕ => F (1 : ℝ) n) := by
      obtain ⟨C, hC⟩ := hT_bdd
      refine summable_of_sum_range_le (hF_nonneg 1) fun m ↦ le_of_tendsto
        (tendsto_finsetSum _ fun i _ ↦ hF_tend i)
        (eventually_of_mem self_mem_nhdsWithin fun σ hσ ↦
          ((hSumm σ hσ).sum_le_tsum _ (fun n _ ↦ hF_nonneg σ n)).trans (hC ⟨σ, hσ, rfl⟩))
    have hg_ne_top : (∑' n : ℕ, ENNReal.ofReal (F 1 n)) ≠ ⊤ := hsum1.tsum_ofReal_ne_top
    have hENN : Tendsto (fun k => ∑' n, ENNReal.ofReal (F (σseq k) n)) atTop
        (𝓝 (∑' n, ENNReal.ofReal (F 1 n))) :=
      tendsto_tsum_of_monotone_convergence (fun n _ _ hk ↦ ENNReal.ofReal_le_ofReal (hmono_seq n hk))
        (fun n ↦ ENNReal.tendsto_ofReal (htend_seq n))
    have hrew (σ) : (∑' n, ENNReal.ofReal (F σ n)).toReal = ∑' n, F σ n := by
      rw [ENNReal.tsum_toReal_eq (fun n ↦ by simp)]
      exact tsum_congr fun n ↦ by simp [hF_nonneg σ n]
    simp only [T, ← hrew]; exact (ENNReal.tendsto_toReal hg_ne_top).comp hENN
  have hsSup_eq : sSup (T '' Set.Ioi (1 : ℝ)) = T 1 :=
    tendsto_nhds_unique (hT_tend_sup.comp hσseq_tend_nhdsWithin) hTseq
  simpa [T, hsSup_eq] using hT_tend_sup

lemma limiting_fourier_variant_lim1_aux
    {f : ℕ → ℝ} {x : ℝ} (ψ : CS 2 ℂ)
    (hpos : 0 ≤ f)
    (hf : ∀ (σ : ℝ), 1 < σ → Summable (nterm f σ))
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0) :
    ∀ (σ : ℝ), 1 < σ →
      Summable (fun n : ℕ =>
        (if n = 0 then 0 else f n / ((n : ℝ) ^ σ)) *
          (𝓕 ψ.toFun (1 / (2 * π) * Real.log ((n : ℝ) / x))).re) := by
  intro σ hσ
  let y : ℕ → ℝ := fun n => (1 / (2 * π)) * Real.log ((n : ℝ) / x)
  let W : ℕ → ℝ := fun n => (𝓕 ψ.toFun (y n)).re
  let base : ℕ → ℝ := fun n => if n = 0 then 0 else f n / ((n : ℝ) ^ σ)
  obtain ⟨C, hC⟩ := decay_bounds_cor (W21.ofCS2 ψ)
  have hC_nonneg : 0 ≤ C := (norm_nonneg _).trans ((hC 0).trans (by simp))
  have hW_nonneg (n : ℕ) : 0 ≤ W n := (hψpos (y n)).1
  have hnorm_four (n : ℕ) : ‖𝓕 ψ.toFun (y n)‖ = W n := by
    have him0 : (𝓕 ψ.toFun (y n)).im = 0 := (hψpos (y n)).2
    rw [show 𝓕 ψ.toFun (y n) = W n by exact Complex.ext rfl him0]
    simp [abs_of_nonneg (hW_nonneg n)]
  have hW_le_C (n : ℕ) : W n ≤ C := by
    rw [← hnorm_four]; exact (hC (y n)).trans (div_le_self hC_nonneg (by nlinarith [sq_nonneg (y n)]))
  have hbase_summ : Summable base := by
    convert hf σ hσ using 1; ext n
    by_cases hn : n = 0 <;> simp [nterm, base, hn, Real.norm_eq_abs, abs_of_nonneg (hpos n)]
  refine (hbase_summ.mul_left C).of_norm_bounded fun n ↦ ?_
  by_cases hn : n = 0
  · simp [base, hn]
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hbase_nonneg : 0 ≤ base n := by
      simp only [base, hn, if_false]
      exact div_nonneg (hpos n) (Real.rpow_pos_of_pos hnpos σ).le
    calc |base n * W n| = base n * W n := abs_of_nonneg (mul_nonneg hbase_nonneg (hW_nonneg n))
      _ ≤ base n * C := mul_le_mul_of_nonneg_left (hW_le_C n) hbase_nonneg
      _ = C * base n := mul_comm _ _

theorem limiting_fourier_variant_lim1
    {f : ℕ → ℝ} {x : ℝ} {ψ : CS 2 ℂ}
    (hpos : 0 ≤ f)
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0)
    (S : ℝ → ℂ)
    (hSdef :
      ∀ σ' : ℝ,
        S σ' =
          ∑' n : ℕ,
            term (fun n ↦ (f n : ℂ)) (σ' : ℝ) n *
              𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x)))
    (hbounded : BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ' : ℝ => ‖S σ'‖))
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) :
    Tendsto
      (fun σ' : ℝ =>
        ∑' n : ℕ,
          term (fun n ↦ (f n : ℂ)) (σ' : ℝ) n *
            𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x)))
      (𝓝[>] (1 : ℝ))
      (𝓝
        (∑' n : ℕ,
          (f n : ℂ) / (n : ℂ) *
            𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x)))) := by

  let y : ℕ → ℝ := fun n => (π⁻¹ * 2⁻¹) * Real.log ((n : ℝ) / x)
  let w : ℕ → ℝ := fun n => (𝓕 ψ.toFun (y n)).re

  have hw_nonneg : ∀ n, 0 ≤ w n := by
    intro n
    exact (hψpos (y n)).1

  have hFour_eq_ofReal : ∀ n, 𝓕 ψ.toFun (y n) = Complex.ofReal (w n) := by
    intro n
    have h := hψpos (y n)
    refine Complex.ext ?_ ?_
    · simp [w]
    · simp [w, h.2]

  let rterm : ℝ → ℕ → ℝ :=
    fun σ n =>
      if h0 : n = 0 then 0 else (f n) / ((n : ℝ) ^ σ) * (w n)

  have summand_eq_ofReal :
      ∀ (σ : ℝ) (n : ℕ),
        term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)
          = Complex.ofReal (rterm σ n) := by
    intro σ n
    by_cases hn : n = 0
    · subst hn
      simp [rterm, y]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hn0 : 0 ≤ (n : ℝ) := le_of_lt hnpos
      have hcpow :
          ( (n : ℂ) ^ ((σ : ℝ) : ℂ) ) = ( ( (n : ℝ) ^ σ : ℝ) : ℂ ) := by
        simpa using (Complex.ofReal_cpow hn0 σ).symm
      have hpow_ne : ((n : ℝ) ^ σ) ≠ 0 := by
        exact (ne_of_gt (Real.rpow_pos_of_pos hnpos σ))
      calc
        term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)
            =
          ((f n : ℂ) / ((n : ℂ) ^ ((σ : ℝ) : ℂ))) * ( (w n : ℝ) : ℂ ) := by
            simp [term, LSeries.term, hn, hFour_eq_ofReal]
        _ =
          ((f n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)) * ((w n : ℝ) : ℂ) := by
            simp [hcpow]
        _ =
          (( (f n : ℝ) : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)) * ((w n : ℝ) : ℂ) := by
            simp
        _ =
          ( ( (f n : ℝ) / ((n : ℝ) ^ σ) : ℝ) : ℂ ) * ((w n : ℝ) : ℂ) := by
            simp [Complex.ofReal_div]
        _ =
          ( ( (f n : ℝ) / ((n : ℝ) ^ σ) * (w n) : ℝ ) : ℂ ) := by
            simp [Complex.ofReal_mul]
        _ =
          Complex.ofReal (rterm σ n) := by
            simp [rterm, hn]

  let T : ℝ → ℝ := fun σ => ∑' n, rterm σ n

  have tsum_eq_ofReal_T : ∀ σ : ℝ,
      (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
        = Complex.ofReal (T σ) := by
    intro σ
    have hcongr :
        (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
          = ∑' n : ℕ, (Complex.ofReal (rterm σ n)) := by
      refine tsum_congr ?_
      intro n
      simpa using (summand_eq_ofReal σ n)

    calc
      (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
          = ∑' n : ℕ, (Complex.ofReal (rterm σ n)) := hcongr
      _ = Complex.ofReal (∑' n : ℕ, rterm σ n) := by
            simpa using (Complex.ofReal_tsum (fun n : ℕ => rterm σ n)).symm
      _ = Complex.ofReal (T σ) := by rfl

  have hS_ofReal_T : ∀ σ : ℝ, S σ = Complex.ofReal (T σ) := by
    intro σ
    simpa [hSdef σ, y] using (tsum_eq_ofReal_T σ)

  have rterm_nonneg : ∀ σ n, 0 ≤ rterm σ n := by
    intro σ n
    by_cases hn : n = 0
    · subst hn; simp [rterm]
    · have hf : 0 ≤ f n := hpos n
      have hw : 0 ≤ w n := hw_nonneg n
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hden : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
      have : 0 ≤ (f n) / ((n : ℝ) ^ σ) := div_nonneg hf (le_of_lt hden)
      simp [rterm, hn, mul_nonneg this hw]

  have T_nonneg : ∀ σ, 0 ≤ T σ := by
    intro σ
    exact tsum_nonneg (fun n => rterm_nonneg σ n)

  have hT_eq_normS : ∀ σ, T σ = ‖S σ‖ := by
    intro σ
    have := hS_ofReal_T σ
    calc
      T σ = ‖Complex.ofReal (T σ)‖ := by simp [abs_of_nonneg (T_nonneg σ)]
      _ = ‖S σ‖ := by simp [this]

  have hboundedT : BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ : ℝ => T σ) := by
    have : (fun σ : ℝ => T σ) = (fun σ : ℝ => ‖S σ‖) := by
      funext σ; exact hT_eq_normS σ
    simpa [this] using hbounded

  have rterm_antitone : ∀ n, AntitoneOn (fun σ => rterm σ n) (Set.Ioi 1) := by
    intro n σ₁ hσ₁ σ₂ hσ₂ hσ₁₂
    by_cases hn : n = 0
    · subst hn; simp [rterm]
    · have hf : 0 ≤ f n := hpos n
      have hw : 0 ≤ w n := hw_nonneg n
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hpow : (n : ℝ) ^ σ₁ ≤ (n : ℝ) ^ σ₂ :=
        Real.rpow_le_rpow_of_exponent_le hn1 hσ₁₂
      have hinv :
      (1 / ((n : ℝ) ^ σ₂)) ≤ (1 / ((n : ℝ) ^ σ₁)) := by
        have hpos1 : 0 < (n : ℝ) ^ σ₁ := Real.rpow_pos_of_pos hnpos σ₁
        exact one_div_le_one_div_of_le hpos1 hpow
      have hinv_inv : ((n : ℝ) ^ σ₂)⁻¹ ≤ ((n : ℝ) ^ σ₁)⁻¹ := by
        simpa [one_div] using hinv
      have hmul1 :
          (f n) * (((n : ℝ) ^ σ₂)⁻¹) ≤ (f n) * (((n : ℝ) ^ σ₁)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv_inv hf
      have hmul2 :
          ((f n) * (((n : ℝ) ^ σ₂)⁻¹)) * (w n)
            ≤ ((f n) * (((n : ℝ) ^ σ₁)⁻¹)) * (w n) :=
        mul_le_mul_of_nonneg_right hmul1 hw
      simpa [rterm, hn, div_eq_mul_inv, mul_assoc] using hmul2

  have rterm_tend : ∀ n, Tendsto (fun σ : ℝ => rterm σ n) (𝓝[>] (1 : ℝ)) (𝓝 (rterm 1 n)) := by
    intro n
    have hterm :
        Tendsto (fun σ : ℝ => term (fun n ↦ (f n : ℂ)) (σ : ℝ) n)
          (𝓝[>] (1 : ℝ)) (𝓝 ((f n : ℂ) / (n : ℂ))) := by
      by_cases hn : n = 0
      · subst hn
        simp [term, LSeries.term]
      · have hden :
            Tendsto (fun σ : ℝ => ((n : ℂ) ^ ((σ : ℝ) : ℂ))) (𝓝[>] (1 : ℝ)) (𝓝 ((n : ℂ) ^ (1 : ℂ))) := by
          simpa using ((continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds).const_cpow

        have hden' :
            Tendsto (fun σ : ℝ => ((n : ℂ) ^ ((σ : ℝ) : ℂ))) (𝓝[>] (1 : ℝ)) (𝓝 (n : ℂ)) := by
          simpa using hden

        have hnC : (n : ℂ) ≠ 0 := by
          exact_mod_cast hn

        have hterm :
            Tendsto (fun σ : ℝ => term (fun n ↦ (f n : ℂ)) (σ : ℝ) n)
              (𝓝[>] (1 : ℝ)) (𝓝 ((f n : ℂ) / (n : ℂ))) := by
          have hnC : (n : ℂ) ≠ 0 := by
            exact_mod_cast hn
          simp only [term, LSeries.term, hn, ↓reduceIte]
          change Tendsto (((fun _ : ℝ => (f n : ℂ)) /
              fun σ : ℝ => (n : ℂ) ^ ((σ : ℝ) : ℂ)))
            (𝓝[>] (1 : ℝ)) (𝓝 ((f n : ℂ) / (n : ℂ)))
          exact tendsto_const_nhds.div hden' hnC
        exact hterm

    have hsummand :
        Tendsto
          (fun σ : ℝ =>
            term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
          (𝓝[>] (1 : ℝ))
          (𝓝 (((f n : ℂ) / (n : ℂ)) * 𝓕 ψ.toFun (y n))) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (hterm.mul_const (𝓕 ψ.toFun (y n)))

    have hre : ∀ σ, rterm σ n =
        (term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)).re := by
      intro σ
      have := congrArg Complex.re (summand_eq_ofReal σ n)
      simpa [Complex.ofReal_re] using this.symm

    have hRe : Tendsto
        (fun σ : ℝ =>
          (term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)).re)
        (𝓝[>] (1 : ℝ))
        (𝓝 ((((f n : ℂ) / (n : ℂ)) * 𝓕 ψ.toFun (y n)).re)) :=
      (continuous_re.tendsto _).comp hsummand

    have hlimit_re :
      (f n / (n : ℝ)) * (𝓕 ψ.toFun (y n)).re = rterm 1 n := by
      have h0 :
          (term (fun n ↦ (f n : ℂ)) (1 : ℝ) n * 𝓕 ψ.toFun (y n)).re = rterm 1 n := by
        have := congrArg Complex.re (summand_eq_ofReal (σ := (1 : ℝ)) n)
        simpa [Complex.ofReal_re] using this

      by_cases hn : n = 0
      · subst hn
        simp [rterm, y]
      · have h1 :
            (term (fun n ↦ (f n : ℂ)) (1 : ℝ) n * 𝓕 ψ.toFun (y n)).re
              = (f n / (n : ℝ)) * (𝓕 ψ.toFun (y n)).re := by
          simp [Complex.mul_re, term, LSeries.term, hn, y,
                (hψpos (y n)).2]

        exact (h1.symm.trans h0)

    simpa [hre, hlimit_re] using hRe

  have hSumm_rterm : ∀ σ : ℝ, 1 < σ → Summable (fun n : ℕ => rterm σ n) := by
    simpa [rterm] using limiting_fourier_variant_lim1_aux (ψ := ψ)
      (f := f) (x := x) hpos hf hψpos

  have hT_tend :
      Tendsto T (𝓝[>] (1 : ℝ)) (𝓝 (T 1)) := by
    have :
        Tendsto (fun σ : ℝ => ∑' n : ℕ, rterm σ n)
          (𝓝[>] (1 : ℝ))
          (𝓝 (∑' n : ℕ, rterm (1 : ℝ) n)) := by
      refine tendsto_tsum_of_monotone_convergence_nhdsGT_one
        (F := rterm)
        (hF_nonneg := rterm_nonneg)
        (hF_antitone := rterm_antitone)
        (hF_tend := rterm_tend)
        (hSumm := hSumm_rterm)
        (hbounded := hboundedT)

    simpa [T] using this

  have hToReal :
      Tendsto (fun σ => Complex.ofReal (T σ)) (𝓝[>] (1 : ℝ)) (𝓝 (Complex.ofReal (T 1))) :=
    (continuous_ofReal.tendsto _).comp hT_tend

  have hsource :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
        = fun σ : ℝ => Complex.ofReal (T σ) := by
    funext σ
    exact (tsum_eq_ofReal_T σ)

  have hσ1 :
    (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (↑(1:ℝ)) n * 𝓕 ψ.toFun (y n))
      = (↑(T 1) : ℂ) :=
    by simpa using (tsum_eq_ofReal_T (σ := (1:ℝ)))
  have hterm1 :
      ∀ n : ℕ, term (fun n ↦ (f n : ℂ)) (1 : ℂ) n = (f n : ℂ) / (n : ℂ) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [term, LSeries.term]
    · simp [term, LSeries.term, hn]

  have hrewrite :
      (∑' n : ℕ,
        term (fun n ↦ (f n : ℂ)) (1 : ℂ) n * 𝓕 ψ.toFun (y n))
        =
      (∑' n : ℕ,
        (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (y n)) := by
    refine tsum_congr ?_
    intro n
    simp [hterm1 n]

  have htarget :
      (∑' n : ℕ,
        (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (y n))
        = (↑(T 1) : ℂ) := by
    exact (hrewrite.symm.trans hσ1)

  simpa [hsource, htarget, y] using hToReal

lemma limiting_fourier_variant
    (hpos : 0 ≤ f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (ψ : CS 2 ℂ)
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0)
    (hx : 0 < x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l2 := limiting_fourier_lim2_gt_zero (A := A) (x := x) ψ hx
  have l3 := limiting_fourier_lim3_gt_zero (G := G) (x := x) hG ψ hx

  let S : ℝ → ℂ := fun σ' =>
    ∑' n : ℕ,
      term (fun n ↦ (f n : ℂ)) σ' n *
        𝓕 ψ.toFun (1 / (2 * π) * Real.log ((n : ℝ) / x))
  let Pole : ℝ → ℂ := fun σ' =>
    (A : ℂ) * ((x ^ (1 - σ') : ℝ) : ℂ) *
      ∫ u in Set.Ici (-Real.log x),
        (rexp (-u * (σ' - 1)) : ℂ) *
          𝓕 (W21.ofCS2 ψ).toFun (u / (2 * π))
  let RHS : ℝ → ℂ := fun σ' =>
    ∫ t : ℝ, G (σ' + t * I) * ψ.toFun t * (x : ℂ) ^ (t * I)

  have haux :
    (fun σ' ↦
        ∑' (n : ℕ),
          term (fun n ↦ (f n : ℂ)) (σ' : ℂ) n *
            𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x))
        - (A : ℂ) * ((x ^ (1 - σ') : ℝ) : ℂ) *
          ∫ (u : ℝ) in Ici (-Real.log x),
            cexp (-( (u : ℂ) * ((σ' : ℂ) - 1))) *
              𝓕 (W21.ofCS2 ψ).toFun (u / (2 * π)))
      =ᶠ[𝓝[>] (1 : ℝ)]
    (fun σ' ↦
      ∫ (t : ℝ), G ((σ' : ℂ) + (t : ℂ) * I) * ψ.toFun t * (x : ℂ) ^ ((t : ℂ) * I)) := by
    rw [Filter.EventuallyEq]

    refine eventually_nhdsWithin_of_forall ?_
    intro σ' hσ'
    have hσ' : (1 : ℝ) < σ' := by
      simpa [Set.mem_Ioi] using hσ'
    simpa using (limiting_fourier_aux_gt_zero (G := G) (f := f) (A := A) hG' hf ψ hx σ' hσ')

  have haux' :
    (fun σ' : ℝ => S σ') =ᶠ[𝓝[>] (1 : ℝ)] (fun σ' : ℝ => RHS σ' + Pole σ') := by
    rw [Filter.EventuallyEq] at haux ⊢
    filter_upwards [haux] with σ' hσ'
    have hσ'' : S σ' - Pole σ' = RHS σ' := by
      simpa [S, Pole, RHS] using hσ'
    have hadd : (S σ' - Pole σ') + Pole σ' = RHS σ' + Pole σ' :=
      congrArg (fun z : ℂ => z + Pole σ') hσ''
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd

  let Pole₁ : ℂ := (A : ℂ) * ∫ u in Set.Ici (-Real.log x), 𝓕 (W21.ofCS2 ψ).toFun (u / (2 * π))
  let RHS₁ : ℂ := ∫ t : ℝ, G (1 + (t : ℂ) * I) * ψ.toFun t * (x : ℂ) ^ ((t : ℂ) * I)

  have hRHS_le :
      ∀ᶠ σ' : ℝ in 𝓝[>] (1 : ℝ), ‖RHS σ'‖ ≤ ‖RHS₁‖ + 1 := by
    have hball : Metric.ball RHS₁ (1 : ℝ) ∈ 𝓝 RHS₁ := by
      simpa using (Metric.ball_mem_nhds (x := RHS₁) (ε := (1 : ℝ)) (by norm_num))
    have hpre : {σ' : ℝ | RHS σ' ∈ Metric.ball RHS₁ (1 : ℝ)} ∈ (𝓝[>] (1 : ℝ)) :=
      l3 hball
    filter_upwards [hpre] with σ' hmem
    have hdist' : dist (RHS σ') RHS₁ < (1 : ℝ) := by
      simpa [Metric.mem_ball] using hmem
    have hdist : ‖RHS σ' - RHS₁‖ < (1 : ℝ) := by
      simpa [dist_eq_norm] using hdist'
    have htri : ‖RHS σ'‖ ≤ ‖RHS₁‖ + ‖RHS σ' - RHS₁‖ := by
      have h := norm_add_le (RHS σ' - RHS₁) RHS₁
      simpa [sub_add_cancel, add_comm, add_left_comm, add_assoc] using h
    have hle : ‖RHS₁‖ + ‖RHS σ' - RHS₁‖ ≤ ‖RHS₁‖ + (1 : ℝ) := by
      exact add_le_add_right (le_of_lt hdist) ‖RHS₁‖
    exact htri.trans hle

  have hPole_le :
    ∀ᶠ σ' : ℝ in 𝓝[>] (1 : ℝ), ‖Pole σ'‖ ≤ ‖Pole₁‖ + 1 := by
    have hball : Metric.ball Pole₁ 1 ∈ 𝓝 Pole₁ := by
      simpa using (Metric.ball_mem_nhds Pole₁ (by norm_num : (0 : ℝ) < 1))
    have hpre : {σ' : ℝ | Pole σ' ∈ Metric.ball Pole₁ 1} ∈ (𝓝[>] (1 : ℝ)) := l2 hball
    filter_upwards [hpre] with σ' hmem
    have hdist : ‖Pole σ' - Pole₁‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hmem
    have htri : ‖Pole σ'‖ ≤ ‖Pole₁‖ + ‖Pole σ' - Pole₁‖ := by
      have hdecomp : Pole σ' = Pole₁ + (Pole σ' - Pole₁) := by abel
      have hnorm_eq : ‖Pole σ'‖ = ‖Pole₁ + (Pole σ' - Pole₁)‖ := by
        simp [congrArg (fun z : ℂ => ‖z‖) hdecomp]
      calc
        ‖Pole σ'‖ = ‖Pole₁ + (Pole σ' - Pole₁)‖ := hnorm_eq
        _ ≤ ‖Pole₁‖ + ‖Pole σ' - Pole₁‖ := norm_add_le _ _
    have hdist_le : ‖Pole σ' - Pole₁‖ ≤ 1 := le_of_lt hdist
    have hsum : ‖Pole₁‖ + ‖Pole σ' - Pole₁‖ ≤ ‖Pole₁‖ + 1 := by
      simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_left hdist_le ‖Pole₁‖)
    exact htri.trans hsum

  have hS_le :
      ∀ᶠ σ' : ℝ in 𝓝[>] (1 : ℝ),
        ‖S σ'‖ ≤ (‖RHS₁‖ + 1) + (‖Pole₁‖ + 1) := by
    rw [Filter.EventuallyEq] at haux'
    filter_upwards [haux', hRHS_le, hPole_le] with σ' hEq hR hP
    calc
      ‖S σ'‖ = ‖RHS σ' + Pole σ'‖ := by simp [hEq]
      _ ≤ ‖RHS σ'‖ + ‖Pole σ'‖ := norm_add_le _ _
      _ ≤ (‖RHS₁‖ + 1) + (‖Pole₁‖ + 1) := by
        exact add_le_add hR hP

  have hbounded : BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ' : ℝ => ‖S σ'‖) := by
    let C : ℝ := ‖RHS₁‖ + 1 + (‖Pole₁‖ + 1)
    simp only [BoundedAtFilter, Asymptotics.IsBigO, Asymptotics.IsBigOWith]
    refine ⟨C, ?_⟩
    filter_upwards [hS_le] with σ' hσ'
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (S σ'))] using hσ'

  have hcoef : (1 / (2 * π) : ℝ) = (π⁻¹ * 2⁻¹ : ℝ) := by field_simp [pi_ne_zero]

  have l1 :=
    limiting_fourier_variant_lim1
      (f := f) (x := x) (ψ := ψ)
      hpos hψpos
      (S := S)
      (hSdef := by
        intro σ
        simp [S, hcoef] )
      hbounded
      hf
  have l1S :
    Tendsto S (𝓝[>] (1 : ℝ))
      (𝓝 (∑' n : ℕ, (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (1 / (2 * π) * Real.log (↑n / x)))) := by
    simpa [S, hcoef] using l1

  have l12 : Tendsto (fun σ' : ℝ => S σ' - Pole σ') (𝓝[>] (1 : ℝ))
    (𝓝 ((∑' n : ℕ, (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (1 / (2 * π) * Real.log (↑n / x))) - Pole₁)) :=
  l1S.sub l2

  have hPole : (Pole : ℝ → ℂ) =ᶠ[𝓝[>] (1 : ℝ)] Pole := by simp
  have haux_sub :
    (fun σ' : ℝ => S σ' - Pole σ') =ᶠ[𝓝[>] (1 : ℝ)] RHS := by
    filter_upwards [haux'] with σ' hσ'
    calc
      S σ' - Pole σ'
          = (RHS σ' + Pole σ') - Pole σ' := by simp [hσ']
      _   = RHS σ' := by simp
  have hlim :=
    tendsto_nhds_unique_of_eventuallyEq (l1S.sub l2) l3 haux_sub

  simpa [Pole₁, RHS₁] using hlim

lemma norm_mul_integral_Ici_le_integral_norm
    (A : ℂ) (F : ℝ → ℂ) (a : ℝ)
    (hF : IntegrableOn F (Set.Ici a))
    (hnorm : Integrable (fun u : ℝ => ‖F u‖)) :
    ‖A * (∫ u in Set.Ici a, F u)‖ ≤ ‖A‖ * (∫ u : ℝ, ‖F u‖) := by
  have hmul : ‖A * (∫ u in Set.Ici a, F u)‖ = ‖A‖ * ‖∫ u in Set.Ici a, F u‖ := by
    simp
  have hnormI :
      ‖∫ u in Set.Ici a, F u‖ ≤ ∫ u in Set.Ici a, ‖F u‖ := by
    have _ : Integrable F (Measure.restrict volume (Set.Ici a)) := hF
    have h :
        ‖∫ u, F u ∂Measure.restrict volume (Set.Ici a)‖
          ≤ ∫ u, ‖F u‖ ∂Measure.restrict volume (Set.Ici a) :=
      norm_integral_le_integral_norm (μ := Measure.restrict volume (Set.Ici a)) (f := F)
    simpa using h

  have hdom :
      (∫ u in Set.Ici a, ‖F u‖) ≤ ∫ u : ℝ, ‖F u‖ := by
    have hEq :
        (∫ u in Set.Ici a, ‖F u‖) =
          ∫ u : ℝ, Set.indicator (Set.Ici a) (fun u => ‖F u‖) u := by
      have h := (integral_indicator (μ := (volume : Measure ℝ))
        (s := Set.Ici a) (f := fun u => ‖F u‖))
      have h' := h measurableSet_Ici
      simpa using h'.symm
    have hind_int :
        Integrable (Set.indicator (Set.Ici a) (fun u => ‖F u‖)) :=
      hnorm.indicator measurableSet_Ici
    have hpoint :
        Set.indicator (Set.Ici a) (fun u => ‖F u‖)
            ≤ᵐ[volume] (fun u : ℝ => ‖F u‖) := by
      filter_upwards with u
      by_cases hu : u ∈ Set.Ici a
      · simp [Set.indicator_of_mem hu]
      · simp [Set.indicator_of_notMem hu]
    have hmono :=
        integral_mono_ae (μ := (volume : Measure ℝ))
          hind_int hnorm hpoint
    simpa [hEq] using hmono

  calc
    ‖A * (∫ u in Set.Ici a, F u)‖
        = ‖A‖ * ‖∫ u in Set.Ici a, F u‖ := hmul
    _   ≤ ‖A‖ * (∫ u in Set.Ici a, ‖F u‖) :=
      mul_le_mul_of_nonneg_left hnormI (by simp)
    _   ≤ ‖A‖ * (∫ u : ℝ, ‖F u‖) :=
      mul_le_mul_of_nonneg_left hdom (by simp)

lemma fourier_decay_of_CS2
    (ψ : CS 2 ℂ) :
    ∃ C : ℝ, ∀ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  let ψ' : W21 := (ψ : W21)
  obtain ⟨C, hC⟩ :
      ∃ C : ℝ, ∀ u : ℝ, ‖𝓕 (ψ' : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
    simpa using (decay_bounds_cor (ψ := ψ'))
  refine ⟨C, ?_⟩
  intro u
  simpa [ψ'] using (hC u)

lemma integrable_norm_fourier_scaled_of_CS2
    (ψ : CS 2 ℂ) :
    Integrable (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
  obtain ⟨C, hdecay⟩ := fourier_decay_of_CS2 (ψ := ψ)
  have hC_nonneg : 0 ≤ C := by
    have h0 := hdecay 0
    have hnorm : 0 ≤ ‖𝓕 (ψ : ℝ → ℂ) 0‖ := norm_nonneg _
    have hC' : ‖𝓕 (ψ : ℝ → ℂ) 0‖ ≤ C := by simpa using h0
    exact hnorm.trans hC'
  have hmaj_int : Integrable (fun u : ℝ => (C : ℝ) / (1 + (u / (2 * Real.pi))^2)) := by
    have hbase : Integrable (fun u : ℝ => (1 + u ^ 2)⁻¹) := integrable_inv_one_add_sq
    have hscale :
        Integrable (fun u : ℝ => (1 + (u / (2 * Real.pi)) ^ 2)⁻¹) :=
      hbase.comp_div (by nlinarith [Real.pi_pos])
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, pow_two] using
      hscale.const_mul C
  have hle :
      (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖)
        ≤ᵐ[volume]
      (fun u : ℝ => (C : ℝ) / (1 + (u / (2 * Real.pi))^2)) := by
    refine Filter.Eventually.of_forall ?_
    intro u
    simpa using (hdecay (u / (2 * Real.pi)))
  have hle_norm :
      (fun u : ℝ => ‖‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖‖)
        ≤ᵐ[volume]
      (fun u : ℝ => ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖) := by
    refine hle.mono ?_
    intro u hu
    have hden_pos : 0 < 1 + (u / (2 * Real.pi)) ^ 2 := by nlinarith
    have hnonneg : 0 ≤ (C : ℝ) / (1 + (u / (2 * Real.pi))^2) :=
      div_nonneg hC_nonneg hden_pos.le
    have hleft_nonneg : 0 ≤ ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖ := norm_nonneg _
    have hbound : ‖‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖‖ ≤
        (C : ℝ) / (1 + (u / (2 * Real.pi))^2) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg] using hu
    have hC_abs : |C| = C := abs_of_nonneg hC_nonneg
    have hden_abs : |1 + (u / (2 * Real.pi))^2| = 1 + (u / (2 * Real.pi))^2 := by
      have : 0 ≤ 1 + (u / (2 * Real.pi))^2 := by nlinarith
      simpa using abs_of_nonneg this
    have hnorm :
        ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖ =
          (C : ℝ) / (1 + (u / (2 * Real.pi))^2) := by
      have hrec :
          ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖ =
            |C| / |1 + (u / (2 * Real.pi))^2| := by
        simp [Real.norm_eq_abs]
      simp [hC_abs, hden_abs, hrec]
    simpa [hnorm] using hbound
  have hmaj_int_norm :
      Integrable (fun u : ℝ => ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖) :=
    hmaj_int.norm
  have hmeas :
      AEStronglyMeasurable (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
    have hcont : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) u := by
      simpa using continuous_FourierIntegral (ψ : W21)
    have hcont_scaled : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)) :=
      hcont.comp (by continuity)
    exact hcont_scaled.aestronglyMeasurable.norm
  exact hmaj_int_norm.mono' hmeas hle_norm

lemma exists_bound_norm_G_on_tsupport
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (ψ : CS 2 ℂ) :
    ∃ K : ℝ, ∀ t : ℝ, t ∈ tsupport (ψ : ℝ → ℂ) →
      ‖G (1 + t * Complex.I)‖ ≤ K := by
  let s : Set ℝ := tsupport (ψ : ℝ → ℂ)
  have hscompact : IsCompact s := by
    simpa [s] using (ψ.h2.isCompact : IsCompact (tsupport (ψ : ℝ → ℂ)))
  have hphi_cont : Continuous (fun t : ℝ => (1 : ℂ) + t * Complex.I) := by continuity
  have hphi_maps :
      Set.MapsTo (fun t : ℝ => (1 : ℂ) + t * Complex.I) s {z : ℂ | 1 ≤ z.re} := by
    intro t ht
    simp
  have hGcomp : ContinuousOn (fun t : ℝ => G ((1 : ℂ) + t * Complex.I)) s :=
    hG.comp hphi_cont.continuousOn hphi_maps
  have hnorm_contOn : ContinuousOn (fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) s := hGcomp.norm
  have hbdd : BddAbove ((fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) '' s) :=
    (hscompact.image_of_continuousOn hnorm_contOn).bddAbove
  refine ⟨sSup ((fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) '' s), ?_⟩
  intro t ht
  have : ‖G ((1 : ℂ) + t * Complex.I)‖ ∈
      (fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) '' s := ⟨t, ht, rfl⟩
  exact le_csSup hbdd this

lemma norm_integrand_le_K_mul_norm_psi
    {x K : ℝ}
    (hx : 0 < x)
    (hK : ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K) :
    ∀ t : ℝ,
      ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ ≤ K * ‖ψ t‖ := by
  intro t
  by_cases ht : t ∈ Function.support ψ
  · have hxnorm : ‖((x : ℂ) ^ (t * Complex.I))‖ = 1 := norm_x_cpow_it x t hx
    calc
      ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
          = ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ * ‖((x : ℂ) ^ (t * Complex.I))‖ := by
              simp [mul_left_comm, mul_comm]
      _   = ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ * 1 := by simp [hxnorm]
      _   ≤ K * ‖ψ t‖ := by
            have hGle : ‖G (1 + t * Complex.I)‖ ≤ K := hK t ht
            have : ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ ≤ K * ‖ψ t‖ :=
              mul_le_mul_of_nonneg_right hGle (norm_nonneg _)
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
  · have hψ0 : ψ t = 0 := by
      by_contra hψ0
      exact ht (by simpa [Function.support] using hψ0)
    simp [hψ0, mul_comm]

lemma norm_error_integral_le
    (ψ : ℝ → ℂ) (x K : ℝ)
    (hGline_meas : Measurable (fun t : ℝ => G (1 + t * I)))
    (hψ_meas : AEStronglyMeasurable ψ)
    (hx : 0 < x)
    (hK : ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K)
    (hψ : Integrable (fun t : ℝ => ‖ψ t‖) ) :
    ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
      ≤ K * (∫ t : ℝ, ‖ψ t‖) := by
  have h1 : ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
        ≤ ∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ := by
    simpa using (norm_integral_le_integral_norm
        (f := fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))))
  have hmeas_main : AEStronglyMeasurable
        (fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))) := by
    have hG' : AEMeasurable fun t : ℝ => G (1 + t * Complex.I) := hGline_meas.aemeasurable
    have hψ_meas' : AEMeasurable ψ := hψ_meas.aemeasurable
    have hx_ne : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    have hx_ne' : NeZero (x : ℂ) := ⟨hx_ne⟩
    have hxpow_meas : AEMeasurable fun t : ℝ => ((x : ℂ) ^ (t * Complex.I)) := by
      have hcontℂ : Continuous fun z : ℂ => ((x : ℂ) ^ z) :=
        continuous_const_cpow (z := (x : ℂ))
      have hcont : Continuous fun t : ℝ => ((x : ℂ) ^ ((t : ℂ) * Complex.I)) :=
        hcontℂ.comp (by
          have h : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by
            exact (continuous_ofReal.mul continuous_const).congr fun t => rfl
          simpa [mul_comm] using h)
      exact hcont.measurable.aemeasurable
    have hGψ_meas : AEMeasurable fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) := hG'.mul hψ_meas'
    have htotal : AEMeasurable (fun t : ℝ =>
            (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))) :=
      hGψ_meas.mul hxpow_meas
    exact htotal.aestronglyMeasurable
  have hpt : (fun t : ℝ =>
          ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖)
        ≤ᵐ[volume] (fun t : ℝ => K * ‖ψ t‖) := by
    refine Eventually.of_forall ?_
    intro t
    exact norm_integrand_le_K_mul_norm_psi (hx := hx) (hK := hK) t
  have hR : Integrable (fun t : ℝ => K * ‖ψ t‖) := hψ.const_mul K
  have hL : Integrable (fun t : ℝ =>
        ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖) := by
      have hpt_norm :
          (fun t : ℝ => ‖‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖‖)
            ≤ᵐ[volume] (fun t : ℝ => K * ‖ψ t‖) := hpt.mono (by
          intro t ht
          simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using ht)
      exact hR.mono' hmeas_main.norm hpt_norm
  have h2 : (∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖)
        ≤ ∫ t : ℝ, K * ‖ψ t‖ := integral_mono_ae (μ := (volume : Measure ℝ)) hL hR hpt
  have h3 : (∫ t : ℝ, K * ‖ψ t‖) = K * (∫ t : ℝ, ‖ψ t‖) := by
    simp [integral_const_mul]
  calc
    ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
        ≤ ∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ := h1
    _   ≤ ∫ t : ℝ, K * ‖ψ t‖ := h2
    _   = K * (∫ t : ℝ, ‖ψ t‖) := h3

lemma crude_upper_bound
    (hpos : 0 ≤ f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (ψ : CS 2 ℂ)
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0) :
    ∃ B : ℝ, ∀ x : ℝ, 0 < x → ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤ B := by

  -- Integrability of ψ
  have hψ_int : MeasureTheory.Integrable (ψ : ℝ → ℂ) := by
    simpa using (ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2)
  have hψ_norm_int : MeasureTheory.Integrable (fun t : ℝ => ‖(ψ : ℝ → ℂ) t‖) :=
    hψ_int.norm
  have hψ_meas : MeasureTheory.AEStronglyMeasurable (ψ : ℝ → ℂ) :=
    hψ_int.aestronglyMeasurable

  -- Uniform bound K for ‖G(1+it)‖ on support ψ
  rcases exists_bound_norm_G_on_tsupport (G := G) hG ψ with ⟨K, hK_ts⟩
  have hK_support :
      ∀ t : ℝ, t ∈ Function.support (ψ : ℝ → ℂ) → ‖G (1 + t * Complex.I)‖ ≤ K := by
    have hbnG (hKts : ∀ t : ℝ, t ∈ tsupport ψ → ‖G (1 + t * Complex.I)‖ ≤ K) :
      ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K := by
      intro t ht
      exact hKts t ((subset_tsupport ψ) ht)
    exact hbnG hK_ts

  -- Measurability of the line restriction t ↦ G(1 + t I) from continuity-on
  have hGline_meas : Measurable (fun t : ℝ => G (1 + t * Complex.I)) := by
    have hline_cont : Continuous (fun t : ℝ => (1 : ℂ) + t * Complex.I) := by
      continuity
    have hmem : ∀ t : ℝ, ((1 : ℂ) + t * Complex.I) ∈ {s : ℂ | 1 ≤ s.re} := by
      intro t
      simp
    have hcont : Continuous (G ∘ fun t : ℝ => (1 : ℂ) + t * Complex.I) :=
      hG.comp_continuous hline_cont hmem
    simpa [Function.comp_def] using hcont.measurable

  -- L¹ bound for the scaled Fourier transform norm
  have hF_norm_int :
      MeasureTheory.Integrable (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) :=
    integrable_norm_fourier_scaled_of_CS2 ψ
  have hF_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))) := by
    have hcont : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) u := by
      simpa using continuous_FourierIntegral (ψ : W21)
    have hcont_scaled : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)) :=
      hcont.comp (by continuity)
    exact hcont_scaled.aestronglyMeasurable
  have hF_int :
      MeasureTheory.Integrable (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))) :=
    by
      have hfin_norm :
          MeasureTheory.HasFiniteIntegral
            (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) :=
        hF_norm_int.hasFiniteIntegral
      have hfin :
          MeasureTheory.HasFiniteIntegral
            (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))) := by
        simpa [MeasureTheory.hasFiniteIntegral_iff_norm] using hfin_norm
      exact ⟨hF_meas, hfin⟩
  refine ⟨K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖)
            + ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖), ?_⟩
  intro x hx
  set I : ℂ := ∫ u in Set.Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)) with hI

  -- Lemma 12
  have hlim :=
    limiting_fourier_variant (f := f) (A := A) (G := G)
      hpos hG hG' hf ψ hψpos hx
  have hlim' :
      (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log (n / x)))
        - A * I
      = ∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I) := by
    simpa [hI] using hlim

  -- express the tsum as RHS + A*I
  have htsum :
      (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log (n / x)))
      = (∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I := by
    have h' :
        (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log (n / x)))
          = (∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I :=
      eq_add_of_sub_eq hlim'
    simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using h'

  -- bound the RHS integral
  have hRHS_bound :
      ‖∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)‖
        ≤ K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖) :=
    norm_error_integral_le (G := G) (ψ := (ψ : ℝ → ℂ)) (x := x) (K := K)
      hGline_meas hψ_meas hx hK_support hψ_norm_int

  -- bound the A * I term
  have hA_bound :
      ‖A * I‖ ≤ ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
    have hF_on : MeasureTheory.IntegrableOn
        (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)))
        (Set.Ici (-Real.log x)) :=
      hF_int.integrableOn
    simpa [hI] using
      norm_mul_integral_Ici_le_integral_norm (A := A)
        (F := fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)))
        (a := -Real.log x) hF_on hF_norm_int

  -- combine bounds
  have htsum_std :
      (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x)))
        = (∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I := by
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using htsum

  -- bound in the normalized form
  have hbound :
      ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ)
          (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖
        ≤ K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖)
          + ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
    have hnorm :
        ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ)
            (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖ =
          ‖(∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I‖ :=
      congrArg norm htsum_std
    calc
      ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ)
          (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖
          = ‖(∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I‖ := hnorm
      _ ≤ ‖∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)‖ + ‖A * I‖ :=
            norm_add_le _ _
      _ ≤ K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖)
          + ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) :=
            add_le_add hRHS_bound hA_bound
  exact hbound

set_option backward.isDefEq.respectTransparency false in
private lemma _root_.Real.fourierIntegral_convolution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume) = 𝓕 f * 𝓕 g := by
  ext y
  simp only [Pi.mul_apply, FourierTransform.fourier, MeasureTheory.convolution,
    VectorFourier.fourierIntegral, ContinuousLinearMap.mul_apply']
  have h_int : Integrable (fun p : ℝ × ℝ ↦ 𝐞 (-(y * p.1)) • (f p.2 * g (p.1 - p.2))) := by
    simp only [Circle.smul_def, smul_eq_mul]
    refine (Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hf hg).bdd_mul
      (c := 1) ?_ ?_
    · exact (by continuity : Continuous _).aestronglyMeasurable
    · filter_upwards with p; simp
  calc ∫ v, 𝐞 (-(y * v)) • ∫ t, f t * g (v - t)
      = ∫ v, ∫ t, 𝐞 (-(y * v)) • (f t * g (v - t)) := by
        simp only [Circle.smul_def, smul_eq_mul, ← integral_const_mul]
    _ = ∫ t, ∫ v, 𝐞 (-(y * v)) • (f t * g (v - t)) := integral_integral_swap h_int
    _ = ∫ t, f t • ∫ v, 𝐞 (-(y * v)) • g (v - t) := by
        simp only [Circle.smul_def, smul_eq_mul, mul_left_comm, integral_const_mul]
    _ = ∫ t, f t • ∫ u, 𝐞 (-(y * (u + t))) • g u := by
        congr 1; ext t
        rw [← integral_add_right_eq_self (fun v ↦ 𝐞 (-(y * v)) • g (v - t)) t]; simp
    _ = ∫ t, f t • ∫ u, (𝐞 (-(y * t)) * 𝐞 (-(y * u))) • g u := by
        congr 2 with t; congr 1
        simp only [mul_add, neg_add, mul_comm, Real.fourierChar.map_add_eq_mul]
    _ = ∫ t, 𝐞 (-(y * t)) • f t • ∫ u, 𝐞 (-(y * u)) • g u := by
        congr 1; ext t
        simp only [mul_smul, Circle.smul_def, smul_eq_mul, integral_const_mul]; ring
    _ = (∫ t, 𝐞 (-(y * t)) • f t) * ∫ u, 𝐞 (-(y * u)) • g u := by
        simp only [Circle.smul_def, smul_eq_mul, ← mul_assoc, integral_mul_const]

private lemma _root_.Real.fourierIntegral_conj_neg {f : ℝ → ℂ} (y : ℝ) :
    𝓕 (fun x ↦ conj (f (-x))) y = conj (𝓕 f y) := by
  simp only [fourier_real_eq]
  have h_conj : ∀ x, 𝐞 (-(x * y)) • conj (f (-x)) = conj (𝐞 (x * y) • f (-x)) := fun x ↦ by
    simp only [Circle.smul_def, Real.fourierChar_apply, map_mul, smul_eq_mul, neg_mul,
      Complex.ofReal_neg, mul_neg]
    congr 1
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, mul_neg]
  calc ∫ x, 𝐞 (-(x * y)) • conj (f (-x))
      = ∫ x, conj (𝐞 (x * y) • f (-x)) := by congr 1; ext x; exact h_conj x
    _ = conj (∫ x, 𝐞 (x * y) • f (-x)) := integral_conj
    _ = conj (∫ x, 𝐞 (-(x * y)) • f x) := by
        rw [← integral_neg_eq_self (fun x => 𝐞 (-(x * y)) • f x)]
        congr 2 with x; ring_nf

/-- Smooth compactly supported function with non-negative Fourier transform via self-convolution. -/
lemma auto_cheby_exists_smooth_nonneg_fourier_kernel :
    ∃ (ψ : ℝ → ℂ), ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
    (∀ y, 0 ≤ (𝓕 ψ y).re ∧ (𝓕 ψ y).im = 0) ∧ 0 < (𝓕 ψ 0).re := by
  obtain ⟨φ_real, hφSmooth, hφCompact, hφIcc, _, hφsupp⟩ :=
    smooth_urysohn_support_Ioo (a := 1/2) (b := 1) (c := 1) (d := 2) (by norm_num) (by norm_num)
  let φ : ℝ → ℂ := Complex.ofReal ∘ φ_real
  let φ_rev : ℝ → ℂ := fun x ↦ conj (φ (-x))
  let ψ_fun : ℝ → ℂ := convolution φ φ_rev (ContinuousLinearMap.mul ℝ ℂ) volume
  have hφSmooth' : ContDiff ℝ ∞ φ := contDiff_ofReal.comp hφSmooth
  have hφCompact' : HasCompactSupport φ := hφCompact.comp_left rfl
  have hφRevSmooth : ContDiff ℝ ∞ φ_rev := Complex.conjCLE.contDiff.comp (hφSmooth'.comp contDiff_neg)
  have hφRevCompact : HasCompactSupport φ_rev := (hφCompact'.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (by simp)
  have hφInt : Integrable φ := hφSmooth'.continuous.integrable_of_hasCompactSupport hφCompact'
  have hφRevInt : Integrable φ_rev := hφRevSmooth.continuous.integrable_of_hasCompactSupport hφRevCompact
  have hψSmooth : ContDiff ℝ ∞ ψ_fun := by
    convert hφRevCompact.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      (hφSmooth'.continuous.locallyIntegrable (μ := volume)) hφRevSmooth
  have hψCompact : HasCompactSupport ψ_fun :=
    HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℂ) hφCompact' hφRevCompact
  refine ⟨ψ_fun, hψSmooth, hψCompact, fun y ↦ ?_, ?_⟩
  · rw [Real.fourierIntegral_convolution hφInt hφRevInt, Pi.mul_apply,
      Real.fourierIntegral_conj_neg y, mul_comm, ← Complex.normSq_eq_conj_mul_self]
    exact ⟨Complex.normSq_nonneg _, rfl⟩
  · have hφ_nonneg : ∀ x, 0 ≤ φ_real x := fun x ↦ by
      have hx := hφIcc x; by_cases h : x ∈ Set.Icc (1:ℝ) 1
      · simp only [Set.indicator_of_mem h, Pi.one_apply] at hx; linarith
      · simp only [Set.indicator_of_notMem h] at hx; exact hx
    have hvol_supp : (1 : ENNReal) ≤ volume (Function.support φ_real) := by
      have hsub : Set.Ico (1:ℝ) 2 ⊆ Function.support φ_real := fun x hx ↦
        hφsupp.symm ▸ Set.mem_Ioo.mpr ⟨by linarith [hx.1], hx.2⟩
      calc _ = volume (Set.Ico (1:ℝ) 2) := by simp [Real.volume_Ico]; norm_num
           _ ≤ _ := volume.mono hsub
    have hφint_pos : 0 < ∫ x, φ_real x :=
      (integral_pos_iff_support_of_nonneg_ae (.of_forall hφ_nonneg)
        (hφSmooth.continuous.integrable_of_hasCompactSupport hφCompact)).2
        (lt_of_lt_of_le (by simp) hvol_supp)
    have hFφ0_re : 0 < (𝓕 φ 0).re := by
      simp only [φ, fourier_real_eq, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul,
        Function.comp_apply]
      have hint : Integrable (fun x => (φ_real x : ℂ)) :=
        (hφSmooth.continuous.integrable_of_hasCompactSupport hφCompact).ofReal
      calc (∫ x, (φ_real x : ℂ)).re = ∫ x, (φ_real x : ℂ).re := (integral_re hint).symm
        _ = ∫ x, φ_real x := by simp only [Complex.ofReal_re]
        _ > 0 := hφint_pos
    rw [Real.fourierIntegral_convolution hφInt hφRevInt, Pi.mul_apply,
      Real.fourierIntegral_conj_neg 0, mul_comm, ← Complex.normSq_eq_conj_mul_self]
    exact Complex.normSq_pos.2 (fun h ↦ (ne_of_gt hFφ0_re) (by simp [h]))

/-- The series `∑ f(n)/n · 𝓕ψ(log(n/x)/(2π))` is summable for `x ≥ 1`. -/
lemma auto_cheby_fourier_summable (hpos : 0 ≤ f) (hf : ∀ σ', 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (ψ : ℝ → ℂ) (hψSmooth : ContDiff ℝ ∞ ψ) (hψCompact : HasCompactSupport ψ)
    (hψpos : ∀ y, 0 ≤ (𝓕 ψ y).re ∧ (𝓕 ψ y).im = 0) (x : ℝ) (hx : 1 ≤ x) :
    Summable fun n ↦ (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x)) := by
  let ψCS : CS 2 ℂ := ⟨ψ, hψSmooth.of_le (by norm_cast), hψCompact⟩
  let S : ℝ → ℂ := fun σ' ↦ ∑' n, term (f · : ℕ → ℂ) σ' n * 𝓕 ψCS.toFun (1 / (2 * π) * Real.log (n / x))
  let Pole : ℝ → ℂ := fun σ' ↦ (A : ℂ) * (x ^ (1 - σ') : ℝ) *
    ∫ u in Set.Ici (-Real.log x), (rexp (-u * (σ' - 1)) : ℂ) * 𝓕 (W21.ofCS2 ψCS).toFun (u / (2 * π))
  let RHS : ℝ → ℂ := fun σ' ↦ ∫ t : ℝ, G (σ' + t * I) * ψCS.toFun t * (x : ℂ) ^ (t * I)
  have l2 := limiting_fourier_lim2 (A := A) (x := x) ψCS hx
  have l3 := limiting_fourier_lim3 (G := G) hG ψCS hx
  have haux : (fun σ' ↦ S σ' - Pole σ') =ᶠ[𝓝[>] 1] RHS := eventually_nhdsWithin_of_forall fun σ' hσ' ↦ by
    simpa [S, Pole, RHS] using limiting_fourier_aux hG' hf ψCS hx σ' hσ'
  have hS_tendsto : Tendsto S (𝓝[>] 1) (𝓝 (RHS 1 + A * ∫ u in Set.Ici (-Real.log x),
      𝓕 (W21.ofCS2 ψCS).toFun (u / (2 * π)))) := by
    have hS_decomp :
        (fun σ' : ℝ => (S σ' - Pole σ') + Pole σ') =ᶠ[𝓝[>] 1] S := by
      exact Eventually.of_forall fun σ' => by simp
    simpa [Pole, RHS] using ((l3.congr' haux.symm).add l2).congr' hS_decomp
  have hbounded : BoundedAtFilter (𝓝[>] 1) (fun σ' ↦ ‖S σ'‖) := by
    simp only [BoundedAtFilter]
    let L := ‖RHS 1 + A * ∫ u in Set.Ici (-Real.log x), 𝓕 (W21.ofCS2 ψCS).toFun (u / (2 * π))‖
    have : ∀ᶠ σ' in 𝓝[>] 1, ‖S σ'‖ < L + 1 :=
      hS_tendsto.norm.eventually_lt tendsto_const_nhds (lt_add_one L)
    exact Asymptotics.IsBigO.of_bound (L + 1) (by filter_upwards [this] with σ h; simpa using h.le)
  let y : ℕ → ℝ := fun n ↦ (1 / (2 * π)) * Real.log (n / x)
  let w : ℕ → ℝ := fun n ↦ (𝓕 ψCS.toFun (y n)).re
  have hw : ∀ n, 0 ≤ w n := fun n ↦ (hψpos (y n)).1
  let rt : ℝ → ℕ → ℝ := fun σ n ↦ if n = 0 then 0 else f n / (n : ℝ) ^ σ * w n
  have rt_nn σ n : 0 ≤ rt σ n := by
    simp only [rt]; split_ifs with hn
    · rfl
    · exact mul_nonneg (div_nonneg (hpos n) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero hn)) σ).le) (hw n)
  have hS_eq σ' (hσ' : 1 < σ') : S σ' = ↑(∑' n, rt σ' n) := by
    rw [Complex.ofReal_tsum]; apply tsum_congr; intro n
    simp only [rt, term, LSeries.term, y, w, one_div, mul_inv_rev]
    split_ifs with hn <;> simp only [hn, CharP.cast_eq_zero, Complex.ofReal_zero, zero_mul,
      Complex.ofReal_mul, Complex.ofReal_div]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; congr 1
    exact Complex.ext rfl (hψpos _).2
  have hMono n : AntitoneOn (fun σ ↦ rt σ n) (Set.Ioi 1) := fun σ₁ _ σ₂ _ h ↦ by
    simp only [rt]; split_ifs with hn; · rfl
    apply mul_le_mul_of_nonneg_right _ (hw n)
    apply div_le_div_of_nonneg_left (hpos n) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero hn)) σ₁)
    exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)) h
  have hT_bdd : BoundedAtFilter (𝓝[>] 1) fun σ ↦ ∑' n, rt σ n := by
    rw [BoundedAtFilter, Asymptotics.isBigO_iff] at hbounded ⊢
    obtain ⟨C, hC⟩ := hbounded
    refine ⟨C, ?_⟩
    filter_upwards [hC, self_mem_nhdsWithin] with σ hnorm hσ
    rw [hS_eq σ hσ] at hnorm; simpa using hnorm
  have hSumm σ (hσ : 1 < σ) : Summable (rt σ ·) := by
    simpa [rt, w, y] using limiting_fourier_variant_lim1_aux ψCS hpos hf hψpos σ hσ
  have hSumm_1 : Summable (rt 1 ·) := by
    let σ_seq : ℕ → ℝ := fun k ↦ 1 + 1 / ((k : ℝ) + 1)
    have hσ_gt k : 1 < σ_seq k := by simp only [σ_seq, lt_add_iff_pos_right, one_div]; positivity
    have h_tendsto : Tendsto σ_seq atTop (𝓝[>] 1) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, by filter_upwards with k; exact hσ_gt k⟩
      have : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
        simp only [one_div]; exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).inv_tendsto_atTop
      simpa [σ_seq] using tendsto_const_nhds.add this
    have h_ptwise n : Tendsto (fun k ↦ rt (σ_seq k) n) atTop (𝓝 (rt 1 n)) := by
      simp only [rt]; split_ifs with hn; · exact tendsto_const_nhds
      refine ((tendsto_const_nhds.rpow (tendsto_nhdsWithin_iff.mp h_tendsto).1 (Or.inl ?_)).inv₀
        (by simp [hn])).const_mul (f n) |>.mul_const (w n)
      exact (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp (hT_bdd.comp_tendsto h_tendsto)
    refine summable_of_sum_range_le (c := C) (rt_nn 1) fun m ↦ le_of_tendsto (tendsto_finsetSum _
        fun i _ ↦ h_ptwise i) ?_
    filter_upwards [h_tendsto.eventually self_mem_nhdsWithin, hC] with k hk hCk
    calc ∑ i ∈ Finset.range m, rt (σ_seq k) i
        ≤ ∑' n, rt (σ_seq k) n := (hSumm _ hk).sum_le_tsum _ fun n _ ↦ rt_nn _ n
      _ ≤ |∑' n, rt (σ_seq k) n| := le_abs_self _
      _ ≤ C := by simpa using hCk
  rw [show (fun n ↦ (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x))) =
      Complex.ofRealCLM ∘ (rt 1 ·) from ?_]
  · exact hSumm_1.map Complex.ofRealCLM Complex.ofRealCLM.continuous
  ext n; simp only [rt, Real.rpow_one, one_div, w, y, Function.comp_apply]
  split_ifs with hn; · simp [hn]
  have him0 : (𝓕 ψCS.toFun ((2 * π)⁻¹ * Real.log (n / x))).im = 0 := (hψpos _).2
  have hre_eq : 𝓕 ψCS.toFun ((2 * π)⁻¹ * Real.log (n / x)) =
      Complex.ofReal ((𝓕 ψCS.toFun ((2 * π)⁻¹ * Real.log (n / x))).re) := by
    rw [← Complex.re_add_im (𝓕 ψCS.toFun _), him0]; simp
  conv_lhs => rw [show ψ = ψCS.toFun from rfl, hre_eq]
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast]

/-- Short interval bound from global filtered bound: if `∑ f(n)/n · 𝓕ψ(log(n/x)) ≤ B`,
then `∑_{(1-ε)x < n ≤ x} f(n) ≤ Cx` for some `ε, C > 0`. -/
lemma auto_cheby_short_interval_bound (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (B : ℝ) (ψ : ℝ → ℂ) (hψSmooth : ContDiff ℝ ∞ ψ) (hψCompact : HasCompactSupport ψ)
    (hψpos : ∀ y, 0 ≤ (𝓕 ψ y).re ∧ (𝓕 ψ y).im = 0) (hψ0 : 0 < (𝓕 ψ 0).re)
    (hB_bound : ∀ x ≥ 1, ‖∑' n, f n / n * 𝓕 ψ (1 / (2 * Real.pi) * Real.log (n / x))‖ ≤ B) :
    ∃ (ε : ℝ) (C : ℝ), ε > 0 ∧ ε < 1 ∧ C > 0 ∧ ∀ x ≥ 1,
      ∑' n, (f n) * (Set.indicator (Set.Ioc ((1 - ε) * x) x) (fun _ ↦ 1) (n : ℝ)) ≤ C * x := by
  have hF : Continuous (𝓕 ψ) := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by continuity) (hψSmooth.continuous.integrable_of_hasCompactSupport hψCompact)
  have hg : Continuous fun y ↦ (𝓕 ψ y).re := Complex.continuous_re.comp hF
  obtain ⟨δ, hδpos, hball⟩ := Metric.mem_nhds_iff.1 <|
    hg.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Ioi (half_lt_self hψ0))
  let c := (𝓕 ψ 0).re / 2
  have hcpos : 0 < c := by dsimp only [c]; linarith
  have h_psi_ge_c : ∀ y, |y| < δ → c ≤ (𝓕 ψ y).re := fun y hy ↦ (hball (mem_ball_zero_iff.mpr hy)).le
  let ε := 1 - Real.exp (-2 * π * δ)
  have hε : 0 < ε ∧ ε < 1 := by
    have h1 : Real.exp (-2 * π * δ) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    exact ⟨by simp only [ε]; linarith, by simp only [ε]; linarith [Real.exp_pos (-2 * π * δ)]⟩
  have hB_nonneg : 0 ≤ B := (norm_nonneg _).trans (hB_bound 1 le_rfl)
  refine ⟨ε, B / c + 1, hε.1, hε.2, by positivity, fun x hx ↦ ?_⟩
  have h_summable : Summable fun n ↦ (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x)) :=
    auto_cheby_fourier_summable hpos hf hG hG' ψ hψSmooth hψCompact hψpos x hx
  have hx_pos : 0 < x := by linarith
  have h_sum_lower : c / x * ∑' n, f n * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (n : ℝ)
      ≤ ∑' n, f n / n * (𝓕 ψ (1 / (2 * π) * Real.log (n / x))).re := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n ↦ ?_) ?_ ?_
    · by_cases hn : (n : ℝ) ∈ Set.Ioc ((1 - ε) * x) x
      · rw [Set.indicator_of_mem hn, Pi.one_apply, mul_one]
        have hn_pos : 0 < (n : ℝ) := by nlinarith [hn.1, hε.2]
        let y := (1 / (2 * π)) * Real.log (n / x)
        have h_arg_small : |y| < δ := by
          have h2pi : 0 < 2 * π := by linarith [Real.pi_pos]
          simp only [y, abs_mul, abs_div, abs_one, abs_of_pos h2pi]
          field_simp [ne_of_gt h2pi]; rw [mul_comm, abs_lt]
          have h_log_lower : -2 * π * δ < Real.log (n / x) := by
            rw [← Real.log_exp (-2 * π * δ), Real.log_lt_log_iff (Real.exp_pos _) (by positivity)]
            have : Real.exp (-2 * π * δ) = 1 - ε := by simp only [ε]; ring
            rw [this]; field_simp; exact hn.1
          have h_log_upper : Real.log (n / x) ≤ 0 :=
            Real.log_nonpos (by positivity) (div_le_one_of_le₀ hn.2 hx_pos.le)
          constructor <;> nlinarith [Real.pi_pos]
        have h1 : x⁻¹ ≤ (n : ℝ)⁻¹ := by rw [inv_le_inv₀ hx_pos hn_pos]; exact hn.2
        have h2 : c ≤ (𝓕 ψ y).re := h_psi_ge_c y h_arg_small
        have hfn : 0 ≤ f n := hpos n
        have hre : 0 ≤ (𝓕 ψ y).re := (hψpos y).1
        have hn_inv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn_pos.le
        calc c / x * f n = c * x⁻¹ * f n := by rw [div_eq_mul_inv]
          _ ≤ c * (n : ℝ)⁻¹ * f n := by gcongr
          _ ≤ (𝓕 ψ y).re * (n : ℝ)⁻¹ * f n := by gcongr
          _ = (n : ℝ)⁻¹ * (𝓕 ψ y).re * f n := by ring
          _ = f n / n * (𝓕 ψ y).re := by ring
      · rw [Set.indicator_of_notMem hn, mul_zero, mul_zero]
        exact mul_nonneg (div_nonneg (hpos n) (Nat.cast_nonneg n)) (hψpos _).1
    · refine summable_of_hasFiniteSupport <| (Set.finite_le_nat ⌊x⌋₊).subset fun n hn ↦ ?_
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Set.indicator_apply_ne_zero] at hn
      exact Nat.le_floor hn.2.2.1.2
    · rw [← Complex.summable_ofReal]; convert h_summable using 1; ext n
      rw [Complex.ofReal_mul, Complex.ofReal_div]
      norm_cast
      rw [Complex.ofReal_mul]
      congr 1
      apply Complex.ext
      · simp only [Complex.ofReal_re]
      · simp only [Complex.ofReal_im]; exact (hψpos _).2.symm
  have h_real_eq : ∑' n, f n / n * (𝓕 ψ (1 / (2 * π) * Real.log (n / x))).re =
      (∑' n, (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x))).re := by
    rw [Complex.re_tsum h_summable]; congr with n
    rw [Complex.mul_re]; norm_cast; simp only [zero_mul, sub_zero]
  calc ∑' n, f n * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (n : ℝ)
      = x / c * (c / x * ∑' n, f n * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (n : ℝ)) := by
        field_simp [ne_of_gt hcpos, ne_of_gt hx_pos]
    _ ≤ x / c * B := by
        gcongr; rw [h_real_eq] at h_sum_lower
        exact h_sum_lower.trans ((Complex.re_le_norm _).trans (hB_bound x hx))
    _ = (B / c) * x := by field_simp [ne_of_gt hcpos]
    _ ≤ (B / c + 1) * x := by nlinarith

/-- Bootstraps short interval bounds to global Chebyshev bound via strong induction.
If `∑_{(1-ε)x < n ≤ x} f(n) ≤ Cx` for all `x ≥ 1`, then `∑_{n ≤ x} f(n) = O(x)`. -/
lemma auto_cheby_bootstrap_induction (hpos : 0 ≤ f)
    (h_short : ∃ (ε : ℝ) (C : ℝ), ε > 0 ∧ ε < 1 ∧ C > 0 ∧ ∀ x ≥ 1,
      ∑' n, (f n) * (Set.indicator (Set.Ioc ((1 - ε) * x) x) (fun _ ↦ 1) (n : ℝ)) ≤ C * x) :
    cheby f := by
  obtain ⟨ε, C₀, hε, hε1, hC₀, h_bound⟩ := h_short
  let C := C₀ / ε + f 0 + 1
  have hf0 : (0 : ℝ) ≤ f 0 := hpos 0
  have hdiv : 0 ≤ C₀ / ε := div_nonneg hC₀.le hε.le
  have hC : 0 ≤ C := by linarith
  refine ⟨C, fun n ↦ ?_⟩
  induction n using Nat.strong_induction_on with | h n ih =>
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp [cumsum]
    · simp only [cumsum, Finset.sum_range_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf0,
        Nat.cast_one, mul_one, C]
      linarith
  let x := (n : ℝ) - 1
  have hx : x ≥ 1 := by simp only [x, ge_iff_le, le_sub_iff_add_le]; norm_cast
  let m := ⌊(1 - ε) * x⌋₊ + 1
  have hm_lt : m < n := by
    simp only [m, x]
    have h1 : (1 - ε) * (n - 1 : ℝ) < (n - 1 : ℕ) := by
      calc (1 - ε) * (↑n - 1) < 1 * (↑n - 1) := by gcongr; linarith
        _ = ↑n - 1 := by ring
        _ = ↑(n - 1) := by simp [Nat.cast_sub (by omega : 1 ≤ n)]
    have h2 : ⌊(1 - ε) * (n - 1 : ℝ)⌋₊ < n - 1 :=
      (Nat.floor_lt (mul_nonneg (by linarith) (by linarith : (0 : ℝ) ≤ n - 1))).mpr h1
    omega
  have hm_gt : (m : ℝ) > (1 - ε) * x := by
    simp only [m, Nat.cast_add, Nat.cast_one, gt_iff_lt]
    exact Nat.lt_floor_add_one ((1 - ε) * x)
  have h_decomp : cumsum (fun k ↦ ‖(f k : ℂ)‖) n = cumsum (fun k ↦ ‖(f k : ℂ)‖) m + ∑ k ∈ Finset.Ico m n, f k := by
    simp only [cumsum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos _),
      Finset.sum_range_add_sum_Ico _ (by omega : m ≤ n)]
  have h_Ico : ∑ k ∈ Finset.Ico m n, f k ≤ C₀ * x := by
    calc ∑ k ∈ Finset.Ico m n, f k
        = ∑ k ∈ Finset.Ico m n, f k * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (k : ℝ) := by
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          have ⟨hkm, hkn⟩ := Finset.mem_Ico.mp hk
          have hk_gt : (k : ℝ) > (1 - ε) * x := by linarith [hm_gt, (Nat.cast_le (α := ℝ)).mpr hkm]
          have hk_le : (k : ℝ) ≤ x := by
            have h1 : k ≤ n - 1 := Nat.le_pred_of_lt hkn
            have h2 : (k : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast h1
            simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, x] at h2 ⊢; exact h2
          simp only [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hk_gt, hk_le⟩), Pi.one_apply, mul_one]
      _ ≤ ∑' k, f k * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (k : ℝ) := by
          refine Summable.sum_le_tsum _ (fun k _ ↦ mul_nonneg (hpos k) (Set.indicator_nonneg (by simp) _)) ?_
          refine summable_of_hasFiniteSupport <| (Set.finite_le_nat ⌊x⌋₊).subset fun k hk ↦ ?_
          simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Set.indicator_apply_ne_zero] at hk
          exact Nat.le_floor hk.2.1.2
      _ ≤ C₀ * x := h_bound x hx
  have hm_le : (m : ℝ) ≤ (1 - ε) * x + 1 := by
    have hpos' : 0 ≤ (1 - ε) * x := mul_nonneg (by linarith) (by linarith : (0 : ℝ) ≤ x)
    simp only [m, Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le hpos']
  have hnorm : ∀ k, ‖(f k : ℂ)‖ = f k := fun k ↦ by simp [abs_of_nonneg (hpos k)]
  simp only [hnorm] at h_decomp ih ⊢
  calc cumsum f n = cumsum f m + ∑ k ∈ Finset.Ico m n, f k := h_decomp
    _ ≤ C * m + C₀ * x := by linarith [ih m hm_lt, h_Ico]
    _ ≤ C * ((1 - ε) * x + 1) + C₀ * x := by nlinarith [hC]
    _ = (C * (1 - ε) + C₀) * x + C := by ring
    _ ≤ C * x + C := by
        have : C₀ ≤ C * ε := by
          calc C₀ = (C₀ / ε) * ε := by field_simp [ne_of_gt hε]
            _ ≤ (C₀ / ε + f 0 + 1) * ε := by gcongr; linarith [hpos 0]
            _ = C * ε := by simp only [C]
        nlinarith [hε, hε1, hx]
    _ ≤ C * n := by simp only [x]; ring_nf; linarith [hC]

lemma auto_cheby (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) : cheby f := by
  obtain ⟨ψ_fun, hψSmooth, hψCompact, hψpos, hψ0⟩ := auto_cheby_exists_smooth_nonneg_fourier_kernel
  obtain ⟨B, hB⟩ := crude_upper_bound hpos hG hG' hf ⟨ψ_fun, hψSmooth.of_le ENat.LEInfty.out, hψCompact⟩ hψpos
  exact auto_cheby_bootstrap_induction hpos <| auto_cheby_short_interval_bound hpos hf hG hG' B ψ_fun
    hψSmooth hψCompact hψpos hψ0 fun x hx ↦ hB x (by linarith)

end auto_cheby

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Consequences.lean` -/

section
set_option lang.lemmaCmd true

open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

lemma th43_b (x : ℝ) (hx : 2 ≤ x) :
    Nat.primeCounting ⌊x⌋₊ =
      θ x / log x + ∫ t in Set.Icc 2 x, θ t / (t * (Real.log t) ^ 2) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx

/-- If u ~ v and u-w = o(v) then w ~ v. -/
private theorem _root_.Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact Asymptotics.IsEquivalent.sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp only [rpow_one] at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · change Tendsto (fun x : ℝ => (∑ n ∈ Icc 0 ⌊x⌋₊, Λ n) / (⌊x⌋₊ : ℝ))
          atTop (nhds 1)
        simpa [Function.comp_def, Finset.Iic_eq_Icc] using
          Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_ofPred_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'

/-- `√x · log x = o(x)` as `x → ∞`. -/
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2
      · rfl
      · rfl
      · rw [← sqrt_eq_rpow, div_sqrt, sqrt_eq_rpow]
  exact this

theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · convert isLittleO_sqrt_mul_log.const_mul_left 2 using 1
    · rfl
    · rfl
    · ext x
      ring
    · ext x
      rfl

theorem chebyshev_asymptotic' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun t ↦ ε * t)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ (x : ℝ), θ x = x + f x := by
  have H := chebyshev_asymptotic
  rw [IsEquivalent, isLittleO_iff] at H
  let f := (fun x ↦ θ x - x)
  have integrable (x : ℝ) (hx : 2 ≤ x) : IntegrableOn f (Set.Icc 2 x) := by
    rw [IntegrableOn]
    refine Integrable.sub ?_ (ContinuousOn.integrableOn_Icc (continuousOn_id' _))
    refine Chebyshev.integrableOn_theta_div_id_mul_log_sq x |>.mul_continuousOn (g' := fun t => t * log t ^ 2)
      (ContinuousOn.mul (continuousOn_id' _) (ContinuousOn.pow (continuousOn_log |>.mono <| by
        rintro t ⟨ht1, _⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith) 2)) isCompact_Icc |>.congr_fun_ae ?_
    simp only [measurableSet_Icc, ae_restrict_eq, EventuallyEq, eventually_inf_principal]
    refine .of_forall fun t ⟨ht1, _⟩ => ?_
    rw [div_mul_cancel₀]
    simpa only [ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      log_eq_zero, _root_.or_self_left, not_or] using ⟨by linarith, by linarith, by linarith⟩
  refine ⟨f, fun ε hε ↦ ?_, integrable, ?_⟩
  · rw [isLittleO_iff]
    intro c hc
    specialize @H (c * ε) (mul_pos hc hε)
    simp only [Pi.sub_apply, norm_eq_abs, mul_assoc, eventually_atTop, norm_mul,
      abs_of_pos hε, f] at H ⊢
    exact H
  refine fun r => by simp [f]

theorem chebyshev_asymptotic'' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun _ ↦ ε)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ x > (0 : ℝ), θ x = x + x * (f x) := by
  obtain ⟨f, hf1, inte, hf2⟩ := chebyshev_asymptotic'
  refine ⟨fun t => f t / t, fun ε hε ↦ ?_, ?_, ?_⟩
  · simp only [isLittleO_iff, norm_eq_abs, norm_mul, eventually_atTop,
      norm_div] at hf1 ⊢
    intro r hr
    replace hf1 := hf1 ε hε
    obtain ⟨N, hN⟩ := hf1 hr
    use |N| + 1
    intro x hx
    have hx' : |N| + 1 ≤ |x| := by rwa [abs_of_nonneg (a := x) (le_trans (by positivity) hx)]
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hx'), mul_assoc]
    exact hN x (le_trans (le_trans (le_abs_self N) (by linarith)) hx)

  · intro x hx
    refine inte x hx |>.mul_continuousOn (g' := fun t : ℝ => t⁻¹)
      (continuousOn_inv₀ |>.mono <| by
        rintro t ⟨ht1, _⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith) isCompact_Icc |>.congr_fun_ae <| .of_forall <| by simp [div_eq_mul_inv]
  intro x hx
  rw [hf2, mul_div_cancel₀]
  linarith

-- one could also consider adding a version with p < x instead of p \leq x

lemma continuousOn_log0 :
    ContinuousOn (fun x ↦ -1 / (x * log x ^ 2)) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

lemma continuousOn_log1 : ContinuousOn (fun x ↦ (log x ^ 2)⁻¹ * x⁻¹) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

lemma integral_log_inv (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in a..b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in a..b, ((log t)^2)⁻¹ := by
  rw [le_iff_lt_or_eq] at hb
  rcases hb with hb | rfl; swap
  · simp only [intervalIntegral.integral_same, sub_self, add_zero]
  · have := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun x => (log x)⁻¹)
      (u' := fun x => -1 / (x * (log x)^2))
      (v := fun x => x)
      (v' := fun _ => 1) (a := a) (b := b)
      (fun x hx => by
        rw [Set.uIcc_eq_union, Set.Icc_eq_empty (lt_iff_not_ge |>.1 hb), Set.union_empty] at hx
        obtain ⟨hx1, _⟩ := hx
        rw [show (-1 / (x * log x ^ 2)) = (-1 / log x ^ 2) * (x⁻¹) by
          rw [mul_comm x]; field_simp]
        apply HasDerivAt.comp
          (h := fun t => log t) (h₂ := (fun t : ℝ => t)⁻¹) (x := x)
        · exact HasDerivAt.inv (c := fun t : ℝ => t) (c' := 1) (x := log x)
            (hasDerivAt_id' (log x))
            (by simp only [ne_eq, log_eq_zero, not_or]; refine ⟨?_, ?_, ?_⟩ <;> linarith)
        · apply hasDerivAt_log; linarith)
      (fun x _ => hasDerivAt_id' x)
      (by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le (le_of_lt hb)]
        apply ContinuousOn.integrableOn_Icc
        refine continuousOn_log0.mono fun x hx ↦ ?_
        simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] at hx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> linarith)
      (by
        constructor <;>
        apply MeasureTheory.integrable_const)
    simp only [mul_one] at this
    rw [this]
    simp_rw [neg_div, neg_mul]
    rw [sub_eq_add_neg]
    congr 1
    rw [intervalIntegral.integral_of_le (le_of_lt hb),
      intervalIntegral.integral_of_le (le_of_lt hb),
      ← MeasureTheory.integral_neg]
    simp_rw [neg_neg]
    refine integral_congr_ae ?_
    · rw [ae_restrict_eq, eventuallyEq_inf_principal_iff]
      · refine .of_forall fun x hx => ?_
        simp only [Set.mem_Ioc, one_div, mul_inv_rev, mul_assoc] at hx ⊢
        rw [inv_mul_cancel₀, mul_one]
        linarith
      exact measurableSet_Ioc

lemma integral_log_inv' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  have := integral_log_inv a b ha hb
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, if_pos hb, Set.uIoc_of_le hb,
    smul_eq_mul, one_mul] at this
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  rw [this]

lemma integral_log_inv'' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    (log a)⁻¹ * a + ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) + ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  rw [integral_log_inv' a b ha hb]
  group

lemma integral_log_inv_pos (x : ℝ) (hx : 2 < x) :
    0 < ∫ t in Set.Icc 2 x, (log t)⁻¹ := by
  classical
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · simp only [Function.support_inv, measurableSet_Icc, Measure.restrict_apply']
    rw [show Function.support log ∩ Set.Icc 2 x = Set.Icc 2 x by
      rw [Set.inter_eq_right]
      intro t ht
      simp only [Set.mem_Icc, Function.mem_support, ne_eq, log_eq_zero, not_or] at ht ⊢
      exact ⟨by linarith, by linarith, by linarith⟩]
    simpa
  · simp only [measurableSet_Icc, ae_restrict_eq, EventuallyLE, eventually_inf_principal]
    refine .of_forall fun t (ht : _ ∧ _) => ?_
    simpa only [Pi.zero_apply, inv_nonneg] using log_nonneg (by linarith)
  · apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.inv₀
    · exact (continuousOn_log).mono <| by aesop

    · rintro t ⟨ht, -⟩
      simp only [ne_eq, log_eq_zero, not_or]
      exact ⟨by linarith, by linarith, by linarith⟩

lemma integral_log_inv_ne_zero (x : ℝ) (hx : 2 < x) :
    ∫ t in Set.Icc 2 x, (log t)⁻¹ ≠ 0 := by
  have := integral_log_inv_pos x hx
  linarith

lemma pi_asymp_aux (x : ℝ) (hx : 2 ≤ x) : Nat.primeCounting ⌊x⌋₊ =
    (log x)⁻¹ * θ x + ∫ t in Set.Icc 2 x, θ t * (t * log t ^ 2)⁻¹ := by
  rw [th43_b _ hx]
  simp_rw [div_eq_mul_inv, Chebyshev.theta_eq_sum_Icc]
  ring_nf!

theorem pi_asymp'' :
    (fun x => ((Nat.primeCounting ⌊x⌋₊ : ℝ) / ∫ t in Set.Icc 2 x, 1 / log t) - (1 : ℝ)) =o[atTop]
      fun _ => (1 : ℝ) := by
  obtain ⟨f, hf, f_int, hf'⟩ := chebyshev_asymptotic''
  have eq1 : ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (log x)⁻¹ * (x + x * f x) +
      (∫ t in Set.Icc 2 x,
        (t + t * f t) * (t * log t ^ 2)⁻¹) := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    rw [pi_asymp_aux x hx, hf' x (by linarith)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
    rw [hf' t (by grind)]

  replace eq1 :
    ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (log x)⁻¹ * (x + x * f x) +
      ((∫ t in Set.Icc 2 x, (log t ^ 2)⁻¹) +
        (∫ t in Set.Icc 2 x, (f t) * (log t ^ 2)⁻¹)) := by
    filter_upwards [eq1, eventually_ge_atTop 2] with x eq1 hx
    rw [eq1]
    congr
    simp_rw [mul_inv_rev, add_mul]
    rw [MeasureTheory.integral_add]
    · congr 1
      all_goals
        apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        field [show t ≠ 0 by grind]
    · apply IntegrableOn.mul_continuousOn
        (hg := ContinuousOn.integrableOn_Icc <| continuousOn_id' _)
        (hK := isCompact_Icc)
      apply continuousOn_log1.mono ?_
      intro y h
      simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] at h ⊢
      exact ⟨by linarith, by linarith, by linarith⟩
    · rw [show (fun t ↦ t * f t * ((log t ^ 2)⁻¹ * t⁻¹)) =
        fun t ↦ f t * (t * (log t ^ 2)⁻¹ * t⁻¹) by ext; ring]
      apply IntegrableOn.mul_continuousOn (hK := isCompact_Icc)
      · apply f_int x (by linarith)
      · simp_rw [mul_assoc]
        refine ContinuousOn.mul (continuousOn_id' (Set.Icc 2 x)) ?_
        apply continuousOn_log1.mono ?_
        intro y h
        simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or] at h ⊢
        exact ⟨by linarith, by linarith, by linarith⟩

  simp_rw [mul_add] at eq1
  simp_rw [show ∀ (x : ℝ),
    (log x)⁻¹ * x + (log x)⁻¹ * (x * f x) +
    ((∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹) +
      ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) =
    ((log x)⁻¹ * x + (∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹)) +
    ((log x)⁻¹ * (x * f x) +
      ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)
    by intros; ring] at eq1

  replace eq1 :
    ∃ (C : ℝ), ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
      ((log x)⁻¹ * (x * f x) +
        ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) +
      C := by
    use ((log 2)⁻¹ * 2)
    filter_upwards [eq1, eventually_ge_atTop 2] with x eq1 hx
    rw [eq1, ← integral_log_inv'' _ _ (by rfl) hx]
    ring
  replace eq1 :
    ∃ (C : ℝ), ∀ᶠ (x : ℝ) in atTop,
      (⌊x⌋₊.primeCounting / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - 1 =
      ((log x)⁻¹ * (x * f x) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        (∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)) +
      C / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
    obtain ⟨C, hC⟩ := eq1
    use C
    filter_upwards [hC, eventually_gt_atTop 2] with x hC hx
    rw [hC]
    field [integral_log_inv_ne_zero]
  simp_rw [isLittleO_iff] at hf
  choose C hC using eq1
  simp_rw [← one_div] at hC
  apply isLittleO_congr hC (by rfl) |>.mpr
  have ineq1 (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 0 < c) : ∀ᶠ(x : ℝ) in atTop,
    (log x)⁻¹ * x * |f x| ≤ c * ε * ((log x)⁻¹ * x) := by
    filter_upwards [eventually_ge_atTop 2, hf ε hε hc] with x hx hM
    simp only [norm_eq_abs] at hM
    rw [abs_of_pos hε] at hM
    rw [mul_comm (c * ε)]
    gcongr
    bound
  have int_flog {a b : ℝ} (ha: 2 ≤ a) (hb : 2 ≤ b) :
      IntegrableOn (fun t ↦ |f t| * (log t ^ 2)⁻¹) (Set.Icc a b) volume := by
    apply IntegrableOn.mul_continuousOn
    · apply Integrable.abs <| f_int b hb |>.mono (Set.Icc_subset_Icc_left ha) (by rfl)
    · refine ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
      · simp
        grind
      · intro t ht
        simp only [Set.mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
        exact ⟨by linarith, by linarith, by linarith⟩
    · exact isCompact_Icc
  have int_inv_log_sq {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
      IntegrableOn (fun t ↦ (log t ^ 2)⁻¹) (Set.Icc a b) volume := by
    refine ContinuousOn.integrableOn_Icc <|
      ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
    · grind
    · intro t ht
      simp only [Set.mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
      exact ⟨by linarith, by linarith, by linarith⟩
  simp_rw [eventually_atTop] at hf
  choose M hM using hf
  have ineq2 (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 0 < c)  :
    ∃ (D : ℝ),
      ∀ᶠ (x : ℝ) in atTop,
      |∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹| ≤
      c * ε * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x) + D := by
    use (((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), |f t| * (log t ^ 2)⁻¹) -
              c * ε * ∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹) +
            c * ε * ((log 2)⁻¹ * 2))
    filter_upwards [eventually_gt_atTop (max 2 (M ε hε hc))] with x hx
    calc _
      _ ≤ ∫ (t : ℝ) in Set.Icc 2 x, |f t * (log t ^ 2)⁻¹| :=
        norm_integral_le_integral_norm fun a ↦ f a * (log a ^ 2)⁻¹
      _ = ∫ (t : ℝ) in Set.Icc 2 x, |f t| * (log t ^ 2)⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        rw [abs_mul, abs_of_nonneg (a := (log t ^ 2)⁻¹)]
        norm_num
        apply pow_nonneg
        exact log_nonneg <| by grind
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          (∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x,
          |f t| * (log t ^ 2)⁻¹) := by
        rw [← setIntegral_union₀, Set.Icc_union_Icc_eq_Icc (le_max_left ..) hx.le]
        · rw [AEDisjoint, Set.Icc_inter_Icc_eq_singleton (le_max_left ..) hx.le, volume_singleton]
        · simp only [measurableSet_Icc, MeasurableSet.nullMeasurableSet]
        · apply int_flog (by rfl) (le_max_left ..)
        · apply int_flog (le_max_left ..) (le_trans (le_max_left ..) hx.le)
      _ ≤ (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          (∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x,
          (c * ε) * (log t ^ 2)⁻¹) := by
          gcongr 1
          apply setIntegral_mono_on
          · apply int_flog (le_max_left ..) (le_trans (le_max_left ..) hx.le)
          · rw [IntegrableOn, integrable_const_mul_iff]
            · apply int_inv_log_sq (le_max_left ..) (le_trans (le_max_left ..) hx.le)
            · simp only [isUnit_iff_ne_zero, ne_eq, _root_.mul_eq_zero, not_or]
              exact ⟨by linarith, by linarith⟩
          · exact measurableSet_Icc
          · intro t ht
            simp only [Set.mem_Icc, sup_le_iff] at ht
            apply mul_le_mul_of_nonneg_right
            · refine hM ε hε hc t ht.1.2 |>.trans ?_
              simp only [norm_eq_abs, abs_of_pos hε, le_refl]
            · norm_num
              refine pow_nonneg (log_nonneg <| by linarith) 2
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          ((c * ε) * ∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x, (log t ^ 2)⁻¹) := by
          congr 1
          exact integral_const_mul (c * ε) _
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          ((c * ε) *
            ((∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x, (log t ^ 2)⁻¹) +
            ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) -
            ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)))) := by
        ring
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          ((c * ε) *
            ((∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹) -
              ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)))) := by
          congr 3
          rw [add_comm, ← setIntegral_union₀, Set.Icc_union_Icc_eq_Icc (le_max_left ..) hx.le]
          · rw [AEDisjoint, Set.Icc_inter_Icc_eq_singleton (le_max_left ..) hx.le,
              volume_singleton]
          · simp only [measurableSet_Icc, MeasurableSet.nullMeasurableSet]
          · apply int_inv_log_sq (by rfl) (le_max_left ..)
          · apply int_inv_log_sq (le_max_left ..) (le_trans (le_max_left ..) hx.le)
      _ = ((c * ε) * (∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹)) +
        ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
        |f t| * (log t ^ 2)⁻¹) -
        (c * ε) * (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) := by
        ring
      _ = ((c * ε) * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
            ((log 2)⁻¹ * 2) - ((log x)⁻¹ * x))) +
        ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
        |f t| * (log t ^ 2)⁻¹) -
        (c * ε) * (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) := by
        congr 2
        rw [integral_log_inv' _ _ (by rfl)]
        · ring
        · simp only [max_lt_iff] at hx
          linarith
      _ = _ := by ring
  choose D hD using ineq2

  have ineq4 (const : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, |const / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)| ≤ 1/2 * ε := by
    obtain rfl|hconst := eq_or_ne const 0
    · filter_upwards with x
      simp[hε.le]
    have ineq (x : ℝ) (hx : 2 < x) :=
      calc (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)
        _ ≥ (∫ (_ : ℝ) in Set.Icc 2 x, (log x)⁻¹) := by
          apply setIntegral_mono_on (integrable_const _)
          · refine ContinuousOn.integrableOn_Icc <|
              ContinuousOn.inv₀ (continuousOn_log |>.mono ?_) ?_
            · simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, not_and, not_le,
              isEmpty_Prop, ofNat_pos, IsEmpty.forall_iff]
            · intro t ht
              simp only [Set.mem_Icc, ne_eq, log_eq_zero, not_or] at ht ⊢
              exact ⟨by linarith, by linarith, by linarith⟩
          · exact measurableSet_Icc
          · intro t ⟨ht1, ht2⟩
            gcongr
            bound
        _ = (x - 2) * (log x)⁻¹ := by
          rw [MeasureTheory.integral_const]
          simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, volume_Icc,
            smul_eq_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff, sub_nonneg,
            inv_eq_zero, log_eq_zero, Measure.real]
          refine Or.inl (le_of_lt hx)

    simp_rw [abs_div]
    have ineq (x : ℝ) (hx : 2 < x) :
        |const| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| ≤
        |const| / ((x - 2) * (log x)⁻¹) := by
      apply div_le_div₀ (abs_nonneg _) (by rfl)
      · apply mul_pos
        · linarith
        · norm_num
          rw [Real.log_pos_iff]
          · linarith
          · linarith
      · rw [abs_of_pos (integral_log_inv_pos _ hx)]
        exact ineq x hx
    have ineq (x : ℝ) (hx : 2 < x) :
        |const| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| ≤
        |const| * (log x / ((x - 2))) := by
      refine ineq x hx |>.trans <| le_of_eq ?_
      field_simp
    have lim := Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 (by norm_num)
    simp only [pow_one, one_mul, ← sub_eq_add_neg] at lim
    rw [tendsto_atTop_nhds] at lim
    specialize lim (Metric.ball 0 ((1/2) * ε / |const| : ℝ)) (by
      simp only [Metric.mem_ball, _root_.dist_self]
      apply _root_.div_pos
      · linarith
      · simpa only [abs_pos, ne_eq]) Metric.isOpen_ball
    obtain ⟨M, hM⟩ := lim
    rw [eventually_atTop]
    refine ⟨max 3 M, ?_⟩
    intro x hx
    simp only [Metric.mem_ball, _root_.dist_zero_right, max_le_iff, norm_eq_abs] at hM hx
    refine ineq x (by linarith) |>.trans ?_
    specialize hM x hx.2
    rw [abs_of_nonneg (by
      apply div_nonneg
      · refine log_nonneg (by linarith)
      · linarith)] at hM
    have ineq' : |const| * (log x / (x - 2)) < |const| * ((1/2) * ε / |const|) := by
      rw [mul_lt_mul_iff_right₀]
      · exact hM
      · simpa only [abs_pos, ne_eq]
    rw [mul_div_cancel₀] at ineq'
    · refine le_of_lt ineq'
    · simpa only [ne_eq, abs_eq_zero]
  rw [isLittleO_iff]
  intro ε hε
  specialize ineq4 (|D ε hε (1/2) (by linarith)| + |C|) ε hε
  simp only [one_div, norm_eq_abs, norm_one, mul_one]
  filter_upwards [eventually_gt_atTop 2, ineq4, ineq1 ε hε (1 / 2) (by norm_num),
      hD ε hε (1 / 2) (by norm_num)] with x hx hB ineq1 hD
  have := integral_log_inv_pos x (by linarith) |>.le
  calc _
    _ ≤ |((log x)⁻¹ * (x * f x) / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)| +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) /
          ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |C / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
      apply abs_add_three
    _ = |(log x)⁻¹ * (x * f x)| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |C| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
      rw [abs_div, abs_div, abs_div]
    _ = |(log x)⁻¹ * (x * f x)| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        repeat rw [abs_of_pos <| integral_log_inv_pos _ (by linarith)]
    _ = ((log x)⁻¹ * x * |f x|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        congr
        rw [abs_mul, abs_mul, abs_of_nonneg (by bound), abs_of_nonneg (by linarith), mul_assoc]
    _ ≤ ((1/2) * ε * ((log x)⁻¹ * x)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        ((1/2) * ε * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x) +
          D ε hε (1/2) (by linarith)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        gcongr
    _ = ((1/2) * ε * (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)) /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        (D ε hε (1/2) (by linarith) + |C|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      ring
    _ = (1/2) * ε + (D ε hε (1/2) (by linarith) + |C|) /
        (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      congr 1
      rw [mul_div_assoc, div_self, mul_one]
      apply integral_log_inv_ne_zero
      linarith
    _ ≤ (1/2) * ε + (|D ε hε (1/2) (by linarith)| + |C|) /
        (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      gcongr
      apply le_abs_self
    _ ≤ (1/2) * ε + (1/2) * ε := by
      rw [abs_div, abs_of_nonneg, abs_of_pos (a := ∫ _ in _, _)] at hB
      · gcongr
      · apply integral_log_inv_pos; linarith
      · positivity
    _ = ε := by
      field

theorem pi_asymp :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ (x : ℝ) in atTop,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * ∫ t in (2 : ℝ)..x, 1 / (log t) := by
  refine ⟨_, pi_asymp'', ?_⟩
  filter_upwards [eventually_ge_atTop 3] with x hx
  rw [intervalIntegral.integral_of_le (by linarith),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  field [(integral_log_inv_pos x (by linarith)).ne']

lemma inv_div_log_asy : ∃ c, ∀ᶠ (x : ℝ) in atTop,
    ∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2 ≤ c * (x / log x ^ 2) := by
  have := Chebyshev.integral_one_div_log_sq_isBigO
  rw [isBigO_iff] at this
  obtain ⟨c, hc⟩ := this
  use c
  filter_upwards [hc, eventually_ge_atTop 2] with x hc hx
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  apply le_trans (by apply le_norm_self)
  nth_rewrite 2 [norm_of_nonneg (by positivity)] at hc
  exact hc

lemma integral_log_inv_pialt (x : ℝ) (hx : 4 ≤ x) : ∫ (t : ℝ) in Set.Icc 2 x, 1 / log t =
    x / log x - 2 / log 2 + ∫ (t : ℝ) in Set.Icc 2 x, 1 / (log t) ^ 2 := by
  have := integral_log_inv 2 x (by norm_num) (by linarith)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [hx]),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [hx]),
    ← mul_one_div, one_div, ← mul_one_div, one_div]
  simp only [one_div, this, mul_comm]

lemma integral_div_log_asymptotic : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ᶠ (x : ℝ) in atTop, ∫ t in Set.Icc 2 x, 1 / (log t) = (1 + c x) * x / (log x) := by
  obtain ⟨c, hc⟩ := inv_div_log_asy
  use fun x => ((∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2) - 2 / log 2) * log x / x
  constructor
  · simp_rw [mul_div_assoc, mul_comm]
    apply isLittleO_mul_iff_isLittleO_div _|>.mpr
    · simp_rw [one_div_div]
      apply IsLittleO.sub
      · apply IsBigO.trans_isLittleO (g := (fun x ↦ x / log x ^ 2))
        · rw [isBigO_iff]
          use c
          filter_upwards [eventually_ge_atTop 2, hc] with x hx hc
          simp only [norm_eq_abs]
          rwa [abs_of_nonneg, abs_of_nonneg]
          · bound
          · apply setIntegral_nonneg measurableSet_Icc fun t ht ↦ (by bound)
        apply isLittleO_of_tendsto
        · simp
        apply tendsto_log_atTop.inv_tendsto_atTop.congr'
        filter_upwards [eventually_ne_atTop 0] with x hx
        simp only [Pi.inv_apply]
        field
      apply isLittleO_mul_iff_isLittleO_div _|>.mp
      · conv => arg 2; ext; rw [mul_comm]
        apply IsLittleO.const_mul_left isLittleO_log_id_atTop
      · filter_upwards [eventually_ge_atTop 2] with x hx
        simp; grind
    filter_upwards [eventually_ge_atTop 2] with x hx
    simp
    grind
  · filter_upwards [eventually_ge_atTop 4] with x hx
    rw [integral_log_inv_pialt x hx]
    field [show log x ≠ 0 by simp; grind]

theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  obtain ⟨f, hf, h⟩ := pi_asymp
  obtain ⟨f', hf', h'⟩ := integral_div_log_asymptotic
  use (fun x => (log x / x) * ⌊x⌋₊.primeCounting - 1)
  constructor
  · apply IsLittleO.congr' (f₁ := (fun x ↦ f x + f x * f' x + f' x)) _ _ (by rfl)
    · apply IsLittleO.add _ hf'
      apply IsLittleO.add hf
      simpa [Pi.mul_apply, one_mul] using hf.mul hf'
    · filter_upwards [eventually_ge_atTop 2, h, h'] with x hx h h'
      rw [h, intervalIntegral.integral_of_le hx, ← integral_Icc_eq_integral_Ioc, h']
      have : log x ≠ 0 := by simp; grind
      field
  · intro x
    obtain rfl|hx := eq_or_ne x 0
    · simp
    obtain rfl|hx := eq_or_ne x 1
    · simp
    obtain rfl|hx := eq_or_ne x (-1 : ℝ)
    · simp
      norm_num
    have : log x ≠ 0 := by simp_all
    field

noncomputable def R (x : ℝ) : ℝ := Psi x - x

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Lemma12Candidates.lean` -/

section
/-!
# The four-prime candidate family in Martin's Lemma 12

This file constructs the candidate multipliers used in the large-prime-power
elimination step.  For a scale `t`, the source primes lie in `(c*t,t]`, with
the prime below the prime power being eliminated removed.  Candidate
multipliers are products of four-element subsets of that prime band.

The construction is deliberately separated from the modular dispersion
argument.  Its exported facts are unconditional: exact cardinality, unique
factorisation, the product interval, coprimality to the eliminated prime
power, and a sharp description of all prime factors.  A final existence
theorem extracts a candidate family of any prescribed cardinality allowed by
the prime-number-theorem count.
-/

namespace Lemma12Candidates

open Filter Finset Real Asymptotics
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos285.PrimePowers

/-- The nonnegative fourth root, expressed using two square roots so that its
fourth-power identity is elementary. -/
def fourthRoot (x : ℝ) : ℝ := Real.sqrt (Real.sqrt x)

lemma fourthRoot_nonneg (x : ℝ) : 0 ≤ fourthRoot x := Real.sqrt_nonneg _

lemma fourthRoot_pos {x : ℝ} (hx : 0 < x) : 0 < fourthRoot x := by
  exact Real.sqrt_pos.2 (Real.sqrt_pos.2 hx)

lemma fourthRoot_lt_one {x : ℝ} (hx1 : x < 1) : fourthRoot x < 1 := by
  apply (Real.sqrt_lt' (by norm_num)).2
  apply (Real.sqrt_lt' (by norm_num)).2
  simpa using hx1

lemma fourthRoot_pow_four {x : ℝ} (hx : 0 ≤ x) : fourthRoot x ^ 4 = x := by
  rw [show fourthRoot x ^ 4 = (Real.sqrt (Real.sqrt x) ^ 2) ^ 2 by
      simp only [fourthRoot]; ring,
    Real.sq_sqrt (Real.sqrt_nonneg x), Real.sq_sqrt hx]

/-- Primes in the half-open real interval `(c*t,t]`. -/
def primeBand (c t : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊t⌋₊ \ Nat.primesLE ⌊c * t⌋₊

/-- The prime band with the base prime of the current prime power removed. -/
def candidatePrimes (p : ℕ) (c t : ℝ) : Finset ℕ :=
  (primeBand c t).erase p

/-- Products of four distinct primes from the candidate band. -/
def rawCandidates (p : ℕ) (c t : ℝ) : Finset ℕ :=
  ((candidatePrimes p c t).powersetCard 4).image fun S ↦ S.prod id

lemma mem_primeBand {c t : ℝ} {r : ℕ} (_hc : 0 ≤ c) (ht : 0 ≤ t)
    (hr : r ∈ primeBand c t) :
    r.Prime ∧ c * t < r ∧ (r : ℝ) ≤ t := by
  rw [primeBand, Finset.mem_sdiff] at hr
  have hrUpper := Nat.mem_primesLE.mp hr.1
  have hrLower : ⌊c * t⌋₊ < r := by
    simpa [Nat.mem_primesLE, hrUpper.2] using hr.2
  refine ⟨hrUpper.2, Nat.lt_of_floor_lt hrLower, ?_⟩
  exact (Nat.cast_le.mpr hrUpper.1).trans (Nat.floor_le ht)

lemma mem_candidatePrimes {p r : ℕ} {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hr : r ∈ candidatePrimes p c t) :
    r.Prime ∧ r ≠ p ∧ c * t < r ∧ (r : ℝ) ≤ t := by
  rw [candidatePrimes, Finset.mem_erase] at hr
  have hband := mem_primeBand hc ht hr.2
  exact ⟨hband.1, hr.1, hband.2.1, hband.2.2⟩

lemma candidatePrime_pos {p r : ℕ} {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hr : r ∈ candidatePrimes p c t) : 0 < r :=
  (mem_candidatePrimes hc ht hr).1.pos

private lemma product_of_primes_factors_toFinset {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    (S.prod id).primeFactorsList.toFinset = S := by
  have hprod : (S.sort (· ≤ ·)).prod = S.prod id := by
    calc
      (S.sort (· ≤ ·)).prod = (S.sort (· ≤ ·)).toFinset.prod id := by
        simpa using (List.prod_toFinset id (S.sort_nodup (· ≤ ·))).symm
      _ = S.prod id := by rw [Finset.sort_toFinset]
  have hprime : ∀ p ∈ S.sort (· ≤ ·), p.Prime := by
    intro p hp
    exact hS p ((Finset.mem_sort (· ≤ ·)).mp hp)
  have hperm : List.Perm (S.sort (· ≤ ·)) (S.prod id).primeFactorsList :=
    Nat.primeFactorsList_unique hprod hprime
  exact (List.toFinset_eq_of_perm _ _ hperm).symm.trans (Finset.sort_toFinset _ _)

lemma prod_injective_on_candidatePrimeSubsets (p : ℕ) (c t : ℝ) :
    Set.InjOn (fun S : Finset ℕ ↦ S.prod id) (candidatePrimes p c t).powerset := by
  intro A hA B hB hprod
  have hAprime : ∀ r ∈ A, r.Prime := by
    intro r hr
    have hr' := Finset.mem_powerset.mp hA hr
    exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp
      (Finset.mem_erase.mp hr').2).1).2
  have hBprime : ∀ r ∈ B, r.Prime := by
    intro r hr
    have hr' := Finset.mem_powerset.mp hB hr
    exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp
      (Finset.mem_erase.mp hr').2).1).2
  change A.prod id = B.prod id at hprod
  calc
    A = (A.prod id).primeFactorsList.toFinset :=
      (product_of_primes_factors_toFinset hAprime).symm
    _ = (B.prod id).primeFactorsList.toFinset := by rw [hprod]
    _ = B := product_of_primes_factors_toFinset hBprime

lemma rawCandidates_card (p : ℕ) (c t : ℝ) :
    (rawCandidates p c t).card = Nat.choose (candidatePrimes p c t).card 4 := by
  rw [rawCandidates, Finset.card_image_iff.mpr]
  · exact Finset.card_powersetCard 4 (candidatePrimes p c t)
  · apply (prod_injective_on_candidatePrimeSubsets p c t).mono
    intro S hS
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1

lemma rawCandidates_card_lower (p : ℕ) (c t : ℝ) :
    ((((candidatePrimes p c t).card + 1 - 4 : ℕ) : ℝ) ^ 4) /
        ((Nat.factorial 4 : ℕ) : ℝ) ≤
      (rawCandidates p c t).card := by
  rw [rawCandidates_card]
  exact Nat.pow_le_choose 4 (candidatePrimes p c t).card

lemma mem_rawCandidates_source {p n : ℕ} {c t : ℝ}
    (hn : n ∈ rawCandidates p c t) :
    ∃ S ⊆ candidatePrimes p c t, S.card = 4 ∧ n = S.prod id := by
  rw [rawCandidates, Finset.mem_image] at hn
  obtain ⟨S, hS, rfl⟩ := hn
  exact ⟨S, (Finset.mem_powersetCard.mp hS).1,
    (Finset.mem_powersetCard.mp hS).2, rfl⟩

lemma rawCandidate_isKPrimeProductAway {p ν n : ℕ} {c t : ℝ}
    (hp : p.Prime) (hn : n ∈ rawCandidates p c t) :
    Erdos285.Dispersion.IsKPrimeProductAway 4 (p ^ ν) n := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_rawCandidates_source hn
  refine ⟨S, hcard, ?_, rfl⟩
  intro r hr
  have hrC := Finset.mem_erase.mp (hS hr)
  have hrPrime : r.Prime :=
    (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hrC.2).1).2
  refine ⟨hrPrime, ?_⟩
  exact hrPrime.coprime_iff_not_dvd.mp
    (Nat.Coprime.pow_right ν ((Nat.coprime_primes hrPrime hp).2 hrC.1))

lemma rawCandidate_coprime_primePow {p ν n : ℕ} {c t : ℝ}
    (hp : p.Prime) (hn : n ∈ rawCandidates p c t) :
    Nat.Coprime n (p ^ ν) :=
  Erdos285.Dispersion.isKPrimeProductAway_coprime
    (rawCandidate_isKPrimeProductAway hp hn)

lemma rawCandidate_pos {p n : ℕ} {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hn : n ∈ rawCandidates p c t) : 0 < n := by
  obtain ⟨S, hS, -, rfl⟩ := mem_rawCandidates_source hn
  exact Finset.prod_pos fun r hr ↦ candidatePrime_pos hc ht (hS hr)

lemma rawCandidate_upper {p n : ℕ} {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hn : n ∈ rawCandidates p c t) :
    (n : ℝ) ≤ t ^ 4 := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_rawCandidates_source hn
  push_cast
  calc
    ∏ r ∈ S, (r : ℝ) ≤ ∏ _r ∈ S, t := by
      exact Finset.prod_le_prod (fun _ _ ↦ by positivity)
        (fun r hr ↦ (mem_candidatePrimes hc ht (hS hr)).2.2.2)
    _ = t ^ 4 := by simp [Finset.prod_const, hcard]

lemma rawCandidate_upper_strict {p n : ℕ} {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 < t) (hn : n ∈ rawCandidates p c t) :
    (n : ℝ) < t ^ 4 := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_rawCandidates_source hn
  push_cast
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r, hr⟩ := hSne
  have hEraseCard : (S.erase r).card = 3 := by
    rw [Finset.card_erase_of_mem hr, hcard]
  have hErase : (S.erase r).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨s, hsErase⟩ := hErase
  have hs : s ∈ S := Finset.mem_of_mem_erase hsErase
  have hsr : s ≠ r := (Finset.mem_erase.mp hsErase).1
  have hrle := (mem_candidatePrimes hc ht.le (hS hr)).2.2.2
  have hsle := (mem_candidatePrimes hc ht.le (hS hs)).2.2.2
  have hstrict : ∃ u ∈ S, (u : ℝ) < t := by
    by_cases hrt : (r : ℝ) < t
    · exact ⟨r, hr, hrt⟩
    · have hre : (r : ℝ) = t := le_antisymm hrle (le_of_not_gt hrt)
      have hst : (s : ℝ) < t := by
        by_contra hnst
        have hse : (s : ℝ) = t := le_antisymm hsle (le_of_not_gt hnst)
        apply hsr
        exact_mod_cast hse.trans hre.symm
      exact ⟨s, hs, hst⟩
  calc
    ∏ u ∈ S, (u : ℝ) < ∏ _u ∈ S, t := by
      apply Finset.prod_lt_prod
      · intro u hu
        exact_mod_cast (mem_candidatePrimes hc ht.le (hS hu)).1.pos
      · intro u hu
        exact (mem_candidatePrimes hc ht.le (hS hu)).2.2.2
      · exact hstrict
    _ = t ^ 4 := by simp [Finset.prod_const, hcard]

lemma rawCandidate_lower {p n : ℕ} {c t : ℝ}
    (hc : 0 < c) (ht : 0 < t) (hn : n ∈ rawCandidates p c t) :
    (c * t) ^ 4 < (n : ℝ) := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_rawCandidates_source hn
  push_cast
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hprod : (c * t) ^ S.card < ∏ r ∈ S, (r : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_lt_prod_of_nonempty
      (fun _ _ ↦ mul_pos hc ht)
      (fun r hr ↦ (mem_candidatePrimes hc.le ht.le (hS hr)).2.2.1) hSne
  simpa [hcard] using hprod

/-! ## Prime-number-theorem count -/

lemma primeBand_card_eq {c t : ℝ} (_hc : 0 ≤ c) (hc1 : c ≤ 1) (ht : 0 ≤ t) :
    ((primeBand c t).card : ℝ) =
      Nat.primeCounting ⌊t⌋₊ - Nat.primeCounting ⌊c * t⌋₊ := by
  have hct : c * t ≤ t := by nlinarith
  have hfloor : ⌊c * t⌋₊ ≤ ⌊t⌋₊ := Nat.floor_mono hct
  have hsub : Nat.primesLE ⌊c * t⌋₊ ⊆ Nat.primesLE ⌊t⌋₊ :=
    Nat.primesLE_mono hfloor
  rw [primeBand, Finset.card_sdiff_of_subset hsub,
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  rw [Nat.cast_sub (Nat.monotone_primeCounting hfloor)]

/-- A fixed positive-width multiplicative prime band contains a positive
multiple of `t/log t` primes.  The constant is intentionally loose. -/
theorem eventually_primeBand_card_lower {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t : ℝ in atTop,
      (1 - c) * t / (4 * Real.log t) ≤ ((primeBand c t).card : ℝ) := by
  let η : ℝ := (1 - c) / 16
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η < 1 := by dsimp [η]; nlinarith
  obtain ⟨e, he, hpi⟩ := pi_alt
  have heBound := he.bound hη
  have hscale : Tendsto (fun t : ℝ ↦ c * t) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have heBoundScaled := hscale.eventually heBound
  filter_upwards [heBound, heBoundScaled, eventually_gt_atTop (max 2 (1 / c + 1)),
    Real.tendsto_log_atTop.eventually_ge_atTop (-Real.log c / η)]
      with t het hect ht hlogLarge
  have ht2 : 2 < t := (le_max_left (2 : ℝ) (1 / c + 1)).trans_lt ht
  have ht0 : 0 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have hctpos : 0 < c * t := mul_pos hc htpos
  have hctone : 1 < c * t := by
    have htlarge : 1 / c + 1 < t := lt_of_le_of_lt (le_max_right 2 (1 / c + 1)) ht
    have hcInv : c * (1 / c) = 1 := by field_simp
    nlinarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogct : 0 < Real.log (c * t) := Real.log_pos hctone
  have hlogCompare : (1 - η) * Real.log t ≤ Real.log (c * t) := by
    rw [Real.log_mul hc.ne' htpos.ne']
    have := mul_le_mul_of_nonneg_left hlogLarge hη.le
    field_simp [hη.ne'] at this
    nlinarith
  have heLower : 1 - η ≤ 1 + e t := by
    have := (abs_le.mp (show |e t| ≤ η by simpa using het)).1
    linarith
  have heUpper : 1 + e (c * t) ≤ 1 + η := by
    have := (abs_le.mp (show |e (c * t)| ≤ η by simpa using hect)).2
    linarith
  have hpiLower : (1 - η) * (t / Real.log t) ≤
      Nat.primeCounting ⌊t⌋₊ := by
    rw [hpi t]
    simpa [mul_div_assoc] using
      mul_le_mul_of_nonneg_right heLower (div_nonneg ht0 hlogt.le)
  have hcoeff : 0 ≤ (1 + η) * c / (1 - η) := by positivity
  have hden : 1 - η ≠ 0 := ne_of_gt (sub_pos.mpr hη1)
  have hpiUpper : (Nat.primeCounting ⌊c * t⌋₊ : ℝ) ≤
      ((1 + η) * c / (1 - η)) * (t / Real.log t) := by
    rw [hpi (c * t)]
    apply (div_le_iff₀ hlogct).2
    calc
      (1 + e (c * t)) * (c * t) ≤ (1 + η) * (c * t) := by
        exact mul_le_mul_of_nonneg_right heUpper hctpos.le
      _ = (((1 + η) * c / (1 - η)) * (t / Real.log t)) *
          ((1 - η) * Real.log t) := by
            field_simp [hden, hlogt.ne']
      _ ≤ (((1 + η) * c / (1 - η)) * (t / Real.log t)) *
          Real.log (c * t) := by
            gcongr
  have hcoefGap : (1 - c) / 4 ≤
      (1 - η) - (1 + η) * c / (1 - η) := by
    rw [show (1 - η) - (1 + η) * c / (1 - η) =
      ((1 - η) ^ 2 - (1 + η) * c) / (1 - η) by
        field_simp [hden]
        ]
    rw [le_div_iff₀ (sub_pos.mpr hη1)]
    dsimp [η]
    nlinarith [sq_nonneg (1 - c)]
  rw [primeBand_card_eq hc.le hc1.le ht0]
  calc
    (1 - c) * t / (4 * Real.log t) = ((1 - c) / 4) * (t / Real.log t) := by ring
    _ ≤ ((1 - η) - (1 + η) * c / (1 - η)) *
        (t / Real.log t) := by gcongr
    _ = (1 - η) * (t / Real.log t) -
        ((1 + η) * c / (1 - η)) * (t / Real.log t) := by ring
    _ ≤ (Nat.primeCounting ⌊t⌋₊ : ℝ) - Nat.primeCounting ⌊c * t⌋₊ :=
      sub_le_sub hpiLower hpiUpper

lemma primeBand_card_le_candidatePrimes_card_add_one (p : ℕ) (c t : ℝ) :
    (primeBand c t).card ≤ (candidatePrimes p c t).card + 1 := by
  by_cases hp : p ∈ primeBand c t
  · rw [candidatePrimes, Finset.card_erase_of_mem hp]
    have := Finset.card_pos.mpr ⟨p, hp⟩
    omega
  · simp [candidatePrimes, hp]

/-! ## Extracting a prescribed candidate family -/

lemma rawCandidate_squarefree {p n : ℕ} {c t : ℝ}
    (hn : n ∈ rawCandidates p c t) : Squarefree n := by
  obtain ⟨S, hS, -, rfl⟩ := mem_rawCandidates_source hn
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro r hr s hs hrs
    have hrC := Finset.mem_erase.mp (hS hr)
    have hsC := Finset.mem_erase.mp (hS hs)
    have hrPrime : r.Prime :=
      (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hrC.2).1).2
    have hsPrime : s.Prime :=
      (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hsC.2).1).2
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes hrPrime hsPrime).2 hrs)
  · intro r hr
    have hrC := Finset.mem_erase.mp (hS hr)
    exact ((Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hrC.2).1).2).squarefree

lemma rawCandidate_primeFactors_eq {p n : ℕ} {c t : ℝ}
    (hn : n ∈ rawCandidates p c t) :
    ∃ S ⊆ candidatePrimes p c t, S.card = 4 ∧
      n = S.prod id ∧ n.primeFactors = S := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_rawCandidates_source hn
  refine ⟨S, hS, hcard, rfl, ?_⟩
  exact Nat.primeFactors_prod fun r hr ↦ by
    have hrC := Finset.mem_erase.mp (hS hr)
    exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hrC.2).1).2

lemma rawCandidate_primeFactors_lt {p ν n : ℕ} {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 ≤ t) (htq : t ≤ (p ^ ν : ℕ))
    (hn : n ∈ rawCandidates p c t) :
    ∀ r ∈ n.primeFactors, r < p ^ ν := by
  obtain ⟨S, hS, -, -, hfac⟩ := rawCandidate_primeFactors_eq hn
  intro r hr
  rw [hfac] at hr
  have hrData := mem_candidatePrimes hc ht (hS hr)
  have hrleR : (r : ℝ) ≤ (p ^ ν : ℕ) := hrData.2.2.2.trans htq
  have hrle : r ≤ p ^ ν := by exact_mod_cast hrleR
  have hrne : r ≠ p ^ ν := by
    intro hre
    have hqprime : (p ^ ν).Prime := by simpa [← hre] using hrData.1
    have hνone : ν = 1 := hqprime.eq_one_of_pow
    subst ν
    apply hrData.2.1
    simpa using hre
  exact lt_of_le_of_ne hrle hrne

/-- The current prime power is the largest exact prime-power part of every
displayed denominator `p^ν*n`, provided the prime band lies below it. -/
lemma largestPrimePowerPart_primePow_mul_rawCandidate
    {p ν n : ℕ} {c t : ℝ}
    (hp : p.Prime) (hν : 0 < ν) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (htq : t ≤ (p ^ ν : ℕ)) (hn : n ∈ rawCandidates p c t) :
    largestPrimePowerPart (p ^ ν * n) = p ^ ν := by
  let q := p ^ ν
  have hqpos : 0 < q := pow_pos hp.pos ν
  have hqpp : IsPrimePow q :=
    (isPrimePow_pow_iff hν.ne').2 hp.isPrimePow
  have hcop : Nat.Coprime q n :=
    (rawCandidate_coprime_primePow hp hn).symm
  have hqmem : q ∈ primePowerParts (q * n) := by
    apply (mem_primePowerParts (mul_ne_zero hqpos.ne' (rawCandidate_pos hc ht hn).ne')).2
    refine ⟨hqpp, Nat.dvd_mul_right q n, ?_⟩
    simpa [Nat.mul_div_cancel_left n hqpos] using hcop
  apply Nat.le_antisymm
  · rw [largestPrimePowerPart_le_iff]
    intro ℓ hℓ
    have hspec := (mem_primePowerParts
      (mul_ne_zero hqpos.ne' (rawCandidate_pos hc ht hn).ne')).1 hℓ
    rcases hcop.isPrimePow_dvd_mul hspec.1 |>.1 hspec.2.1 with hdivq | hdivn
    · exact Nat.le_of_dvd hqpos hdivq
    · have hℓprime : ℓ.Prime := Nat.squarefree_and_prime_pow_iff_prime.mp
        ⟨(rawCandidate_squarefree hn).squarefree_of_dvd hdivn, hspec.1⟩
      have hℓfac : ℓ ∈ n.primeFactors :=
        hℓprime.mem_primeFactors hdivn (rawCandidate_pos hc ht hn).ne'
      exact (rawCandidate_primeFactors_lt hc ht htq hn ℓ hℓfac).le
  · exact le_largestPrimePowerPart hqmem

/-- The LCM of an arbitrary subfamily is squarefree: taking an LCM does not
reintroduce the multiplicities that would occur in the product of all
candidates. -/
lemma candidateFamily_lcm_squarefree {p : ℕ} {c t : ℝ} {M : Finset ℕ}
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hM : M ⊆ rawCandidates p c t) :
    Squarefree (M.lcm id) := by
  have hnonzero : ∀ m ∈ M, id m ≠ 0 := by
    intro m hm
    exact (rawCandidate_pos hc ht (hM hm)).ne'
  have hL0 : M.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr hnonzero
  apply Nat.squarefree_of_factorization_le_one hL0
  intro r
  rw [Finset.factorization_lcm hnonzero]
  refine Finset.sup_le_iff.mpr ?_
  intro m hm
  exact (rawCandidate_squarefree (hM hm)).natFactorization_le_one r

/-- Every prime power dividing the candidate LCM is in fact one of its source
primes, and therefore lies below the eliminated prime power once the source
band does. -/
lemma primePower_dvd_candidateFamily_lcm_lt
    {p ν ℓ : ℕ} {c t : ℝ} {M : Finset ℕ}
    (hc : 0 ≤ c) (ht : 0 ≤ t) (htq : t ≤ (p ^ ν : ℕ))
    (hM : M ⊆ rawCandidates p c t)
    (hℓpp : IsPrimePow ℓ) (hℓdvd : ℓ ∣ M.lcm id) : ℓ < p ^ ν := by
  have hLsquare := candidateFamily_lcm_squarefree hc ht hM
  have hℓprime : ℓ.Prime := Nat.squarefree_and_prime_pow_iff_prime.mp
    ⟨hLsquare.squarefree_of_dvd hℓdvd, hℓpp⟩
  have hprod : ℓ ∣ M.prod id := hℓdvd.trans (Finset.lcm_dvd_prod M id)
  obtain ⟨m, hm, hℓm⟩ := hℓprime.prime.exists_mem_finset_dvd hprod
  have hℓfac : ℓ ∈ m.primeFactors :=
    hℓprime.mem_primeFactors hℓm (rawCandidate_pos hc ht (hM hm)).ne'
  exact rawCandidate_primeFactors_lt hc ht htq (hM hm) ℓ hℓfac

/-- Combine a pre-existing prime-power bound for an old denominator quotient
with the candidate-LCM bound.  The coprime factorization of an LCM is used
here; unlike replacing the LCM by a product, it cannot spuriously add prime
exponents shared by the two sides. -/
lemma primePower_dvd_lcm_candidateFamily_lt
    {A p ν ℓ : ℕ} {c t : ℝ} {M : Finset ℕ}
    (hA0 : A ≠ 0) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (htq : t ≤ (p ^ ν : ℕ)) (hM : M ⊆ rawCandidates p c t)
    (hA : ∀ d : ℕ, IsPrimePow d → d ∣ A → d < p ^ ν)
    (hℓpp : IsPrimePow ℓ) (hℓdvd : ℓ ∣ Nat.lcm A (M.lcm id)) :
    ℓ < p ^ ν := by
  have hnonzero : ∀ m ∈ M, id m ≠ 0 := by
    intro m hm
    exact (rawCandidate_pos hc ht (hM hm)).ne'
  have hL0 : M.lcm id ≠ 0 := Finset.lcm_ne_zero_iff.mpr hnonzero
  have hdecomp := Nat.factorizationLCMLeft_mul_factorizationLCMRight hA0 hL0
  have hcop := Nat.coprime_factorizationLCMLeft_factorizationLCMRight A (M.lcm id)
  have hsplit : ℓ ∣ Nat.factorizationLCMLeft A (M.lcm id) ∨
      ℓ ∣ Nat.factorizationLCMRight A (M.lcm id) := by
    apply (hcop.isPrimePow_dvd_mul hℓpp).1
    rwa [hdecomp]
  rcases hsplit with hleft | hright
  · exact hA ℓ hℓpp (hleft.trans (Nat.factorizationLCMLeft_dvd_left A (M.lcm id)))
  · exact primePower_dvd_candidateFamily_lcm_lt hc ht htq hM hℓpp
      (hright.trans (Nat.factorizationLCMRight_dvd_right A (M.lcm id)))

/-- Candidate properties at the scale used in Lemma 12.  The lower prime-band
ratio is the fourth root of `ξ`; hence products of four band primes lie in
`(ξ*x/q,x/q]`. -/
theorem rawCandidate_elimination_properties
    {ξ : ℝ} {x p ν n : ℕ}
    (hξ : 0 < ξ) (_hξ1 : ξ < 1) (hx : 0 < x) (hp : p.Prime)
    (hn : n ∈ rawCandidates p (fourthRoot ξ)
      (fourthRoot ((x : ℝ) / (p ^ ν : ℕ)))) :
    Erdos285.Dispersion.IsKPrimeProductAway 4 (p ^ ν) n ∧
      Nat.Coprime n (p ^ ν) ∧
      ξ * x < ((p ^ ν) * n : ℕ) ∧
      (((p ^ ν) * n : ℕ) : ℝ) ≤ x ∧
      Squarefree n := by
  let q : ℕ := p ^ ν
  let c : ℝ := fourthRoot ξ
  let t : ℝ := fourthRoot ((x : ℝ) / q)
  have hqpos : 0 < q := pow_pos hp.pos ν
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hxq : 0 < (x : ℝ) / q := div_pos hxR hqR
  have hc : 0 < c := fourthRoot_pos hξ
  have ht : 0 < t := fourthRoot_pos hxq
  have hc4 : c ^ 4 = ξ := fourthRoot_pow_four hξ.le
  have ht4 : t ^ 4 = (x : ℝ) / q := fourthRoot_pow_four hxq.le
  have hn' : n ∈ rawCandidates p c t := by simpa [c, t, q] using hn
  have hnLower := rawCandidate_lower hc ht hn'
  have hnUpper := rawCandidate_upper hc.le ht.le hn'
  rw [mul_pow, hc4, ht4] at hnLower
  rw [ht4] at hnUpper
  have hLower : ξ * x < ((q * n : ℕ) : ℝ) := by
    push_cast
    calc
      ξ * (x : ℝ) = (q : ℝ) * (ξ * ((x : ℝ) / q)) := by
        field_simp [hqR.ne']
      _ < (q : ℝ) * n := mul_lt_mul_of_pos_left hnLower hqR
  have hUpper : (((q * n : ℕ) : ℝ)) ≤ x := by
    push_cast
    calc
      (q : ℝ) * n ≤ (q : ℝ) * ((x : ℝ) / q) :=
        mul_le_mul_of_nonneg_left hnUpper hqR.le
      _ = x := by field_simp [hqR.ne']
  refine ⟨?_, ?_, ?_, ?_, rawCandidate_squarefree hn'⟩
  · simpa [q, c, t] using rawCandidate_isKPrimeProductAway (p := p) (ν := ν) hp hn'
  · simpa [q, c, t] using rawCandidate_coprime_primePow (p := p) (ν := ν) hp hn'
  · simpa [q] using hLower
  · simpa [q] using hUpper

lemma rawCandidate_lt_eliminationScale
    {x p ν n : ℕ} {ξ : ℝ} (hx : 0 < x) (hp : p.Prime)
    (hn : n ∈ rawCandidates p (fourthRoot ξ)
      (fourthRoot ((x : ℝ) / (p ^ ν : ℕ)))) :
    (n : ℝ) < (x : ℝ) / (p ^ ν : ℕ) := by
  have hqpos : (0 : ℝ) < (p ^ ν : ℕ) := by
    exact_mod_cast pow_pos hp.pos ν
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hxq : 0 < (x : ℝ) / (p ^ ν : ℕ) := div_pos hxR hqpos
  have h := rawCandidate_upper_strict (fourthRoot_nonneg ξ)
    (fourthRoot_pos hxq) hn
  rwa [fourthRoot_pow_four hxq.le] at h

end

end Lemma12Candidates

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Lemma12.lean` -/

section
/-!
# Martin's large-prime-power elimination step

This file formalizes the algebraic and finite-combinatorial content of Lemma 12
in Greg Martin's *Denser Egyptian fractions*.  Its algebraic core exposes one
bounded-surjectivity interface: every residue modulo the prime power `q` is a
sum of inverses of at most `martinBlockBound x q` members of the candidate set.
The final theorems instantiate that interface from the proved dense, scaled
dispersion, and published sufficiently-large-modulus subset-sum results.

The main theorem then selects the corresponding denominator block, proves its
interval, cardinality, and largest-prime-power properties, clears denominators,
and converts the inverse congruence into strict descent of the largest exact
prime-power part of the reduced residual denominator.
-/

namespace Lemma12

open Filter Finset
open scoped BigOperators
open Erdos285.PrimePowers

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A number is a product of four pairwise distinct primes.  Martin obtains the
candidate multipliers from four separated prime intervals, which in particular
implies this predicate and injectivity of the resulting products. -/
def IsFourPrimeProduct (m : ℕ) : Prop :=
  ∃ P : Finset ℕ, P.card = 4 ∧
    (∀ p ∈ P, p.Prime) ∧ m = P.prod id

lemma IsFourPrimeProduct.pos {m : ℕ} (hm : IsFourPrimeProduct m) : 0 < m := by
  obtain ⟨P, -, hP, rfl⟩ := hm
  exact Finset.prod_pos fun p hp ↦ (hP p hp).pos

lemma IsFourPrimeProduct.ne_zero {m : ℕ} (hm : IsFourPrimeProduct m) : m ≠ 0 :=
  hm.pos.ne'

/-- The denominators corresponding to a set of auxiliary multipliers. -/
def denominatorBlock (q : ℕ) (K : Finset ℕ) : Finset ℕ :=
  K.image fun m ↦ q * m

@[simp] lemma mem_denominatorBlock {q u : ℕ} {K : Finset ℕ} :
    u ∈ denominatorBlock q K ↔ ∃ m ∈ K, q * m = u := by
  simp [denominatorBlock]

lemma card_denominatorBlock {q : ℕ} (hq : q ≠ 0) (K : Finset ℕ) :
    (denominatorBlock q K).card = K.card := by
  rw [denominatorBlock, Finset.card_image_iff]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) hab

lemma rec_sum_denominatorBlock {q : ℕ} (hq : q ≠ 0) (K : Finset ℕ) :
    UnitFractions.rec_sum (denominatorBlock q K) =
      ∑ m ∈ K, (1 : ℚ) / (q * m : ℕ) := by
  rw [denominatorBlock, UnitFractions.rec_sum, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) hab

/-- The common numerator of `∑ m⁻¹` over the least common multiple of all
members of `K`. -/
def commonReciprocalNumerator (K : Finset ℕ) : ℕ :=
  ∑ m ∈ K, K.lcm id / m

lemma rec_sum_eq_commonReciprocalNumerator_div_lcm
    {K : Finset ℕ} (hK0 : ∀ m ∈ K, m ≠ 0) :
    UnitFractions.rec_sum K =
      (commonReciprocalNumerator K : ℚ) / (K.lcm id : ℕ) := by
  have hlcm0 : K.lcm id ≠ 0 := by
    rw [Finset.lcm_ne_zero_iff]
    exact hK0
  rw [UnitFractions.rec_sum, commonReciprocalNumerator, Nat.cast_sum,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  have hmlcm : m ∣ K.lcm id := Finset.dvd_lcm hm
  have hm0 := hK0 m hm
  field_simp [hm0, hlcm0]
  exact_mod_cast (show K.lcm id = m * (K.lcm id / m) by
    rw [mul_comm, Nat.div_mul_cancel hmlcm])

/-- Martin's numerical upper bound for the selected correction block.  `rpow`
is used for the exponent `2/3`. -/
def martinBlockBound (x q : ℕ) : ℕ :=
  ⌊200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) * (Real.log x) ^ 3⌋₊

lemma martinBlockBound_cast_le {x q : ℕ} (hx : 1 ≤ x) :
    (martinBlockBound x q : ℝ) ≤
      200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) * (Real.log x) ^ 3 := by
  apply Nat.floor_le
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hx)
  positivity

/-- The large-prime-power range in Lemma 12. -/
def InEliminationRange (x q : ℕ) : Prop :=
  (x : ℝ) ^ ((1 : ℝ) / 5) ≤ q ∧
    (q : ℝ) ≤ x * (Real.log x) ^ (-22 : ℝ)

/-- The lower endpoint `x^(1/5) ≤ q` is exactly what is needed to put
the fourth-root candidate-prime scale below `q`. -/
lemma fourthRoot_div_le_of_fifthRoot_le {x q : ℕ} (hq : 0 < q)
    (h : (x : ℝ) ^ ((1 : ℝ) / 5) ≤ q) :
    Erdos285.Lemma12Candidates.fourthRoot ((x : ℝ) / q) ≤ (q : ℝ) := by
  have hrootpow : ((x : ℝ) ^ ((1 : ℝ) / 5)) ^ (5 : ℕ) = (x : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg x)]
    norm_num
  have hxq5 : (x : ℝ) ≤ (q : ℝ) ^ (5 : ℕ) := by
    rw [← hrootpow]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg x) _) h 5
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hxdiv : (x : ℝ) / q ≤ (q : ℝ) ^ (4 : ℕ) := by
    rw [div_le_iff₀ hqR]
    calc
      (x : ℝ) ≤ (q : ℝ) ^ (5 : ℕ) := hxq5
      _ = (q : ℝ) ^ (4 : ℕ) * q := by ring
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hqR.le
  rw [Erdos285.Lemma12Candidates.fourthRoot_pow_four (by positivity)]
  exact hxdiv

/-- The exact inverse-subset interface supplied by Martin's Lemmas 10 and 11.
The chosen subset is indexed by distinct auxiliary multipliers, even if their
inverse residues coincide. -/
def BoundedInverseSubsetSurjective (q C : ℕ) (M : Finset ℕ) : Prop :=
  ∀ a : ZMod q, ∃ K : Finset ℕ,
    K ⊆ M ∧ K.card ≤ C ∧
      K.sum (fun m ↦ ((m : ZMod q)⁻¹)) = a

/-- The denominator used after removing the exact `q`-part from `r.den` and
combining it with the selected auxiliary denominators.  The outer LCM is
essential: multiplying would artificially increase exponents of primes shared
by the two inputs. -/
def residualAuxiliaryLcm (r : ℚ) (q : ℕ) (K : Finset ℕ) : ℕ :=
  Nat.lcm (r.den / q) (K.lcm id)

/-- The integer numerator obtained over
`q * lcm (r.den / q) (lcm K)`. -/
def clearedNumerator (r : ℚ) (q : ℕ) (K : Finset ℕ) : ℤ :=
  r.num * (residualAuxiliaryLcm r q K / (r.den / q) : ℕ) -
    ((residualAuxiliaryLcm r q K / K.lcm id) *
      commonReciprocalNumerator K : ℕ)

/-- The LCM of a selected subfamily divides the LCM of the full candidate
family. -/
lemma lcm_dvd_lcm_of_subset {K M : Finset ℕ} (hKM : K ⊆ M) :
    K.lcm id ∣ M.lcm id :=
  Finset.lcm_mono hKM

/-- A prime power dividing an LCM already divides one of its two inputs.
This is stronger than the corresponding statement for arbitrary divisors.
The factorization-LCM decomposition avoids any multiplication of repeated
prime factors. -/
lemma isPrimePow_dvd_lcm {ℓ a b : ℕ}
    (hℓ : IsPrimePow ℓ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : ℓ ∣ Nat.lcm a b) : ℓ ∣ a ∨ ℓ ∣ b := by
  have hsplit := Nat.factorizationLCMLeft_mul_factorizationLCMRight ha hb
  have hdiv' : ℓ ∣ Nat.factorizationLCMLeft a b *
      Nat.factorizationLCMRight a b := by
    rwa [hsplit]
  rw [Nat.Coprime.isPrimePow_dvd_mul
    (Nat.coprime_factorizationLCMLeft_factorizationLCMRight a b) hℓ] at hdiv'
  exact hdiv'.imp
    (fun h ↦ h.trans (Nat.factorizationLCMLeft_dvd_left a b))
    (fun h ↦ h.trans (Nat.factorizationLCMRight_dvd_right a b))

/-- A prime power dividing the LCM of a nonzero finite family divides one of
the family members. -/
lemma isPrimePow_dvd_finsetLcm {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → ℕ} {ℓ : ℕ}
    (hℓ : IsPrimePow ℓ) (hf : ∀ i ∈ s, f i ≠ 0)
    (hdiv : ℓ ∣ s.lcm f) : ∃ i ∈ s, ℓ ∣ f i := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.lcm_empty] at hdiv
      exact (hℓ.ne_one (Nat.dvd_one.mp hdiv)).elim
  | @insert a s ha ih =>
      rw [Finset.lcm_insert] at hdiv
      have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self _ _)
      have hfs : ∀ i ∈ s, f i ≠ 0 :=
        fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have hlcms : s.lcm f ≠ 0 := by
        rw [Finset.lcm_ne_zero_iff]
        exact hfs
      rcases isPrimePow_dvd_lcm hℓ hfa hlcms hdiv with hleft | hright
      · exact ⟨a, Finset.mem_insert_self _ _, hleft⟩
      · obtain ⟨i, hi, hidiv⟩ := ih hfs hright
        exact ⟨i, Finset.mem_insert_of_mem hi, hidiv⟩

/-- A common-denominator identity for the selected block. -/
lemma residual_eq_clearedFraction
    {r : ℚ} {q : ℕ} {K : Finset ℕ}
    (hqden : q ∣ r.den) (hq0 : q ≠ 0)
    (hK0 : ∀ m ∈ K, m ≠ 0) :
    r - UnitFractions.rec_sum (denominatorBlock q K) =
      (clearedNumerator r q K : ℚ) /
        (q * residualAuxiliaryLcm r q K : ℕ) := by
  have hlcm0 : K.lcm id ≠ 0 := by
    rw [Finset.lcm_ne_zero_iff]
    exact hK0
  have hdeneq : q * (r.den / q) = r.den := Nat.mul_div_cancel' hqden
  have hblock : UnitFractions.rec_sum (denominatorBlock q K) =
      (commonReciprocalNumerator K : ℚ) / (q * K.lcm id : ℕ) := by
    rw [rec_sum_denominatorBlock hq0]
    calc
      (∑ m ∈ K, (1 : ℚ) / (q * m : ℕ)) =
          (1 : ℚ) / q * UnitFractions.rec_sum K := by
        rw [UnitFractions.rec_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        have hm0 := hK0 m hm
        push_cast
        field_simp [hq0, hm0]
      _ = (commonReciprocalNumerator K : ℚ) / (q * K.lcm id : ℕ) := by
        rw [rec_sum_eq_commonReciprocalNumerator_div_lcm hK0]
        push_cast
        field_simp [hq0, hlcm0]
  have hdeneqQ : (r.den : ℚ) = (q : ℚ) * ((r.den / q : ℕ) : ℚ) := by
    exact_mod_cast hdeneq.symm
  have hb0 : r.den / q ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd r.den_pos hqden)
      (Nat.pos_of_ne_zero hq0))
  have hD0 : residualAuxiliaryLcm r q K ≠ 0 := by
    exact Nat.lcm_ne_zero hb0 hlcm0
  have hbD : r.den / q ∣ residualAuxiliaryLcm r q K :=
    Nat.dvd_lcm_left _ _
  have hLD : K.lcm id ∣ residualAuxiliaryLcm r q K :=
    Nat.dvd_lcm_right _ _
  rw [hblock]
  conv_lhs =>
    lhs
    rw [← r.num_div_den]
  simp only [clearedNumerator, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Nat.cast_mul]
  change
    (r.num : ℚ) / (r.den : ℚ) -
        (commonReciprocalNumerator K : ℚ) /
          ((q : ℚ) * (K.lcm id : ℕ)) =
      ((r.num : ℚ) *
            (residualAuxiliaryLcm r q K / (r.den / q) : ℕ) -
          (residualAuxiliaryLcm r q K / K.lcm id : ℕ) *
            (commonReciprocalNumerator K : ℕ)) /
        ((q : ℚ) * residualAuxiliaryLcm r q K)
  rw [hdeneqQ]
  field_simp [hq0, hb0, hlcm0, hD0]
  have hDbQ :
      ((residualAuxiliaryLcm r q K / (r.den / q) : ℕ) : ℚ) *
          (r.den / q : ℕ) = residualAuxiliaryLcm r q K := by
    exact_mod_cast Nat.div_mul_cancel hbD
  have hDLQ :
      ((residualAuxiliaryLcm r q K / K.lcm id : ℕ) : ℚ) *
          (K.lcm id : ℕ) = residualAuxiliaryLcm r q K := by
    exact_mod_cast Nat.div_mul_cancel hLD
  have hfirst :
      (r.num : ℚ) * (K.lcm id : ℕ) * residualAuxiliaryLcm r q K =
        (r.den / q : ℕ) * (K.lcm id : ℕ) *
          ((r.num : ℚ) *
            (residualAuxiliaryLcm r q K / (r.den / q) : ℕ)) := by
    rw [← hDbQ]
    ring
  have hsecond :
      (r.den / q : ℕ) * (commonReciprocalNumerator K : ℕ) *
          residualAuxiliaryLcm r q K =
        (r.den / q : ℕ) * (K.lcm id : ℕ) *
          ((commonReciprocalNumerator K : ℚ) *
            (residualAuxiliaryLcm r q K / K.lcm id : ℕ)) := by
    rw [← hDLQ]
    ring
  rw [sub_mul, hfirst, hsecond]
  ring

/-- In `ZMod q`, the common reciprocal numerator is the LCM of `K` times the
sum of the inverse residues. -/
lemma commonReciprocalNumerator_cast
    {q : ℕ} [NeZero q] {K : Finset ℕ}
    (hcop : ∀ m ∈ K, Nat.Coprime m q) :
    (commonReciprocalNumerator K : ZMod q) =
      ((K.lcm id : ℕ) : ZMod q) * K.sum (fun m ↦ ((m : ZMod q)⁻¹)) := by
  rw [commonReciprocalNumerator, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmlcm : m ∣ K.lcm id := Finset.dvd_lcm hm
  have hunit : IsUnit (m : ZMod q) :=
    (ZMod.isUnit_iff_coprime m q).mpr (hcop m hm)
  have hcastLcm : (m : ZMod q) * ((K.lcm id / m : ℕ) : ZMod q) =
      ((K.lcm id : ℕ) : ZMod q) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hmlcm]
  calc
    ((K.lcm id / m : ℕ) : ZMod q) =
        (m : ZMod q)⁻¹ * ((K.lcm id : ℕ) : ZMod q) := by
      calc
        ((K.lcm id / m : ℕ) : ZMod q) =
            ((m : ZMod q)⁻¹ * (m : ZMod q)) *
              ((K.lcm id / m : ℕ) : ZMod q) := by
                rw [ZMod.inv_mul_of_unit _ hunit, one_mul]
        _ = (m : ZMod q)⁻¹ *
              ((m : ZMod q) * ((K.lcm id / m : ℕ) : ZMod q)) := by ring
        _ = (m : ZMod q)⁻¹ * ((K.lcm id : ℕ) : ZMod q) := by rw [hcastLcm]
    _ = ((K.lcm id : ℕ) : ZMod q) * (m : ZMod q)⁻¹ := by ac_rfl

/-- Cast an exact natural quotient into `ZMod q` by multiplying with the
inverse of its (unit) divisor. -/
lemma natCast_div_eq_mul_inv {q a d : ℕ} [NeZero q]
    (hda : d ∣ a) (hdunit : IsUnit (d : ZMod q)) :
    ((a / d : ℕ) : ZMod q) = (a : ZMod q) * (d : ZMod q)⁻¹ := by
  have hcast : (d : ZMod q) * ((a / d : ℕ) : ZMod q) = (a : ZMod q) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hda]
  calc
    ((a / d : ℕ) : ZMod q) =
        (d : ZMod q)⁻¹ * ((d : ZMod q) * ((a / d : ℕ) : ZMod q)) := by
      rw [← mul_assoc, ZMod.inv_mul_of_unit _ hdunit, one_mul]
    _ = (d : ZMod q)⁻¹ * (a : ZMod q) := by rw [hcast]
    _ = (a : ZMod q) * (d : ZMod q)⁻¹ := by ac_rfl

/-- The inverse congruence selected by Lemma 11 makes the cleared residual
numerator divisible by `q`. -/
lemma clearedNumerator_dvd_of_inverseCongruence
    {r : ℚ} {q : ℕ} {K : Finset ℕ}
    (hqpart : q ∈ primePowerParts r.den)
    (hcop : ∀ m ∈ K, Nat.Coprime m q)
    (hcong : K.sum (fun m ↦ ((m : ZMod q)⁻¹)) =
      (r.num : ZMod q) * ((r.den / q : ℕ) : ZMod q)⁻¹) :
    (q : ℤ) ∣ clearedNumerator r q K := by
  have hqspec := (mem_primePowerParts r.den_ne_zero).mp hqpart
  let _ : NeZero q := ⟨hqspec.1.ne_zero⟩
  let b : ℕ := r.den / q
  let L : ℕ := K.lcm id
  let D : ℕ := residualAuxiliaryLcm r q K
  have hbunit : IsUnit (b : ZMod q) :=
    (ZMod.isUnit_iff_coprime (r.den / q) q).mpr hqspec.2.2.symm
  have hLcop : Nat.Coprime L q := by
    apply Nat.Coprime.of_dvd_left
        (show K.lcm id ∣ K.prod id by
          apply Finset.lcm_dvd
          intro m hm
          exact Finset.dvd_prod_of_mem id hm)
    rw [Nat.coprime_prod_left_iff]
    exact hcop
  have hLunit : IsUnit (L : ZMod q) :=
    (ZMod.isUnit_iff_coprime L q).mpr hLcop
  have hbD : b ∣ D := Nat.dvd_lcm_left _ _
  have hLD : L ∣ D := Nat.dvd_lcm_right _ _
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [clearedNumerator, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Nat.cast_mul]
  change
    (r.num : ZMod q) * ((D / b : ℕ) : ZMod q) -
      ((D / L : ℕ) : ZMod q) * (commonReciprocalNumerator K : ZMod q) = 0
  rw [natCast_div_eq_mul_inv hbD hbunit,
    natCast_div_eq_mul_inv hLD hLunit,
    commonReciprocalNumerator_cast hcop, hcong]
  calc
    (r.num : ZMod q) * ((D : ZMod q) * (b : ZMod q)⁻¹) -
          ((D : ZMod q) * (L : ZMod q)⁻¹) *
            (((L : ZMod q) *
              ((r.num : ZMod q) * (b : ZMod q)⁻¹))) =
        (D : ZMod q) * (r.num : ZMod q) * (b : ZMod q)⁻¹ *
          (1 - (L : ZMod q)⁻¹ * (L : ZMod q)) := by ring
    _ = 0 := by
      rw [ZMod.inv_mul_of_unit _ hLunit]
      ring

/-- The reduced denominator after the congruence step divides the exact LCM of
the old denominator with its `q`-part removed and the selected auxiliaries. -/
lemma residual_den_dvd_auxiliaryLcm
    {r : ℚ} {q : ℕ} {K : Finset ℕ}
    (hqpart : q ∈ primePowerParts r.den)
    (hK0 : ∀ m ∈ K, m ≠ 0)
    (hcop : ∀ m ∈ K, Nat.Coprime m q)
    (hcong : K.sum (fun m ↦ ((m : ZMod q)⁻¹)) =
      (r.num : ZMod q) * ((r.den / q : ℕ) : ZMod q)⁻¹) :
    (r - UnitFractions.rec_sum (denominatorBlock q K)).den ∣
      residualAuxiliaryLcm r q K := by
  have hqspec := (mem_primePowerParts r.den_ne_zero).mp hqpart
  have hcleared := residual_eq_clearedFraction hqspec.2.1 hqspec.1.ne_zero hK0
  obtain ⟨z, hz⟩ := clearedNumerator_dvd_of_inverseCongruence hqpart hcop hcong
  have hq0Z : (q : ℤ) ≠ 0 := by exact_mod_cast hqspec.1.ne_zero
  have haux0 : (residualAuxiliaryLcm r q K : ℤ) ≠ 0 := by
    have hbpos : 0 < r.den / q :=
      Nat.div_pos (Nat.le_of_dvd r.den_pos hqspec.2.1) hqspec.1.pos
    have hL0 : K.lcm id ≠ 0 := by
      rw [Finset.lcm_ne_zero_iff]
      exact hK0
    exact_mod_cast Nat.lcm_ne_zero hbpos.ne' hL0
  have heq : r - UnitFractions.rec_sum (denominatorBlock q K) =
      (z : ℚ) / (residualAuxiliaryLcm r q K : ℕ) := by
    rw [hcleared, hz]
    push_cast
    field_simp [hqspec.1.ne_zero]
  have hdenZ :
      ((r - UnitFractions.rec_sum (denominatorBlock q K)).den : ℤ) ∣
        (residualAuxiliaryLcm r q K : ℤ) := by
    have := Rat.den_dvd z (residualAuxiliaryLcm r q K : ℤ)
    have hrat : Rat.divInt z (residualAuxiliaryLcm r q K : ℤ) =
        r - UnitFractions.rec_sum (denominatorBlock q K) := by
      rw [Rat.divInt_eq_div]
      exact heq.symm
    rw [hrat] at this
    exact this
  exact_mod_cast hdenZ

/-- If every prime power dividing the ambient auxiliary LCM is below `q`,
then denominator divisibility gives strict largest-prime-power descent. -/
lemma largestPrimePowerPart_residual_lt
    {r : ℚ} {q : ℕ} {K M : Finset ℕ}
    (hqpart : q ∈ primePowerParts r.den)
    (hKM : K ⊆ M)
    (hden : (r - UnitFractions.rec_sum (denominatorBlock q K)).den ∣
      residualAuxiliaryLcm r q K)
    (hbound : ∀ ℓ : ℕ, IsPrimePow ℓ →
      ℓ ∣ residualAuxiliaryLcm r q M → ℓ < q) :
    largestPrimePowerPart
        (r - UnitFractions.rec_sum (denominatorBlock q K)).den < q := by
  let s : ℚ := r - UnitFractions.rec_sum (denominatorBlock q K)
  have hqspec := (mem_primePowerParts r.den_ne_zero).mp hqpart
  have haux : residualAuxiliaryLcm r q K ∣ residualAuxiliaryLcm r q M := by
    exact lcm_dvd_lcm dvd_rfl (lcm_dvd_lcm_of_subset hKM)
  by_cases hs : 2 ≤ s.den
  · have hmem : largestPrimePowerPart s.den ∈ primePowerParts s.den :=
      largestPrimePowerPart_mem hs
    have hspec := (mem_primePowerParts s.den_ne_zero).mp hmem
    exact hbound _ hspec.1 (hspec.2.1.trans (hden.trans haux))
  · have hsmall : s.den < 2 := Nat.lt_of_not_ge hs
    have hempty : primePowerParts s.den = ∅ := primePowerParts_empty_iff.mpr hsmall
    have hzero : largestPrimePowerPart s.den = 0 := by
      rw [largestPrimePowerPart, hempty]
      simp
    change largestPrimePowerPart s.den < q
    rw [hzero]
    exact hqspec.1.pos

/-- The finite candidate data used after the analytic prime-interval and
dispersion estimates have been discharged. -/
structure CandidateData (ξ : ℝ) (x q : ℕ) (r : ℚ) (M : Finset ℕ) : Prop where
  range : InEliminationRange x q
  q_part : q ∈ primePowerParts r.den
  four_primes : ∀ m ∈ M, IsFourPrimeProduct m
  coprime : ∀ m ∈ M, Nat.Coprime m q
  interval : ∀ m ∈ M,
    ξ * x ≤ (q * m : ℕ) ∧ (q * m : ℕ) ≤ x
  largest_part : ∀ m ∈ M, largestPrimePowerPart (q * m) = q
  auxiliary_bound : ∀ ℓ : ℕ, IsPrimePow ℓ →
    ℓ ∣ residualAuxiliaryLcm r q M → ℓ < q

/-- A four-prime-product-away witness in the dispersion module supplies the
local product predicate used by the elimination algebra. -/
lemma isFourPrimeProduct_of_isKPrimeProductAway
    {q m : ℕ} (hm : Erdos285.Dispersion.IsKPrimeProductAway 4 q m) :
    IsFourPrimeProduct m := by
  obtain ⟨P, hPcard, hP, hprod⟩ := hm
  exact ⟨P, hPcard, fun p hp ↦ (hP p hp).1, hprod⟩

/-- Build all of `CandidateData` from the actual four-prime family.  In
particular, the `auxiliary_bound` field is proved for the exact double LCM,
using the old-cofactor hypothesis and the squarefree candidate-LCM theorem. -/
theorem candidateData_of_rawCandidateFamily
    {ξ : ℝ} {x p ν : ℕ} {r : ℚ} {M : Finset ℕ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hx : 0 < x)
    (hp : p.Prime) (hν : 0 < ν)
    (hrange : InEliminationRange x (p ^ ν))
    (hqpart : p ^ ν ∈ primePowerParts r.den)
    (hM : M ⊆ Erdos285.Lemma12Candidates.rawCandidates p
      (Erdos285.Lemma12Candidates.fourthRoot ξ)
      (Erdos285.Lemma12Candidates.fourthRoot
        ((x : ℝ) / (p ^ ν : ℕ))))
    (hcofactor : ∀ ℓ : ℕ, IsPrimePow ℓ →
      ℓ ∣ r.den / (p ^ ν) → ℓ < p ^ ν) :
    CandidateData ξ x (p ^ ν) r M := by
  let c : ℝ := Erdos285.Lemma12Candidates.fourthRoot ξ
  let t : ℝ := Erdos285.Lemma12Candidates.fourthRoot
    ((x : ℝ) / (p ^ ν : ℕ))
  have hc : 0 ≤ c := Erdos285.Lemma12Candidates.fourthRoot_nonneg ξ
  have ht : 0 ≤ t := Erdos285.Lemma12Candidates.fourthRoot_nonneg _
  have htq : t ≤ ((p ^ ν : ℕ) : ℝ) := by
    exact fourthRoot_div_le_of_fifthRoot_le (pow_pos hp.pos ν) hrange.1
  refine ⟨hrange, hqpart, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    exact isFourPrimeProduct_of_isKPrimeProductAway (q := p ^ ν)
      (Erdos285.Lemma12Candidates.rawCandidate_isKPrimeProductAway
        (ν := ν) hp (hM hm))
  · intro m hm
    exact Erdos285.Lemma12Candidates.rawCandidate_coprime_primePow hp (hM hm)
  · intro m hm
    have hprops := Erdos285.Lemma12Candidates.rawCandidate_elimination_properties
      hξ hξ1 hx hp (hM hm)
    exact ⟨hprops.2.2.1.le, by exact_mod_cast hprops.2.2.2.1⟩
  · intro m hm
    exact Erdos285.Lemma12Candidates.largestPrimePowerPart_primePow_mul_rawCandidate
      hp hν hc ht (by simpa [t] using htq) (by simpa [c, t] using hM hm)
  · intro ℓ hℓ hℓdvd
    have hqspec := (mem_primePowerParts r.den_ne_zero).mp hqpart
    have hb0 : r.den / (p ^ ν) ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd r.den_pos hqspec.2.1) hqspec.1.pos).ne'
    apply Erdos285.Lemma12Candidates.primePower_dvd_lcm_candidateFamily_lt
      hb0 hc ht (by simpa [t] using htq) (by simpa [c, t] using hM)
      hcofactor hℓ
    simpa [residualAuxiliaryLcm] using hℓdvd

/-- The algebraic/finite form of Martin's Lemma 12.

The analytic Lemmas 10 and 11 are used only through `hsurj`.  All remaining
conclusions of Lemma 12 are constructed here. -/
theorem largePrimePowerElimination
    {ξ : ℝ} {x q : ℕ} {r : ℚ} {M : Finset ℕ}
    (hdata : CandidateData ξ x q r M)
    (hsurj : BoundedInverseSubsetSurjective q (martinBlockBound x q) M) :
    ∃ U : Finset ℕ,
      U.card ≤ martinBlockBound x q ∧
      (∀ u ∈ U, ξ * x ≤ (u : ℝ) ∧ (u : ℝ) ≤ x) ∧
      (∀ u ∈ U, largestPrimePowerPart u = q) ∧
      Nat.Coprime (r - UnitFractions.rec_sum U).den q ∧
      largestPrimePowerPart (r - UnitFractions.rec_sum U).den < q := by
  have hqspec := (mem_primePowerParts r.den_ne_zero).mp hdata.q_part
  let _ : NeZero q := ⟨hqspec.1.ne_zero⟩
  let target : ZMod q :=
    (r.num : ZMod q) * ((r.den / q : ℕ) : ZMod q)⁻¹
  obtain ⟨K, hKM, hKcard, hKsum⟩ := hsurj target
  let U := denominatorBlock q K
  have hK0 : ∀ m ∈ K, m ≠ 0 := by
    intro m hm
    exact (hdata.four_primes m (hKM hm)).ne_zero
  have hKcop : ∀ m ∈ K, Nat.Coprime m q :=
    fun m hm ↦ hdata.coprime m (hKM hm)
  have hden : (r - UnitFractions.rec_sum U).den ∣
      residualAuxiliaryLcm r q K := by
    exact residual_den_dvd_auxiliaryLcm hdata.q_part hK0 hKcop hKsum
  have hKLCoprime : Nat.Coprime (K.lcm id) q := by
    apply Nat.Coprime.of_dvd_left
        (show K.lcm id ∣ K.prod id by
          apply Finset.lcm_dvd
          intro m hm
          exact Finset.dvd_prod_of_mem id hm)
    rw [Nat.coprime_prod_left_iff]
    exact hKcop
  have hauxCoprime : Nat.Coprime (residualAuxiliaryLcm r q K) q := by
    apply Nat.Coprime.of_dvd_left
        (show residualAuxiliaryLcm r q K ∣ (r.den / q) * K.lcm id by
          exact Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
    exact Nat.Coprime.mul_left hqspec.2.2.symm hKLCoprime
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_denominatorBlock hqspec.1.ne_zero]
    exact hKcard
  · intro u hu
    obtain ⟨m, hm, rfl⟩ := mem_denominatorBlock.mp hu
    refine ⟨(hdata.interval m (hKM hm)).1, ?_⟩
    exact_mod_cast (hdata.interval m (hKM hm)).2
  · intro u hu
    obtain ⟨m, hm, rfl⟩ := mem_denominatorBlock.mp hu
    exact hdata.largest_part m (hKM hm)
  · exact Nat.Coprime.of_dvd_left hden hauxCoprime
  · exact largestPrimePowerPart_residual_lt hdata.q_part hKM hden hdata.auxiliary_bound

end

end Lemma12

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Lemma12Numerics.lean` -/

section
/-!
# Uniform numerical estimates for Martin's Lemma 12

This file contains the elementary (but rather exponent-heavy) estimates which
put the four-prime family from `Lemma12Candidates` into the hypotheses of the
dispersion/subset-sum theorem.  All estimates are uniform in the prime power
`q` in the enlarged elimination range

`x^(1/5) <= q <= x * log(x)^(-30)`.

The exponent `30` leaves enough slack to use the explicit PNT lower bound in
`Lemma12Candidates` without formalising a sharper smooth-number estimate.
-/

namespace Lemma12Numerics

open Filter Finset Real
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos285.Lemma12Candidates

/-- The enlarged-log-saving range used by the Lean implementation of Lemma 12. -/
def InStrongEliminationRange (x q : ℕ) : Prop :=
  (x : ℝ) ^ ((1 : ℝ) / 5) ≤ q ∧
    (q : ℝ) ≤ x * Real.log x ^ (-30 : ℝ)

/-- The upper endpoint of the strong elimination range is equivalently a
uniform lower bound `log(x)^30 <= x/q`. -/
lemma log_pow_thirty_le_div {x q : ℕ} (hq : 0 < q)
    (hlog : 0 < Real.log (x : ℝ))
    (hupper : (q : ℝ) ≤ x * Real.log x ^ (-30 : ℝ)) :
    Real.log (x : ℝ) ^ (30 : ℕ) ≤ (x : ℝ) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpow : 0 < Real.log (x : ℝ) ^ (30 : ℕ) := pow_pos hlog _
  rw [show (-30 : ℝ) = -(30 : ℝ) by norm_num,
    Real.rpow_neg hlog.le] at hupper
  rw [show (30 : ℝ) = ((30 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast] at hupper
  rw [le_div_iff₀ hqR]
  calc
    Real.log (x : ℝ) ^ (30 : ℕ) * q
        ≤ Real.log (x : ℝ) ^ (30 : ℕ) *
            ((x : ℝ) * (Real.log (x : ℝ) ^ (30 : ℕ))⁻¹) := by
          exact mul_le_mul_of_nonneg_left hupper hpow.le
    _ = (x : ℝ) := by field_simp [hpow.ne']

/-- A convenient integral-power lower bound for the candidate-prime scale. -/
lemma log_pow_seven_le_fourthRoot_div {x q : ℕ} (hq : 0 < q)
    (hlog : 1 ≤ Real.log (x : ℝ))
    (hupper : (q : ℝ) ≤ x * Real.log x ^ (-30 : ℝ)) :
    Real.log (x : ℝ) ^ (7 : ℕ) ≤
      fourthRoot ((x : ℝ) / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hxR : (0 : ℝ) < x := by
    have hlogpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hlog
    have hxone : 1 < (x : ℝ) :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ x)).mp hlogpos
    linarith
  have hratio : 0 ≤ (x : ℝ) / q := (div_pos hxR hqR).le
  have h30 := log_pow_thirty_le_div hq (lt_of_lt_of_le (by norm_num) hlog) hupper
  have h28_30 : Real.log (x : ℝ) ^ (28 : ℕ) ≤
      Real.log (x : ℝ) ^ (30 : ℕ) := by
    exact pow_le_pow_right₀ hlog (by norm_num)
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
      (fourthRoot_nonneg _)
  rw [← pow_mul, show 7 * 4 = 28 by norm_num, fourthRoot_pow_four hratio]
  exact h28_30.trans h30

/-- The candidate-prime PNT estimate can be made uniform in the single prime
which is erased from the band.  This uniformity is needed because the base
prime of `q` varies with `x`. -/
theorem eventually_candidatePrimes_card_lower_uniform {c : ℝ}
    (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t : ℝ in atTop, ∀ p : ℕ,
      (1 - c) * t / (8 * Real.log t) ≤
        ((candidatePrimes p c t).card : ℝ) := by
  have hgrowth : Tendsto (fun t : ℝ ↦ (1 - c) * t / (8 * Real.log t))
      atTop atTop := by
    have h := (Real.tendsto_exp_div_pow_atTop 1).const_mul_atTop
      (show 0 < (1 - c) / 8 by positivity)
    refine (h.comp Real.tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp_apply, pow_one]
    rw [Real.exp_log ht]
    ring
  filter_upwards [eventually_primeBand_card_lower hc hc1,
    hgrowth.eventually_ge_atTop 1, eventually_gt_atTop 2]
      with t hband hgrow ht
  intro p
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  let A : ℝ := (1 - c) * t / (8 * Real.log t)
  have htwice : 2 * A = (1 - c) * t / (4 * Real.log t) := by
    dsimp [A]
    ring
  have hband2 : 2 * A ≤ ((primeBand c t).card : ℝ) := by
    rwa [htwice]
  have hcardRel : ((primeBand c t).card : ℝ) ≤
      (candidatePrimes p c t).card + 1 := by
    exact_mod_cast primeBand_card_le_candidatePrimes_card_add_one p c t
  have hA : 1 ≤ A := by simpa [A] using hgrow
  dsimp [A] at *
  linarith

/-- Uniform PNT lower bound for four-prime products. -/
theorem eventually_rawCandidates_card_lower_uniform {c : ℝ}
    (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t : ℝ in atTop, ∀ p : ℕ,
      (((1 - c) * t / (16 * Real.log t)) ^ 4) / 24 ≤
        ((rawCandidates p c t).card : ℝ) := by
  have hgrowth : Tendsto (fun t : ℝ ↦ (1 - c) * t / (8 * Real.log t))
      atTop atTop := by
    have h := (Real.tendsto_exp_div_pow_atTop 1).const_mul_atTop
      (show 0 < (1 - c) / 8 by positivity)
    refine (h.comp Real.tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp_apply, pow_one]
    rw [Real.exp_log ht]
    ring
  filter_upwards [eventually_candidatePrimes_card_lower_uniform hc hc1,
    hgrowth.eventually_ge_atTop 8, eventually_gt_atTop 2]
      with t hprime hgrowth8 ht
  intro p
  let A : ℝ := (1 - c) * t / (8 * Real.log t)
  have hcard8 : 8 ≤ (candidatePrimes p c t).card := by
    exact_mod_cast hgrowth8.trans (hprime p)
  have hhalf : (1 - c) * t / (16 * Real.log t) ≤
      (((candidatePrimes p c t).card + 1 - 4 : ℕ) : ℝ) := by
    have hhalfCard : (1 - c) * t / (16 * Real.log t) ≤
        ((candidatePrimes p c t).card : ℝ) / 2 := by
      calc
        (1 - c) * t / (16 * Real.log t) = A / 2 := by dsimp [A]; ring
        _ ≤ ((candidatePrimes p c t).card : ℝ) / 2 := by gcongr; exact hprime p
    have hfour : 4 ≤ (candidatePrimes p c t).card := by omega
    calc
      (1 - c) * t / (16 * Real.log t) ≤
          ((candidatePrimes p c t).card : ℝ) / 2 := hhalfCard
      _ ≤ (((candidatePrimes p c t).card + 1 - 4 : ℕ) : ℝ) := by
        rw [show (candidatePrimes p c t).card + 1 - 4 =
          (candidatePrimes p c t).card - 3 by omega, Nat.cast_sub (by omega)]
        push_cast
        have hc8 : (8 : ℝ) ≤ (candidatePrimes p c t).card := by
          exact_mod_cast hcard8
        nlinarith
  have hbaseNonneg : 0 ≤ (1 - c) * t / (16 * Real.log t) := by
    exact (div_nonneg
      (mul_nonneg (sub_nonneg.mpr hc1.le) (by linarith))
      (mul_nonneg (by norm_num) (Real.log_pos (by linarith)).le))
  calc
    (((1 - c) * t / (16 * Real.log t)) ^ 4) / 24 ≤
        (((((candidatePrimes p c t).card + 1 - 4 : ℕ) : ℝ) ^ 4) / 24) := by
      gcongr
    _ ≤ ((rawCandidates p c t).card : ℝ) := by
      have hraw := rawCandidates_card_lower p c t
      norm_num at hraw
      exact hraw

/-- Uniform extraction form of the preceding PNT estimate. -/
theorem eventually_exists_rawCandidates_subset_uniform {c : ℝ}
    (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t : ℝ in atTop, ∀ (p C : ℕ),
      (C : ℝ) ≤ (((1 - c) * t / (16 * Real.log t)) ^ 4) / 24 →
      ∃ M ⊆ rawCandidates p c t, M.card = C := by
  filter_upwards [eventually_rawCandidates_card_lower_uniform hc hc1]
    with t ht
  intro p C hC
  apply Finset.exists_subset_card_eq
  exact_mod_cast hC.trans (ht p)

/-- In the strong elimination range the fourth-root scale eventually lies in
the (uniform-in-the-erased-prime) PNT regime. -/
theorem eventually_rawCandidates_subset_at_elimination_scale {ξ : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    ∀ᶠ x : ℕ in atTop, ∀ (q p C : ℕ), 0 < q →
      (q : ℝ) ≤ x * Real.log x ^ (-30 : ℝ) →
      (C : ℝ) ≤
        (((1 - fourthRoot ξ) * fourthRoot ((x : ℝ) / q) /
            (16 * Real.log (fourthRoot ((x : ℝ) / q)))) ^ 4) / 24 →
      ∃ M ⊆ rawCandidates p (fourthRoot ξ)
          (fourthRoot ((x : ℝ) / q)), M.card = C := by
  have hc : 0 < fourthRoot ξ := fourthRoot_pos hξ
  have hc1 : fourthRoot ξ < 1 := fourthRoot_lt_one hξ1
  obtain ⟨T, hT⟩ := (eventually_atTop.1
    (eventually_exists_rawCandidates_subset_uniform hc hc1))
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogTop.eventually_ge_atTop (max T 1)] with x hlogMax
  intro q p C hq hupper hC
  have hlog : 1 ≤ Real.log (x : ℝ) := (le_max_right T 1).trans hlogMax
  have hxT : T ≤ Real.log (x : ℝ) ^ (7 : ℕ) := by
    calc
      T ≤ Real.log (x : ℝ) := (le_max_left T 1).trans hlogMax
      _ ≤ Real.log (x : ℝ) ^ (7 : ℕ) := by
        simpa using pow_le_pow_right₀ hlog (by norm_num : 1 ≤ (7 : ℕ))
  have htT : T ≤ fourthRoot ((x : ℝ) / q) :=
    hxT.trans (log_pow_seven_le_fourthRoot_div hq hlog hupper)
  exact hT _ htT p C hC

/-! ## Power bookkeeping -/

lemma log_pow_ten_le_rpow_one_third {L y : ℝ}
    (hL : 0 ≤ L) (_hy : 0 ≤ y) (h30 : L ^ (30 : ℕ) ≤ y) :
    L ^ (10 : ℕ) ≤ y ^ ((1 : ℝ) / 3) := by
  calc
    L ^ (10 : ℕ) = (L ^ (30 : ℕ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast]
      rw [← Real.rpow_mul hL]
      norm_num
    _ ≤ y ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (pow_nonneg hL 30) h30 (by norm_num)

lemma rpow_two_thirds_mul_log_pow_ten_le {L y : ℝ}
    (hL : 0 ≤ L) (hy : 0 ≤ y) (h30 : L ^ (30 : ℕ) ≤ y) :
    y ^ ((2 : ℝ) / 3) * L ^ (10 : ℕ) ≤ y := by
  rcases hy.eq_or_lt with rfl | hypos
  · simp
  calc
    y ^ ((2 : ℝ) / 3) * L ^ (10 : ℕ) ≤
        y ^ ((2 : ℝ) / 3) * y ^ ((1 : ℝ) / 3) := by
      exact mul_le_mul_of_nonneg_left
        (log_pow_ten_le_rpow_one_third hL hy h30)
        (Real.rpow_nonneg hy _)
    _ = y ^ (((2 : ℝ) / 3) + (1 : ℝ) / 3) :=
      (Real.rpow_add hypos _ _).symm
    _ = y := by norm_num

lemma rpow_two_thirds_log_bound {a L y : ℝ}
    (ha : 0 ≤ a) (hL : 1 ≤ L) (hy : 0 ≤ y)
    (h30 : L ^ (30 : ℕ) ≤ y) (hconst : 4800 ≤ a ^ 4 * L ^ 3) :
    200 * y ^ ((2 : ℝ) / 3) * L ^ 3 ≤
      a ^ 4 * y / (24 * L ^ 4) := by
  have hpow7_10 : L ^ (7 : ℕ) ≤ L ^ (10 : ℕ) :=
    pow_le_pow_right₀ hL (by norm_num)
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hycore := rpow_two_thirds_mul_log_pow_ten_le hL0 hy h30
  have hscaled : 4800 * (y ^ ((2 : ℝ) / 3) * L ^ 7) ≤ a ^ 4 * y := by
    calc
      4800 * (y ^ ((2 : ℝ) / 3) * L ^ 7) ≤
          (a ^ 4 * L ^ 3) * (y ^ ((2 : ℝ) / 3) * L ^ 7) := by
        exact mul_le_mul_of_nonneg_right hconst
          (mul_nonneg (Real.rpow_nonneg hy _) (pow_nonneg hL0 7))
      _ = a ^ 4 * (y ^ ((2 : ℝ) / 3) * L ^ 10) := by ring
      _ ≤ a ^ 4 * y := mul_le_mul_of_nonneg_left hycore (pow_nonneg ha 4)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  apply (le_div_iff₀ (mul_pos (by norm_num) (pow_pos hLpos 4))).2
  calc
    (200 * y ^ ((2 : ℝ) / 3) * L ^ 3) * (24 * L ^ 4) =
        4800 * (y ^ ((2 : ℝ) / 3) * L ^ 7) := by ring
    _ ≤ a ^ 4 * y := hscaled

/-- The numerical block size is eventually below the explicit PNT lower
bound for the four-prime candidate family, uniformly in `q`. -/
theorem eventually_martinBlockBound_le_candidateLower {ξ : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    ∀ᶠ x : ℕ in atTop, ∀ q : ℕ, 0 < q → InStrongEliminationRange x q →
      (Erdos285.Lemma12.martinBlockBound x q : ℝ) ≤
        (((1 - fourthRoot ξ) * fourthRoot ((x : ℝ) / q) /
            (16 * Real.log (fourthRoot ((x : ℝ) / q)))) ^ 4) / 24 := by
  let a : ℝ := (1 - fourthRoot ξ) / 16
  have hc1 : fourthRoot ξ < 1 := fourthRoot_lt_one hξ1
  have ha : 0 < a := by dsimp [a]; positivity
  have ha4 : 0 < a ^ (4 : ℕ) := pow_pos ha _
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogTop.eventually_ge_atTop
    (max 2 (4800 / a ^ (4 : ℕ)))] with x hlogLarge
  intro q hq hrange
  let L : ℝ := Real.log (x : ℝ)
  let y : ℝ := (x : ℝ) / q
  let t : ℝ := fourthRoot y
  have hL2 : 2 ≤ L := (le_max_left 2 (4800 / a ^ (4 : ℕ))).trans hlogLarge
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hxpos : (0 : ℝ) < x := by
    have hxone : 1 < (x : ℝ) :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ x)).mp hLpos
    linarith
  have hxNat : 0 < x := by exact_mod_cast hxpos
  have hypos : 0 < y := div_pos hxpos hqR
  have htpos : 0 < t := fourthRoot_pos hypos
  have h30 : L ^ (30 : ℕ) ≤ y := by
    exact log_pow_thirty_le_div hq hLpos hrange.2
  have hconst0 : 4800 / a ^ (4 : ℕ) ≤ L :=
    (le_max_right 2 (4800 / a ^ (4 : ℕ))).trans hlogLarge
  have hconstLinear : 4800 ≤ a ^ (4 : ℕ) * L := by
    rw [div_le_iff₀ ha4] at hconst0
    nlinarith
  have hL_le_cube : L ≤ L ^ (3 : ℕ) := by
    simpa using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (3 : ℕ))
  have hconst : 4800 ≤ a ^ (4 : ℕ) * L ^ (3 : ℕ) :=
    hconstLinear.trans (mul_le_mul_of_nonneg_left hL_le_cube ha4.le)
  have hrealBound :
      200 * y ^ ((2 : ℝ) / 3) * L ^ 3 ≤
        a ^ 4 * y / (24 * L ^ 4) :=
    rpow_two_thirds_log_bound ha.le hL1 hypos.le h30 hconst
  have hqleX : (q : ℝ) ≤ x := by
    calc
      (q : ℝ) ≤ (x : ℝ) * L ^ (-30 : ℝ) := hrange.2
      _ ≤ (x : ℝ) * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)) hxpos.le
      _ = x := mul_one _
  have htq : t ≤ (q : ℝ) := by
    simpa [t, y] using
      (Erdos285.Lemma12.fourthRoot_div_le_of_fifthRoot_le hq hrange.1)
  have htx : t ≤ (x : ℝ) := htq.trans hqleX
  have hlogtpos : 0 < Real.log t := by
    have htlog7 : L ^ (7 : ℕ) ≤ t := by
      simpa [L, y, t] using
        (log_pow_seven_le_fourthRoot_div hq hL1 hrange.2)
    have hLlt : 1 < L := by linarith
    have hOnePow : (1 : ℝ) < L ^ (7 : ℕ) := by
      calc
        (1 : ℝ) < L := hLlt
        _ ≤ L ^ (7 : ℕ) := by
          simpa using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (7 : ℕ))
    have htone : 1 < t := hOnePow.trans_le htlog7
    exact Real.log_pos htone
  have hlogtle : Real.log t ≤ L := by
    exact Real.log_le_log htpos htx
  have hfrac : a * t / L ≤ a * t / Real.log t :=
    div_le_div_of_nonneg_left (mul_nonneg ha.le htpos.le) hlogtpos hlogtle
  have hpowfrac : (a * t / L) ^ (4 : ℕ) ≤
      (a * t / Real.log t) ^ (4 : ℕ) := by
    exact pow_le_pow_left₀ (by positivity) hfrac _
  have ht4 : t ^ (4 : ℕ) = y := fourthRoot_pow_four hypos.le
  calc
    (Erdos285.Lemma12.martinBlockBound x q : ℝ) ≤
        200 * y ^ ((2 : ℝ) / 3) * L ^ 3 := by
      simpa [L, y] using Erdos285.Lemma12.martinBlockBound_cast_le
        (x := x) (q := q) hxNat
    _ ≤ a ^ 4 * y / (24 * L ^ 4) := hrealBound
    _ = (a * t / L) ^ 4 / 24 := by
      have heq : (a * t / L) ^ 4 / 24 =
          a ^ 4 * y / (24 * L ^ 4) := by
        rw [div_pow, mul_pow, ht4]
        ring
      exact heq.symm
    _ ≤ (a * t / Real.log t) ^ 4 / 24 := by gcongr
    _ = (((1 - fourthRoot ξ) * t / (16 * Real.log t)) ^ 4) / 24 := by
      dsimp [a]
      congr 2
      ring
    _ = (((1 - fourthRoot ξ) * fourthRoot ((x : ℝ) / q) /
          (16 * Real.log (fourthRoot ((x : ℝ) / q)))) ^ 4) / 24 := by
      rfl

lemma q_cast_le_x_of_strongRange {x q : ℕ}
    (hlog : 1 ≤ Real.log (x : ℝ))
    (hrange : InStrongEliminationRange x q) : (q : ℝ) ≤ x := by
  calc
    (q : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) ^ (-30 : ℝ) := hrange.2
    _ ≤ (x : ℝ) * 1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hlog (by norm_num)) (by positivity)
    _ = x := mul_one _

/-- The two numerical hypotheses in Martin's prescribed subset-sum lemma,
plus the older dispersion threshold, in the concrete `k = 4` form. -/
lemma fourPrime_subsetSum_and_dispersion_thresholds
    {x q : ℕ} (hq : 0 < q) (hL2 : 2 ≤ Real.log (x : ℝ))
    (hLLq2 : 2 ≤ Real.log (Real.log (q : ℝ)))
    (hrange : InStrongEliminationRange x q) :
    let B : ℝ := (x : ℝ) / q
    Real.log q ^ ((3 : ℝ) / 2) /
          Real.log (Real.log q) ^ (2 : ℝ) < B ∧
      200 * (B ^ ((2 : ℝ) / 3) * Real.log q ^ (3 : ℝ) /
          Real.log (Real.log q) ^ ((8 : ℝ) / 3)) <
        Erdos285.Lemma12.martinBlockBound x q ∧
      200 * (Real.log q / Real.log (Real.log q)) ^ (4 : ℕ) <
        Erdos285.Lemma12.martinBlockBound x q := by
  dsimp only
  let L : ℝ := Real.log (x : ℝ)
  let lq : ℝ := Real.log (q : ℝ)
  let llq : ℝ := Real.log lq
  let y : ℝ := (x : ℝ) / q
  let A : ℝ := 200 * y ^ ((2 : ℝ) / 3) * L ^ (3 : ℕ)
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLLq : 2 ≤ llq := by simpa [llq, lq] using hLLq2
  have hLLqpos : 0 < llq := by linarith
  have hlqone : 1 < lq := by
    have : 0 < Real.log lq := by simpa [llq] using hLLqpos
    exact (Real.log_pos_iff (by positivity)).mp this
  have hlqpos : 0 < lq := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqleX := q_cast_le_x_of_strongRange hL1 hrange
  have hlqL : lq ≤ L := by
    simpa [lq, L] using Real.log_le_log hqR hqleX
  have hypos : 0 < y := by
    dsimp [y]
    exact div_pos (by
      have hxone : 1 < (x : ℝ) :=
        (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ x)).mp hLpos
      linarith) hqR
  have h30 : L ^ (30 : ℕ) ≤ y := by
    simpa [L, y] using log_pow_thirty_le_div hq hLpos hrange.2
  have hyone : 1 ≤ y := by
    calc
      (1 : ℝ) ≤ L ^ (30 : ℕ) := by
        simpa using pow_le_pow_right₀ hL1 (by norm_num : 0 ≤ (30 : ℕ))
      _ ≤ y := h30
  have hlqPow : lq ^ ((3 : ℝ) / 2) ≤ L ^ (2 : ℕ) := by
    calc
      lq ^ ((3 : ℝ) / 2) ≤ L ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow hlqpos.le hlqL (by norm_num)
      _ ≤ L ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L ^ (2 : ℕ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
  have hLLqPowOne : 1 ≤ llq ^ (2 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hBsourceLe :
      lq ^ ((3 : ℝ) / 2) / llq ^ (2 : ℝ) ≤ L ^ (2 : ℕ) := by
    calc
      lq ^ ((3 : ℝ) / 2) / llq ^ (2 : ℝ) ≤
          lq ^ ((3 : ℝ) / 2) :=
        div_le_self (Real.rpow_nonneg hlqpos.le _) hLLqPowOne
      _ ≤ L ^ (2 : ℕ) := hlqPow
  have hLpowStrict : L ^ (2 : ℕ) < L ^ (30 : ℕ) :=
    pow_lt_pow_right₀ (by linarith : 1 < L) (by norm_num)
  have hBsource : lq ^ ((3 : ℝ) / 2) / llq ^ (2 : ℝ) < y :=
    hBsourceLe.trans_lt (hLpowStrict.trans_le h30)
  have hlq3 : lq ^ (3 : ℕ) ≤ L ^ (3 : ℕ) :=
    pow_le_pow_left₀ hlqpos.le hlqL _
  have hLLq83 : 2 ≤ llq ^ ((8 : ℝ) / 3) := by
    calc
      (2 : ℝ) ≤ llq := hLLq
      _ = llq ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ llq ^ ((8 : ℝ) / 3) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hsourceHalf :
      200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ) /
          llq ^ ((8 : ℝ) / 3)) ≤ A / 2 := by
    have hnum : 0 ≤ 200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ)) := by positivity
    calc
      200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ) /
          llq ^ ((8 : ℝ) / 3)) =
          (200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ))) /
            llq ^ ((8 : ℝ) / 3) := by ring
      _ ≤ (200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ))) / 2 :=
        div_le_div_of_nonneg_left hnum (by norm_num) hLLq83
      _ ≤ (200 * (y ^ ((2 : ℝ) / 3) * L ^ (3 : ℕ))) / 2 := by
        gcongr
      _ = A / 2 := by dsimp [A]; ring
  have hA2 : 2 ≤ A := by
    have hy23 : 1 ≤ y ^ ((2 : ℝ) / 3) :=
      Real.one_le_rpow hyone (by norm_num)
    have hL3 : 1 ≤ L ^ (3 : ℕ) := by
      simpa using pow_le_pow_right₀ hL1 (by norm_num : 0 ≤ (3 : ℕ))
    dsimp [A]
    nlinarith [mul_le_mul hy23 hL3 (by norm_num : (0 : ℝ) ≤ 1)
      (Real.rpow_nonneg hypos.le _)]
  have hfloor : A <
      (Erdos285.Lemma12.martinBlockBound x q : ℝ) + 1 := by
    simpa only [A, L, y, Erdos285.Lemma12.martinBlockBound]
      using Nat.lt_floor_add_one A
  have hcardSource :
      200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ) /
          llq ^ ((8 : ℝ) / 3)) <
        Erdos285.Lemma12.martinBlockBound x q := by
    calc
      200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ) /
          llq ^ ((8 : ℝ) / 3)) ≤ A / 2 := hsourceHalf
      _ ≤ A - 1 := by linarith
      _ < Erdos285.Lemma12.martinBlockBound x q := by linarith
  have hL20 : L ^ (20 : ℕ) ≤ y ^ ((2 : ℝ) / 3) := by
    calc
      L ^ (20 : ℕ) = (L ^ (30 : ℕ)) ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast]
        rw [← Real.rpow_mul hLpos.le]
        norm_num
      _ ≤ y ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow (pow_nonneg hLpos.le 30) h30 (by norm_num)
  have htwoL : 2 * L ≤ y ^ ((2 : ℝ) / 3) := by
    calc
      2 * L ≤ L ^ (20 : ℕ) := by
        have hLpow : L ^ (2 : ℕ) ≤ L ^ (20 : ℕ) :=
          pow_le_pow_right₀ hL1 (by norm_num)
        nlinarith [sq_nonneg (L - 1)]
      _ ≤ y ^ ((2 : ℝ) / 3) := hL20
  have hquot : 0 ≤ lq / llq ∧ lq / llq ≤ L := by
    constructor
    · positivity
    · calc
        lq / llq ≤ lq := div_le_self hlqpos.le (by linarith)
        _ ≤ L := hlqL
  have hdispLe : 200 * (lq / llq) ^ (4 : ℕ) ≤ A / 2 := by
    have hpowq : (lq / llq) ^ (4 : ℕ) ≤ L ^ (4 : ℕ) :=
      pow_le_pow_left₀ hquot.1 hquot.2 _
    calc
      200 * (lq / llq) ^ (4 : ℕ) ≤ 200 * L ^ (4 : ℕ) := by gcongr
      _ ≤ A / 2 := by
        dsimp [A]
        have hL3pos : 0 < L ^ (3 : ℕ) := pow_pos hLpos _
        calc
          200 * L ^ (4 : ℕ) = (200 * L ^ 3) * L := by ring
          _ ≤ (200 * L ^ 3) * (y ^ ((2 : ℝ) / 3) / 2) := by
            gcongr
            rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
            simpa [mul_comm] using htwoL
          _ = 200 * y ^ ((2 : ℝ) / 3) * L ^ 3 / 2 := by ring
  have hdisp : 200 * (lq / llq) ^ (4 : ℕ) <
      Erdos285.Lemma12.martinBlockBound x q := by
    exact hdispLe.trans_lt ((show A / 2 <
      (Erdos285.Lemma12.martinBlockBound x q : ℝ) by
        calc
          A / 2 ≤ A - 1 := by linarith
          _ < _ := by linarith))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [lq, llq, y,
      show Real.log (Real.log (q : ℝ)) ^ (2 : ℝ) =
          Real.log (Real.log (q : ℝ)) ^ (2 : ℕ) by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]] using hBsource
  · simpa only [lq, llq, y,
      show Real.log (q : ℝ) ^ (3 : ℝ) =
          Real.log (q : ℝ) ^ (3 : ℕ) by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]] using hcardSource
  · simpa only [lq, llq] using hdisp

/-- Fully assembled candidate-family interface for Lemma 12.  Besides the
structural properties of the four-prime products, this theorem applies
Martin's subset-sum lemma and hence supplies a bounded inverse subset sum for
every residue modulo the varying prime power. -/
theorem eventually_exists_martin_candidate_family {ξ : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    ∀ᶠ x : ℕ in atTop, ∀ (p ν : ℕ), p.Prime → 0 < ν →
      InStrongEliminationRange x (p ^ ν) →
      ∃ M : Finset ℕ,
        M.card = Erdos285.Lemma12.martinBlockBound x (p ^ ν) ∧
        M ⊆ rawCandidates p (fourthRoot ξ)
          (fourthRoot ((x : ℝ) / (p ^ ν : ℕ))) ∧
        fourthRoot ((x : ℝ) / (p ^ ν : ℕ)) ≤ (p ^ ν : ℕ) ∧
        (∀ m ∈ M,
          (m : ℝ) < (x : ℝ) / (p ^ ν : ℕ) ∧
          Erdos285.Dispersion.IsKPrimeProductAway 4 (p ^ ν) m) ∧
        (Real.log (p ^ ν : ℕ) ^ ((3 : ℝ) / 2) /
            Real.log (Real.log (p ^ ν : ℕ)) ^ (2 : ℝ) <
              (x : ℝ) / (p ^ ν : ℕ)) ∧
        (200 * ((((x : ℝ) / (p ^ ν : ℕ)) ^ ((2 : ℝ) / 3)) *
              Real.log (p ^ ν : ℕ) ^ (3 : ℝ) /
            Real.log (Real.log (p ^ ν : ℕ)) ^ ((8 : ℝ) / 3)) <
              Erdos285.Lemma12.martinBlockBound x (p ^ ν)) ∧
        (200 * (Real.log (p ^ ν : ℕ) /
              Real.log (Real.log (p ^ ν : ℕ))) ^ (4 : ℕ) <
              Erdos285.Lemma12.martinBlockBound x (p ^ ν)) ∧
        ∀ residue : ZMod (p ^ ν), ∃ K : Finset ℕ,
          K ⊆ M ∧
          K.card ≤ Erdos285.Lemma12.martinBlockBound x (p ^ ν) ∧
          K.sum (fun m ↦ ((m : ZMod (p ^ ν))⁻¹)) = residue := by
  have hExtract :=
    eventually_rawCandidates_subset_at_elimination_scale hξ hξ1
  have hCandidateBound :=
    eventually_martinBlockBound_le_candidateLower hξ hξ1
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hllTop : Tendsto
      (fun q : ℕ ↦ Real.log (Real.log (q : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨Qll, hQll⟩ := eventually_atTop.1
    (hllTop.eventually_ge_atTop (2 : ℝ))
  obtain ⟨Qsubset, hQsubset⟩ := eventually_atTop.1
    (Erdos285.SubsetSum.eventually_bounded_inverse_subset_sum_of_martin_hypotheses
      4 (by omega))
  let Q : ℕ := max Qll Qsubset
  have hrootTop : Tendsto (fun x : ℕ ↦
      (x : ℝ) ^ ((1 : ℝ) / 5)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 5)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hExtract, hCandidateBound,
    hlogTop.eventually_ge_atTop 2,
    hrootTop.eventually_ge_atTop (Q : ℝ)]
      with x hExtractX hBoundX hlogX hrootQ
  intro p ν hp hν hrange
  let q : ℕ := p ^ ν
  have hq : 0 < q := pow_pos hp.pos ν
  have hQq : Q ≤ q := by
    exact_mod_cast (hrootQ.trans hrange.1)
  have hllq : 2 ≤ Real.log (Real.log (q : ℝ)) :=
    hQll q ((le_max_left Qll Qsubset).trans hQq)
  have hthreshold := fourPrime_subsetSum_and_dispersion_thresholds
    hq hlogX hllq hrange
  obtain ⟨M, hM, hMcard⟩ := hExtractX q p
    (Erdos285.Lemma12.martinBlockBound x q) hq hrange.2 (hBoundX q hq hrange)
  have htq : fourthRoot ((x : ℝ) / q) ≤ (q : ℝ) :=
    Erdos285.Lemma12.fourthRoot_div_le_of_fifthRoot_le hq hrange.1
  have hx : 0 < x := by
    have hlogpos : 0 < Real.log (x : ℝ) := by linarith
    have hxR : (0 : ℝ) < x := by
      have hxone : 1 < (x : ℝ) :=
        (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ x)).mp hlogpos
      linarith
    exact_mod_cast hxR
  have hMsource : ∀ m ∈ M,
      (m : ℝ) < (x : ℝ) / q ∧
        Erdos285.Dispersion.IsKPrimeProductAway 4 q m := by
    intro m hm
    exact ⟨rawCandidate_lt_eliminationScale hx hp (hM hm),
      rawCandidate_isKPrimeProductAway (ν := ν) hp (hM hm)⟩
  have hBpos : 0 < (x : ℝ) / q := by positivity
  have hsurj := hQsubset q
    ((le_max_right Qll Qsubset).trans hQq)
    (Erdos285.Lemma12.martinBlockBound x q)
    ((x : ℝ) / q) M (by simp [hMcard]) hBpos
    (by
      convert hthreshold.1 using 1 <;> norm_num [Real.rpow_natCast])
    (by
      rw [hMcard]
      convert hthreshold.2.1 using 1 <;> norm_num [Real.rpow_natCast])
    hMsource
  refine ⟨M, hMcard, hM, ?_, hMsource, ?_, ?_, ?_, hsurj⟩
  · simpa [q] using htq
  · simpa [q] using hthreshold.1
  · simpa [q] using hthreshold.2.1
  · simpa [q] using hthreshold.2.2

end

end Lemma12Numerics

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/SmoothReservoir.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős 285: a reservoir of products of five nearby primes

Martin's proof uses a positive-density theorem for smooth numbers only to obtain
enough unused denominators for a cardinality adjustment.  A smaller reservoir
suffices for that use.  This file constructs one from products of five distinct
primes in the interval `(9y/10,y]`.

There are asymptotically a positive constant times `y / log y` primes in this
interval.  Products of five-element subsets are distinct by unique
factorization, so the reservoir has order `(y / log y)^5`.  Every product lies
in `(y^5/2,y^5]` and every prime-power divisor is at most `y`.
-/

open Filter Finset Real Asymptotics
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Primes in the fixed narrow interval `(9y/10,y]`. -/
def reservoirPrimes (y : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊y⌋₊ \ Nat.primesLE ⌊(9 / 10 : ℝ) * y⌋₊

/-- Products of five distinct primes in `reservoirPrimes y`. -/
def smoothReservoir (y : ℝ) : Finset ℕ :=
  (reservoirPrimes y).powersetCard 5 |>.image fun S ↦ S.prod id

lemma mem_reservoirPrimes {y : ℝ} {p : ℕ} (hp : p ∈ reservoirPrimes y) :
    p.Prime ∧ (9 / 10 : ℝ) * y < p ∧ (p : ℝ) ≤ y := by
  rw [reservoirPrimes, Finset.mem_sdiff] at hp
  have hpUpper := Nat.mem_primesLE.mp hp.1
  have hpLower : ⌊(9 / 10 : ℝ) * y⌋₊ < p := by
    simpa [Nat.mem_primesLE, hpUpper.2] using hp.2
  have hy : 0 ≤ y := by
    have hfloorPos : 0 < ⌊y⌋₊ := lt_of_lt_of_le hpUpper.2.pos hpUpper.1
    exact zero_le_one.trans (Nat.floor_pos.mp hfloorPos)
  refine ⟨hpUpper.2, Nat.lt_of_floor_lt hpLower, ?_⟩
  exact (Nat.cast_le.mpr hpUpper.1).trans (Nat.floor_le hy)

private lemma product_of_primes_factors_toFinset {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    (S.prod id).primeFactorsList.toFinset = S := by
  have hprod : (S.sort (· ≤ ·)).prod = S.prod id := by
    calc
      (S.sort (· ≤ ·)).prod = (S.sort (· ≤ ·)).toFinset.prod id := by
        simpa using (List.prod_toFinset id (S.sort_nodup (· ≤ ·))).symm
      _ = S.prod id := by rw [Finset.sort_toFinset]
  have hprime : ∀ p ∈ S.sort (· ≤ ·), p.Prime := by
    intro p hp
    exact hS p ((Finset.mem_sort (· ≤ ·)).mp hp)
  have hperm : List.Perm (S.sort (· ≤ ·)) (S.prod id).primeFactorsList :=
    Nat.primeFactorsList_unique hprod hprime
  exact (List.toFinset_eq_of_perm _ _ hperm).symm.trans (Finset.sort_toFinset _ _)

lemma prod_injective_on_primeSubsets (y : ℝ) :
    Set.InjOn (fun S : Finset ℕ ↦ S.prod id) (reservoirPrimes y).powerset := by
  intro A hA B hB hprod
  have hAprime : ∀ p ∈ A, p.Prime := by
    intro p hp
    exact (mem_reservoirPrimes (Finset.mem_powerset.mp hA hp)).1
  have hBprime : ∀ p ∈ B, p.Prime := by
    intro p hp
    exact (mem_reservoirPrimes (Finset.mem_powerset.mp hB hp)).1
  change A.prod id = B.prod id at hprod
  calc
    A = (A.prod id).primeFactorsList.toFinset :=
      (product_of_primes_factors_toFinset hAprime).symm
    _ = (B.prod id).primeFactorsList.toFinset := by rw [hprod]
    _ = B := product_of_primes_factors_toFinset hBprime

lemma smoothReservoir_card (y : ℝ) :
    (smoothReservoir y).card = Nat.choose (reservoirPrimes y).card 5 := by
  rw [smoothReservoir, Finset.card_image_iff.mpr]
  · exact Finset.card_powersetCard 5 (reservoirPrimes y)
  · apply (prod_injective_on_primeSubsets y).mono
    intro S hS
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1

lemma smoothReservoir_card_lower (y : ℝ) :
    (((reservoirPrimes y).card + 1 - 5 : ℕ) : ℝ) ^ 5 /
        ((Nat.factorial 5 : ℕ) : ℝ) ≤
      (smoothReservoir y).card := by
  rw [smoothReservoir_card]
  exact Nat.pow_le_choose 5 (reservoirPrimes y).card

/-- Select any requested number of unused cardinality-adjustment terms from the
reservoir.  All interval and smoothness properties are then inherited from the
ambient finset. -/
lemma exists_smoothReservoir_subset_card_eq {y : ℝ} {m : ℕ}
    (hm : m ≤ (smoothReservoir y).card) :
    ∃ T ⊆ smoothReservoir y, T.card = m :=
  Finset.exists_subset_card_eq hm

lemma mem_smoothReservoir_source {y : ℝ} {n : ℕ} (hn : n ∈ smoothReservoir y) :
    ∃ S ⊆ reservoirPrimes y, S.card = 5 ∧ n = S.prod id := by
  rw [smoothReservoir, Finset.mem_image] at hn
  obtain ⟨S, hS, rfl⟩ := hn
  exact ⟨S, (Finset.mem_powersetCard.mp hS).1, (Finset.mem_powersetCard.mp hS).2, rfl⟩

lemma smoothReservoir_upper {y : ℝ} (_hy : 0 ≤ y) {n : ℕ}
    (hn : n ∈ smoothReservoir y) :
    (n : ℝ) ≤ y ^ 5 := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_smoothReservoir_source hn
  push_cast
  calc
    ∏ p ∈ S, (p : ℝ) ≤ ∏ _p ∈ S, y := by
      exact Finset.prod_le_prod (fun _ _ ↦ by positivity)
        (fun p hp ↦ (mem_reservoirPrimes (hS hp)).2.2)
    _ = y ^ 5 := by simp [Finset.prod_const, hcard]

lemma smoothReservoir_lower {y : ℝ} (hy : 0 < y) {n : ℕ}
    (hn : n ∈ smoothReservoir y) :
    y ^ 5 / 2 < (n : ℝ) := by
  obtain ⟨S, hS, hcard, rfl⟩ := mem_smoothReservoir_source hn
  push_cast
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hprod : ((9 / 10 : ℝ) * y) ^ S.card < ∏ p ∈ S, (p : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_lt_prod_of_nonempty
      (fun _ _ ↦ mul_pos (by norm_num) hy)
      (fun p hp ↦ (mem_reservoirPrimes (hS hp)).2.1) hSne
  rw [hcard] at hprod
  calc
    y ^ 5 / 2 < ((9 / 10 : ℝ) * y) ^ 5 := by
      have hy5 : 0 < y ^ 5 := pow_pos hy _
      rw [mul_pow]
      norm_num
      nlinarith
    _ < ∏ p ∈ S, (p : ℝ) := hprod

lemma smoothReservoir_primePower_bound {y : ℝ} {n : ℕ}
    (hn : n ∈ smoothReservoir y) :
    UnitFractions.is_smooth y n := by
  obtain ⟨S, hS, -, rfl⟩ := mem_smoothReservoir_source hn
  intro q hq hqDvd
  have hprimeS : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (mem_reservoirPrimes (hS hp)).1
  have hsquarefree : Squarefree (S.prod id) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp <|
        (Nat.coprime_primes (hprimeS p hp) (hprimeS q hq)).2 hpq
    · intro p hp
      exact (hprimeS p hp).squarefree
  have hqprime : q.Prime :=
    Nat.squarefree_and_prime_pow_iff_prime.mp
      ⟨hsquarefree.squarefree_of_dvd hqDvd, hq⟩
  obtain ⟨p, hpS, hqDvdP⟩ := hqprime.prime.exists_mem_finset_dvd hqDvd
  have hqp : q = p := by
    exact (Nat.dvd_prime (hprimeS p hpS)).mp hqDvdP |>.resolve_left hqprime.ne_one
  subst p
  exact (mem_reservoirPrimes (hS hpS)).2.2

/-! ## Prime-number-theorem input -/

lemma reservoirPrimes_card_eq (y : ℝ) (hy : 0 ≤ y) :
    ((reservoirPrimes y).card : ℝ) =
      Nat.primeCounting ⌊y⌋₊ - Nat.primeCounting ⌊(9 / 10 : ℝ) * y⌋₊ := by
  have hfloor : ⌊(9 / 10 : ℝ) * y⌋₊ ≤ ⌊y⌋₊ := by
    exact Nat.floor_mono (by nlinarith)
  have hsub : Nat.primesLE ⌊(9 / 10 : ℝ) * y⌋₊ ⊆ Nat.primesLE ⌊y⌋₊ :=
    Nat.primesLE_mono hfloor
  rw [reservoirPrimes, Finset.card_sdiff_of_subset hsub, Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_card_eq_primeCounting]
  rw [Nat.cast_sub (Nat.monotone_primeCounting hfloor)]

/-- A quantitative eventual lower bound for the number of primes in `(9y/10,y]`.
The deliberately loose constant makes the statement convenient downstream. -/
theorem eventually_reservoirPrimes_card_lower :
    ∀ᶠ y : ℝ in atTop,
      y / (100 * Real.log y) ≤ ((reservoirPrimes y).card : ℝ) := by
  obtain ⟨e, he, hpi⟩ := pi_alt
  have heBound := he.bound (show (0 : ℝ) < 1 / 100 by norm_num)
  have hscale : Tendsto (fun y : ℝ ↦ (9 / 10 : ℝ) * y) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have heBoundScaled := hscale.eventually heBound
  filter_upwards [heBound, heBoundScaled, eventually_gt_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop (-100 * Real.log (9 / 10 : ℝ))]
      with y hey hecy hy hlogLarge
  have hy0 : 0 ≤ y := by linarith
  have hyPos : 0 < y := by linarith
  have hcy0 : 0 < (9 / 10 : ℝ) * y := mul_pos (by norm_num) hyPos
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogcy : 0 < Real.log ((9 / 10 : ℝ) * y) := by
    apply Real.log_pos
    nlinarith
  have hlogCompare : (99 / 100 : ℝ) * Real.log y ≤
      Real.log ((9 / 10 : ℝ) * y) := by
    rw [Real.log_mul (by norm_num : (9 / 10 : ℝ) ≠ 0) (ne_of_gt hyPos)]
    nlinarith
  have heLower : (99 / 100 : ℝ) ≤ 1 + e y := by
    have := (abs_le.mp (show |e y| ≤ (1 / 100 : ℝ) by simpa using hey)).1
    linarith
  have heUpper : 1 + e ((9 / 10 : ℝ) * y) ≤ (101 / 100 : ℝ) := by
    have := (abs_le.mp (show |e ((9 / 10 : ℝ) * y)| ≤ (1 / 100 : ℝ) by
      simpa using hecy)).2
    linarith
  have hpiLower : (99 / 100 : ℝ) * (y / Real.log y) ≤
      Nat.primeCounting ⌊y⌋₊ := by
    rw [hpi y]
    simpa [mul_div_assoc] using
      mul_le_mul_of_nonneg_right heLower (div_nonneg hy0 hlogy.le)
  have hpiUpper : (Nat.primeCounting ⌊(9 / 10 : ℝ) * y⌋₊ : ℝ) ≤
      (19 / 20 : ℝ) * (y / Real.log y) := by
    rw [hpi ((9 / 10 : ℝ) * y)]
    apply (div_le_iff₀ hlogcy).2
    calc
      (1 + e ((9 / 10 : ℝ) * y)) * ((9 / 10 : ℝ) * y)
          ≤ (101 / 100 : ℝ) * ((9 / 10 : ℝ) * y) := by
            exact mul_le_mul_of_nonneg_right heUpper hcy0.le
      _ ≤ (19 / 20 : ℝ) * (y / Real.log y) *
          ((99 / 100 : ℝ) * Real.log y) := by
            field_simp
            nlinarith
      _ ≤ (19 / 20 : ℝ) * (y / Real.log y) *
          Real.log ((9 / 10 : ℝ) * y) := by
            gcongr
  rw [reservoirPrimes_card_eq y hy0]
  calc
    y / (100 * Real.log y) ≤
        (99 / 100 : ℝ) * (y / Real.log y) -
          (19 / 20 : ℝ) * (y / Real.log y) := by
      field_simp
      nlinarith
    _ ≤ (Nat.primeCounting ⌊y⌋₊ : ℝ) -
        Nat.primeCounting ⌊(9 / 10 : ℝ) * y⌋₊ := sub_le_sub hpiLower hpiUpper

/-- The five-prime reservoir eventually has at least a fixed multiple of
`(y / log y)^5` elements. -/
theorem eventually_smoothReservoir_card_lower :
    ∀ᶠ y : ℝ in atTop,
      (y / (200 * Real.log y)) ^ 5 / 120 ≤ ((smoothReservoir y).card : ℝ) := by
  have hgrowth : Tendsto (fun y : ℝ ↦ y / (100 * Real.log y)) atTop atTop := by
    have h := (Real.tendsto_exp_div_pow_atTop 1).const_mul_atTop
      (show (0 : ℝ) < 1 / 100 by norm_num)
    refine (h.comp Real.tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [Function.comp_apply, pow_one]
    rw [Real.exp_log hy]
    ring
  filter_upwards [eventually_reservoirPrimes_card_lower,
    eventually_gt_atTop 2,
    hgrowth.eventually_ge_atTop 10]
      with y hband hy hgrowth10
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hbandNonneg : 0 ≤ y / (100 * Real.log y) := by positivity
  have hcardLarge : 10 ≤ (reservoirPrimes y).card := by
    exact_mod_cast hgrowth10.trans hband
  have hhalf : y / (200 * Real.log y) ≤
      (((reservoirPrimes y).card + 1 - 5 : ℕ) : ℝ) := by
    have hhalfCard : y / (200 * Real.log y) ≤ ((reservoirPrimes y).card : ℝ) / 2 := by
      calc
        y / (200 * Real.log y) = (y / (100 * Real.log y)) / 2 := by ring
        _ ≤ ((reservoirPrimes y).card : ℝ) / 2 := by gcongr
    have hfour : 4 ≤ (reservoirPrimes y).card := hcardLarge.trans' (by omega)
    calc
      y / (200 * Real.log y) ≤ ((reservoirPrimes y).card : ℝ) / 2 := hhalfCard
      _ ≤ (((reservoirPrimes y).card + 1 - 5 : ℕ) : ℝ) := by
        rw [show (reservoirPrimes y).card + 1 - 5 =
          (reservoirPrimes y).card - 4 by omega, Nat.cast_sub hfour]
        push_cast
        have hc : (10 : ℝ) ≤ (reservoirPrimes y).card := by exact_mod_cast hcardLarge
        nlinarith
  calc
    (y / (200 * Real.log y)) ^ 5 / 120 ≤
        ((((reservoirPrimes y).card + 1 - 5 : ℕ) : ℝ) ^ 5) /
          ((Nat.factorial 5 : ℕ) : ℝ) := by
      norm_num
      gcongr
    _ ≤ ((smoothReservoir y).card : ℝ) := smoothReservoir_card_lower y

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Proposition6.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős 285: the construction in Martin's Proposition 6

This file begins the source-faithful construction, rather than treating the
large set in Proposition 6 as an unspecified input.

The initial block is

`{n : exp (-r) x < n ≤ x and every prime-power divisor of n is at most z}`.

The strict lower endpoint is arithmetically immaterial and has the useful formal
consequence that the lower smooth reservoir, whose elements are at most
`exp (-r) x`, is automatically disjoint from the main block.

The second part couples the finite-set recursion in `Approximation.lean` to the
running rational residual.  It proves the exact residual identity at every
stage and implements well-founded descent on the largest exact prime-power part
of the reduced residual denominator.  Martin's Lemma 12 supplies the one-step
existence theorem used to instantiate this recursion.
-/

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The source's initial prime-power-smooth block -/

/--
The initial block in Proposition 6, with lower ratio `alpha`, scale `x`, and
prime-power cutoff `z`.
-/
def initialSmoothBlock (alpha : ℝ) (x : ℕ) (z : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊alpha * (x : ℝ)⌋₊ x).filter (UnitFractions.is_smooth z)

/--
The large prime-power cutoff used in this formalization.  Martin uses exponent
`22`; exponent `30` leaves enough room for the elementary five-prime reservoir:
the elimination loss becomes `O(x / log(x)^7)`, while that reservoir has size
`≫ x / log(x)^5`.
-/
def proposition6MainCutoff (x : ℕ) : ℝ :=
  (x : ℝ) / Real.log (x : ℝ) ^ 30

/-- The fifth-root scale whose five-prime products lie below `alpha*x`. -/
def proposition6ReservoirScale (alpha : ℝ) (x : ℕ) : ℝ :=
  (alpha * (x : ℝ)) ^ ((5 : ℝ)⁻¹)

lemma proposition6ReservoirScale_pow_five {alpha : ℝ} {x : ℕ}
    (halpha : 0 ≤ alpha) :
    proposition6ReservoirScale alpha x ^ 5 = alpha * (x : ℝ) := by
  exact Real.rpow_inv_natCast_pow
    (mul_nonneg halpha (Nat.cast_nonneg x)) (by norm_num : (5 : ℕ) ≠ 0)

@[simp] lemma mem_initialSmoothBlock {alpha z : ℝ} {x n : ℕ} :
    n ∈ initialSmoothBlock alpha x z ↔
      ⌊alpha * (x : ℝ)⌋₊ < n ∧ n ≤ x ∧ UnitFractions.is_smooth z n := by
  simp [initialSmoothBlock, and_assoc]

lemma initialSmoothBlock_zero_not_mem (alpha z : ℝ) (x : ℕ) :
    0 ∉ initialSmoothBlock alpha x z := by
  intro h
  have := (mem_initialSmoothBlock.mp h).1
  omega

lemma initialSmoothBlock_upper {alpha z : ℝ} {x n : ℕ}
    (hn : n ∈ initialSmoothBlock alpha x z) : n ≤ x :=
  (mem_initialSmoothBlock.mp hn).2.1

lemma initialSmoothBlock_smooth {alpha z : ℝ} {x n : ℕ}
    (hn : n ∈ initialSmoothBlock alpha x z) : UnitFractions.is_smooth z n :=
  (mem_initialSmoothBlock.mp hn).2.2

lemma initialSmoothBlock_lower {alpha z : ℝ} {x n : ℕ}
    (_halpha : 0 ≤ alpha) (hn : n ∈ initialSmoothBlock alpha x z) :
    alpha * (x : ℝ) < n := by
  exact Nat.lt_of_floor_lt (mem_initialSmoothBlock.mp hn).1

/-- The initial recursion state: every initially selected term is marked used. -/
def initialApproximationState (alpha : ℝ) (x : ℕ) (z : ℝ) :
    ApproximationState where
  selected := initialSmoothBlock alpha x z
  used := initialSmoothBlock alpha x z

/-! ## A concrete lower reservoir and its separation from the main block -/

/--
The five-prime reservoir API becomes the interval `[alpha*x/2,alpha*x]` when
`y^5 = alpha*x`.
-/
lemma smoothReservoir_in_lower_interval {alpha y : ℝ} {x n : ℕ}
    (hy : 0 < y) (hy5 : y ^ 5 = alpha * (x : ℝ))
    (hn : n ∈ smoothReservoir y) :
    alpha * (x : ℝ) / 2 < (n : ℝ) ∧ (n : ℝ) ≤ alpha * x := by
  constructor
  · rw [← hy5]
    exact smoothReservoir_lower hy hn
  · rw [← hy5]
    exact smoothReservoir_upper hy.le hn

/-- A reservoir built at any lower ratio `beta ≤ alpha` is disjoint from
the main block beginning above `alpha * x`. -/
lemma proposition6Reservoir_disjoint_initial_of_le
    {alpha beta z : ℝ} {x : ℕ} (hbeta : 0 < beta) (hba : beta ≤ alpha) :
    Disjoint (initialSmoothBlock alpha x z)
      (smoothReservoir (proposition6ReservoirScale beta x)) := by
  by_cases hx : x = 0
  · subst x
    simp [initialSmoothBlock]
  · rw [Finset.disjoint_left]
    intro n hnMain hnReservoir
    have hmainLower := initialSmoothBlock_lower
      (hbeta.le.trans hba) hnMain
    have hypos : 0 < proposition6ReservoirScale beta x :=
      Real.rpow_pos_of_pos
        (mul_pos hbeta (by exact_mod_cast Nat.pos_of_ne_zero hx)) _
    have hreservoirUpper := (smoothReservoir_in_lower_interval hypos
      (proposition6ReservoirScale_pow_five (x := x) hbeta.le) hnReservoir).2
    have hbetaAlpha : beta * (x : ℝ) ≤ alpha * x :=
      mul_le_mul_of_nonneg_right hba (Nat.cast_nonneg x)
    linarith

/-! ## Residual-preserving recursion -/

/--
A recursion state together with the residual rational.  The balance equation is
Martin's invariant `sum(selected) + residual = r`.
-/
structure ResidualApproximationState (r : ℚ) where
  terms : ApproximationState
  residual : ℚ
  balance : UnitFractions.rec_sum terms.selected + residual = r

/-- A residual state whose selected terms have all been marked as used. -/
def ResidualApproximationState.Coherent {r : ℚ}
    (s : ResidualApproximationState r) : Prop :=
  s.terms.selected ⊆ s.terms.used

/-- The residual change opposite to the reciprocal-sum change of a stage. -/
def ApproximationStep.residualDelta (d : ApproximationStep) : ℚ :=
  UnitFractions.rec_sum d.remove - UnitFractions.rec_sum d.add

/-- Apply one valid stage while maintaining the exact rational balance. -/
def ResidualApproximationState.applyStep {r : ℚ}
    (s : ResidualApproximationState r) (d : ApproximationStep)
    (hd : d.Valid s.terms) : ResidualApproximationState r where
  terms := s.terms.applyStep d
  residual := s.residual + d.residualDelta
  balance := by
    change UnitFractions.rec_sum (s.terms.applyStep d).selected +
      (s.residual + (UnitFractions.rec_sum d.remove - UnitFractions.rec_sum d.add)) = r
    linarith [s.balance, hd.rec_sum_balance]

lemma ResidualApproximationState.Coherent.applyStep {r : ℚ}
    {s : ResidualApproximationState r} {d : ApproximationStep}
    (hd : d.Valid s.terms) :
    (s.applyStep d hd).Coherent := by
  exact hd.selected_subset_used_after

@[simp] lemma ResidualApproximationState.applyStep_residual {r : ℚ}
    (s : ResidualApproximationState r) (d : ApproximationStep)
    (hd : d.Valid s.terms) :
    (s.applyStep d hd).residual = s.residual + d.residualDelta := rfl

/-- Package any completed residual state directly as the finite Proposition 6
certificate, using the rational's canonical reduced numerator and denominator.
-/
noncomputable def approximationCertificate_of_residualState
    {r : ℚ} {x R : ℕ} (s : ResidualApproximationState r)
    (hcard : s.terms.selected.card = R)
    (hzero : 0 ∉ s.terms.selected)
    (hinterval : ∀ n ∈ s.terms.selected,
      Real.exp (-(r : ℝ)) * (x : ℝ) / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ x)
    (hpos : 0 < s.residual)
    (hlower : (Real.log (x : ℝ))⁻¹ < (s.residual : ℝ))
    (hupper : (s.residual : ℝ) < 1)
    (hsmooth : ∀ q : ℕ, IsPrimePow q → q ∣ s.residual.den → q ^ 5 ≤ x) :
    ApproximationCertificate r x R := by
  have hnumPos : 0 < s.residual.num := Rat.num_pos.mpr hpos
  have hnumAbs : (s.residual.num.natAbs : ℤ) = s.residual.num :=
    Int.natAbs_of_nonneg hnumPos.le
  have hresidualQ :
      (s.residual.num.natAbs : ℚ) / s.residual.den = s.residual := by
    rw [← Int.cast_natCast, hnumAbs, Rat.num_div_den]
  have hresidualR :
      (s.residual.num.natAbs : ℝ) / s.residual.den = (s.residual : ℝ) := by
    have hcast := congrArg (fun u : ℚ ↦ (u : ℝ)) hresidualQ
    norm_num at hcast ⊢
    exact hcast
  refine
    { denominators := s.terms.selected
      numerator := s.residual.num.natAbs
      denominator := s.residual.den
      denominator_pos := s.residual.den_pos
      numerator_pos := Int.natAbs_pos.mpr hnumPos.ne'
      reduced := s.residual.reduced
      card_eq := hcard
      zero_not_mem := hzero
      interval := hinterval
      sum_add_residual := ?_
      residual_lower := ?_
      residual_upper := ?_
      denominator_primePower_bound := hsmooth }
  · rw [hresidualQ]
    exact s.balance
  · rw [hresidualR]
    exact hlower
  · rw [hresidualR]
    exact hupper

/-- Adding a fresh reservoir set, without removing any current term. -/
def reservoirPaddingStep (padding : Finset ℕ) : ApproximationStep where
  remove := ∅
  add := padding

lemma reservoirPaddingStep_valid {r : ℚ} {s : ResidualApproximationState r}
    (hs : s.Coherent) {padding : Finset ℕ} (hfresh : Disjoint padding s.terms.used) :
    (reservoirPaddingStep padding).Valid s.terms := by
  refine ⟨hs, ?_, hfresh⟩
  exact Finset.empty_subset _

lemma reservoirPaddingStep_selected {r : ℚ} {s : ResidualApproximationState r}
    {padding : Finset ℕ} (hfresh : Disjoint padding s.terms.used)
    (hs : s.Coherent) :
    (s.applyStep (reservoirPaddingStep padding)
      (reservoirPaddingStep_valid hs hfresh)).terms.selected =
      s.terms.selected ∪ padding := by
  simp [ResidualApproximationState.applyStep, ApproximationState.applyStep,
    reservoirPaddingStep]

lemma reservoirPaddingStep_residual {r : ℚ} {s : ResidualApproximationState r}
    {padding : Finset ℕ} (hfresh : Disjoint padding s.terms.used)
    (hs : s.Coherent) :
    (s.applyStep (reservoirPaddingStep padding)
      (reservoirPaddingStep_valid hs hfresh)).residual =
      s.residual - UnitFractions.rec_sum padding := by
  simp [ResidualApproximationState.applyStep, ApproximationStep.residualDelta,
    reservoirPaddingStep]
  ring

/--
Concrete smooth-reservoir padding.  This is the exact-cardinality step at the
end of Proposition 6; the residual is updated by subtracting the newly inserted
unit fractions, and the defining reciprocal-sum balance remains exact.
-/
theorem exists_fivePrimeReservoir_padding
    {r : ℚ} {alpha : ℝ} {x R : ℕ} {s : ResidualApproximationState r}
    (halpha : 0 < alpha) (hs : s.Coherent)
    (hcard : s.terms.selected.card ≤ R)
    (hcapacity : R - s.terms.selected.card ≤
      (smoothReservoir (proposition6ReservoirScale alpha x)).card)
    (hfresh : Disjoint s.terms.used
      (smoothReservoir (proposition6ReservoirScale alpha x))) :
    ∃ padding : Finset ℕ,
      padding ⊆ smoothReservoir (proposition6ReservoirScale alpha x) ∧
      Disjoint padding s.terms.used ∧
      ∃ hp : (reservoirPaddingStep padding).Valid s.terms,
        (s.applyStep (reservoirPaddingStep padding) hp).terms.selected.card = R ∧
        (s.applyStep (reservoirPaddingStep padding) hp).Coherent ∧
        (s.applyStep (reservoirPaddingStep padding) hp).residual =
          s.residual - UnitFractions.rec_sum padding ∧
        UnitFractions.rec_sum
            (s.applyStep (reservoirPaddingStep padding) hp).terms.selected +
          (s.applyStep (reservoirPaddingStep padding) hp).residual = r ∧
        (∀ n ∈ padding,
          alpha * (x : ℝ) / 2 < (n : ℝ) ∧
          (n : ℝ) ≤ alpha * x ∧
          UnitFractions.is_smooth (proposition6ReservoirScale alpha x) n) := by
  obtain ⟨padding, hpadding, hpaddingCard⟩ :=
    exists_smoothReservoir_subset_card_eq hcapacity
  have hpadUsed : Disjoint padding s.terms.used :=
    (hfresh.mono_right hpadding).symm
  let hp : (reservoirPaddingStep padding).Valid s.terms :=
    reservoirPaddingStep_valid hs hpadUsed
  refine ⟨padding, hpadding, hpadUsed, hp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [reservoirPaddingStep_selected hpadUsed hs,
      Finset.card_union_of_disjoint
        (hpadUsed.mono_right hs).symm,
      hpaddingCard]
    omega
  · exact ResidualApproximationState.Coherent.applyStep hp
  · exact reservoirPaddingStep_residual hpadUsed hs
  · exact (s.applyStep (reservoirPaddingStep padding) hp).balance
  · intro n hn
    have hnReservoir := hpadding hn
    have hypos : 0 < proposition6ReservoirScale alpha x := by
      have hxpos : 0 < x := by
        by_contra hx
        have hx0 : x = 0 := Nat.eq_zero_of_not_pos hx
        subst x
        have hscale : proposition6ReservoirScale alpha 0 = 0 := by
          simp [proposition6ReservoirScale, Real.zero_rpow (by norm_num : (5 : ℝ)⁻¹ ≠ 0)]
        rw [hscale] at hnReservoir
        obtain ⟨S, hS, hScard, -⟩ := mem_smoothReservoir_source hnReservoir
        have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨p, hp⟩ := hSne
        have hpdata := mem_reservoirPrimes (hS hp)
        have hple : p ≤ 0 := by exact_mod_cast hpdata.2.2
        have hppos : 0 < p := hpdata.1.pos
        omega
      exact Real.rpow_pos_of_pos (mul_pos halpha (by exact_mod_cast hxpos)) _
    have hy5 := proposition6ReservoirScale_pow_five (x := x) halpha.le
    refine ⟨(smoothReservoir_in_lower_interval hypos hy5 hnReservoir).1,
      (smoothReservoir_in_lower_interval hypos hy5 hnReservoir).2, ?_⟩
    exact smoothReservoir_primePower_bound hnReservoir

/-! ## Removal steps and availability of lower-tagged terms -/

/-- The descent measure in Martin's recursive extraction. -/
def ResidualApproximationState.primePowerMeasure {r : ℚ}
    (s : ResidualApproximationState r) : ℕ :=
  PrimePowers.largestPrimePowerPart s.residual.den

/-- A source-faithful Lemma 12 step removes a block and adds nothing. -/
def eliminationRemovalStep (U : Finset ℕ) : ApproximationStep where
  remove := U
  add := ∅

lemma eliminationRemovalStep_valid {r : ℚ} {s : ResidualApproximationState r}
    (hs : s.Coherent) {U : Finset ℕ} (hU : U ⊆ s.terms.selected) :
    (eliminationRemovalStep U).Valid s.terms := by
  refine ⟨hs, hU, ?_⟩
  simp [eliminationRemovalStep]

lemma eliminationRemovalStep_selected {r : ℚ} {s : ResidualApproximationState r}
    {U : Finset ℕ} (hs : s.Coherent) (hU : U ⊆ s.terms.selected) :
    (s.applyStep (eliminationRemovalStep U)
      (eliminationRemovalStep_valid hs hU)).terms.selected = s.terms.selected \ U := by
  simp [ResidualApproximationState.applyStep, ApproximationState.applyStep,
    eliminationRemovalStep]

lemma eliminationRemovalStep_residual {r : ℚ} {s : ResidualApproximationState r}
    {U : Finset ℕ} (hs : s.Coherent) (hU : U ⊆ s.terms.selected) :
    (s.applyStep (eliminationRemovalStep U)
      (eliminationRemovalStep_valid hs hU)).residual =
      s.residual + UnitFractions.rec_sum U := by
  simp [ResidualApproximationState.applyStep, ApproximationStep.residualDelta,
    eliminationRemovalStep]

/--
Availability invariant for descending tag elimination.  Every member of the
original block whose exact prime-power tag is no larger than the current
residual measure is still selected.
-/
def AvailableBelow (base : Finset ℕ) {r : ℚ}
    (s : ResidualApproximationState r) : Prop :=
  ∀ n ∈ base,
    PrimePowers.largestPrimePowerPart n ≤ s.primePowerMeasure →
      n ∈ s.terms.selected

/--
Removing a block tagged by the current measure preserves all terms whose tags
are at most the strictly smaller new measure.
-/
lemma AvailableBelow.eliminationRemovalStep
    {base : Finset ℕ} {r : ℚ} {s : ResidualApproximationState r}
    (havail : AvailableBelow base s) (hs : s.Coherent)
    {U : Finset ℕ} (hU : U ⊆ s.terms.selected)
    (htag : ∀ n ∈ U,
      PrimePowers.largestPrimePowerPart n = s.primePowerMeasure)
    (hdesc :
      (s.applyStep (eliminationRemovalStep U)
        (eliminationRemovalStep_valid hs hU)).primePowerMeasure <
          s.primePowerMeasure) :
    AvailableBelow base
      (s.applyStep (eliminationRemovalStep U)
        (eliminationRemovalStep_valid hs hU)) := by
  intro n hnbase hntag
  have hnold : n ∈ s.terms.selected :=
    havail n hnbase (hntag.trans hdesc.le)
  rw [eliminationRemovalStep_selected hs hU, Finset.mem_sdiff]
  refine ⟨hnold, ?_⟩
  intro hnU
  have := htag n hnU
  omega

/-- A largest-exact-prime-power bound implies `UnitFractions.is_smooth`. -/
lemma isSmooth_of_largestPrimePowerPart_le
    {z : ℝ} {n : ℕ} (hz : 0 ≤ z) (hn : n ≠ 0)
    (hmax : (PrimePowers.largestPrimePowerPart n : ℝ) ≤ z) :
    UnitFractions.is_smooth z n := by
  intro q hqpp hqdiv
  have hqexact : ∃ exactPart : ℕ,
      exactPart ∈ PrimePowers.primePowerParts n ∧ q ∣ exactPart := by
    rcases (isPrimePow_nat_iff q).1 hqpp with ⟨p, k, hp, hk, rfl⟩
    let exactPart := p ^ n.factorization p
    have hkle : k ≤ n.factorization p :=
      (hp.pow_dvd_iff_le_factorization hn).1 hqdiv
    have hfac : n.factorization p ≠ 0 :=
      Nat.ne_zero_of_lt (hk.trans_le hkle)
    refine ⟨exactPart, (PrimePowers.mem_primePowerParts hn).2 ?_, ?_⟩
    · refine ⟨hp.isPrimePow.pow hfac, ?_, ?_⟩
      · dsimp [exactPart]
        simpa using Nat.ordProj_dvd n p
      · dsimp [exactPart]
        exact ((UnitFractions.factorization_eq_iff (n := n) hp hfac).2 rfl).2
    · dsimp [exactPart]
      exact pow_dvd_pow p hkle
  obtain ⟨exactPart, hpart, hqpart⟩ := hqexact
  have hpartpos : 0 < exactPart :=
    ((PrimePowers.mem_primePowerParts hn).1 hpart).1.pos
  have hqle : (q : ℝ) ≤ exactPart := by
    exact_mod_cast Nat.le_of_dvd hpartpos hqpart
  have hpartmax : (exactPart : ℝ) ≤
      PrimePowers.largestPrimePowerPart n := by
    exact_mod_cast PrimePowers.le_largestPrimePowerPart hpart
  exact hqle.trans (hpartmax.trans hmax)

/-- Smooth displayed denominators give a smooth reduced denominator for their
finite reciprocal sum. -/
lemma recSum_den_isSmooth {y : ℝ} {A : Finset ℕ}
    (hzero : ∀ n ∈ A, n ≠ 0)
    (hsmooth : ∀ n ∈ A, UnitFractions.is_smooth y n) :
    UnitFractions.is_smooth y (UnitFractions.rec_sum A).den := by
  intro q hq hqden
  have hqlcm : q ∣ A.lcm id :=
    hqden.trans (PrimePowers.recSum_den_dvd_lcm A)
  obtain ⟨n, hn, hqn⟩ :=
    Lemma12.isPrimePow_dvd_finsetLcm hq hzero hqlcm
  exact hsmooth n hn q hq hqn

/-- Smoothness bounds the largest exact prime-power part by the natural floor
of the smoothness parameter. -/
lemma largestPrimePowerPart_le_floor_of_isSmooth
    {y : ℝ} {n : ℕ} (hy : 0 ≤ y)
    (hsmooth : UnitFractions.is_smooth y n) :
    PrimePowers.largestPrimePowerPart n ≤ ⌊y⌋₊ := by
  by_cases hn : 2 ≤ n
  · have hmem := PrimePowers.largestPrimePowerPart_mem hn
    have hspec := (PrimePowers.mem_primePowerParts (by omega : n ≠ 0)).mp hmem
    exact Nat.le_floor (hsmooth _ hspec.1 hspec.2.1)
  · have hempty : PrimePowers.primePowerParts n = ∅ :=
      PrimePowers.primePowerParts_empty_iff.mpr (Nat.lt_of_not_ge hn)
    simp [PrimePowers.largestPrimePowerPart, hempty]

/-- Subtracting a reciprocal sum whose displayed denominators are smooth
preserves smoothness of a smooth rational denominator. -/
lemma sub_recSum_den_isSmooth {y : ℝ} (rho : ℚ) {A : Finset ℕ}
    (hrho : UnitFractions.is_smooth y rho.den)
    (hzero : ∀ n ∈ A, n ≠ 0)
    (hA : ∀ n ∈ A, UnitFractions.is_smooth y n) :
    UnitFractions.is_smooth y (rho - UnitFractions.rec_sum A).den := by
  have hsum := recSum_den_isSmooth hzero hA
  intro q hq hqden
  have hqLcm : q ∣ Nat.lcm rho.den (UnitFractions.rec_sum A).den :=
    hqden.trans (Rat.sub_den_dvd_lcm rho (UnitFractions.rec_sum A))
  rcases Lemma12.isPrimePow_dvd_lcm hq rho.den_ne_zero
      (UnitFractions.rec_sum A).den_ne_zero hqLcm with hqrho | hqsum
  · exact hrho q hq hqrho
  · exact hsum q hq hqsum

/-- Smoothness at the real fifth-root scale is exactly the integral
prime-power bound stored in an approximation certificate. -/
lemma primePower_pow_five_le_of_den_isSmooth
    {x d : ℕ}
    (hsmooth : UnitFractions.is_smooth
      ((x : ℝ) ^ ((5 : ℝ)⁻¹)) d) :
    ∀ q : ℕ, IsPrimePow q → q ∣ d → q ^ 5 ≤ x := by
  intro q hq hqd
  have hqle : (q : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹) :=
    hsmooth q hq hqd
  have hpow : (q : ℝ) ^ 5 ≤
      ((x : ℝ) ^ ((5 : ℝ)⁻¹)) ^ 5 :=
    pow_le_pow_left₀ (Nat.cast_nonneg q) hqle 5
  have hroot : ((x : ℝ) ^ ((5 : ℝ)⁻¹)) ^ 5 = x := by
    convert Real.rpow_inv_natCast_pow (Nat.cast_nonneg x)
      (by norm_num : (5 : ℕ) ≠ 0) using 1
    all_goals norm_num
  rw [hroot] at hpow
  exact_mod_cast hpow

/-!
## Instantiating one recursion stage with the concrete Lemma 12

The sign change is the correction to the printed Proposition 6 recursion:
Lemma 12 is applied to the negative residual.  Removing `U` from the selected
set changes the residual from `ρ` to `ρ + rec_sum U`, the negative of
`-ρ - rec_sum U` appearing in Lemma 12.
-/

theorem lemma12_eliminationRemovalStep
    {r : ℚ} {alpha xi z : ℝ} {x : ℕ}
    {s : ResidualApproximationState r} {M : Finset ℕ}
    (hs : s.Coherent)
    (havail : AvailableBelow (initialSmoothBlock alpha x z) s)
    (hdata : Lemma12.CandidateData xi x s.primePowerMeasure (-s.residual) M)
    (hsurj : Lemma12.BoundedInverseSubsetSurjective s.primePowerMeasure
      (Lemma12.martinBlockBound x s.primePowerMeasure) M)
    (halpha : 0 ≤ alpha)
    (hxi : (⌊alpha * (x : ℝ)⌋₊ : ℝ) < xi * x)
    (hqz : (s.primePowerMeasure : ℝ) ≤ z) :
    ∃ U : Finset ℕ,
      U.card ≤ Lemma12.martinBlockBound x s.primePowerMeasure ∧
      U ⊆ initialSmoothBlock alpha x z ∧
      ∃ hp : (eliminationRemovalStep U).Valid s.terms,
        (s.applyStep (eliminationRemovalStep U) hp).primePowerMeasure <
          s.primePowerMeasure ∧
        AvailableBelow (initialSmoothBlock alpha x z)
          (s.applyStep (eliminationRemovalStep U) hp) := by
  obtain ⟨U, hUcard, hUint, hUtag, -, hdescNeg⟩ :=
    Lemma12.largePrimePowerElimination hdata hsurj
  have hqspec :=
    (PrimePowers.mem_primePowerParts (-s.residual).den_ne_zero).mp hdata.q_part
  have hqpos : 0 < s.primePowerMeasure := hqspec.1.pos
  have hz : 0 ≤ z := (by exact_mod_cast hqpos.le : (0 : ℝ) ≤ s.primePowerMeasure).trans hqz
  have hUbase : U ⊆ initialSmoothBlock alpha x z := by
    intro u hu
    apply mem_initialSmoothBlock.mpr
    have huLowerR : (⌊alpha * (x : ℝ)⌋₊ : ℝ) < u :=
      hxi.trans_le (hUint u hu).1
    have huLower : ⌊alpha * (x : ℝ)⌋₊ < u := by exact_mod_cast huLowerR
    have huUpper : u ≤ x := by exact_mod_cast (hUint u hu).2
    have hu0 : u ≠ 0 := by omega
    have huSmooth : UnitFractions.is_smooth z u := by
      apply isSmooth_of_largestPrimePowerPart_le hz hu0
      rw [hUtag u hu]
      exact hqz
    exact ⟨huLower, huUpper, huSmooth⟩
  have hUselected : U ⊆ s.terms.selected := by
    intro u hu
    exact havail u (hUbase hu) (by rw [hUtag u hu])
  let hp : (eliminationRemovalStep U).Valid s.terms :=
    eliminationRemovalStep_valid hs hUselected
  have hresidual :
      (s.applyStep (eliminationRemovalStep U) hp).residual =
        s.residual + UnitFractions.rec_sum U := by
    exact eliminationRemovalStep_residual hs hUselected
  have hdenEq :
      ((-s.residual) - UnitFractions.rec_sum U).den =
        (s.residual + UnitFractions.rec_sum U).den := by
    have heq : (-s.residual) - UnitFractions.rec_sum U =
        -(s.residual + UnitFractions.rec_sum U) := by ring
    rw [heq, Rat.den_neg_eq_den]
  have hdesc :
      (s.applyStep (eliminationRemovalStep U) hp).primePowerMeasure <
        s.primePowerMeasure := by
    rw [ResidualApproximationState.primePowerMeasure, hresidual, ← hdenEq]
    exact hdescNeg
  refine ⟨U, hUcard, hUbase, hp, hdesc, ?_⟩
  exact havail.eliminationRemovalStep hs hUselected hUtag hdesc

/-- Sum of the worst-case Lemma 12 block bounds for all tags up to `Q`. -/
def totalEliminationBudget (x Q : ℕ) : ℕ :=
  ∑ q ∈ Finset.range (Q + 1), Lemma12.martinBlockBound x q

lemma totalEliminationBudget_mono (x : ℕ) : Monotone (totalEliminationBudget x) := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.succ_le_succ hab)
  · simp

lemma largestPrimePowerPart_mem_of_pos {n : ℕ}
    (hpos : 0 < PrimePowers.largestPrimePowerPart n) :
    PrimePowers.largestPrimePowerPart n ∈ PrimePowers.primePowerParts n := by
  apply PrimePowers.largestPrimePowerPart_mem
  by_contra hn
  have hempty : PrimePowers.primePowerParts n = ∅ :=
    PrimePowers.primePowerParts_empty_iff.mpr (Nat.lt_of_not_ge hn)
  rw [PrimePowers.largestPrimePowerPart, hempty] at hpos
  simp at hpos

/-- Every prime power in the cofactor left after removing the largest exact
prime-power part is strictly smaller than that part. -/
lemma primePower_dvd_cofactor_lt_largest
    {t : ℚ} {q ℓ : ℕ}
    (hqpart : q ∈ PrimePowers.primePowerParts t.den)
    (hmax : PrimePowers.largestPrimePowerPart t.den = q)
    (hℓpp : IsPrimePow ℓ) (hℓdiv : ℓ ∣ t.den / q) : ℓ < q := by
  have hqspec := (PrimePowers.mem_primePowerParts t.den_ne_zero).mp hqpart
  have hℓden : ℓ ∣ t.den :=
    hℓdiv.trans (Nat.div_dvd_of_dvd hqspec.2.1)
  have hsmooth : UnitFractions.is_smooth (q : ℝ) t.den := by
    apply isSmooth_of_largestPrimePowerPart_le (Nat.cast_nonneg q) t.den_ne_zero
    rw [hmax]
  have hℓle : ℓ ≤ q := by
    exact_mod_cast hsmooth ℓ hℓpp hℓden
  have hℓne : ℓ ≠ q := by
    intro heq
    subst ℓ
    have hqone := Nat.eq_one_of_dvd_coprimes hqspec.2.2 dvd_rfl hℓdiv
    exact hqspec.1.ne_one hqone
  exact lt_of_le_of_ne hℓle hℓne

/-- The precise finite input which the four-prime construction and the
modular subset-sum theorem supply at one residual state. -/
def Lemma12StepData {r : ℚ} (xi : ℝ) (x : ℕ)
    (s : ResidualApproximationState r) : Prop :=
  ∃ M : Finset ℕ,
    Lemma12.CandidateData xi x s.primePowerMeasure (-s.residual) M ∧
      Lemma12.BoundedInverseSubsetSurjective s.primePowerMeasure
        (Lemma12.martinBlockBound x s.primePowerMeasure) M

/-- Assemble the exact Lemma 12 input from an explicit subfamily of the
four-prime candidates.  All structural, interval, largest-part, and auxiliary
LCM fields are discharged here; only the separately proved subset-sum
surjectivity remains as an argument. -/
theorem lemma12StepData_of_rawCandidateFamily
    {r : ℚ} {xi : ℝ} {x p ν : ℕ}
    {s : ResidualApproximationState r} {M : Finset ℕ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hx : 0 < x)
    (hp : p.Prime) (hν : 0 < ν)
    (hqeq : s.primePowerMeasure = p ^ ν)
    (hrange : Lemma12.InEliminationRange x s.primePowerMeasure)
    (hM : M ⊆ Lemma12Candidates.rawCandidates p
      (Lemma12Candidates.fourthRoot xi)
      (Lemma12Candidates.fourthRoot ((x : ℝ) / (p ^ ν : ℕ))))
    (hsurj : Lemma12.BoundedInverseSubsetSurjective s.primePowerMeasure
      (Lemma12.martinBlockBound x s.primePowerMeasure) M) :
    Lemma12StepData xi x s := by
  have hqpos : 0 < s.primePowerMeasure := by
    rw [hqeq]
    exact pow_pos hp.pos ν
  have hqpartResidual : s.primePowerMeasure ∈
      PrimePowers.primePowerParts s.residual.den :=
    largestPrimePowerPart_mem_of_pos hqpos
  have hqpart : p ^ ν ∈ PrimePowers.primePowerParts (-s.residual).den := by
    rw [Rat.den_neg_eq_den, ← hqeq]
    exact hqpartResidual
  have hcofactor : ∀ ℓ : ℕ, IsPrimePow ℓ →
      ℓ ∣ (-s.residual).den / (p ^ ν) → ℓ < p ^ ν := by
    intro ℓ hℓpp hℓdiv
    apply primePower_dvd_cofactor_lt_largest hqpart
    · simpa [ResidualApproximationState.primePowerMeasure,
        Rat.den_neg_eq_den] using hqeq
    · exact hℓpp
    · exact hℓdiv
  unfold Lemma12StepData
  rw [hqeq]
  refine ⟨M, ?_, ?_⟩
  · apply Lemma12.candidateData_of_rawCandidateFamily
      hxi hxi1 hx hp hν
    · simpa [hqeq] using hrange
    · exact hqpart
    · exact hM
    · exact hcofactor
  · simpa [hqeq] using hsurj

/-- The strong `log⁻³⁰` range used by the uniform candidate construction is
contained in Martin's `log⁻²²` elimination range once `log x ≥ 1`. -/
lemma inEliminationRange_of_strongRange
    {x q : ℕ} (hlog : 1 ≤ Real.log (x : ℝ))
    (hrange : Lemma12Numerics.InStrongEliminationRange x q) :
    Lemma12.InEliminationRange x q := by
  refine ⟨hrange.1, hrange.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg x)
  exact Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)

/-- Uniform, unconditional Lemma 12 input at every residual state in the
strong elimination range.  The four-prime family, its exact cardinality, and
the bounded inverse-subset surjectivity are all supplied by
`Lemma12Numerics`; no state-local number-theoretic theorem remains as a
parameter. -/
theorem eventually_lemma12StepData_threeFourths :
    ∀ᶠ x : ℕ in atTop, ∀ {r : ℚ} (s : ResidualApproximationState r),
      Lemma12Numerics.InStrongEliminationRange x s.primePowerMeasure →
      Lemma12StepData ((3 : ℝ) / 4) x s := by
  have hfamilies :=
    Lemma12Numerics.eventually_exists_martin_candidate_family
      (show (0 : ℝ) < 3 / 4 by norm_num)
      (show (3 : ℝ) / 4 < 1 by norm_num)
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hfamilies, hlogTop.eventually_ge_atTop 1]
      with x hfamily hlog
  intro r s hrange
  have hx : 0 < x := by
    have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlog
    have hxone : 1 < (x : ℝ) :=
      (Real.log_pos_iff (Nat.cast_nonneg x)).mp hlogpos
    exact_mod_cast (zero_lt_one.trans hxone)
  have hqpos : 0 < s.primePowerMeasure := by
    have hrootpos : 0 < (x : ℝ) ^ ((1 : ℝ) / 5) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hx) _
    have hqreal : (0 : ℝ) < s.primePowerMeasure :=
      hrootpos.trans_le hrange.1
    exact_mod_cast hqreal
  have hqpart : s.primePowerMeasure ∈
      PrimePowers.primePowerParts s.residual.den :=
    largestPrimePowerPart_mem_of_pos hqpos
  have hqpp : IsPrimePow s.primePowerMeasure :=
    ((PrimePowers.mem_primePowerParts s.residual.den_ne_zero).mp hqpart).1
  rcases (isPrimePow_nat_iff s.primePowerMeasure).1 hqpp with
    ⟨p, ν, hp, hν, hqeq⟩
  obtain ⟨M, -, hM, -, -, -, -, -, hsurj⟩ :=
    hfamily p ν hp hν (by simpa [hqeq] using hrange)
  have hsurj' : Lemma12.BoundedInverseSubsetSurjective s.primePowerMeasure
      (Lemma12.martinBlockBound x s.primePowerMeasure) M := by
    rw [← hqeq]
    exact hsurj
  apply lemma12StepData_of_rawCandidateFamily
      (s := s) (M := M) (p := p) (ν := ν)
  · norm_num
  · norm_num
  · exact hx
  · exact hp
  · exact hν
  · exact hqeq.symm
  · exact inEliminationRange_of_strongRange hlog hrange
  · simpa [hqeq] using hM
  · exact hsurj'

/--
The complete output of the descending removal recursion, including the union of
all removed blocks and the explicit sum of their individual Lemma 12 bounds.
-/
structure RemovalDescentOutcome
    (base : Finset ℕ) (x y : ℕ) {r : ℚ}
    (start : ResidualApproximationState r) where
  final : ResidualApproximationState r
  removed : Finset ℕ
  coherent : final.Coherent
  available : AvailableBelow base final
  measure_le : final.primePowerMeasure ≤ y
  removed_subset_base : removed ⊆ base
  removed_subset_selected : removed ⊆ start.terms.selected
  selected_eq : final.terms.selected = start.terms.selected \ removed
  used_eq : final.terms.used = start.terms.used
  residual_eq : final.residual = start.residual + UnitFractions.rec_sum removed
  card_le : removed.card ≤ totalEliminationBudget x start.primePowerMeasure

lemma RemovalDescentOutcome.final_card_eq
    {base : Finset ℕ} {x y : ℕ} {r : ℚ}
    {start : ResidualApproximationState r}
    (out : RemovalDescentOutcome base x y start) :
    out.final.terms.selected.card =
      start.terms.selected.card - out.removed.card := by
  rw [out.selected_eq, Finset.card_sdiff_of_subset out.removed_subset_selected]

/-- A removal-only step leaves the ever-used set unchanged. -/
lemma eliminationRemovalStep_used {r : ℚ} {s : ResidualApproximationState r}
    {U : Finset ℕ} (hs : s.Coherent) (hU : U ⊆ s.terms.selected) :
    (s.applyStep (eliminationRemovalStep U)
      (eliminationRemovalStep_valid hs hU)).terms.used = s.terms.used := by
  simp [ResidualApproximationState.applyStep, ApproximationState.applyStep,
    eliminationRemovalStep]

/--
Well-founded descending recursion with exact removal-set bookkeeping.  The
one-step premise is precisely what `lemma12_eliminationRemovalStep` proves from
concrete candidate data and bounded inverse-subset surjectivity.
-/
noncomputable def exists_removalDescentOutcome
    (base : Finset ℕ) (x y measureBound : ℕ) {r : ℚ}
    (start : ResidualApproximationState r) (hcoh : start.Coherent)
    (havail : AvailableBelow base start)
    (hbound : start.primePowerMeasure ≤ measureBound)
    (hstep : ∀ s : ResidualApproximationState r, s.Coherent →
      AvailableBelow base s → s.primePowerMeasure ≤ measureBound →
      y < s.primePowerMeasure →
      ∃ U : Finset ℕ,
        U.card ≤ Lemma12.martinBlockBound x s.primePowerMeasure ∧
        U ⊆ base ∧
        ∃ hp : (eliminationRemovalStep U).Valid s.terms,
          (s.applyStep (eliminationRemovalStep U) hp).primePowerMeasure <
            s.primePowerMeasure ∧
          AvailableBelow base (s.applyStep (eliminationRemovalStep U) hp)) :
    RemovalDescentOutcome base x y start := by
  induction hmeasure : start.primePowerMeasure using Nat.strongRecOn generalizing start with
  | ind q ih =>
      by_cases hdone : start.primePowerMeasure ≤ y
      · exact
          { final := start
            removed := ∅
            coherent := hcoh
            available := havail
            measure_le := hdone
            removed_subset_base := by simp
            removed_subset_selected := by simp
            selected_eq := by simp
            used_eq := rfl
            residual_eq := by simp
            card_le := by simp }
      · have habove : y < start.primePowerMeasure := Nat.lt_of_not_ge hdone
        let hstage := hstep start hcoh havail hbound habove
        let U : Finset ℕ := Classical.choose hstage
        have hUfacts := Classical.choose_spec hstage
        have hUcard : U.card ≤
            Lemma12.martinBlockBound x start.primePowerMeasure := hUfacts.1
        have hUbase : U ⊆ base := hUfacts.2.1
        let hp : (eliminationRemovalStep U).Valid start.terms :=
          Classical.choose hUfacts.2.2
        have hpFacts := Classical.choose_spec hUfacts.2.2
        have hdesc :
            (start.applyStep (eliminationRemovalStep U) hp).primePowerMeasure <
              start.primePowerMeasure := hpFacts.1
        have hnextAvail : AvailableBelow base
            (start.applyStep (eliminationRemovalStep U) hp) := hpFacts.2
        have hUselected : U ⊆ start.terms.selected := hp.2.1
        let next := start.applyStep (eliminationRemovalStep U) hp
        have hnextCoh : next.Coherent :=
          ResidualApproximationState.Coherent.applyStep hp
        have hnextSelected : next.terms.selected = start.terms.selected \ U := by
          simp [next, ResidualApproximationState.applyStep,
            ApproximationState.applyStep, eliminationRemovalStep]
        have hnextMeasure : next.primePowerMeasure < q := by
          rw [← hmeasure]
          exact hdesc
        have hnextBound : next.primePowerMeasure ≤ measureBound :=
          hdesc.le.trans hbound
        have tail :=
          ih next.primePowerMeasure hnextMeasure next hnextCoh hnextAvail hnextBound rfl
        let removed := U ∪ tail.removed
        have hdisjoint : Disjoint U tail.removed := by
          rw [Finset.disjoint_left]
          intro n hnU hnTail
          have hnNext : n ∈ next.terms.selected := tail.removed_subset_selected hnTail
          have hnDiff : n ∈ start.terms.selected \ U := by
            rwa [hnextSelected] at hnNext
          exact (Finset.mem_sdiff.mp hnDiff).2 hnU
        refine
          { final := tail.final
            removed := removed
            coherent := tail.coherent
            available := tail.available
            measure_le := tail.measure_le
            removed_subset_base := ?_
            removed_subset_selected := ?_
            selected_eq := ?_
            used_eq := ?_
            residual_eq := ?_
            card_le := ?_ }
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnTail
          · exact hUbase hnU
          · exact tail.removed_subset_base hnTail
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnTail
          · exact hUselected hnU
          · have hnNext := tail.removed_subset_selected hnTail
            have hnDiff : n ∈ start.terms.selected \ U := by
              rwa [hnextSelected] at hnNext
            exact (Finset.mem_sdiff.mp hnDiff).1
        · rw [tail.selected_eq]
          ext n
          simp only [hnextSelected, Finset.mem_sdiff]
          simp [removed]
          tauto
        · rw [tail.used_eq]
          exact eliminationRemovalStep_used hcoh hUselected
        · rw [tail.residual_eq]
          have hnextResidual : next.residual =
              start.residual + UnitFractions.rec_sum U := by
            simpa [next] using eliminationRemovalStep_residual hcoh hUselected
          rw [hnextResidual, UnitFractions.rec_sum_disjoint hdisjoint]
          ring
        · rw [Finset.card_union_of_disjoint hdisjoint]
          have htailBudget :
              totalEliminationBudget x next.primePowerMeasure ≤
                ∑ i ∈ Finset.range start.primePowerMeasure,
                  Lemma12.martinBlockBound x i := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.range_mono hdesc
            · simp
          calc
            U.card + tail.removed.card ≤
                Lemma12.martinBlockBound x start.primePowerMeasure +
                  totalEliminationBudget x next.primePowerMeasure :=
              Nat.add_le_add hUcard tail.card_le
            _ ≤ Lemma12.martinBlockBound x start.primePowerMeasure +
                ∑ i ∈ Finset.range start.primePowerMeasure,
                  Lemma12.martinBlockBound x i := Nat.add_le_add_left htailBudget _
            _ = totalEliminationBudget x start.primePowerMeasure := by
              rw [totalEliminationBudget, Finset.sum_range_succ]
              omega

/--
Run the removal recursion using the actual finite conclusion of Martin's
Lemma 12, rather than an abstract one-step eliminator.  The only input left in
this theorem is `Lemma12StepData`, the exact interface proved by the explicit
four-prime candidate and subset-sum construction.
-/
noncomputable def lemma12RemovalDescent
    (alpha xi z : ℝ) (base : Finset ℕ) (x y measureBound : ℕ)
    {r : ℚ} (start : ResidualApproximationState r)
    (hbase : base = initialSmoothBlock alpha x z)
    (hcoh : start.Coherent) (havail : AvailableBelow base start)
    (hbound : start.primePowerMeasure ≤ measureBound)
    (hboundZ : (measureBound : ℝ) ≤ z)
    (halpha : 0 ≤ alpha)
    (hxi : (⌊alpha * (x : ℝ)⌋₊ : ℝ) < xi * x)
    (hdata : ∀ s : ResidualApproximationState r, s.Coherent →
      AvailableBelow base s → s.primePowerMeasure ≤ measureBound →
      y < s.primePowerMeasure → Lemma12StepData xi x s) :
    RemovalDescentOutcome base x y start :=
  exists_removalDescentOutcome base x y measureBound start hcoh havail hbound
    (fun s hs ha hsBound hy ↦ by
      have hqz : (s.primePowerMeasure : ℝ) ≤ z := by
        have hcast : (s.primePowerMeasure : ℝ) ≤ measureBound := by
          exact_mod_cast hsBound
        exact hcast.trans hboundZ
      obtain ⟨M, hMdata, hMsurj⟩ := hdata s hs ha hsBound hy
      subst base
      exact lemma12_eliminationRemovalStep hs ha hMdata hMsurj halpha hxi hqz)

/-! ## Exact padding and certificate assembly -/

/-- The rational residual left by the explicit initial smooth block. -/
def initialResidual (r : ℚ) (alpha : ℝ) (x : ℕ) (z : ℝ) : ℚ :=
  r - UnitFractions.rec_sum (initialSmoothBlock alpha x z)

/-- Initial block and initial residual bundled with their exact balance. -/
def initialResidualApproximationState
    (r : ℚ) (alpha : ℝ) (x : ℕ) (z : ℝ) :
    ResidualApproximationState r where
  terms := initialApproximationState alpha x z
  residual := initialResidual r alpha x z
  balance := by
    simp [initialResidual, initialApproximationState]

/-- The initial residual inherits the smoothness bound of both the target
rational and every denominator in the initial block. -/
lemma initialResidual_den_isSmooth
    {r : ℚ} {alpha z : ℝ} {x : ℕ}
    (hr : UnitFractions.is_smooth z r.den) :
    UnitFractions.is_smooth z (initialResidual r alpha x z).den := by
  rw [initialResidual]
  apply sub_recSum_den_isSmooth r hr
  · intro n hn hn0
    subst n
    exact initialSmoothBlock_zero_not_mem alpha z x hn
  · intro n hn
    exact initialSmoothBlock_smooth hn

/-- Consequently the starting descent measure is at most the natural smooth
cutoff. -/
lemma initialResidualApproximationState_measure_le_floor
    {r : ℚ} {alpha z : ℝ} {x : ℕ} (hz : 0 ≤ z)
    (hr : UnitFractions.is_smooth z r.den) :
    (initialResidualApproximationState r alpha x z).primePowerMeasure ≤ ⌊z⌋₊ := by
  apply largestPrimePowerPart_le_floor_of_isSmooth hz
  exact initialResidual_den_isSmooth hr

/-- Specialization of the starting-measure bound to the target rational `1`. -/
lemma initialResidualApproximationState_one_measure_le_floor
    {alpha z : ℝ} {x : ℕ} (hz : 0 ≤ z) :
    (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure ≤
      ⌊z⌋₊ := by
  apply initialResidualApproximationState_measure_le_floor hz
  intro q hq hqdiv
  have hqone : q = 1 := Nat.dvd_one.mp (by simpa using hqdiv)
  exact (hq.ne_one hqone).elim

/-- The complete Lemma 12 recursion for the target rational `1`, uniform in
every moving lower endpoint below `3/4`.  All candidate and subset-sum inputs
come from the proved eventual theorem above. -/
theorem eventually_concreteRemovalDescent_one :
    ∀ᶠ x : ℕ in atTop, ∀ (alpha : ℝ), 0 ≤ alpha → alpha < (3 : ℝ) / 4 →
      Nonempty (RemovalDescentOutcome
        (initialSmoothBlock alpha x (proposition6MainCutoff x)) x
        (approximationCorrectionScale x)
        (initialResidualApproximationState (1 : ℚ) alpha x
          (proposition6MainCutoff x))) := by
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_lemma12StepData_threeFourths,
    eventually_ge_atTop 1, hlogTop.eventually_ge_atTop 1]
      with x hstepData hx hlog
  intro alpha halpha halphaXi
  let z := proposition6MainCutoff x
  let y := approximationCorrectionScale x
  let Q := ⌊z⌋₊
  let start := initialResidualApproximationState (1 : ℚ) alpha x z
  have hz : 0 ≤ z := by
    dsimp [z, proposition6MainCutoff]
    positivity
  have hbound : start.primePowerMeasure ≤ Q := by
    exact initialResidualApproximationState_one_measure_le_floor hz
  have hQz : (Q : ℝ) ≤ z := by
    exact Nat.floor_le hz
  have hxi : (⌊alpha * (x : ℝ)⌋₊ : ℝ) < ((3 : ℝ) / 4) * x := by
    have hfloor : (⌊alpha * (x : ℝ)⌋₊ : ℝ) ≤ alpha * x :=
      Nat.floor_le (mul_nonneg halpha (Nat.cast_nonneg x))
    have hxR : (0 : ℝ) < x := by exact_mod_cast (Nat.zero_lt_of_lt hx)
    exact hfloor.trans_lt (mul_lt_mul_of_pos_right halphaXi hxR)
  have hdata : ∀ s : ResidualApproximationState (1 : ℚ), s.Coherent →
      AvailableBelow (initialSmoothBlock alpha x z) s →
      s.primePowerMeasure ≤ Q → y < s.primePowerMeasure →
      Lemma12StepData ((3 : ℝ) / 4) x s := by
    intro s _ _ hsQ hys
    apply hstepData s
    constructor
    · have hrootLt : (x : ℝ) ^ ((5 : ℝ)⁻¹) <
          ((⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊ + 1 : ℕ) : ℝ) := by
        simpa using Nat.lt_floor_add_one ((x : ℝ) ^ ((5 : ℝ)⁻¹))
      have hsucc : ⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊ + 1 ≤
          s.primePowerMeasure := by
        change y + 1 ≤ s.primePowerMeasure
        omega
      have hsuccR : ((⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊ + 1 : ℕ) : ℝ) ≤
          (s.primePowerMeasure : ℝ) := by exact_mod_cast hsucc
      simpa only [show ((5 : ℝ)⁻¹) = (1 : ℝ) / 5 by norm_num] using
        hrootLt.le.trans hsuccR
    · have hqQ : (s.primePowerMeasure : ℝ) ≤ Q := by
        exact_mod_cast hsQ
      have hupper := hqQ.trans hQz
      calc
        (s.primePowerMeasure : ℝ) ≤ z := hupper
        _ = (x : ℝ) * Real.log x ^ (-30 : ℝ) := by
          dsimp [z, proposition6MainCutoff]
          rw [show (-30 : ℝ) = -(30 : ℝ) by norm_num,
            Real.rpow_neg (zero_lt_one.trans_le hlog).le,
            show (30 : ℝ) = ((30 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
          ring
  exact ⟨lemma12RemovalDescent alpha ((3 : ℝ) / 4) z
    (initialSmoothBlock alpha x z) x y Q start rfl
    (by exact Finset.Subset.rfl)
    (by intro n hn _; exact hn) hbound hQz halpha hxi hdata⟩

/--
Turn a completed Lemma 12 removal descent into a Proposition 6 certificate.
All loss estimates are explicit in the hypotheses: the removal union is
bounded by `totalEliminationBudget`, and the same quantity controls both the
reservoir capacity and the reciprocal-sum margins.  No analytic or
number-theoretic conclusion is assumed inside the bookkeeping proof.
-/
theorem exists_approximationCertificate_of_removalDescent
    {r : ℚ} {alpha beta z : ℝ} {x y R : ℕ}
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hbeta : 0 < beta) (hbetaAlpha : beta ≤ alpha)
    (hExpLe : Real.exp (-(r : ℝ)) ≤ beta) (hx : 0 < x)
    (out : RemovalDescentOutcome (initialSmoothBlock alpha x z) x y
      (initialResidualApproximationState r alpha x z))
    (hmainCard : (initialSmoothBlock alpha x z).card ≤ R)
    (hcapacity :
      R - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState r alpha x z).primePowerMeasure ≤
        (smoothReservoir (proposition6ReservoirScale beta x)).card)
    (hyRoot : (y : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹))
    (hlowerPositive :
      0 < (Real.log (x : ℝ))⁻¹)
    (hlowerXMargin :
      (Real.log (x : ℝ))⁻¹ +
          ((R - (initialSmoothBlock alpha x z).card +
              totalEliminationBudget x
                (initialResidualApproximationState r alpha x z).primePowerMeasure : ℕ) : ℝ) /
            (beta * x / 2) <
        (initialResidual r alpha x z : ℝ))
    (hupperMargin :
      (initialResidual r alpha x z : ℝ) +
          (totalEliminationBudget x
              (initialResidualApproximationState r alpha x z).primePowerMeasure : ℝ) /
            (alpha * x) < 1) :
    Nonempty (ApproximationCertificate r x R) := by
  let start := initialResidualApproximationState r alpha x z
  let reservoir := smoothReservoir (proposition6ReservoirScale beta x)
  have hfinalCardEq : out.final.terms.selected.card =
      (initialSmoothBlock alpha x z).card - out.removed.card := by
    simpa [start, initialResidualApproximationState, initialApproximationState] using
      out.final_card_eq
  have hfinalCard : out.final.terms.selected.card ≤ R := by
    rw [hfinalCardEq]
    omega
  have hneed : R - out.final.terms.selected.card ≤ reservoir.card := by
    have houtBudget := out.card_le
    have hneedBound : R - out.final.terms.selected.card ≤
        R - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState r alpha x z).primePowerMeasure := by
      rw [hfinalCardEq]
      omega
    exact hneedBound.trans (by simpa [reservoir] using hcapacity)
  have hfresh : Disjoint out.final.terms.used reservoir := by
    rw [out.used_eq]
    change Disjoint (initialSmoothBlock alpha x z) reservoir
    simpa [reservoir] using proposition6Reservoir_disjoint_initial_of_le
      (x := x) (z := z) hbeta hbetaAlpha
  obtain ⟨padding, hpadding, hpaddingUsed, hp, hcard, hcoherent,
      hresidual, hbalance, hpaddingProps⟩ :=
    exists_fivePrimeReservoir_padding hbeta out.coherent hfinalCard hneed hfresh
  let completed := out.final.applyStep (reservoirPaddingStep padding) hp
  have hpaddingCard : padding.card = R - out.final.terms.selected.card := by
    have hselected := reservoirPaddingStep_selected hpaddingUsed out.coherent
    have hdis : Disjoint out.final.terms.selected padding :=
      hpaddingUsed.mono_right out.coherent |>.symm
    have hcardUnion : (out.final.terms.selected ∪ padding).card =
        out.final.terms.selected.card + padding.card :=
      Finset.card_union_of_disjoint hdis
    have hcompletedCard : completed.terms.selected.card = R := by
      simpa [completed] using hcard
    rw [hselected, hcardUnion] at hcompletedCard
    omega
  have hpaddingCardBound : padding.card ≤
      R - (initialSmoothBlock alpha x z).card +
        totalEliminationBudget x
          (initialResidualApproximationState r alpha x z).primePowerMeasure := by
    rw [hpaddingCard, hfinalCardEq]
    have houtBudget := out.card_le
    omega
  have halphaX : 0 < alpha * (x : ℝ) :=
    mul_pos halpha (by exact_mod_cast hx)
  have hbetaX : 0 < beta * (x : ℝ) :=
    mul_pos hbeta (by exact_mod_cast hx)
  have hremovedSum : ((UnitFractions.rec_sum out.removed : ℚ) : ℝ) ≤
      (out.removed.card : ℝ) / (alpha * x) := by
    apply UnitFractions.rec_sum_le_card_div halphaX
    intro n hn
    exact (initialSmoothBlock_lower halpha.le (out.removed_subset_base hn)).le
  have hpaddingSum : ((UnitFractions.rec_sum padding : ℚ) : ℝ) ≤
      (padding.card : ℝ) / (beta * x / 2) := by
    apply UnitFractions.rec_sum_le_card_div (div_pos hbetaX (by norm_num))
    intro n hn
    exact (hpaddingProps n hn).1.le
  have hremovedNonneg :
      0 ≤ ((UnitFractions.rec_sum out.removed : ℚ) : ℝ) := by
    exact_mod_cast UnitFractions.rec_sum_nonneg
  have hpaddingNonneg :
      0 ≤ ((UnitFractions.rec_sum padding : ℚ) : ℝ) := by
    exact_mod_cast UnitFractions.rec_sum_nonneg
  have hremovedBudget : ((UnitFractions.rec_sum out.removed : ℚ) : ℝ) ≤
      (totalEliminationBudget x
          (initialResidualApproximationState r alpha x z).primePowerMeasure : ℝ) /
        (alpha * x) := by
    refine hremovedSum.trans ?_
    apply div_le_div_of_nonneg_right _ halphaX.le
    exact_mod_cast out.card_le
  have hpaddingBudget : ((UnitFractions.rec_sum padding : ℚ) : ℝ) ≤
      ((R - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState r alpha x z).primePowerMeasure : ℕ) : ℝ) /
        (beta * x / 2) := by
    refine hpaddingSum.trans ?_
    apply div_le_div_of_nonneg_right _ (div_nonneg hbetaX.le (by norm_num))
    exact_mod_cast hpaddingCardBound
  have hcompletedResidualQ : completed.residual =
      initialResidual r alpha x z + UnitFractions.rec_sum out.removed -
        UnitFractions.rec_sum padding := by
    rw [show completed.residual = out.final.residual -
        UnitFractions.rec_sum padding by simpa [completed] using hresidual,
      out.residual_eq]
    rfl
  have hcompletedResidualR : (completed.residual : ℝ) =
      (initialResidual r alpha x z : ℝ) +
        (UnitFractions.rec_sum out.removed : ℝ) -
        (UnitFractions.rec_sum padding : ℝ) := by
    have hcast := congrArg (fun u : ℚ ↦ (u : ℝ)) hcompletedResidualQ
    norm_num at hcast ⊢
    exact hcast
  have hlowerX : (Real.log (x : ℝ))⁻¹ < (completed.residual : ℝ) := by
    rw [hcompletedResidualR]
    nlinarith
  have hupper : (completed.residual : ℝ) < 1 := by
    rw [hcompletedResidualR]
    nlinarith
  have hpositiveR : (0 : ℝ) < (completed.residual : ℝ) :=
    hlowerPositive.trans hlowerX
  have hpositiveQ : (0 : ℚ) < completed.residual := by
    exact_mod_cast hpositiveR
  have hrootNonneg : 0 ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹) :=
    Real.rpow_nonneg (Nat.cast_nonneg x) _
  have hfinalSmooth : UnitFractions.is_smooth
      ((x : ℝ) ^ ((5 : ℝ)⁻¹)) out.final.residual.den := by
    apply isSmooth_of_largestPrimePowerPart_le hrootNonneg out.final.residual.den_ne_zero
    exact (by exact_mod_cast out.measure_le :
      (out.final.primePowerMeasure : ℝ) ≤ y) |>.trans hyRoot
  have hreservoirScaleLeRoot : proposition6ReservoirScale beta x ≤
      (x : ℝ) ^ ((5 : ℝ)⁻¹) := by
    apply Real.rpow_le_rpow
    · exact mul_nonneg hbeta.le (Nat.cast_nonneg x)
    · exact mul_le_of_le_one_left (Nat.cast_nonneg x)
        (hbetaAlpha.trans halphaOne)
    · norm_num
  have hpaddingSmooth : ∀ n ∈ padding,
      UnitFractions.is_smooth ((x : ℝ) ^ ((5 : ℝ)⁻¹)) n := by
    intro n hn q hq hqn
    exact (smoothReservoir_primePower_bound (hpadding hn) q hq hqn).trans
      hreservoirScaleLeRoot
  have hpaddingZero : ∀ n ∈ padding, n ≠ 0 := by
    intro n hn hn0
    subst n
    have hzeroLower := (hpaddingProps 0 hn).1
    norm_num at hzeroLower
    nlinarith
  have hcompletedSmooth : UnitFractions.is_smooth
      ((x : ℝ) ^ ((5 : ℝ)⁻¹)) completed.residual.den := by
    rw [show completed.residual = out.final.residual -
        UnitFractions.rec_sum padding by simpa [completed] using hresidual]
    exact sub_recSum_den_isSmooth out.final.residual hfinalSmooth
      hpaddingZero hpaddingSmooth
  have hprimePowerBound :=
    primePower_pow_five_le_of_den_isSmooth hcompletedSmooth
  have hcompletedZero : 0 ∉ completed.terms.selected := by
    intro hzero
    have hselected := reservoirPaddingStep_selected hpaddingUsed out.coherent
    rw [show completed.terms.selected = out.final.terms.selected ∪ padding by
      simpa [completed] using hselected, Finset.mem_union] at hzero
    rcases hzero with hzero | hzero
    · have hfinalSubset : out.final.terms.selected ⊆ initialSmoothBlock alpha x z := by
        rw [out.selected_eq]
        exact Finset.sdiff_subset.trans (by
          change (initialSmoothBlock alpha x z) ⊆ initialSmoothBlock alpha x z
          exact Finset.Subset.rfl)
      exact initialSmoothBlock_zero_not_mem alpha z x (hfinalSubset hzero)
    · exact hpaddingZero 0 hzero rfl
  have hcompletedInterval : ∀ n ∈ completed.terms.selected,
      Real.exp (-(r : ℝ)) * (x : ℝ) / 2 ≤ (n : ℝ) ∧
        (n : ℝ) ≤ x := by
    intro n hn
    have hselected := reservoirPaddingStep_selected hpaddingUsed out.coherent
    rw [show completed.terms.selected = out.final.terms.selected ∪ padding by
      simpa [completed] using hselected, Finset.mem_union] at hn
    rcases hn with hn | hn
    · have hnBase : n ∈ initialSmoothBlock alpha x z := by
        rw [out.selected_eq] at hn
        exact Finset.sdiff_subset hn
      constructor
      · calc
          Real.exp (-(r : ℝ)) * (x : ℝ) / 2 ≤ alpha * (x : ℝ) / 2 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hExpLe.trans hbetaAlpha)
                (Nat.cast_nonneg x)) (by norm_num)
          _ ≤ alpha * (x : ℝ) :=
            div_le_self (mul_nonneg halpha.le (Nat.cast_nonneg x)) (by norm_num)
          _ ≤ (n : ℝ) := (initialSmoothBlock_lower halpha.le hnBase).le
      · exact_mod_cast initialSmoothBlock_upper hnBase
    · have hpdata := hpaddingProps n hn
      constructor
      · exact (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hExpLe (Nat.cast_nonneg x)) (by norm_num)).trans
            hpdata.1.le
      · have hleBetaAlpha : beta * (x : ℝ) ≤ alpha * x :=
          mul_le_mul_of_nonneg_right hbetaAlpha (Nat.cast_nonneg x)
        have hleAlpha : alpha * (x : ℝ) ≤ x :=
          mul_le_of_le_one_left (Nat.cast_nonneg x) halphaOne
        exact hpdata.2.1.trans (hleBetaAlpha.trans hleAlpha)
  exact ⟨approximationCertificate_of_residualState completed
    (by simpa [completed] using hcard) hcompletedZero hcompletedInterval
    hpositiveQ hlowerX hupper hprimePowerBound⟩

/--
Finite last-crossing wrapper for the preceding certificate constructor.  If
the score `initial.card + correction` lies below `t`, its deficit and the full
Lemma 12 loss are each at most `D`, and the reservoir contains `2D` terms,
then all exact-cardinality and reciprocal-mass hypotheses follow.  This is the
arithmetic interface consumed by the final eventual construction.
-/
theorem exists_approximationCertificate_one_of_budget
    {alpha beta z : ℝ} {x y t correction D : ℕ}
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hbeta : 0 < beta) (hbetaAlpha : beta ≤ alpha)
    (hExpLe : Real.exp (-1) ≤ beta) (hx : 0 < x)
    (out : RemovalDescentOutcome (initialSmoothBlock alpha x z) x y
      (initialResidualApproximationState (1 : ℚ) alpha x z))
    (hscore : (initialSmoothBlock alpha x z).card + correction ≤ t)
    (hdeficit : t - ((initialSmoothBlock alpha x z).card + correction) ≤ D)
    (hbudget : totalEliminationBudget x
      (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure ≤ D)
    (hreservoir : 2 * D ≤
      (smoothReservoir (proposition6ReservoirScale beta x)).card)
    (hyRoot : (y : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹))
    (hlowerPositive : 0 < (Real.log (x : ℝ))⁻¹)
    (hlowerMargin :
      (Real.log (x : ℝ))⁻¹ +
          4 * (D : ℝ) / (beta * x) <
        (initialResidual (1 : ℚ) alpha x z : ℝ))
    (hupperMargin :
      (initialResidual (1 : ℚ) alpha x z : ℝ) +
          (D : ℝ) / (alpha * x) < 1) :
    Nonempty (ApproximationCertificate (1 : ℚ) x (t - correction)) := by
  have hmainCard : (initialSmoothBlock alpha x z).card ≤ t - correction := by
    omega
  have hrequestedDeficit :
      (t - correction) - (initialSmoothBlock alpha x z).card =
        t - ((initialSmoothBlock alpha x z).card + correction) := by
    omega
  have hcount :
      (t - correction) - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure ≤
        2 * D := by
    rw [hrequestedDeficit]
    omega
  have hcapacity :
      (t - correction) - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure ≤
        (smoothReservoir (proposition6ReservoirScale beta x)).card :=
    hcount.trans hreservoir
  have halphaX : 0 < alpha * (x : ℝ) :=
    mul_pos halpha (by exact_mod_cast hx)
  have hbetaX : 0 < beta * (x : ℝ) :=
    mul_pos hbeta (by exact_mod_cast hx)
  have hcountR :
      (((t - correction) - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure : ℕ) : ℝ) ≤
        2 * D := by
    exact_mod_cast hcount
  have hquotient :
      (((t - correction) - (initialSmoothBlock alpha x z).card +
          totalEliminationBudget x
            (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure : ℕ) : ℝ) /
          (beta * x / 2) ≤
        4 * (D : ℝ) / (beta * x) := by
    calc
      _ ≤ (2 * (D : ℝ)) / (beta * x / 2) := by
        exact div_le_div_of_nonneg_right hcountR
          (div_nonneg hbetaX.le (by norm_num))
      _ = 4 * (D : ℝ) / (beta * x) := by field_simp; ring
  have hlowerNeeded :
      (Real.log (x : ℝ))⁻¹ +
          (((t - correction) - (initialSmoothBlock alpha x z).card +
              totalEliminationBudget x
                (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure : ℕ) : ℝ) /
            (beta * x / 2) <
        (initialResidual (1 : ℚ) alpha x z : ℝ) := by
    calc
      _ ≤ (Real.log (x : ℝ))⁻¹ + 4 * (D : ℝ) / (beta * x) := by
        exact add_le_add_right hquotient _
      _ < (initialResidual (1 : ℚ) alpha x z : ℝ) := hlowerMargin
  have hbudgetR :
      (totalEliminationBudget x
        (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure : ℝ) ≤ D := by
    exact_mod_cast hbudget
  have hupperNeeded :
      (initialResidual (1 : ℚ) alpha x z : ℝ) +
          (totalEliminationBudget x
              (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure : ℝ) /
            (alpha * x) < 1 := by
    calc
      _ ≤ (initialResidual (1 : ℚ) alpha x z : ℝ) +
          (D : ℝ) / (alpha * x) := by
        exact add_le_add_right
          (div_le_div_of_nonneg_right hbudgetR halphaX.le) _
      _ < 1 := hupperMargin
  exact exists_approximationCertificate_of_removalDescent
    halpha halphaOne hbeta hbetaAlpha (by simpa using hExpLe) hx out
    hmainCard hcapacity hyRoot
    hlowerPositive hlowerNeeded hupperNeeded

/--
A concrete elimination stage: the finite-set step is valid and strictly lowers
the largest exact prime-power part of the reduced residual denominator.
-/
def ApproximationStep.EliminatesLargestPrimePower {r : ℚ}
    (s : ResidualApproximationState r) (d : ApproximationStep) : Prop :=
  ∃ hd : d.Valid s.terms,
    (s.applyStep d hd).primePowerMeasure < s.primePowerMeasure

lemma ApproximationStep.EliminatesLargestPrimePower.valid {r : ℚ}
    {s : ResidualApproximationState r} {d : ApproximationStep}
    (h : d.EliminatesLargestPrimePower s) : d.Valid s.terms := by
  exact h.choose

/-! ## Concrete initialization -/

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/RoughCounts.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős Problem 285: rough-denominator counting

This file isolates the finite union bound in Martin's Lemma 9.  An integer whose
largest exact prime-power part exceeds `y` is a multiple of a prime power in
`(y,x]`.  Consequently its count, and its reciprocal mass in an interval bounded
away from zero, are controlled by the reciprocal mass of those prime powers.

The last section combines this finite estimate with the prime-power Mertens
estimate already proved in `UnitFractions.ForMathlib.BasicEstimates`.  It is
phrased for a general moving cutoff.  In particular it applies as soon as one
has the elementary logarithmic calculation for `y = x / log(x)^A`.
-/

namespace RoughCounts

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos285.PrimePowers

/-- Prime powers in the half-open interval `(y,x]`. -/
def largePrimePowers (x y : ℕ) : Finset ℕ :=
  (Icc (y + 1) x).filter IsPrimePow

/-- Integers in `[L,x]` whose largest exact prime-power part is larger than `y`. -/
def roughNumbersIn (L x y : ℕ) : Finset ℕ :=
  (Icc L x).filter fun n ↦ y < largestPrimePowerPart n

/-- Multiples of `q` in `[1,x]`. -/
def multiplesUpTo (x q : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun n ↦ q ∣ n

/-- Reciprocal mass of the prime powers in `(y,x]`. -/
def primePowerReciprocalTail (x y : ℕ) : ℝ :=
  ∑ q ∈ largePrimePowers x y, (q : ℝ)⁻¹

/-- Reciprocal mass of a finite set of natural numbers. -/
def reciprocalMass (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, (n : ℝ)⁻¹

/-- The prime-power Mertens summatory function. -/
def primePowerReciprocalUpTo (x : ℕ) : ℝ :=
  ∑ q ∈ (Icc 1 x).filter IsPrimePow, (q : ℝ)⁻¹

/-- Martin's standard logarithmic cutoff, rounded down to a natural number. -/
def logPowerCutoff (A x : ℕ) : ℕ :=
  ⌊(x : ℝ) / Real.log (x : ℝ) ^ A⌋₊

/-- Natural left endpoint of a terminal interval `[alpha*x,x]`. -/
def proportionalLeftEndpoint (α : ℝ) (x : ℕ) : ℕ :=
  ⌈α * x⌉₊

@[simp] lemma mem_largePrimePowers {x y q : ℕ} :
    q ∈ largePrimePowers x y ↔ y < q ∧ q ≤ x ∧ IsPrimePow q := by
  simp only [largePrimePowers, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hyq, hqx⟩, hq⟩
    exact ⟨Nat.lt_of_succ_le hyq, hqx, hq⟩
  · rintro ⟨hyq, hqx, hq⟩
    exact ⟨⟨hyq, hqx⟩, hq⟩

@[simp] lemma mem_roughNumbersIn {L x y n : ℕ} :
    n ∈ roughNumbersIn L x y ↔ L ≤ n ∧ n ≤ x ∧ y < largestPrimePowerPart n := by
  simp [roughNumbersIn, and_assoc]

@[simp] lemma mem_multiplesUpTo {x q n : ℕ} :
    n ∈ multiplesUpTo x q ↔ 1 ≤ n ∧ n ≤ x ∧ q ∣ n := by
  simp [multiplesUpTo, and_assoc]

lemma reciprocalMass_nonneg (A : Finset ℕ) : 0 ≤ reciprocalMass A := by
  exact Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)

lemma primePowerReciprocalTail_nonneg (x y : ℕ) :
    0 ≤ primePowerReciprocalTail x y := by
  exact Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Every rough integer is covered by the multiples of its largest exact
prime-power part. -/
lemma roughNumbersIn_subset_biUnion (L x y : ℕ) :
    roughNumbersIn L x y ⊆
      (largePrimePowers x y).biUnion (multiplesUpTo x) := by
  intro n hn
  rw [mem_roughNumbersIn] at hn
  have hn2 : 2 ≤ n := by
    by_contra h
    have hnlt : n < 2 := Nat.lt_of_not_ge h
    have hempty : primePowerParts n = ∅ := primePowerParts_empty_iff.mpr hnlt
    have hz : largestPrimePowerPart n = 0 := by
      simp [largestPrimePowerPart, hempty]
    omega
  let q := largestPrimePowerPart n
  have hqmem : q ∈ primePowerParts n := largestPrimePowerPart_mem hn2
  have hqspec := (mem_primePowerParts (by omega : n ≠ 0)).mp hqmem
  rw [Finset.mem_biUnion]
  refine ⟨q, ?_, ?_⟩
  · rw [mem_largePrimePowers]
    exact ⟨hn.2.2, largestPrimePowerPart_le.trans hn.2.1, hqspec.1⟩
  · rw [mem_multiplesUpTo]
    exact ⟨by omega, hn.2.1, hqspec.2.1⟩

/-- The number of rough integers is at most the sum of the numbers of multiples
of the relevant prime powers. -/
lemma roughNumbersIn_card_le_sum_div (L x y : ℕ) :
    (roughNumbersIn L x y).card ≤
      ∑ q ∈ largePrimePowers x y, x / q := by
  calc
    (roughNumbersIn L x y).card ≤
        ((largePrimePowers x y).biUnion (multiplesUpTo x)).card :=
      Finset.card_le_card (roughNumbersIn_subset_biUnion L x y)
    _ ≤ ∑ q ∈ largePrimePowers x y, (multiplesUpTo x q).card :=
      Finset.card_biUnion_le
    _ = ∑ q ∈ largePrimePowers x y, x / q := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq1 : 1 ≤ q := (mem_largePrimePowers.mp hq).2.2.one_lt.le
      exact UnitFractions.count_multiples hq1

/-- Real-valued form of the union bound. -/
lemma roughNumbersIn_card_le_mul_tail (L x y : ℕ) :
    ((roughNumbersIn L x y).card : ℝ) ≤
      (x : ℝ) * primePowerReciprocalTail x y := by
  have hcast :
      ((↑(∑ q ∈ largePrimePowers x y, x / q) : ℕ) : ℝ) =
        ∑ q ∈ largePrimePowers x y, ((x / q : ℕ) : ℝ) := by
    norm_cast
  calc
    ((roughNumbersIn L x y).card : ℝ) ≤
        (↑(∑ q ∈ largePrimePowers x y, x / q) : ℕ) := by
      exact_mod_cast roughNumbersIn_card_le_sum_div L x y
    _ = ∑ q ∈ largePrimePowers x y, ((x / q : ℕ) : ℝ) := hcast
    _ ≤ ∑ q ∈ largePrimePowers x y, (x : ℝ) / q := by
      apply Finset.sum_le_sum
      intro q hq
      exact Nat.cast_div_le
    _ = (x : ℝ) * primePowerReciprocalTail x y := by
      simp only [primePowerReciprocalTail, div_eq_mul_inv, Finset.mul_sum]

/-- On an interval with positive left endpoint, reciprocal mass is bounded by
cardinality divided by that endpoint. -/
lemma reciprocalMass_le_card_div {A : Finset ℕ} {L : ℕ} (hL : 1 ≤ L)
    (hA : ∀ n ∈ A, L ≤ n) :
    reciprocalMass A ≤ (A.card : ℝ) / L := by
  calc
    reciprocalMass A ≤ ∑ n ∈ A, (L : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hL.trans (hA n hn)
      have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
      have hLn : (L : ℝ) ≤ n := by exact_mod_cast hA n hn
      exact (inv_le_inv₀ hnpos hLpos).2 hLn
    _ = (A.card : ℝ) / L := by
      simp [div_eq_mul_inv, nsmul_eq_mul]

/-- Reciprocal-mass version of the rough-number union bound. -/
lemma roughNumbersIn_reciprocalMass_le (L x y : ℕ) (hL : 1 ≤ L) :
    reciprocalMass (roughNumbersIn L x y) ≤
      ((x : ℝ) / L) * primePowerReciprocalTail x y := by
  calc
    reciprocalMass (roughNumbersIn L x y) ≤
        ((roughNumbersIn L x y).card : ℝ) / L := by
      apply reciprocalMass_le_card_div hL
      intro n hn
      exact (mem_roughNumbersIn.mp hn).1
    _ ≤ ((x : ℝ) * primePowerReciprocalTail x y) / L := by
      exact div_le_div_of_nonneg_right (roughNumbersIn_card_le_mul_tail L x y)
        (Nat.cast_nonneg L)
    _ = ((x : ℝ) / L) * primePowerReciprocalTail x y := by ring

/-- The tail is the difference of the two prime-power Mertens sums. -/
lemma primePowerReciprocalTail_eq_sub {x y : ℕ} (hyx : y ≤ x) :
    primePowerReciprocalTail x y =
      primePowerReciprocalUpTo x - primePowerReciprocalUpTo y := by
  let A := (Icc 1 x).filter IsPrimePow
  let B := (Icc 1 y).filter IsPrimePow
  have hBA : B ⊆ A := by
    intro q hq
    simp only [B, A, Finset.mem_filter, Finset.mem_Icc] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.trans hyx⟩, hq.2⟩
  change (∑ q ∈ largePrimePowers x y, (q : ℝ)⁻¹) =
    (∑ q ∈ A, (q : ℝ)⁻¹) - ∑ q ∈ B, (q : ℝ)⁻¹
  rw [← Finset.sum_sdiff hBA]
  rw [add_sub_cancel_right]
  apply Finset.sum_congr
  · ext q
    simp only [largePrimePowers, A, B, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hyq, hqx⟩, hqpp⟩
      refine ⟨⟨⟨hqpp.one_lt.le, hqx⟩, hqpp⟩, ?_⟩
      intro hqy
      omega
    · rintro ⟨⟨⟨hq1, hqx⟩, hqpp⟩, hnot⟩
      refine ⟨⟨?_, hqx⟩, hqpp⟩
      by_contra hyq
      apply hnot
      exact ⟨⟨hq1, Nat.le_of_not_gt hyq⟩, hqpp⟩
  · intro q hq
    rfl

/-- The error term in the prime-power Mertens formula tends to zero along the
natural numbers. -/
lemma exists_primePowerReciprocalUpTo_error_tendsto_zero :
    ∃ b : ℝ,
      Tendsto
        (fun x : ℕ ↦
          primePowerReciprocalUpTo x - (Real.log (Real.log (x : ℝ)) + b))
        atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := prime_power_reciprocal
  refine ⟨b, ?_⟩
  have hb' := hb.comp_tendsto tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun x : ℕ ↦ (Real.log (x : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_coe_at_top
  have hzero := hb'.trans_tendsto hinv
  simpa [Function.comp_def, primePowerReciprocalUpTo, Nat.floor_natCast] using hzero

/-! ## The cutoff `x / log(x)^A` -/

lemma logPowerScale_tendsto_atTop (A : ℕ) :
    Tendsto (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ) ^ A) atTop atTop := by
  have h := (UnitFractions.tendsto_mul_add_div_pow_log_at_top
    (1 : ℝ) 0 A zero_lt_one).comp tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using h

lemma logPowerCutoff_tendsto_atTop (A : ℕ) :
    Tendsto (logPowerCutoff A) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp (logPowerScale_tendsto_atTop A)

lemma logPowerCutoff_eventually_le (A : ℕ) :
    ∀ᶠ x : ℕ in atTop, logPowerCutoff A x ≤ x := by
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ))]
      with x hx
  have hden : (1 : ℝ) ≤ Real.log (x : ℝ) ^ A := one_le_pow₀ hx
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hscale0 : 0 ≤ (x : ℝ) / Real.log (x : ℝ) ^ A :=
    div_nonneg hx0 (zero_le_one.trans hden)
  have hfloor : (logPowerCutoff A x : ℝ) ≤
      (x : ℝ) / Real.log (x : ℝ) ^ A := by
    exact Nat.floor_le hscale0
  have hscale : (x : ℝ) / Real.log (x : ℝ) ^ A ≤ x :=
    div_le_self hx0 hden
  exact_mod_cast hfloor.trans hscale

lemma proportionalLeftEndpoint_eventually_one_le {α : ℝ} (hα : 0 < α) :
    ∀ᶠ x : ℕ in atTop, 1 ≤ proportionalLeftEndpoint α x := by
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [proportionalLeftEndpoint, Nat.one_le_ceil_iff]
  exact mul_pos hα (by exact_mod_cast hx)

lemma proportionalLeftEndpoint_eventually_ratio_le_inv {α : ℝ} (hα : 0 < α) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) / proportionalLeftEndpoint α x ≤ α⁻¹ := by
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hceilpos : (0 : ℝ) < proportionalLeftEndpoint α x := by
    exact_mod_cast (Nat.ceil_pos.mpr (mul_pos hα hxpos))
  rw [div_le_iff₀ hceilpos, inv_mul_eq_div, le_div_iff₀ hα]
  simpa [proportionalLeftEndpoint, mul_comm] using Nat.le_ceil (α * (x : ℝ))

lemma loglog_div_log_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))
      atTop (𝓝 0) := by
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_log_coe_at_top
  simpa [id, Function.comp_def] using h

lemma logPowerCutoff_ratio_tendsto_one (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦
        (logPowerCutoff A x : ℝ) /
          ((x : ℝ) / Real.log (x : ℝ) ^ A))
      atTop (𝓝 1) := by
  exact tendsto_nat_floor_div_atTop.comp (logPowerScale_tendsto_atTop A)

lemma log_logPowerCutoff_ratio_tendsto_zero (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦ Real.log
        ((logPowerCutoff A x : ℝ) /
          ((x : ℝ) / Real.log (x : ℝ) ^ A)))
      atTop (𝓝 0) := by
  have hcont : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
    simpa using (Real.continuousAt_log one_ne_zero).tendsto
  exact hcont.comp (logPowerCutoff_ratio_tendsto_one A)

lemma log_logPowerCutoff_div_log_tendsto_one (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦ Real.log (logPowerCutoff A x : ℝ) /
        Real.log (x : ℝ)) atTop (𝓝 1) := by
  let scale : ℕ → ℝ := fun x ↦ (x : ℝ) / Real.log (x : ℝ) ^ A
  let ratio : ℕ → ℝ := fun x ↦ (logPowerCutoff A x : ℝ) / scale x
  have hratio : Tendsto ratio atTop (𝓝 1) := by
    simpa [ratio, scale] using logPowerCutoff_ratio_tendsto_one A
  have hlogratio : Tendsto (fun x ↦ Real.log (ratio x)) atTop (𝓝 0) := by
    simpa [ratio, scale] using log_logPowerCutoff_ratio_tendsto_zero A
  have hlogratio_div : Tendsto
      (fun x : ℕ ↦ Real.log (ratio x) / Real.log (x : ℝ)) atTop (𝓝 0) :=
    hlogratio.div_atTop tendsto_log_coe_at_top
  have hmain : Tendsto
      (fun x : ℕ ↦
        1 - (A : ℝ) *
          (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) +
          Real.log (ratio x) / Real.log (x : ℝ)) atTop (𝓝 1) := by
    have hmiddle : Tendsto
        (fun x : ℕ ↦ -(A : ℝ) *
          (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)))
        atTop (𝓝 0) := by
      simpa using (loglog_div_log_tendsto_zero.const_mul (-(A : ℝ)))
    simpa [sub_eq_add_neg] using
      (tendsto_const_nhds.add hmiddle).add hlogratio_div
  apply hmain.congr'
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
      (logPowerScale_tendsto_atTop A).eventually (eventually_gt_atTop (0 : ℝ)),
      hratio.eventually (Ioi_mem_nhds zero_lt_one)] with x hlogx hxone hscale hratioPos
  have hxpos : (0 : ℝ) < x := zero_lt_one.trans hxone
  have hlogne : Real.log (x : ℝ) ≠ 0 := hlogx.ne'
  have hpowpos : 0 < Real.log (x : ℝ) ^ A := pow_pos hlogx A
  have hscalene : scale x ≠ 0 := hscale.ne'
  have hratione : ratio x ≠ 0 := hratioPos.ne'
  have hcutoff : (logPowerCutoff A x : ℝ) = ratio x * scale x := by
    dsimp [ratio]
    exact (div_mul_cancel₀ _ hscalene).symm
  rw [hcutoff, Real.log_mul hratione hscalene]
  dsimp [scale]
  rw [Real.log_div hxpos.ne' (pow_ne_zero A hlogne), Real.log_pow]
  field_simp
  ring

lemma logPowerCutoff_loglog_sub_tendsto_zero (A : ℕ) :
    Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (logPowerCutoff A x : ℝ)))
      atTop (𝓝 0) := by
  have hratio := log_logPowerCutoff_div_log_tendsto_one A
  have hlogratio : Tendsto
      (fun x : ℕ ↦ Real.log
        (Real.log (logPowerCutoff A x : ℝ) / Real.log (x : ℝ)))
      atTop (𝓝 0) := by
    have hcont : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact hcont.comp hratio
  have hneg := hlogratio.neg
  have hneg0 : Tendsto
      (fun x : ℕ ↦ -Real.log
        (Real.log (logPowerCutoff A x : ℝ) / Real.log (x : ℝ)))
      atTop (𝓝 0) := by simpa using hneg
  apply hneg0.congr'
  have hlogCutoffTop : Tendsto
      (fun x : ℕ ↦ Real.log (logPowerCutoff A x : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (logPowerCutoff_tendsto_atTop A))
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      hlogCutoffTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hcut
  rw [Real.log_div hcut.ne' hx.ne']
  ring

/-- A moving prime-power tail tends to zero whenever both endpoints tend to
infinity and their logarithmic logarithms become equal.  This is the exact
analytic interface needed for cutoffs such as `x / log(x)^A`. -/
lemma primePowerReciprocalTail_tendsto_zero {y : ℕ → ℕ}
    (hy_le : ∀ᶠ x in atTop, y x ≤ x)
    (hy_top : Tendsto y atTop atTop)
    (hlog : Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (y x : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun x : ℕ ↦ primePowerReciprocalTail x (y x)) atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := exists_primePowerReciprocalUpTo_error_tendsto_zero
  have hby := hb.comp hy_top
  have hsum := hlog.add (hb.sub hby)
  have hsum0 : Tendsto
      (fun x : ℕ ↦
        Real.log (Real.log (x : ℝ)) - Real.log (Real.log (y x : ℝ)) +
          ((primePowerReciprocalUpTo x - (Real.log (Real.log (x : ℝ)) + b)) -
            (primePowerReciprocalUpTo (y x) -
              (Real.log (Real.log (y x : ℝ)) + b)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hsum
  apply hsum0.congr'
  filter_upwards [hy_le] with x hyx
  rw [primePowerReciprocalTail_eq_sub hyx]
  ring

/-- The three moving-cutoff facts used when specializing Martin's union bound. -/
theorem logPowerCutoff_spec (A : ℕ) :
    (∀ᶠ x : ℕ in atTop, logPowerCutoff A x ≤ x) ∧
      Tendsto (logPowerCutoff A) atTop atTop ∧
      Tendsto
        (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
          Real.log (Real.log (logPowerCutoff A x : ℝ)))
        atTop (𝓝 0) :=
  ⟨logPowerCutoff_eventually_le A, logPowerCutoff_tendsto_atTop A,
    logPowerCutoff_loglog_sub_tendsto_zero A⟩

/-- Epsilon form of Martin's rough-count estimate.  The exceptional set has
`o(x)` elements under the moving-cutoff hypotheses. -/
lemma roughNumbersIn_card_isLittleO {y : ℕ → ℕ}
    (hy_le : ∀ᶠ x in atTop, y x ≤ x)
    (hy_top : Tendsto y atTop atTop)
    (hlog : Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (y x : ℝ))) atTop (𝓝 0)) :
    (fun x : ℕ ↦ ((roughNumbersIn 1 x (y x)).card : ℝ))
      =o[atTop] (fun x : ℕ ↦ (x : ℝ)) := by
  have htail := primePowerReciprocalTail_tendsto_zero hy_le hy_top hlog
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have heps : ∀ᶠ x in atTop, primePowerReciprocalTail x (y x) ≤ ε :=
    (htail.eventually (Iio_mem_nhds hε)).mono fun _ h ↦ h.le
  filter_upwards [heps] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    ((roughNumbersIn 1 x (y x)).card : ℝ) ≤
        (x : ℝ) * primePowerReciprocalTail x (y x) :=
      roughNumbersIn_card_le_mul_tail 1 x (y x)
    _ ≤ (x : ℝ) * ε := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg x)
    _ = ε * (x : ℝ) := by ring

lemma roughNumbersIn_logPowerCutoff_card_isLittleO (A : ℕ) :
    (fun x : ℕ ↦
      ((roughNumbersIn 1 x (logPowerCutoff A x)).card : ℝ))
      =o[atTop] (fun x : ℕ ↦ (x : ℝ)) := by
  exact roughNumbersIn_card_isLittleO
    (logPowerCutoff_eventually_le A)
    (logPowerCutoff_tendsto_atTop A)
    (logPowerCutoff_loglog_sub_tendsto_zero A)

/-- Reciprocal mass tends to zero in any family of terminal intervals whose
left endpoint remains a fixed positive proportion of the right endpoint. -/
lemma roughNumbersIn_reciprocalMass_tendsto_zero
    {L y : ℕ → ℕ} {C : ℝ}
    (hL : ∀ᶠ x : ℕ in atTop, 1 ≤ L x)
    (hratio : ∀ᶠ x : ℕ in atTop, (x : ℝ) / L x ≤ C)
    (hy_le : ∀ᶠ x : ℕ in atTop, y x ≤ x)
    (hy_top : Tendsto y atTop atTop)
    (hlog : Tendsto
      (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
        Real.log (Real.log (y x : ℝ))) atTop (𝓝 0)) :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass (roughNumbersIn (L x) x (y x)))
      atTop (𝓝 0) := by
  have htail := primePowerReciprocalTail_tendsto_zero hy_le hy_top hlog
  have hupper : Tendsto
      (fun x : ℕ ↦ C * primePowerReciprocalTail x (y x)) atTop (𝓝 0) := by
    simpa using htail.const_mul C
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x ↦ reciprocalMass_nonneg _
  · filter_upwards [hL, hratio] with x hLx hrat
    calc
      reciprocalMass (roughNumbersIn (L x) x (y x)) ≤
          ((x : ℝ) / L x) * primePowerReciprocalTail x (y x) :=
        roughNumbersIn_reciprocalMass_le (L x) x (y x) hLx
      _ ≤ C * primePowerReciprocalTail x (y x) :=
        mul_le_mul_of_nonneg_right hrat (primePowerReciprocalTail_nonneg _ _)
  · exact hupper

/-- Concrete reciprocal-mass form for Martin's interval
`[ceil(alpha*x),x]` and logarithmic prime-power cutoff. -/
lemma roughNumbersIn_logPowerCutoff_reciprocalMass_tendsto_zero
    (A : ℕ) {α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass
        (roughNumbersIn (proportionalLeftEndpoint α x) x
          (logPowerCutoff A x)))
      atTop (𝓝 0) := by
  exact roughNumbersIn_reciprocalMass_tendsto_zero
    (proportionalLeftEndpoint_eventually_one_le hα)
    (proportionalLeftEndpoint_eventually_ratio_le_inv hα)
    (logPowerCutoff_eventually_le A)
    (logPowerCutoff_tendsto_atTop A)
    (logPowerCutoff_loglog_sub_tendsto_zero A)

/-! ## A quantitative logarithmic-cutoff estimate -/

/-! ## Square tails for the exact-correction stage -/

/-- The elementary telescoping majorant `1/n^2 <= 1/(n-1)-1/n`. -/
lemma inv_sq_le_inv_pred_sub_inv {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) ^ 2)⁻¹ ≤ ((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpredR : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnsub : (n : ℝ) - 1 ≠ 0 := by nlinarith
  have heq : ((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ =
      ((n : ℝ) * (n - 1 : ℕ))⁻¹ := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    field_simp [hnR.ne', hpredR.ne', hnsub]
    ring
  rw [heq]
  refine (inv_le_inv₀ (sq_pos_of_pos hnR) (mul_pos hnR hpredR)).2 ?_
  nlinarith [show ((n - 1 : ℕ) : ℝ) ≤ n by exact_mod_cast (by omega : n - 1 ≤ n)]

/-- The finite integer square tail above `L` is at most `1/L`. -/
lemma sum_Icc_inv_sq_le_inv (L X : ℕ) (hL : 1 ≤ L) :
    (∑ n ∈ Icc (L + 1) X, ((n : ℝ) ^ 2)⁻¹) ≤ (L : ℝ)⁻¹ := by
  by_cases hLX : L < X
  · have hrewrite :
        (∑ n ∈ Icc (L + 1) X, ((n : ℝ) ^ 2)⁻¹) =
          ∑ i ∈ range (X - L), ((((L + i + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      have hsets : Icc (L + 1) X = Ico (L + 1) (X + 1) := by
        ext n
        simp
      rw [hsets, Finset.sum_Ico_eq_sum_range]
      have hlen : X + 1 - (L + 1) = X - L := by omega
      rw [hlen]
      apply Finset.sum_congr rfl
      intro i hi
      congr 3
      omega
    rw [hrewrite]
    calc
      (∑ i ∈ range (X - L), ((((L + i + 1 : ℕ) : ℝ) ^ 2)⁻¹)) ≤
          ∑ i ∈ range (X - L),
            (((L + i : ℕ) : ℝ)⁻¹ - ((L + i + 1 : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [Nat.add_assoc] using
          (inv_sq_le_inv_pred_sub_inv (n := L + i + 1) (by omega))
      _ = (L : ℝ)⁻¹ - (X : ℝ)⁻¹ := by
        change (range (X - L)).sum (fun i ↦
          (fun j : ℕ ↦ ((L + j : ℕ) : ℝ)⁻¹) i -
            (fun j : ℕ ↦ ((L + j : ℕ) : ℝ)⁻¹) (i + 1)) = _
        rw [Finset.sum_range_sub']
        simp [Nat.add_sub_of_le hLX.le]
      _ ≤ (L : ℝ)⁻¹ := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg X))
  · have hempty : Icc (L + 1) X = ∅ := by
      rw [Finset.Icc_eq_empty]
      omega
    simp [hempty, inv_nonneg.mpr (show (0 : ℝ) ≤ L by positivity)]

/-- Square reciprocal mass of prime powers in `(L,X]`. -/
def primePowerSquareTail (X L : ℕ) : ℝ :=
  ∑ q ∈ largePrimePowers X L, ((q : ℝ) ^ 2)⁻¹

/-- A logarithmically dilated intermediate cutoff. -/
def logDilate (L : ℕ) : ℕ :=
  L * ⌈Real.log (L : ℝ)⌉₊

/-- The small-prime/large-prime transition used by Martin's exact correction. -/
def naturalLogCutoff (y : ℕ) : ℕ :=
  ⌊Real.log (y : ℝ)⌋₊

lemma primePowerSquareTail_nonneg (X L : ℕ) :
    0 ≤ primePowerSquareTail X L := by
  exact Finset.sum_nonneg fun _ _ ↦ inv_nonneg.mpr (sq_nonneg _)

/-- Split a square tail at an intermediate point `U`.  Below `U` one gains a
factor `1/L` against the Mertens tail; above `U` the full integer square tail
costs only `1/U`. -/
lemma primePowerSquareTail_le_split (X L U : ℕ) (hL : 1 ≤ L) (hU : 1 ≤ U) :
    primePowerSquareTail X L ≤
      (L : ℝ)⁻¹ * primePowerReciprocalTail U L + (U : ℝ)⁻¹ := by
  let S := largePrimePowers X L
  have hsplit :
      primePowerSquareTail X L =
        ∑ q ∈ S.filter (fun q ↦ q ≤ U), ((q : ℝ) ^ 2)⁻¹ +
          ∑ q ∈ S.filter (fun q ↦ U < q), ((q : ℝ) ^ 2)⁻¹ := by
    change (∑ q ∈ S, ((q : ℝ) ^ 2)⁻¹) = _
    rw [← Finset.sum_filter_add_sum_filter_not S (fun q ↦ q ≤ U)]
    simp only [not_le]
  rw [hsplit]
  apply add_le_add
  · calc
      (∑ q ∈ S.filter (fun q ↦ q ≤ U), ((q : ℝ) ^ 2)⁻¹) ≤
          ∑ q ∈ S.filter (fun q ↦ q ≤ U),
            (L : ℝ)⁻¹ * (q : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro q hq
        have hLq : L ≤ q := by
          rcases Finset.mem_filter.mp hq with ⟨hqS, -⟩
          exact (mem_largePrimePowers.mp hqS).1.le
        have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
        have hqpos : (0 : ℝ) < q := by exact_mod_cast hL.trans hLq
        rw [show ((q : ℝ) ^ 2)⁻¹ = (q : ℝ)⁻¹ * (q : ℝ)⁻¹ by
          rw [sq, mul_inv]]
        exact mul_le_mul_of_nonneg_right
          ((inv_le_inv₀ hqpos hLpos).2 (by exact_mod_cast hLq))
          (inv_nonneg.mpr hqpos.le)
      _ ≤ ∑ q ∈ largePrimePowers U L,
          (L : ℝ)⁻¹ * (q : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqS, hqU⟩
          rw [mem_largePrimePowers] at hqS ⊢
          exact ⟨hqS.1, hqU, hqS.2.2⟩
        · intro q hq hqnot
          positivity
      _ = (L : ℝ)⁻¹ * primePowerReciprocalTail U L := by
        simp [primePowerReciprocalTail, Finset.mul_sum]
  · calc
      (∑ q ∈ S.filter (fun q ↦ U < q), ((q : ℝ) ^ 2)⁻¹) ≤
          ∑ q ∈ Icc (U + 1) X, ((q : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          rcases Finset.mem_filter.mp hq with ⟨hqS, hUq⟩
          rw [Finset.mem_Icc]
          exact ⟨hUq, (mem_largePrimePowers.mp hqS).2.1⟩
        · intro q hq hqnot
          positivity
      _ ≤ (U : ℝ)⁻¹ := by
        exact sum_Icc_inv_sq_le_inv U X hU

/-- Moving-endpoint form of the prime-power Mertens tail. -/
lemma primePowerReciprocalTail_between_tendsto_zero {L U : ℕ → ℕ}
    (hLU : ∀ᶠ n : ℕ in atTop, L n ≤ U n)
    (hLtop : Tendsto L atTop atTop)
    (hlog : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (U n : ℝ)) -
        Real.log (Real.log (L n : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun n ↦ primePowerReciprocalTail (U n) (L n)) atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := exists_primePowerReciprocalUpTo_error_tendsto_zero
  have hUtop : Tendsto U atTop atTop := by
    exact tendsto_atTop_mono' atTop hLU hLtop
  have hbL := hb.comp hLtop
  have hbU := hb.comp hUtop
  have hsum := hlog.add (hbU.sub hbL)
  have hsum0 : Tendsto
      (fun n : ℕ ↦
        Real.log (Real.log (U n : ℝ)) - Real.log (Real.log (L n : ℝ)) +
          ((primePowerReciprocalUpTo (U n) -
              (Real.log (Real.log (U n : ℝ)) + b)) -
            (primePowerReciprocalUpTo (L n) -
              (Real.log (Real.log (L n : ℝ)) + b)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hsum
  apply hsum0.congr'
  filter_upwards [hLU] with n hle
  rw [primePowerReciprocalTail_eq_sub hle]
  ring

lemma logDilate_eventually_one_le :
    ∀ᶠ L : ℕ in atTop, 1 ≤ logDilate L := by
  filter_upwards
    [eventually_ge_atTop 1,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
      with L hL hlog
  exact Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (Nat.one_le_iff_ne_zero.mp hL)
      (Nat.one_le_iff_ne_zero.mp (Nat.one_le_ceil_iff.mpr hlog)))

lemma eventually_le_logDilate :
    ∀ᶠ L : ℕ in atTop, L ≤ logDilate L := by
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
      with L hlog
  exact Nat.le_mul_of_pos_right L (Nat.ceil_pos.mpr hlog)

lemma logDilate_tendsto_atTop : Tendsto logDilate atTop atTop := by
  exact tendsto_atTop_mono' atTop eventually_le_logDilate tendsto_id

lemma ceil_log_ratio_tendsto_one :
    Tendsto
      (fun L : ℕ ↦ (⌈Real.log (L : ℝ)⌉₊ : ℝ) / Real.log (L : ℝ))
      atTop (𝓝 1) := by
  exact tendsto_nat_ceil_div_atTop.comp tendsto_log_coe_at_top

lemma log_ceil_log_div_log_tendsto_zero :
    Tendsto
      (fun L : ℕ ↦ Real.log (⌈Real.log (L : ℝ)⌉₊ : ℝ) /
        Real.log (L : ℝ)) atTop (𝓝 0) := by
  let ratio : ℕ → ℝ := fun L ↦
    (⌈Real.log (L : ℝ)⌉₊ : ℝ) / Real.log (L : ℝ)
  have hratio : Tendsto ratio atTop (𝓝 1) := by
    simpa [ratio] using ceil_log_ratio_tendsto_one
  have hlogratio : Tendsto (fun L ↦ Real.log (ratio L)) atTop (𝓝 0) := by
    have hcont : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact hcont.comp hratio
  have hlogratioDiv : Tendsto
      (fun L ↦ Real.log (ratio L) / Real.log (L : ℝ)) atTop (𝓝 0) :=
    hlogratio.div_atTop tendsto_log_coe_at_top
  have hsum := hlogratioDiv.add loglog_div_log_tendsto_zero
  have hsum0 : Tendsto
      (fun L : ℕ ↦ Real.log (ratio L) / Real.log (L : ℝ) +
        Real.log (Real.log (L : ℝ)) / Real.log (L : ℝ))
      atTop (𝓝 0) := by simpa using hsum
  apply hsum0.congr'
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      hratio.eventually (Ioi_mem_nhds zero_lt_one)] with L hlog hrat
  have hceilpos : (0 : ℝ) < ⌈Real.log (L : ℝ)⌉₊ := by
    exact_mod_cast Nat.ceil_pos.mpr hlog
  have heq : (⌈Real.log (L : ℝ)⌉₊ : ℝ) = ratio L * Real.log (L : ℝ) := by
    dsimp [ratio]
    exact (div_mul_cancel₀ _ hlog.ne').symm
  rw [heq, Real.log_mul hrat.ne' hlog.ne']
  ring

lemma log_logDilate_div_log_tendsto_one :
    Tendsto
      (fun L : ℕ ↦ Real.log (logDilate L : ℝ) / Real.log (L : ℝ))
      atTop (𝓝 1) := by
  have hmain : Tendsto
      (fun L : ℕ ↦ (1 : ℝ) +
        Real.log (⌈Real.log (L : ℝ)⌉₊ : ℝ) / Real.log (L : ℝ))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add log_ceil_log_div_log_tendsto_zero)
  apply hmain.congr'
  filter_upwards
    [eventually_ge_atTop 1,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
      with L hL hlog
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hceil : 0 < ⌈Real.log (L : ℝ)⌉₊ := Nat.ceil_pos.mpr hlog
  rw [logDilate, Nat.cast_mul,
    Real.log_mul hLR.ne' (by exact_mod_cast hceil.ne')]
  field_simp

lemma logDilate_loglog_sub_tendsto_zero :
    Tendsto
      (fun L : ℕ ↦ Real.log (Real.log (logDilate L : ℝ)) -
        Real.log (Real.log (L : ℝ))) atTop (𝓝 0) := by
  have hratio := log_logDilate_div_log_tendsto_one
  have hlogratio : Tendsto
      (fun L : ℕ ↦ Real.log
        (Real.log (logDilate L : ℝ) / Real.log (L : ℝ)))
      atTop (𝓝 0) := by
    have hcont : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact hcont.comp hratio
  apply hlogratio.congr'
  have hlogDilateTop : Tendsto (fun L ↦ Real.log (logDilate L : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp logDilate_tendsto_atTop)
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ)),
      hlogDilateTop.eventually (eventually_gt_atTop (0 : ℝ))] with L hL hU
  rw [Real.log_div hU.ne' hL.ne']

lemma logDilate_ratio_tendsto_zero :
    Tendsto (fun L : ℕ ↦ (L : ℝ) / logDilate L) atTop (𝓝 0) := by
  have hceilTop : Tendsto (fun L : ℕ ↦ (⌈Real.log (L : ℝ)⌉₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_ceil_atTop.comp tendsto_log_coe_at_top)
  have hinv := tendsto_inv_atTop_zero.comp hceilTop
  apply hinv.congr'
  filter_upwards
    [eventually_ge_atTop 1,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
      with L hL hlog
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  have hceil : (⌈Real.log (L : ℝ)⌉₊ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ceil_pos.mpr hlog).ne'
  simp only [logDilate, Nat.cast_mul]
  dsimp [Function.comp_def]
  field_simp [hLR, hceil]

lemma naturalLogCutoff_tendsto_atTop :
    Tendsto naturalLogCutoff atTop atTop := by
  exact tendsto_nat_floor_atTop.comp tendsto_log_coe_at_top

lemma primePowerSquareTail_scaled_tendsto_zero
    {X L U : ℕ → ℕ}
    (hLone : ∀ᶠ n : ℕ in atTop, 1 ≤ L n)
    (hUone : ∀ᶠ n : ℕ in atTop, 1 ≤ U n)
    (hLU : ∀ᶠ n : ℕ in atTop, L n ≤ U n)
    (hLtop : Tendsto L atTop atTop)
    (hlog : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (U n : ℝ)) -
        Real.log (Real.log (L n : ℝ))) atTop (𝓝 0))
    (hratio : Tendsto (fun n : ℕ ↦ (L n : ℝ) / U n) atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ ↦ (L n : ℝ) * primePowerSquareTail (X n) (L n))
      atTop (𝓝 0) := by
  have hpp := primePowerReciprocalTail_between_tendsto_zero hLU hLtop hlog
  have hupper : Tendsto
      (fun n : ℕ ↦ primePowerReciprocalTail (U n) (L n) +
        (L n : ℝ) / U n) atTop (𝓝 0) := by
    simpa using hpp.add hratio
  apply squeeze_zero'
  · filter_upwards with n
    exact mul_nonneg (Nat.cast_nonneg _) (primePowerSquareTail_nonneg _ _)
  · filter_upwards [hLone, hUone] with n hLn hUn
    have hLpos : (0 : ℝ) < L n := by exact_mod_cast hLn
    calc
      (L n : ℝ) * primePowerSquareTail (X n) (L n) ≤
          (L n : ℝ) *
            ((L n : ℝ)⁻¹ * primePowerReciprocalTail (U n) (L n) +
              (U n : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (primePowerSquareTail_le_split (X n) (L n) (U n) hLn hUn)
          (Nat.cast_nonneg _)
      _ = primePowerReciprocalTail (U n) (L n) + (L n : ℝ) / U n := by
        rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hLpos.ne', one_mul]
        rfl
  · exact hupper

lemma naturalLogCutoff_ratio_tendsto_one :
    Tendsto
      (fun y : ℕ ↦ (naturalLogCutoff y : ℝ) / Real.log (y : ℝ))
      atTop (𝓝 1) := by
  exact tendsto_nat_floor_div_atTop.comp tendsto_log_coe_at_top

/-- Proposition 7 square-cost estimate in limit form.  Multiplying the finite
prime-power square tail above `floor(log y)` by `log y` still tends to zero. -/
theorem ten_mul_primePowerSquareTail_mul_log_tendsto_zero :
    Tendsto
      (fun y : ℕ ↦
        10 * primePowerSquareTail y (naturalLogCutoff y) * Real.log (y : ℝ))
      atTop (𝓝 0) := by
  let L := naturalLogCutoff
  let U : ℕ → ℕ := fun y ↦ logDilate (L y)
  have hLtop : Tendsto L atTop atTop := naturalLogCutoff_tendsto_atTop
  have hscaled : Tendsto
      (fun y : ℕ ↦ (L y : ℝ) * primePowerSquareTail y (L y))
      atTop (𝓝 0) := by
    apply primePowerSquareTail_scaled_tendsto_zero
    · exact hLtop.eventually (eventually_ge_atTop 1)
    · exact logDilate_eventually_one_le.filter_mono hLtop
    · exact eventually_le_logDilate.filter_mono hLtop
    · exact hLtop
    · exact logDilate_loglog_sub_tendsto_zero.comp hLtop
    · exact logDilate_ratio_tendsto_zero.comp hLtop
  have hreverse : Tendsto
      (fun y : ℕ ↦ Real.log (y : ℝ) / (L y : ℝ)) atTop (𝓝 1) := by
    have hinv := naturalLogCutoff_ratio_tendsto_one.inv₀ one_ne_zero
    have hinv1 : Tendsto
        (fun y : ℕ ↦ ((naturalLogCutoff y : ℝ) / Real.log (y : ℝ))⁻¹)
        atTop (𝓝 1) := by simpa using hinv
    apply hinv1.congr'
    filter_upwards
      [hLtop.eventually (eventually_ge_atTop 1),
        tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
        with y hLy hlog
    dsimp [L]
    field_simp
  have hprod := hreverse.mul hscaled
  have hprod0 : Tendsto
      (fun y : ℕ ↦ Real.log (y : ℝ) *
        primePowerSquareTail y (L y)) atTop (𝓝 0) := by
    have hprod' : Tendsto
        (fun y : ℕ ↦ Real.log (y : ℝ) / (L y : ℝ) *
          ((L y : ℝ) * primePowerSquareTail y (L y)))
        atTop (𝓝 0) := by simpa using hprod
    apply hprod'.congr'
    filter_upwards
      [hLtop.eventually (eventually_ge_atTop 1)] with y hLy
    have hLne : (L y : ℝ) ≠ 0 := by exact_mod_cast (by omega : L y ≠ 0)
    field_simp
  simpa [L, mul_assoc, mul_comm, mul_left_comm] using hprod0.const_mul 10

/-- Epsilon form consumed by the exact-correction recursion. -/
theorem eventually_ten_mul_primePowerSquareTail_lt_div_log
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℕ in atTop,
      10 * primePowerSquareTail y (naturalLogCutoff y) <
        c / Real.log (y : ℝ) := by
  have hsmall := ten_mul_primePowerSquareTail_mul_log_tendsto_zero.eventually
    (Metric.ball_mem_nhds 0 hc)
  filter_upwards
    [hsmall,
      tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
      with y hy hlog
  rw [_root_.dist_zero_right, Real.norm_eq_abs] at hy
  rw [lt_div_iff₀ hlog]
  exact (le_abs_self _).trans_lt hy

/-- The weighted square tail in the literal finite-sum form used by the recursion. -/
lemma ten_mul_primePowerSquareTail_eq_sum (X L : ℕ) :
    10 * primePowerSquareTail X L =
      ∑ q ∈ largePrimePowers X L, 10 / (q : ℝ) ^ 2 := by
  simp [primePowerSquareTail, Finset.mul_sum, div_eq_mul_inv]

/-- Direct finite-sum form of the Proposition 7 square-cost estimate. -/
theorem eventually_sum_ten_div_primePower_sq_lt_div_log
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℕ in atTop,
      (∑ q ∈ largePrimePowers y (naturalLogCutoff y), 10 / (q : ℝ) ^ 2) <
        c / Real.log (y : ℝ) := by
  filter_upwards [eventually_ten_mul_primePowerSquareTail_lt_div_log hc] with y hy
  rw [← ten_mul_primePowerSquareTail_eq_sum]
  exact hy

end

end RoughCounts

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Proposition6Asymptotic.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős 285: analytic estimates for Martin's Proposition 6

This file proves the analytic and counting assertions for the explicit initial
block used in `Proposition6.lean`.  The main cutoff is `x / log(x)^30`.  The
integers discarded from a terminal interval are covered by large exact
prime-power divisors, so the prime-power Mertens estimate in `RoughCounts`
shows that both their relative cardinality and their reciprocal mass vanish.

The final section gives a concrete summable deletion budget and compares it
with the elementary five-prime reservoir from `SmoothReservoir.lean`.
-/

open Filter Finset Real Asymptotics
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open PrimePowers RoughCounts

/-- The natural-valued version of the main cutoff. -/
def mainCutoffNat (x : ℕ) : ℕ :=
  logPowerCutoff 30 x

lemma mainCutoffNat_eq (x : ℕ) :
    mainCutoffNat x = ⌊proposition6MainCutoff x⌋₊ := by
  rfl

/-- The lower endpoint ratio for the target `r = 1`. -/
def oneLowerRatio : ℝ := Real.exp (-1)

lemma oneLowerRatio_pos : 0 < oneLowerRatio := by
  exact Real.exp_pos _

/-! ## Smoothness and exact prime-power parts -/

/-- Smoothness can be tested on the largest exact prime-power part. -/
lemma isSmooth_iff_largestPrimePowerPart_le_floor {z : ℝ} {n : ℕ}
    (hz : 0 ≤ z) (hn : n ≠ 0) :
    UnitFractions.is_smooth z n ↔ largestPrimePowerPart n ≤ ⌊z⌋₊ := by
  constructor
  · intro hs
    by_cases hn2 : 2 ≤ n
    · have hmem := largestPrimePowerPart_mem hn2
      have hspec := (mem_primePowerParts hn).mp hmem
      exact Nat.le_floor (hs _ hspec.1 hspec.2.1)
    · have hempty : primePowerParts n = ∅ :=
        primePowerParts_empty_iff.mpr (Nat.lt_of_not_ge hn2)
      simp [largestPrimePowerPart, hempty]
  · intro hmax q hqpp hqdiv
    have hqexact : ∃ r : ℕ, r ∈ primePowerParts n ∧ q ∣ r := by
      rcases (isPrimePow_nat_iff q).1 hqpp with ⟨p, k, hp, hk, rfl⟩
      let r := p ^ n.factorization p
      have hk' : k ≤ n.factorization p :=
        (hp.pow_dvd_iff_le_factorization hn).1 hqdiv
      have hfac : n.factorization p ≠ 0 := Nat.ne_zero_of_lt (lt_of_lt_of_le hk hk')
      have hrd : r ∣ n := by
        dsimp [r]
        simpa using Nat.ordProj_dvd n p
      have hcop : Nat.Coprime r (n / r) := by
        dsimp [r]
        exact ((UnitFractions.factorization_eq_iff (n := n) hp hfac).2 rfl).2
      refine ⟨r, (mem_primePowerParts hn).2
        ⟨hp.isPrimePow.pow hfac, hrd, hcop⟩, ?_⟩
      dsimp [r]
      exact pow_dvd_pow p hk'
    obtain ⟨r, hrmem, hqr⟩ := hqexact
    have hrpos : 0 < r := ((mem_primePowerParts hn).1 hrmem).1.pos
    have hqle : q ≤ ⌊z⌋₊ :=
      (Nat.le_of_dvd hrpos hqr).trans
        ((le_largestPrimePowerPart hrmem).trans hmax)
    exact (Nat.cast_le.2 hqle).trans (Nat.floor_le hz)

/-- The discarded part of the terminal interval. -/
def initialRoughPart (x : ℕ) : Finset ℕ :=
  roughNumbersIn (⌊oneLowerRatio * (x : ℝ)⌋₊ + 1) x (mainCutoffNat x)

/-! ## Cardinality of the initial block -/

lemma proposition6MainCutoff_nonneg (x : ℕ) :
    0 ≤ proposition6MainCutoff x := by
  unfold proposition6MainCutoff
  positivity

lemma mainCutoffNat_spec :
    (∀ᶠ x : ℕ in atTop, mainCutoffNat x ≤ x) ∧
      Tendsto mainCutoffNat atTop atTop ∧
      Tendsto
        (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
          Real.log (Real.log (mainCutoffNat x : ℝ)))
        atTop (𝓝 0) := by
  change
    (∀ᶠ x : ℕ in atTop, logPowerCutoff 30 x ≤ x) ∧
      Tendsto (logPowerCutoff 30) atTop atTop ∧
      Tendsto
        (fun x : ℕ ↦ Real.log (Real.log (x : ℝ)) -
          Real.log (Real.log (logPowerCutoff 30 x : ℝ)))
        atTop (𝓝 0)
  exact logPowerCutoff_spec 30

/-! ## Reciprocal mass of the initial block -/

lemma reciprocalMass_Ioc_eq_harmonic_sub {a b : ℕ} (hab : a ≤ b) :
    reciprocalMass (Ioc a b) =
      ((harmonic b : ℚ) : ℝ) - ((harmonic a : ℚ) : ℝ) := by
  have hsub : Icc 1 a ⊆ Icc 1 b := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hab⟩
  have hsdiff : Icc 1 b \ Icc 1 a = Ioc a b := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  change (∑ n ∈ Ioc a b, (n : ℝ)⁻¹) = _
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [← hsdiff, ← Finset.sum_sdiff hsub]
  ring

lemma floorOneEndpoint_tendsto_atTop :
    Tendsto (fun x : ℕ ↦ ⌊oneLowerRatio * (x : ℝ)⌋₊) atTop atTop := by
  exact tendsto_nat_floor_mul_atTop oneLowerRatio oneLowerRatio_pos

lemma initialRoughPart_subset_proportionalRough (x : ℕ) :
    initialRoughPart x ⊆
      roughNumbersIn (proportionalLeftEndpoint oneLowerRatio x) x
        (logPowerCutoff 30 x) := by
  intro n hn
  rw [initialRoughPart, mem_roughNumbersIn] at hn
  rw [mem_roughNumbersIn]
  refine ⟨?_, hn.2.1, by simpa [mainCutoffNat] using hn.2.2⟩
  have hceil : proportionalLeftEndpoint oneLowerRatio x ≤
      ⌊oneLowerRatio * (x : ℝ)⌋₊ + 1 := by
    simpa [proportionalLeftEndpoint] using
      Nat.ceil_le_floor_add_one (oneLowerRatio * (x : ℝ))
  exact hceil.trans hn.1

lemma reciprocalMass_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    reciprocalMass A ≤ reciprocalMass B := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB fun n _ _ ↦
    inv_nonneg.mpr (Nat.cast_nonneg n)

lemma initialRoughPart_reciprocalMass_tendsto_zero :
    Tendsto (fun x : ℕ ↦ reciprocalMass (initialRoughPart x))
      atTop (𝓝 0) := by
  have hupper :=
    roughNumbersIn_logPowerCutoff_reciprocalMass_tendsto_zero
      30 oneLowerRatio_pos
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x ↦ reciprocalMass_nonneg _
  · exact Filter.Eventually.of_forall fun x ↦
      reciprocalMass_mono (initialRoughPart_subset_proportionalRough x)
  · exact hupper

lemma reciprocalMass_sdiff {A B : Finset ℕ} (hBA : B ⊆ A) :
    reciprocalMass (A \ B) = reciprocalMass A - reciprocalMass B := by
  unfold reciprocalMass
  rw [← Finset.sum_sdiff hBA]
  ring

lemma ratCast_recSum_eq_reciprocalMass (A : Finset ℕ) :
    ((UnitFractions.rec_sum A : ℚ) : ℝ) = reciprocalMass A := by
  simp [UnitFractions.rec_sum, reciprocalMass, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]

/-! ## A fixed nearby endpoint `alpha` -/

/-- The terminal interval with arbitrary fixed lower ratio. -/
def fullInitialIntervalAt (alpha : ℝ) (x : ℕ) : Finset ℕ :=
  Ioc ⌊alpha * (x : ℝ)⌋₊ x

/-- The source-faithful smooth block with arbitrary fixed lower ratio. -/
def initialBlockAt (alpha : ℝ) (x : ℕ) : Finset ℕ :=
  initialSmoothBlock alpha x (proposition6MainCutoff x)

def initialRoughPartAt (alpha : ℝ) (x : ℕ) : Finset ℕ :=
  roughNumbersIn (⌊alpha * (x : ℝ)⌋₊ + 1) x (mainCutoffNat x)

lemma initialBlockAt_eq_sdiff (alpha : ℝ) (x : ℕ) :
    initialBlockAt alpha x =
      fullInitialIntervalAt alpha x \ initialRoughPartAt alpha x := by
  ext n
  simp only [initialBlockAt, initialSmoothBlock, fullInitialIntervalAt,
    initialRoughPartAt, Finset.mem_filter, Finset.mem_Ioc,
    Finset.mem_sdiff, mem_roughNumbersIn]
  have hcut := proposition6MainCutoff_nonneg x
  by_cases hn : n = 0
  · subst n
    simp
  · rw [isSmooth_iff_largestPrimePowerPart_le_floor hcut hn]
    rw [mainCutoffNat_eq]
    omega

lemma initialRoughPartAt_subset_full (alpha : ℝ) (x : ℕ) :
    initialRoughPartAt alpha x ⊆ fullInitialIntervalAt alpha x := by
  intro n hn
  rw [initialRoughPartAt, mem_roughNumbersIn] at hn
  simp only [fullInitialIntervalAt, Finset.mem_Ioc]
  omega

lemma initialRoughPartAt_subset_global (alpha : ℝ) (x : ℕ) :
    initialRoughPartAt alpha x ⊆ roughNumbersIn 1 x (logPowerCutoff 30 x) := by
  intro n hn
  rw [initialRoughPartAt, mem_roughNumbersIn] at hn
  rw [mem_roughNumbersIn]
  exact ⟨by omega, hn.2.1, by simpa [mainCutoffNat] using hn.2.2⟩

/-! ## The accumulated Lemma 12 deletion budget -/

lemma sum_Icc_rpow_neg_two_thirds_le (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ q ∈ Icc 1 Q, (q : ℝ) ^ (-(2 : ℝ) / 3)) ≤
      3 * (Q : ℝ) ^ ((1 : ℝ) / 3) := by
  let f : ℝ → ℝ := fun t ↦ t ^ (-(2 : ℝ) / 3)
  have hanti : AntitoneOn f (Set.Icc 1 (1 + ((Q - 1 : ℕ) : ℝ))) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num :
      (-(2 : ℝ) / 3) ≤ 0)).mono
    intro t ht
    exact ht.1.trans_lt' zero_lt_one
  have hsum := hanti.sum_le_integral
  have htop : (1 : ℝ) + (Q - 1 : ℕ) = Q := by
    exact_mod_cast (show 1 + (Q - 1) = Q by omega)
  have htail : (∑ q ∈ Icc 2 Q, f q) ≤ ∫ t in (1 : ℝ)..Q, f t := by
    rw [← htop]
    calc
      (∑ q ∈ Icc 2 Q, f q) =
          ∑ i ∈ Ico 0 (Q - 1), f (i + 2 : ℕ) := by
        symm
        rw [Finset.sum_Ico_add' (fun q : ℕ ↦ f q) 0 (Q - 1) 2]
        apply Finset.sum_congr
        · ext q
          simp
          omega
        · intro q hq
          rfl
      _ =
          ∑ i ∈ Ico 0 (Q - 1), f (i + 2 : ℕ) := by
        rfl
      _ = ∑ i ∈ Ico 0 (Q - 1), f (1 + (i + 1 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        push_cast
        ring
      _ = ∑ i ∈ range (Q - 1), f (1 + (i + 1 : ℕ)) := by
        rw [Finset.range_eq_Ico]
      _ ≤ ∫ t in (1 : ℝ)..1 + (Q - 1 : ℕ), f t := hsum
  have hint : (∫ t in (1 : ℝ)..Q, f t) =
      3 * ((Q : ℝ) ^ ((1 : ℝ) / 3) - 1) := by
    dsimp [f]
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(2 : ℝ) / 3))]
    norm_num [Real.one_rpow]
    ring
  have hone : f 1 = 1 := by simp [f]
  have hdecomp : Icc 1 Q = insert 1 (Icc 2 Q) := by
    ext q
    simp
    omega
  rw [hdecomp, Finset.sum_insert (by simp)]
  have honeRaw : ((1 : ℕ) : ℝ) ^ (-(2 : ℝ) / 3) = 1 := by norm_num
  rw [honeRaw]
  calc
    1 + ∑ q ∈ Icc 2 Q, f q
        ≤ 1 + ∫ t in (1 : ℝ)..Q, f t := by
          simpa [add_comm] using add_le_add_left htail 1
    _ = 3 * (Q : ℝ) ^ ((1 : ℝ) / 3) - 2 := by rw [hint]; ring
    _ ≤ 3 * (Q : ℝ) ^ ((1 : ℝ) / 3) := by linarith

lemma deletion_rpow_identity {x L : ℝ} (hx : 0 < x) (hL : 0 < L) :
    x ^ ((2 : ℝ) / 3) * (x / L ^ 30) ^ ((1 : ℝ) / 3) * L ^ 3 =
      x / L ^ 7 := by
  rw [Real.div_rpow hx.le (pow_nonneg hL.le 30)]
  have hxpow : x ^ ((2 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) = x := by
    rw [← Real.rpow_add hx]
    norm_num
  have hLpow : (L ^ 30) ^ ((1 : ℝ) / 3) = L ^ 10 := by
    rw [← Real.rpow_natCast L 30, ← Real.rpow_mul hL.le]
    norm_num
  rw [hLpow]
  field_simp
  nlinarith

lemma div_rpow_two_thirds {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q) :
    (x / q) ^ ((2 : ℝ) / 3) =
      x ^ ((2 : ℝ) / 3) * q ^ (-(2 : ℝ) / 3) := by
  rw [Real.div_rpow hx hq.le]
  have he : (-(2 : ℝ) / 3) = -((2 : ℝ) / 3) := by ring
  rw [he, Real.rpow_neg hq.le]
  ring

/-- A convenient explicit `x/log(x)^7` budget. -/
def proposition6DeletionBudget (x : ℕ) : ℕ :=
  ⌈1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7⌉₊

/-! ## Capacity of the five-prime reservoir for the deletion budget -/

lemma proposition6ReservoirScale_tendsto_atTop (alpha : ℝ) (halpha : 0 < alpha) :
    Tendsto (fun x : ℕ ↦ proposition6ReservoirScale alpha x) atTop atTop := by
  have hbase : Tendsto (fun x : ℕ ↦ alpha * (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop halpha
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (5 : ℝ)⁻¹)).comp hbase

lemma reservoirScale_log_le_log (alpha : ℝ) (halpha0 : 0 < alpha)
    (halpha1 : alpha ≤ 1) {x : ℕ} (hx : 1 < x) :
    Real.log (proposition6ReservoirScale alpha x) ≤ Real.log (x : ℝ) := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (Nat.zero_lt_of_lt hx)
  have haxpos : 0 < alpha * (x : ℝ) := mul_pos halpha0 hxpos
  rw [proposition6ReservoirScale, Real.log_rpow haxpos,
    Real.log_mul halpha0.ne' hxpos.ne']
  have hloga : Real.log alpha ≤ 0 := Real.log_nonpos halpha0.le halpha1
  have hlogx : 0 ≤ Real.log (x : ℝ) := (Real.log_pos (by exact_mod_cast hx)).le
  norm_num
  linarith

/-- The elementary five-prime reservoir is more than large enough for twice
the complete Lemma 12 deletion budget. -/
theorem eventually_two_budget_le_smoothReservoir (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    ∀ᶠ x : ℕ in atTop,
      2 * proposition6DeletionBudget x ≤
        (smoothReservoir (proposition6ReservoirScale alpha x)).card := by
  let C : ℝ := 120 * 200 ^ 5
  have hC : 0 < C := by dsimp [C]; positivity
  have hyTop := proposition6ReservoirScale_tendsto_atTop alpha halpha0
  have hreservoir := hyTop.eventually eventually_smoothReservoir_card_lower
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    tendsto_log_coe_at_top
  have hscaled : Tendsto
      (fun x : ℕ ↦ alpha * (x : ℝ) / Real.log (x : ℝ) ^ 5)
      atTop atTop := by
    have ht :=
      (UnitFractions.tendsto_mul_add_div_pow_log_at_top alpha 0 5 halpha0).comp
        tendsto_natCast_atTop_atTop
    apply ht.congr'
    exact Filter.Eventually.of_forall fun x ↦ by simp
  filter_upwards [hreservoir, eventually_ge_atTop 3,
    hlogTop.eventually (eventually_ge_atTop (max 1 (4000 * C / alpha))),
    hscaled.eventually (eventually_ge_atTop (4 * C)),
    hyTop.eventually (eventually_gt_atTop 1)]
      with x hreservoir hx hlogLarge hscaledLarge hy1
  let y := proposition6ReservoirScale alpha x
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hypos : 0 < y := by
    exact Real.rpow_pos_of_pos (mul_pos halpha0 hxpos) _
  have hlogy : 0 < Real.log y := by
    exact Real.log_pos hy1
  have hlogyx : Real.log y ≤ Real.log (x : ℝ) :=
    reservoirScale_log_le_log alpha halpha0 halpha1 (by omega)
  have hy5 : y ^ 5 = alpha * (x : ℝ) :=
    proposition6ReservoirScale_pow_five halpha0.le
  have hreservoirEq : (y / (200 * Real.log y)) ^ 5 / 120 =
      alpha * (x : ℝ) / (C * Real.log y ^ 5) := by
    dsimp [C]
    rw [div_pow, hy5]
    ring
  have hdenlog : C * Real.log y ^ 5 ≤ C * Real.log (x : ℝ) ^ 5 := by
    gcongr
  have hlower : alpha * (x : ℝ) /
      (C * Real.log (x : ℝ) ^ 5) ≤
      ((smoothReservoir y).card : ℝ) := by
    calc
      alpha * (x : ℝ) / (C * Real.log (x : ℝ) ^ 5) ≤
          alpha * (x : ℝ) / (C * Real.log y ^ 5) := by
            exact div_le_div_of_nonneg_left
              (mul_nonneg halpha0.le hxpos.le)
              (mul_pos hC (pow_pos hlogy _)) hdenlog
      _ = (y / (200 * Real.log y)) ^ 5 / 120 := hreservoirEq.symm
      _ ≤ ((smoothReservoir y).card : ℝ) := hreservoir
  have hlogsq : 4000 * C ≤ alpha * Real.log (x : ℝ) ^ 2 := by
    have h1 : 1 ≤ Real.log (x : ℝ) := (le_max_left _ _).trans hlogLarge
    have hthreshold : 4000 * C / alpha ≤ Real.log (x : ℝ) :=
      (le_max_right _ _).trans hlogLarge
    have := mul_le_mul_of_nonneg_left hthreshold halpha0.le
    field_simp at this
    nlinarith
  have hmain : 2 * (1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7) ≤
      alpha * (x : ℝ) / (2 * C * Real.log (x : ℝ) ^ 5) := by
    have hcore : 2000 * (2 * C * Real.log (x : ℝ) ^ 5) ≤
        alpha * Real.log (x : ℝ) ^ 7 := by
      calc
        2000 * (2 * C * Real.log (x : ℝ) ^ 5) =
            (4000 * C) * Real.log (x : ℝ) ^ 5 := by ring
        _ ≤ (alpha * Real.log (x : ℝ) ^ 2) *
            Real.log (x : ℝ) ^ 5 := by gcongr
        _ = alpha * Real.log (x : ℝ) ^ 7 := by ring
    rw [show 2 * (1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7) =
      2000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 by ring]
    apply (div_le_div_iff₀ (pow_pos hlogx 7)
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hC) (pow_pos hlogx 5))).2
    have := mul_le_mul_of_nonneg_left hcore hxpos.le
    ring_nf at this ⊢
    exact this
  have htwo : (2 : ℝ) ≤
      alpha * (x : ℝ) / (2 * C * Real.log (x : ℝ) ^ 5) := by
    have hcross : 4 * C * Real.log (x : ℝ) ^ 5 ≤ alpha * (x : ℝ) := by
      exact (le_div_iff₀ (pow_pos hlogx 5)).1 hscaledLarge
    apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hC) (pow_pos hlogx 5))).2
    nlinarith
  have hbudgetCast : (proposition6DeletionBudget x : ℝ) <
      1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have htarget : (2 * proposition6DeletionBudget x : ℕ) ≤
      (smoothReservoir y).card := by
    have hcast : ((2 * proposition6DeletionBudget x : ℕ) : ℝ) ≤
        ((smoothReservoir y).card : ℝ) := by
      calc
      ((2 * proposition6DeletionBudget x : ℕ) : ℝ) ≤
          2 * (1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 + 1) := by
            push_cast
            exact (mul_lt_mul_of_pos_left hbudgetCast (by norm_num)).le
      _ ≤ alpha * (x : ℝ) / (C * Real.log (x : ℝ) ^ 5) := by
        calc
          2 * (1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 + 1) =
              2 * (1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7) + 2 := by ring
          _ ≤ alpha * (x : ℝ) / (2 * C * Real.log (x : ℝ) ^ 5) +
              alpha * (x : ℝ) / (2 * C * Real.log (x : ℝ) ^ 5) :=
                add_le_add hmain htwo
          _ = alpha * (x : ℝ) / (C * Real.log (x : ℝ) ^ 5) := by ring
      _ ≤ ((smoothReservoir y).card : ℝ) := hlower
    exact_mod_cast hcast
  exact htarget

/-! ## Residual margins -/

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/ExactCorrection.lean` -/

section
/-!
# Exact finite correction and cardinality padding

This file isolates the algebraic part of Martin's exact-correction argument for
Erdős Problem 285.  All reciprocal sums here are rational.  The analytic
construction converts its error into a rational number, so this loses no
information and makes divisibility arguments available.

The final quantitative bound on the largest denominator requires Martin's
prime-power elimination lemmas.  The results below provide the exact
telescoping identity, the odd-prime inverse-pair construction, and the
displayed-fraction cancellation identities used by those lemmas.
-/

namespace ExactCorrection

open Finset
open scoped BigOperators

noncomputable section

/-- The elementary two-term split used to increase the cardinality of an
Egyptian representation by one. -/
theorem unitFraction_split (n : ℕ) (hn : 0 < n) :
    (1 : ℚ) / n = 1 / (n + 1 : ℕ) + 1 / (n * (n + 1) : ℕ) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn10 : (n : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

/-- A finite version of the telescoping split.

For `m = 1` this is `unitFraction_split`.  In Martin's padding step it replaces
one denominator `n` by `m + 1` unit fractions while preserving the sum.
-/
theorem unitFraction_telescoping (n m : ℕ) (hn : 0 < n) :
    (1 : ℚ) / n = 1 / (n + m : ℕ) +
      ∑ j ∈ range m, (1 : ℚ) / ((n + j) * (n + j + 1) : ℕ) := by
  have hterm : ∀ j : ℕ,
      (1 : ℚ) / ((n + j) * (n + j + 1) : ℕ) =
        1 / (n + j : ℕ) - 1 / (n + j + 1 : ℕ) := by
    intro j
    have hj : (0 : ℚ) < n + j := by exact_mod_cast Nat.add_pos_left hn j
    have hj1 : (0 : ℚ) < n + j + 1 := by positivity
    push_cast
    field_simp
    ring
  simp_rw [hterm]
  have htel := sum_range_sub' (fun j : ℕ ↦ (1 : ℚ) / (n + j : ℕ)) m
  simpa [Nat.add_assoc] using congrArg (fun x : ℚ ↦ 1 / (n + m : ℕ) + x) htel.symm

/-! ## The inverse-pair core of the odd-prime case -/

/-- Source-faithful pigeonhole core of Martin's Lemma 14 for primes at least
five.  The numbers `s,t` are the small positive complements of the desired
integers near a prime power. -/
theorem exists_inverse_pair_complements (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (a : ZMod p) :
    ∃ s t : ℕ,
      1 ≤ s ∧ s ≤ (p + 3) / 2 ∧
      1 ≤ t ∧ t ≤ (p + 3) / 2 ∧
      s ≠ t ∧
      (-((s : ℕ) : ZMod p))⁻¹ + (-((t : ℕ) : ZMod p))⁻¹ = a := by
  let _ : Fact p.Prime := ⟨hp⟩
  let h : ℕ := (p + 3) / 2
  let D : Finset ℕ := Icc 1 h
  let f : ℕ → ZMod p := fun s ↦ (-((s : ℕ) : ZMod p))⁻¹
  let A : Finset (ZMod p) := D.image f
  let B : Finset (ZMod p) := A.image fun x ↦ a - x
  have hpne2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hpne2
  have heven : Even (p + 3) := by
    rcases hpodd with ⟨w, hw⟩
    refine ⟨w + 2, ?_⟩
    omega
  have htwoh : 2 * h = p + 3 := by
    exact Nat.two_mul_div_two_of_even heven
  have hltp : h < p := by
    dsimp [h]
    omega
  have hDcard : D.card = h := by
    simp [D]
  have hfinj : Set.InjOn f D := by
    intro s hs t ht hst
    have hsD := Finset.mem_Icc.mp hs
    have htD := Finset.mem_Icc.mp ht
    have hcast : (s : ZMod p) = (t : ZMod p) := by
      apply neg_injective
      exact inv_inj.mp hst
    have hmod : s ≡ t [MOD p] :=
      (ZMod.natCast_eq_natCast_iff s t p).mp hcast
    exact hmod.eq_of_lt_of_lt (hsD.2.trans_lt hltp) (htD.2.trans_lt hltp)
  have hAcard : A.card = h := by
    change (D.image f).card = h
    rw [Finset.card_image_iff.mpr hfinj, hDcard]
  have hBcard : B.card = h := by
    change (A.image (fun x ↦ a - x)).card = h
    rw [Finset.card_image_iff.mpr, hAcard]
    intro x _ y _ hxy
    exact sub_right_injective hxy
  have hunion : (A ∪ B).card ≤ p := by
    simpa [ZMod.card] using Finset.card_le_univ (A ∪ B)
  have hinter : 3 ≤ (A ∩ B).card := by
    have hcount := Finset.card_inter_add_card_union A B
    rw [hAcard, hBcard] at hcount
    omega
  have hexists : ∃ r ∈ A ∩ B, r ≠ a / 2 := by
    by_contra hnone
    push Not at hnone
    have hsub : A ∩ B ⊆ {a / 2} := by
      intro r hr
      simpa using hnone r hr
    have hsmall := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hsmall
    omega
  obtain ⟨r, hr, hrhalf⟩ := hexists
  obtain ⟨s, hsD, hsr⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hr).1
  obtain ⟨x, hxA, hxr⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hr).2
  obtain ⟨t, htD, htx⟩ := Finset.mem_image.mp hxA
  have hsum : f s + f t = a := by
    rw [hsr, htx]
    exact ((sub_eq_iff_eq_add).mp hxr).symm
  have htwo : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    intro hz
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hple : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    omega
  have hst : s ≠ t := by
    intro hst
    subst t
    have hfxr : f s = r := hsr
    have hfx : f s = x := htx
    apply hrhalf
    rw [← hfxr, ← hfx] at hxr
    rw [← hfxr, eq_div_iff htwo, mul_two]
    exact ((sub_eq_iff_eq_add).mp hxr).symm
  rcases Finset.mem_Icc.mp hsD with ⟨hs1, hsh⟩
  rcases Finset.mem_Icc.mp htD with ⟨ht1, hth⟩
  exact ⟨s, t, hs1, hsh, ht1, hth, hst, hsum⟩

/-- Martin's Lemma 14 for prime powers whose underlying prime is at least
five.  The inverse congruence is modulo `p`, exactly as used to remove one
power of `p` from the reduced denominator. -/
theorem martin_lemma14_of_five_le {p ν : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hν : 0 < ν) (a : ZMod p) :
    ∃ m₁ m₂ : ℕ,
      (p ^ ν - 3) / 2 ≤ m₁ ∧
      m₁ < m₂ ∧ m₂ < p ^ ν ∧
      ¬ p ∣ m₁ * m₂ ∧
      ((m₁ : ZMod p)⁻¹ + (m₂ : ZMod p)⁻¹) = a := by
  obtain ⟨s, t, hs1, hsh, ht1, hth, hst, hsum⟩ :=
    exists_inverse_pair_complements p hp hp5 a
  let q : ℕ := p ^ ν
  let h : ℕ := (p + 3) / 2
  have hp0 : 0 < p := hp.pos
  have hpq : p ≤ q := by
    dsimp [q]
    exact Nat.le_pow hν
  have hq5 : 5 ≤ q := hp5.trans hpq
  have htwoh : 2 * h = p + 3 := by
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have heven : Even (p + 3) := by
      rcases hpodd with ⟨w, hw⟩
      exact ⟨w + 2, by omega⟩
    exact Nat.two_mul_div_two_of_even heven
  have hhp : h < p := by
    dsimp [h]
    omega
  have hsq : s ≤ q := hsh.trans (hhp.le.trans hpq)
  have htq : t ≤ q := hth.trans (hhp.le.trans hpq)
  have hqh : h ≤ q := hhp.le.trans hpq
  have hlower : (q - 3) / 2 ≤ q - h := by
    omega
  have hqdiv : p ∣ q := by
    dsimp [q]
    exact dvd_pow_self p (Nat.ne_zero_of_lt hν)
  have hnotdvd_s : ¬ p ∣ q - s := by
    intro hdiff
    have hps : p ∣ s := by
      rw [Nat.dvd_add_iff_left hdiff]
      rw [show s + (q - s) = q by omega]
      exact hqdiv
    have hple : p ≤ s := Nat.le_of_dvd (by omega) hps
    omega
  have hnotdvd_t : ¬ p ∣ q - t := by
    intro hdiff
    have hpt : p ∣ t := by
      rw [Nat.dvd_add_iff_left hdiff]
      rw [show t + (q - t) = q by omega]
      exact hqdiv
    have hple : p ≤ t := Nat.le_of_dvd (by omega) hpt
    omega
  have hqcast : (q : ZMod p) = 0 := by
    apply (ZMod.natCast_eq_zero_iff q p).mpr
    exact hqdiv
  have hinv_s : (((q - s : ℕ) : ZMod p)⁻¹) = (-((s : ℕ) : ZMod p))⁻¹ := by
    rw [Nat.cast_sub hsq, hqcast, zero_sub]
  have hinv_t : (((q - t : ℕ) : ZMod p)⁻¹) = (-((t : ℕ) : ZMod p))⁻¹ := by
    rw [Nat.cast_sub htq, hqcast, zero_sub]
  rcases lt_or_gt_of_ne hst with hstlt | htslt
  · refine ⟨q - t, q - s, ?_, ?_, ?_, ?_, ?_⟩
    · exact hlower.trans (Nat.sub_le_sub_left hth q)
    · omega
    · omega
    · intro hdvd
      rcases (hp.dvd_mul.mp hdvd) with hdvd | hdvd
      · exact hnotdvd_t hdvd
      · exact hnotdvd_s hdvd
    · rw [hinv_t, hinv_s, add_comm]
      exact hsum
  · refine ⟨q - s, q - t, ?_, ?_, ?_, ?_, ?_⟩
    · exact hlower.trans (Nat.sub_le_sub_left hsh q)
    · omega
    · omega
    · intro hdvd
      rcases (hp.dvd_mul.mp hdvd) with hdvd | hdvd
      · exact hnotdvd_s hdvd
      · exact hnotdvd_t hdvd
    · rw [hinv_s, hinv_t]
      exact hsum

/-! ## Displayed-fraction cancellation -/

/-- If a common natural factor divides both the displayed numerator and
denominator of a rational, then the reduced denominator divides the displayed
denominator after that factor is cancelled.

This is the bridge from the modular numerator congruence in Martin's Lemmas
15 and 16 to strict descent of the reduced denominator's prime-power part. -/
theorem rat_den_dvd_div_of_eq_divInt {r : ℚ} {a : ℤ} {b p : ℕ}
    (hb : b ≠ 0) (hp : p ≠ 0) (hpb : p ∣ b)
    (hpa : (p : ℤ) ∣ a) (hr : r = Rat.divInt a b) :
    r.den ∣ b / p := by
  obtain ⟨b', rfl⟩ := hpb
  obtain ⟨a', ha'⟩ := hpa
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have hrepr : r = Rat.divInt a' b' := by
    rw [hr, ha']
    push_cast
    exact Rat.divInt_mul_left hpZ
  rw [hrepr]
  have hdenZ : (((Rat.divInt a' b').den : ℕ) : ℤ) ∣ (b' : ℤ) :=
    Rat.den_dvd a' b'
  have hden : (Rat.divInt a' b').den ∣ b' := by
    exact_mod_cast hdenZ
  simpa [hp] using hden

end

end ExactCorrection

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Lemma14.lean` -/

section
/-!
# Martin's two-inverse lemma

This file gives the source-faithful form of Lemma 14 in Greg Martin's
*Denser Egyptian fractions*.  If the odd prime power `q = p ^ ν` is at
least five, then every residue modulo its underlying prime is a sum of the
inverses of two distinct integers in `[(q - 3) / 2, q)`.

The prime-three case is the separate explicit construction from the paper.
For primes at least five we reuse the finite pigeonhole proof in
`Erdos285.ExactCorrection`.
-/

namespace MartinCorrection

private theorem martin_lemma14_three {q ν : ℕ} (hν : 0 < ν)
    (hqpow : q = 3 ^ ν) (hq5 : 5 ≤ q) (a : ZMod 3) :
    ∃ m₁ m₂ : ℕ,
      (q - 3) / 2 ≤ m₁ ∧
      m₁ < m₂ ∧ m₂ < q ∧
      ¬ 3 ∣ m₁ * m₂ ∧
      ((m₁ : ZMod 3)⁻¹ + (m₂ : ZMod 3)⁻¹) = a := by
  have hν2 : 2 ≤ ν := by
    by_contra h
    have hν1 : ν = 1 := by omega
    subst ν
    norm_num [hqpow] at hq5
  have hq9 : 9 ≤ q := by
    rw [hqpow]
    exact Nat.pow_le_pow_right (n := 3) (by omega) hν2
  have hqdiv : 3 ∣ q := by
    rw [hqpow]
    exact dvd_pow_self 3 (Nat.ne_zero_of_lt hν)
  have hqcast : (q : ZMod 3) = 0 :=
    (ZMod.natCast_eq_zero_iff q 3).2 hqdiv
  have hthree : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
  have hinv_two : ((2 : ZMod 3)⁻¹) = 2 := by
    apply ZMod.inv_eq_of_mul_eq_one
    linear_combination hthree
  have hneg_one : (-((1 : ℕ) : ZMod 3)) = 2 := by
    linear_combination -hthree
  have hneg_two : (-((2 : ℕ) : ZMod 3)) = 1 := by
    linear_combination -hthree
  have hneg_four : (-((4 : ℕ) : ZMod 3)) = 2 := by
    linear_combination -2 * hthree
  have hneg_five : (-((5 : ℕ) : ZMod 3)) = 1 := by
    linear_combination -2 * hthree
  fin_cases a
  · refine ⟨q - 2, q - 1, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · intro hdvd
      have hz : (((q - 2) * (q - 1) : ℕ) : ZMod 3) = 0 :=
        (ZMod.natCast_eq_zero_iff ((q - 2) * (q - 1)) 3).2 hdvd
      push_cast at hz
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast] at hz
      have hdiv : 3 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).1 hz
      norm_num at hdiv
    · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast]
      change (-((2 : ℕ) : ZMod 3))⁻¹ + (-((1 : ℕ) : ZMod 3))⁻¹ = 0
      simp only [hneg_two, hneg_one, ZMod.inv_one, hinv_two]
      exact hthree
  · refine ⟨q - 4, q - 1, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · intro hdvd
      have hz : (((q - 4) * (q - 1) : ℕ) : ZMod 3) = 0 :=
        (ZMod.natCast_eq_zero_iff ((q - 4) * (q - 1)) 3).2 hdvd
      push_cast at hz
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast] at hz
      have hdiv : 3 ∣ 4 := (ZMod.natCast_eq_zero_iff 4 3).1 hz
      norm_num at hdiv
    · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast]
      change (-((4 : ℕ) : ZMod 3))⁻¹ + (-((1 : ℕ) : ZMod 3))⁻¹ = 1
      simp only [hneg_four, hneg_one, hinv_two]
      linear_combination hthree
  · refine ⟨q - 5, q - 2, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · intro hdvd
      have hz : (((q - 5) * (q - 2) : ℕ) : ZMod 3) = 0 :=
        (ZMod.natCast_eq_zero_iff ((q - 5) * (q - 2)) 3).2 hdvd
      push_cast at hz
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast] at hz
      have hdiv : 3 ∣ 10 := (ZMod.natCast_eq_zero_iff 10 3).1 hz
      norm_num at hdiv
    · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), hqcast]
      change (-((5 : ℕ) : ZMod 3))⁻¹ + (-((2 : ℕ) : ZMod 3))⁻¹ = 2
      simp only [hneg_five, hneg_two, ZMod.inv_one]
      ring

/--
Martin's Lemma 14.  The congruence in the conclusion is modulo the underlying
prime `p`, rather than modulo the prime power `q`.
-/
theorem martin_lemma14 {p q ν : ℕ} (hp : p.Prime) (hν : 0 < ν)
    (hqpow : q = p ^ ν) (hqodd : Odd q) (hq5 : 5 ≤ q) (a : ZMod p) :
    ∃ m₁ m₂ : ℕ,
      (q - 3) / 2 ≤ m₁ ∧
      m₁ < m₂ ∧ m₂ < q ∧
      ¬ p ∣ m₁ * m₂ ∧
      ((m₁ : ZMod p)⁻¹ + (m₂ : ZMod p)⁻¹) = a := by
  by_cases hp3 : p = 3
  · subst p
    exact martin_lemma14_three hν hqpow hq5 a
  · have hp2 : p ≠ 2 := by
      intro hp2
      subst p
      have htwo_dvd : 2 ∣ q := by
        rw [hqpow]
        exact dvd_pow_self 2 (Nat.ne_zero_of_lt hν)
      exact (Nat.not_even_iff_odd.mpr hqodd) (even_iff_two_dvd.mpr htwo_dvd)
    have hp5 : 5 ≤ p := by
      have hp_one := hp.one_lt
      have hp_odd := hp.odd_of_ne_two hp2
      rcases hp_odd with ⟨k, hk⟩
      omega
    simpa [hqpow] using
      (Erdos285.ExactCorrection.martin_lemma14_of_five_le hp hp5 hν a)

end MartinCorrection

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Lemma15.lean` -/

section
/-!
# Martin's prime-power elimination lemma

This file formalizes the bounded two-term (or one-term at the prime `2`)
denominator correction used in the exact-correction stage of the proof of
Erdős Problem 285.
-/

namespace MartinCorrection

open Finset
open scoped BigOperators

noncomputable section

open PrimePowers

/-- Every exact prime-power part of an LCM is already an exact part of one of
the two inputs.  The exponent in an LCM is the maximum of the two exponents. -/
lemma primePowerParts_lcm_subset {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    primePowerParts (Nat.lcm a b) ⊆ primePowerParts a ∪ primePowerParts b := by
  intro q hq
  rcases (mem_primePowerParts (Nat.lcm_ne_zero ha hb)).mp hq with
    ⟨hqpp, hqdiv, hqcop⟩
  rcases (isPrimePow_nat_iff q).mp hqpp with ⟨p, k, hp, hk, rfl⟩
  have hlcmfac : (Nat.lcm a b).factorization p = k :=
    (UnitFractions.factorization_eq_iff hp hk.ne').mp ⟨hqdiv, hqcop⟩
  rw [Nat.factorization_lcm ha hb, Finsupp.sup_apply] at hlcmfac
  have hcases : a.factorization p = k ∨ b.factorization p = k := by
    omega
  rw [Finset.mem_union]
  rcases hcases with hafac | hbfac
  · left
    apply (mem_primePowerParts ha).mpr
    exact ⟨hp.isPrimePow.pow hk.ne',
      (UnitFractions.factorization_eq_iff hp hk.ne').mpr hafac⟩
  · right
    apply (mem_primePowerParts hb).mpr
    exact ⟨hp.isPrimePow.pow hk.ne',
      (UnitFractions.factorization_eq_iff hp hk.ne').mpr hbfac⟩

/-- Taking an LCM preserves a common upper bound for exact prime-power parts. -/
lemma largestPrimePowerPart_lcm_le {a b y : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha_bound : largestPrimePowerPart a ≤ y)
    (hb_bound : largestPrimePowerPart b ≤ y) :
    largestPrimePowerPart (Nat.lcm a b) ≤ y := by
  rw [largestPrimePowerPart_le_iff] at ha_bound hb_bound ⊢
  intro q hq
  rcases Finset.mem_union.mp (primePowerParts_lcm_subset ha hb hq) with hqa | hqb
  · exact ha_bound q hqa
  · exact hb_bound q hqb

/-- A positive prime power is its own largest exact prime-power part. -/
lemma largestPrimePowerPart_primePower {q : ℕ} (hq : IsPrimePow q) :
    largestPrimePowerPart q = q := by
  apply le_antisymm largestPrimePowerPart_le
  apply le_largestPrimePowerPart
  apply (mem_primePowerParts hq.ne_zero).mpr
  refine ⟨hq, dvd_rfl, ?_⟩
  rw [Nat.div_self hq.pos]
  exact (Nat.coprime_one_right_iff q).mpr trivial

/-- Multiplying a prime power by a smaller coprime factor leaves that prime
power as the largest exact prime-power part. -/
lemma largestPrimePowerPart_mul_eq_left {q m : ℕ} (hq : IsPrimePow q)
    (hm : m < q) (hcop : Nat.Coprime q m) :
    largestPrimePowerPart (q * m) = q := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hm0 : m ≠ 0 := by
    intro hm0
    subst m
    simp at hcop
    exact hq.ne_one hcop
  have hmul : Nat.lcm q m = q * m := hcop.lcm_eq_mul
  have hle : largestPrimePowerPart (q * m) ≤ q := by
    rw [← hmul]
    apply largestPrimePowerPart_lcm_le hq0 hm0
    · exact (largestPrimePowerPart_primePower hq).le
    · exact largestPrimePowerPart_le.trans (Nat.le_of_lt hm)
  apply le_antisymm hle
  apply le_largestPrimePowerPart
  apply (mem_primePowerParts (mul_ne_zero hq0 hm0)).mpr
  refine ⟨hq, dvd_mul_right q m, ?_⟩
  simpa [Nat.mul_div_cancel_left _ hq.pos] using hcop

/-- If the first input has no exact prime-power part larger than the prime
power `q`, then `q` is an exact part of its LCM with `q`. -/
lemma primePower_mem_parts_lcm_right {a q : ℕ} (ha : a ≠ 0)
    (hq : IsPrimePow q) (ha_bound : largestPrimePowerPart a ≤ q) :
    q ∈ primePowerParts (Nat.lcm a q) := by
  rcases (isPrimePow_nat_iff q).mp hq with ⟨p, ν, hp, hν, rfl⟩
  have hfac_le : a.factorization p ≤ ν := by
    by_cases hfac0 : a.factorization p = 0
    · omega
    · have hpart : p ^ a.factorization p ∈ primePowerParts a := by
        apply (mem_primePowerParts ha).mpr
        exact ⟨hp.isPrimePow.pow hfac0,
          (UnitFractions.factorization_eq_iff hp hfac0).mpr rfl⟩
      have hpw_le : p ^ a.factorization p ≤ p ^ ν :=
        (le_largestPrimePowerPart hpart).trans ha_bound
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpw_le
  have hlcm0 : Nat.lcm a (p ^ ν) ≠ 0 :=
    Nat.lcm_ne_zero ha (pow_ne_zero _ hp.ne_zero)
  apply (mem_primePowerParts hlcm0).mpr
  refine ⟨hp.isPrimePow.pow hν.ne', ?_⟩
  apply (UnitFractions.factorization_eq_iff hp hν.ne').mpr
  rw [Nat.factorization_lcm ha (pow_ne_zero _ hp.ne_zero),
    Finsupp.sup_apply, hp.factorization_pow]
  simp [hfac_le]

/-- If all exact parts are at most `q`, but `q` itself does not divide the
integer, then the largest exact part is strictly smaller than `q`. -/
lemma largestPrimePowerPart_lt_of_le_of_not_dvd {n q : ℕ}
    (hq : IsPrimePow q) (hbound : largestPrimePowerPart n ≤ q)
    (hnotdvd : ¬ q ∣ n) : largestPrimePowerPart n < q := by
  by_cases hn : n < 2
  · have hempty : primePowerParts n = ∅ := primePowerParts_empty_iff.mpr hn
    simp [largestPrimePowerPart, hempty, hq.pos]
  · have hn2 : 2 ≤ n := Nat.le_of_not_gt hn
    have hmem := largestPrimePowerPart_mem hn2
    have hne : largestPrimePowerPart n ≠ q := by
      intro heq
      have hspec := (mem_primePowerParts (by omega)).mp hmem
      exact hnotdvd (heq ▸ hspec.2.1)
    omega

/-- Exact prime-power parts can only decrease on passing to a divisor. -/
lemma largestPrimePowerPart_le_of_dvd {a b : ℕ} (hb : b ≠ 0)
    (hab : a ∣ b) : largestPrimePowerPart a ≤ largestPrimePowerPart b := by
  rw [largestPrimePowerPart_le_iff]
  intro q hqa
  rcases (mem_primePowerParts (fun ha ↦ hb (zero_dvd_iff.mp (ha ▸ hab)))).mp hqa with
    ⟨hqpp, hqdiva, hqcop⟩
  rcases (isPrimePow_nat_iff q).mp hqpp with ⟨p, k, hp, hk, rfl⟩
  have hafac : a.factorization p = k :=
    (UnitFractions.factorization_eq_iff hp hk.ne').mp ⟨hqdiva, hqcop⟩
  have hfac_le : a.factorization p ≤ b.factorization p := by
    exact (Nat.factorization_le_iff_dvd
      (fun ha ↦ hb (zero_dvd_iff.mp (ha ▸ hab))) hb).mpr hab p
  let K := b.factorization p
  have hK : K ≠ 0 := by
    dsimp [K]
    omega
  have hpart : p ^ K ∈ primePowerParts b := by
    apply (mem_primePowerParts hb).mpr
    exact ⟨hp.isPrimePow.pow hK,
      (UnitFractions.factorization_eq_iff hp hK).mpr rfl⟩
  calc
    p ^ k ≤ p ^ K := Nat.pow_le_pow_right hp.pos (by simpa [K, hafac] using hfac_le)
    _ ≤ largestPrimePowerPart b := le_largestPrimePowerPart hpart

/-- A finite LCM has bounded exact prime-power parts when every member does. -/
lemma largestPrimePowerPart_finset_lcm_le {A : Finset ℕ} {q : ℕ}
    (hzero : 0 ∉ A) (hA : ∀ n ∈ A, largestPrimePowerPart n ≤ q) :
    largestPrimePowerPart (A.lcm id) ≤ q := by
  induction A using Finset.induction with
  | empty =>
      have hparts : primePowerParts 1 = ∅ := primePowerParts_empty_iff.mpr (by omega)
      simp [largestPrimePowerPart, hparts]
  | @insert n A hn ih =>
      have hn0 : n ≠ 0 := by
        intro hn0
        exact hzero (hn0 ▸ Finset.mem_insert_self n A)
      have hA0 : 0 ∉ A := fun h ↦ hzero (Finset.mem_insert_of_mem h)
      rw [Finset.lcm_insert]
      apply largestPrimePowerPart_lcm_le hn0 (UnitFractions.lcm_ne_zero_of_zero_not_mem hA0)
      · exact hA n (Finset.mem_insert_self n A)
      · apply ih hA0
        intro m hm
        exact hA m (Finset.mem_insert_of_mem hm)

/-- The residual denominator remains `q`-smooth after subtracting a finite
sum whose displayed denominators all have largest exact part `q`. -/
lemma residual_largestPrimePowerPart_le (q : ℕ) (r : ℚ) (U : Finset ℕ)
    (hq : IsPrimePow q) (hr : largestPrimePowerPart r.den ≤ q)
    (hU : ∀ n ∈ U, largestPrimePowerPart n = q) :
    largestPrimePowerPart (r - UnitFractions.rec_sum U).den ≤ q := by
  have hzero : 0 ∉ U := by
    intro h0
    have hz := hU 0 h0
    simp [largestPrimePowerPart, primePowerParts] at hz
    exact hq.ne_zero hz.symm
  have hlcm0 : U.lcm id ≠ 0 := UnitFractions.lcm_ne_zero_of_zero_not_mem hzero
  have hUlcm : largestPrimePowerPart (U.lcm id) ≤ q := by
    apply largestPrimePowerPart_finset_lcm_le hzero
    intro n hn
    rw [hU n hn]
  let L := Nat.lcm r.den (U.lcm id)
  have hL0 : L ≠ 0 := Nat.lcm_ne_zero r.den_ne_zero hlcm0
  have hLbound : largestPrimePowerPart L ≤ q :=
    largestPrimePowerPart_lcm_le r.den_ne_zero hlcm0 hr hUlcm
  have hrec : (UnitFractions.rec_sum U).den ∣ U.lcm id :=
    recSum_den_dvd_lcm U
  have hden : (r - UnitFractions.rec_sum U).den ∣ L := by
    exact (Rat.sub_den_dvd_lcm r (UnitFractions.rec_sum U)).trans
      (lcm_dvd_lcm dvd_rfl hrec)
  exact (largestPrimePowerPart_le_of_dvd hL0 hden).trans hLbound

/-- Put a rational and two unit fractions over a common displayed
denominator.  The LCM applications below take `D = lcm r.den q`. -/
lemma two_term_residual_eq_divInt (r : ℚ) (q m₁ m₂ D : ℕ)
    (hq : q ≠ 0) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hD0 : D ≠ 0)
    (hdenD : r.den ∣ D) (hqD : q ∣ D) :
    r - ((1 : ℚ) / (q * m₁) + 1 / (q * m₂)) =
      Rat.divInt
        (r.num * (D / r.den : ℕ) * m₁ * m₂ -
          ((D / q : ℕ) * (m₁ + m₂) : ℕ))
        (D * m₁ * m₂ : ℕ) := by
  have hden0 : r.den ≠ 0 := r.den_ne_zero
  have hDden : r.den * (D / r.den) = D := Nat.mul_div_cancel' hdenD
  have hDq : q * (D / q) = D := Nat.mul_div_cancel' hqD
  have hDdenQ : (r.den : ℚ) * (D / r.den : ℕ) = D := by exact_mod_cast hDden
  have hDqQ : (q : ℚ) * (D / q : ℕ) = D := by exact_mod_cast hDq
  have hcastDen : (D : ℚ) / r.den = (D / r.den : ℕ) := by
    rw [div_eq_iff]
    · exact_mod_cast hDden.symm.trans (mul_comm _ _)
    · exact_mod_cast hden0
  have hcastQ : (D : ℚ) / q = (D / q : ℕ) := by
    rw [div_eq_iff]
    · exact_mod_cast hDq.symm.trans (mul_comm _ _)
    · exact_mod_cast hq
  rw [Rat.divInt_eq_div]
  nth_rw 1 [← r.num_div_den]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Nat.cast_add]
  field_simp
  simp only [Int.cast_add, Int.cast_natCast]
  ring_nf at hDdenQ hDqQ ⊢
  rw [hDdenQ]
  linear_combination ((r.den : ℚ) * m₁ + r.den * m₂) * hDqQ

/-- One-term version of the displayed-denominator identity. -/
lemma one_term_residual_eq_divInt (r : ℚ) (q m : ℕ)
    (hq : q ≠ 0) (hm : m ≠ 0) (hqd : q ∣ r.den) :
    r - (1 : ℚ) / (q * m : ℕ) =
      Rat.divInt (r.num * m - (r.den / q : ℕ)) (r.den * m) := by
  let d := r.den / q
  change r - (1 : ℚ) / (q * m : ℕ) =
    Rat.divInt (r.num * m - (d : ℕ)) (r.den * m)
  have hden : q * d = r.den := Nat.mul_div_cancel' hqd
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hdenQ : (q : ℚ) * d = r.den := by exact_mod_cast hden
  rw [Rat.divInt_eq_div]
  nth_rw 1 [← r.num_div_den]
  push_cast
  field_simp
  rw [← hdenQ]
  ring

/-- Cancelling one copy of the underlying prime from a displayed denominator
whose exact `p`-part is `p^ν` makes that prime power cease to divide. -/
lemma primePow_not_dvd_mul_div_prime {p ν q D m : ℕ} (hp : p.Prime)
    (hν : 0 < ν) (hq : q = p ^ ν) (hpart : q ∈ primePowerParts D)
    (hpm : ¬ p ∣ m) : ¬ q ∣ (D * m) / p := by
  subst q
  have hD0 : D ≠ 0 := by
    intro h
    subst D
    simp [primePowerParts] at hpart
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    exact hpm (dvd_zero p)
  have hDfac : D.factorization p = ν := by
    have hs := (mem_primePowerParts hD0).mp hpart
    exact (UnitFractions.factorization_eq_iff hp hν.ne').mp hs.2
  have hpD : p ∣ D := by
    exact (dvd_pow_self p hν.ne').trans ((mem_primePowerParts hD0).mp hpart).2.1
  have hpDm : p ∣ D * m := hpD.trans (dvd_mul_right D m)
  have hDm0 : D * m ≠ 0 := mul_ne_zero hD0 hm0
  have hB0 : (D * m) / p ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hDm0.bot_lt hpDm) hp.pos)
  have hfac : ((D * m) / p).factorization p = ν - 1 := by
    rw [Nat.factorization_div hpDm]
    simp [Nat.factorization_mul hD0 hm0, hDfac,
      Nat.factorization_eq_zero_of_not_dvd hpm, hp.factorization_self]
  intro hdvd
  have hνle : ν ≤ ((D * m) / p).factorization p :=
    (hp.pow_dvd_iff_le_factorization hB0).mp hdvd
  rw [hfac] at hνle
  omega

/-- Martin's prime-power elimination step.  The inequalities
`q^2 ≤ 5*n` and `n ≤ q^2` are the integral form of
`n ∈ [q^2/5,q^2]`. -/
theorem exists_elimination_set (q : ℕ) (hqpp : IsPrimePow q) (hq4 : 4 ≤ q)
    (r : ℚ) (hr : largestPrimePowerPart r.den ≤ q) :
    ∃ U : Finset ℕ,
      (∀ n ∈ U, q ^ 2 ≤ 5 * n ∧ n ≤ q ^ 2) ∧
      (Odd q → U.card = 2) ∧
      (Even q → U.card ≤ 1) ∧
      (∀ n ∈ U, largestPrimePowerPart n = q) ∧
      largestPrimePowerPart (r - UnitFractions.rec_sum U).den < q := by
  rcases (isPrimePow_nat_iff q).mp hqpp with ⟨p, ν, hp, hν, hqpow⟩
  let _ : Fact p.Prime := ⟨hp⟩
  have hq0 : q ≠ 0 := hqpp.ne_zero
  by_cases hqodd : Odd q
  · have hq5 : 5 ≤ q := by
      rcases hqodd with ⟨k, hk⟩
      omega
    let D := Nat.lcm r.den q
    have hD0 : D ≠ 0 := Nat.lcm_ne_zero r.den_ne_zero hq0
    have hdenD : r.den ∣ D := Nat.dvd_lcm_left _ _
    have hqD : q ∣ D := Nat.dvd_lcm_right _ _
    have hDpart : q ∈ primePowerParts D :=
      primePower_mem_parts_lcm_right r.den_ne_zero hqpp hr
    have hDspec := (mem_primePowerParts hD0).mp hDpart
    have hpq : p ∣ q := by
      rw [← hqpow]
      exact dvd_pow_self p hν.ne'
    have hpe : ¬ p ∣ D / q := by
      exact hp.coprime_iff_not_dvd.mp
        (Nat.Coprime.of_dvd_left hpq hDspec.2.2)
    let C : ℤ := r.num * (D / r.den : ℕ)
    let a : ZMod p := (C : ZMod p) * ((D / q : ℕ) : ZMod p)⁻¹
    obtain ⟨m₁, m₂, hm₁lo, hm₁m₂, hm₂q, hpm, hinv⟩ :=
      martin_lemma14 hp hν hqpow.symm hqodd hq5 a
    have hm₁pos : 0 < m₁ := by
      have : 1 ≤ (q - 3) / 2 := by omega
      omega
    have hm₂pos : 0 < m₂ := hm₁pos.trans hm₁m₂
    have hpm₁ : ¬ p ∣ m₁ := fun h ↦ hpm (h.trans (dvd_mul_right m₁ m₂))
    have hpm₂ : ¬ p ∣ m₂ := fun h ↦ hpm (h.trans (dvd_mul_left m₂ m₁))
    have hcop₁ : Nat.Coprime q m₁ := by
      rw [← hqpow]
      exact (hp.coprime_pow_of_not_dvd hpm₁).symm
    have hcop₂ : Nat.Coprime q m₂ := by
      rw [← hqpow]
      exact (hp.coprime_pow_of_not_dvd hpm₂).symm
    let n₁ := q * m₁
    let n₂ := q * m₂
    have hn₁ne : n₁ ≠ n₂ := by
      dsimp [n₁, n₂]
      intro h
      exact (Nat.ne_of_lt hm₁m₂) (mul_left_cancel₀ hq0 h)
    let U : Finset ℕ := {n₁, n₂}
    have hn₁largest : largestPrimePowerPart n₁ = q := by
      exact largestPrimePowerPart_mul_eq_left hqpp (hm₁m₂.trans hm₂q) hcop₁
    have hn₂largest : largestPrimePowerPart n₂ = q := by
      exact largestPrimePowerPart_mul_eq_left hqpp hm₂q hcop₂
    have hUlargest : ∀ n ∈ U, largestPrimePowerPart n = q := by
      intro n hn
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl
      · exact hn₁largest
      · exact hn₂largest
    have hinterval : ∀ n ∈ U, q ^ 2 ≤ 5 * n ∧ n ≤ q ^ 2 := by
      have hbase : q ≤ 5 * ((q - 3) / 2) := by
        obtain ⟨t, ht⟩ := hqodd
        omega
      have hqm₁ : q ≤ 5 * m₁ :=
        hbase.trans (Nat.mul_le_mul_left 5 hm₁lo)
      have hqm₂ : q ≤ 5 * m₂ := hqm₁.trans (Nat.mul_le_mul_left 5 hm₁m₂.le)
      intro n hn
      simp only [U, Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl
      · dsimp [n₁]
        constructor <;> nlinarith
      · dsimp [n₂]
        constructor <;> nlinarith
    let z : ℤ := C * m₁ * m₂ - ((D / q) * (m₁ + m₂) : ℕ)
    have hecast : ((D / q : ℕ) : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact hpe
    have hm₁cast : (m₁ : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact hpm₁
    have hm₂cast : (m₂ : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact hpm₂
    have hzcast : (z : ZMod p) = 0 := by
      simp only [z, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast, Nat.cast_mul,
        Nat.cast_add]
      calc
        (C : ZMod p) * m₁ * m₂ -
            (D / q : ℕ) * ((m₁ : ZMod p) + (m₂ : ZMod p)) =
            (D / q : ℕ) * m₁ * m₂ *
              ((C : ZMod p) * ((D / q : ℕ) : ZMod p)⁻¹ -
                ((m₁ : ZMod p)⁻¹ + (m₂ : ZMod p)⁻¹)) := by
                  field_simp
                  ring
        _ = 0 := by rw [hinv]; simp [a]
    have hpz : (p : ℤ) ∣ z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hzcast
    have hrepr : r - UnitFractions.rec_sum U =
        Rat.divInt z (D * m₁ * m₂) := by
      have hraw := two_term_residual_eq_divInt r q m₁ m₂ D hq0
        hm₁pos.ne' hm₂pos.ne' hD0 hdenD hqD
      dsimp [z, C]
      simpa [U, n₁, n₂, UnitFractions.rec_sum, hn₁ne, sub_eq_add_neg,
        add_assoc] using hraw
    have hpB : p ∣ D * m₁ * m₂ := by
      exact (hpq.trans hDspec.2.1).trans
        (dvd_mul_of_dvd_left (dvd_mul_right D m₁) m₂)
    have hdenDiv : (r - UnitFractions.rec_sum U).den ∣
        (D * (m₁ * m₂)) / p := by
      have := ExactCorrection.rat_den_dvd_div_of_eq_divInt
        (r := r - UnitFractions.rec_sum U) (a := z)
        (b := D * m₁ * m₂) (p := p)
        (mul_ne_zero (mul_ne_zero hD0 hm₁pos.ne') hm₂pos.ne') hp.ne_zero hpB hpz hrepr
      simpa [mul_assoc] using this
    have hqnotB : ¬ q ∣ (D * (m₁ * m₂)) / p :=
      primePow_not_dvd_mul_div_prime hp hν hqpow.symm hDpart hpm
    have hqnotden : ¬ q ∣ (r - UnitFractions.rec_sum U).den :=
      fun h ↦ hqnotB (h.trans hdenDiv)
    have hresle : largestPrimePowerPart (r - UnitFractions.rec_sum U).den ≤ q :=
      residual_largestPrimePowerPart_le q r U hqpp hr hUlargest
    refine ⟨U, hinterval, ?_, ?_, hUlargest,
      largestPrimePowerPart_lt_of_le_of_not_dvd hqpp hresle hqnotden⟩
    · intro _
      simp [U, hn₁ne]
    · intro heven
      exact ((Nat.not_even_iff_odd.mpr hqodd) heven).elim
  · have hqeven : Even q := Nat.not_odd_iff_even.mp hqodd
    by_cases hqd : q ∣ r.den
    · -- The even correction is the single denominator `q(q-1)`.
      have hp2 : p = 2 := by
        rcases hp.eq_two_or_odd' with hp2 | hpodd
        · exact hp2
        · exfalso
          apply hqodd
          rw [← hqpow]
          exact hpodd.pow
      subst p
      have hqpow2 : q = 2 ^ ν := hqpow.symm
      have h2q : 2 ∣ q := by
        rw [hqpow2]
        exact dvd_pow_self 2 hν.ne'
      let m := q - 1
      have hmpos : 0 < m := by dsimp [m]; omega
      have hcop : Nat.Coprime q m := by
        apply (Nat.coprime_sub_self_left (Nat.sub_le q 1)).mp
        have hsub : q - (q - 1) = 1 := by omega
        rw [hsub]
        exact (Nat.coprime_one_left_iff (q - 1)).mpr trivial
      have h2m : ¬ 2 ∣ m := by
        exact Nat.prime_two.coprime_iff_not_dvd.mp
          (Nat.Coprime.of_dvd_left h2q hcop)
      let n := q * m
      let U : Finset ℕ := {n}
      have hnlargest : largestPrimePowerPart n = q := by
        apply largestPrimePowerPart_mul_eq_left hqpp
        · dsimp [m]
          omega
        · exact hcop
      have hUlargest : ∀ x ∈ U, largestPrimePowerPart x = q := by
        intro x hx
        have hx' : x = n := by simpa [U] using hx
        rw [hx']
        exact hnlargest
      have hinterval : ∀ x ∈ U, q ^ 2 ≤ 5 * x ∧ x ≤ q ^ 2 := by
        intro x hx
        have hx' : x = n := by simpa [U] using hx
        subst x
        dsimp [n, m]
        constructor
        · have hsmall : q ≤ 5 * (q - 1) := by omega
          have := Nat.mul_le_mul_left q hsmall
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
        · have := Nat.mul_le_mul_left q (Nat.sub_le q 1)
          simpa [pow_two] using this
      have hlcm : Nat.lcm r.den q = r.den := by
        apply Nat.dvd_antisymm
        · exact Nat.lcm_dvd dvd_rfl hqd
        · exact Nat.dvd_lcm_left _ _
      have hdenpart : q ∈ primePowerParts r.den := by
        have h := primePower_mem_parts_lcm_right r.den_ne_zero hqpp hr
        rwa [hlcm] at h
      have hdenspec := (mem_primePowerParts r.den_ne_zero).mp hdenpart
      have h2den : 2 ∣ r.den := h2q.trans hqd
      have hnumcop : Nat.Coprime 2 r.num.natAbs :=
        Nat.Coprime.of_dvd_left h2den r.reduced.symm
      have hquotcop : Nat.Coprime 2 (r.den / q) :=
        Nat.Coprime.of_dvd_left h2q hdenspec.2.2
      have hnumcast : (r.num : ZMod 2) ≠ 0 := by
        rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact fun hdiv ↦ (Nat.prime_two.coprime_iff_not_dvd.mp hnumcop)
          (Int.natCast_dvd.mp hdiv)
      have hmcast : (m : ZMod 2) ≠ 0 := by
        rw [ne_eq, ZMod.natCast_eq_zero_iff]
        exact h2m
      have hquotcast : ((r.den / q : ℕ) : ZMod 2) ≠ 0 := by
        rw [ne_eq, ZMod.natCast_eq_zero_iff]
        exact Nat.prime_two.coprime_iff_not_dvd.mp hquotcop
      have hnum1 : (r.num : ZMod 2) = 1 := Fin.eq_one_of_ne_zero _ hnumcast
      have hm1 : (m : ZMod 2) = 1 := Fin.eq_one_of_ne_zero _ hmcast
      have hquot1 : ((r.den / q : ℕ) : ZMod 2) = 1 :=
        Fin.eq_one_of_ne_zero _ hquotcast
      let z : ℤ := r.num * m - (r.den / q : ℕ)
      have hzcast : (z : ZMod 2) = 0 := by
        simp only [z, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
        rw [hnum1, hm1, hquot1]
        ring
      have h2z : (2 : ℤ) ∣ z :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mp hzcast
      have hrepr : r - UnitFractions.rec_sum U =
          Rat.divInt z (r.den * m) := by
        have hraw := one_term_residual_eq_divInt r q m hq0 hmpos.ne' hqd
        dsimp [z]
        simpa [U, n, UnitFractions.rec_sum] using hraw
      have h2B : 2 ∣ r.den * m := h2den.trans (dvd_mul_right r.den m)
      have hdenDiv : (r - UnitFractions.rec_sum U).den ∣ (r.den * m) / 2 :=
        ExactCorrection.rat_den_dvd_div_of_eq_divInt
          (r := r - UnitFractions.rec_sum U) (a := z) (b := r.den * m) (p := 2)
          (mul_ne_zero r.den_ne_zero hmpos.ne') (by norm_num) h2B h2z hrepr
      have hqnotB : ¬ q ∣ (r.den * m) / 2 :=
        primePow_not_dvd_mul_div_prime Nat.prime_two hν hqpow2 hdenpart h2m
      have hqnotden : ¬ q ∣ (r - UnitFractions.rec_sum U).den :=
        fun h ↦ hqnotB (h.trans hdenDiv)
      have hresle : largestPrimePowerPart (r - UnitFractions.rec_sum U).den ≤ q :=
        residual_largestPrimePowerPart_le q r U hqpp hr hUlargest
      refine ⟨U, hinterval, ?_, ?_, hUlargest,
        largestPrimePowerPart_lt_of_le_of_not_dvd hqpp hresle hqnotden⟩
      · intro h
        exact (hqodd h).elim
      · intro _
        simp [U]
    · refine ⟨∅, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · intro h
        exact (hqodd h).elim
      · simp
      · simp
      · simpa using largestPrimePowerPart_lt_of_le_of_not_dvd hqpp hr hqd

end

end MartinCorrection

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Lemma16.lean` -/

section
/-!
# Martin's small-prime-power elimination lemma

This file formalizes the elementary LCM step used for the small prime powers
in Martin's exact correction.  If `q = p ^ e` is the largest exact
prime-power part of the reduced denominator of a rational `r`, we subtract a
single unit fraction whose denominator is `lcm(1,...,q) / a`, where
`1 ≤ a ≤ p - 1`.  The residue `a` is chosen so that reduction cancels one
additional factor of `p`; all other prime-power parts were already strictly
smaller than `q`.
-/

namespace Lemma16

open Finset
open scoped BigOperators

noncomputable section

open PrimePowers

/-- A prime power dividing `lcm(1,...,y)` is at most `y`. -/
lemma isPrimePow_le_of_dvd_initialLcm {y t : ℕ} (ht : IsPrimePow t)
    (htL : t ∣ initialLcm y) : t ≤ y := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 ht
  have hL0 : initialLcm y ≠ 0 := by
    simp [initialLcm]
  have hkL : k ≤ (initialLcm y).factorization p :=
    (hp.pow_dvd_iff_le_factorization hL0).1 htL
  have hfac : (initialLcm y).factorization p =
      (Icc 1 y).sup (fun a ↦ a.factorization p) := by
    rw [initialLcm]
    simpa only [id_eq] using
      (Finset.factorization_lcm
        (s := Icc 1 y) (f := id) (by
          intro a ha
          exact Nat.ne_of_gt (Finset.mem_Icc.mp ha).1) p)
  rw [hfac] at hkL
  have hIcc : (Icc 1 y).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hkL
    omega
  obtain ⟨a, ha, hsup⟩ :=
    Finset.sup_eq_mem (s := Icc 1 y)
      (f := fun a ↦ a.factorization p) hIcc
  rw [hsup] at hkL
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp ha).1
  have hpa : p ^ k ∣ a := (hp.pow_dvd_iff_le_factorization ha0).2 hkL
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hpa).trans (Finset.mem_Icc.mp ha).2

/-- If all exact prime-power parts of `d` are at most `y`, then `d` divides
`lcm(1,...,y)`. -/
lemma dvd_initialLcm_of_primePowerSmooth {d y : ℕ} (hd : d ≠ 0)
    (hdy : PrimePowerSmooth y d) : d ∣ initialLcm y := by
  have hparts : (primePowerParts d).lcm id ∣ initialLcm y := by
    apply Finset.lcm_dvd
    intro t ht
    exact (Finset.dvd_lcm (s := Icc 1 y) (f := id)
      (Finset.mem_Icc.mpr
        ⟨((mem_primePowerParts hd).mp ht).1.one_lt.le, hdy t ht⟩))
  have hpartsEq : (primePowerParts d).lcm id = d := by
    calc
      (primePowerParts d).lcm id =
          UnitFractions.lcmA (UnitFractions.ppowers_in_set {d}) := by
            rw [primePowerParts_eq_ppowers_in_singleton]
      _ = UnitFractions.lcmA ({d} : Finset ℕ) :=
        UnitFractions.lcm_Q (by simpa using hd.symm)
      _ = d := by simp [UnitFractions.lcmA]
  rwa [hpartsEq] at hparts

/-- At the endpoint `q = p^e`, the `p`-part of `lcm(1,...,q)` is exactly
`q`. -/
lemma primePower_mem_initialLcm_parts {p e q : ℕ} (hp : p.Prime)
    (he : 0 < e) (hq : q = p ^ e) :
    q ∈ primePowerParts (initialLcm q) := by
  subst q
  have hqpp : IsPrimePow (p ^ e) := ⟨p, e, hp.prime, he, rfl⟩
  have hqmem : p ^ e ∈ Icc 1 (p ^ e) := by
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, le_rfl⟩
  have hqL : p ^ e ∣ initialLcm (p ^ e) :=
    Finset.dvd_lcm (s := Icc 1 (p ^ e)) (f := id) hqmem
  rw [mem_primePowerParts (by simp [initialLcm])]
  refine ⟨hqpp, hqL, ?_⟩
  rw [Nat.coprime_pow_left_iff he, hp.coprime_iff_not_dvd]
  intro hpdiv
  have hsuccDiv : p ^ (e + 1) ∣ initialLcm (p ^ e) := by
    rw [pow_succ]
    exact Nat.mul_dvd_of_dvd_div hqL hpdiv
  have hle := isPrimePow_le_of_dvd_initialLcm
    (show IsPrimePow (p ^ (e + 1)) from
      ⟨p, e + 1, hp.prime, Nat.succ_pos e, rfl⟩) hsuccDiv
  exact (not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self e))) hle

/-- Dividing the endpoint LCM by its base prime removes the only possible
exact prime-power part of size `q = p^e`. -/
lemma largestPrimePowerPart_lt_of_dvd_initialLcm_div_prime
    {p e q d : ℕ} (hp : p.Prime) (he : 0 < e) (hq : q = p ^ e)
    (hd : d ∣ initialLcm q / p) :
    largestPrimePowerPart d < q := by
  subst q
  have hpq : p ∣ p ^ e := dvd_pow_self p he.ne'
  have hqL : p ^ e ∣ initialLcm (p ^ e) :=
    Finset.dvd_lcm (s := Icc 1 (p ^ e)) (f := id)
      (Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, le_rfl⟩)
  have hpL : p ∣ initialLcm (p ^ e) := hpq.trans hqL
  have hbound : PrimePowerSmooth (p ^ e - 1) d := by
    intro t ht
    have hd0 : d ≠ 0 := by
      intro hzero
      subst d
      simp [primePowerParts] at ht
    have htSpec := (mem_primePowerParts hd0).mp ht
    have htLdiv : t ∣ initialLcm (p ^ e) / p := htSpec.2.1.trans hd
    have htL : t ∣ initialLcm (p ^ e) :=
      htLdiv.trans (Nat.div_dvd_of_dvd hpL)
    have htle : t ≤ p ^ e :=
      isPrimePow_le_of_dvd_initialLcm htSpec.1 htL
    have htne : t ≠ p ^ e := by
      intro hteq
      subst t
      have hsuccDiv : p ^ (e + 1) ∣ initialLcm (p ^ e) := by
        simpa [pow_succ, mul_comm] using
          (Nat.mul_dvd_of_dvd_div hpL htLdiv)
      have hle := isPrimePow_le_of_dvd_initialLcm
        (show IsPrimePow (p ^ (e + 1)) from
          ⟨p, e + 1, hp.prime, Nat.succ_pos e, rfl⟩) hsuccDiv
      exact (not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self e))) hle
    omega
  have hle : largestPrimePowerPart d ≤ p ^ e - 1 :=
    largestPrimePowerPart_le_iff.mpr hbound
  have hqpos : 0 < p ^ e := pow_pos hp.pos e
  omega

/-- Cancel a displayed common natural factor before bounding a rational's
reduced denominator. -/
lemma rat_den_dvd_div_of_eq_divInt {r : ℚ} {a : ℤ} {b p : ℕ}
    (hb : b ≠ 0) (hp0 : p ≠ 0) (hpb : p ∣ b)
    (hpa : (p : ℤ) ∣ a) (hr : r = Rat.divInt a b) :
    r.den ∣ b / p := by
  obtain ⟨b', rfl⟩ := hpb
  obtain ⟨a', ha'⟩ := hpa
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp0
  have hrepr : r = Rat.divInt a' b' := by
    rw [hr, ha']
    push_cast
    exact Rat.divInt_mul_left hpZ
  rw [hrepr]
  have hdenZ : (((Rat.divInt a' b').den : ℕ) : ℤ) ∣ (b' : ℤ) :=
    Rat.den_dvd a' b'
  have hden : (Rat.divInt a' b').den ∣ b' := by
    exact_mod_cast hdenZ
  simpa [hp0] using hden

/-- Martin's Lemma 16 (the small-prime-power step).

The returned numerator `a` is the least positive residue of
`r.num * (L / r.den)` modulo `p`, and the unit-fraction denominator is
`n = L / a`, where `L = lcm(1,...,q)`. -/
theorem smallPrimePower_elimination (r : ℚ) {p e q : ℕ}
    (hp : p.Prime) (he : 0 < e) (hq : q = p ^ e)
    (hqmax : q = largestPrimePowerPart r.den) :
    ∃ a n : ℕ,
      1 ≤ a ∧ a ≤ p - 1 ∧ Nat.Coprime p a ∧
      a ∣ initialLcm q ∧ n = initialLcm q / a ∧
      initialLcm q / (p - 1) ≤ n ∧
      q ∣ n ∧ q ∈ primePowerParts n ∧
      PrimePowerSmooth q n ∧ largestPrimePowerPart n = q ∧
      largestPrimePowerPart (r - (1 : ℚ) / n).den < q := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hqpp : IsPrimePow q := by
    subst q
    exact ⟨p, e, hp.prime, he, rfl⟩
  have hqpos : 0 < q := hqpp.pos
  have hqleDen : q ≤ r.den := by
    rw [hqmax]
    exact largestPrimePowerPart_le
  have hden2 : 2 ≤ r.den := hqpp.two_le.trans hqleDen
  have hqDen : q ∈ primePowerParts r.den := by
    rw [hqmax]
    exact largestPrimePowerPart_mem hden2
  have hdenSmooth : PrimePowerSmooth q r.den := by
    rw [← largestPrimePowerPart_le_iff, ← hqmax]
  have hdenL : r.den ∣ initialLcm q :=
    dvd_initialLcm_of_primePowerSmooth r.den_ne_zero hdenSmooth
  have hqLpart : q ∈ primePowerParts (initialLcm q) :=
    primePower_mem_initialLcm_parts hp he hq
  have hLpos : 0 < initialLcm q :=
    Nat.pos_of_ne_zero (by simp [initialLcm])
  have hqDenSpec := (mem_primePowerParts r.den_ne_zero).mp hqDen
  have hqLSpec := (mem_primePowerParts (by simp [initialLcm])).mp hqLpart
  have hpq : p ∣ q := by
    subst q
    exact dvd_pow_self p he.ne'
  have hpDen : p ∣ r.den := hpq.trans hqDenSpec.2.1
  have hpNumCoprime : Nat.Coprime p r.num.natAbs :=
    Nat.Coprime.of_dvd_left hpDen r.reduced.symm
  have hratioDvd : initialLcm q / r.den ∣ initialLcm q / q :=
    Nat.div_dvd_div_left hdenL hqDenSpec.2.1
  have hpRatioCoprime : Nat.Coprime p (initialLcm q / r.den) := by
    have hpLquot : Nat.Coprime p (initialLcm q / q) :=
      Nat.Coprime.of_dvd_left hpq hqLSpec.2.2
    exact Nat.Coprime.of_dvd_right hratioDvd hpLquot
  have hnumCast : (r.num : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun hdiv ↦ (hp.coprime_iff_not_dvd.mp hpNumCoprime)
      (Int.natCast_dvd.mp hdiv)
  have hratioCast : ((initialLcm q / r.den : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hp.coprime_iff_not_dvd.mp hpRatioCoprime
  let u : ZMod p :=
    (r.num : ZMod p) * ((initialLcm q / r.den : ℕ) : ZMod p)
  have hu : u ≠ 0 := mul_ne_zero hnumCast hratioCast
  let a : ℕ := u.val
  have haPos : 0 < a := ZMod.val_pos.mpr hu
  have haLt : a < p := ZMod.val_lt u
  have haLe : a ≤ p - 1 := by omega
  have hpa : Nat.Coprime p a := by
    rw [hp.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt haPos haLt
  have hpLeq : p ≤ q := by
    rw [hq]
    exact Nat.le_self_pow he.ne' p
  have haq : a ≤ q := haLt.le.trans hpLeq
  have haL : a ∣ initialLcm q := by
    exact Finset.dvd_lcm (s := Icc 1 q) (f := id)
      (Finset.mem_Icc.mpr ⟨haPos, haq⟩)
  let n : ℕ := initialLcm q / a
  have hnEq : n = initialLcm q / a := rfl
  have hlower : initialLcm q / (p - 1) ≤ n := by
    rw [hnEq]
    exact Nat.div_le_div le_rfl haLe haPos.ne'
  have haqCoprime : Nat.Coprime a q := by
    rw [hq]
    exact hpa.symm.pow_right e
  have haLquot : a ∣ initialLcm q / q := by
    rw [← haqCoprime.dvd_mul_right]
    simpa [Nat.mul_div_cancel' hqLSpec.2.1, mul_comm] using haL
  have hnFactor : n = q * ((initialLcm q / q) / a) := by
    rw [hnEq, ← Nat.mul_div_assoc q haLquot, Nat.mul_div_cancel' hqLSpec.2.1]
  have hqN : q ∣ n := hnFactor.symm ▸ dvd_mul_right q _
  have hqNquot : n / q = (initialLcm q / q) / a := by
    rw [hnFactor, Nat.mul_div_cancel_left _ hqpos]
  have hqNcoprime : Nat.Coprime q (n / q) := by
    rw [hqNquot]
    exact Nat.Coprime.of_dvd_right (Nat.div_dvd_of_dvd haLquot) hqLSpec.2.2
  have hqNpart : q ∈ primePowerParts n := by
    have hn0 : n ≠ 0 := by
      exact Nat.ne_of_gt
        (Nat.div_pos (Nat.le_of_dvd hLpos haL) haPos)
    exact (mem_primePowerParts hn0).mpr ⟨hqpp, hqN, hqNcoprime⟩
  have hnSmooth : PrimePowerSmooth q n := by
    intro t ht
    have hn0 : n ≠ 0 := by
      exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hLpos haL) haPos)
    have htSpec := (mem_primePowerParts hn0).mp ht
    exact isPrimePow_le_of_dvd_initialLcm htSpec.1
      (htSpec.2.1.trans (Nat.div_dvd_of_dvd haL))
  have hnLargest : largestPrimePowerPart n = q := by
    apply Nat.le_antisymm
    · exact largestPrimePowerPart_le_iff.mpr hnSmooth
    · exact le_largestPrimePowerPart hqNpart
  let m : ℕ := initialLcm q / r.den
  let z : ℤ := r.num * (m : ℤ) - a
  have hzCast : (z : ZMod p) = 0 := by
    simp only [z, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    rw [show (a : ZMod p) = u by exact ZMod.natCast_zmod_val u]
    simp [u, m]
  have hpz : (p : ℤ) ∣ z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hzCast
  have hresidual : r - (1 : ℚ) / n = Rat.divInt z (initialLcm q) := by
    rw [Rat.divInt_eq_div]
    change r - (1 : ℚ) / n = (z : ℚ) / (initialLcm q : ℚ)
    have hzRat : (z : ℚ) = (r.num : ℚ) * (m : ℚ) - (a : ℚ) := by
      simp [z]
    rw [hzRat]
    nth_rewrite 1 [← Rat.num_div_den r]
    have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast haPos.ne'
    rw [hnEq, Nat.cast_div haL haQ]
    have hLdecomp : (initialLcm q : ℚ) =
        (r.den : ℚ) * (m : ℕ) := by
      dsimp [m]
      exact_mod_cast (Nat.mul_div_cancel' hdenL).symm
    have hmPos : 0 < m := by
      dsimp [m]
      exact Nat.div_pos (Nat.le_of_dvd hLpos hdenL) r.den_pos
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hmPos.ne'
    have hdQ : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    rw [hLdecomp]
    field_simp [haQ, hmQ, hdQ]
  have hpL : p ∣ initialLcm q := hpq.trans hqLSpec.2.1
  have hresDen : (r - (1 : ℚ) / n).den ∣ initialLcm q / p :=
    rat_den_dvd_div_of_eq_divInt hLpos.ne' hp.ne_zero hpL hpz hresidual
  have hdescent :
      largestPrimePowerPart (r - (1 : ℚ) / n).den < q :=
    largestPrimePowerPart_lt_of_dvd_initialLcm_div_prime hp he hq hresDen
  exact ⟨a, n, haPos, haLe, hpa, haL, hnEq, hlower, hqN, hqNpart,
    hnSmooth, hnLargest, hdescent⟩

end

end Lemma16

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/LcmTelescope.lean` -/

section
/-!
# LCM increments and the small-prime-power telescope

For a prime power `q = p ^ e`, the least common multiple of `1, ..., q`
acquires exactly one new factor `p` at `q`.  At every other positive integer
the least common multiple is unchanged.  These two facts turn the cost of
Martin's small-prime-power eliminations into an exact telescoping sum.
-/

namespace LcmTelescope

open Finset
open scoped BigOperators

noncomputable section

open PrimePowers

private lemma prime_log_pow_sub_one {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    p.log (p ^ e - 1) = e - 1 := by
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · have hepos : 0 < e := Nat.pos_of_ne_zero he
    have hexp : e - 1 < e := Nat.sub_lt hepos (by omega)
    have hpows : p ^ (e - 1) < p ^ e := Nat.pow_lt_pow_right hp.one_lt hexp
    omega
  · have hepos : 0 < e := Nat.pos_of_ne_zero he
    have hexp : e - 1 + 1 = e := by omega
    rw [hexp]
    exact Nat.sub_lt (pow_pos hp.pos e) (by omega)

private lemma prime_log_pow_eq_log_pred_of_ne {p e r : ℕ}
    (hp : p.Prime) (he : e ≠ 0) (hr : r.Prime) (hrp : r ≠ p) :
    r.log (p ^ e) = r.log (p ^ e - 1) := by
  have hq2 : 2 ≤ p ^ e := by
    exact IsPrimePow.two_le (hp.isPrimePow.pow he)
  have hpred : p ^ e - 1 ≠ 0 := by omega
  have hsucc : p ^ e - 1 + 1 = p ^ e := by omega
  symm
  rw [← hsucc]
  apply (Nat.log_eq_log_succ_iff hr.one_lt hpred).2
  intro hpow
  rw [hsucc] at hpow
  have hlog : r.log (p ^ e) ≠ 0 := by
    intro hz
    simp [hz] at hpow
    omega
  have hrdiv : r ∣ p ^ e := by
    rw [← hpow]
    exact dvd_pow_self r hlog
  exact hrp (Nat.prime_eq_prime_of_dvd_pow hr hp hrdiv)

/-- At a prime power `p ^ e`, the initial LCM acquires exactly one new factor
`p`. -/
theorem initialLcm_prime_pow {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    initialLcm (p ^ e) = p * initialLcm (p ^ e - 1) := by
  apply Nat.eq_of_factorization_eq
  · simp [initialLcm]
  · exact mul_ne_zero hp.ne_zero (by simp [initialLcm])
  · intro r
    by_cases hr : r.Prime
    · rw [show initialLcm (p ^ e) = Nat.lcmUpto (p ^ e) by rfl]
      rw [show initialLcm (p ^ e - 1) = Nat.lcmUpto (p ^ e - 1) by rfl]
      rw [Nat.factorization_lcmUpto (p ^ e) hr,
        Nat.factorization_mul hp.ne_zero (Nat.lcmUpto_ne_zero (p ^ e - 1))]
      simp only [Finsupp.add_apply]
      rw [Nat.factorization_lcmUpto (p ^ e - 1) hr]
      by_cases hrp : r = p
      · subst r
        rw [Nat.log_pow hp.one_lt, prime_log_pow_sub_one hp he]
        simp [hp]
        omega
      · rw [prime_log_pow_eq_log_pred_of_ne hp he hr hrp]
        simp [hp.factorization, hrp]
    · simp [Nat.factorization_eq_zero_of_not_prime, hr]

/-- Away from prime powers, adjoining the right endpoint does not change the
initial LCM. -/
theorem initialLcm_eq_pred_of_not_isPrimePow {q : ℕ} (hq : ¬ IsPrimePow q) :
    initialLcm q = initialLcm (q - 1) := by
  by_cases hq0 : q = 0
  · subst q
    simp [initialLcm]
  by_cases hq1 : q = 1
  · subst q
    simp [initialLcm]
  have hq2 : 2 ≤ q := by omega
  have hpred : q - 1 ≠ 0 := by omega
  have hsucc : q - 1 + 1 = q := by omega
  apply Nat.eq_of_factorization_eq
  · simp [initialLcm]
  · simp [initialLcm]
  · intro r
    by_cases hr : r.Prime
    · rw [show initialLcm q = Nat.lcmUpto q by rfl]
      rw [show initialLcm (q - 1) = Nat.lcmUpto (q - 1) by rfl]
      rw [Nat.factorization_lcmUpto q hr,
        Nat.factorization_lcmUpto (q - 1) hr]
      symm
      rw [← hsucc]
      apply (Nat.log_eq_log_succ_iff hr.one_lt hpred).2
      intro hpow
      rw [hsucc] at hpow
      have hlog : r.log q ≠ 0 := by
        intro hz
        simp [hz] at hpow
        omega
      apply hq
      rw [← hpow]
      exact hr.isPrimePow.pow hlog
    · simp [Nat.factorization_eq_zero_of_not_prime, hr]

/-- The LCM increment at `p ^ e` is equivalently a difference of two unit
fractions. -/
theorem prime_pow_cost_identity {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    (((p - 1 : ℕ) : ℚ) / initialLcm (p ^ e)) =
      (1 : ℚ) / initialLcm (p ^ e - 1) -
        (1 : ℚ) / initialLcm (p ^ e) := by
  rw [initialLcm_prime_pow hp he]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hL0 : (initialLcm (p ^ e - 1) : ℚ) ≠ 0 := by
    exact_mod_cast (show initialLcm (p ^ e - 1) ≠ 0 by simp [initialLcm])
  push_cast [Nat.cast_sub hp.one_le]
  field_simp

/-- The cost attached to a prime power.  It will only be summed at arguments
which satisfy `IsPrimePow`. -/
def primePowerCost (q : ℕ) : ℚ :=
  ((q.minFac - 1 : ℕ) : ℚ) / initialLcm q

/-- The accumulated cost of the prime powers at most `lo`. -/
def smallPrimePowerCost (lo : ℕ) : ℚ :=
  (primePowersUpTo lo).sum primePowerCost

lemma primePowerCost_eq_sub {q : ℕ} (hq : IsPrimePow q) :
    primePowerCost q =
      (1 : ℚ) / initialLcm (q - 1) - (1 : ℚ) / initialLcm q := by
  obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff _).mp hq
  simpa [primePowerCost, hp.pow_minFac he.ne'] using
    prime_pow_cost_identity hp he.ne'

private lemma primePowersUpTo_eq_insert_pred {q : ℕ} (hq : IsPrimePow q) :
    primePowersUpTo q = insert q (primePowersUpTo (q - 1)) := by
  have hqnot : q ∉ primePowersUpTo (q - 1) := by
    intro hmem
    have hle := (mem_primePowersUpTo.mp hmem).2
    have hqpos := hq.pos
    omega
  ext t
  simp only [mem_primePowersUpTo, Finset.mem_insert]
  constructor
  · rintro ⟨htpp, htq⟩
    by_cases ht : t = q
    · exact Or.inl ht
    · exact Or.inr ⟨htpp, by omega⟩
  · rintro (rfl | ⟨htpp, htq⟩)
    · exact ⟨hq, le_rfl⟩
    · exact ⟨htpp, htq.trans (Nat.sub_le q 1)⟩

private lemma primePowersUpTo_eq_pred {q : ℕ} (hq : ¬ IsPrimePow q) :
    primePowersUpTo q = primePowersUpTo (q - 1) := by
  ext t
  simp only [mem_primePowersUpTo]
  constructor
  · rintro ⟨htpp, htq⟩
    exact ⟨htpp, by
      by_cases ht : t = q
      · exact False.elim (hq (ht ▸ htpp))
      · omega⟩
  · rintro ⟨htpp, htq⟩
    exact ⟨htpp, htq.trans (Nat.sub_le q 1)⟩

/-- Exact telescope for all small-prime-power costs. -/
theorem smallPrimePowerCost_eq (lo : ℕ) :
    smallPrimePowerCost lo =
      1 - (1 : ℚ) / initialLcm lo := by
  induction lo with
  | zero => simp [smallPrimePowerCost, primePowersUpTo, initialLcm]
  | succ n ih =>
      by_cases hq : IsPrimePow (n + 1)
      · have hnot : n + 1 ∉ primePowersUpTo n := by
          rw [mem_primePowersUpTo]
          omega
        have hset : primePowersUpTo (n + 1) =
            insert (n + 1) (primePowersUpTo n) := by
          simpa only [Nat.add_sub_cancel] using primePowersUpTo_eq_insert_pred hq
        rw [smallPrimePowerCost, hset, Finset.sum_insert hnot]
        rw [← smallPrimePowerCost, ih, primePowerCost_eq_sub hq]
        simp only [Nat.add_sub_cancel]
        ring
      · have hset : primePowersUpTo (n + 1) = primePowersUpTo n := by
          simpa only [Nat.add_sub_cancel] using primePowersUpTo_eq_pred hq
        rw [smallPrimePowerCost, hset]
        rw [← smallPrimePowerCost, ih,
          initialLcm_eq_pred_of_not_isPrimePow hq]
        simp only [Nat.add_sub_cancel]

/-- The one-step form of the telescope, arranged for direct use in a strong
induction which descends from a prime power `q` to a value below `q`. -/
theorem primePowerCost_add_smallPrimePowerCost_pred {q : ℕ}
    (hq : IsPrimePow q) :
    primePowerCost q + smallPrimePowerCost (q - 1) =
      smallPrimePowerCost q := by
  rw [primePowerCost_eq_sub hq, smallPrimePowerCost_eq,
    smallPrimePowerCost_eq]
  ring

lemma primePowerCost_nonneg (q : ℕ) : 0 ≤ primePowerCost q := by
  rw [primePowerCost]
  exact div_nonneg (by positivity) (by positivity)

theorem smallPrimePowerCost_mono : Monotone smallPrimePowerCost := by
  intro x y hxy
  rw [smallPrimePowerCost, smallPrimePowerCost]
  exact Finset.sum_le_sum_of_subset_of_nonneg (primePowersUpTo_mono hxy)
    (fun q _ _ ↦ primePowerCost_nonneg q)

/-- Budget inequality for a strict descent `q' < q`. -/
theorem primePowerCost_add_smallPrimePowerCost_of_lt {q' q : ℕ}
    (hq' : q' < q) (hq : IsPrimePow q) :
    primePowerCost q + smallPrimePowerCost q' ≤
      smallPrimePowerCost q := by
  calc
    primePowerCost q + smallPrimePowerCost q' ≤
        primePowerCost q + smallPrimePowerCost (q - 1) := by
      have hmono : smallPrimePowerCost q' ≤ smallPrimePowerCost (q - 1) :=
        smallPrimePowerCost_mono (show q' ≤ q - 1 by omega)
      linarith
    _ = smallPrimePowerCost q :=
      primePowerCost_add_smallPrimePowerCost_pred hq

/-- The total small-prime-power cost is strictly less than one. -/
theorem smallPrimePowerCost_lt_one (lo : ℕ) :
    smallPrimePowerCost lo < 1 := by
  rw [smallPrimePowerCost_eq]
  have hLpos : (0 : ℚ) < initialLcm lo := by
    exact_mod_cast (Nat.pos_of_ne_zero (by simp [initialLcm] : initialLcm lo ≠ 0))
  have hinvpos : (0 : ℚ) < 1 / initialLcm lo := div_pos zero_lt_one hLpos
  linarith

end

end LcmTelescope

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Proposition7.lean` -/

section
/-!
# Martin's Proposition 7: descent and cardinality bookkeeping

This file contains the part of Proposition 7 which is independent of the
congruence calculations in Lemmas 15 and 16.  An `EliminationStep` records the
output of either lemma.  Its new rational has a strictly smaller largest exact
prime-power part, and every denominator introduced at the step is tagged by
the part which was eliminated.  Strong induction then proves termination,
pairwise distinctness of all denominators, and the bound `2 * piStar y` on the
number of terms.

The final section proves the finite-set bookkeeping for Martin's telescoping
padding operation.  Replacing the largest denominator `n` by `m + 1` larger
denominators increases the cardinality by exactly `m`, preserves the reciprocal
sum, and gives an explicit square bound for every new denominator.
-/

namespace Proposition7

open Finset
open scoped BigOperators

noncomputable section

open PrimePowers

lemma initialLcm_mono {x y : ℕ} (hxy : x ≤ y) :
    initialLcm x ≤ initialLcm y := by
  have hdiv : initialLcm x ∣ initialLcm y := by
    apply Finset.lcm_dvd
    intro n hn
    exact Finset.dvd_lcm (s := Icc 1 y) (f := id)
      (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hxy⟩)
  have hpos : 0 < initialLcm y := Nat.pos_of_ne_zero (by simp [initialLcm])
  exact Nat.le_of_dvd hpos hdiv

/-! ## Strict growth of the prime-power counting function -/

/-- Passing a prime-power endpoint strictly increases `piStar`. -/
lemma piStar_lt_of_lt_of_isPrimePow {x q : ℕ} (hxq : x < q)
    (hq : IsPrimePow q) : piStar x < piStar q := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨primePowersUpTo_mono hxq.le, ?_⟩
  intro heq
  have hqmem : q ∈ primePowersUpTo q := mem_primePowersUpTo.mpr ⟨hq, le_rfl⟩
  have : q ∈ primePowersUpTo x := heq.symm ▸ hqmem
  exact (not_le_of_gt hxq) (mem_primePowersUpTo.mp this).2

lemma piStar_eq_succ_pred_of_isPrimePow {q : ℕ} (hq : IsPrimePow q) :
    piStar q = piStar (q - 1) + 1 := by
  have hqpos : 0 < q := hq.pos
  have hqnot : q ∉ primePowersUpTo (q - 1) := by
    intro hmem
    have hle := (mem_primePowersUpTo.mp hmem).2
    omega
  have heq : primePowersUpTo q = insert q (primePowersUpTo (q - 1)) := by
    ext t
    rw [mem_primePowersUpTo]
    simp only [Finset.mem_insert, mem_primePowersUpTo]
    constructor
    · rintro ⟨htpp, htq⟩
      by_cases ht : t = q
      · exact Or.inl ht
      · exact Or.inr ⟨htpp, by omega⟩
    · rintro (rfl | ⟨htpp, htq⟩)
      · exact ⟨hq, le_rfl⟩
      · exact ⟨htpp, htq.trans (Nat.sub_le q 1)⟩
  rw [piStar, piStar, heq, Finset.card_insert_of_notMem hqnot]

lemma piStar_eq_pred_of_not_isPrimePow {q : ℕ} (hq : ¬ IsPrimePow q) :
    piStar q = piStar (q - 1) := by
  have heq : primePowersUpTo q = primePowersUpTo (q - 1) := by
    ext t
    rw [mem_primePowersUpTo, mem_primePowersUpTo]
    constructor
    · rintro ⟨htpp, htq⟩
      exact ⟨htpp, by
        by_cases ht : t = q
        · exact False.elim (hq (ht ▸ htpp))
        · have htpos := htpp.pos
          omega⟩
    · rintro ⟨htpp, htq⟩
      exact ⟨htpp, htq.trans (Nat.sub_le q 1)⟩
  change (primePowersUpTo q).card = (primePowersUpTo (q - 1)).card
  exact congrArg Finset.card heq

/-! ## A generic Lemma 15/16 step -/

/--
The common output needed from Martin's Lemmas 15 and 16 at a rational `r`.

The concrete lemmas additionally provide interval and exponential estimates.
Those estimates imply `le_bound`; the recursion itself needs only the fields
below.  `tagged` is what makes denominators introduced at different stages
automatically distinct.
-/
structure EliminationStep (B : ℕ) (r : ℚ) (U : Finset ℕ) : Prop where
  card_le_two : U.card ≤ 2
  zero_not_mem : 0 ∉ U
  le_bound : ∀ n ∈ U, n ≤ B
  tagged : ∀ n ∈ U,
    largestPrimePowerPart n = largestPrimePowerPart r.den
  descends :
    largestPrimePowerPart (r - UnitFractions.rec_sum U).den <
      largestPrimePowerPart r.den

/-- A Lemma 16 step together with its exact share of the telescoping
reciprocal budget. -/
structure SmallEliminationStep (B : ℕ) (r : ℚ) (U : Finset ℕ) : Prop
    extends EliminationStep B r U where
  card_le_one : U.card ≤ 1
  rec_sum_le_cost : UnitFractions.rec_sum U ≤
    LcmTelescope.primePowerCost (largestPrimePowerPart r.den)

theorem exists_smallEliminationStep_of_lemma16
    (B lo : ℕ) (hL : initialLcm lo ≤ B)
    (r : ℚ) (hden : r.den ≠ 1)
    (hrlo : largestPrimePowerPart r.den ≤ lo) :
    ∃ U : Finset ℕ, SmallEliminationStep B r U := by
  have hden2 : 2 ≤ r.den := by
    have := r.den_pos
    omega
  let q := largestPrimePowerPart r.den
  have hqpp : IsPrimePow q := (largestPrimePowerPart_spec hden2).1
  obtain ⟨p, e, hp, he, hqpow⟩ := (isPrimePow_nat_iff q).mp hqpp
  obtain ⟨a, n, haPos, haLe, hpa, haL, hnEq, hnLower, hqN, hqNpart,
      hnSmooth, hnLargest, hdesc⟩ :=
    Lemma16.smallPrimePower_elimination (p := p) (e := e) (q := q)
      r hp he hqpow.symm rfl
  have hLpos : 0 < initialLcm q :=
    Nat.pos_of_ne_zero (by simp [initialLcm])
  have hnPos : 0 < n := by
    rw [hnEq]
    exact Nat.div_pos (Nat.le_of_dvd hLpos haL) haPos
  have hnLeLq : n ≤ initialLcm q := by
    rw [hnEq]
    exact Nat.div_le_self _ _
  have hnB : n ≤ B :=
    hnLeLq.trans ((initialLcm_mono hrlo).trans hL)
  have hunitEq : (1 : ℚ) / n = (a : ℚ) / initialLcm q := by
    rw [hnEq, Nat.cast_div_charZero haL]
    have haQ : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hLQ : (initialLcm q : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hLpos.ne'
    field_simp [haQ, hLQ]
  have hcost : (1 : ℚ) / n ≤ LcmTelescope.primePowerCost q := by
    have hmin : q.minFac = p := by
      rw [← hqpow, hp.pow_minFac he.ne']
    rw [hunitEq, LcmTelescope.primePowerCost, hmin]
    exact (div_le_div_iff_of_pos_right (by exact_mod_cast hLpos)).2
      (by exact_mod_cast haLe)
  refine ⟨{n}, ?_⟩
  refine
    { toEliminationStep :=
        { card_le_two := by simp
          zero_not_mem := by simpa using hnPos.ne
          le_bound := by
            intro m hm
            simp only [Finset.mem_singleton] at hm
            subst m
            exact hnB
          tagged := by
            intro m hm
            simp only [Finset.mem_singleton] at hm
            subst m
            exact hnLargest
          descends := by simpa [UnitFractions.rec_sum] using hdesc }
      card_le_one := by simp
      rec_sum_le_cost := by simpa [UnitFractions.rec_sum, q] using hcost }

/--
The result of running all elimination steps.  The final residual is an integer;
`tag_le` remembers enough information to prove disjointness at the preceding
recursive stage.
-/
structure EliminationResult (B : ℕ) (r : ℚ) (E : Finset ℕ) : Prop where
  zero_not_mem : 0 ∉ E
  le_bound : ∀ n ∈ E, n ≤ B
  card_le : E.card ≤ 2 * piStar (largestPrimePowerPart r.den)
  tag_le : ∀ n ∈ E,
    largestPrimePowerPart n ≤ largestPrimePowerPart r.den
  residual_isInt : ∃ z : ℤ, r - UnitFractions.rec_sum E = z

/-- The Lemma 16 descent with the reciprocal cost retained.  Since Lemma 16
adds one denominator at each visited prime power, its cost is bounded by the
exact LCM telescope below the initial largest part. -/
structure SmallEliminationResult (B : ℕ) (r : ℚ) (E : Finset ℕ) : Prop where
  zero_not_mem : 0 ∉ E
  le_bound : ∀ n ∈ E, n ≤ B
  card_le : E.card ≤ piStar (largestPrimePowerPart r.den)
  tag_le : ∀ n ∈ E,
    largestPrimePowerPart n ≤ largestPrimePowerPart r.den
  residual_isInt : ∃ z : ℤ, r - UnitFractions.rec_sum E = z
  rec_sum_le_cost : UnitFractions.rec_sum E ≤
    LcmTelescope.smallPrimePowerCost (largestPrimePowerPart r.den)

/-- Complete current-factor Lemma 16 descent, including Martin's telescoping
budget. -/
theorem exists_smallEliminationResult_of_lemma16
    (B lo : ℕ) (hL : initialLcm lo ≤ B)
    (r : ℚ) (hrlo : largestPrimePowerPart r.den ≤ lo) :
    ∃ E : Finset ℕ, SmallEliminationResult B r E := by
  suffices hmain : ∀ q : ℕ, ∀ s : ℚ,
      largestPrimePowerPart s.den = q → q ≤ lo →
        ∃ E : Finset ℕ, SmallEliminationResult B s E by
    exact hmain (largestPrimePowerPart r.den) r rfl hrlo
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro s hqeq hqlo
      by_cases hden : s.den = 1
      · refine ⟨∅, ?_⟩
        refine
          { zero_not_mem := by simp
            le_bound := by simp
            card_le := by simp
            tag_le := by simp
            residual_isInt := ?_
            rec_sum_le_cost := ?_ }
        · simpa using isInt_of_primePowerParts_empty
            ((den_eq_one_iff_primePowerParts_empty s).mp hden)
        · simp only [UnitFractions.rec_sum, Finset.sum_empty]
          rw [LcmTelescope.smallPrimePowerCost]
          exact Finset.sum_nonneg fun t _ ↦
            LcmTelescope.primePowerCost_nonneg t
      · obtain ⟨U, hU⟩ :=
          exists_smallEliminationStep_of_lemma16 B lo hL s hden
            (hqeq.trans_le hqlo)
        let s' : ℚ := s - UnitFractions.rec_sum U
        have hdesc : largestPrimePowerPart s'.den < q := by
          simpa [s', hqeq] using hU.descends
        obtain ⟨E, hE⟩ := ih (largestPrimePowerPart s'.den) hdesc s' rfl
          (hdesc.le.trans hqlo)
        have hden2 : 2 ≤ s.den := by
          have := s.den_pos
          omega
        have hqpp : IsPrimePow q := by
          rw [← hqeq]
          exact (largestPrimePowerPart_spec hden2).1
        have hpi : piStar (largestPrimePowerPart s'.den) < piStar q :=
          piStar_lt_of_lt_of_isPrimePow hdesc hqpp
        have hdisjoint : Disjoint U E := by
          rw [Finset.disjoint_left]
          intro n hnU hnE
          have htagU : largestPrimePowerPart n = q := by
            simpa [hqeq] using hU.tagged n hnU
          have htagE := hE.tag_le n hnE
          omega
        refine ⟨U ∪ E, ?_⟩
        refine
          { zero_not_mem := ?_
            le_bound := ?_
            card_le := ?_
            tag_le := ?_
            residual_isInt := ?_
            rec_sum_le_cost := ?_ }
        · simpa only [Finset.mem_union, not_or] using
            ⟨hU.zero_not_mem, hE.zero_not_mem⟩
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · exact hU.le_bound n hnU
          · exact hE.le_bound n hnE
        · rw [Finset.card_union_of_disjoint hdisjoint]
          calc
            U.card + E.card ≤ 1 + piStar (largestPrimePowerPart s'.den) :=
              Nat.add_le_add hU.card_le_one hE.card_le
            _ ≤ piStar q := by omega
            _ = piStar (largestPrimePowerPart s.den) := by rw [hqeq]
        · intro n hn
          rcases Finset.mem_union.mp hn with hnU | hnE
          · rw [hU.tagged n hnU, hqeq]
          · exact (hE.tag_le n hnE).trans hdesc.le |>.trans_eq hqeq.symm
        · obtain ⟨z, hz⟩ := hE.residual_isInt
          refine ⟨z, ?_⟩
          rw [UnitFractions.rec_sum_disjoint hdisjoint]
          dsimp [s'] at hz
          linarith
        · rw [UnitFractions.rec_sum_disjoint hdisjoint]
          calc
            UnitFractions.rec_sum U + UnitFractions.rec_sum E ≤
                LcmTelescope.primePowerCost q +
                  LcmTelescope.smallPrimePowerCost
                    (largestPrimePowerPart s'.den) := by
              exact add_le_add (by simpa [hqeq] using hU.rec_sum_le_cost)
                hE.rec_sum_le_cost
            _ ≤ LcmTelescope.smallPrimePowerCost q :=
              LcmTelescope.primePowerCost_add_smallPrimePowerCost_of_lt
                hdesc hqpp
            _ = LcmTelescope.smallPrimePowerCost
                (largestPrimePowerPart s.den) := by rw [hqeq]

/-- A rational integer of absolute value less than one is zero. -/
lemma eq_zero_of_isInt_of_abs_lt_one {r : ℚ} (hint : ∃ z : ℤ, r = z)
    (hr : |r| < 1) : r = 0 := by
  obtain ⟨z, rfl⟩ := hint
  have hz : |z| < 1 := by exact_mod_cast hr
  have hznonneg : 0 ≤ |z| := abs_nonneg z
  have habs : |z| = 0 := by omega
  simp only [abs_eq_zero] at habs
  simp [habs]

/-- The terminal integer residual is zero as soon as the independent size
estimate places it in `(-1,1)`. -/
lemma EliminationResult.residual_eq_zero {B : ℕ} {r : ℚ} {E : Finset ℕ}
    (h : EliminationResult B r E)
    (hsmall : |r - UnitFractions.rec_sum E| < 1) :
    r - UnitFractions.rec_sum E = 0 :=
  eq_zero_of_isInt_of_abs_lt_one h.residual_isInt hsmall

/-! ## Scheduling Lemma 15 through all large prime powers -/

/-- The output of Lemma 15 when it is run at a scheduled prime power `q`.
Unlike `EliminationStep`, the scheduled `q` need not currently occur in the
reduced denominator. -/
structure ScheduledStep (r : ℚ) (q : ℕ) (U : Finset ℕ) : Prop where
  card_le_two : U.card ≤ 2
  card_eq_two_of_odd : Odd q → U.card = 2
  zero_not_mem : 0 ∉ U
  tagged : ∀ n ∈ U, largestPrimePowerPart n = q
  lower : ∀ n ∈ U, q ^ 2 ≤ 5 * n
  upper : ∀ n ∈ U, n ≤ q ^ 2
  descends :
    largestPrimePowerPart (r - UnitFractions.rec_sum U).den < q

/-- The total reciprocal majorant charged to the prime-power stages in
`(lo,q]`.  Each Lemma 15 stage costs at most `10/t^2`. -/
def largeSquareCost (lo q : ℕ) : ℝ :=
  ∑ t ∈ RoughCounts.largePrimePowers q lo, 10 / (t : ℝ) ^ 2

lemma largePrimePowers_succ_of_isPrimePow {lo q : ℕ} (hloq : lo < q)
    (hq : IsPrimePow q) :
    RoughCounts.largePrimePowers q lo =
      insert q (RoughCounts.largePrimePowers (q - 1) lo) := by
  ext t
  simp only [RoughCounts.largePrimePowers, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_insert]
  constructor
  · rintro ⟨⟨hlt, htle⟩, htpp⟩
    by_cases htq : t = q
    · exact Or.inl htq
    · exact Or.inr ⟨⟨hlt, by omega⟩, htpp⟩
  · rintro (rfl | ⟨⟨hlt, htle⟩, htpp⟩)
    · exact ⟨⟨by omega, le_rfl⟩, hq⟩
    · exact ⟨⟨hlt, htle.trans (Nat.sub_le q 1)⟩, htpp⟩

lemma largePrimePowers_pred_of_not_isPrimePow {lo q : ℕ}
    (hq : ¬ IsPrimePow q) :
    RoughCounts.largePrimePowers q lo =
      RoughCounts.largePrimePowers (q - 1) lo := by
  ext t
  simp only [RoughCounts.largePrimePowers, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hlt, htle⟩, htpp⟩
    exact ⟨⟨hlt, by
      by_cases htq : t = q
      · exact False.elim (hq (htq ▸ htpp))
      · omega⟩, htpp⟩
  · rintro ⟨⟨hlt, htle⟩, htpp⟩
    exact ⟨⟨hlt, htle.trans (Nat.sub_le q 1)⟩, htpp⟩

lemma largeSquareCost_succ_of_isPrimePow {lo q : ℕ} (hloq : lo < q)
    (hq : IsPrimePow q) :
    largeSquareCost lo q = largeSquareCost lo (q - 1) + 10 / (q : ℝ) ^ 2 := by
  rw [largeSquareCost, largeSquareCost,
    largePrimePowers_succ_of_isPrimePow hloq hq]
  have hnot : q ∉ RoughCounts.largePrimePowers (q - 1) lo := by
    rw [RoughCounts.largePrimePowers, Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [Finset.sum_insert hnot]
  ring

lemma largeSquareCost_pred_of_not_isPrimePow {lo q : ℕ}
    (hq : ¬ IsPrimePow q) :
    largeSquareCost lo q = largeSquareCost lo (q - 1) := by
  simp only [largeSquareCost,
    largePrimePowers_pred_of_not_isPrimePow hq]

lemma ScheduledStep.rec_sum_le_cost {r : ℚ} {q : ℕ} {U : Finset ℕ}
    (hq : IsPrimePow q) (h : ScheduledStep r q U) :
    (UnitFractions.rec_sum U : ℝ) ≤ 10 / (q : ℝ) ^ 2 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hterm : ∀ n ∈ U, (1 : ℝ) / n ≤ 5 / (q : ℝ) ^ 2 := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (Nat.pos_of_ne_zero (fun hn0 ↦ h.zero_not_mem (hn0 ▸ hn)))
    rw [div_le_div_iff₀ hnpos (sq_pos_of_pos hqpos)]
    norm_num
    exact_mod_cast h.lower n hn
  rw [UnitFractions.rec_sum]
  push_cast
  calc
    (∑ n ∈ U, (1 : ℝ) / n) ≤ U.card * (5 / (q : ℝ) ^ 2) := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul U (fun n ↦ (1 : ℝ) / n)
        (5 / (q : ℝ) ^ 2) hterm
    _ ≤ 2 * (5 / (q : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h.card_le_two)
        (div_nonneg (by positivity) (sq_nonneg _))
    _ = 10 / (q : ℝ) ^ 2 := by ring

/-- The concrete scheduled step supplied by Martin's Lemma 15. -/
theorem exists_scheduledStep_of_lemma15
    (q : ℕ) (hqpp : IsPrimePow q) (hq4 : 4 ≤ q)
    (r : ℚ) (hr : largestPrimePowerPart r.den ≤ q) :
    ∃ U : Finset ℕ, ScheduledStep r q U := by
  obtain ⟨U, hinterval, hodd, heven, htag, hdesc⟩ :=
    MartinCorrection.exists_elimination_set q hqpp hq4 r hr
  have hcard : U.card ≤ 2 := by
    rcases Nat.even_or_odd q with hqeven | hqodd
    · exact (heven hqeven).trans (by omega)
    · rw [hodd hqodd]
  have hzero : 0 ∉ U := by
    intro h0
    have hlower := (hinterval 0 h0).1
    have hqpos := hqpp.pos
    norm_num at hlower
    omega
  exact ⟨U,
    { card_le_two := hcard
      card_eq_two_of_odd := hodd
      zero_not_mem := hzero
      tagged := htag
      lower := fun n hn ↦ (hinterval n hn).1
      upper := fun n hn ↦ (hinterval n hn).2
      descends := hdesc }⟩

/-- The result of processing every prime power in `(lo,q]`, in decreasing
order. -/
structure ScheduledResult (lo q : ℕ) (r : ℚ)
    (E : Finset ℕ) (s : ℚ) : Prop where
  zero_not_mem : 0 ∉ E
  card_le : E.card ≤ 2 * (piStar q - piStar lo)
  tag_range : ∀ n ∈ E,
    lo < largestPrimePowerPart n ∧ largestPrimePowerPart n ≤ q
  denominator_range : ∀ n ∈ E,
    largestPrimePowerPart n ^ 2 ≤ 5 * n ∧
      n ≤ largestPrimePowerPart n ^ 2
  residual_eq : s = r - UnitFractions.rec_sum E
  residual_smooth : largestPrimePowerPart s.den ≤ lo
  rec_sum_le_cost : (UnitFractions.rec_sum E : ℝ) ≤ largeSquareCost lo q
  odd_stage : ∀ t, lo < t → t ≤ q → IsPrimePow t → Odd t →
    ∃ U ⊆ E, U.card = 2 ∧
      ∀ n ∈ U, largestPrimePowerPart n = t

/--
Run Lemma 15 at every large prime power, including prime powers which do not
occur in the current reduced denominator.  This is the source-faithful
schedule responsible for the eventual near-exact term count.
-/
theorem exists_scheduledResult
    (lo : ℕ) (hlo : 1 ≤ lo)
    (step : ∀ q : ℕ, ∀ r : ℚ, lo < q → IsPrimePow q →
      largestPrimePowerPart r.den ≤ q →
        ∃ U : Finset ℕ, ScheduledStep r q U)
    (q : ℕ) (r : ℚ) (hrq : largestPrimePowerPart r.den ≤ q) :
    ∃ E : Finset ℕ, ∃ s : ℚ, ScheduledResult lo q r E s := by
  induction q using Nat.strong_induction_on generalizing r with
  | h q ih =>
      by_cases hqlo : q ≤ lo
      · refine ⟨∅, r, ?_⟩
        refine
          { zero_not_mem := by simp
            card_le := by
              simp only [Finset.card_empty, zero_le]
            tag_range := by simp
            denominator_range := by simp
            residual_eq := by simp
            residual_smooth := hrq.trans hqlo
            rec_sum_le_cost := by
              simp only [UnitFractions.rec_sum, Finset.sum_empty, Rat.cast_zero]
              exact Finset.sum_nonneg fun _ _ ↦
                div_nonneg (by positivity) (sq_nonneg _)
            odd_stage := ?_ }
        intro t hlot htq
        omega
      · have hloq : lo < q := Nat.lt_of_not_ge hqlo
        by_cases hqpp : IsPrimePow q
        · obtain ⟨U, hU⟩ := step q r hloq hqpp hrq
          let r' : ℚ := r - UnitFractions.rec_sum U
          have hdesc : largestPrimePowerPart r'.den < q := by
            simpa [r'] using hU.descends
          obtain ⟨E, s, hE⟩ := ih (q - 1) (by omega) r' (by omega)
          have hdisjoint : Disjoint U E := by
            rw [Finset.disjoint_left]
            intro n hnU hnE
            have htagU := hU.tagged n hnU
            have htagE := (hE.tag_range n hnE).2
            omega
          refine ⟨U ∪ E, s, ?_⟩
          refine
            { zero_not_mem := ?_
              card_le := ?_
              tag_range := ?_
              denominator_range := ?_
              residual_eq := ?_
              residual_smooth := hE.residual_smooth
              rec_sum_le_cost := ?_
              odd_stage := ?_ }
          · simpa only [Finset.mem_union, not_or] using
              ⟨hU.zero_not_mem, hE.zero_not_mem⟩
          · rw [Finset.card_union_of_disjoint hdisjoint]
            calc
              U.card + E.card ≤ 2 + 2 * (piStar (q - 1) - piStar lo) :=
                Nat.add_le_add hU.card_le_two hE.card_le
              _ = 2 * (piStar q - piStar lo) := by
                have hloPred : lo ≤ q - 1 := by omega
                have hpiLo : piStar lo ≤ piStar (q - 1) := piStar_mono hloPred
                rw [piStar_eq_succ_pred_of_isPrimePow hqpp]
                omega
          · intro n hn
            rcases Finset.mem_union.mp hn with hnU | hnE
            · rw [hU.tagged n hnU]
              exact ⟨hloq, le_rfl⟩
            · have hnrange := hE.tag_range n hnE
              exact ⟨hnrange.1, hnrange.2.trans (Nat.sub_le q 1)⟩
          · intro n hn
            rcases Finset.mem_union.mp hn with hnU | hnE
            · rw [hU.tagged n hnU]
              exact ⟨hU.lower n hnU, hU.upper n hnU⟩
            · exact hE.denominator_range n hnE
          · rw [hE.residual_eq, UnitFractions.rec_sum_disjoint hdisjoint]
            dsimp [r']
            ring
          · rw [UnitFractions.rec_sum_disjoint hdisjoint, Rat.cast_add,
              largeSquareCost_succ_of_isPrimePow hloq hqpp]
            nlinarith [hU.rec_sum_le_cost hqpp, hE.rec_sum_le_cost]
          · intro t hlot htq htpp htodd
            rcases lt_or_eq_of_le htq with htlt | rfl
            · obtain ⟨V, hVE, hVcard, hVtag⟩ :=
                hE.odd_stage t hlot (by omega) htpp htodd
              exact ⟨V, hVE.trans subset_union_right, hVcard, hVtag⟩
            · exact ⟨U, subset_union_left, hU.card_eq_two_of_odd htodd, hU.tagged⟩
        · have hnext : largestPrimePowerPart r.den ≤ q - 1 := by
            by_contra hnot
            have heq : largestPrimePowerPart r.den = q := by omega
            have hden2 : 2 ≤ r.den := by
              have hpartle := largestPrimePowerPart_le (n := r.den)
              omega
            exact hqpp (heq ▸ (largestPrimePowerPart_spec hden2).1)
          obtain ⟨E, s, hE⟩ := ih (q - 1) (by omega) r hnext
          refine ⟨E, s, ?_⟩
          refine
            { zero_not_mem := hE.zero_not_mem
              card_le := ?_
              tag_range := ?_
              denominator_range := hE.denominator_range
              residual_eq := hE.residual_eq
              residual_smooth := hE.residual_smooth
              rec_sum_le_cost := by
                simpa [largeSquareCost_pred_of_not_isPrimePow hqpp] using
                  hE.rec_sum_le_cost
              odd_stage := ?_ }
          · simpa [piStar_eq_pred_of_not_isPrimePow hqpp] using hE.card_le
          · intro n hn
            have hnrange := hE.tag_range n hn
            exact ⟨hnrange.1, hnrange.2.trans (Nat.sub_le q 1)⟩
          · intro t hlot htq htpp htodd
            have htlt : t < q := lt_of_le_of_ne htq (fun heq ↦ hqpp (heq ▸ htpp))
            exact hE.odd_stage t hlot (by omega) htpp htodd

/-! ## Mixed Lemma 15 / Lemma 16 recursion -/

/-- The complete preliminary correction before the final cardinality padding
step. -/
structure PreliminaryResult (B lo y : ℕ) (r : ℚ) (E : Finset ℕ) : Prop where
  zero_not_mem : 0 ∉ E
  le_bound : ∀ n ∈ E, n ≤ B
  card_le : E.card ≤ 2 * piStar y
  tag_le : ∀ n ∈ E, largestPrimePowerPart n ≤ y
  residual_isInt : ∃ z : ℤ, r - UnitFractions.rec_sum E = z
  odd_large_stage : ∀ t, lo < t → t ≤ y → IsPrimePow t → Odd t →
    ∃ U ⊆ E, U.card = 2 ∧
      (∀ n ∈ U, largestPrimePowerPart n = t) ∧
      ∀ n ∈ U, t ^ 2 ≤ 5 * n

lemma PreliminaryResult.residual_eq_zero {B lo y : ℕ} {r : ℚ}
    {E : Finset ℕ} (h : PreliminaryResult B lo y r E)
    (hsmall : |r - UnitFractions.rec_sum E| < 1) :
    r - UnitFractions.rec_sum E = 0 :=
  eq_zero_of_isInt_of_abs_lt_one h.residual_isInt hsmall

/-- A preliminary correction carrying the quantitative estimate needed to
show that its terminal integer is zero. -/
structure BudgetedPreliminaryResult (lo y : ℕ) (r : ℚ)
    (E : Finset ℕ) : Prop extends PreliminaryResult (y ^ 2) lo y r E where
  rec_sum_lt : (UnitFractions.rec_sum E : ℝ) < 1 + largeSquareCost lo y

/-- Lemmas 15 and 16, combined with the exact small-prime-power telescope. -/
theorem exists_budgetedPreliminaryResult_of_lemmas
    (lo y : ℕ) (hlo : 3 ≤ lo) (hloy : lo ≤ y)
    (hL : initialLcm lo ≤ y ^ 2)
    (r : ℚ) (hry : largestPrimePowerPart r.den ≤ y) :
    ∃ E : Finset ℕ, BudgetedPreliminaryResult lo y r E := by
  obtain ⟨A, s, hA⟩ := exists_scheduledResult lo (by omega)
    (fun q t hloq hqpp ht ↦
      exists_scheduledStep_of_lemma15 q hqpp (by omega) t ht)
    y r hry
  obtain ⟨C, hC⟩ :=
    exists_smallEliminationResult_of_lemma16 (y ^ 2) lo hL s
      hA.residual_smooth
  have hdisjoint : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro n hnA hnC
    have hnAlo := (hA.tag_range n hnA).1
    have hnCle := (hC.tag_le n hnC).trans hA.residual_smooth
    omega
  refine ⟨A ∪ C, ?_⟩
  refine
    { toPreliminaryResult :=
        { zero_not_mem := by
            simpa only [Finset.mem_union, not_or] using
              ⟨hA.zero_not_mem, hC.zero_not_mem⟩
          le_bound := ?_
          card_le := ?_
          tag_le := ?_
          residual_isInt := ?_
          odd_large_stage := ?_ }
      rec_sum_lt := ?_ }
  · intro n hn
    rcases Finset.mem_union.mp hn with hnA | hnC
    · exact (hA.denominator_range n hnA).2.trans
        (Nat.pow_le_pow_left (hA.tag_range n hnA).2 2)
    · exact hC.le_bound n hnC
  · rw [Finset.card_union_of_disjoint hdisjoint]
    calc
      A.card + C.card ≤
          2 * (piStar y - piStar lo) +
            piStar (largestPrimePowerPart s.den) :=
        Nat.add_le_add hA.card_le hC.card_le
      _ ≤ 2 * (piStar y - piStar lo) + piStar lo := by
        exact Nat.add_le_add_left (piStar_mono hA.residual_smooth) _
      _ ≤ 2 * (piStar y - piStar lo) + 2 * piStar lo := by omega
      _ = 2 * piStar y := by
        have hpile : piStar lo ≤ piStar y := piStar_mono hloy
        omega
  · intro n hn
    rcases Finset.mem_union.mp hn with hnA | hnC
    · exact (hA.tag_range n hnA).2
    · exact (hC.tag_le n hnC).trans hA.residual_smooth |>.trans hloy
  · obtain ⟨z, hz⟩ := hC.residual_isInt
    refine ⟨z, ?_⟩
    rw [UnitFractions.rec_sum_disjoint hdisjoint]
    linarith [hA.residual_eq]
  · intro t hlot hty htpp htodd
    obtain ⟨U, hUA, hUcard, hUtag⟩ :=
      hA.odd_stage t hlot hty htpp htodd
    refine ⟨U, hUA.trans subset_union_left, hUcard, hUtag, ?_⟩
    intro n hn
    have hden := hA.denominator_range n (hUA hn)
    simpa [hUtag n hn] using hden.1
  · have hCltQ : UnitFractions.rec_sum C < 1 :=
      hC.rec_sum_le_cost.trans_lt
        (LcmTelescope.smallPrimePowerCost_lt_one _)
    have hClt : (UnitFractions.rec_sum C : ℝ) < 1 := by
      exact_mod_cast hCltQ
    rw [UnitFractions.rec_sum_disjoint hdisjoint, Rat.cast_add]
    linarith [hA.rec_sum_le_cost]

/-! ## Telescoping padding -/

/-- The denominators in the telescoping replacement of `1/n`. -/
def paddingTerms (n m : ℕ) : Finset ℕ :=
  {n + m} ∪ (Finset.range m).image (fun j ↦ (n + j) * (n + j + 1))

lemma paddingProduct_strictMono (n : ℕ) (hn : 0 < n) :
    StrictMono (fun j : ℕ ↦ (n + j) * (n + j + 1)) := by
  intro a b hab
  nlinarith [Nat.add_pos_left hn a, Nat.add_pos_left hn b]

lemma paddingTerms_product_gt {n m j : ℕ} (hn : 0 < n) (_hj : j < m) :
    n < (n + j) * (n + j + 1) := by
  nlinarith [Nat.add_pos_left hn j]

lemma paddingTerms_product_le {n m j : ℕ} (hj : j < m) :
    (n + j) * (n + j + 1) ≤ (n + m) ^ 2 := by
  have h1 : n + j + 1 ≤ n + m := by omega
  have h2 : n + j ≤ n + m := by omega
  nlinarith

/-- The telescoping replacement has exactly `m + 1` distinct denominators.
The condition `m < n` prevents the linear denominator `n+m` from colliding
with a quadratic denominator. -/
lemma card_paddingTerms (n m : ℕ) (hn : 0 < n) (hm : m < n) :
    (paddingTerms n m).card = m + 1 := by
  have hinj : Set.InjOn (fun j : ℕ ↦ (n + j) * (n + j + 1)) (Finset.range m) :=
    (paddingProduct_strictMono n hn).injective.injOn
  have hcardImage : ((Finset.range m).image
      (fun j ↦ (n + j) * (n + j + 1))).card = m := by
    rw [Finset.card_image_iff.mpr hinj]
    simp
  have hnotmem : n + m ∉ (Finset.range m).image
      (fun j ↦ (n + j) * (n + j + 1)) := by
    intro hmem
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hmem
    have hjm : j < m := Finset.mem_range.mp hj
    have hquad : 2 * n ≤ (n + j) * (n + j + 1) := by
      nlinarith [Nat.add_pos_left hn j]
    have hlin : n + m < 2 * n := by omega
    omega
  rw [paddingTerms, Finset.card_union_of_disjoint]
  · simp [hcardImage, Nat.add_comm]
  · simpa [Finset.disjoint_left] using hnotmem

lemma zero_not_mem_paddingTerms {n m : ℕ} (hn : 0 < n) :
    0 ∉ paddingTerms n m := by
  rw [paddingTerms, Finset.mem_union, not_or]
  refine ⟨?_, ?_⟩
  · intro h
    simp only [Finset.mem_singleton] at h
    omega
  simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
  intro j hj
  exact Nat.ne_of_gt (Nat.mul_pos (Nat.add_pos_left hn j) (by omega))

lemma mem_paddingTerms_le_square {n m a : ℕ} (ha : a ∈ paddingTerms n m) :
    a ≤ (n + m) ^ 2 := by
  rcases Finset.mem_union.mp ha with ha | ha
  · simp only [Finset.mem_singleton] at ha
    subst a
    nlinarith
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact paddingTerms_product_le (Finset.mem_range.mp hj)

lemma paddingTerms_above {n m a : ℕ} (hn : 0 < n) (hm : 0 < m)
    (ha : a ∈ paddingTerms n m) : n < a := by
  rcases Finset.mem_union.mp ha with ha | ha
  · have heq : a = n + m := Finset.mem_singleton.mp ha
    omega
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact paddingTerms_product_gt hn (Finset.mem_range.mp hj)

/-- The reciprocal sum of all padding terms is exactly the original unit
fraction. -/
lemma rec_sum_paddingTerms (n m : ℕ) (hn : 0 < n) (hm : m < n) :
    UnitFractions.rec_sum (paddingTerms n m) = (1 : ℚ) / n := by
  have hdisj : Disjoint ({n + m} : Finset ℕ)
      ((Finset.range m).image (fun j ↦ (n + j) * (n + j + 1))) := by
    rw [Finset.disjoint_left]
    intro a ha haImage
    simp only [Finset.mem_singleton] at ha
    subst a
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp haImage
    have hjm : j < m := Finset.mem_range.mp hj
    have hquad : 2 * n ≤ (n + j) * (n + j + 1) := by
      nlinarith [Nat.add_pos_left hn j]
    have hlin : n + m < 2 * n := by omega
    omega
  rw [paddingTerms, UnitFractions.rec_sum_disjoint hdisj]
  simp only [UnitFractions.rec_sum, Finset.sum_singleton]
  have himage :
      ∑ a ∈ (Finset.range m).image (fun j ↦ (n + j) * (n + j + 1)),
          (1 : ℚ) / a =
        ∑ j ∈ Finset.range m, (1 : ℚ) / ((n + j) * (n + j + 1) : ℕ) := by
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact (paddingProduct_strictMono n hn).injective hab
  rw [himage]
  exact (ExactCorrection.unitFraction_telescoping n m hn).symm

/-- Replace the largest member of `A` by the telescoping padding set. -/
def padAt (A : Finset ℕ) (n m : ℕ) : Finset ℕ :=
  A.erase n ∪ paddingTerms n m

/--
Source-faithful exact-cardinality padding interface.

If `n` is the largest denominator of a nonempty positive finite set and the
required deficit `m` is smaller than `n`, then `padAt A n m` has exactly
`A.card + m` members, has the same reciprocal sum, remains positive, and all
its denominators are at most `(n+m)^2`.
-/
theorem padAt_spec {A : Finset ℕ} {n m : ℕ}
    (hnA : n ∈ A) (hnmax : ∀ a ∈ A, a ≤ n)
    (hzero : 0 ∉ A) (hm : m < n) :
    (padAt A n m).card = A.card + m ∧
      UnitFractions.rec_sum (padAt A n m) = UnitFractions.rec_sum A ∧
      0 ∉ padAt A n m ∧
      ∀ a ∈ padAt A n m, a ≤ (n + m) ^ 2 := by
  have hn : 0 < n := by
    have : n ≠ 0 := by
      intro hn0
      exact hzero (hn0 ▸ hnA)
    omega
  have hdisj : Disjoint (A.erase n) (paddingTerms n m) := by
    rw [Finset.disjoint_left]
    intro a haA haP
    have han : a ≤ n := hnmax a (Finset.mem_of_mem_erase haA)
    rcases eq_or_lt_of_le (Nat.zero_le m) with hm0 | hmpos
    · subst m
      simp [paddingTerms] at haP
      subst a
      simp at haA
    · exact (not_lt_of_ge han) (paddingTerms_above hn hmpos haP)
  have hcardErase : (A.erase n).card = A.card - 1 := by
    rw [Finset.card_erase_of_mem hnA]
  have hsumErase : UnitFractions.rec_sum (A.erase n) + (1 : ℚ) / n =
      UnitFractions.rec_sum A := by
    simpa [UnitFractions.rec_sum] using
      (Finset.sum_erase_add (s := A) (f := fun a : ℕ ↦ (1 : ℚ) / a) hnA)
  have hcardPos : 0 < A.card := Finset.card_pos.mpr ⟨n, hnA⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [padAt, Finset.card_union_of_disjoint hdisj, hcardErase,
      card_paddingTerms n m hn hm]
    omega
  · rw [padAt, UnitFractions.rec_sum_disjoint hdisj,
      rec_sum_paddingTerms n m hn hm]
    exact hsumErase
  · rw [padAt, Finset.mem_union, not_or]
    exact ⟨fun h ↦ hzero (Finset.mem_of_mem_erase h), zero_not_mem_paddingTerms hn⟩
  · intro a ha
    rcases Finset.mem_union.mp ha with haA | haP
    · have han : a ≤ n := hnmax a (Finset.mem_of_mem_erase haA)
      calc
        a ≤ n := han
        _ ≤ (n + m) ^ 2 := by nlinarith
    · exact mem_paddingTerms_le_square haP

/-- Padding directly to a prescribed target cardinality. -/
theorem exists_padded_to_card {A : Finset ℕ} {n K : ℕ}
    (hnA : n ∈ A) (hnmax : ∀ a ∈ A, a ≤ n)
    (hzero : 0 ∉ A) (hcard : A.card ≤ K)
    (hdeficit : K - A.card < n) :
    ∃ E : Finset ℕ,
      E.card = K ∧
      UnitFractions.rec_sum E = UnitFractions.rec_sum A ∧
      0 ∉ E ∧
      ∀ a ∈ E, a ≤ (n + (K - A.card)) ^ 2 := by
  let m := K - A.card
  refine ⟨padAt A n m, ?_⟩
  obtain ⟨hcardPad, hsumPad, hzeroPad, hboundPad⟩ :=
    padAt_spec hnA hnmax hzero hdeficit
  refine ⟨?_, hsumPad, hzeroPad, hboundPad⟩
  dsimp [m] at hcardPad ⊢
  omega

/-! ## Final padding bound -/

/--
Turn a preliminary exact correction into the exact cardinality
`2 * piStar y`.  Bertrand's postulate supplies an odd prime in `(y/2,y]`;
the scheduled Lemma 15 stage at that prime provides a denominator large enough
to absorb the entire cardinality deficit.  The square estimate from
`padAt_spec` is then at most `2*y^4`.
-/
theorem exists_exactCard_of_preliminary
    {lo y : ℕ} {r : ℚ} {A : Finset ℕ}
    (hy : 40 ≤ y) (hlo : lo < y / 2)
    (hA : PreliminaryResult (y ^ 2) lo y r A)
    (hsmall : |r - UnitFractions.rec_sum A| < 1) :
    ∃ E : Finset ℕ,
      E.card = 2 * piStar y ∧
      UnitFractions.rec_sum E = r ∧
      0 ∉ E ∧
      ∀ n ∈ E, n ≤ 2 * y ^ 4 := by
  have hyhalf : y / 2 ≠ 0 := by omega
  obtain ⟨p, hp, hyhp, hpyle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (y / 2) hyhalf
  have hpy : p ≤ y := hpyle.trans (by omega)
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hpp : IsPrimePow p := ⟨p, 1, hp.prime, by omega, by simp⟩
  obtain ⟨U, hUA, hUcard, hUtag, hUlower⟩ :=
    hA.odd_large_stage p (hlo.trans hyhp) hpy hpp hpodd
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨n, hnU⟩ := hUne
  have hnA : n ∈ A := hUA hnU
  have hAne : A.Nonempty := ⟨n, hnA⟩
  let N : ℕ := A.max' hAne
  have hnN : n ≤ N := by
    exact Finset.le_max' A n hnA
  have hNmem : N ∈ A := Finset.max'_mem A hAne
  have hNmax : ∀ a ∈ A, a ≤ N := by
    intro a ha
    exact Finset.le_max' A a ha
  have hNupper : N ≤ y ^ 2 := hA.le_bound N hNmem
  let K : ℕ := 2 * piStar y
  let d : ℕ := K - A.card
  have hcardAK : A.card ≤ K := by
    simpa [K] using hA.card_le
  have hKle : K ≤ 2 * y := by
    dsimp [K]
    exact Nat.mul_le_mul_left 2 (piStar_le y)
  have hdle : d ≤ 2 * y := by
    exact (Nat.sub_le K A.card).trans hKle
  have hyhalfBound : y ≤ 2 * (y / 2) + 1 := by omega
  have hpSq : 10 * y < p ^ 2 := by
    nlinarith
  have hpn : p ^ 2 ≤ 5 * n := hUlower n hnU
  have hnlarge : 2 * y < n := by nlinarith
  have hdN : d < N := hdle.trans_lt (hnlarge.trans_le hnN)
  obtain ⟨E, hEcard, hEsum, hEzero, hEbound⟩ :=
    exists_padded_to_card hNmem hNmax hA.zero_not_mem hcardAK hdN
  have hAsum : UnitFractions.rec_sum A = r := by
    have hz := hA.residual_eq_zero hsmall
    linarith
  have hsumBound : N + d ≤ y ^ 2 + 2 * y := Nat.add_le_add hNupper hdle
  have hfour : 4 * (N + d) ≤ 5 * y ^ 2 := by
    nlinarith [show 8 * y ≤ y ^ 2 by nlinarith]
  have hsquare : (N + d) ^ 2 ≤ 2 * y ^ 4 := by
    nlinarith [sq_nonneg (4 * (N + d)), sq_nonneg (5 * y ^ 2)]
  refine ⟨E, ?_, ?_, hEzero, ?_⟩
  · simpa [K] using hEcard
  · exact hEsum.trans hAsum
  · intro a ha
    exact (hEbound a ha).trans (by simpa [N, d] using hsquare)

/-- Converting a Chebyshev bound at a cutoff into the concrete `y^2` LCM
bound required by the small-prime-power construction. -/
lemma initialLcm_le_sq_of_chebyshev {lo y : ℕ} (hy : 1 ≤ y)
    (hlo : (lo : ℝ) ≤ Real.log (y : ℝ))
    (hpsi : chebyshev_second (lo : ℝ) ≤ 2 * (lo : ℝ)) :
    initialLcm lo ≤ y ^ 2 := by
  have hLpos : (0 : ℝ) < initialLcm lo := by
    exact_mod_cast
      (Nat.pos_of_ne_zero (by simp [initialLcm] : initialLcm lo ≠ 0))
  have hypos : (0 : ℝ) < y := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hy)
  have hlogL : Real.log (initialLcm lo : ℝ) =
      chebyshev_second (lo : ℝ) := by
    change Real.log (Nat.lcmUpto lo : ℝ) = Chebyshev.psi (lo : ℝ)
    exact (Chebyshev.psi_eq_log_lcmUpto lo).symm
  have hlogle : Real.log (initialLcm lo : ℝ) ≤
      2 * Real.log (y : ℝ) := by
    rw [hlogL]
    linarith
  have hexp := Real.exp_le_exp.mpr hlogle
  rw [Real.exp_log hLpos] at hexp
  have hrhs : Real.exp (2 * Real.log (y : ℝ)) = (y : ℝ) ^ 2 := by
    rw [show 2 * Real.log (y : ℝ) =
      Real.log (y : ℝ) + Real.log (y : ℝ) by ring,
      Real.exp_add, Real.exp_log hypos]
    ring
  rw [hrhs] at hexp
  exact_mod_cast hexp

/-- A convenient elementary cutoff separation used by the eventual wrapper. -/
lemma log_lt_quarter_natCast (y : ℕ) (hy : 40 ≤ y) :
    Real.log (y : ℝ) < (y : ℝ) / 4 := by
  have hyR : (0 : ℝ) < y := by positivity
  have hdiv : 0 < (y : ℝ) / 8 := div_pos hyR (by norm_num)
  have hbase := Real.log_le_sub_one_of_pos hdiv
  have hlog2 : Real.log (2 : ℝ) < 1 := by
    nlinarith [Real.log_two_lt_d9]
  have hlog8 : Real.log (8 : ℝ) < 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    nlinarith
  have hdecomp : Real.log (y : ℝ) =
      Real.log 8 + Real.log ((y : ℝ) / 8) := by
    rw [Real.log_div hyR.ne' (by norm_num : (8 : ℝ) ≠ 0)]
    linarith
  rw [hdecomp]
  have hyR40 : (40 : ℝ) ≤ y := by exact_mod_cast hy
  nlinarith

lemma naturalLogCutoff_lt_half (y : ℕ) (hy : 40 ≤ y) :
    RoughCounts.naturalLogCutoff y < y / 2 := by
  have hy1 : 1 ≤ y := by omega
  have hlognonneg : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hy1)
  have hfloor : ((RoughCounts.naturalLogCutoff y : ℕ) : ℝ) ≤
      Real.log (y : ℝ) := Nat.floor_le hlognonneg
  have hlog := log_lt_quarter_natCast y hy
  have hnat : y < 4 * (y / 2) := by omega
  have hreal : (y : ℝ) < 4 * ((y / 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hquarter : (y : ℝ) / 4 < ((y / 2 : ℕ) : ℝ) := by
    nlinarith
  exact_mod_cast hfloor.trans_lt (hlog.trans hquarter)

/-- Finite, quantitative form of Martin's Proposition 7.  The positive
constant `c` is arbitrary; the source's `1/log y` is the case `c = 1`, while
the upper-bound assembly uses `c = 1/6` to absorb the fifth-root floor. -/
theorem proposition7_of_cutoff
    {c : ℝ} (_hc : 0 < c) {lo y : ℕ} {r : ℚ}
    (hy : 40 ≤ y) (hlo : 3 ≤ lo) (hloy : lo ≤ y)
    (hlohalf : lo < y / 2) (hL : initialLcm lo ≤ y ^ 2)
    (hry : largestPrimePowerPart r.den ≤ y)
    (hrLower : c / Real.log (y : ℝ) < (r : ℝ))
    (hrUpper : (r : ℝ) < 1)
    (htail : largeSquareCost lo y < c / Real.log (y : ℝ)) :
    ∃ E : Finset ℕ,
      E.card = 2 * piStar y ∧
      UnitFractions.rec_sum E = r ∧
      0 ∉ E ∧
      ∀ n ∈ E, n ≤ 2 * y ^ 4 := by
  obtain ⟨A, hA⟩ :=
    exists_budgetedPreliminaryResult_of_lemmas lo y hlo hloy hL r hry
  have hsumlt : (UnitFractions.rec_sum A : ℝ) < 1 + (r : ℝ) := by
    linarith [hA.rec_sum_lt]
  have hsum_nonnegQ : 0 ≤ UnitFractions.rec_sum A :=
    UnitFractions.rec_sum_nonneg
  have hsum_nonneg : (0 : ℝ) ≤ UnitFractions.rec_sum A := by
    exact_mod_cast hsum_nonnegQ
  have hresLower : (-1 : ℝ) < (r : ℝ) - UnitFractions.rec_sum A := by
    linarith
  have hresUpper : (r : ℝ) - UnitFractions.rec_sum A < 1 := by
    linarith
  have hsmallR : |(r : ℝ) - UnitFractions.rec_sum A| < 1 :=
    (abs_lt).2 ⟨hresLower, hresUpper⟩
  have hsmall : |r - UnitFractions.rec_sum A| < (1 : ℚ) := by
    exact_mod_cast hsmallR
  exact exists_exactCard_of_preliminary hy hlohalf hA.toPreliminaryResult hsmall

/-- At the natural logarithmic cutoff, the small denominators supplied by
Lemma 16 are eventually at most `y^2`. -/
lemma eventually_initialLcm_naturalLogCutoff_le_sq :
    ∀ᶠ y : ℕ in Filter.atTop,
      initialLcm (RoughCounts.naturalLogCutoff y) ≤ y ^ 2 := by
  have hc2 : 2 * Real.log 2 < (2 : ℝ) := by
    nlinarith [Real.log_two_lt_d9]
  have hpsiReal := (chebyshev_upper_explicit hc2).bound
  have hcutReal : Filter.Tendsto
      (fun y : ℕ ↦ (RoughCounts.naturalLogCutoff y : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp
      RoughCounts.naturalLogCutoff_tendsto_atTop
  have hpsi := hcutReal.eventually hpsiReal
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ), hpsi]
      with y hy hpsiY
  have hlognonneg : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hy)
  have hcutle : (RoughCounts.naturalLogCutoff y : ℝ) ≤
      Real.log (y : ℝ) := Nat.floor_le hlognonneg
  apply initialLcm_le_sq_of_chebyshev hy hcutle
  simpa [Real.norm_eq_abs,
    abs_of_nonneg (chebyshev_second_nonneg _)] using hpsiY

/-- Unconditional eventual form of Martin's Proposition 7.  All congruence,
descent, reciprocal-mass, and LCM estimates have been discharged; the only
remaining assumptions are the mathematical hypotheses on the input rational.
-/
theorem eventually_proposition7 {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℕ in Filter.atTop, ∀ r : ℚ,
      largestPrimePowerPart r.den ≤ y →
      c / Real.log (y : ℝ) < (r : ℝ) →
      (r : ℝ) < 1 →
      ∃ E : Finset ℕ,
        E.card = 2 * piStar y ∧
        UnitFractions.rec_sum E = r ∧
        0 ∉ E ∧
        ∀ n ∈ E, n ≤ 2 * y ^ 4 := by
  have htail :=
    RoughCounts.eventually_sum_ten_div_primePower_sq_lt_div_log hc
  have hcut3 := RoughCounts.naturalLogCutoff_tendsto_atTop.eventually
    (Filter.eventually_ge_atTop (3 : ℕ))
  filter_upwards [Filter.eventually_ge_atTop (40 : ℕ), htail, hcut3,
    eventually_initialLcm_naturalLogCutoff_le_sq]
      with y hy htailY hcut3Y hLY
  intro r hry hrLower hrUpper
  apply proposition7_of_cutoff hc hy hcut3Y
  · exact (naturalLogCutoff_lt_half y hy).le.trans (Nat.div_le_self y 2)
  · exact naturalLogCutoff_lt_half y hy
  · exact hLY
  · exact hry
  · exact hrLower
  · exact hrUpper
  · simpa [largeSquareCost] using htailY

end

end Proposition7

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/UpperAssembly.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős 285: Martin's upper-bound assembly

This file contains only the high-level bookkeeping in Proposition 4 of
Greg Martin's *Denser Egyptian fractions*.  The two difficult arithmetic
inputs are represented by explicit finite sets:

* `large` is the set supplied by the approximate-representation result
  (Proposition 6 in Martin's paper), and
* `correction` is the small-denominator set supplied by the exact-correction
  result (Proposition 7).

The theorem `propositionFour_upperAssembly` proves, rather than assumes, that
their union is disjoint, has the requested cardinality, has the exact
reciprocal sum, avoids zero, and has all denominators at most the chosen
cutoff.  `propositionFour_upperAssembly_eventually` is the filter-level form
used by an asymptotic proof.  The final two lemmas turn the quantitative
choice of the cutoff into convergence of its ratio to the number of terms.
-/

open Filter Finset
open scoped BigOperators Topology

/-- The real reciprocal sum of a finite set of natural denominators. -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, (1 : ℝ) / n

/-- Martin's `π⁺(y)`: the number of prime powers not exceeding `y`. -/
def primePowerCount (y : ℕ) : ℕ :=
  ((Finset.Icc 1 y).filter IsPrimePow).card

/-- Proposition 7 contributes exactly twice `π⁺(y)` denominators. -/
def correctionCount (y : ℕ) : ℕ :=
  2 * primePowerCount y

/-- The number `R = t - 2π⁺(y)` requested from Proposition 6. -/
def mainCount (t y : ℕ) : ℕ :=
  t - correctionCount y

/-- The upper bound `2 y⁴` for the denominators in Proposition 7. -/
def correctionCutoff (y : ℕ) : ℕ :=
  2 * y ^ 4

theorem mainCount_add_correctionCount {t y : ℕ} (hcount : correctionCount y ≤ t) :
    mainCount t y + correctionCount y = t := by
  exact Nat.sub_add_cancel hcount

/-- The properties of the final finite set needed by the upper-bound argument. -/
structure UpperWitness (r : ℝ) (t x : ℕ) (A : Finset ℕ) : Prop where
  card_eq : A.card = t
  zero_not_mem : 0 ∉ A
  sum_eq : reciprocalSum A = r
  le_cutoff : ∀ n ∈ A, n ≤ x

/--
All Proposition 6/7 hypotheses at one value of `t`.  This bundled form is
useful under `Filter.Eventually`; the main assembly theorem below also exposes
every field as an ordinary theorem argument.
-/
structure PropositionFourInput
    (r : ℝ) (t y R lower x : ℕ) (residual : ℝ)
    (large correction : Finset ℕ) : Prop where
  R_eq : R = mainCount t y
  correctionCount_le : correctionCount y ≤ t
  large_card : large.card = R
  correction_card : correction.card = correctionCount y
  large_zero_not_mem : 0 ∉ large
  correction_zero_not_mem : 0 ∉ correction
  large_sum : reciprocalSum large = r - residual
  correction_sum : reciprocalSum correction = residual
  large_lower : ∀ n ∈ large, lower ≤ n
  large_upper : ∀ n ∈ large, n ≤ x
  correction_upper : ∀ n ∈ correction, n ≤ correctionCutoff y
  cutoffs_separated : correctionCutoff y < lower
  correctionCutoff_le : correctionCutoff y ≤ x

/--
The bookkeeping step in Martin's Proposition 4.

The interval separation proves disjointness.  Consequently cardinalities and
reciprocal sums add without overlap.  The identities `R = t - 2π⁺(y)` and
`|correction| = 2π⁺(y)` then give exactly `t` terms.
-/
theorem propositionFour_upperAssembly
    {r : ℝ} {t y R lower x : ℕ} {residual : ℝ}
    {large correction : Finset ℕ}
    (hR : R = mainCount t y)
    (hcount : correctionCount y ≤ t)
    (hlargeCard : large.card = R)
    (hcorrectionCard : correction.card = correctionCount y)
    (hlargeZero : 0 ∉ large)
    (hcorrectionZero : 0 ∉ correction)
    (hlargeSum : reciprocalSum large = r - residual)
    (hcorrectionSum : reciprocalSum correction = residual)
    (hlargeLower : ∀ n ∈ large, lower ≤ n)
    (hlargeUpper : ∀ n ∈ large, n ≤ x)
    (hcorrectionUpper : ∀ n ∈ correction, n ≤ correctionCutoff y)
    (hseparated : correctionCutoff y < lower)
    (hcorrectionCutoff : correctionCutoff y ≤ x) :
    Disjoint large correction ∧ UpperWitness r t x (large ∪ correction) := by
  have hdisjoint : Disjoint large correction := by
    rw [Finset.disjoint_left]
    intro n hnlarge hncorrection
    have hnlow : lower ≤ n := hlargeLower n hnlarge
    have hnupper : n ≤ correctionCutoff y := hcorrectionUpper n hncorrection
    omega
  refine ⟨hdisjoint, ?_⟩
  refine
    { card_eq := ?_
      zero_not_mem := ?_
      sum_eq := ?_
      le_cutoff := ?_ }
  · rw [Finset.card_union_of_disjoint hdisjoint, hlargeCard, hR, hcorrectionCard]
    exact mainCount_add_correctionCount hcount
  · simpa only [Finset.mem_union, not_or] using ⟨hlargeZero, hcorrectionZero⟩
  · rw [reciprocalSum, Finset.sum_union hdisjoint, ← reciprocalSum,
      ← reciprocalSum, hlargeSum, hcorrectionSum]
    ring
  · intro n hn
    rw [Finset.mem_union] at hn
    rcases hn with hnlarge | hncorrection
    · exact hlargeUpper n hnlarge
    · exact (hcorrectionUpper n hncorrection).trans hcorrectionCutoff

/-- The bundled-input version of `propositionFour_upperAssembly`. -/
theorem PropositionFourInput.assemble
    {r : ℝ} {t y R lower x : ℕ} {residual : ℝ}
    {large correction : Finset ℕ}
    (h : PropositionFourInput r t y R lower x residual large correction) :
    Disjoint large correction ∧ UpperWitness r t x (large ∪ correction) := by
  exact propositionFour_upperAssembly h.R_eq h.correctionCount_le h.large_card
    h.correction_card h.large_zero_not_mem h.correction_zero_not_mem h.large_sum
    h.correction_sum h.large_lower h.large_upper h.correction_upper
    h.cutoffs_separated h.correctionCutoff_le

/--
Apply the two arithmetic constructions eventually and assemble their union at
every sufficiently large number of terms.
-/
theorem propositionFour_upperAssembly_eventually
    (r : ℝ) (y R lower x : ℕ → ℕ) (residual : ℕ → ℝ)
    (large correction : ℕ → Finset ℕ)
    (hinput : ∀ᶠ t in atTop,
      PropositionFourInput r t (y t) (R t) (lower t) (x t) (residual t)
        (large t) (correction t)) :
    ∀ᶠ t in atTop, UpperWitness r t (x t) (large t ∪ correction t) := by
  filter_upwards [hinput] with t ht
  exact ht.assemble.2

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Proposition4.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Martin's Proposition 4 for Erdős Problem 285

This file fixes the asymptotic parameters in the final upper-bound assembly.
The arithmetic constructions are supplied by Propositions 6 and 7 in the
companion files; the lemmas here prove that their correction has negligible
cardinality, that the two denominator ranges are separated, and that the
integer rounding does not change the limiting constant.
-/

namespace Proposition4

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

/-- The integer fifth-root scale used for the exact correction. -/
def fifthRootFloor (x : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ ((5 : ℝ)⁻¹)⌋₊

@[simp] lemma fifthRootFloor_eq_approximationCorrectionScale (x : ℕ) :
    fifthRootFloor x = approximationCorrectionScale x := rfl

/-- The lower endpoint `e⁻¹ x / 2` of Martin's large-denominator block. -/
def largeLowerCutoff (x : ℕ) : ℕ :=
  ⌊Real.exp (-1) * (x : ℝ) / 2⌋₊

/-- A fixed threshold after which `2 y⁴` lies below `e⁻¹ y⁵/2`. -/
def separationThreshold : ℕ :=
  max 2 ⌈6 * Real.exp 1⌉₊

/-- A linearly scaled cutoff with an arbitrary vanishing relative buffer. -/
def bufferedCutoff (error : ℕ → ℝ) (t : ℕ) : ℕ :=
  ⌈(Analytic.densityConstant + error t) * (t : ℝ)⌉₊

/-- Martin's explicit vanishing displacement of the lower endpoint.  The
square-root logarithm is slow enough to dominate all quantitative errors in
the filtered initial block, but still tends to zero. -/
def martinMargin (t : ℕ) : ℝ :=
  (Real.sqrt (Real.log (t : ℝ)))⁻¹

/-- A fixed coefficient strictly larger than the square of the limiting
cutoff ratio.  This makes the displaced interval contain a positive
`martinMargin t * t` surplus of terms. -/
def cutoffBufferConstant : ℝ :=
  Analytic.densityConstant ^ 2 + 1

/-- The moving lower endpoint ratio in the final Proposition 6 invocation. -/
def martinLowerRatio (t : ℕ) : ℝ :=
  Real.exp (-1) + martinMargin t

/-- The concrete cutoff used in the final assembly. -/
def martinCutoff (t : ℕ) : ℕ :=
  bufferedCutoff (fun t ↦ cutoffBufferConstant * martinMargin t) t

/-- The full moving initial block used in the last-crossing construction. -/
def martinInitialBlock (x : ℕ) : Finset ℕ :=
  initialBlockAt (martinLowerRatio x) x

/-- Total term score at cutoff `x`: the full Proposition 6 block together
with the cardinality reserved for Proposition 7. -/
def martinScore (x : ℕ) : ℕ :=
  (martinInitialBlock x).card + correctionCount (fifthRootFloor x)

/-- Reindex a term-count cutoff by the formal statement's `k + 1`. -/
def indexedCutoff (x : ℕ → ℕ) (k : ℕ) : ℕ := x k.succ

@[simp] lemma fifthRootFloor_zero : fifthRootFloor 0 = 0 := by
  simp [fifthRootFloor, Real.zero_rpow (by norm_num : (5 : ℝ)⁻¹ ≠ 0)]

@[simp] lemma martinScore_zero : martinScore 0 = 0 := by
  unfold martinScore
  rw [fifthRootFloor_zero]
  simp [martinInitialBlock, initialBlockAt, initialSmoothBlock,
    martinLowerRatio, martinMargin, correctionCount, primePowerCount]

lemma fifthRootFloor_cast_le (x : ℕ) :
    (fifthRootFloor x : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹) := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) _)

lemma fifthRootFloor_pow_five_le (x : ℕ) :
    fifthRootFloor x ^ 5 ≤ x := by
  have h := pow_le_pow_left₀ (Nat.cast_nonneg (fifthRootFloor x))
    (fifthRootFloor_cast_le x) 5
  have hp : ((x : ℝ) ^ ((5 : ℝ)⁻¹) : ℝ) ^ 5 = x := by
    convert Real.rpow_inv_natCast_pow (Nat.cast_nonneg x)
      (by norm_num : (5 : ℕ) ≠ 0) using 1
    all_goals norm_num
  rw [hp] at h
  exact_mod_cast h

/-- The rounded fifth root increases by at most one in one integer step. -/
lemma fifthRootFloor_succ_le (x : ℕ) :
    fifthRootFloor (x + 1) ≤ fifthRootFloor x + 1 := by
  have hreal : ((x + 1 : ℕ) : ℝ) ^ ((5 : ℝ)⁻¹) ≤
      (x : ℝ) ^ ((5 : ℝ)⁻¹) + 1 := by
    have h := Real.rpow_add_le_add_rpow (a := (x : ℝ)) (b := 1)
      (by positivity) (by norm_num) (by norm_num : (0 : ℝ) ≤ (5 : ℝ)⁻¹)
      (by norm_num : (5 : ℝ)⁻¹ ≤ 1)
    norm_num at h ⊢
    exact h
  rw [fifthRootFloor, fifthRootFloor]
  apply Nat.le_of_lt_succ
  rw [Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hlt := Nat.lt_floor_add_one ((x : ℝ) ^ ((5 : ℝ)⁻¹))
  push_cast
  norm_num at hreal ⊢
  linarith

lemma le_fifthRootFloor_of_pow_five_le {q x : ℕ} (hqx : q ^ 5 ≤ x) :
    q ≤ fifthRootFloor x := by
  rw [fifthRootFloor, Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg x) _)]
  apply le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0)
    (Real.rpow_nonneg (Nat.cast_nonneg x) _)
  have hqxR : (q : ℝ) ^ 5 ≤ (x : ℝ) := by exact_mod_cast hqx
  calc
    (q : ℝ) ^ 5 ≤ (x : ℝ) := hqxR
    _ = ((x : ℝ) ^ ((5 : ℝ)⁻¹)) ^ 5 := by
      symm
      convert Real.rpow_inv_natCast_pow (Nat.cast_nonneg x)
        (by norm_num : (5 : ℕ) ≠ 0) using 1
      all_goals norm_num

lemma primePowerCount_le (y : ℕ) : primePowerCount y ≤ y := by
  rw [primePowerCount]
  calc
    ((Icc 1 y).filter IsPrimePow).card ≤ (Icc 1 y).card := card_filter_le _ _
    _ ≤ y := by simp

lemma primePowerCount_succ_le (y : ℕ) :
    primePowerCount (y + 1) ≤ primePowerCount y + 1 := by
  let A := (Icc 1 (y + 1)).filter IsPrimePow
  let B := (Icc 1 y).filter IsPrimePow
  have hsub : A ⊆ insert (y + 1) B := by
    intro q hq
    simp only [A, B, mem_filter, mem_Icc, Finset.mem_insert] at hq ⊢
    by_cases hqy : q = y + 1
    · exact Or.inl hqy
    · exact Or.inr ⟨⟨hq.1.1, by omega⟩, hq.2⟩
  unfold primePowerCount
  change A.card ≤ B.card + 1
  calc
    A.card ≤ (insert (y + 1) B).card := card_le_card hsub
    _ ≤ B.card + 1 := card_insert_le _ _

lemma correctionCount_le_twice (y : ℕ) : correctionCount y ≤ 2 * y := by
  simpa [correctionCount] using Nat.mul_le_mul_left 2 (primePowerCount_le y)

lemma correctionCount_fifthRoot_succ_le (x : ℕ) :
    correctionCount (fifthRootFloor (x + 1)) ≤
      correctionCount (fifthRootFloor x) + 2 := by
  have hr := fifthRootFloor_succ_le x
  have hp := primePowerCount_succ_le (fifthRootFloor x)
  rw [correctionCount, correctionCount]
  have hmono : primePowerCount (fifthRootFloor (x + 1)) ≤
      primePowerCount (fifthRootFloor x + 1) := by
    rw [primePowerCount]
    exact Finset.card_le_card (by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_Icc] at hq ⊢
      exact ⟨⟨hq.1.1, hq.1.2.trans hr⟩, hq.2⟩)
  omega

lemma primePowerCount_eq_piStar (y : ℕ) :
    primePowerCount y = PrimePowers.piStar y := by
  unfold primePowerCount PrimePowers.piStar PrimePowers.primePowersUpTo
  apply congrArg Finset.card
  ext q
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hq1, hqy⟩, hq⟩
    exact ⟨⟨hq.one_lt, hqy⟩, hq⟩
  · rintro ⟨⟨hq2, hqy⟩, hq⟩
    exact ⟨⟨(by omega), hqy⟩, hq⟩

lemma correctionCount_eq_two_mul_piStar (y : ℕ) :
    correctionCount y = 2 * PrimePowers.piStar y := by
  simp [correctionCount, primePowerCount_eq_piStar]

lemma approximationCertificate_residual_den_eq
    {r : ℚ} {x R : ℕ} (C : ApproximationCertificate r x R) :
    C.residual.den = C.denominator := by
  have hb : (0 : ℤ) < C.denominator := by exact_mod_cast C.denominator_pos
  have hcoprime : Nat.Coprime
      ((C.numerator : ℤ).natAbs) ((C.denominator : ℤ).natAbs) := by
    simpa using C.reduced
  have hden := Rat.den_div_eq_of_coprime hb hcoprime
  change (((C.numerator : ℚ) / C.denominator).den : ℤ) =
    (C.denominator : ℤ) at hden
  exact_mod_cast hden

lemma approximationCertificate_residual_largestPart_le
    {r : ℚ} {x R : ℕ} (C : ApproximationCertificate r x R) :
    PrimePowers.largestPrimePowerPart C.residual.den ≤ fifthRootFloor x := by
  rw [approximationCertificate_residual_den_eq C,
    PrimePowers.largestPrimePowerPart_le_iff]
  intro q hq
  have hqdata := (PrimePowers.mem_primePowerParts C.denominator_pos.ne').mp hq
  exact le_fifthRootFloor_of_pow_five_le
    (C.denominator_primePower_bound q hqdata.1 hqdata.2.1)

lemma approximationCertificate_residual_lt_one
    {r : ℚ} {x R : ℕ} (C : ApproximationCertificate r x R) :
    C.residual < 1 := by
  have hcast : (C.residual : ℝ) =
      (C.numerator : ℝ) / C.denominator := by
    simp [ApproximationCertificate.residual]
  have hu := C.residual_upper
  rw [← hcast] at hu
  exact_mod_cast hu

lemma bufferedCutoff_ratio_tendsto {error : ℕ → ℝ}
    (herror : Tendsto error atTop (nhds 0)) :
    Tendsto (fun t : ℕ ↦ (bufferedCutoff error t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant) := by
  let coefficient : ℕ → ℝ := fun t ↦ Analytic.densityConstant + error t
  let scale : ℕ → ℝ := fun t ↦ coefficient t * (t : ℝ)
  have hcoefficient : Tendsto coefficient atTop (nhds Analytic.densityConstant) := by
    simpa [coefficient] using tendsto_const_nhds.add herror
  have hscale : Tendsto scale atTop atTop := by
    have hmul := tendsto_natCast_atTop_atTop.atTop_mul_pos
      Analytic.densityConstant_pos hcoefficient
    apply hmul.congr'
    filter_upwards [] with t
    simp [scale, mul_comm]
  have hround : Tendsto (fun t : ℕ ↦ (⌈scale t⌉₊ : ℝ) / scale t)
      atTop (nhds 1) := tendsto_nat_ceil_div_atTop.comp hscale
  have hprod := hround.mul hcoefficient
  have hprod' : Tendsto
      (fun t : ℕ ↦ (⌈scale t⌉₊ : ℝ) / scale t * coefficient t)
      atTop (nhds Analytic.densityConstant) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [hscale.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with t hscalePos ht
  have hscaleNe : scale t ≠ 0 := hscalePos.ne'
  have htNe : (t : ℝ) ≠ 0 := by positivity
  have hcoefficientNe : coefficient t ≠ 0 := by
    intro hzero
    simp [scale, hzero] at hscalePos
  dsimp [bufferedCutoff]
  change (⌈scale t⌉₊ : ℝ) / scale t * coefficient t =
    (⌈(coefficient t) * (t : ℝ)⌉₊ : ℝ) / (t : ℝ)
  rw [show scale t = coefficient t * (t : ℝ) by rfl]
  field_simp

lemma martinMargin_tendsto_zero :
    Tendsto martinMargin atTop (nhds 0) := by
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_log_coe_at_top)

lemma martinMargin_pos :
    ∀ᶠ t : ℕ in atTop, 0 < martinMargin t := by
  filter_upwards [eventually_ge_atTop 2] with t ht
  exact inv_pos.mpr (Real.sqrt_pos.2 (Real.log_pos (by exact_mod_cast (by omega : 1 < t))))

lemma martinMargin_mul_t_tendsto_atTop :
    Tendsto (fun t : ℕ ↦ martinMargin t * (t : ℝ)) atTop atTop := by
  have hsqrtTop : Tendsto (fun t : ℕ ↦ Real.sqrt (t : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop.2
  intro b
  filter_upwards [hsqrtTop.eventually (eventually_ge_atTop b),
    eventually_ge_atTop 2] with t hbt ht
  apply hbt.trans
  have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hlogPos : 0 < Real.log (t : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hlogLe : Real.log (t : ℝ) ≤ (t : ℝ) :=
    (Real.log_le_sub_one_of_pos htR).trans (by linarith)
  have hsqrtLe : Real.sqrt (Real.log (t : ℝ)) ≤ Real.sqrt (t : ℝ) :=
    Real.sqrt_le_sqrt hlogLe
  rw [martinMargin, inv_mul_eq_div, le_div_iff₀ (Real.sqrt_pos.2 hlogPos)]
  calc
    Real.sqrt (t : ℝ) * Real.sqrt (Real.log (t : ℝ)) ≤
        Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ) := by
      exact mul_le_mul_of_nonneg_left hsqrtLe (Real.sqrt_nonneg _)
    _ = (t : ℝ) := Real.mul_self_sqrt htR.le

lemma martinLowerRatio_tendsto :
    Tendsto martinLowerRatio atTop (nhds (Real.exp (-1))) := by
  change Tendsto (fun t : ℕ ↦ Real.exp (-1) + martinMargin t) atTop
    (nhds (Real.exp (-1)))
  simpa using tendsto_const_nhds.add martinMargin_tendsto_zero

lemma eventually_martinLowerRatio_bounds :
    ∀ᶠ t : ℕ in atTop,
      Real.exp (-1) < martinLowerRatio t ∧ martinLowerRatio t < 1 := by
  have hexp : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  have hup := martinLowerRatio_tendsto.eventually
    (Iio_mem_nhds hexp)
  filter_upwards [martinMargin_pos, hup] with t hmargin halpha
  exact ⟨by simp [martinLowerRatio, hmargin], halpha⟩

lemma martinCutoff_ratio_tendsto :
    Tendsto (fun t : ℕ ↦ (martinCutoff t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant) := by
  apply bufferedCutoff_ratio_tendsto
  simpa using martinMargin_tendsto_zero.const_mul cutoffBufferConstant

lemma martinLowerEndpoint_floor_ratio_tendsto :
    Tendsto
      (fun x : ℕ ↦
        ((⌊martinLowerRatio x * (x : ℝ)⌋₊ : ℕ) : ℝ) / (x : ℝ))
      atTop (nhds (Real.exp (-1))) := by
  let scale : ℕ → ℝ := fun x ↦ martinLowerRatio x * (x : ℝ)
  have haPos : 0 < Real.exp (-1) := Real.exp_pos _
  have hscale : Tendsto scale atTop atTop := by
    have hmul := tendsto_natCast_atTop_atTop.atTop_mul_pos haPos
      martinLowerRatio_tendsto
    apply hmul.congr'
    filter_upwards [] with x
    simp [scale, mul_comm]
  have hround : Tendsto
      (fun x : ℕ ↦ ((⌊scale x⌋₊ : ℕ) : ℝ) / scale x)
      atTop (nhds 1) := tendsto_nat_floor_div_atTop.comp hscale
  have hprod := hround.mul martinLowerRatio_tendsto
  have hprod' : Tendsto
      (fun x : ℕ ↦ ((⌊scale x⌋₊ : ℕ) : ℝ) / scale x * martinLowerRatio x)
      atTop (nhds (Real.exp (-1))) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [hscale.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with x hscalePos hx
  have hxne : (x : ℝ) ≠ 0 := by positivity
  have hane : martinLowerRatio x ≠ 0 := by
    intro ha
    simp [scale, ha] at hscalePos
  dsimp [scale]
  field_simp

lemma movingFullInitialInterval_card_ratio_tendsto :
    Tendsto
      (fun x : ℕ ↦
        ((fullInitialIntervalAt (martinLowerRatio x) x).card : ℝ) / (x : ℝ))
      atTop (nhds (1 - Real.exp (-1))) := by
  have hlim := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub
      martinLowerEndpoint_floor_ratio_tendsto
  apply hlim.congr'
  filter_upwards [eventually_martinLowerRatio_bounds,
    eventually_ge_atTop 1] with x halpha hx
  have hfloorle : ⌊martinLowerRatio x * (x : ℝ)⌋₊ ≤ x := by
    have hreal : ((⌊martinLowerRatio x * (x : ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) :=
      (Nat.floor_le (mul_nonneg
        ((Real.exp_pos (-1)).trans halpha.1).le
        (Nat.cast_nonneg x))).trans
        (mul_le_of_le_one_left (Nat.cast_nonneg x) halpha.2.le)
    exact_mod_cast hreal
  rw [show (fullInitialIntervalAt (martinLowerRatio x) x).card =
      x - ⌊martinLowerRatio x * (x : ℝ)⌋₊ by
    simp [fullInitialIntervalAt], Nat.cast_sub hfloorle]
  field_simp

lemma movingInitialRoughPart_card_ratio_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦
        ((initialRoughPartAt (martinLowerRatio x) x).card : ℝ) / (x : ℝ))
      atTop (nhds 0) := by
  have hglobal :=
    (RoughCounts.roughNumbersIn_logPowerCutoff_card_isLittleO 30).tendsto_div_nhds_zero
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x ↦
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards with x
    have hc : ((initialRoughPartAt (martinLowerRatio x) x).card : ℝ) ≤
        ((RoughCounts.roughNumbersIn 1 x
          (RoughCounts.logPowerCutoff 30 x)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (initialRoughPartAt_subset_global (martinLowerRatio x) x)
    exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg x)
  · exact hglobal

lemma martinInitialBlock_card_ratio_tendsto :
    Tendsto (fun x : ℕ ↦ ((martinInitialBlock x).card : ℝ) / (x : ℝ))
      atTop (nhds (1 - Real.exp (-1))) := by
  have hlim := movingFullInitialInterval_card_ratio_tendsto.sub
    movingInitialRoughPart_card_ratio_tendsto_zero
  have hlim' : Tendsto
      (fun x : ℕ ↦
        ((fullInitialIntervalAt (martinLowerRatio x) x).card : ℝ) / x -
          ((initialRoughPartAt (martinLowerRatio x) x).card : ℝ) / x)
      atTop (nhds (1 - Real.exp (-1))) := by simpa using hlim
  apply hlim'.congr'
  filter_upwards with x
  have hsub := initialRoughPartAt_subset_full (martinLowerRatio x) x
  rw [martinInitialBlock, initialBlockAt_eq_sdiff,
    Finset.card_sdiff_of_subset hsub,
    Nat.cast_sub (Finset.card_le_card hsub)]
  ring

/-! ## Fifth-root asymptotics for an arbitrary asymptotically optimal cutoff -/

lemma fifthRoot_ratio_formula {x t : ℕ} (ht : 0 < t) :
    ((x : ℝ) ^ ((5 : ℝ)⁻¹)) / t =
      (((x : ℝ) / t) ^ ((5 : ℝ)⁻¹)) *
        (t : ℝ) ^ (-(4 / 5 : ℝ)) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  calc
    ((x : ℝ) ^ ((5 : ℝ)⁻¹)) / t =
        ((((x : ℝ) / t) * t) ^ ((5 : ℝ)⁻¹)) / t := by
          rw [div_mul_cancel₀ _ htR.ne']
    _ = ((((x : ℝ) / t) ^ ((5 : ℝ)⁻¹)) *
          (t : ℝ) ^ ((5 : ℝ)⁻¹)) / t := by
          rw [Real.mul_rpow (by positivity) htR.le]
    _ = (((x : ℝ) / t) ^ ((5 : ℝ)⁻¹)) *
          (t : ℝ) ^ (-(4 / 5 : ℝ)) := by
          have hquot : (t : ℝ) ^ ((5 : ℝ)⁻¹) / t =
              (t : ℝ) ^ (-(4 / 5 : ℝ)) := by
            conv_lhs => rhs; rw [← Real.rpow_one (t : ℝ)]
            rw [← Real.rpow_sub htR]
            congr 1
            norm_num
          rw [mul_div_assoc, hquot]

lemma natCast_cutoff_tendsto_atTop
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    Tendsto (fun t : ℕ ↦ (x t : ℝ)) atTop atTop := by
  have hprod : Tendsto
      (fun t : ℕ ↦ (t : ℝ) * ((x t : ℝ) / (t : ℝ)))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_pos hC hx
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
  have htR : (t : ℝ) ≠ 0 := by positivity
  field_simp

lemma fifthRootFloor_tendsto_atTop
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    Tendsto (fun t ↦ fifthRootFloor (x t)) atTop atTop := by
  apply tendsto_nat_floor_atTop.comp
  apply (tendsto_rpow_atTop (by positivity : (0 : ℝ) < (5 : ℝ)⁻¹)).comp
  exact natCast_cutoff_tendsto_atTop hC hx

lemma fifthRootFloor_ratio_tendsto_zero
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    Tendsto (fun t : ℕ ↦ (fifthRootFloor (x t) : ℝ) / (t : ℝ))
      atTop (nhds 0) := by
  have hfirst : Tendsto
      (fun t : ℕ ↦ ((x t : ℝ) / (t : ℝ)) ^ ((5 : ℝ)⁻¹))
      atTop (nhds (C ^ ((5 : ℝ)⁻¹))) :=
    hx.rpow_const (.inl hC.ne')
  have hsecond : Tendsto (fun t : ℕ ↦ (t : ℝ) ^ (-(4 / 5 : ℝ)))
      atTop (nhds 0) := by
    exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp
      tendsto_natCast_atTop_atTop
  have hroot : Tendsto
      (fun t : ℕ ↦ ((x t : ℝ) ^ ((5 : ℝ)⁻¹)) / (t : ℝ))
      atTop (nhds 0) := by
    have hm := hfirst.mul hsecond
    have heq : (fun t : ℕ ↦
        ((x t : ℝ) / (t : ℝ)) ^ ((5 : ℝ)⁻¹) *
          (t : ℝ) ^ (-(4 / 5 : ℝ))) =ᶠ[atTop]
        (fun t : ℕ ↦ ((x t : ℝ) ^ ((5 : ℝ)⁻¹)) / (t : ℝ)) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
      exact (fifthRoot_ratio_formula ht).symm
    simpa only [mul_zero] using hm.congr' heq
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hroot
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
    exact div_le_div_of_nonneg_right (fifthRootFloor_cast_le (x t)) (by positivity)

lemma correctionCount_ratio_tendsto_zero
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    Tendsto
      (fun t : ℕ ↦
        (correctionCount (fifthRootFloor (x t)) : ℝ) / (t : ℝ))
      atTop (nhds 0) := by
  have hy := fifthRootFloor_ratio_tendsto_zero hC hx
  have hupper : Tendsto
      (fun t : ℕ ↦ 2 * ((fifthRootFloor (x t) : ℝ) / (t : ℝ)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hy
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
    have hc : (correctionCount (fifthRootFloor (x t)) : ℝ) ≤
        (2 * fifthRootFloor (x t) : ℕ) := by
      exact_mod_cast correctionCount_le_twice (fifthRootFloor (x t))
    calc
      (correctionCount (fifthRootFloor (x t)) : ℝ) / t ≤
          (2 * fifthRootFloor (x t) : ℕ) / (t : ℝ) :=
        div_le_div_of_nonneg_right hc (by positivity)
      _ = 2 * ((fifthRootFloor (x t) : ℝ) / (t : ℝ)) := by
        push_cast
        ring

lemma eventually_correctionCount_le
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    ∀ᶠ t in atTop, correctionCount (fifthRootFloor (x t)) ≤ t := by
  have hratio := correctionCount_ratio_tendsto_zero hC hx
  have hlt : ∀ᶠ t in atTop,
      (correctionCount (fifthRootFloor (x t)) : ℝ) / (t : ℝ) < 1 :=
    hratio.eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with t hlt ht
  rw [div_lt_iff₀ (by exact_mod_cast ht : (0 : ℝ) < t)] at hlt
  have hcR : (correctionCount (fifthRootFloor (x t)) : ℝ) ≤ (t : ℝ) := by
    linarith
  exact_mod_cast hcR

/-! ## Separation of the main and correction denominator ranges -/

lemma correctionCutoff_le_of_two_le {x y : ℕ} (hy : 2 ≤ y)
    (hy5 : y ^ 5 ≤ x) : correctionCutoff y ≤ x := by
  apply le_trans ?_ hy5
  rw [correctionCutoff]
  calc
    2 * y ^ 4 ≤ y * y ^ 4 := Nat.mul_le_mul_right (y ^ 4) hy
    _ = y ^ 5 := by ring

lemma correctionCutoff_lt_largeLowerCutoff {x y : ℕ}
    (hy : separationThreshold ≤ y) (hy5 : y ^ 5 ≤ x) :
    correctionCutoff y < largeLowerCutoff x := by
  have hy2 : 2 ≤ y := (le_max_left 2 ⌈6 * Real.exp 1⌉₊).trans hy
  have hyceil : ⌈6 * Real.exp 1⌉₊ ≤ y :=
    (le_max_right 2 ⌈6 * Real.exp 1⌉₊).trans hy
  have hscale : 6 * Real.exp 1 ≤ (y : ℝ) :=
    (Nat.le_ceil (6 * Real.exp 1)).trans (by exact_mod_cast hyceil)
  have hexp : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hmul : (6 : ℝ) ≤ Real.exp (-1) * y := by
    have := mul_le_mul_of_nonneg_left hscale (Real.exp_pos (-1)).le
    have heq : Real.exp (-1) * (6 * Real.exp 1) = (6 : ℝ) := by
      calc
        Real.exp (-1) * (6 * Real.exp 1) = 6 * (Real.exp (-1) * Real.exp 1) := by ring
        _ = 6 := by rw [hexp]; ring
    rw [heq] at this
    exact this
  have hy4pos : (1 : ℝ) ≤ (y : ℝ) ^ 4 := by
    have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hy1 4]
  have hcore : 3 * (y : ℝ) ^ 4 ≤
      Real.exp (-1) * (y : ℝ) ^ 5 / 2 := by
    have hmul' := mul_le_mul_of_nonneg_left hmul
      (show 0 ≤ (y : ℝ) ^ 4 / 2 by positivity)
    calc
      3 * (y : ℝ) ^ 4 = ((y : ℝ) ^ 4 / 2) * 6 := by ring
      _ ≤ ((y : ℝ) ^ 4 / 2) * (Real.exp (-1) * y) := hmul'
      _ = Real.exp (-1) * (y : ℝ) ^ 5 / 2 := by ring
  have hy5R : (y : ℝ) ^ 5 ≤ (x : ℝ) := by exact_mod_cast hy5
  have hreal : ((correctionCutoff y + 1 : ℕ) : ℝ) ≤
      Real.exp (-1) * (x : ℝ) / 2 := by
    rw [correctionCutoff]
    push_cast
    calc
      2 * (y : ℝ) ^ 4 + 1 ≤ 3 * (y : ℝ) ^ 4 := by linarith
      _ ≤ Real.exp (-1) * (y : ℝ) ^ 5 / 2 := hcore
      _ ≤ Real.exp (-1) * (x : ℝ) / 2 := by
        gcongr
  have hfloor : correctionCutoff y + 1 ≤ largeLowerCutoff x := by
    rw [largeLowerCutoff, Nat.le_floor_iff (by positivity)]
    exact hreal
  omega

/-- Flooring the fifth root costs less than one.  A deliberately coarse sixth
power absorbs that rounding once the root is at least `32`. -/
lemma cutoff_lt_sixth_power_fifthRoot {x : ℕ} (hy : 32 ≤ fifthRootFloor x) :
    x < fifthRootFloor x ^ 6 := by
  let y := fifthRootFloor x
  have hroot : (x : ℝ) ^ ((5 : ℝ)⁻¹) < (y + 1 : ℕ) := by
    rw [Nat.cast_add, Nat.cast_one]
    dsimp only [y, fifthRootFloor]
    exact Nat.lt_floor_add_one ((x : ℝ) ^ ((5 : ℝ)⁻¹))
  have hpowR := pow_lt_pow_left₀ hroot
    (Real.rpow_nonneg (Nat.cast_nonneg x) _) (by norm_num : (5 : ℕ) ≠ 0)
  have hrootPow : ((x : ℝ) ^ ((5 : ℝ)⁻¹)) ^ 5 = (x : ℝ) := by
    convert Real.rpow_inv_natCast_pow (Nat.cast_nonneg x)
      (by norm_num : (5 : ℕ) ≠ 0) using 1
    all_goals norm_num
  rw [hrootPow] at hpowR
  have hxSuccPow : x < (y + 1) ^ 5 := by exact_mod_cast hpowR
  have hsucc : y + 1 ≤ 2 * y := by dsimp [y] at hy ⊢; omega
  have hsuccPow : (y + 1) ^ 5 ≤ (2 * y) ^ 5 :=
    pow_le_pow_left₀ (Nat.zero_le _) hsucc 5
  have h32 : 32 * y ^ 5 ≤ y * y ^ 5 :=
    Nat.mul_le_mul_right (y ^ 5) (by simpa [y] using hy)
  calc
    x < (y + 1) ^ 5 := hxSuccPow
    _ ≤ (2 * y) ^ 5 := hsuccPow
    _ = 32 * y ^ 5 := by ring
    _ ≤ y * y ^ 5 := h32
    _ = y ^ 6 := by ring

lemma log_cutoff_lt_six_mul_log_fifthRoot {x : ℕ}
    (hy : 32 ≤ fifthRootFloor x) :
    Real.log (x : ℝ) < 6 * Real.log (fifthRootFloor x : ℝ) := by
  have hxy := cutoff_lt_sixth_power_fifthRoot hy
  have hxpos : (0 : ℝ) < x := by
    have hy5 := fifthRootFloor_pow_five_le x
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < fifthRootFloor x ^ 5) hy5)
  have hypowpos : (0 : ℝ) < fifthRootFloor x ^ 6 := by positivity
  have hlog := Real.strictMonoOn_log hxpos hypowpos (by exact_mod_cast hxy)
  simpa [Real.log_pow] using hlog

lemma one_sixth_mul_inv_log_fifthRoot_lt_inv_log_cutoff {x : ℕ}
    (hy : 32 ≤ fifthRootFloor x) :
    (1 / 6 : ℝ) * (Real.log (fifthRootFloor x : ℝ))⁻¹ <
      (Real.log (x : ℝ))⁻¹ := by
  have hyone : (1 : ℝ) < fifthRootFloor x := by exact_mod_cast (show 1 < fifthRootFloor x by omega)
  have hylog : 0 < Real.log (fifthRootFloor x : ℝ) := Real.log_pos hyone
  have hxone : (1 : ℝ) < x := by
    have hy5 := fifthRootFloor_pow_five_le x
    have : 1 < fifthRootFloor x ^ 5 :=
      one_lt_pow₀ (show 1 < fifthRootFloor x by omega) (by norm_num)
    exact_mod_cast this.trans_le hy5
  have hxlog : 0 < Real.log (x : ℝ) := Real.log_pos hxone
  have hlog := log_cutoff_lt_six_mul_log_fifthRoot hy
  have hinv := one_div_lt_one_div_of_lt hxlog hlog
  calc
    (1 / 6 : ℝ) * (Real.log (fifthRootFloor x : ℝ))⁻¹ =
        1 / (6 * Real.log (fifthRootFloor x : ℝ)) := by field_simp
    _ < 1 / Real.log (x : ℝ) := hinv
    _ = (Real.log (x : ℝ))⁻¹ := one_div _

/-- Proposition 6's lower residual bound at scale `x` implies the weakened
fixed-constant bound required by Proposition 7 at the rounded fifth-root
scale.  The slack from `1/5` to `1/6` absorbs the floor. -/
lemma approximationCertificate_residual_lower_one_sixth
    {x R : ℕ} (C : ApproximationCertificate (1 : ℚ) x R)
    (hy : 32 ≤ fifthRootFloor x) :
    (1 / 6 : ℝ) * (Real.log (fifthRootFloor x : ℝ))⁻¹ <
      (C.residual : ℝ) := by
  have hcast : (C.residual : ℝ) =
      (C.numerator : ℝ) / (C.denominator : ℝ) := by
    simp [ApproximationCertificate.residual]
  rw [hcast]
  exact (one_sixth_mul_inv_log_fifthRoot_lt_inv_log_cutoff hy).trans
    C.residual_lower

lemma eventually_cutoffs_separated
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    ∀ᶠ t in atTop,
      correctionCutoff (fifthRootFloor (x t)) < largeLowerCutoff (x t) := by
  have hyTop := fifthRootFloor_tendsto_atTop hC hx
  filter_upwards [hyTop.eventually_ge_atTop separationThreshold] with t ht
  exact correctionCutoff_lt_largeLowerCutoff ht
    (fifthRootFloor_pow_five_le (x t))

lemma eventually_correctionCutoff_le
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C)) :
    ∀ᶠ t in atTop, correctionCutoff (fifthRootFloor (x t)) ≤ x t := by
  have hyTop := fifthRootFloor_tendsto_atTop hC hx
  filter_upwards [hyTop.eventually_ge_atTop 2] with t ht
  exact correctionCutoff_le_of_two_le ht (fifthRootFloor_pow_five_le (x t))

/-! ## The concrete moving parameters -/

lemma identity_cutoff_ratio_tendsto :
    Tendsto (fun x : ℕ ↦ (x : ℝ) / (x : ℝ)) atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with x hx
  field_simp

lemma martinScore_ratio_tendsto :
    Tendsto (fun x : ℕ ↦ (martinScore x : ℝ) / (x : ℝ)) atTop
      (nhds (1 - Real.exp (-1))) := by
  have hcorr := correctionCount_ratio_tendsto_zero (C := (1 : ℝ))
    (by norm_num) identity_cutoff_ratio_tendsto
  have hsum := martinInitialBlock_card_ratio_tendsto.add hcorr
  have hsum' : Tendsto
      (fun x : ℕ ↦ ((martinInitialBlock x).card : ℝ) / x +
        (correctionCount (fifthRootFloor x) : ℝ) / x)
      atTop (nhds (1 - Real.exp (-1))) := by simpa using hsum
  apply hsum'.congr'
  filter_upwards with x
  simp only [martinScore, Nat.cast_add]
  ring

lemma martinScore_tendsto_atTop :
    Tendsto martinScore atTop atTop := by
  have hd : 0 < 1 - Real.exp (-1) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    norm_num
  have hreal := natCast_cutoff_tendsto_atTop hd martinScore_ratio_tendsto
  exact tendsto_natCast_atTop_iff.mp hreal

/-! ## Conversion of Propositions 6 and 7 into the assembly input -/

theorem propositionFourInput_of_certificates
    {t x y R : ℕ} (C : ApproximationCertificate (1 : ℚ) x R)
    {correction : Finset ℕ}
    (hR : R = mainCount t y)
    (hcount : correctionCount y ≤ t)
    (hcorrectionCard : correction.card = correctionCount y)
    (hcorrectionZero : 0 ∉ correction)
    (hcorrectionSum : UnitFractions.rec_sum correction = C.residual)
    (hcorrectionUpper : ∀ n ∈ correction, n ≤ correctionCutoff y)
    (hseparated : correctionCutoff y < largeLowerCutoff x)
    (hcorrectionCutoff : correctionCutoff y ≤ x) :
    PropositionFourInput 1 t y R (largeLowerCutoff x) x (C.residual : ℝ)
      C.denominators correction := by
  refine
    { R_eq := hR
      correctionCount_le := hcount
      large_card := C.card_eq
      correction_card := hcorrectionCard
      large_zero_not_mem := C.zero_not_mem
      correction_zero_not_mem := hcorrectionZero
      large_sum := ?_
      correction_sum := ?_
      large_lower := ?_
      large_upper := ?_
      correction_upper := hcorrectionUpper
      cutoffs_separated := hseparated
      correctionCutoff_le := hcorrectionCutoff }
  · rw [show reciprocalSum C.denominators = realRecSum C.denominators by rfl,
      realRecSum_eq_ratCast, C.reciprocal_sum_eq_sub_residual]
    norm_num
  · rw [show reciprocalSum correction = realRecSum correction by rfl,
      realRecSum_eq_ratCast, hcorrectionSum]
  · intro n hn
    have hfloorR : (largeLowerCutoff x : ℝ) ≤
        Real.exp (-1) * (x : ℝ) / 2 := by
      exact Nat.floor_le (by positivity)
    have hnR : Real.exp (-1) * (x : ℝ) / 2 ≤ (n : ℝ) := by
      simpa using (C.interval n hn).1
    exact_mod_cast hfloorR.trans hnR
  · intro n hn
    exact_mod_cast (C.interval n hn).2

/-- The same bridge with Proposition 7's native cardinality notation
`2 * piStar y`. -/
theorem propositionFourInput_of_martin_certificates
    {t x y R : ℕ} (C : ApproximationCertificate (1 : ℚ) x R)
    {correction : Finset ℕ}
    (hR : R = mainCount t y)
    (hcount : correctionCount y ≤ t)
    (hcorrectionCard : correction.card = 2 * PrimePowers.piStar y)
    (hcorrectionZero : 0 ∉ correction)
    (hcorrectionSum : UnitFractions.rec_sum correction = C.residual)
    (hcorrectionUpper : ∀ n ∈ correction, n ≤ 2 * y ^ 4)
    (hseparated : correctionCutoff y < largeLowerCutoff x)
    (hcorrectionCutoff : correctionCutoff y ≤ x) :
    PropositionFourInput 1 t y R (largeLowerCutoff x) x (C.residual : ℝ)
      C.denominators correction := by
  apply propositionFourInput_of_certificates C hR hcount
  · simpa [correctionCount_eq_two_mul_piStar] using hcorrectionCard
  · exact hcorrectionZero
  · exact hcorrectionSum
  · simpa only [correctionCutoff] using hcorrectionUpper
  · exact hseparated
  · exact hcorrectionCutoff

/-- Proposition 7 turns every sufficiently large Proposition 6 certificate
at the rounded fifth-root scale into the complete finite assembly input.  This
is the unconditional Proposition 6-to-7 bridge: no arithmetic construction is
passed as a theorem argument. -/
theorem eventually_propositionFourInput_of_approximationCertificates
    {x : ℕ → ℕ} {C : ℝ} (hC : 0 < C)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop (nhds C))
    (hcert : ∀ᶠ t : ℕ in atTop,
      Nonempty (ApproximationCertificate (1 : ℚ) (x t)
        (mainCount t (fifthRootFloor (x t))))) :
    ∀ᶠ t in atTop,
      ∃ residual : ℝ, ∃ large correction : Finset ℕ,
        PropositionFourInput 1 t (fifthRootFloor (x t))
          (mainCount t (fifthRootFloor (x t))) (largeLowerCutoff (x t))
          (x t) residual large correction := by
  have hyTop := fifthRootFloor_tendsto_atTop hC hx
  have hp7 := hyTop.eventually
    (Proposition7.eventually_proposition7 (c := (1 / 6 : ℝ)) (by positivity))
  have hy32 := hyTop.eventually (eventually_ge_atTop 32)
  have hcount := eventually_correctionCount_le hC hx
  have hsep := eventually_cutoffs_separated hC hx
  have hcut := eventually_correctionCutoff_le hC hx
  filter_upwards [hcert, hp7, hy32, hcount, hsep, hcut]
      with t htCert htP7 htY htCount htSep htCut
  rcases htCert with ⟨cert⟩
  have hpart := approximationCertificate_residual_largestPart_le cert
  have hlower := approximationCertificate_residual_lower_one_sixth cert htY
  have hupperQ := approximationCertificate_residual_lt_one cert
  have hupper : (cert.residual : ℝ) < 1 := by exact_mod_cast hupperQ
  obtain ⟨E, hEcard, hEsum, hEzero, hEupper⟩ :=
    htP7 cert.residual hpart (by simpa [div_eq_mul_inv] using hlower) hupper
  refine ⟨(cert.residual : ℝ), cert.denominators, E, ?_⟩
  exact propositionFourInput_of_martin_certificates cert rfl htCount
    hEcard hEzero hEsum hEupper htSep htCut

/-- The existential filter form used once the unconditional Proposition 6 and
Proposition 7 constructions have supplied their certificates. -/
theorem eventually_upperWitness_of_eventually_input
    (x : ℕ → ℕ)
    (hinput : ∀ᶠ t in atTop,
      ∃ residual : ℝ, ∃ large correction : Finset ℕ,
        PropositionFourInput 1 t (fifthRootFloor (x t))
          (mainCount t (fifthRootFloor (x t))) (largeLowerCutoff (x t))
          (x t) residual large correction) :
    ∀ᶠ t in atTop, ∃ A : Finset ℕ, UpperWitness 1 t (x t) A := by
  filter_upwards [hinput] with t ht
  obtain ⟨residual, large, correction, hdata⟩ := ht
  exact ⟨large ∪ correction, hdata.assemble.2⟩

/-- Shift the term-count form of Proposition 4 to the `k + 1` convention of
the formal-conjectures statement. -/
theorem shift_to_formal_index
    (x : ℕ → ℕ)
    (hupper : ∀ᶠ t in atTop, ∃ A : Finset ℕ, UpperWitness 1 t (x t) A)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant)) :
    (∀ᶠ k in atTop,
      ∃ A : Finset ℕ, UpperWitness 1 k.succ (indexedCutoff x k) A) ∧
    Tendsto
      (fun k : ℕ ↦ (indexedCutoff x k : ℝ) / (k + 1 : ℕ)) atTop
      (nhds Analytic.densityConstant) := by
  have hshift := tendsto_add_atTop_nat 1
  constructor
  · have hpull := hshift.eventually hupper
    simpa [indexedCutoff, Nat.succ_eq_add_one, Function.comp_def] using hpull
  · have hpull := hx.comp hshift
    simpa [indexedCutoff, Nat.succ_eq_add_one, Function.comp_def] using hpull

/-- Complete high-level assembly, still phrased in terms of the eventual
certificate proposition that the arithmetic files discharge. -/
theorem propositionFour_from_eventually_input
    (x : ℕ → ℕ)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant))
    (hinput : ∀ᶠ t in atTop,
      ∃ residual : ℝ, ∃ large correction : Finset ℕ,
        PropositionFourInput 1 t (fifthRootFloor (x t))
          (mainCount t (fifthRootFloor (x t))) (largeLowerCutoff (x t))
          (x t) residual large correction) :
    (∀ᶠ k in atTop,
      ∃ A : Finset ℕ, UpperWitness 1 k.succ (indexedCutoff x k) A) ∧
    Tendsto
      (fun k : ℕ ↦ (indexedCutoff x k : ℝ) / (k + 1 : ℕ)) atTop
      (nhds Analytic.densityConstant) := by
  exact shift_to_formal_index x
    (eventually_upperWitness_of_eventually_input x hinput) hx

/-- Complete Proposition 4 once the concrete Proposition 6 certificate stream
has been constructed.  Proposition 7 is invoked internally by
`eventually_propositionFourInput_of_approximationCertificates`. -/
theorem propositionFour_of_approximationCertificates
    (x : ℕ → ℕ)
    (hx : Tendsto (fun t : ℕ ↦ (x t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant))
    (hcert : ∀ᶠ t : ℕ in atTop,
      Nonempty (ApproximationCertificate (1 : ℚ) (x t)
        (mainCount t (fifthRootFloor (x t))))) :
    (∀ᶠ k in atTop,
      ∃ A : Finset ℕ, UpperWitness 1 k.succ (indexedCutoff x k) A) ∧
    Tendsto
      (fun k : ℕ ↦ (indexedCutoff x k : ℝ) / (k + 1 : ℕ)) atTop
      (nhds Analytic.densityConstant) := by
  apply propositionFour_from_eventually_input x hx
  exact eventually_propositionFourInput_of_approximationCertificates
    Analytic.densityConstant_pos hx hcert

end

end Proposition4

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/MovingBounds.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Moving-parameter estimates for Martin's Proposition 6

The final construction takes the lower endpoint
`exp (-1) + 1 / sqrt (log x)`, rather than a fixed endpoint.  Consequently
the initial residual tends to zero and the fixed-parameter margin theorem in
`Proposition6Asymptotic` does not apply directly.  This file proves the
quantitative moving estimates used by the final Proposition 6 invocation.
-/

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open RoughCounts

/-! ## The elimination budget -/

/-- The actual recursion budget, summed over every possible measure up to the
main cutoff, is eventually covered by the explicit deletion budget. -/
theorem eventually_totalEliminationBudget_mainCutoff_le :
    ∀ᶠ x : ℕ in atTop,
      totalEliminationBudget x (mainCutoffNat x) ≤ proposition6DeletionBudget x := by
  have hQtop : Tendsto mainCutoffNat atTop atTop := mainCutoffNat_spec.2.1
  have hlogtop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    tendsto_log_coe_at_top
  filter_upwards [eventually_ge_atTop 3,
    hQtop.eventually (eventually_ge_atTop 1),
    hlogtop.eventually (eventually_ge_atTop 1)] with x hx hQ hlog
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hlog0 : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlog
  have hQcut : (mainCutoffNat x : ℝ) ≤
      (x : ℝ) / Real.log (x : ℝ) ^ 30 := by
    rw [← show proposition6MainCutoff x =
      (x : ℝ) / Real.log (x : ℝ) ^ 30 by rfl, mainCutoffNat_eq]
    exact Nat.floor_le (proposition6MainCutoff_nonneg x)
  have hsum : (totalEliminationBudget x (mainCutoffNat x) : ℝ) ≤
      600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    rw [totalEliminationBudget, Nat.cast_sum]
    calc
      ∑ q ∈ range (mainCutoffNat x + 1),
          (Erdos285.Lemma12.martinBlockBound x q : ℝ) ≤
          ∑ q ∈ range (mainCutoffNat x + 1),
            200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) *
              Real.log (x : ℝ) ^ 3 := by
        apply Finset.sum_le_sum
        intro q hq
        exact Erdos285.Lemma12.martinBlockBound_cast_le hx1
      _ = ∑ q ∈ Icc 1 (mainCutoffNat x),
            200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) *
              Real.log (x : ℝ) ^ 3 := by
        rw [show range (mainCutoffNat x + 1) = insert 0 (Icc 1 (mainCutoffNat x)) by
          ext q
          simp
          omega]
        simp
      _ = 200 * (x : ℝ) ^ ((2 : ℝ) / 3) *
            Real.log (x : ℝ) ^ 3 *
              (∑ q ∈ Icc 1 (mainCutoffNat x),
                (q : ℝ) ^ (-(2 : ℝ) / 3)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        have hqpos : (0 : ℝ) < q := by
          have : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)
        rw [div_rpow_two_thirds hx0 hqpos]
        ring
      _ ≤ 200 * (x : ℝ) ^ ((2 : ℝ) / 3) *
            Real.log (x : ℝ) ^ 3 *
              (3 * (mainCutoffNat x : ℝ) ^ ((1 : ℝ) / 3)) := by
        gcongr
        exact sum_Icc_rpow_neg_two_thirds_le _ hQ
      _ ≤ 200 * (x : ℝ) ^ ((2 : ℝ) / 3) *
            Real.log (x : ℝ) ^ 3 *
              (3 * ((x : ℝ) / Real.log (x : ℝ) ^ 30) ^
                ((1 : ℝ) / 3)) := by
        gcongr
      _ = 600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
        calc
          200 * (x : ℝ) ^ ((2 : ℝ) / 3) * Real.log (x : ℝ) ^ 3 *
                (3 * ((x : ℝ) / Real.log (x : ℝ) ^ 30) ^
                  ((1 : ℝ) / 3)) =
              600 * ((x : ℝ) ^ ((2 : ℝ) / 3) *
                ((x : ℝ) / Real.log (x : ℝ) ^ 30) ^ ((1 : ℝ) / 3) *
                Real.log (x : ℝ) ^ 3) := by ring
          _ = 600 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) := by
            rw [deletion_rpow_identity (by positivity) hlog0]
          _ = 600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by ring
  have htarget : (totalEliminationBudget x (mainCutoffNat x) : ℝ) ≤
      1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    calc
      (totalEliminationBudget x (mainCutoffNat x) : ℝ) ≤
          600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := hsum
      _ ≤ 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
        have hr : 0 ≤ (x : ℝ) / Real.log (x : ℝ) ^ 7 := by positivity
        calc
          600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 =
              600 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) := by ring
          _ ≤ 1000 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) :=
            mul_le_mul_of_nonneg_right (by norm_num) hr
          _ = 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by ring
  have hceil : 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 ≤
      (proposition6DeletionBudget x : ℝ) := Nat.le_ceil _
  exact_mod_cast htarget.trans hceil

/-! ## Moving terminal intervals -/

private def movingEndpoint (x : ℕ) : ℕ :=
  ⌊Proposition4.martinLowerRatio x * (x : ℝ)⌋₊

lemma movingEndpoint_ratio_tendsto :
    Tendsto (fun x : ℕ ↦ (movingEndpoint x : ℝ) / (x : ℝ)) atTop
      (nhds (Real.exp (-1))) := by
  simpa [movingEndpoint] using Proposition4.martinLowerEndpoint_floor_ratio_tendsto

lemma movingEndpoint_tendsto_atTop : Tendsto movingEndpoint atTop atTop := by
  have hbase : Tendsto
      (fun x : ℕ ↦ ⌊oneLowerRatio * (x : ℝ)⌋₊) atTop atTop :=
    floorOneEndpoint_tendsto_atTop
  apply tendsto_atTop.2
  intro b
  filter_upwards [hbase.eventually (eventually_ge_atTop b),
    Proposition4.eventually_martinLowerRatio_bounds] with x hb halpha
  exact hb.trans (Nat.floor_mono
    (mul_le_mul_of_nonneg_right halpha.1.le (Nat.cast_nonneg x)))

lemma movingFullInitialInterval_reciprocalMass_tendsto_one :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass
        (fullInitialIntervalAt (Proposition4.martinLowerRatio x) x))
      atTop (nhds 1) := by
  have herrorX := Real.tendsto_harmonic_sub_log
  have herrorA := Real.tendsto_harmonic_sub_log.comp movingEndpoint_tendsto_atTop
  have herror : Tendsto
      (fun x : ℕ ↦
        (((harmonic x : ℚ) : ℝ) - Real.log (x : ℝ)) -
        (((harmonic (movingEndpoint x) : ℚ) : ℝ) -
          Real.log (movingEndpoint x : ℝ)))
      atTop (nhds 0) := by
    simpa using herrorX.sub herrorA
  have hlogratio : Tendsto
      (fun x : ℕ ↦ Real.log ((movingEndpoint x : ℝ) / (x : ℝ)))
      atTop (nhds (-1)) := by
    have h := (Real.continuousAt_log (Real.exp_ne_zero (-1))).tendsto.comp
      movingEndpoint_ratio_tendsto
    simpa [Function.comp_def] using h
  have hlogdiff : Tendsto
      (fun x : ℕ ↦ Real.log (x : ℝ) - Real.log (movingEndpoint x : ℝ))
      atTop (nhds 1) := by
    have h : Tendsto
        (fun x : ℕ ↦ -Real.log ((movingEndpoint x : ℝ) / (x : ℝ)))
        atTop (nhds 1) := by simpa using hlogratio.neg
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      movingEndpoint_tendsto_atTop.eventually (eventually_gt_atTop 0)]
        with x hx hA
    rw [Real.log_div (by positivity) (by positivity)]
    ring
  have htotal := herror.add hlogdiff
  have htotal' : Tendsto
      (fun x : ℕ ↦ ((harmonic x : ℚ) : ℝ) -
        ((harmonic (movingEndpoint x) : ℚ) : ℝ)) atTop (nhds 1) := by
    convert htotal using 1 <;> norm_num
    funext x
    ring
  apply htotal'.congr'
  filter_upwards [Proposition4.eventually_martinLowerRatio_bounds,
    eventually_gt_atTop (0 : ℕ)] with x halpha hx
  have hAle : movingEndpoint x ≤ x := by
    have hreal : (movingEndpoint x : ℝ) ≤ (x : ℝ) :=
      (Nat.floor_le (mul_nonneg
        ((Real.exp_pos (-1)).trans halpha.1).le (Nat.cast_nonneg x))).trans
        (mul_le_of_le_one_left (Nat.cast_nonneg x) halpha.2.le)
    exact_mod_cast hreal
  symm
  simpa [movingEndpoint, fullInitialIntervalAt] using
    reciprocalMass_Ioc_eq_harmonic_sub hAle

lemma movingInitialRoughPart_reciprocalMass_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass
        (initialRoughPartAt (Proposition4.martinLowerRatio x) x))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x ↦ reciprocalMass_nonneg _
  · filter_upwards [Proposition4.eventually_martinLowerRatio_bounds]
      with x halpha
    apply reciprocalMass_mono (B := initialRoughPart x)
    intro n hn
    rw [initialRoughPartAt, mem_roughNumbersIn] at hn
    rw [initialRoughPart, mem_roughNumbersIn]
    refine ⟨?_, hn.2.1, hn.2.2⟩
    have hmul : oneLowerRatio * (x : ℝ) ≤
        Proposition4.martinLowerRatio x * (x : ℝ) := by
      exact mul_le_mul_of_nonneg_right halpha.1.le (Nat.cast_nonneg x)
    have hfloor : ⌊oneLowerRatio * (x : ℝ)⌋₊ ≤
        ⌊Proposition4.martinLowerRatio x * (x : ℝ)⌋₊ :=
      Nat.floor_mono hmul
    omega
  · exact initialRoughPart_reciprocalMass_tendsto_zero

lemma movingInitialBlock_reciprocalMass_tendsto_one :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass
        (initialBlockAt (Proposition4.martinLowerRatio x) x))
      atTop (nhds 1) := by
  have h := movingFullInitialInterval_reciprocalMass_tendsto_one.sub
    movingInitialRoughPart_reciprocalMass_tendsto_zero
  have h' : Tendsto
      (fun x : ℕ ↦
        reciprocalMass (fullInitialIntervalAt (Proposition4.martinLowerRatio x) x) -
          reciprocalMass (initialRoughPartAt (Proposition4.martinLowerRatio x) x))
      atTop (nhds 1) := by simpa using h
  apply h'.congr'
  filter_upwards with x
  rw [initialBlockAt_eq_sdiff,
    reciprocalMass_sdiff (initialRoughPartAt_subset_full _ _)]

lemma movingInitialResidual_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦
        (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ))
      atTop (nhds 0) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop
    (nhds 1)).sub movingInitialBlock_reciprocalMass_tendsto_one
  simpa [initialResidual, initialBlockAt, ratCast_recSum_eq_reciprocalMass] using h

/-! ## Quantitative positive lower margin -/

lemma log_one_add_lower {t : ℝ} (ht0 : 0 ≤ t) :
    t / (1 + t) ≤ Real.log (1 + t) := by
  have hpos : 0 < 1 + t := by linarith
  have hinv : 0 < (1 + t)⁻¹ := inv_pos.mpr hpos
  have h := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv] at h
  have hne : 1 + t ≠ 0 := hpos.ne'
  field_simp at h ⊢
  nlinarith

lemma eventually_moving_full_residual_ge_margin_quarter :
    ∀ᶠ x : ℕ in atTop,
      Proposition4.martinMargin x / 4 ≤
        1 - reciprocalMass
          (fullInitialIntervalAt (Proposition4.martinLowerRatio x) x) := by
  have hmargin0 := Proposition4.martinMargin_tendsto_zero
  have hmargintop := Proposition4.martinMargin_mul_t_tendsto_atTop
  filter_upwards [Proposition4.eventually_martinLowerRatio_bounds,
    Proposition4.martinMargin_pos,
    hmargin0.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hmargintop.eventually (eventually_ge_atTop 2),
    eventually_ge_atTop 3] with x halpha hmpos hmle hmx hx
  let a := movingEndpoint x
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hapos : 0 < a := by
    have hax : (1 : ℝ) ≤ Proposition4.martinMargin x * (x : ℝ) := by
      linarith
    have hbase : 0 ≤ Real.exp (-1) * (x : ℝ) := by positivity
    have hscale : (1 : ℝ) ≤
        Proposition4.martinLowerRatio x * (x : ℝ) := by
      rw [Proposition4.martinLowerRatio]
      nlinarith
    have : 1 ≤ a := by
      change 1 ≤ movingEndpoint x
      rw [movingEndpoint, Nat.one_le_floor_iff]
      exact hscale
    omega
  have hale : a ≤ x := by
    have hreal : (a : ℝ) ≤ (x : ℝ) := by
      dsimp [a, movingEndpoint]
      exact (Nat.floor_le (mul_nonneg
        ((Real.exp_pos (-1)).trans halpha.1).le (Nat.cast_nonneg x))).trans
        (mul_le_of_le_one_left (Nat.cast_nonneg x) halpha.2.le)
    exact_mod_cast hreal
  have heuler :
      ((harmonic x : ℚ) : ℝ) - Real.log (x : ℝ) ≤
        ((harmonic a : ℚ) : ℝ) - Real.log (a : ℝ) := by
    simpa [Real.eulerMascheroniSeq', (show x ≠ 0 by omega),
      (show a ≠ 0 by omega)] using
      Real.strictAnti_eulerMascheroniSeq'.antitone hale
  have hmass : reciprocalMass
      (fullInitialIntervalAt (Proposition4.martinLowerRatio x) x) =
      ((harmonic x : ℚ) : ℝ) - ((harmonic a : ℚ) : ℝ) := by
    simpa [a, movingEndpoint, fullInitialIntervalAt] using
      reciprocalMass_Ioc_eq_harmonic_sub hale
  have hafloor : Proposition4.martinLowerRatio x * (x : ℝ) - 1 ≤
      (a : ℝ) := by
    dsimp [a, movingEndpoint]
    have h := (Nat.lt_floor_add_one
      (Proposition4.martinLowerRatio x * (x : ℝ))).le
    linarith
  have haRatio : Real.exp (-1) + Proposition4.martinMargin x / 2 ≤
      (a : ℝ) / (x : ℝ) := by
    rw [Proposition4.martinLowerRatio] at hafloor
    rw [le_div_iff₀ hxpos]
    have hhalf : (1 : ℝ) ≤ Proposition4.martinMargin x * (x : ℝ) / 2 := by
      linarith
    nlinarith
  have haRatioPos : 0 < (a : ℝ) / (x : ℝ) := div_pos (by exact_mod_cast hapos) hxpos
  have hlogRatio : Real.log (Real.exp (-1) + Proposition4.martinMargin x / 2) ≤
      Real.log ((a : ℝ) / (x : ℝ)) :=
    Real.log_le_log (by positivity) haRatio
  let t : ℝ := Real.exp 1 * Proposition4.martinMargin x / 2
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ Real.exp 1 / 2 := by
    dsimp [t]
    exact div_le_div_of_nonneg_right
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hmle.le (Real.exp_pos (1 : ℝ)).le)
      (by norm_num)
  have htDiv : Proposition4.martinMargin x / 4 ≤ t / (1 + t) := by
    have hden : 1 + t ≤ Real.exp 1 := by
      dsimp [t]
      have hexp2 : (2 : ℝ) ≤ Real.exp 1 := by
        linarith [Real.exp_one_gt_d9]
      nlinarith
    have htEq : t = Real.exp 1 * Proposition4.martinMargin x / 2 := rfl
    rw [htEq]
    have htpos : 0 < 1 + t := by dsimp [t]; positivity
    apply (le_div_iff₀ htpos).2
    calc
      Proposition4.martinMargin x / 4 * (1 + t) ≤
          Proposition4.martinMargin x / 4 * Real.exp 1 :=
        mul_le_mul_of_nonneg_left hden (div_nonneg hmpos.le (by norm_num))
      _ ≤ Real.exp 1 * Proposition4.martinMargin x / 2 := by
        nlinarith [Real.exp_pos (1 : ℝ), hmpos]
  have hlogLower : Proposition4.martinMargin x / 4 ≤ Real.log (1 + t) :=
    htDiv.trans (log_one_add_lower ht0)
  have hfactor : Real.exp (-1) + Proposition4.martinMargin x / 2 =
      Real.exp (-1) * (1 + t) := by
    dsimp [t]
    have hexp : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      norm_num
    calc
      Real.exp (-1) + Proposition4.martinMargin x / 2 =
          Real.exp (-1) +
            (Real.exp (-1) * Real.exp 1) * Proposition4.martinMargin x / 2 := by
        rw [hexp, one_mul]
      _ = Real.exp (-1) *
          (1 + Real.exp 1 * Proposition4.martinMargin x / 2) := by ring
  have hlogGap : Proposition4.martinMargin x / 4 ≤
      1 + Real.log ((a : ℝ) / (x : ℝ)) := by
    calc
      Proposition4.martinMargin x / 4 ≤ Real.log (1 + t) := hlogLower
      _ = 1 + Real.log (Real.exp (-1) + Proposition4.martinMargin x / 2) := by
        rw [hfactor, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp]
        ring
      _ ≤ 1 + Real.log ((a : ℝ) / (x : ℝ)) := by linarith
  rw [hmass]
  have haRne : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hapos)
  rw [Real.log_div haRne hxpos.ne'] at hlogGap
  have htail : ((harmonic x : ℚ) : ℝ) - ((harmonic a : ℚ) : ℝ) ≤
      Real.log (x : ℝ) - Real.log (a : ℝ) := by linarith
  linarith

/-! ## The moving errors are smaller than the positive margin -/

lemma eventually_moving_budget_ratio_le_log_pow :
    ∀ᶠ x : ℕ in atTop,
      (proposition6DeletionBudget x : ℝ) /
          (Real.exp (-1) * (x : ℝ)) ≤
        (1001 / Real.exp (-1)) * (Real.log (x : ℝ) ^ 7)⁻¹ := by
  have hscale : Tendsto
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ) ^ 7) atTop atTop := by
    have h := (UnitFractions.tendsto_mul_add_div_pow_log_at_top
      (1 : ℝ) 0 7 zero_lt_one).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  filter_upwards [hscale.eventually (eventually_ge_atTop 1), eventually_ge_atTop 3]
      with x hscale1 hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hceil : (proposition6DeletionBudget x : ℝ) ≤
      1001 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    calc
      (proposition6DeletionBudget x : ℝ) ≤
          1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      _ = 1000 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) + 1 := by ring
      _ ≤ 1000 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) +
          ((x : ℝ) / Real.log (x : ℝ) ^ 7) := by
        exact add_le_add (le_refl _) hscale1
      _ = 1001 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by ring
  calc
    (proposition6DeletionBudget x : ℝ) /
        (Real.exp (-1) * (x : ℝ)) ≤
      (1001 * (x : ℝ) / Real.log (x : ℝ) ^ 7) /
        (Real.exp (-1) * (x : ℝ)) := by
      exact div_le_div_of_nonneg_right hceil (by positivity)
    _ = (1001 / Real.exp (-1)) * (Real.log (x : ℝ) ^ 7)⁻¹ := by
      field_simp

lemma moving_errors_div_margin_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦
        ((Real.log (x : ℝ))⁻¹ +
          4 * ((proposition6DeletionBudget x : ℝ) /
            (Real.exp (-1) * (x : ℝ)))) /
          Proposition4.martinMargin x)
      atTop (nhds 0) := by
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    tendsto_log_coe_at_top
  have hfirst : Tendsto
      (fun x : ℕ ↦ (Real.sqrt (Real.log (x : ℝ)))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hlogTop)
  have hsecond : Tendsto
      (fun x : ℕ ↦ (1001 / Real.exp (-1)) *
        Real.log (x : ℝ) ^ (-(13 : ℝ) / 2)) atTop (nhds 0) := by
    have hpow := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 13 / 2)).comp hlogTop
    convert hpow.const_mul (1001 / Real.exp (-1)) using 1 <;> norm_num
  have hupper := hfirst.add (hsecond.const_mul 4)
  apply squeeze_zero' (g := fun x : ℕ ↦
    (Real.sqrt (Real.log (x : ℝ)))⁻¹ +
      4 * ((1001 / Real.exp (-1)) *
        Real.log (x : ℝ) ^ (-(13 : ℝ) / 2)))
  · filter_upwards [eventually_ge_atTop 3,
      Proposition4.eventually_martinLowerRatio_bounds,
      Proposition4.martinMargin_pos] with x hx halpha hm
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have halphapos : 0 < Proposition4.martinLowerRatio x :=
      (Real.exp_pos _).trans halpha.1
    have hlognonneg : 0 ≤ Real.log (x : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
    exact div_nonneg
      (add_nonneg (inv_nonneg.mpr hlognonneg)
        (mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (Real.exp_pos (-1)).le hxpos.le)))) hm.le
  · filter_upwards [eventually_moving_budget_ratio_le_log_pow,
      eventually_ge_atTop 3, Proposition4.martinMargin_pos]
      with x hbudget hx hm
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.2 hlog
    have hmargin : Proposition4.martinMargin x =
        (Real.sqrt (Real.log (x : ℝ)))⁻¹ := rfl
    have hbudget' := mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ 4)
    have hpowid : (Real.log (x : ℝ) ^ 7)⁻¹ *
        Real.sqrt (Real.log (x : ℝ)) =
        Real.log (x : ℝ) ^ (-(13 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (Real.log (x : ℝ)) 7,
        ← Real.rpow_neg hlog.le, Real.sqrt_eq_rpow]
      rw [← Real.rpow_add hlog]
      norm_num
    rw [hmargin, div_inv_eq_mul, add_mul]
    have hfirstId : (Real.log (x : ℝ))⁻¹ *
        Real.sqrt (Real.log (x : ℝ)) =
        (Real.sqrt (Real.log (x : ℝ)))⁻¹ := by
      field_simp [hsqrt.ne', hlog.ne']
      rw [Real.sq_sqrt hlog.le]
    have hbmul := mul_le_mul_of_nonneg_right hbudget' hsqrt.le
    calc
      (Real.log (x : ℝ))⁻¹ * Real.sqrt (Real.log (x : ℝ)) +
          (4 * ((proposition6DeletionBudget x : ℝ) /
            (Real.exp (-1) * (x : ℝ)))) *
            Real.sqrt (Real.log (x : ℝ)) ≤
        (Real.sqrt (Real.log (x : ℝ)))⁻¹ +
          (4 * ((1001 / Real.exp (-1)) * (Real.log (x : ℝ) ^ 7)⁻¹)) *
            Real.sqrt (Real.log (x : ℝ)) := by
              rw [hfirstId]
              simpa [add_comm] using
                add_le_add_left hbmul (Real.sqrt (Real.log (x : ℝ)))⁻¹
      _ = (Real.sqrt (Real.log (x : ℝ)))⁻¹ +
          4 * ((1001 / Real.exp (-1)) *
            Real.log (x : ℝ) ^ (-(13 : ℝ) / 2)) := by
              rw [← hpowid]
              ring
  · simpa using hupper

theorem eventually_moving_initial_residual_margins :
    ∀ᶠ x : ℕ in atTop,
      (Real.log (x : ℝ))⁻¹ +
          4 * ((proposition6DeletionBudget x : ℝ) /
            (Real.exp (-1) * (x : ℝ))) <
        (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ) ∧
      (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ) +
          (proposition6DeletionBudget x : ℝ) /
            (Proposition4.martinLowerRatio x * (x : ℝ)) < 1 := by
  have hnormalized := moving_errors_div_margin_tendsto_zero.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have hbudgetZero : Tendsto
      (fun x : ℕ ↦ (proposition6DeletionBudget x : ℝ) /
        (Proposition4.martinLowerRatio x * (x : ℝ))) atTop (nhds 0) := by
    have hupper : Tendsto
        (fun x : ℕ ↦ (1001 / Real.exp (-1)) *
          (Real.log (x : ℝ) ^ 7)⁻¹) atTop (nhds 0) := by
      have htop := (tendsto_pow_atTop (by norm_num : (7 : ℕ) ≠ 0)).comp
        tendsto_log_coe_at_top
      simpa using (tendsto_inv_atTop_zero.comp htop).const_mul
        (1001 / Real.exp (-1))
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop 1,
        Proposition4.eventually_martinLowerRatio_bounds] with x hx ha
      have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
      have hapos : 0 < Proposition4.martinLowerRatio x :=
        (Real.exp_pos _).trans ha.1
      exact div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg hapos.le hxpos.le)
    · filter_upwards [eventually_moving_budget_ratio_le_log_pow,
        Proposition4.eventually_martinLowerRatio_bounds,
        eventually_ge_atTop 1] with x hfixed halpha hx
      have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
      have hden : Real.exp (-1) * (x : ℝ) ≤
          Proposition4.martinLowerRatio x * (x : ℝ) :=
        mul_le_mul_of_nonneg_right halpha.1.le hxpos.le
      exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (mul_pos (Real.exp_pos _) hxpos) hden).trans hfixed
    · exact hupper
  have hsum : Tendsto
      (fun x : ℕ ↦
        (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ) +
        (proposition6DeletionBudget x : ℝ) /
          (Proposition4.martinLowerRatio x * (x : ℝ)))
      atTop (nhds 0) := by
    simpa using movingInitialResidual_tendsto_zero.add hbudgetZero
  have hupper := hsum.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_moving_full_residual_ge_margin_quarter,
    hnormalized, hupper, Proposition4.martinMargin_pos]
      with x hfull hnorm hup hm
  constructor
  · have herr : (Real.log (x : ℝ))⁻¹ +
        4 * ((proposition6DeletionBudget x : ℝ) /
          (Real.exp (-1) * (x : ℝ))) <
        Proposition4.martinMargin x / 4 := by
      rw [div_lt_iff₀ hm] at hnorm
      nlinarith
    have hsmoothLeFull : reciprocalMass
        (initialBlockAt (Proposition4.martinLowerRatio x) x) ≤
        reciprocalMass
          (fullInitialIntervalAt (Proposition4.martinLowerRatio x) x) := by
      exact reciprocalMass_mono (by
        rw [initialBlockAt_eq_sdiff]
        exact Finset.sdiff_subset)
    have hres : Proposition4.martinMargin x / 4 ≤
        (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ) := by
      rw [initialResidual]
      rw [Rat.cast_sub, Rat.cast_one]
      rw [ratCast_recSum_eq_reciprocalMass]
      change Proposition4.martinMargin x / 4 ≤
        1 - reciprocalMass (initialBlockAt (Proposition4.martinLowerRatio x) x)
      linarith
    exact herr.trans_le hres
  · exact hup

/-! ## Final bundled form -/

/-- The three moving estimates consumed by the final Proposition 6
constructor.  The lower error is stated with the fixed lower bound
`exp (-1)`, while the upper error retains the sharper moving denominator. -/
theorem eventually_moving_proposition6_bounds :
    ∀ᶠ x : ℕ in atTop,
      (Real.log (x : ℝ))⁻¹ +
          4 * ((proposition6DeletionBudget x : ℝ) /
            (Real.exp (-1) * (x : ℝ))) <
        (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ) ∧
      (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ) +
          (proposition6DeletionBudget x : ℝ) /
            (Proposition4.martinLowerRatio x * (x : ℝ)) < 1 ∧
      totalEliminationBudget x ⌊proposition6MainCutoff x⌋₊ ≤
        proposition6DeletionBudget x := by
  filter_upwards [eventually_moving_initial_residual_margins,
    eventually_totalEliminationBudget_mainCutoff_le] with x hmargins hbudget
  simpa [mainCutoffNat_eq] using ⟨hmargins.1, hmargins.2, hbudget⟩

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/LastCrossing.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős 285: exact-cardinality scale selection

This file isolates the ``last scale below the requested cardinality'' argument.
No monotonicity of the source count is assumed.  The only local input is an
upper bound for a positive one-step jump.  This is useful for converting a
density theorem for a finite source block into an exact-cardinality theorem.

The final section also records the slowly varying surplus parameter used in
the alternative variable-endpoint implementation of Proposition 4.
-/

namespace LastCrossing

open Filter Finset Real Asymptotics
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The last admissible scale -/

/-- Scales no larger than `M t` whose source count has not yet exceeded `t`. -/
def admissibleScales (s M : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (range (M t + 1)).filter fun x ↦ s x ≤ t

lemma zero_mem_admissibleScales {s M : ℕ → ℕ} (hs0 : s 0 = 0) (t : ℕ) :
    0 ∈ admissibleScales s M t := by
  simp [admissibleScales, hs0]

/-- The largest admissible scale.  The harmless value `0` is used only when
the admissible set is empty; all applications have `s 0 = 0`.-/
def lastBelow (s M : ℕ → ℕ) (t : ℕ) : ℕ :=
  if h : (admissibleScales s M t).Nonempty then
    (admissibleScales s M t).max' h
  else 0

lemma lastBelow_mem {s M : ℕ → ℕ} (hs0 : s 0 = 0) (t : ℕ) :
    lastBelow s M t ∈ admissibleScales s M t := by
  rw [lastBelow]
  split_ifs with h
  · exact Finset.max'_mem _ h
  · exact (h ⟨0, zero_mem_admissibleScales hs0 t⟩).elim

lemma lastBelow_le_cap {s M : ℕ → ℕ} (hs0 : s 0 = 0) (t : ℕ) :
    lastBelow s M t ≤ M t := by
  have h := lastBelow_mem (s := s) (M := M) hs0 t
  simp only [admissibleScales, mem_filter, mem_range] at h
  omega

lemma sourceCount_lastBelow_le {s M : ℕ → ℕ} (hs0 : s 0 = 0) (t : ℕ) :
    s (lastBelow s M t) ≤ t := by
  have h := lastBelow_mem (s := s) (M := M) hs0 t
  exact (by simpa [admissibleScales] using h :
    lastBelow s M t ≤ M t ∧ s (lastBelow s M t) ≤ t).2

/-- Maximality, phrased without a monotonicity assumption on `s`. -/
lemma le_lastBelow_of_le_cap_of_sourceCount_le {s M : ℕ → ℕ}
    {t y : ℕ} (hyM : y ≤ M t) (hys : s y ≤ t) :
    y ≤ lastBelow s M t := by
  have hy : y ∈ admissibleScales s M t := by
    simp only [admissibleScales, mem_filter, mem_range]
    exact ⟨by omega, hys⟩
  rw [lastBelow]
  split_ifs with h
  · exact Finset.le_max' _ _ hy
  · exact (h ⟨y, hy⟩).elim

lemma lastBelow_lt_cap_of_sourceCount_cap_gt {s M : ℕ → ℕ}
    (hs0 : s 0 = 0) {t : ℕ} (hcap : t < s (M t)) :
    lastBelow s M t < M t := by
  have hle := lastBelow_le_cap (s := s) (M := M) hs0 t
  exact hle.lt_of_ne fun h ↦ by
    have hsle := sourceCount_lastBelow_le (s := s) (M := M) hs0 t
    rw [h] at hsle
    exact (not_lt_of_ge hsle) hcap

lemma sourceCount_succ_lastBelow_gt {s M : ℕ → ℕ}
    (hs0 : s 0 = 0) {t : ℕ} (hcap : t < s (M t)) :
    t < s (lastBelow s M t + 1) := by
  have hlt := lastBelow_lt_cap_of_sourceCount_cap_gt (s := s) (M := M) hs0 hcap
  by_contra h
  have hs : s (lastBelow s M t + 1) ≤ t := Nat.le_of_not_gt h
  have hmax := le_lastBelow_of_le_cap_of_sourceCount_le (s := s) (M := M)
    (show lastBelow s M t + 1 ≤ M t by omega) hs
  omega

/-! ## Asymptotic inversion -/

lemma lastBelow_tendsto_atTop {s M : ℕ → ℕ}
    (_hs0 : s 0 = 0) (hM : Tendsto M atTop atTop) :
    Tendsto (lastBelow s M) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro y
  obtain ⟨a, ha⟩ := (tendsto_atTop_atTop.mp hM) y
  refine ⟨max a (s y), fun t ht ↦ ?_⟩
  apply le_lastBelow_of_le_cap_of_sourceCount_le
  · exact ha t (le_trans (le_max_left _ _) ht)
  · exact le_trans (le_max_right _ _) ht

lemma eventually_deficit_lastBelow_le_jump {s M J : ℕ → ℕ}
    (hs0 : s 0 = 0) (hM : Tendsto M atTop atTop)
    (hcross : ∀ᶠ t in atTop, t < s (M t))
    (hjump : ∀ᶠ x in atTop, s (x + 1) ≤ s x + J x) :
    ∀ᶠ t in atTop, t - s (lastBelow s M t) ≤ J (lastBelow s M t) := by
  have hxtop := lastBelow_tendsto_atTop (s := s) (M := M) hs0 hM
  have hjumpx : ∀ᶠ t in atTop,
      s (lastBelow s M t + 1) ≤
        s (lastBelow s M t) + J (lastBelow s M t) := hxtop.eventually hjump
  filter_upwards [hcross, hjumpx] with t hcap hj
  have hnext := sourceCount_succ_lastBelow_gt (s := s) (M := M) hs0 hcap
  omega

/-! A canonical cap when no explicit quantitative cap is convenient. -/

/-- The least scale at which `s` exceeds `t`. -/
def firstAbove (s : ℕ → ℕ) (hunbounded : ∀ t, ∃ x, t < s x) (t : ℕ) : ℕ :=
  Nat.find (hunbounded t)

lemma firstAbove_spec {s : ℕ → ℕ} {hunbounded : ∀ t, ∃ x, t < s x} (t : ℕ) :
    t < s (firstAbove s hunbounded t) :=
  Nat.find_spec (hunbounded t)

/-- The first crossing escapes every finite prefix. -/
lemma firstAbove_tendsto_atTop {s : ℕ → ℕ} (hunbounded : ∀ t, ∃ x, t < s x) :
    Tendsto (firstAbove s hunbounded) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro y
  let B : ℕ := ∑ i ∈ range (y + 1), s i
  refine ⟨B, fun t ht ↦ ?_⟩
  by_contra hnot
  have hMle : firstAbove s hunbounded t ≤ y := Nat.le_of_not_ge hnot
  have hmem : firstAbove s hunbounded t ∈ range (y + 1) := by simpa using hMle
  have hsingle : s (firstAbove s hunbounded t) ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hmem
  have hcross := firstAbove_spec (s := s) (hunbounded := hunbounded) t
  omega

/-- Generic nonmonotone inversion theorem with an arbitrary cap tending to
infinity.  The crossing is kept explicit because this is the most convenient
finite interface for applications. -/
theorem lastBelow_ratio_tendsto_of_cap_tendsto
    {s M J : ℕ → ℕ} {d : ℝ}
    (hs0 : s 0 = 0) (hd : 0 < d) (hMtop : Tendsto M atTop atTop)
    (hs : Tendsto (fun x : ℕ ↦ (s x : ℝ) / (x : ℝ)) atTop (nhds d))
    (hcross : ∀ᶠ t in atTop, t < s (M t))
    (hjump : ∀ᶠ x in atTop, s (x + 1) ≤ s x + J x)
    (hJ : (fun x : ℕ ↦ (J x : ℝ)) =o[atTop] (fun x : ℕ ↦ (x : ℝ))) :
    Tendsto (fun t : ℕ ↦ (lastBelow s M t : ℝ) / (t : ℝ))
      atTop (nhds d⁻¹) := by
  have hxtop : Tendsto (lastBelow s M) atTop atTop := lastBelow_tendsto_atTop hs0 hMtop
  have hsx : Tendsto
      (fun t : ℕ ↦ (s (lastBelow s M t) : ℝ) / (lastBelow s M t : ℝ))
      atTop (nhds d) := hs.comp hxtop
  have hJratio : Tendsto (fun x : ℕ ↦ (J x : ℝ) / (x : ℝ))
      atTop (nhds 0) := hJ.tendsto_div_nhds_zero
  have hJx := hJratio.comp hxtop
  have hsum : Tendsto
      (fun t : ℕ ↦
        (s (lastBelow s M t) : ℝ) / (lastBelow s M t : ℝ) +
          (J (lastBelow s M t) : ℝ) / (lastBelow s M t : ℝ))
      atTop (nhds d) := by simpa using hsx.add hJx
  have hlower := hsum.inv₀ hd.ne'
  have hupper := hsx.inv₀ hd.ne'
  have hjumpx : ∀ᶠ t in atTop,
      s (lastBelow s M t + 1) ≤
        s (lastBelow s M t) + J (lastBelow s M t) := hxtop.eventually hjump
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hcross, hxtop.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop 1, hjumpx] with t hcap hx ht hj
    have hstep := sourceCount_succ_lastBelow_gt (s := s) (M := M) hs0 hcap
    have hxR : (0 : ℝ) < lastBelow s M t := by exact_mod_cast hx
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have hreal : (t : ℝ) < (s (lastBelow s M t) : ℝ) + J (lastBelow s M t) := by
      exact_mod_cast hstep.trans_le hj
    rw [show (s (lastBelow s M t) : ℝ) / (lastBelow s M t : ℝ) +
        (J (lastBelow s M t) : ℝ) / (lastBelow s M t : ℝ) =
        ((s (lastBelow s M t) : ℝ) + J (lastBelow s M t)) /
          (lastBelow s M t : ℝ) by ring, inv_div]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) htR hreal.le
  · filter_upwards [hxtop.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop 1, hsx.eventually (Ioi_mem_nhds (show d / 2 < d by linarith))]
      with t hx ht hspos
    have hsle := sourceCount_lastBelow_le (s := s) (M := M) hs0 t
    have hxR : (0 : ℝ) < lastBelow s M t := by exact_mod_cast hx
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have hsR : (0 : ℝ) < s (lastBelow s M t) := by
      have hratioPos : 0 < (s (lastBelow s M t) : ℝ) /
          (lastBelow s M t : ℝ) := (show 0 < d / 2 by positivity).trans hspos
      rcases div_pos_iff.mp hratioPos with h | h
      · exact h.1
      · exact (not_lt_of_ge hxR.le h.2).elim
    rw [inv_div]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hsR (by exact_mod_cast hsle)

/-! ## A slowly varying surplus parameter -/

/-! ## One-step control for the logarithmic smoothness cutoff -/

/-- The real scale before rounding in `mainCutoffNat`. -/
def mainCutoffScale (x : ℕ) : ℝ :=
  (x : ℝ) / Real.log (x : ℝ) ^ 30

@[simp] lemma mainCutoffNat_eq_floor_scale (x : ℕ) :
    mainCutoffNat x = ⌊mainCutoffScale x⌋₊ := rfl

/-- Although no global monotonicity is needed, the logarithmic cutoff can
increase by at most one in one step once `log x > 1`. -/
theorem eventually_mainCutoffNat_succ_le :
    ∀ᶠ x : ℕ in atTop, mainCutoffNat (x + 1) ≤ mainCutoffNat x + 1 := by
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ))]
    with x hlog
  have hxR : (0 : ℝ) < x := by
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    exact zero_lt_one.trans ((Real.log_pos_iff hx0).mp (zero_lt_one.trans hlog))
  have hxsuccR : (0 : ℝ) < (x + 1 : ℕ) := by positivity
  have hlogmono : Real.log (x : ℝ) ≤ Real.log (x + 1 : ℕ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hxR) (Set.mem_Ioi.mpr hxsuccR) (by exact_mod_cast Nat.le_succ x)
  have hpowpos : 0 < Real.log (x : ℝ) ^ 30 := pow_pos (zero_lt_one.trans hlog) _
  have hpowle : Real.log (x : ℝ) ^ 30 ≤ Real.log (x + 1 : ℕ) ^ 30 := by
    exact pow_le_pow_left₀ (zero_lt_one.trans hlog).le hlogmono _
  have hscaleStep : mainCutoffScale (x + 1) < mainCutoffScale x + 1 := by
    calc
      mainCutoffScale (x + 1) ≤ (x + 1 : ℕ) / Real.log (x : ℝ) ^ 30 := by
        dsimp [mainCutoffScale]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpowpos hpowle
      _ = mainCutoffScale x + (Real.log (x : ℝ) ^ 30)⁻¹ := by
        dsimp [mainCutoffScale]
        push_cast
        field_simp
      _ < mainCutoffScale x + 1 := by
        gcongr
        exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hlog (by norm_num))
  rw [mainCutoffNat_eq_floor_scale, mainCutoffNat_eq_floor_scale]
  apply Nat.lt_succ_iff.mp
  have hscale0 : 0 ≤ mainCutoffScale (x + 1) := by
    exact div_nonneg (Nat.cast_nonneg _)
      (pow_nonneg ((zero_lt_one.trans hlog).le.trans hlogmono) _)
  rw [Nat.floor_lt hscale0]
  calc
    mainCutoffScale (x + 1) < mainCutoffScale x + 1 := hscaleStep
    _ < ((⌊mainCutoffScale x⌋₊ + 1 + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.lt_floor_add_one (mainCutoffScale x)]

/-- A convenient global majorant for the one-step score jump.  The quotient
is the number of multiples of the sole newly allowed cutoff value; the
constant covers the moving endpoints, the new right endpoint, and the
two-term prime-power correction. -/
def logarithmicStepJump (x : ℕ) : ℕ :=
  5 + x / (mainCutoffNat x + 1)

lemma logarithmicStepJump_isLittleO :
    (fun x : ℕ ↦ (logarithmicStepJump x : ℝ))
      =o[atTop] (fun x : ℕ ↦ (x : ℝ)) := by
  have hQtop : Tendsto (fun x : ℕ ↦ mainCutoffNat x + 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨a, ha⟩ := (tendsto_atTop_atTop.mp mainCutoffNat_spec.2.1) b
    exact ⟨a, fun x hx ↦ (ha x hx).trans (Nat.le_add_right _ _)⟩
  have hinv : Tendsto (fun x : ℕ ↦ ((mainCutoffNat x + 1 : ℕ) : ℝ)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hQtop)
  have hconst : Tendsto (fun x : ℕ ↦ (5 : ℝ) / (x : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hupper := hconst.add hinv
  have hratio : Tendsto
      (fun x : ℕ ↦ (logarithmicStepJump x : ℝ) / (x : ℝ)) atTop (nhds 0) := by
    apply squeeze_zero' (g := fun x : ℕ ↦
      (5 : ℝ) / (x : ℝ) + ((mainCutoffNat x + 1 : ℕ) : ℝ)⁻¹)
    · filter_upwards [eventually_ge_atTop 1] with x hx
      positivity
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
      have hdiv : ((x / (mainCutoffNat x + 1) : ℕ) : ℝ) ≤
          (x : ℝ) / (mainCutoffNat x + 1 : ℕ) := Nat.cast_div_le
      rw [logarithmicStepJump, Nat.cast_add]
      calc
        ((5 : ℝ) + (x / (mainCutoffNat x + 1) : ℕ)) / (x : ℝ) ≤
            ((5 : ℝ) + (x : ℝ) / (mainCutoffNat x + 1 : ℕ)) /
              (x : ℝ) := div_le_div_of_nonneg_right (by linarith) hxR.le
        _ = (5 : ℝ) / (x : ℝ) +
            ((mainCutoffNat x + 1 : ℕ) : ℝ)⁻¹ := by
          have hq : ((mainCutoffNat x + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp
    · simpa using hupper
  exact (Asymptotics.isLittleO_iff_tendsto' (by
    filter_upwards [eventually_ge_atTop 1] with x hx
    intro hzero
    exact ((show (x : ℝ) ≠ 0 by exact_mod_cast (show x ≠ 0 by omega)) hzero).elim)).2
      hratio

/-- The one-step jump is eventually much smaller than the deletion budget.
This is the quantitative comparison needed before applying the five-prime
reservoir capacity theorem. -/
theorem eventually_logarithmicStepJump_le_deletionBudget :
    ∀ᶠ x : ℕ in atTop, logarithmicStepJump x ≤ proposition6DeletionBudget x := by
  have hscale7 : Tendsto
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ) ^ 7) atTop atTop := by
    have h := (UnitFractions.tendsto_mul_add_div_pow_log_at_top
      (1 : ℝ) 0 7 zero_lt_one).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hscale37 : Tendsto
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ) ^ 37) atTop atTop := by
    have h := (UnitFractions.tendsto_mul_add_div_pow_log_at_top
      (1 : ℝ) 0 37 zero_lt_one).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hQratio := RoughCounts.logPowerCutoff_ratio_tendsto_one 30
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ)),
    hscale7.eventually (eventually_ge_atTop (1 : ℝ)),
    hscale37.eventually (eventually_ge_atTop (1 : ℝ)),
    hQratio.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
      with x hlog h7 h37 hQratioHalf
  have hxR : (0 : ℝ) < x := by
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    exact zero_lt_one.trans ((Real.log_pos_iff hx0).mp (zero_lt_one.trans hlog))
  have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans hlog
  have hpow7 : 0 < Real.log (x : ℝ) ^ 7 := pow_pos hlogpos _
  have hpow30 : 0 < Real.log (x : ℝ) ^ 30 := pow_pos hlogpos _
  have hscalePos : 0 < (x : ℝ) / Real.log (x : ℝ) ^ 30 :=
    div_pos hxR hpow30
  have hQlower : (x : ℝ) / (2 * Real.log (x : ℝ) ^ 30) ≤
      (mainCutoffNat x : ℝ) := by
    have hhalf : (1 / 2 : ℝ) *
        ((x : ℝ) / Real.log (x : ℝ) ^ 30) < mainCutoffNat x := by
      change (1 / 2 : ℝ) < (mainCutoffNat x : ℝ) /
        ((x : ℝ) / Real.log (x : ℝ) ^ 30) at hQratioHalf
      rwa [lt_div_iff₀ hscalePos] at hQratioHalf
    calc
      (x : ℝ) / (2 * Real.log (x : ℝ) ^ 30) =
          (1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ) ^ 30) := by ring
      _ ≤ (mainCutoffNat x : ℝ) := hhalf.le
  have hquotient : ((x / (mainCutoffNat x + 1) : ℕ) : ℝ) ≤
      2 * Real.log (x : ℝ) ^ 30 := by
    have hcastDiv : ((x / (mainCutoffNat x + 1) : ℕ) : ℝ) ≤
        (x : ℝ) / (mainCutoffNat x + 1 : ℕ) := Nat.cast_div_le
    have hden : (x : ℝ) / (2 * Real.log (x : ℝ) ^ 30) ≤
        (mainCutoffNat x + 1 : ℕ) := hQlower.trans (by norm_num)
    calc
      ((x / (mainCutoffNat x + 1) : ℕ) : ℝ) ≤
          (x : ℝ) / (mainCutoffNat x + 1 : ℕ) := hcastDiv
      _ ≤ (x : ℝ) / ((x : ℝ) / (2 * Real.log (x : ℝ) ^ 30)) := by
        exact div_le_div_of_nonneg_left hxR.le (div_pos hxR (mul_pos (by norm_num) hpow30)) hden
      _ = 2 * Real.log (x : ℝ) ^ 30 := by field_simp
  have hlog37le : Real.log (x : ℝ) ^ 37 ≤ (x : ℝ) := by
    rw [le_div_iff₀ (pow_pos hlogpos 37)] at h37
    simpa using h37
  have hlog30le : Real.log (x : ℝ) ^ 30 ≤
      (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    rw [le_div_iff₀ hpow7]
    rw [← pow_add]
    norm_num
    exact hlog37le
  have hjumpCast : (logarithmicStepJump x : ℝ) ≤
      1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    rw [logarithmicStepJump, Nat.cast_add]
    calc
      (5 : ℝ) + (x / (mainCutoffNat x + 1) : ℕ) ≤
          5 + 2 * Real.log (x : ℝ) ^ 30 := by linarith
      _ ≤ 5 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) +
          2 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) := by nlinarith
      _ ≤ 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
        have hsnonneg : 0 ≤ (x : ℝ) / Real.log (x : ℝ) ^ 7 := by positivity
        rw [show 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 =
          1000 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) by ring]
        nlinarith
  have hceil : 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 ≤
      (proposition6DeletionBudget x : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hjumpCast.trans hceil

end

end LastCrossing

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/ScoreCrossing.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős 285: the concrete last-crossing score

This file instantiates the nonmonotone inversion theorem from
`LastCrossing.lean` with the moving smooth block and exact-correction score
defined in `Proposition4.lean`.
-/

namespace ScoreCrossing

open Filter Finset Real Asymptotics
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open RoughCounts

/-! ## Motion of the lower endpoint -/

lemma log_succ_sub_log_le_inv {x : ℕ} (hx : 0 < x) :
    Real.log (x + 1 : ℕ) - Real.log (x : ℝ) ≤ (x : ℝ)⁻¹ := by
  have h := Analytic.log_succ_ratio_le_reciprocal hx
  rw [Real.log_div (by positivity) (by positivity)] at h
  simpa [one_div] using h

/-- The slowly varying contribution `x/sqrt(log x)` is eventually
nondecreasing. -/
lemma eventually_weighted_martinMargin_mono :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * Proposition4.martinMargin x ≤
        (x + 1 : ℕ) * Proposition4.martinMargin (x + 1) := by
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ))]
    with x hlog
  have hxNat : 0 < x := by
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    have hx1 := (Real.log_pos_iff hx0).mp (zero_lt_one.trans hlog)
    exact_mod_cast (zero_lt_one.trans hx1)
  have hx : (0 : ℝ) < x := by exact_mod_cast hxNat
  have hlogSucc : 0 < Real.log (x + 1 : ℕ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < x + 1 by omega))
  have hlogDiff := log_succ_sub_log_le_inv hxNat
  have hsq : (x : ℝ) ^ 2 * Real.log (x + 1 : ℕ) ≤
      ((x + 1 : ℕ) : ℝ) ^ 2 * Real.log (x : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlogDiff (sq_nonneg (x : ℝ))
    have hxinv : (x : ℝ) ^ 2 * (x : ℝ)⁻¹ = x := by field_simp
    have hinc : (x : ℝ) ^ 2 *
        (Real.log (x + 1 : ℕ) - Real.log (x : ℝ)) ≤ x := by
      simpa [hxinv] using hmul
    have hinc' : (x : ℝ) ^ 2 *
        (Real.log ((x : ℝ) + 1) - Real.log (x : ℝ)) ≤ x := by
      simpa only [Nat.cast_add, Nat.cast_one] using hinc
    have hterm : (x : ℝ) ≤ (2 * x + 1) * Real.log x := by
      calc
        (x : ℝ) ≤ (2 * x + 1) * 1 := by nlinarith
        _ ≤ (2 * x + 1) * Real.log x := by
          gcongr
    push_cast
    calc
      (x : ℝ) ^ 2 * Real.log ((x : ℝ) + 1) =
          (x : ℝ) ^ 2 * Real.log (x : ℝ) +
            (x : ℝ) ^ 2 *
              (Real.log ((x : ℝ) + 1) - Real.log (x : ℝ)) := by ring
      _ ≤ (x : ℝ) ^ 2 * Real.log (x : ℝ) + x := by linarith
      _ ≤ ((x : ℝ) + 1) ^ 2 * Real.log (x : ℝ) := by
        nlinarith
  have hleft0 : 0 ≤ (x : ℝ) * Real.sqrt (Real.log (x + 1 : ℕ)) := by positivity
  have hright0 : 0 ≤ ((x + 1 : ℕ) : ℝ) *
      Real.sqrt (Real.log (x : ℝ)) := by positivity
  have hsq' : ((x : ℝ) * Real.sqrt (Real.log (x + 1 : ℕ))) ^ 2 ≤
      (((x + 1 : ℕ) : ℝ) * Real.sqrt (Real.log (x : ℝ))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hlogSucc.le,
      Real.sq_sqrt (zero_lt_one.trans hlog).le]
    exact hsq
  have hcross : (x : ℝ) * Real.sqrt (Real.log (x + 1 : ℕ)) ≤
      ((x + 1 : ℕ) : ℝ) * Real.sqrt (Real.log (x : ℝ)) := by
    nlinarith [sq_nonneg
      (((x + 1 : ℕ) : ℝ) * Real.sqrt (Real.log (x : ℝ)) -
        (x : ℝ) * Real.sqrt (Real.log (x + 1 : ℕ)))]
  dsimp [Proposition4.martinMargin]
  change (x : ℝ) / Real.sqrt (Real.log (x : ℝ)) ≤
    ((x + 1 : ℕ) : ℝ) / Real.sqrt (Real.log (x + 1 : ℕ))
  exact (div_le_div_iff₀ (Real.sqrt_pos.2 (zero_lt_one.trans hlog))
    (Real.sqrt_pos.2 hlogSucc)).2 hcross

lemma eventually_martinLowerEndpoint_mono :
    ∀ᶠ x : ℕ in atTop,
      Proposition4.martinLowerRatio x * (x : ℝ) ≤
        Proposition4.martinLowerRatio (x + 1) * (x + 1 : ℕ) := by
  filter_upwards [eventually_weighted_martinMargin_mono] with x hm
  dsimp [Proposition4.martinLowerRatio]
  have hexp : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  push_cast
  have hm' : (x : ℝ) * Proposition4.martinMargin x ≤
      ((x : ℝ) + 1) * Proposition4.martinMargin (x + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hm
  calc
    (Real.exp (-1) + Proposition4.martinMargin x) * (x : ℝ) =
        Real.exp (-1) * x + x * Proposition4.martinMargin x := by ring
    _ ≤ Real.exp (-1) * (x + 1) +
        (x + 1) * Proposition4.martinMargin (x + 1) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (by linarith) hexp) hm'
    _ = (Real.exp (-1) + Proposition4.martinMargin (x + 1)) * (x + 1) := by ring

lemma eventually_martinLowerFloor_mono :
    ∀ᶠ x : ℕ in atTop,
      ⌊Proposition4.martinLowerRatio x * (x : ℝ)⌋₊ ≤
        ⌊Proposition4.martinLowerRatio (x + 1) * (x + 1 : ℕ)⌋₊ := by
  filter_upwards [eventually_martinLowerEndpoint_mono] with x hx
  exact Nat.floor_mono hx

/-! ## One-step change of the smooth block -/

lemma newly_smooth_dvd_cutoffSucc {x n : ℕ}
    (hcut : mainCutoffNat (x + 1) ≤ mainCutoffNat x + 1)
    (hnzero : n ≠ 0)
    (hnew : UnitFractions.is_smooth (proposition6MainCutoff (x + 1)) n)
    (hold : ¬ UnitFractions.is_smooth (proposition6MainCutoff x) n) :
    mainCutoffNat x + 1 ∣ n := by
  have hnewMax : PrimePowers.largestPrimePowerPart n ≤ mainCutoffNat (x + 1) :=
    (isSmooth_iff_largestPrimePowerPart_le_floor
      (proposition6MainCutoff_nonneg (x + 1)) hnzero).1 hnew
  have holdMax : ¬ PrimePowers.largestPrimePowerPart n ≤ mainCutoffNat x := by
    intro h
    exact hold ((isSmooth_iff_largestPrimePowerPart_le_floor
      (proposition6MainCutoff_nonneg x) hnzero).2 h)
  have heq : PrimePowers.largestPrimePowerPart n = mainCutoffNat x + 1 := by omega
  have hn2 : 2 ≤ n := by
    by_contra hnlt
    have hempty : PrimePowers.primePowerParts n = ∅ :=
      PrimePowers.primePowerParts_empty_iff.mpr (Nat.lt_of_not_ge hnlt)
    have hz : PrimePowers.largestPrimePowerPart n = 0 := by
      simp [PrimePowers.largestPrimePowerPart, hempty]
    omega
  have hmem := PrimePowers.largestPrimePowerPart_mem hn2
  have hspec := (PrimePowers.mem_primePowerParts hnzero).mp hmem
  rw [← heq]
  exact hspec.2.1

lemma martinInitialBlock_succ_subset (x : ℕ)
    (hfloor : ⌊Proposition4.martinLowerRatio x * (x : ℝ)⌋₊ ≤
      ⌊Proposition4.martinLowerRatio (x + 1) * (x + 1 : ℕ)⌋₊)
    (hcut : mainCutoffNat (x + 1) ≤ mainCutoffNat x + 1) :
    Proposition4.martinInitialBlock (x + 1) ⊆
      Proposition4.martinInitialBlock x ∪
        insert (x + 1) (multiplesUpTo x (mainCutoffNat x + 1)) := by
  intro n hn
  by_cases hnold : n ∈ Proposition4.martinInitialBlock x
  · exact Finset.mem_union_left _ hnold
  apply Finset.mem_union_right
  have hn' := hn
  simp only [Proposition4.martinInitialBlock, initialBlockAt, initialSmoothBlock,
    Finset.mem_filter, Finset.mem_Ioc] at hn'
  by_cases hnx : n ≤ x
  · rw [Finset.mem_insert]
    right
    rw [mem_multiplesUpTo]
    refine ⟨?_, hnx, ?_⟩
    · omega
    · apply newly_smooth_dvd_cutoffSucc hcut (by omega) hn'.2
      intro hsold
      apply hnold
      simp only [Proposition4.martinInitialBlock, initialBlockAt, initialSmoothBlock,
        Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨lt_of_le_of_lt hfloor hn'.1.1, hnx⟩, hsold⟩
  · rw [Finset.mem_insert]
    left
    omega

lemma martinInitialBlock_succ_card_le (x : ℕ)
    (hfloor : ⌊Proposition4.martinLowerRatio x * (x : ℝ)⌋₊ ≤
      ⌊Proposition4.martinLowerRatio (x + 1) * (x + 1 : ℕ)⌋₊)
    (hcut : mainCutoffNat (x + 1) ≤ mainCutoffNat x + 1) :
    (Proposition4.martinInitialBlock (x + 1)).card ≤
      (Proposition4.martinInitialBlock x).card +
        (x / (mainCutoffNat x + 1) + 1) := by
  calc
    (Proposition4.martinInitialBlock (x + 1)).card ≤
        (Proposition4.martinInitialBlock x ∪
          insert (x + 1) (multiplesUpTo x (mainCutoffNat x + 1))).card :=
      Finset.card_le_card (martinInitialBlock_succ_subset x hfloor hcut)
    _ ≤ (Proposition4.martinInitialBlock x).card +
        (insert (x + 1) (multiplesUpTo x (mainCutoffNat x + 1))).card :=
      Finset.card_union_le _ _
    _ ≤ (Proposition4.martinInitialBlock x).card +
        ((multiplesUpTo x (mainCutoffNat x + 1)).card + 1) := by
      gcongr
      exact Finset.card_insert_le _ _
    _ = (Proposition4.martinInitialBlock x).card +
        (x / (mainCutoffNat x + 1) + 1) := by
      have hcard : (multiplesUpTo x (mainCutoffNat x + 1)).card =
          x / (mainCutoffNat x + 1) := by
        simpa [multiplesUpTo] using
          (UnitFractions.count_multiples (n := x)
            (show 1 ≤ mainCutoffNat x + 1 by omega))
      rw [hcard]

theorem eventually_martinInitialBlock_succ_card_le :
    ∀ᶠ x : ℕ in atTop,
      (Proposition4.martinInitialBlock (x + 1)).card ≤
        (Proposition4.martinInitialBlock x).card +
          (x / (mainCutoffNat x + 1) + 1) := by
  filter_upwards [eventually_martinLowerFloor_mono,
    LastCrossing.eventually_mainCutoffNat_succ_le] with x hfloor hcut
  exact martinInitialBlock_succ_card_le x hfloor hcut

/-! ## The concrete score jump -/

theorem eventually_martinScore_succ_le :
    ∀ᶠ x : ℕ in atTop,
      Proposition4.martinScore (x + 1) ≤
        Proposition4.martinScore x + LastCrossing.logarithmicStepJump x := by
  filter_upwards [eventually_martinInitialBlock_succ_card_le] with x hblock
  have hcorr := Proposition4.correctionCount_fifthRoot_succ_le x
  simp only [Proposition4.martinScore, LastCrossing.logarithmicStepJump]
  omega

/-! ## The unconditional selected scale -/

lemma martinScore_exists_above (t : ℕ) :
    ∃ x : ℕ, t < Proposition4.martinScore x := by
  obtain ⟨a, ha⟩ :=
    (tendsto_atTop_atTop.mp Proposition4.martinScore_tendsto_atTop) (t + 1)
  refine ⟨a, ?_⟩
  exact lt_of_lt_of_le (Nat.lt_succ_self t) (ha a le_rfl)

/-- The first cutoff at which the full source score exceeds the requested
number of terms. -/
def martinFirstAbove : ℕ → ℕ :=
  LastCrossing.firstAbove Proposition4.martinScore martinScore_exists_above

lemma martinFirstAbove_crosses (t : ℕ) :
    t < Proposition4.martinScore (martinFirstAbove t) :=
  LastCrossing.firstAbove_spec t

lemma martinFirstAbove_tendsto_atTop : Tendsto martinFirstAbove atTop atTop :=
  LastCrossing.firstAbove_tendsto_atTop martinScore_exists_above

/-- The largest cutoff no later than the first crossing whose score is still
at most the requested cardinality. -/
def martinSelectedScale : ℕ → ℕ :=
  LastCrossing.lastBelow Proposition4.martinScore martinFirstAbove

lemma martinSelectedScale_tendsto_atTop : Tendsto martinSelectedScale atTop atTop :=
  LastCrossing.lastBelow_tendsto_atTop Proposition4.martinScore_zero
    martinFirstAbove_tendsto_atTop

lemma martinScore_selected_le (t : ℕ) :
    Proposition4.martinScore (martinSelectedScale t) ≤ t :=
  LastCrossing.sourceCount_lastBelow_le Proposition4.martinScore_zero t

lemma martinSelectedScale_ratio_tendsto :
    Tendsto (fun t : ℕ ↦ (martinSelectedScale t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant) := by
  have hd : 0 < 1 - Real.exp (-1) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    norm_num
  have h := LastCrossing.lastBelow_ratio_tendsto_of_cap_tendsto
    Proposition4.martinScore_zero hd martinFirstAbove_tendsto_atTop
    Proposition4.martinScore_ratio_tendsto
    (Filter.Eventually.of_forall martinFirstAbove_crosses)
    eventually_martinScore_succ_le LastCrossing.logarithmicStepJump_isLittleO
  have hinv : (1 - Real.exp (-1))⁻¹ = Analytic.densityConstant := by
    rw [← Analytic.densityConstant_inv, inv_inv]
  simpa [martinSelectedScale, hinv] using h

lemma eventually_selected_deficit_le_stepJump :
    ∀ᶠ t : ℕ in atTop,
      t - Proposition4.martinScore (martinSelectedScale t) ≤
        LastCrossing.logarithmicStepJump (martinSelectedScale t) := by
  exact LastCrossing.eventually_deficit_lastBelow_le_jump
    Proposition4.martinScore_zero martinFirstAbove_tendsto_atTop
    (Filter.Eventually.of_forall martinFirstAbove_crosses)
    eventually_martinScore_succ_le

/-- The exact-cardinality deficit fits inside one Proposition 6 deletion
budget at the selected scale. -/
theorem eventually_selected_deficit_le_deletionBudget :
    ∀ᶠ t : ℕ in atTop,
      t - Proposition4.martinScore (martinSelectedScale t) ≤
        proposition6DeletionBudget (martinSelectedScale t) := by
  have hbudget := martinSelectedScale_tendsto_atTop.eventually
    LastCrossing.eventually_logarithmicStepJump_le_deletionBudget
  filter_upwards [eventually_selected_deficit_le_stepJump, hbudget]
    with t hdef hstep
  exact hdef.trans hstep

end

end ScoreCrossing

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Proposition6Final.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős 285: unconditional final form of Martin's Proposition 6

This module joins the three independently verified parts of the construction:

* `ScoreCrossing` chooses the last scale whose full smooth-block score fits the
  requested number of terms and bounds its exact deficit by one deletion
  budget;
* `Proposition6` performs the concrete Lemma 12 descent and the exact finite
  padding/cardinality bookkeeping;
* `MovingBounds` proves the residual, deletion-budget, and five-prime-reservoir
  estimates at the moving lower endpoint.

The theorem below has no Martin-content hypotheses: it supplies the eventual
stream of finite approximation certificates used directly by Proposition 4.
-/

open Filter Finset Real
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-- At every sufficiently large requested cardinality, the selected scale
carries an exact Proposition 6 certificate with precisely the number of main
terms left after reserving Proposition 7's correction count. -/
theorem eventually_martinApproximationCertificate :
    ∀ᶠ t : ℕ in atTop,
      Nonempty (ApproximationCertificate (1 : ℚ)
        (ScoreCrossing.martinSelectedScale t)
        (mainCount t
          (Proposition4.fifthRootFloor
            (ScoreCrossing.martinSelectedScale t)))) := by
  let X := ScoreCrossing.martinSelectedScale
  have hXtop : Tendsto X atTop atTop :=
    ScoreCrossing.martinSelectedScale_tendsto_atTop
  have hdescent := hXtop.eventually eventually_concreteRemovalDescent_one
  have hmoving := hXtop.eventually eventually_moving_proposition6_bounds
  have hreservoir := hXtop.eventually
    (eventually_two_budget_le_smoothReservoir (Real.exp (-1))
      (Real.exp_pos _) (by
        rw [Real.exp_le_one_iff]
        norm_num))
  have halphaBounds := hXtop.eventually
    Proposition4.eventually_martinLowerRatio_bounds
  have halphaThreeFourths := hXtop.eventually
    (Proposition4.martinLowerRatio_tendsto.eventually
      (Iio_mem_nhds (show Real.exp (-1) < (3 : ℝ) / 4 by
        exact Real.exp_neg_one_lt_half.trans (by norm_num))))
  have hxLarge := hXtop.eventually (eventually_ge_atTop 3)
  have hdeficit := ScoreCrossing.eventually_selected_deficit_le_deletionBudget
  filter_upwards [hdescent, hmoving, hreservoir, halphaBounds, halphaThreeFourths,
    hxLarge, hdeficit] with t hdescent hmoving hreservoir halphaBounds halphaXi hx hdeficit
  let x := X t
  let alpha := Proposition4.martinLowerRatio x
  let z := proposition6MainCutoff x
  let y := approximationCorrectionScale x
  let correction := correctionCount (Proposition4.fifthRootFloor x)
  let D := proposition6DeletionBudget x
  have halpha : 0 < alpha :=
    (Real.exp_pos (-1)).trans halphaBounds.1
  have halphaOne : alpha ≤ 1 := halphaBounds.2.le
  have hExpLe : Real.exp (-1) ≤ alpha := halphaBounds.1.le
  have hxpos : 0 < x := by omega
  obtain ⟨out⟩ := hdescent alpha halpha.le halphaXi
  have hscore : (initialSmoothBlock alpha x z).card + correction ≤ t := by
    simpa [x, alpha, z, correction, X, Proposition4.martinScore,
      Proposition4.martinInitialBlock, initialBlockAt] using
        ScoreCrossing.martinScore_selected_le t
  have hdeficit' :
      t - ((initialSmoothBlock alpha x z).card + correction) ≤ D := by
    simpa [x, alpha, z, correction, D, X, Proposition4.martinScore,
      Proposition4.martinInitialBlock, initialBlockAt] using hdeficit
  have hz : 0 ≤ z := by
    dsimp [z, proposition6MainCutoff]
    positivity
  have hstartMeasure :
      (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure ≤
        ⌊z⌋₊ :=
    initialResidualApproximationState_one_measure_le_floor hz
  have hbudget : totalEliminationBudget x
      (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure ≤ D := by
    exact (totalEliminationBudget_mono x hstartMeasure).trans (by
      simpa [x, z, D] using hmoving.2.2)
  have hrootNonneg : 0 ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹) :=
    Real.rpow_nonneg (Nat.cast_nonneg x) _
  have hyRoot : (y : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹) := by
    dsimp [y, approximationCorrectionScale]
    exact Nat.floor_le hrootNonneg
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlowerPositive : 0 < (Real.log (x : ℝ))⁻¹ := inv_pos.mpr hlogpos
  have hcertificate := exists_approximationCertificate_one_of_budget
    halpha halphaOne (Real.exp_pos (-1)) hExpLe le_rfl hxpos out
    hscore hdeficit' hbudget
    (by simpa [x, D] using hreservoir) hyRoot hlowerPositive
    (by simpa [x, alpha, z, D, div_eq_mul_inv, mul_assoc] using hmoving.1)
    (by simpa [x, alpha, z, D] using hmoving.2.1)
  simpa [x, correction, X, mainCount] using hcertificate

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/MartinUpperFinal.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős 285: unconditional final upper construction

This module applies the abstract Proposition 4 assembly to the unconditional
Proposition 6 certificate stream at `ScoreCrossing.martinSelectedScale`.
The resulting cutoff is indexed by the formal problem's parameter `k`, hence
uses the selected scale for the requested cardinality `k + 1`.
-/

namespace MartinUpperFinal

open Filter
open scoped Topology

noncomputable section

/-- Martin's selected denominator cutoff for the formal problem's `k + 1`
term indexing. -/
def martinCutoff (k : ℕ) : ℕ :=
  Proposition4.indexedCutoff ScoreCrossing.martinSelectedScale k

/-- The unconditional upper half of Martin's Proposition 4: sufficiently
large `k` possess an exact `k + 1` term Egyptian-fraction representation whose
denominators are bounded by `martinCutoff k`, and this cutoff has the optimal
asymptotic ratio. -/
theorem martinUpperConclusion :
    (∀ᶠ k : ℕ in atTop,
      ∃ A : Finset ℕ, UpperWitness 1 k.succ (martinCutoff k) A) ∧
    Tendsto
      (fun k : ℕ ↦ (martinCutoff k : ℝ) / (k + 1 : ℕ)) atTop
      (nhds Analytic.densityConstant) := by
  simpa only [martinCutoff] using
    Proposition4.propositionFour_of_approximationCertificates
      ScoreCrossing.martinSelectedScale
      ScoreCrossing.martinSelectedScale_ratio_tendsto
      eventually_martinApproximationCertificate

/-- The unconditional eventual finite-set witness stream. -/
theorem eventually_martinUpperWitness :
    ∀ᶠ k : ℕ in atTop,
      ∃ A : Finset ℕ, UpperWitness 1 k.succ (martinCutoff k) A :=
  martinUpperConclusion.1

/-- Martin's selected cutoff divided by the requested number of terms tends
to `e / (e - 1)`. -/
theorem martinCutoff_ratio_tendsto :
    Tendsto
      (fun k : ℕ ↦ (martinCutoff k : ℝ) / (k + 1 : ℕ)) atTop
      (nhds Analytic.densityConstant) :=
  martinUpperConclusion.2

end

end MartinUpperFinal

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Basic.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős Problem 285: elementary representation infrastructure

This file contains the definitions occurring literally in the formal-conjectures
statement, their equivalent finite-set formulation, and the elementary splitting
operation for Egyptian fractions.  The analytic and number-theoretic estimates in
Martin's theorem are intentionally kept out of this file.
-/

open Filter
open scoped BigOperators Topology Real

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A strictly increasing representation of one by exactly `k + 1` positive,
distinct unit fractions.  This is the predicate used in the upstream statement. -/
def Representation (k : ℕ) (n : Fin k.succ → ℕ) : Prop :=
  StrictMono n ∧ 0 ∉ Set.range n ∧ 1 = ∑ i, (1 : ℝ) / n i

/-- The set of indices `k` for which a representation with `k + 1` terms exists. -/
def ValidIndices : Set ℕ :=
  {k | ∃ n : Fin k.succ → ℕ, Representation k n}

/-- The possible final (and therefore largest) denominators of `k + 1`-term
representations.  Its syntax matches the set minimized in the upstream theorem. -/
def LastDenominators (k : ℕ) : Set ℕ :=
  {n (Fin.last k) |
    (n : Fin k.succ → ℕ) (_ : StrictMono n) (_ : 0 ∉ Set.range n)
      (_ : 1 = ∑ i, (1 : ℝ) / n i)}

@[simp] theorem mem_validIndices {k : ℕ} :
    k ∈ ValidIndices ↔ ∃ n : Fin k.succ → ℕ, Representation k n :=
  Iff.rfl

@[simp] theorem mem_lastDenominators {k m : ℕ} :
    m ∈ LastDenominators k ↔
      ∃ n : Fin k.succ → ℕ, Representation k n ∧ n (Fin.last k) = m := by
  simp only [LastDenominators, Representation, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, hnmono, hnzero, hnsum, rfl⟩
    exact ⟨n, ⟨hnmono, hnzero, hnsum⟩, rfl⟩
  · rintro ⟨n, ⟨hnmono, hnzero, hnsum⟩, rfl⟩
    exact ⟨n, hnmono, hnzero, hnsum, rfl⟩

/-! ## Conversion to finite sets -/

/-- The finite set of denominators occurring in an indexed family. -/
def denominatorFinset {k : ℕ} (n : Fin k.succ → ℕ) : Finset ℕ :=
  Finset.image n Finset.univ

@[simp] theorem mem_denominatorFinset {k : ℕ} {n : Fin k.succ → ℕ} {m : ℕ} :
    m ∈ denominatorFinset n ↔ m ∈ Set.range n := by
  simp [denominatorFinset]

theorem sum_denominatorFinset {k : ℕ} {n : Fin k.succ → ℕ}
    (hn : StrictMono n) :
    ∑ m ∈ denominatorFinset n, (1 : ℝ) / m = ∑ i, (1 : ℝ) / n i := by
  classical
  rw [denominatorFinset, Finset.sum_image]
  exact fun i _ j _ hij ↦ hn.injective hij

/-- Enumerate a finite set increasingly when its cardinality is `k + 1`. -/
def enumerate {k : ℕ} (A : Finset ℕ) (hA : A.card = k.succ) : Fin k.succ → ℕ :=
  A.orderEmbOfFin hA

theorem enumerate_strictMono {k : ℕ} (A : Finset ℕ) (hA : A.card = k.succ) :
    StrictMono (enumerate A hA) :=
  (A.orderEmbOfFin hA).strictMono

theorem range_enumerate {k : ℕ} (A : Finset ℕ) (hA : A.card = k.succ) :
    Set.range (enumerate A hA) = A := by
  exact A.range_orderEmbOfFin hA

@[simp] theorem denominatorFinset_enumerate {k : ℕ} (A : Finset ℕ)
    (hA : A.card = k.succ) :
    denominatorFinset (enumerate A hA) = A := by
  exact A.image_orderEmbOfFin_univ hA

theorem sum_enumerate {k : ℕ} (A : Finset ℕ) (hA : A.card = k.succ) :
    ∑ i, (1 : ℝ) / enumerate A hA i = ∑ m ∈ A, (1 : ℝ) / m := by
  calc
    ∑ i, (1 : ℝ) / enumerate A hA i =
        ∑ m ∈ denominatorFinset (enumerate A hA), (1 : ℝ) / m :=
      (sum_denominatorFinset (enumerate_strictMono A hA)).symm
    _ = ∑ m ∈ A, (1 : ℝ) / m := by
      rw [denominatorFinset_enumerate A hA]

theorem representation_enumerate {k : ℕ} {A : Finset ℕ}
    (hcard : A.card = k.succ) (hzero : 0 ∉ A)
    (hsum : ∑ m ∈ A, (1 : ℝ) / m = 1) :
    Representation k (enumerate A hcard) := by
  refine ⟨enumerate_strictMono A hcard, ?_, ?_⟩
  · rwa [range_enumerate A hcard]
  · rw [sum_enumerate A hcard, hsum]

/-! ## Splitting the largest denominator -/

/-- Replace the final denominator `m` by `m+1` and `m(m+1)`, retaining all
earlier denominators. -/
def splitLast {k : ℕ} (n : Fin k.succ → ℕ) : Fin k.succ.succ → ℕ :=
  let m := n (Fin.last k)
  Fin.snoc (Fin.snoc (Fin.init n) (m + 1)) (m * (m + 1))

@[simp] theorem splitLast_last {k : ℕ} (n : Fin k.succ → ℕ) :
    splitLast n (Fin.last k.succ) =
      n (Fin.last k) * (n (Fin.last k) + 1) := by
  simp [splitLast]

@[simp] theorem splitLast_penultimate {k : ℕ} (n : Fin k.succ → ℕ) :
    splitLast n (Fin.castSucc (Fin.last k)) = n (Fin.last k) + 1 := by
  simp [splitLast]

@[simp] theorem splitLast_castSucc_castSucc {k : ℕ} (n : Fin k.succ → ℕ)
    (i : Fin k) :
    splitLast n (Fin.castSucc (Fin.castSucc i)) = n (Fin.castSucc i) := by
  simp [splitLast]
  rfl

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Erdos285Lower.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős 285: the elementary lower bound

This file isolates the elementary half of the asymptotic theorem.  A strictly
increasing list of `k + 1` positive denominators with reciprocal sum one has
last denominator `N` satisfying

`exp 1 / (exp 1 - 1) * (k + 1) ≤ N + 1`.

The proof compares the denominators with the final interval of `k + 1`
positive integers ending at `N`, then telescopes logarithms.  The final `+ 1`
is negligible after division by `k + 1`.
-/

namespace Erdos285Lower

open Filter Finset Real Set
open scoped BigOperators Topology

private lemma strictMono_gap {k : ℕ} {n : Fin (k + 1) → ℕ} (hn : StrictMono n)
    (i : ℕ) (hi : i ≤ k) :
    n ⟨i, Nat.lt_succ_of_le hi⟩ + (k - i) ≤ n (Fin.last k) := by
  induction hi using Nat.decreasingInduction with
  | self =>
      simpa only [Nat.sub_self, add_zero] using
        hn.monotone (show (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) ≤ Fin.last k by exact le_rfl)
  | of_succ i hi ih =>
      have hlt :
          n ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt hi)⟩ <
            n ⟨i + 1, Nat.succ_lt_succ_iff.mpr hi⟩ := by
        apply hn
        simp
      omega

/-- The quantitative lower bound behind the elementary half of Erdős 285. -/
theorem max_denominator_lower_bound {k : ℕ} {n : Fin (k + 1) → ℕ}
    (hn : StrictMono n) (hn0 : 0 ∉ Set.range n)
    (hsum : 1 = ∑ i, (1 : ℝ) / n i) :
    Real.exp 1 / (Real.exp 1 - 1) * (k + 1 : ℕ) ≤
      (n (Fin.last k) : ℝ) + 1 := by
  let N := n (Fin.last k)
  let L := N - k
  have hn_pos (i : Fin (k + 1)) : 0 < n i := by
    exact Nat.pos_of_ne_zero fun hi ↦ hn0 ⟨i, hi⟩
  have hgap_zero := strictMono_gap hn 0 (Nat.zero_le k)
  have hkN : k < N := by
    dsimp [N] at hgap_zero
    have := hn_pos (0 : Fin (k + 1))
    omega
  have hL_pos_nat : 0 < L := by
    dsimp [L]
    omega
  have hdenom (i : Fin (k + 1)) : n i ≤ L + i.val := by
    have hi : i.val ≤ k := by omega
    have hgap := strictMono_gap hn i.val hi
    have heq : n ⟨i.val, Nat.lt_succ_of_le hi⟩ = n i := by congr
    rw [heq] at hgap
    dsimp [L, N]
    omega
  have hterm (i : Fin (k + 1)) :
      Real.log (((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ)) ≤
        (1 : ℝ) / n i := by
    have hLi_pos_nat : 0 < L + i.val := Nat.add_pos_left hL_pos_nat _
    have hLi_pos : (0 : ℝ) < (L + i.val : ℕ) := by exact_mod_cast hLi_pos_nat
    have hratio_pos :
        (0 : ℝ) < ((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ) := by
      positivity
    calc
      Real.log (((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ))
          ≤ (((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ)) - 1 :=
        Real.log_le_sub_one_of_pos hratio_pos
      _ = (1 : ℝ) / (L + i.val : ℕ) := by
        field_simp
        norm_num
      _ ≤ (1 : ℝ) / n i := by
        apply one_div_le_one_div_of_le
        · exact_mod_cast hn_pos i
        · exact_mod_cast hdenom i
  have hlog_sum :
      (∑ i : Fin (k + 1),
          Real.log (((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ))) ≤ 1 := by
    calc
      (∑ i : Fin (k + 1),
          Real.log (((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ)))
          ≤ ∑ i : Fin (k + 1), (1 : ℝ) / n i := Finset.sum_le_sum fun i _ ↦ hterm i
      _ = 1 := hsum.symm
  have htel :
      (∑ i : Fin (k + 1),
          Real.log (((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ))) =
        Real.log (N + 1 : ℕ) - Real.log L := by
    have hlog_step (j : ℕ) :
        Real.log (((L + j + 1 : ℕ) : ℝ) / (L + j : ℕ)) =
          Real.log (L + (j + 1) : ℕ) - Real.log (L + j : ℕ) := by
      rw [Real.log_div (by positivity) (by positivity)]
      norm_num [add_assoc]
    change (∑ i : Fin (k + 1),
      (fun j : ℕ ↦ Real.log (((L + j + 1 : ℕ) : ℝ) / (L + j : ℕ))) i) = _
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ ↦ Real.log (((L + j + 1 : ℕ) : ℝ) / (L + j : ℕ))) (k + 1)]
    simp_rw [hlog_step]
    change (∑ i ∈ Finset.range (k + 1),
      ((fun t : ℕ ↦ Real.log (L + t : ℕ)) (i + 1) -
        (fun t : ℕ ↦ Real.log (L + t : ℕ)) i)) = _
    rw [Finset.sum_range_sub (fun t : ℕ ↦ Real.log (L + t : ℕ)) (k + 1)]
    have hLk : L + k = N := by
      dsimp [L]
      exact Nat.sub_add_cancel (Nat.le_of_lt hkN)
    rw [← hLk]
    norm_num [add_assoc]
  rw [htel] at hlog_sum
  have hlog_ratio : Real.log (((N + 1 : ℕ) : ℝ) / L) ≤ 1 := by
    rw [Real.log_div (by positivity) (by positivity)]
    exact hlog_sum
  have hratio_pos : (0 : ℝ) < (((N + 1 : ℕ) : ℝ) / L) := by positivity
  have hratio : (((N + 1 : ℕ) : ℝ) / L) ≤ Real.exp 1 := by
    have hexp := (Real.exp_le_exp.mpr hlog_ratio)
    rwa [Real.exp_log hratio_pos] at hexp
  have hlinear : ((N + 1 : ℕ) : ℝ) ≤ Real.exp 1 * L := by
    exact (div_le_iff₀ (by exact_mod_cast hL_pos_nat)).mp hratio
  have hexp_sub_pos : (0 : ℝ) < Real.exp 1 - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr zero_lt_one)
  change Real.exp 1 / (Real.exp 1 - 1) * (k + 1 : ℕ) ≤ (N : ℝ) + 1
  rw [div_mul_eq_mul_div, div_le_iff₀ hexp_sub_pos]
  push_cast
  have hlinear' : ((N : ℝ) + 1) ≤ Real.exp 1 * (L : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_one] at hlinear ⊢
    exact hlinear
  rw [show (L : ℝ) = (N : ℝ) - k by
    dsimp [L]
    rw [Nat.cast_sub (Nat.le_of_lt hkN)]] at hlinear'
  nlinarith

/-- Pointwise lower bound for the least last denominator, in the exact
`IsLeast` formulation used by the formal-conjectures statement. -/
theorem lower_bound_of_isLeast (f : ℕ → ℕ) (S : Set ℕ)
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n)
          (_ : 0 ∉ Set.range n) (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k)) :
    ∀ k ∈ S, Real.exp 1 / (Real.exp 1 - 1) * (k + 1 : ℕ) ≤ (f k : ℝ) + 1 := by
  intro k hk
  rcases (h k hk).1 with ⟨n, hn, hn0, hsum, hnlast⟩
  rw [← hnlast]
  simpa only [Nat.succ_eq_add_one] using max_denominator_lower_bound hn hn0 hsum

end Erdos285Lower

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/RatioBridge.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős 285: bridge from finite-set witnesses to the least-denominator ratio

This file connects the finite-set output of Martin's upper-bound construction
to the indexed formulation in the formal-conjectures statement.  An upper
witness with `k + 1` elements is enumerated increasingly; minimality then puts
`f k` below its largest denominator and hence below the witness cutoff.  The
elementary lower bound and the asymptotic cutoff bound squeeze the completed
ratio to one.
-/

open Filter
open scoped BigOperators Topology Real

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A finite-set upper witness gives an admissible indexed representation and
therefore an upper bound for the least final denominator. -/
theorem minimalLastDenominator_le_cutoff_of_upperWitness
    (f : ℕ → ℕ) (S : Set ℕ)
    (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧
      0 ∉ Set.range n ∧ 1 = ∑ i, (1 : ℝ) / n i })
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n)
          (_ : 0 ∉ Set.range n) (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k))
    {k x : ℕ} {A : Finset ℕ} (hA : UpperWitness 1 k.succ x A) :
    k ∈ S ∧ f k ≤ x := by
  have hcard : A.card = k.succ := hA.card_eq
  let n : Fin k.succ → ℕ := enumerate A hcard
  have hn : Representation k n := by
    apply representation_enumerate hcard hA.zero_not_mem
    simpa only [reciprocalSum] using hA.sum_eq
  have hkS : k ∈ S := by
    rw [hS]
    exact ⟨n, hn⟩
  refine ⟨hkS, ?_⟩
  have hnLastMem : n (Fin.last k) ∈
      { m (Fin.last k) | (m : Fin k.succ → ℕ) (_ : StrictMono m)
        (_ : 0 ∉ Set.range m) (_ : 1 = ∑ i, (1 : ℝ) / m i) } := by
    exact ⟨n, hn.1, hn.2.1, hn.2.2, rfl⟩
  have hfLast : f k ≤ n (Fin.last k) := (h k hkS).2 hnLastMem
  have hnLastA : n (Fin.last k) ∈ A := by
    dsimp only [n]
    change enumerate A hcard (Fin.last k) ∈ (A : Set ℕ)
    rw [← range_enumerate A hcard]
    exact Set.mem_range_self (Fin.last k)
  exact hfLast.trans (hA.le_cutoff _ hnLastA)

/--
If Martin's construction eventually supplies exact `k + 1`-term witnesses
whose cutoffs divided by `k + 1` tend to `e / (e - 1)`, then the completed
least-denominator ratio in `Erdos285Packaging` tends to one.
-/
theorem uniform_ratio_of_eventually_upperWitness
    (f : ℕ → ℕ) (S : Set ℕ)
    (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧
      0 ∉ Set.range n ∧ 1 = ∑ i, (1 : ℝ) / n i })
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n)
          (_ : 0 ∉ Set.range n) (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k))
    (cutoff : ℕ → ℕ)
    (hupper : ∀ᶠ k in atTop,
      ∃ A : Finset ℕ, UpperWitness 1 k.succ (cutoff k) A)
    (hcutoff : Tendsto
      (fun k : ℕ ↦ (cutoff k : ℝ) / (k + 1 : ℕ)) atTop
      (nhds (rexp 1 / (rexp 1 - 1)))) :
    Tendsto
      (fun k : ℕ ↦
        if k ∈ S then
          (f k : ℝ) / (rexp 1 / (rexp 1 - 1) * (k + 1 : ℕ))
        else 1)
      atTop (nhds 1) := by
  let C : ℝ := rexp 1 / (rexp 1 - 1)
  have hCpos : 0 < C := by
    simpa only [C, Analytic.densityConstant] using
      Analytic.densityConstant_pos
  have hCne : C ≠ 0 := hCpos.ne'
  have hbounds : ∀ᶠ k in atTop, k ∈ S ∧ f k ≤ cutoff k := by
    filter_upwards [hupper] with k hk
    rcases hk with ⟨A, hA⟩
    exact minimalLastDenominator_le_cutoff_of_upperWitness f S hS h hA

  have hinv : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1 : ℕ)) atTop (nhds 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlower : Tendsto
      (fun k : ℕ ↦ 1 - (1 / C) * (1 / (k + 1 : ℕ))) atTop (nhds 1) := by
    have hz : Tendsto (fun k : ℕ ↦ (1 / C) * (1 / (k + 1 : ℕ)))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hinv)
    simpa using (tendsto_const_nhds.sub hz)

  have hcutoffC : Tendsto
      (fun k : ℕ ↦ (cutoff k : ℝ) /
        (C * (k + 1 : ℕ))) atTop (nhds 1) := by
    have hdiv := hcutoff.div_const C
    have heq : ∀ k : ℕ,
        ((cutoff k : ℝ) / (k + 1 : ℕ)) / C =
          (cutoff k : ℝ) / (C * (k + 1 : ℕ)) := by
      intro k
      field_simp [hCne]
    have hdiv' : Tendsto
        (fun k : ℕ ↦ (cutoff k : ℝ) / (C * (k + 1 : ℕ))) atTop
        (nhds (C / C)) := hdiv.congr' (Eventually.of_forall heq)
    simpa [hCne] using hdiv'

  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hcutoffC
  · filter_upwards [hbounds] with k hk
    rw [if_pos hk.1]
    have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hdenom : 0 < C * (k + 1 : ℕ) := mul_pos hCpos hkpos
    have hpoint := Erdos285Lower.lower_bound_of_isLeast f S h k hk.1
    change C * (k + 1 : ℕ) ≤ (f k : ℝ) + 1 at hpoint
    rw [le_div_iff₀ hdenom]
    have halgebra :
        (1 - (1 / C) * (1 / (k + 1 : ℕ))) *
            (C * (k + 1 : ℕ)) = C * (k + 1 : ℕ) - 1 := by
      field_simp [hCne]
    rw [halgebra]
    linarith
  · filter_upwards [hbounds] with k hk
    rw [if_pos hk.1]
    have hdenom : 0 ≤ C * (k + 1 : ℕ) := by positivity
    exact div_le_div_of_nonneg_right (by exact_mod_cast hk.2) hdenom

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285/Erdos285Packaging.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Erdős Problem 285: packaging the asymptotic input

This file isolates the formal-conjectures wrapper from the number-theoretic theorem.
The hypothesis of `erdos_285_of_uniform_ratio` is the internal uniform-ratio result:
on indices represented by `S`, the least possible final denominator, divided by
`e / (e - 1) * (k + 1)`, tends to one.  Off `S` the ratio is completed by the
constant one.  The proof below converts this ratio limit into the error function
and exact equality requested by the upstream statement.
-/

open Filter
open scoped Topology Real

noncomputable section

attribute [local instance] Classical.propDecidable

/--
The exact upstream statement follows from the completed uniform-ratio theorem.

The long hypothesis is deliberately an argument of this theorem.  Thus this file
contains only the packaging implication, and does not postulate the analytic and
number-theoretic content of Martin's theorem.
-/
theorem erdos_285_of_uniform_ratio
    (uniform_ratio :
      ∀ᵉ (f : ℕ → ℕ)
      (S : Set ℕ)
      (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧ 0 ∉ Set.range n ∧
        1 = ∑ i, (1 : ℝ) / n i })
      (h : ∀ k ∈ S,
        IsLeast
          { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n) (_ : 0 ∉ Set.range n)
            (_ : 1 = ∑ i, (1 : ℝ) / n i) }
          (f k)),
      Tendsto
        (fun k : ℕ ↦
          if k ∈ S then
            (f k : ℝ) / (rexp 1 / (rexp 1 - 1) * (k + 1 : ℕ))
          else 1)
        atTop (nhds 1)) :
    ∀ᵉ (f : ℕ → ℕ)
    (S : Set ℕ)
    (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧ 0 ∉ Set.range n ∧
      1 = ∑ i, (1 : ℝ) / n i })
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n) (_ : 0 ∉ Set.range n)
          (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k)),
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
      ∀ k ∈ S, f k = (1 + o k) * rexp 1 / (rexp 1 - 1) * (k + 1) := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _ f S hS h
    have hratio := uniform_ratio f S hS h
    let o : ℕ → ℝ := fun k ↦
      (if k ∈ S then
          (f k : ℝ) / (rexp 1 / (rexp 1 - 1) * (k + 1 : ℕ))
        else 1) - 1
    refine ⟨o, ?_, ?_⟩
    · apply (Asymptotics.isLittleO_one_iff ℝ).2
      have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
      simpa [o] using hratio.sub hone
    · intro k hk
      dsimp [o]
      rw [if_pos hk]
      have hexp : rexp 1 - 1 ≠ 0 :=
        ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.2 zero_lt_one))
      have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      norm_num [div_eq_mul_inv, hexp, hk1]
      field_simp [hexp, hk1]
  · intro _
    trivial

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos285.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 285.
https://www.erdosproblems.com/forum/thread/285

Informal authors:
- Greg Martin

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos285.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/285.lean
-/
/-
This is a Lean formalization of the resolution of Erdős Problem 285.

The theorem is the logical payload of the Google DeepMind Formal Conjectures
statement.

Informal author:
- Greg Martin

Formalization:
- OpenAI Codex

Primary references:
- https://doi.org/10.4064/aa-95-3-231-260
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/285.lean
-/

open Filter
open scoped BigOperators Topology Real

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Erdős Problem 285: the least possible largest denominator in a
`k + 1`-term representation of `1` by distinct unit fractions is asymptotic
to `e / (e - 1) * (k + 1)`. -/
theorem erdos_285 :
    ∀ᵉ (f : ℕ → ℕ)
    (S : Set ℕ)
    (hS : S = {k | ∃ (n : Fin k.succ → ℕ), StrictMono n ∧ 0 ∉ Set.range n ∧
      1 = ∑ i, (1 : ℝ) / n i })
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n)
          (_ : 0 ∉ Set.range n) (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k)),
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
      ∀ k ∈ S,
        f k = (1 + o k) * rexp 1 / (rexp 1 - 1) * (k + 1) := by
  apply erdos_285_of_uniform_ratio
  intro f S hS h
  exact uniform_ratio_of_eventually_upperWitness f S hS h
    MartinUpperFinal.martinCutoff
    MartinUpperFinal.eventually_martinUpperWitness
    MartinUpperFinal.martinCutoff_ratio_tendsto

end

end

#print axioms erdos_285
-- 'Erdos285.erdos_285' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos285
