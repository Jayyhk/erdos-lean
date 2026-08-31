import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos230

/-
# Problem Description

Erdős Problem 230, a conjecture of Erdős and Newman. Let `P(z) = ∑_{1 ≤ k ≤ n} aₖ zᵏ` with
`|aₖ| = 1` for all `k`. Is there a constant `c > 0` such that for `n ≥ 2`

  `max_{|z| = 1} |P(z)| ≥ (1 + c) √n`?

`erdos_230` proves that there is not. The bound `√n` is trivial from Parseval; the answer is
no because Körner constructed ultraflat polynomials, whose circle maximum is `O(√n)`.

`IsUnimodular a` is `∀ i, ‖a i‖ = 1`, and `phasePoly a = ∑_{i < n} aᵢ X^(i+1)`, so the
coefficient vector is zero-indexed while the exponents run `1` to `n` as in the statement.
`circleMaximum a` is `sSup (circleValues a)`; it is proved to be attained, so it really is
the maximum over the unit circle rather than a supremum that could degenerate.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos230/Surface.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Surface statement for Erdős Problem 230

For coefficients `a 0, ..., a (n - 1)` of complex norm one, `phasePoly a`
is the polynomial

`a 0 * X + a 1 * X^2 + ... + a (n - 1) * X^n`.

`ErdosNewmanClaim` is the proposed uniform improvement over the Parseval
lower bound.  Its `circleMaximum` is the supremum of the polynomial norm on
the unit circle; the extreme-value theorem below proves that this supremum is
an attained maximum.

The established negative resolution follows from the existence, at
arbitrarily large degrees, of unimodular polynomials whose norm is at most
`(1 + epsilon) * sqrt n` everywhere on the unit circle.  This file contains
only the finite polynomial interface and the elementary logical implication;
the analytic ultraflat construction is supplied separately.
-/

open scoped BigOperators



noncomputable section

/-! ## Unimodular coefficient polynomials -/

/-- A finite coefficient vector is unimodular when every coefficient has
complex norm one. -/
def IsUnimodular {n : ℕ} (a : Fin n → ℂ) : Prop :=
  ∀ i, ‖a i‖ = 1

/-- The polynomial `sum_(i < n) a_i X^(i+1)`.  Thus the coefficient vector
is zero-indexed while the exponents agree with the one-indexed mathematical
statement of Erdős Problem 230. -/
def phasePoly {n : ℕ} (a : Fin n → ℂ) : Polynomial ℂ :=
  ∑ i : Fin n, Polynomial.monomial (i.1 + 1) (a i)

/-- The corresponding finite trigonometric sum evaluated at `z`. -/
def phaseValue {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ i : Fin n, a i * z ^ (i.1 + 1)

@[simp]
theorem eval_phasePoly {n : ℕ} (a : Fin n → ℂ) (z : ℂ) :
    (phasePoly a).eval z = phaseValue a z := by
  classical
  simp [phasePoly, phaseValue, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]

/-! ## The attained circle maximum -/

/-- The set of norms taken by a coefficient polynomial on the unit circle. -/
def circleValues {n : ℕ} (a : Fin n → ℂ) : Set ℝ :=
  {x | ∃ z : ℂ, ‖z‖ = 1 ∧ x = ‖(phasePoly a).eval z‖}

/-- The circle maximum, initially defined as a supremum.  The next theorem
proves that it is attained. -/
noncomputable def circleMaximum {n : ℕ} (a : Fin n → ℂ) : ℝ :=
  sSup (circleValues a)

theorem circleValues_nonempty {n : ℕ} (a : Fin n → ℂ) :
    (circleValues a).Nonempty := by
  refine ⟨‖(phasePoly a).eval 1‖, ?_⟩
  exact ⟨1, norm_one, rfl⟩

/-- A pointwise circle upper bound also bounds the circle maximum. -/
theorem circleMaximum_le {n : ℕ} (a : Fin n → ℂ) (U : ℝ)
    (hU : ∀ z : ℂ, ‖z‖ = 1 → ‖(phasePoly a).eval z‖ ≤ U) :
    circleMaximum a ≤ U := by
  apply csSup_le (circleValues_nonempty a)
  rintro x ⟨z, hz, rfl⟩
  exact hU z hz

/-- The supremum in `circleMaximum` is an actual maximum, by compactness of
the unit circle and continuity of polynomial evaluation. -/
theorem exists_circleMaximum {n : ℕ} (a : Fin n → ℂ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ‖(phasePoly a).eval z‖ = circleMaximum a := by
  have hne : (Metric.sphere (0 : ℂ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨z, hz, hmax⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn
    hne (phasePoly a).continuous.norm.continuousOn
  have hzunit : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  have hupper : ∀ x ∈ circleValues a, x ≤ ‖(phasePoly a).eval z‖ := by
    rintro x ⟨w, hw, rfl⟩
    exact hmax (mem_sphere_zero_iff_norm.mpr hw)
  have hbdd : BddAbove (circleValues a) :=
    ⟨‖(phasePoly a).eval z‖, hupper⟩
  have hle : ‖(phasePoly a).eval z‖ ≤ circleMaximum a := by
    apply le_csSup hbdd
    exact ⟨z, hzunit, rfl⟩
  have hge : circleMaximum a ≤ ‖(phasePoly a).eval z‖ := by
    exact csSup_le (circleValues_nonempty a) hupper
  exact ⟨z, hzunit, le_antisymm hle hge⟩

/-! ## Exact proposed lower bound and ultraflat upper examples -/

/-- The Erdős--Newman claim in its literal circle-maximum form. -/
def ErdosNewmanClaim : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ n : ℕ, 2 ≤ n →
      ∀ a : Fin n → ℂ, IsUnimodular a →
        (1 + c) * Real.sqrt n ≤ circleMaximum a

/-- Arbitrarily large unimodular polynomials with a uniform upper bound
arbitrarily close to the Parseval scale `sqrt n`.

This is the precise one-sided consequence of an ultraflat family needed to
disprove `ErdosNewmanClaim`.  The lower cutoff `N` records that the examples
occur at arbitrarily large degrees, rather than at a single exceptional
degree. -/
def HasUltraflatUpper : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ n : ℕ, max 2 N ≤ n ∧
      ∃ a : Fin n → ℂ, IsUnimodular a ∧
        ∀ z : ℂ, ‖z‖ = 1 →
          ‖(phasePoly a).eval z‖ ≤ (1 + ε) * Real.sqrt n

/-- Ultraflat upper examples rule out every fixed positive multiplicative
improvement over `sqrt n`. -/
theorem not_erdos230Claim_of_ultraflat_upper
    (hultra : HasUltraflatUpper) : ¬ ErdosNewmanClaim := by
  rintro ⟨c, hc, hclaim⟩
  obtain ⟨n, hn, a, ha, hupper⟩ := hultra (c / 2) (by linarith) 2
  have hn2 : 2 ≤ n := by
    exact (le_max_left 2 2).trans hn
  have hsqrt : 0 < Real.sqrt n := by
    apply Real.sqrt_pos.2
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn2)
  have hfactor : (1 + c / 2) * Real.sqrt n <
      (1 + c) * Real.sqrt n := by
    apply mul_lt_mul_of_pos_right _ hsqrt
    linarith
  have hmax : circleMaximum a ≤ (1 + c / 2) * Real.sqrt n :=
    circleMaximum_le a _ hupper
  exact (not_lt_of_ge ((hclaim n hn2 a ha).trans hmax)) hfactor

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos230/Angular.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Angular form of the polynomials in Erdős Problem 230

The analytic construction is most naturally written on the real line, with
`theta` parametrizing the unit circle by `exp (theta * I)`.  This file gives
the exact bridge to the polynomial statement and records the harmless removal
of a constant coefficient at the end of the construction.
-/

open scoped BigOperators



noncomputable section

/-- The standard real parametrization of the complex unit circle. -/
def unitPoint (theta : ℝ) : ℂ :=
  Complex.exp ((theta : ℂ) * Complex.I)

@[simp]
theorem norm_unitPoint (theta : ℝ) : ‖unitPoint theta‖ = 1 := by
  simp [unitPoint, Complex.norm_exp]

/-- The period-one parametrization used by number-theoretic Fourier sums. -/
def periodicPoint (theta : ℝ) : ℂ :=
  unitPoint (2 * Real.pi * theta)

@[simp]
theorem norm_periodicPoint (theta : ℝ) : ‖periodicPoint theta‖ = 1 := by
  simp [periodicPoint]

theorem periodic_periodicPoint : Function.Periodic periodicPoint 1 := by
  intro x
  rw [periodicPoint, periodicPoint, unitPoint, unitPoint]
  have harg : (((2 * Real.pi * (x + 1) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) + 2 * Real.pi * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Reducing a real phase modulo one does not change its circle point. -/
theorem periodicPoint_fract (x : ℝ) :
    periodicPoint (Int.fract x) = periodicPoint x := by
  have h := (periodic_periodicPoint.int_mul ⌊x⌋) (Int.fract x)
  rw [mul_one, Int.fract_add_floor] at h
  exact h.symm

/-- The value of a Problem 230 polynomial at `exp (theta * I)`. -/
def angularValue {n : ℕ} (a : Fin n → ℂ) (theta : ℝ) : ℂ :=
  ∑ i : Fin n, a i * unitPoint theta ^ (i.1 + 1)

@[simp]
theorem eval_phasePoly_unitPoint {n : ℕ} (a : Fin n → ℂ) (theta : ℝ) :
    (phasePoly a).eval (unitPoint theta) = angularValue a theta := by
  simp [angularValue, eval_phasePoly, phaseValue]

/-- Angularly stated, arbitrarily large one-sided ultraflat examples. -/
def HasAngularUltraflatUpper : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ N : ℕ,
    ∃ n : ℕ, max 2 N ≤ n ∧
      ∃ a : Fin n → ℂ, IsUnimodular a ∧
        ∀ theta : ℝ, ‖angularValue a theta‖ ≤
          (1 + epsilon) * Real.sqrt n

/-- A uniform angular estimate is the same estimate at every point of the
unit circle. -/
theorem hasUltraflatUpper_of_angular (h : HasAngularUltraflatUpper) :
    HasUltraflatUpper := by
  intro epsilon hepsilon N
  obtain ⟨n, hn, a, ha, hbound⟩ := h epsilon hepsilon N
  refine ⟨n, hn, a, ha, ?_⟩
  intro z hz
  obtain ⟨theta, htheta⟩ := (Complex.norm_eq_one_iff z).mp hz
  subst z
  simpa [eval_phasePoly, phaseValue, angularValue, unitPoint] using hbound theta

/-- An analytic polynomial with exponents `0, ..., n`. -/
def zerothValue {n : ℕ} (a : Fin (n + 1) → ℂ) (theta : ℝ) : ℂ :=
  ∑ i : Fin (n + 1), a i * unitPoint theta ^ i.1

/-- The exponent-zero value written with a period-one real parameter. -/
def normalizedZerothValue {n : ℕ} (a : Fin (n + 1) → ℂ) (theta : ℝ) : ℂ :=
  ∑ i : Fin (n + 1), a i * periodicPoint theta ^ i.1

theorem normalizedZerothValue_div_two_pi {n : ℕ}
    (a : Fin (n + 1) → ℂ) (theta : ℝ) :
    normalizedZerothValue a (theta / (2 * Real.pi)) = zerothValue a theta := by
  have hpoint : periodicPoint (theta / (2 * Real.pi)) = unitPoint theta := by
    apply congrArg unitPoint
    field_simp [Real.pi_ne_zero]
  simp [normalizedZerothValue, zerothValue, hpoint]

/-- Remove the constant coefficient and reindex the remaining coefficients. -/
def tailCoeffs {n : ℕ} (a : Fin (n + 1) → ℂ) : Fin n → ℂ :=
  fun i => a i.succ

theorem zerothValue_eq_const_add_angularValue {n : ℕ}
    (a : Fin (n + 1) → ℂ) (theta : ℝ) :
    zerothValue a theta = a 0 + angularValue (tailCoeffs a) theta := by
  classical
  rw [zerothValue, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one]
  congr 1

/-- Deleting a constant coefficient of norm at most one costs at most one in
the uniform norm. -/
theorem norm_angularValue_tail_le {n : ℕ}
    (a : Fin (n + 1) → ℂ) (ha0 : ‖a 0‖ ≤ 1) (theta : ℝ) :
    ‖angularValue (tailCoeffs a) theta‖ ≤ ‖zerothValue a theta‖ + 1 := by
  rw [zerothValue_eq_const_add_angularValue] at *
  have h := norm_sub_le (a 0 + angularValue (tailCoeffs a) theta) (a 0)
  simpa [add_sub_cancel_left] using h.trans (add_le_add_right ha0 _)

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos230/Asymptotics.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The final elementary asymptotics for Erdős Problem 230

The analytic construction uses the integer scales
`n = m^18`, `s = m^12`, and `K = m^15`.  All analytic and probabilistic error
terms are absorbed into `2 * m^8`.  This file proves that the resulting explicit
bound implies the one-sided ultraflat statement needed for Problem 230.
-/



noncomputable section

/-- The concrete output expected from the Gaussian--Poisson and finite-sign
construction.  The quantifier `M` makes the examples arbitrarily large. -/
def HasPowerUpperExamples : Prop :=
  ∀ M : ℕ, ∃ m : ℕ, max 2 M ≤ m ∧
    ∃ a : Fin (m ^ 18 + 1) → ℂ, IsUnimodular a ∧
      ∀ theta : ℝ, ‖zerothValue a theta‖ ≤
        (m : ℝ) ^ 9 + 2 * (m : ℝ) ^ 8

lemma sqrt_nat_pow_eighteen (m : ℕ) :
    Real.sqrt ((m ^ 18 : ℕ) : ℝ) = (m : ℝ) ^ 9 := by
  rw [Nat.cast_pow]
  have h : (m : ℝ) ^ 18 = ((m : ℝ) ^ 9) ^ 2 := by ring
  rw [h, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  positivity

/-- A main term `m^9 = sqrt (m^18)` and error `m^8` give relative error
tending to zero.  Removing the constant coefficient contributes one more,
which is absorbed by the same comparison. -/
theorem hasAngularUltraflatUpper_of_power_examples
    (hpower : HasPowerUpperExamples) : HasAngularUltraflatUpper := by
  intro epsilon hepsilon N
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 3 / epsilon < k := exists_nat_gt (3 / epsilon)
  obtain ⟨m, hm, a, ha, hbound⟩ := hpower (max N k)
  have hm2 : 2 ≤ m := (le_max_left 2 (max N k)).trans hm
  have hmN : N ≤ m :=
    le_trans (le_trans (le_max_left N k) (le_max_right 2 (max N k))) hm
  have hmk : k ≤ m :=
    le_trans (le_trans (le_max_right N k) (le_max_right 2 (max N k))) hm
  refine ⟨m ^ 18, ?_, tailCoeffs a, ?_, ?_⟩
  · exact max_le
      (le_trans hm2 (Nat.le_pow (a := m) (b := 18) (by norm_num)))
      (le_trans hmN (Nat.le_pow (a := m) (b := 18) (by norm_num)))
  · intro i
    exact ha i.succ
  · intro theta
    have htail := norm_angularValue_tail_le a (by rw [ha 0]) theta
    have hraw : ‖angularValue (tailCoeffs a) theta‖ ≤
        (m : ℝ) ^ 9 + 2 * (m : ℝ) ^ 8 + 1 := by
      linarith [hbound theta]
    have hmreal : 3 / epsilon < (m : ℝ) :=
      hk.trans_le (by exact_mod_cast hmk)
    have hepsm : 3 < epsilon * (m : ℝ) := by
      calc
        3 = epsilon * (3 / epsilon) := by field_simp
        _ < epsilon * (m : ℝ) := mul_lt_mul_of_pos_left hmreal hepsilon
    have hmone : 1 ≤ (m : ℝ) ^ 8 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
      exact one_le_pow₀ this
    have herr : 2 * (m : ℝ) ^ 8 + 1 ≤ epsilon * (m : ℝ) ^ 9 := by
      calc
        2 * (m : ℝ) ^ 8 + 1 ≤ 3 * (m : ℝ) ^ 8 := by linarith
        _ ≤ (epsilon * (m : ℝ)) * (m : ℝ) ^ 8 := by gcongr
        _ = epsilon * (m : ℝ) ^ 9 := by ring
    rw [sqrt_nat_pow_eighteen]
    calc
      ‖angularValue (tailCoeffs a) theta‖ ≤
          (m : ℝ) ^ 9 + (2 * (m : ℝ) ^ 8 + 1) := by
        simpa [add_assoc] using hraw
      _ ≤ (m : ℝ) ^ 9 + epsilon * (m : ℝ) ^ 9 := by gcongr
      _ = (1 + epsilon) * (m : ℝ) ^ 9 := by ring

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos230/GaussianCutoff.lean` -/

section
/-!
# Gaussian cutoffs for Erdős Problem 230

This file develops the elementary real-variable estimates for the normalized
Gaussian cutoff used in the ultraflat-polynomial construction.  The scale is
a positive real number; the cutoff locations and sampling points are natural
numbers, coerced to `ℝ` only at the analytic boundary.
-/

namespace GaussianCutoff

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

/-- The normalized real Gaussian of scale `s`. -/
def phi (s x : ℝ) : ℝ :=
  s⁻¹ * Real.exp (-Real.pi * (x / s) ^ 2)

/-- The Gaussian smoothing of the indicator of `[K, n-K]`. -/
def chi (s : ℝ) (K n : ℕ) (x : ℝ) : ℝ :=
  ∫ y in (K : ℝ)..(n - K : ℕ), phi s (x - y)

lemma phi_eq_exp_neg_mul_sq {s : ℝ} (hs : s ≠ 0) (x : ℝ) :
    phi s x = s⁻¹ * Real.exp (-(Real.pi / s ^ 2) * x ^ 2) := by
  unfold phi
  apply congrArg (fun t : ℝ => s⁻¹ * Real.exp t)
  field_simp [hs]

lemma phi_nonneg {s : ℝ} (hs : 0 < s) (x : ℝ) : 0 ≤ phi s x := by
  exact mul_nonneg (inv_nonneg.mpr hs.le) (Real.exp_pos _).le

lemma phi_pos {s : ℝ} (hs : 0 < s) (x : ℝ) : 0 < phi s x := by
  exact mul_pos (inv_pos.mpr hs) (Real.exp_pos _)

@[simp] lemma phi_neg (s x : ℝ) : phi s (-x) = phi s x := by
  simp only [phi, neg_div, neg_sq]

lemma continuous_phi {s : ℝ} : Continuous (phi s) := by
  unfold phi
  fun_prop

lemma integrable_phi {s : ℝ} (hs : 0 < s) : Integrable (phi s) := by
  have hb : 0 < Real.pi / s ^ 2 := div_pos Real.pi_pos (sq_pos_of_pos hs)
  have h := (integrable_exp_neg_mul_sq hb).const_mul s⁻¹
  convert h using 1
  funext x
  exact phi_eq_exp_neg_mul_sq hs.ne' x

/-- The normalization was chosen so that the Gaussian has total mass one. -/
theorem integral_phi {s : ℝ} (hs : 0 < s) : ∫ x : ℝ, phi s x = 1 := by
  have hfun : phi s = fun x : ℝ =>
      s⁻¹ * Real.exp (-(Real.pi / s ^ 2) * x ^ 2) := by
    funext x
    exact phi_eq_exp_neg_mul_sq hs.ne' x
  rw [hfun, integral_const_mul, integral_gaussian]
  have hquot : Real.pi / (Real.pi / s ^ 2) = s ^ 2 := by
    field_simp [Real.pi_ne_zero, hs.ne']
  rw [hquot, Real.sqrt_sq_eq_abs, abs_of_pos hs]
  field_simp

/-- Translation and reflection do not change the total Gaussian mass. -/
theorem integral_phi_sub_left {s x : ℝ} (hs : 0 < s) :
    ∫ y : ℝ, phi s (x - y) = 1 := by
  rw [(volume : Measure ℝ).measurePreserving_sub_left x |>.integral_comp
    (Homeomorph.subLeft x).isClosedEmbedding.measurableEmbedding]
  exact integral_phi hs

/-- The Gaussian upper tail, beginning at `r`. -/
def gaussianTail (s r : ℝ) : ℝ :=
  ∫ x in Ioi r, phi s x

lemma integrable_phi_sub_left {s x : ℝ} (hs : 0 < s) :
    Integrable (fun y : ℝ => phi s (x - y)) := by
  exact ((volume : Measure ℝ).measurePreserving_sub_left x).integrable_comp_emb
      (Homeomorph.subLeft x).isClosedEmbedding.measurableEmbedding |>.2 (integrable_phi hs)

lemma cutoff_endpoints_order {K n : ℕ} (hKn : 2 * K ≤ n) :
    (K : ℝ) ≤ (n - K : ℕ) := by
  norm_cast
  omega

theorem chi_nonneg {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) (x : ℝ) :
    0 ≤ chi s K n x := by
  unfold chi
  apply intervalIntegral.integral_nonneg_of_forall (cutoff_endpoints_order hKn)
  exact fun y => phi_nonneg hs (x - y)

theorem chi_le_one {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) (x : ℝ) :
    chi s K n x ≤ 1 := by
  rw [chi, intervalIntegral.integral_of_le (cutoff_endpoints_order hKn)]
  calc
    (∫ y in Ioc (K : ℝ) (n - K : ℕ), phi s (x - y)) ≤
        ∫ y : ℝ, phi s (x - y) := by
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun y => phi_nonneg hs (x - y))
        (integrable_phi_sub_left hs)
    _ = 1 := integral_phi_sub_left hs

theorem chi_mem_Icc {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) (x : ℝ) :
    chi s K n x ∈ Icc 0 1 :=
  ⟨chi_nonneg hs hKn x, chi_le_one hs hKn x⟩

lemma gaussianTail_nonneg {s : ℝ} (hs : 0 < s) (r : ℝ) :
    0 ≤ gaussianTail s r := by
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => phi_nonneg hs x)

lemma integrableOn_phi_Ioi {s : ℝ} (hs : 0 < s) (r : ℝ) :
    IntegrableOn (phi s) (Ioi r) :=
  (integrable_phi hs).integrableOn

lemma integral_phi_Iic_neg_eq_tail {s : ℝ} (r : ℝ) :
    (∫ x in Iic (-r), phi s x) = gaussianTail s r := by
  rw [gaussianTail]
  calc
    (∫ x in Iic (-r), phi s x) = ∫ x in Iic (-r), phi s (-x) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro x _
      simp
    _ = ∫ x in Ioi r, phi s x := by simpa using integral_comp_neg_Iic (-r) (phi s)

lemma chi_eq_shifted_integral (s : ℝ) (K n : ℕ) (x : ℝ) :
    chi s K n x = ∫ u in x - (n - K : ℕ)..x - K, phi s u := by
  exact intervalIntegral.integral_comp_sub_left (phi s) x

/-- Missing Gaussian mass from an interval is exactly the sum of its two tails. -/
theorem one_sub_integral_neg_to_eq_tail_add_tail {s : ℝ} (hs : 0 < s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 - (∫ x in -a..b, phi s x) = gaussianTail s a + gaussianTail s b := by
  have hab : -a ≤ b := by linarith
  have hdisj : Disjoint (Iic (-a)) (Ioi b) := by
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact (not_lt_of_ge (hxa.trans hab)) hxb
  have hunion :
      (∫ x in Iic (-a) ∪ Ioi b, phi s x) =
        (∫ x in Iic (-a), phi s x) + ∫ x in Ioi b, phi s x := by
    exact setIntegral_union hdisj measurableSet_Ioi
      (integrable_phi hs).integrableOn (integrable_phi hs).integrableOn
  have hcompl : (Ioc (-a) b)ᶜ = Iic (-a) ∪ Ioi b := compl_Ioc
  have hmass := integral_add_compl (s := Ioc (-a) b) measurableSet_Ioc (integrable_phi hs)
  rw [integral_phi hs] at hmass
  rw [intervalIntegral.integral_of_le hab]
  rw [hcompl, hunion, integral_phi_Iic_neg_eq_tail] at hmass
  change (∫ x in Ioc (-a) b, phi s x) +
    (gaussianTail s a + gaussianTail s b) = 1 at hmass
  change 1 - (∫ x in Ioc (-a) b, phi s x) =
    gaussianTail s a + gaussianTail s b
  linarith

theorem one_sub_chi_eq_tail_add_tail {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (x : ℝ) (hxK : (K : ℝ) ≤ x) (hxn : x ≤ (n - K : ℕ)) :
    1 - chi s K n x =
      gaussianTail s (x - K) + gaussianTail s ((n - K : ℕ) - x) := by
  rw [chi_eq_shifted_integral]
  have hleft : 0 ≤ x - (K : ℝ) := sub_nonneg.mpr hxK
  have hright : 0 ≤ (n - K : ℕ) - x := sub_nonneg.mpr hxn
  convert one_sub_integral_neg_to_eq_tail_add_tail hs hright hleft using 1 <;> ring_nf

theorem one_sub_chi_sq_le_two_mul_tails {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) (x : ℝ) (hxK : (K : ℝ) ≤ x)
    (hxn : x ≤ (n - K : ℕ)) :
    1 - chi s K n x ^ 2 ≤
      2 * (gaussianTail s (x - K) + gaussianTail s ((n - K : ℕ) - x)) := by
  rcases chi_mem_Icc hs hKn x with ⟨hchi0, hchi1⟩
  rw [← one_sub_chi_eq_tail_add_tail hs x hxK hxn]
  calc
    1 - chi s K n x ^ 2 = (1 - chi s K n x) * (1 + chi s K n x) := by ring
    _ ≤ (1 - chi s K n x) * 2 := by
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ = 2 * (1 - chi s K n x) := by ring

lemma integrable_id_mul_phi {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : ℝ => x * phi s x) := by
  have hb : 0 < Real.pi / s ^ 2 := div_pos Real.pi_pos (sq_pos_of_pos hs)
  have h := (integrable_mul_exp_neg_mul_sq hb).const_mul s⁻¹
  convert h using 1
  funext x
  rw [phi_eq_exp_neg_mul_sq hs.ne']
  ring

/-- The first moment of the positive half of the normalized Gaussian. -/
theorem integral_id_mul_phi_Ioi {s : ℝ} (hs : 0 < s) :
    (∫ x in Ioi (0 : ℝ), x * phi s x) = s / (2 * Real.pi) := by
  let b : ℝ := Real.pi / s ^ 2
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hmoment : (∫ x : ℝ in Ioi 0, x * Real.exp (-b * x ^ 2)) = (2 * b)⁻¹ := by
    rw [← RCLike.ofReal_inj (K := ℂ), ← integral_ofReal]
    convert integral_mul_cexp_neg_mul_sq (b := (b : ℂ)) (by simpa using hb) using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      push_cast
      simp
    · push_cast
      rfl
  calc
    (∫ x in Ioi (0 : ℝ), x * phi s x) =
        s⁻¹ * ∫ x in Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      change x * phi s x = s⁻¹ * (x * Real.exp (-b * x ^ 2))
      rw [phi_eq_exp_neg_mul_sq hs.ne']
      dsimp [b]
      ring
    _ = s / (2 * Real.pi) := by
      rw [hmoment]
      dsimp [b]
      field_simp [Real.pi_ne_zero, hs.ne']

/-- The integrand whose integral over the positive half-line is the tail at `j`. -/
def tailKernel (s : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  if (j : ℝ) < x then phi s x else 0

lemma gaussianTail_nat_eq_integral_tailKernel (s : ℝ) (j : ℕ) :
    gaussianTail s j = ∫ x in Ioi (0 : ℝ), tailKernel s j x := by
  rw [gaussianTail]
  change (∫ x in Ioi (j : ℝ), phi s x) =
    ∫ x in Ioi (0 : ℝ), (Ioi (j : ℝ)).indicator (phi s) x
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hxj : x ∈ Ioi (j : ℝ)
  · have hx0 : x ∈ Ioi (0 : ℝ) := by
      show 0 < x
      exact lt_of_le_of_lt (Nat.cast_nonneg j) hxj
    simp [indicator_of_mem hxj, indicator_of_mem hx0]
  · simp [indicator_apply, hxj]

lemma integrableOn_tailKernel {s : ℝ} (hs : 0 < s) (j : ℕ) :
    IntegrableOn (tailKernel s j) (Ioi (0 : ℝ)) := by
  have h : Integrable ((Ioi (j : ℝ)).indicator (phi s)) :=
    (integrable_phi hs).indicator measurableSet_Ioi
  exact h.integrableOn

lemma sum_tailKernel_le {s : ℝ} (hs : 0 < s) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    (∑ j ∈ Finset.range (m + 1), tailKernel s j x) ≤ (x + 1) * phi s x := by
  let t : Finset ℕ := (Finset.range (m + 1)).filter fun j => (j : ℝ) < x
  have hsubset : t ⊆ Finset.range (Nat.ceil x) := by
    intro j hj
    simp only [t, Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact Nat.lt_ceil.mpr hj.2
  have hcardNat : t.card ≤ Nat.ceil x := by
    simpa using Finset.card_le_card hsubset
  have hcard : (t.card : ℝ) ≤ x + 1 := by
    calc
      (t.card : ℝ) ≤ (Nat.ceil x : ℕ) := by exact_mod_cast hcardNat
      _ ≤ x + 1 := (Nat.ceil_lt_add_one hx.le).le
  have hphi : 0 ≤ phi s x := phi_nonneg hs x
  change (∑ j ∈ Finset.range (m + 1), if (j : ℝ) < x then phi s x else 0) ≤
    (x + 1) * phi s x
  rw [← Finset.sum_filter]
  change (∑ _j ∈ t, phi s x) ≤ (x + 1) * phi s x
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcard hphi

lemma integral_add_one_mul_phi_Ioi_le {s : ℝ} (hs : 0 < s) :
    (∫ x in Ioi (0 : ℝ), (x + 1) * phi s x) ≤ s + 1 := by
  have hhalf : (∫ x in Ioi (0 : ℝ), phi s x) ≤ 1 := by
    calc
      (∫ x in Ioi (0 : ℝ), phi s x) ≤ ∫ x : ℝ, phi s x := by
        exact integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall (phi_nonneg hs)) (integrable_phi hs)
      _ = 1 := integral_phi hs
  have hmoment : (∫ x in Ioi (0 : ℝ), x * phi s x) ≤ s := by
    rw [integral_id_mul_phi_Ioi hs]
    have hden : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    exact (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2 (by nlinarith)
  have hidint : IntegrableOn (fun x : ℝ => x * phi s x) (Ioi 0) :=
    (integrable_id_mul_phi hs).integrableOn
  have hphiint : IntegrableOn (phi s) (Ioi 0) := (integrable_phi hs).integrableOn
  calc
    (∫ x in Ioi (0 : ℝ), (x + 1) * phi s x) =
        (∫ x in Ioi (0 : ℝ), x * phi s x) + ∫ x in Ioi (0 : ℝ), phi s x := by
      rw [← integral_add hidint hphiint]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      ring
    _ ≤ s + 1 := add_le_add hmoment hhalf

/-- A finite sum of integer Gaussian tails costs at most one scale plus one. -/
theorem sum_gaussianTail_range_le {s : ℝ} (hs : 0 < s) (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), gaussianTail s j) ≤ s + 1 := by
  calc
    (∑ j ∈ Finset.range (m + 1), gaussianTail s j) =
        ∫ x in Ioi (0 : ℝ), ∑ j ∈ Finset.range (m + 1), tailKernel s j x := by
      simp_rw [gaussianTail_nat_eq_integral_tailKernel]
      rw [integral_finsetSum]
      intro j _
      exact integrableOn_tailKernel hs j
    _ ≤ ∫ x in Ioi (0 : ℝ), (x + 1) * phi s x := by
      apply integral_mono_ae
      · exact integrable_finsetSum _ fun j _ => integrableOn_tailKernel hs j
      · exact ((integrable_id_mul_phi hs).add (integrable_phi hs)).integrableOn.congr_fun
          (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact sum_tailKernel_le hs m hx
    _ ≤ s + 1 := integral_add_one_mul_phi_Ioi_le hs

lemma gaussianTail_antitone {s : ℝ} (hs : 0 < s) : Antitone (gaussianTail s) := by
  intro a b hab
  unfold gaussianTail
  exact integral_mono_measure
    (Measure.restrict_mono (by intro x hx; exact hab.trans_lt hx) le_rfl)
    (Filter.Eventually.of_forall fun x => le_of_lt (phi_pos hs x))
    ((integrable_phi hs).integrableOn)

theorem summable_gaussianTail_nat {s : ℝ} (hs : 0 < s) :
    Summable (fun j : ℕ => gaussianTail s j) := by
  apply summable_of_sum_range_le (fun j => gaussianTail_nonneg hs j)
  intro m
  calc
    (∑ j ∈ Finset.range m, gaussianTail s j) ≤
        ∑ j ∈ Finset.range (m + 1), gaussianTail s j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_add_right m 1))
      intro j _ _
      exact gaussianTail_nonneg hs j
    _ ≤ s + 1 := sum_gaussianTail_range_le hs m

theorem tsum_gaussianTail_nat_le {s : ℝ} (hs : 0 < s) :
    (∑' j : ℕ, gaussianTail s j) ≤ s + 1 := by
  apply Real.tsum_le_of_sum_range_le (fun j => gaussianTail_nonneg hs j)
  intro m
  calc
    (∑ j ∈ Finset.range m, gaussianTail s j) ≤
        ∑ j ∈ Finset.range (m + 1), gaussianTail s j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_add_right m 1))
      intro j _ _
      exact gaussianTail_nonneg hs j
    _ ≤ s + 1 := sum_gaussianTail_range_le hs m

lemma chi_le_tail_left {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n)
    (x : ℝ) : chi s K n x ≤ gaussianTail s (K - x) := by
  have hab : x - (n - K : ℕ) ≤ x - K := by
    linarith [cutoff_endpoints_order hKn]
  rw [chi_eq_shifted_integral, intervalIntegral.integral_of_le hab]
  calc
    (∫ u in Ioc (x - (n - K : ℕ)) (x - K), phi s u) ≤
        ∫ u in Iic (x - K), phi s u := by
      exact integral_mono_measure
        (Measure.restrict_mono (by intro u hu; exact hu.2) le_rfl)
        (Filter.Eventually.of_forall (phi_nonneg hs))
        (integrable_phi hs).integrableOn
    _ = gaussianTail s (K - x) := by
      have heq : x - (K : ℝ) = -(K - x) := by ring
      rw [heq, integral_phi_Iic_neg_eq_tail]

lemma chi_le_tail_right {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n)
    (x : ℝ) :
    chi s K n x ≤ gaussianTail s (x - (n - K : ℕ)) := by
  have hab : x - (n - K : ℕ) ≤ x - K := by
    linarith [cutoff_endpoints_order hKn]
  rw [chi_eq_shifted_integral, intervalIntegral.integral_of_le hab]
  calc
    (∫ u in Ioc (x - (n - K : ℕ)) (x - K), phi s u) ≤
        ∫ u in Ioi (x - (n - K : ℕ)), phi s u := by
      exact integral_mono_measure
        (Measure.restrict_mono (by intro u hu; exact hu.1) le_rfl)
        (Filter.Eventually.of_forall (phi_nonneg hs))
        (integrable_phi hs).integrableOn
    _ = gaussianTail s (x - (n - K : ℕ)) := rfl

/-- The exponential factor gained once the Gaussian is sampled at distance `K`. -/
def cutoffExp (s : ℝ) (K : ℕ) : ℝ :=
  Real.exp (-Real.pi * ((K : ℝ) / s) ^ 2 / 2)

lemma cutoffExp_nonneg (s : ℝ) (K : ℕ) : 0 ≤ cutoffExp s K := by
  exact (Real.exp_pos _).le

lemma phi_le_two_mul_cutoffExp_mul_phi_two {s : ℝ} (hs : 0 < s) (K : ℕ)
    {x : ℝ} (hx : (K : ℝ) ≤ x) :
    phi s x ≤ 2 * cutoffExp s K * phi (2 * s) x := by
  have hx0 : 0 ≤ x := (Nat.cast_nonneg K).trans hx
  have hsq : ((K : ℝ) : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
  let d : ℝ := Real.pi / s ^ 2
  have hd : 0 < d := div_pos Real.pi_pos (sq_pos_of_pos hs)
  have hmain : -Real.pi * (x / s) ^ 2 = -d * x ^ 2 := by
    dsimp [d]
    field_simp [hs.ne']
  have hK : -Real.pi * ((K : ℝ) / s) ^ 2 / 2 = -d * (K : ℝ) ^ 2 / 2 := by
    dsimp [d]
    field_simp [hs.ne']
  have htwo : -Real.pi * (x / (2 * s)) ^ 2 = -d * x ^ 2 / 4 := by
    dsimp [d]
    field_simp [hs.ne']
    ring
  have harg : -Real.pi * (x / s) ^ 2 ≤
      -Real.pi * ((K : ℝ) / s) ^ 2 / 2 + -Real.pi * (x / (2 * s)) ^ 2 := by
    rw [hmain, hK, htwo]
    nlinarith
  unfold phi cutoffExp
  have hrhs :
      2 * Real.exp (-Real.pi * ((K : ℝ) / s) ^ 2 / 2) *
          ((2 * s)⁻¹ * Real.exp (-Real.pi * (x / (2 * s)) ^ 2)) =
        s⁻¹ * Real.exp (-Real.pi * ((K : ℝ) / s) ^ 2 / 2 +
          -Real.pi * (x / (2 * s)) ^ 2) := by
    rw [Real.exp_add]
    field_simp [hs.ne']
  rw [hrhs]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (inv_nonneg.mpr hs.le)

lemma gaussianTail_le_two_mul_cutoffExp_mul_tail_two {s : ℝ} (hs : 0 < s) (K : ℕ)
    {r : ℝ} (hr : (K : ℝ) ≤ r) :
    gaussianTail s r ≤ 2 * cutoffExp s K * gaussianTail (2 * s) r := by
  unfold gaussianTail
  rw [← integral_const_mul]
  apply integral_mono_ae
  · exact (integrable_phi hs).integrableOn
  · exact ((integrable_phi (mul_pos two_pos hs)).const_mul (2 * cutoffExp s K)).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact phi_le_two_mul_cutoffExp_mul_phi_two hs K (hr.trans (le_of_lt hx))

/-- Integer samples strictly to the left of `[0,n]`. -/
def outsideLeft (s : ℝ) (K n j : ℕ) : ℝ :=
  chi s K n (-((j + 1 : ℕ) : ℝ))

/-- Integer samples strictly to the right of `[0,n]`. -/
def outsideRight (s : ℝ) (K n j : ℕ) : ℝ :=
  chi s K n ((n + j + 1 : ℕ) : ℝ)

lemma outsideLeft_le_scaled_tail {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n)
    (j : ℕ) :
    outsideLeft s K n j ≤ 2 * cutoffExp s K * gaussianTail (2 * s) j := by
  have hchi : outsideLeft s K n j ≤ gaussianTail s (K + j + 1) := by
    unfold outsideLeft
    simpa only [sub_neg_eq_add, Nat.cast_add, Nat.cast_one, add_assoc] using
      chi_le_tail_left hs hKn (-((j + 1 : ℕ) : ℝ))
  have hscale : gaussianTail s (K + j + 1) ≤
      2 * cutoffExp s K * gaussianTail (2 * s) (K + j + 1) :=
    gaussianTail_le_two_mul_cutoffExp_mul_tail_two hs K (by norm_cast; omega)
  have hmono : gaussianTail (2 * s) (K + j + 1) ≤ gaussianTail (2 * s) j :=
    gaussianTail_antitone (mul_pos two_pos hs) (by norm_cast; omega)
  have hfac : 0 ≤ 2 * cutoffExp s K := mul_nonneg (by norm_num) (cutoffExp_nonneg s K)
  exact hchi.trans (hscale.trans (mul_le_mul_of_nonneg_left hmono hfac))

lemma outsideRight_le_scaled_tail {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) (j : ℕ) :
    outsideRight s K n j ≤ 2 * cutoffExp s K * gaussianTail (2 * s) j := by
  have hchi : outsideRight s K n j ≤ gaussianTail s (K + j + 1) := by
    unfold outsideRight
    have hsub : n - K ≤ n + j + 1 := by omega
    have harg : ((n + j + 1 : ℕ) : ℝ) - ((n - K : ℕ) : ℝ) =
        (K : ℝ) + j + 1 := by
      rw [← Nat.cast_sub hsub]
      norm_cast
      omega
    rw [← harg]
    exact chi_le_tail_right hs hKn _
  have hscale : gaussianTail s (K + j + 1) ≤
      2 * cutoffExp s K * gaussianTail (2 * s) (K + j + 1) :=
    gaussianTail_le_two_mul_cutoffExp_mul_tail_two hs K (by norm_cast; omega)
  have hmono : gaussianTail (2 * s) (K + j + 1) ≤ gaussianTail (2 * s) j :=
    gaussianTail_antitone (mul_pos two_pos hs) (by norm_cast; omega)
  have hfac : 0 ≤ 2 * cutoffExp s K := mul_nonneg (by norm_num) (cutoffExp_nonneg s K)
  exact hchi.trans (hscale.trans (mul_le_mul_of_nonneg_left hmono hfac))

theorem summable_outsideLeft {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) :
    Summable (outsideLeft s K n) := by
  apply summable_of_sum_range_le (fun j => chi_nonneg hs hKn _)
  intro m
  calc
    (∑ j ∈ Finset.range m, outsideLeft s K n j) ≤
        ∑ j ∈ Finset.range m, 2 * cutoffExp s K * gaussianTail (2 * s) j := by
      exact Finset.sum_le_sum fun j _ => outsideLeft_le_scaled_tail hs hKn j
    _ = 2 * cutoffExp s K * ∑ j ∈ Finset.range m, gaussianTail (2 * s) j := by
      rw [Finset.mul_sum]
    _ ≤ 2 * cutoffExp s K * (2 * s + 1) := by
      exact mul_le_mul_of_nonneg_left
        (((summable_gaussianTail_nat (mul_pos two_pos hs)).sum_le_tsum (Finset.range m)
          (fun j _ => gaussianTail_nonneg (mul_pos two_pos hs) j)).trans
            (tsum_gaussianTail_nat_le (mul_pos two_pos hs)))
        (mul_nonneg (by norm_num) (cutoffExp_nonneg s K))

theorem summable_outsideRight {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) :
    Summable (outsideRight s K n) := by
  apply summable_of_sum_range_le (fun j => chi_nonneg hs hKn _)
  intro m
  calc
    (∑ j ∈ Finset.range m, outsideRight s K n j) ≤
        ∑ j ∈ Finset.range m, 2 * cutoffExp s K * gaussianTail (2 * s) j := by
      exact Finset.sum_le_sum fun j _ => outsideRight_le_scaled_tail hs hKn j
    _ = 2 * cutoffExp s K * ∑ j ∈ Finset.range m, gaussianTail (2 * s) j := by
      rw [Finset.mul_sum]
    _ ≤ 2 * cutoffExp s K * (2 * s + 1) := by
      exact mul_le_mul_of_nonneg_left
        (((summable_gaussianTail_nat (mul_pos two_pos hs)).sum_le_tsum (Finset.range m)
          (fun j _ => gaussianTail_nonneg (mul_pos two_pos hs) j)).trans
            (tsum_gaussianTail_nat_le (mul_pos two_pos hs)))
        (mul_nonneg (by norm_num) (cutoffExp_nonneg s K))

/-- Explicit exponentially small `ℓ¹` mass discarded outside the integer interval `[0,n]`. -/
theorem tsum_outside_le {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) :
    (∑' j : ℕ, outsideLeft s K n j) + ∑' j : ℕ, outsideRight s K n j ≤
      4 * cutoffExp s K * (2 * s + 1) := by
  have hleft : (∑' j : ℕ, outsideLeft s K n j) ≤
      2 * cutoffExp s K * (2 * s + 1) := by
    apply (summable_outsideLeft hs hKn).tsum_le_of_sum_le
    intro u
    calc
      (∑ j ∈ u, outsideLeft s K n j) ≤
          ∑ j ∈ u, 2 * cutoffExp s K * gaussianTail (2 * s) j := by
        exact Finset.sum_le_sum fun j _ => outsideLeft_le_scaled_tail hs hKn j
      _ ≤ 2 * cutoffExp s K * (2 * s + 1) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (((summable_gaussianTail_nat (mul_pos two_pos hs)).sum_le_tsum u
            (fun j _ => gaussianTail_nonneg (mul_pos two_pos hs) j)).trans
              (tsum_gaussianTail_nat_le (mul_pos two_pos hs)))
          (mul_nonneg (by norm_num) (cutoffExp_nonneg s K))
  have hright : (∑' j : ℕ, outsideRight s K n j) ≤
      2 * cutoffExp s K * (2 * s + 1) := by
    apply (summable_outsideRight hs hKn).tsum_le_of_sum_le
    intro u
    calc
      (∑ j ∈ u, outsideRight s K n j) ≤
          ∑ j ∈ u, 2 * cutoffExp s K * gaussianTail (2 * s) j := by
        exact Finset.sum_le_sum fun j _ => outsideRight_le_scaled_tail hs hKn j
      _ ≤ 2 * cutoffExp s K * (2 * s + 1) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (((summable_gaussianTail_nat (mul_pos two_pos hs)).sum_le_tsum u
            (fun j _ => gaussianTail_nonneg (mul_pos two_pos hs) j)).trans
              (tsum_gaussianTail_nat_le (mul_pos two_pos hs)))
          (mul_nonneg (by norm_num) (cutoffExp_nonneg s K))
  nlinarith

/-- At the scales used in the construction, the explicit `ℓ¹` truncation bound is below one
already for `m ≥ 2`. -/
theorem cutoffExp_pow_bound_lt_one {m : ℕ} (hm : 2 ≤ m) :
    4 * cutoffExp ((m ^ 12 : ℕ) : ℝ) (m ^ 15) *
        (2 * ((m ^ 12 : ℕ) : ℝ) + 1) < 1 := by
  let x : ℝ := m
  have hx : 2 ≤ x := by
    dsimp [x]
    exact_mod_cast hm
  have hxpos : 0 < x := by linarith
  have hratio : (((m ^ 15 : ℕ) : ℝ) / ((m ^ 12 : ℕ) : ℝ)) = x ^ 3 := by
    dsimp [x]
    push_cast
    field_simp [ne_of_gt hxpos]
  let y : ℝ := x ^ 6
  have hy64 : 64 ≤ y := by
    dsimp [y]
    have := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hx 6
    norm_num at this ⊢
    exact this
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy64
  let A : ℝ := Real.pi * y / 2
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hAlower : (3 / 2 : ℝ) * y < A := by
    dsimp [A]
    have := mul_lt_mul_of_pos_right Real.pi_gt_three hypos
    linarith
  have hcubes : ((3 / 2 : ℝ) * y) ^ 3 < A ^ 3 := by
    exact pow_lt_pow_left₀ hAlower (by positivity) (by norm_num)
  have hygrowth : 64 * y ^ 2 ≤ y ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy64) (sq_nonneg y)]
  have hpoly : 4 * (2 * x ^ 12 + 1) < A ^ 3 / 6 := by
    have hxy : x ^ 12 = y ^ 2 := by dsimp [y]; ring
    rw [hxy]
    nlinarith
  have hexplower : A ^ 3 / 6 ≤ Real.exp A := by
    have h := Real.pow_div_factorial_le_exp A hA0 3
    norm_num at h ⊢
    exact h
  have hden : 4 * (2 * x ^ 12 + 1) < Real.exp A := hpoly.trans_le hexplower
  have hfinal : 4 * Real.exp (-A) * (2 * x ^ 12 + 1) < 1 := by
    rw [Real.exp_neg]
    have hdiv := (div_lt_one (Real.exp_pos A)).2 hden
    rw [div_eq_mul_inv] at hdiv
    nlinarith
  have hcut : cutoffExp ((m ^ 12 : ℕ) : ℝ) (m ^ 15) = Real.exp (-A) := by
    unfold cutoffExp
    rw [hratio]
    congr 1
    dsimp [A, y]
    ring
  rw [hcut]
  simpa [x] using hfinal

theorem eventually_cutoffExp_pow_bound_lt_one :
    ∀ᶠ m : ℕ in Filter.atTop,
      4 * cutoffExp ((m ^ 12 : ℕ) : ℝ) (m ^ 15) *
          (2 * ((m ^ 12 : ℕ) : ℝ) + 1) < 1 := by
  filter_upwards [Filter.eventually_ge_atTop 2] with m hm
  exact cutoffExp_pow_bound_lt_one hm

/-- Direct specialization of the truncation estimate at `(s,K,n)=(m¹²,m¹⁵,m¹⁸)`. -/
theorem tsum_outside_pow_lt_one {m : ℕ} (hm : 2 ≤ m) :
    (∑' j : ℕ, outsideLeft ((m ^ 12 : ℕ) : ℝ) (m ^ 15) (m ^ 18) j) +
        ∑' j : ℕ, outsideRight ((m ^ 12 : ℕ) : ℝ) (m ^ 15) (m ^ 18) j < 1 := by
  have hmpos : 0 < m := by omega
  have hs : 0 < ((m ^ 12 : ℕ) : ℝ) := by positivity
  have hm3 : 2 ≤ m ^ 3 := by
    have hpow := pow_le_pow_left' hm 3
    norm_num at hpow
    omega
  have hKn : 2 * m ^ 15 ≤ m ^ 18 := by
    calc
      2 * m ^ 15 ≤ m ^ 3 * m ^ 15 := Nat.mul_le_mul_right (m ^ 15) hm3
      _ = m ^ 18 := by ring
  exact (tsum_outside_le hs hKn).trans_lt (cutoffExp_pow_bound_lt_one hm)

lemma outsideLeft_sq_le {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n)
    (j : ℕ) : outsideLeft s K n j ^ 2 ≤ gaussianTail s K * gaussianTail s j := by
  have hchi0 : 0 ≤ outsideLeft s K n j := chi_nonneg hs hKn _
  have hchi : outsideLeft s K n j ≤ gaussianTail s (K + j + 1) := by
    unfold outsideLeft
    simpa only [sub_neg_eq_add, Nat.cast_add, Nat.cast_one, add_assoc] using
      chi_le_tail_left hs hKn (-((j + 1 : ℕ) : ℝ))
  have htK : gaussianTail s (K + j + 1) ≤ gaussianTail s K :=
    gaussianTail_antitone hs (by norm_cast; omega)
  have htj : gaussianTail s (K + j + 1) ≤ gaussianTail s j :=
    gaussianTail_antitone hs (by norm_cast; omega)
  nlinarith [gaussianTail_nonneg hs K, gaussianTail_nonneg hs j]

lemma outsideRight_sq_le {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n)
    (j : ℕ) : outsideRight s K n j ^ 2 ≤ gaussianTail s K * gaussianTail s j := by
  have hchi0 : 0 ≤ outsideRight s K n j := chi_nonneg hs hKn _
  have hchi : outsideRight s K n j ≤ gaussianTail s (K + j + 1) := by
    unfold outsideRight
    have hsub : n - K ≤ n + j + 1 := by omega
    have harg : ((n + j + 1 : ℕ) : ℝ) - ((n - K : ℕ) : ℝ) =
        (K : ℝ) + j + 1 := by
      rw [← Nat.cast_sub hsub]
      norm_cast
      omega
    rw [← harg]
    exact chi_le_tail_right hs hKn _
  have htK : gaussianTail s (K + j + 1) ≤ gaussianTail s K :=
    gaussianTail_antitone hs (by norm_cast; omega)
  have htj : gaussianTail s (K + j + 1) ≤ gaussianTail s j :=
    gaussianTail_antitone hs (by norm_cast; omega)
  nlinarith [gaussianTail_nonneg hs K, gaussianTail_nonneg hs j]

theorem summable_outsideLeft_sq {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) :
    Summable (fun j : ℕ => outsideLeft s K n j ^ 2) := by
  apply summable_of_sum_range_le (fun j => sq_nonneg (outsideLeft s K n j))
  intro m
  calc
    (∑ j ∈ Finset.range m, outsideLeft s K n j ^ 2) ≤
        ∑ j ∈ Finset.range m, gaussianTail s K * gaussianTail s j := by
      exact Finset.sum_le_sum fun j _ => outsideLeft_sq_le hs hKn j
    _ = gaussianTail s K * ∑ j ∈ Finset.range m, gaussianTail s j := by
      rw [Finset.mul_sum]
    _ ≤ gaussianTail s K * (s + 1) := by
      exact mul_le_mul_of_nonneg_left
        ((summable_gaussianTail_nat hs).sum_le_tsum (Finset.range m)
          (fun j _ => gaussianTail_nonneg hs j) |>.trans (tsum_gaussianTail_nat_le hs))
        (gaussianTail_nonneg hs K)

theorem summable_outsideRight_sq {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) : Summable (fun j : ℕ => outsideRight s K n j ^ 2) := by
  apply summable_of_sum_range_le (fun j => sq_nonneg (outsideRight s K n j))
  intro m
  calc
    (∑ j ∈ Finset.range m, outsideRight s K n j ^ 2) ≤
        ∑ j ∈ Finset.range m, gaussianTail s K * gaussianTail s j := by
      exact Finset.sum_le_sum fun j _ => outsideRight_sq_le hs hKn j
    _ = gaussianTail s K * ∑ j ∈ Finset.range m, gaussianTail s j := by
      rw [Finset.mul_sum]
    _ ≤ gaussianTail s K * (s + 1) := by
      exact mul_le_mul_of_nonneg_left
        ((summable_gaussianTail_nat hs).sum_le_tsum (Finset.range m)
          (fun j _ => gaussianTail_nonneg hs j) |>.trans (tsum_gaussianTail_nat_le hs))
        (gaussianTail_nonneg hs K)

/-- The squared integer mass discarded outside `[0,n]` is summable and has this explicit tail. -/
theorem tsum_outside_sq_le {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n) :
    (∑' j : ℕ, outsideLeft s K n j ^ 2) +
        ∑' j : ℕ, outsideRight s K n j ^ 2 ≤
      2 * gaussianTail s K * (s + 1) := by
  have hleft : (∑' j : ℕ, outsideLeft s K n j ^ 2) ≤
      gaussianTail s K * (s + 1) := by
    apply (summable_outsideLeft_sq hs hKn).tsum_le_of_sum_le
    intro u
    calc
      (∑ j ∈ u, outsideLeft s K n j ^ 2) ≤
          ∑ j ∈ u, gaussianTail s K * gaussianTail s j := by
        exact Finset.sum_le_sum fun j _ => outsideLeft_sq_le hs hKn j
      _ ≤ gaussianTail s K * (s + 1) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          ((summable_gaussianTail_nat hs).sum_le_tsum u
            (fun j _ => gaussianTail_nonneg hs j) |>.trans (tsum_gaussianTail_nat_le hs))
          (gaussianTail_nonneg hs K)
  have hright : (∑' j : ℕ, outsideRight s K n j ^ 2) ≤
      gaussianTail s K * (s + 1) := by
    apply (summable_outsideRight_sq hs hKn).tsum_le_of_sum_le
    intro u
    calc
      (∑ j ∈ u, outsideRight s K n j ^ 2) ≤
          ∑ j ∈ u, gaussianTail s K * gaussianTail s j := by
        exact Finset.sum_le_sum fun j _ => outsideRight_sq_le hs hKn j
      _ ≤ gaussianTail s K * (s + 1) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          ((summable_gaussianTail_nat hs).sum_le_tsum u
            (fun j _ => gaussianTail_nonneg hs j) |>.trans (tsum_gaussianTail_nat_le hs))
          (gaussianTail_nonneg hs K)
  nlinarith

/-- The loss in squared mass at an integer sampling point. -/
def cutoffDefect (s : ℝ) (K n k : ℕ) : ℝ :=
  1 - chi s K n k ^ 2

lemma cutoffDefect_le_one {s : ℝ} (_hs : 0 < s) {K n : ℕ} (_hKn : 2 * K ≤ n)
    (k : ℕ) : cutoffDefect s K n k ≤ 1 := by
  unfold cutoffDefect
  nlinarith [sq_nonneg (chi s K n k)]

lemma cutoffDefect_middle_le {s : ℝ} (hs : 0 < s) {K n : ℕ} (hKn : 2 * K ≤ n)
    {j : ℕ} (hj : j ≤ n - 2 * K) :
    cutoffDefect s K n (K + j) ≤
      2 * (gaussianTail s j + gaussianTail s ((((n - 2 * K) - j : ℕ) : ℝ))) := by
  have hKj : K + j ≤ n - K := by omega
  have hxK : (K : ℝ) ≤ (K + j : ℕ) := by norm_cast; omega
  have hxn : ((K + j : ℕ) : ℝ) ≤ (n - K : ℕ) := by exact_mod_cast hKj
  have harg : ((n - K : ℕ) : ℝ) - ((K + j : ℕ) : ℝ) =
      (((n - 2 * K) - j : ℕ) : ℝ) := by
    rw [← Nat.cast_sub hKj]
    congr 1
    omega
  have h := one_sub_chi_sq_le_two_mul_tails hs hKn ((K + j : ℕ) : ℝ) hxK hxn
  unfold cutoffDefect
  rw [harg] at h
  simpa only [Nat.cast_add, add_sub_cancel_left] using h

lemma sum_cutoffDefect_middle_le {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) :
    (∑ k ∈ Finset.Icc K (n - K), cutoffDefect s K n k) ≤ 4 * (s + 1) := by
  let m := n - 2 * K
  have hrewrite :
      (∑ k ∈ Finset.Icc K (n - K), cutoffDefect s K n k) =
        ∑ j ∈ Finset.range (m + 1), cutoffDefect s K n (K + j) := by
    have hlen : (n - K + 1) - K = m + 1 := by
      dsimp [m]
      omega
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    rw [hlen]
  rw [hrewrite]
  have hreflect :
      (∑ j ∈ Finset.range (m + 1), gaussianTail s (((m - j : ℕ) : ℝ))) =
        ∑ j ∈ Finset.range (m + 1), gaussianTail s j := by
    simpa using Finset.sum_range_reflect (fun j : ℕ => gaussianTail s j) (m + 1)
  calc
    (∑ j ∈ Finset.range (m + 1), cutoffDefect s K n (K + j)) ≤
        ∑ j ∈ Finset.range (m + 1),
          2 * (gaussianTail s j + gaussianTail s (((m - j : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa [m] using cutoffDefect_middle_le hs hKn (j := j) (by
        simp only [Finset.mem_range] at hj
        omega)
    _ = 4 * (∑ j ∈ Finset.range (m + 1), gaussianTail s j) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hreflect]
      ring
    _ ≤ 4 * (s + 1) := by
      exact mul_le_mul_of_nonneg_left (sum_gaussianTail_range_le hs m) (by norm_num)

/-- Total cutoff defect: two boundary strips plus four Gaussian-tail sums. -/
theorem sum_cutoffDefect_range_le {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) :
    (∑ k ∈ Finset.range (n + 1), cutoffDefect s K n k) ≤
      4 * (K : ℝ) + 4 * (s + 1) := by
  let L := Finset.range K
  let M := Finset.Icc K (n - K)
  let R := Finset.Ioc (n - K) n
  have hpartition : (L ∪ M) ∪ R = Finset.range (n + 1) := by
    ext k
    simp only [L, M, R, Finset.mem_union, Finset.mem_range, Finset.mem_Icc,
      Finset.mem_Ioc]
    omega
  have hLM : Disjoint L M := by
    rw [Finset.disjoint_left]
    intro k hkL hkM
    simp only [L, Finset.mem_range] at hkL
    simp only [M, Finset.mem_Icc] at hkM
    omega
  have hLMR : Disjoint (L ∪ M) R := by
    rw [Finset.disjoint_left]
    intro k hkLM hkR
    simp only [Finset.mem_union] at hkLM
    simp only [R, Finset.mem_Ioc] at hkR
    rcases hkLM with hkL | hkM
    · simp only [L, Finset.mem_range] at hkL
      omega
    · simp only [M, Finset.mem_Icc] at hkM
      omega
  have hL : (∑ k ∈ L, cutoffDefect s K n k) ≤ (K : ℝ) := by
    calc
      (∑ k ∈ L, cutoffDefect s K n k) ≤ ∑ _k ∈ L, (1 : ℝ) := by
        exact Finset.sum_le_sum fun k _ => cutoffDefect_le_one hs hKn k
      _ = (K : ℝ) := by simp [L]
  have hR : (∑ k ∈ R, cutoffDefect s K n k) ≤ (K : ℝ) := by
    calc
      (∑ k ∈ R, cutoffDefect s K n k) ≤ ∑ _k ∈ R, (1 : ℝ) := by
        exact Finset.sum_le_sum fun k _ => cutoffDefect_le_one hs hKn k
      _ = (K : ℝ) := by
        simp only [R, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
        norm_cast
        omega
  have hM : (∑ k ∈ M, cutoffDefect s K n k) ≤ 4 * (s + 1) := by
    exact sum_cutoffDefect_middle_le hs hKn
  rw [← hpartition, Finset.sum_union hLMR, Finset.sum_union hLM]
  nlinarith

/-- The total-defect estimate, expanded in the form used by later constructions. -/
theorem sum_one_sub_chi_sq_range_le {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) :
    (∑ k ∈ Finset.range (n + 1), (1 - chi s K n k ^ 2)) ≤
      4 * (K : ℝ) + 4 * (s + 1) := by
  simpa only [cutoffDefect] using sum_cutoffDefect_range_le hs hKn

end

end GaussianCutoff

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos230/GaussianPoisson.lean` -/

section
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/

/-!
# Gaussian--Poisson aliases for Erdős Problem 230

This file contains the analytic core of the Gaussian-smoothed chirp
construction.  Our exponential convention is `e x = exp (2 * π * I * x)`.
-/

open scoped BigOperators Interval
open MeasureTheory Set Real Complex

noncomputable section

namespace GaussianPoisson

/-- The number-theorists' exponential `exp (2 π i x)`. -/
def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

@[simp] theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  rw [e, Complex.norm_exp]
  simp

/-- Centre of the `h`-th Poisson alias. -/
def aliasCenter (n θ : ℝ) (h : ℤ) : ℝ := n * ((h : ℝ) + 1 / 2 - θ)

/-- Width of the positive Gaussian majorant of an alias. -/
def aliasWidthSq (n r : ℝ) : ℝ := n * (1 + r ^ 2) / r

/-- The positive Gaussian which majorizes the `h`-th alias integrand. -/
def aliasMajorant (n r θ : ℝ) (h : ℤ) (y : ℝ) : ℝ :=
  Real.exp
    (-π * (y - aliasCenter n θ h) ^ 2 /
      aliasWidthSq n r)

/-- The translate-free Gaussian used to bound every alias. -/
def majorantGaussian (n r t : ℝ) : ℝ :=
  Real.exp (-π * t ^ 2 / aliasWidthSq n r)

/-- The interval supporting the translated majorant of the `h`-th alias. -/
def aliasInterval (n K θ : ℝ) (h : ℤ) : Set ℝ :=
  Set.Ioc (K - aliasCenter n θ h) (n - K - aliasCenter n θ h)

/-- Oscillatory integral occurring in one Gaussian--Poisson alias. -/
def aliasIntegral (n r K θ : ℝ) (h : ℤ) : ℂ :=
  ∫ y in K..n - K,
    Complex.exp
      (π * Complex.I * (y - aliasCenter n θ h) ^ 2 /
        (n * (1 - Complex.I * r)))

/-- The pointwise integrand of a normalized Poisson alias. -/
def aliasAtom (n r θ y : ℝ) (h : ℤ) : ℂ :=
  e (-(aliasCenter n θ h) ^ 2 / (2 * n)) /
      (1 - Complex.I * r) ^ (1 / 2 : ℂ) *
    Complex.exp
      (π * Complex.I * (y - aliasCenter n θ h) ^ 2 /
        (n * (1 - Complex.I * r)))

/-- The normalized `h`-th alias. -/
def aliasTerm (n r K θ : ℝ) (h : ℤ) : ℂ :=
  e (-(aliasCenter n θ h) ^ 2 / (2 * n)) /
      (1 - Complex.I * r) ^ (1 / 2 : ℂ) *
    aliasIntegral n r K θ h

/-- The full Poisson-alias expansion of the smoothed chirp. -/
def aliasSum (n r K θ : ℝ) : ℂ :=
  ∑' h : ℤ, aliasTerm n r K θ h

/-! The following raw theta-series formulation is convenient for connecting
the alias expansion to the Gaussian-smoothed coefficients. -/

/-- Quadratic parameter in Jacobi's theta transformation. -/
def thetaA (n s : ℝ) : ℂ :=
  (1 - Complex.I * ((s ^ 2 / n : ℝ) : ℂ)) / ((s ^ 2 : ℝ) : ℂ)

/-- Linear parameter in Jacobi's theta transformation. -/
def thetaB (s θ y : ℝ) : ℂ :=
  y / s ^ 2 + Complex.I * (θ - 1 / 2)

/-- The Gaussian-smoothed chirp summand before applying the theta identity. -/
def gaussianChirpAtom (n s θ y : ℝ) (k : ℤ) : ℂ :=
  (s : ℂ)⁻¹ * Complex.exp
    (-π / s ^ 2 * ((k : ℂ) - y) ^ 2 +
      π * Complex.I / n * (k : ℂ) ^ 2 +
      2 * π * Complex.I * (θ - 1 / 2) * k)

/-- The normalized real Gaussian kernel used in the cutoff. -/
def gaussianKernel (s x : ℝ) : ℝ :=
  s⁻¹ * Real.exp (-π / s ^ 2 * x ^ 2)

/-- The Gaussian smoothing of the interval `[K,n-K]`, at an integer sample. -/
def gaussianCutoff (s K n : ℝ) (k : ℤ) : ℝ :=
  ∫ y in K..n - K, gaussianKernel s ((k : ℝ) - y)

/-- The quadratic chirp phase attached to the `k`-th coefficient. -/
def chirpPhase (n θ : ℝ) (k : ℤ) : ℝ :=
  (k : ℝ) ^ 2 / (2 * n) + (θ - 1 / 2) * k

theorem gaussianChirpAtom_eq_cutoffIntegrand
    (n s θ y : ℝ) (k : ℤ) (hn : 0 < n) (hs : 0 < s) :
    gaussianChirpAtom n s θ y k =
      (gaussianKernel s ((k : ℝ) - y) : ℂ) * e (chirpPhase n θ k) := by
  simp only [gaussianChirpAtom, gaussianKernel, chirpPhase, e]
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  conv_rhs => rw [mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  field_simp [hn.ne', hs.ne']
  ring

theorem norm_gaussianChirpAtom
    (n s θ y : ℝ) (k : ℤ) (hn : 0 < n) (hs : 0 < s) :
    ‖gaussianChirpAtom n s θ y k‖ =
      gaussianKernel s ((k : ℝ) - y) := by
  rw [gaussianChirpAtom_eq_cutoffIntegrand n s θ y k hn hs,
    norm_mul, norm_e, mul_one, Complex.norm_real,
    Real.norm_of_nonneg]
  exact mul_nonneg (inv_nonneg.mpr hs.le) (Real.exp_pos _).le

theorem gaussianKernel_eq_phi (s x : ℝ) (hs : 0 < s) :
    gaussianKernel s x = Erdos230.GaussianCutoff.phi s x := by
  unfold gaussianKernel Erdos230.GaussianCutoff.phi
  congr 2
  field_simp [hs.ne']

theorem gaussianCutoff_eq_chi (s : ℝ) (K n : ℕ) (k : ℤ)
    (hs : 0 < s) (hKn : K ≤ n) :
    gaussianCutoff s K n k = Erdos230.GaussianCutoff.chi s K n k := by
  simp only [gaussianCutoff, Erdos230.GaussianCutoff.chi,
    Nat.cast_sub hKn]
  apply intervalIntegral.integral_congr
  intro y _
  exact gaussianKernel_eq_phi s ((k : ℝ) - y) hs

theorem summable_chi_int (s : ℝ) (K n : ℕ)
    (hs : 0 < s) (hKn : 2 * K ≤ n) :
    Summable (fun k : ℤ => Erdos230.GaussianCutoff.chi s K n (k : ℝ)) := by
  have hrightTail : Summable (fun j : ℕ =>
      Erdos230.GaussianCutoff.chi s K n ((j + (n + 1) : ℕ) : ℝ)) := by
    convert Erdos230.GaussianCutoff.summable_outsideRight hs hKn using 1
    funext j
    simp only [Erdos230.GaussianCutoff.outsideRight]
    congr 2
    norm_cast
    omega
  have hright : Summable (fun j : ℕ =>
      Erdos230.GaussianCutoff.chi s K n (j : ℝ)) :=
    (summable_nat_add_iff (n + 1)).mp hrightTail
  have hleft : Summable (fun j : ℕ =>
      Erdos230.GaussianCutoff.chi s K n (((-((j : ℤ) + 1) : ℤ) : ℝ))) := by
    convert Erdos230.GaussianCutoff.summable_outsideLeft hs hKn using 1
    funext j
    simp only [Erdos230.GaussianCutoff.outsideLeft]
    congr 2
    norm_cast
  exact hright.of_nat_of_neg_add_one hleft

/-- The coefficient-series term of the Gaussian-cutoff chirp. -/
def cutoffChirpTerm (s : ℝ) (K n : ℕ) (θ : ℝ) (k : ℤ) : ℂ :=
  (Erdos230.GaussianCutoff.chi s K n (k : ℝ) : ℂ) *
    e (chirpPhase n θ k)

/-- The cutoff chirp retaining exactly the integer frequencies `0,...,n`. -/
def finiteCutoffChirp (s : ℝ) (K n : ℕ) (θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), cutoffChirpTerm s K n θ (k : ℤ)

theorem norm_cutoffChirpTerm (s : ℝ) (K n : ℕ) (θ : ℝ) (k : ℤ)
    (hs : 0 < s) (hKn : 2 * K ≤ n) :
    ‖cutoffChirpTerm s K n θ k‖ =
      Erdos230.GaussianCutoff.chi s K n (k : ℝ) := by
  rw [cutoffChirpTerm, norm_mul, norm_e, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Erdos230.GaussianCutoff.chi_nonneg hs hKn _)]

theorem summable_cutoffChirpTerm (s : ℝ) (K n : ℕ) (θ : ℝ)
    (hs : 0 < s) (hKn : 2 * K ≤ n) :
    Summable (cutoffChirpTerm s K n θ) := by
  apply Summable.of_norm
  exact (summable_chi_int s K n hs hKn).congr
    (fun k => (norm_cutoffChirpTerm s K n θ k hs hKn).symm)

theorem intervalIntegral_gaussianChirpAtom
    (n s K θ : ℝ) (k : ℤ) (hn : 0 < n) (hs : 0 < s) :
    (∫ y in K..n - K, gaussianChirpAtom n s θ y k) =
      (gaussianCutoff s K n k : ℂ) * e (chirpPhase n θ k) := by
  calc
    (∫ y in K..n - K, gaussianChirpAtom n s θ y k) =
        ∫ y in K..n - K,
          (gaussianKernel s ((k : ℝ) - y) : ℂ) * e (chirpPhase n θ k) := by
      apply intervalIntegral.integral_congr
      intro y _
      exact gaussianChirpAtom_eq_cutoffIntegrand n s θ y k hn hs
    _ = (∫ y in K..n - K,
          (gaussianKernel s ((k : ℝ) - y) : ℂ)) * e (chirpPhase n θ k) := by
      rw [intervalIntegral.integral_mul_const]
    _ = _ := by
      rw [intervalIntegral.integral_ofReal]
      rfl

theorem finset_cutoffChirp_eq_integral
    (n s K θ : ℝ) (S : Finset ℤ) (hn : 0 < n) (hs : 0 < s) :
    (∑ k ∈ S, (gaussianCutoff s K n k : ℂ) * e (chirpPhase n θ k)) =
      ∫ y in K..n - K, ∑ k ∈ S, gaussianChirpAtom n s θ y k := by
  rw [intervalIntegral.integral_finsetSum (fun k _ =>
    (show Continuous (gaussianChirpAtom n s θ · k) by
      unfold gaussianChirpAtom
      fun_prop).intervalIntegrable (μ := volume) K (n - K))]
  apply Finset.sum_congr rfl
  intro k _
  exact (intervalIntegral_gaussianChirpAtom n s K θ k hn hs).symm

/-- The `h`-th raw theta-transform summand at the smoothing point `y`. -/
def thetaAliasAtom (n s θ y : ℝ) (h : ℤ) : ℂ :=
  ((s : ℂ)⁻¹ * Complex.exp (-π * y ^ 2 / s ^ 2) /
      thetaA n s ^ (1 / 2 : ℂ)) *
    Complex.exp
      (-π / thetaA n s * ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2)

/-- The full integer Gaussian-smoothed chirp, written before Poisson
summation as the integral of its absolutely convergent theta series. -/
def fullIntegerSmoothedChirp (n s K θ : ℝ) : ℂ :=
  ∫ y in K..n - K, ∑' k : ℤ, gaussianChirpAtom n s θ y k

/-- The pointwise Jacobi transformation of the smoothed chirp. -/
theorem tsum_gaussianChirpAtom_eq_tsum_thetaAliasAtom
    (n s θ y : ℝ) (hn : 0 < n) (hs : 0 < s) :
    (∑' k : ℤ, gaussianChirpAtom n s θ y k) =
      ∑' h : ℤ, thetaAliasAtom n s θ y h := by
  have ha : 0 < (thetaA n s).re := by
    have heq : (thetaA n s).re = 1 / s ^ 2 := by
      simp only [thetaA, Complex.div_re]
      simp only [pow_two, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      norm_num [Complex.normSq]
    rw [heq]
    positivity
  calc
    (∑' k : ℤ, gaussianChirpAtom n s θ y k) =
        ((s : ℂ)⁻¹ * Complex.exp (-π * y ^ 2 / s ^ 2)) *
          ∑' k : ℤ, Complex.exp
            (-π * thetaA n s * (k : ℂ) ^ 2 +
              2 * π * thetaB s θ y * k) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      simp only [gaussianChirpAtom, thetaA, thetaB]
      conv_rhs => rw [mul_assoc, ← Complex.exp_add]
      congr 1
      congr 1
      simp only [← Complex.ofReal_pow]
      field_simp [hs.ne', hn.ne']
      push_cast
      field_simp [hn.ne']
      ring
    _ = ((s : ℂ)⁻¹ * Complex.exp (-π * y ^ 2 / s ^ 2)) *
        (1 / thetaA n s ^ (1 / 2 : ℂ) *
          ∑' h : ℤ, Complex.exp
            (-π / thetaA n s *
              ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2)) := by
      rw [Complex.tsum_exp_neg_quadratic ha (thetaB s θ y)]
    _ = ∑' h : ℤ, thetaAliasAtom n s θ y h := by
      rw [← tsum_mul_left, ← tsum_mul_left]
      apply tsum_congr
      intro h
      simp only [thetaAliasAtom]
      ring

theorem thetaAlias_exponent_eq_alias_exponent
    (n s θ y : ℝ) (h : ℤ) (hn : 0 < n) (hs : 0 < s) :
    -π * y ^ 2 / s ^ 2 -
        π / thetaA n s * ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2 =
      -π * Complex.I * aliasCenter n θ h ^ 2 / n +
        π * Complex.I * (y - aliasCenter n θ h) ^ 2 /
          (n * (1 - Complex.I * (s ^ 2 / n))) := by
  have hden : (-(s : ℂ) ^ 2 * Complex.I + n) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    have : n = 0 := by simpa [pow_two] using hre
    exact hn.ne' this
  have hdenN : (n - (s : ℂ) ^ 2 * Complex.I) ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using hden
  have hdenUnit : (1 - Complex.I * ((s ^ 2 / n : ℝ) : ℂ)) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    norm_num [pow_two] at hre
  simp only [thetaA, thetaB, aliasCenter]
  simp only [← Complex.ofReal_pow]
  field_simp [hn.ne', hs.ne', hden, hdenN, hdenUnit]
  push_cast
  field_simp [hn.ne', hs.ne', hden, hdenN, hdenUnit]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    calc
      Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = -Complex.I := by rw [Complex.I_sq]; ring
  have hI4 : Complex.I ^ 4 = 1 := by
    calc
      Complex.I ^ 4 = Complex.I ^ 2 * Complex.I ^ 2 := by ring
      _ = 1 := by rw [Complex.I_sq]; ring
  have hI5 : Complex.I ^ 5 = Complex.I := by
    calc
      Complex.I ^ 5 = Complex.I ^ 4 * Complex.I := by ring
      _ = Complex.I := by rw [hI4]; ring
  ring_nf
  rw [hI3, hI4, hI5, Complex.I_sq]
  ring

theorem norm_one_sub_I_mul (r : ℝ) :
    ‖1 - Complex.I * r‖ = Real.sqrt (1 + r ^ 2) := by
  rw [Complex.norm_def]
  congr 1
  norm_num [Complex.normSq]
  ring

theorem norm_thetaA (n s : ℝ) (hn : 0 < n) (hs : 0 < s) :
    ‖thetaA n s‖ =
      Real.sqrt (1 + (s ^ 2 / n) ^ 2) / s ^ 2 := by
  rw [thetaA, norm_div, norm_one_sub_I_mul]
  rw [show ‖((s ^ 2 : ℝ) : ℂ)‖ = s ^ 2 by
    rw [Complex.norm_real, Real.norm_of_nonneg]
    positivity]

theorem thetaA_cpow_half (n s : ℝ) (hn : 0 < n) (hs : 0 < s) :
    thetaA n s ^ (1 / 2 : ℂ) =
      (s : ℂ)⁻¹ * (1 - Complex.I * (s ^ 2 / n)) ^ (1 / 2 : ℂ) := by
  let z : ℂ := 1 - Complex.I * ((s ^ 2 / n : ℝ) : ℂ)
  have hz : z ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [z, pow_two] at hre
  have hs2 : 0 < s⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hs)
  have hfac : thetaA n s = ((s⁻¹ ^ 2 : ℝ) : ℂ) * z := by
    simp only [thetaA, z]
    field_simp [hs.ne']
    push_cast
    field_simp [hs.ne']
  rw [hfac]
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hs2.ne') hz)]
  rw [Complex.log_ofReal_mul hs2 hz]
  rw [add_mul, Complex.exp_add]
  rw [← Complex.cpow_def_of_ne_zero hz]
  have hreal : (((s⁻¹ ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) = (s : ℂ)⁻¹ := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_cpow hs2.le]
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (inv_nonneg.mpr hs.le)]
    push_cast
    rfl
  have hlog : Complex.log ((s⁻¹ ^ 2 : ℝ) : ℂ) =
      (Real.log (s⁻¹ ^ 2) : ℝ) := by
    simpa using Complex.log_ofReal_mul hs2 (one_ne_zero : (1 : ℂ) ≠ 0)
  have hexp : Complex.exp
      ((Real.log (s⁻¹ ^ 2) : ℂ) * (1 / 2 : ℂ)) =
      (((s⁻¹ ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hs2.ne'), hlog]
  rw [hexp, hreal]
  congr 1
  simp only [z]
  push_cast
  rfl

theorem thetaAliasAtom_eq_aliasAtom
    (n s θ y : ℝ) (h : ℤ) (hn : 0 < n) (hs : 0 < s) :
    thetaAliasAtom n s θ y h = aliasAtom n (s ^ 2 / n) θ y h := by
  let z : ℂ := 1 - Complex.I * ((s ^ 2 / n : ℝ) : ℂ)
  have hz : z ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [z, pow_two] at hre
  have hzpow : z ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)]
    exact hz
  calc
    thetaAliasAtom n s θ y h =
        (Complex.exp (-π * y ^ 2 / s ^ 2) / z ^ (1 / 2 : ℂ)) *
          Complex.exp
            (-π / thetaA n s * ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2) := by
      rw [thetaAliasAtom, thetaA_cpow_half n s hn hs]
      simp only [z]
      field_simp [hs.ne', hzpow]
      push_cast
      congr 2 <;> ring
    _ = 1 / z ^ (1 / 2 : ℂ) * Complex.exp
        (-π * y ^ 2 / s ^ 2 -
          π / thetaA n s * ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2) := by
      rw [div_eq_mul_inv]
      calc
        Complex.exp (-π * y ^ 2 / s ^ 2) * (z ^ (1 / 2 : ℂ))⁻¹ *
            Complex.exp
              (-π / thetaA n s * ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2) =
            (z ^ (1 / 2 : ℂ))⁻¹ *
              (Complex.exp (-π * y ^ 2 / s ^ 2) *
                Complex.exp
                  (-π / thetaA n s *
                    ((h : ℂ) + Complex.I * thetaB s θ y) ^ 2)) := by ring
        _ = _ := by
          rw [← Complex.exp_add]
          ring
    _ = 1 / z ^ (1 / 2 : ℂ) * Complex.exp
        (-π * Complex.I * aliasCenter n θ h ^ 2 / n +
          π * Complex.I * (y - aliasCenter n θ h) ^ 2 /
            (n * (1 - Complex.I * (s ^ 2 / n)))) := by
      rw [thetaAlias_exponent_eq_alias_exponent n s θ y h hn hs]
    _ = aliasAtom n (s ^ 2 / n) θ y h := by
      rw [Complex.exp_add]
      have he : e (-(aliasCenter n θ h) ^ 2 / (2 * n)) =
          Complex.exp (-π * Complex.I * aliasCenter n θ h ^ 2 / n) := by
        simp only [e]
        congr 1
        push_cast
        field_simp [hn.ne']
      rw [aliasAtom, he]
      simp only [z]
      push_cast
      field_simp [hn.ne']

theorem gaussianExponent_re (n r A : ℝ) (hn : 0 < n) :
    (π * Complex.I * (A : ℂ) / (n * (1 - Complex.I * r))).re =
      -π * A * r / (n * (1 + r ^ 2)) := by
  rw [Complex.div_re]
  norm_num [Complex.normSq]
  field_simp

theorem norm_aliasIntegrand (n r θ y : ℝ) (h : ℤ)
    (hn : 0 < n) (hr : 0 < r) :
    ‖Complex.exp
      (π * Complex.I * (y - aliasCenter n θ h) ^ 2 /
        (n * (1 - Complex.I * r)))‖ =
      Real.exp
        (-π * (y - aliasCenter n θ h) ^ 2 /
          aliasWidthSq n r) := by
  have hcast :
      (((y : ℂ) - (aliasCenter n θ h : ℂ)) ^ 2) =
        (((y - aliasCenter n θ h) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  rw [Complex.norm_exp]
  rw [gaussianExponent_re n r _ hn]
  congr 1
  simp only [aliasWidthSq]
  field_simp

theorem intervalIntegral_aliasAtom (n r K θ : ℝ) (h : ℤ) :
    (∫ y in K..n - K, aliasAtom n r θ y h) = aliasTerm n r K θ h := by
  unfold aliasAtom aliasTerm aliasIntegral
  rw [intervalIntegral.integral_const_mul]

theorem norm_aliasIntegral_le (n r K θ : ℝ) (h : ℤ)
    (hn : 0 < n) (hr : 0 < r) (hK : K ≤ n - K) :
    ‖aliasIntegral n r K θ h‖ ≤
      ∫ y in K..n - K, aliasMajorant n r θ h y := by
  refine (intervalIntegral.norm_integral_le_integral_norm hK).trans_eq ?_
  apply intervalIntegral.integral_congr
  intro y _
  exact norm_aliasIntegrand n r θ y h hn hr

theorem integral_aliasMajorant_eq (n r K θ : ℝ) (h : ℤ) :
    (∫ y in K..n - K, aliasMajorant n r θ h y) =
      ∫ t in K - aliasCenter n θ h..n - K - aliasCenter n θ h,
        Real.exp (-π * t ^ 2 / aliasWidthSq n r) := by
  simpa only [aliasMajorant] using
    intervalIntegral.integral_comp_sub_right
      (fun t : ℝ => Real.exp (-π * t ^ 2 / aliasWidthSq n r))
      (aliasCenter n θ h)

theorem aliasWidthSq_pos (n r : ℝ) (hn : 0 < n) (hr : 0 < r) :
    0 < aliasWidthSq n r := by
  exact div_pos (mul_pos hn (by positivity)) hr

theorem integrable_majorantGaussian (n r : ℝ) (hn : 0 < n) (hr : 0 < r) :
    Integrable (majorantGaussian n r) := by
  have hb : 0 < π / aliasWidthSq n r :=
    div_pos Real.pi_pos (aliasWidthSq_pos n r hn hr)
  rw [show majorantGaussian n r =
      (fun x : ℝ => Real.exp (-(π / aliasWidthSq n r) * x ^ 2)) by
    funext x
    simp only [majorantGaussian]
    congr 1
    ring]
  exact integrable_exp_neg_mul_sq hb

theorem pairwise_disjoint_aliasInterval (n K θ : ℝ)
    (hn : 0 < n) (hK : 0 ≤ K) :
    Pairwise (fun h j : ℤ =>
      Disjoint (aliasInterval n K θ h) (aliasInterval n K θ j)) := by
  intro h j hne
  rcases lt_or_gt_of_ne hne with hhj | hjh
  · exact (Set.Ioc_disjoint_Ioc_of_le (a := K - aliasCenter n θ j)
      (b := n - K - aliasCenter n θ j)
      (c := K - aliasCenter n θ h)
      (d := n - K - aliasCenter n θ h) (by
        simp only [aliasCenter]
        have hcast : (h : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hhj
        nlinarith)).symm
  · apply Set.Ioc_disjoint_Ioc_of_le
    simp only [aliasInterval, aliasCenter]
    have hcast : (j : ℝ) + 1 ≤ (h : ℝ) := by exact_mod_cast hjh
    nlinarith

theorem tsum_integral_majorant_le_integral (n r K θ : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    (∑' h : ℤ,
      ∫ t in K - aliasCenter n θ h..n - K - aliasCenter n θ h,
        majorantGaussian n r t) ≤
      ∫ t : ℝ, majorantGaussian n r t := by
  have hle (h : ℤ) :
      K - aliasCenter n θ h ≤ n - K - aliasCenter n θ h := by
    linarith
  simp_rw [intervalIntegral.integral_of_le (hle _)]
  change (∑' h : ℤ, ∫ t in aliasInterval n K θ h,
    majorantGaussian n r t) ≤ _
  rw [← MeasureTheory.integral_iUnion
    (s := aliasInterval n K θ)
    (f := majorantGaussian n r)
    (fun _ => measurableSet_Ioc)
    (pairwise_disjoint_aliasInterval n K θ hn hK0)
    ((integrable_majorantGaussian n r hn hr).integrableOn)]
  exact MeasureTheory.setIntegral_le_integral
    (integrable_majorantGaussian n r hn hr)
    (ae_of_all _ fun _ => Real.exp_pos _ |>.le)

theorem integral_majorantGaussian (n r : ℝ) (hn : 0 < n) (hr : 0 < r) :
    (∫ t : ℝ, majorantGaussian n r t) = Real.sqrt (aliasWidthSq n r) := by
  have hw : aliasWidthSq n r ≠ 0 := ne_of_gt (aliasWidthSq_pos n r hn hr)
  rw [show majorantGaussian n r =
      (fun x : ℝ => Real.exp (-(π / aliasWidthSq n r) * x ^ 2)) by
    funext x
    simp only [majorantGaussian]
    congr 1
    ring]
  rw [integral_gaussian]
  congr 1
  field_simp

theorem norm_one_sub_I_mul_cpow_half (r : ℝ) :
    ‖(1 - Complex.I * r) ^ (1 / 2 : ℂ)‖ =
      (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  rw [Complex.norm_cpow_real, Complex.norm_def]
  simp only [Complex.normSq_apply]
  norm_num
  have hb : 0 ≤ 1 + r * r := by nlinarith [sq_nonneg r]
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hb]
  norm_num
  simp only [pow_two]

theorem norm_aliasAtom (n r θ y : ℝ) (h : ℤ)
    (hn : 0 < n) (hr : 0 < r) :
    ‖aliasAtom n r θ y h‖ =
      aliasMajorant n r θ h y / (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
  calc
    ‖aliasAtom n r θ y h‖ =
        1 / (1 + r ^ 2) ^ (1 / 4 : ℝ) *
          ‖Complex.exp
            (π * Complex.I * (y - aliasCenter n θ h) ^ 2 /
              (n * (1 - Complex.I * r)))‖ := by
      rw [aliasAtom, norm_mul, norm_div, norm_e,
        norm_one_sub_I_mul_cpow_half]
    _ = 1 / (1 + r ^ 2) ^ (1 / 4 : ℝ) *
        aliasMajorant n r θ h y := by
      rw [norm_aliasIntegrand n r θ y h hn hr]
      rfl
    _ = _ := by ring

theorem norm_aliasTerm_le (n r K θ : ℝ) (h : ℤ)
    (hn : 0 < n) (hr : 0 < r) (hK : K ≤ n - K) :
    ‖aliasTerm n r K θ h‖ ≤
      (∫ t in K - aliasCenter n θ h..n - K - aliasCenter n θ h,
        majorantGaussian n r t) /
        (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
  calc
    ‖aliasTerm n r K θ h‖ =
        ‖aliasIntegral n r K θ h‖ / (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
      rw [aliasTerm, norm_mul, norm_div, norm_e,
        norm_one_sub_I_mul_cpow_half]
      ring
    _ ≤ (∫ y in K..n - K, aliasMajorant n r θ h y) /
        (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
      exact div_le_div_of_nonneg_right
        (norm_aliasIntegral_le n r K θ h hn hr hK) (by positivity)
    _ = _ := by
      rw [integral_aliasMajorant_eq]
      rfl

theorem summable_interval_majorant (n r K θ : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    Summable (fun h : ℤ =>
      ∫ t in K - aliasCenter n θ h..n - K - aliasCenter n θ h,
        majorantGaussian n r t) := by
  have hle (h : ℤ) :
      K - aliasCenter n θ h ≤ n - K - aliasCenter n θ h := by
    linarith
  simp_rw [intervalIntegral.integral_of_le (hle _)]
  change Summable (fun h : ℤ =>
    ∫ t in aliasInterval n K θ h, majorantGaussian n r t)
  exact (MeasureTheory.hasSum_integral_iUnion
    (s := aliasInterval n K θ)
    (f := majorantGaussian n r)
    (fun _ => measurableSet_Ioc)
    (pairwise_disjoint_aliasInterval n K θ hn hK0)
    ((integrable_majorantGaussian n r hn hr).integrableOn)).summable

theorem summable_norm_aliasTerm (n r K θ : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    Summable (fun h : ℤ => ‖aliasTerm n r K θ h‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun h => norm_aliasTerm_le n r K θ h hn hr hK)
  exact (summable_interval_majorant n r K θ hn hr hK0 hK).div_const _

theorem tsum_norm_aliasTerm_le (n r K θ : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    (∑' h : ℤ, ‖aliasTerm n r K θ h‖) ≤
      Real.sqrt (aliasWidthSq n r) /
        (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
  calc
    (∑' h : ℤ, ‖aliasTerm n r K θ h‖) ≤
        ∑' h : ℤ,
          (∫ t in K - aliasCenter n θ h..n - K - aliasCenter n θ h,
            majorantGaussian n r t) /
              (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
      exact Summable.tsum_le_tsum
        (fun h => norm_aliasTerm_le n r K θ h hn hr hK)
        (summable_norm_aliasTerm n r K θ hn hr hK0 hK)
        ((summable_interval_majorant n r K θ hn hr hK0 hK).div_const _)
    _ = (∑' h : ℤ,
          ∫ t in K - aliasCenter n θ h..n - K - aliasCenter n θ h,
            majorantGaussian n r t) /
              (1 + r ^ 2) ^ (1 / 4 : ℝ) := tsum_div_const
    _ ≤ (∫ t : ℝ, majorantGaussian n r t) /
        (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
      exact div_le_div_of_nonneg_right
        (tsum_integral_majorant_le_integral n r K θ hn hr hK0 hK)
        (by positivity)
    _ = _ := by rw [integral_majorantGaussian n r hn hr]

theorem norm_aliasSum_le (n r K θ : ℝ)
    (hn : 0 < n) (hr : 0 < r) (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    ‖aliasSum n r K θ‖ ≤
      Real.sqrt (aliasWidthSq n r) /
        (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
  calc
    ‖aliasSum n r K θ‖ ≤ ∑' h : ℤ, ‖aliasTerm n r K θ h‖ := by
      exact norm_tsum_le_tsum_norm
        (summable_norm_aliasTerm n r K θ hn hr hK0 hK)
    _ ≤ _ := tsum_norm_aliasTerm_le n r K θ hn hr hK0 hK

theorem hasSum_aliasTerm_fullIntegerSmoothedChirp
    (n s K θ : ℝ) (hn : 0 < n) (hs : 0 < s)
    (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    HasSum (fun h : ℤ => aliasTerm n (s ^ 2 / n) K θ h)
      (fullIntegerSmoothedChirp n s K θ) := by
  let r : ℝ := s ^ 2 / n
  have hr : 0 < r := div_pos (sq_pos_of_pos hs) hn
  let D : ℝ := (1 + r ^ 2) ^ (1 / 4 : ℝ)
  have hFint (h : ℤ) :
      Integrable (aliasAtom n r θ · h)
        (volume.restrict (Set.Ioc K (n - K))) := by
    have hi := (show Continuous (aliasAtom n r θ · h) by
      unfold aliasAtom e aliasCenter
      fun_prop).intervalIntegrable (μ := volume) K (n - K)
    rw [intervalIntegrable_iff, uIoc_of_le hK] at hi
    exact hi
  have hmass : Summable (fun h : ℤ =>
      (∫ y in Set.Ioc K (n - K), ‖aliasAtom n r θ y h‖) ) := by
    have hbase := (summable_interval_majorant n r K θ hn hr hK0 hK).div_const D
    exact hbase.congr (fun h => by
      rw [← intervalIntegral.integral_of_le hK]
      rw [show (∫ y in K..n - K, ‖aliasAtom n r θ y h‖) =
          ∫ y in K..n - K, aliasMajorant n r θ h y / D by
        apply intervalIntegral.integral_congr
        intro y _
        exact norm_aliasAtom n r θ y h hn hr]
      rw [intervalIntegral.integral_div]
      rw [integral_aliasMajorant_eq]
      rfl)
  have hswap := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc K (n - K))) hFint hmass
  have hfull : fullIntegerSmoothedChirp n s K θ =
      ∫ y in Set.Ioc K (n - K), ∑' h : ℤ, aliasAtom n r θ y h := by
    unfold fullIntegerSmoothedChirp
    rw [intervalIntegral.integral_of_le hK]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro y _
    change (∑' k : ℤ, gaussianChirpAtom n s θ y k) =
      ∑' h : ℤ, aliasAtom n r θ y h
    rw [tsum_gaussianChirpAtom_eq_tsum_thetaAliasAtom n s θ y hn hs]
    apply tsum_congr
    intro h
    simpa only [r] using thetaAliasAtom_eq_aliasAtom n s θ y h hn hs
  rw [hfull]
  have hterm : (fun h : ℤ =>
      ∫ y in Set.Ioc K (n - K), aliasAtom n r θ y h) =
      (fun h : ℤ => aliasTerm n (s ^ 2 / n) K θ h) := by
    funext h
    rw [← intervalIntegral_aliasAtom n r K θ h]
    rw [intervalIntegral.integral_of_le hK]
  rw [← hterm]
  exact hswap

theorem fullIntegerSmoothedChirp_eq_aliasSum
    (n s K θ : ℝ) (hn : 0 < n) (hs : 0 < s)
    (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    fullIntegerSmoothedChirp n s K θ = aliasSum n (s ^ 2 / n) K θ := by
  exact (hasSum_aliasTerm_fullIntegerSmoothedChirp n s K θ hn hs hK0 hK).tsum_eq.symm

theorem norm_fullIntegerSmoothedChirp_le
    (n s K θ : ℝ) (hn : 0 < n) (hs : 0 < s)
    (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    ‖fullIntegerSmoothedChirp n s K θ‖ ≤
      Real.sqrt (aliasWidthSq n (s ^ 2 / n)) /
        (1 + (s ^ 2 / n) ^ 2) ^ (1 / 4 : ℝ) := by
  rw [fullIntegerSmoothedChirp_eq_aliasSum n s K θ hn hs hK0 hK]
  exact norm_aliasSum_le n (s ^ 2 / n) K θ hn
    (div_pos (sq_pos_of_pos hs) hn) hK0 hK

theorem aliasBound_eq (n r : ℝ) (hn : 0 < n) (hr : 0 < r) :
    Real.sqrt (aliasWidthSq n r) /
        (1 + r ^ 2) ^ (1 / 4 : ℝ) =
      Real.sqrt n * (1 + r⁻¹ ^ 2) ^ (1 / 4 : ℝ) := by
  have hB : 0 < 1 + r ^ 2 := by positivity
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [aliasWidthSq, Real.div_rpow (mul_nonneg hn.le hB.le) hr.le]
  rw [Real.mul_rpow hn.le hB.le]
  have hBpow : (1 + r ^ 2) ^ (1 / 2 : ℝ) /
      (1 + r ^ 2) ^ (1 / 4 : ℝ) = (1 + r ^ 2) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_sub hB]
    norm_num
  rw [show n ^ (1 / 2 : ℝ) * (1 + r ^ 2) ^ (1 / 2 : ℝ) /
      r ^ (1 / 2 : ℝ) / (1 + r ^ 2) ^ (1 / 4 : ℝ) =
      n ^ (1 / 2 : ℝ) / r ^ (1 / 2 : ℝ) *
        ((1 + r ^ 2) ^ (1 / 2 : ℝ) /
          (1 + r ^ 2) ^ (1 / 4 : ℝ)) by ring]
  rw [hBpow]
  rw [show 1 + r⁻¹ ^ 2 = (1 + r ^ 2) / r ^ 2 by
    field_simp [hr.ne']
    ring]
  rw [Real.div_rpow hB.le hr2.le]
  rw [show (r ^ 2) ^ (1 / 4 : ℝ) = r ^ (1 / 2 : ℝ) by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num]
  ring

theorem norm_fullIntegerSmoothedChirp_le_exact
    (n s K θ : ℝ) (hn : 0 < n) (hs : 0 < s)
    (hK0 : 0 ≤ K) (hK : K ≤ n - K) :
    ‖fullIntegerSmoothedChirp n s K θ‖ ≤
      Real.sqrt n * (1 + (s ^ 2 / n)⁻¹ ^ 2) ^ (1 / 4 : ℝ) := by
  rw [← aliasBound_eq n (s ^ 2 / n) hn
    (div_pos (sq_pos_of_pos hs) hn)]
  exact norm_fullIntegerSmoothedChirp_le n s K θ hn hs hK0 hK

theorem fullIntegerSmoothedChirp_eq_tsum_cutoffChirpTerm
    (s : ℝ) (K n : ℕ) (θ : ℝ) (hs : 0 < s) (hn0 : 0 < n)
    (hKn : 2 * K ≤ n) :
    fullIntegerSmoothedChirp n s K θ =
      ∑' k : ℤ, cutoffChirpTerm s K n θ k := by
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast hn0
  have hKle : K ≤ n := by omega
  have horder : (K : ℝ) ≤ (n : ℝ) - K := by
    rw [← Nat.cast_sub hKle]
    exact Erdos230.GaussianCutoff.cutoff_endpoints_order hKn
  have hFint (k : ℤ) :
      Integrable (gaussianChirpAtom n s θ · k)
        (volume.restrict (Set.Ioc K ((n : ℝ) - K))) := by
    have hi := (show Continuous (gaussianChirpAtom n s θ · k) by
      unfold gaussianChirpAtom
      fun_prop).intervalIntegrable (μ := volume) (K : ℝ) ((n : ℝ) - K)
    rw [intervalIntegrable_iff, uIoc_of_le horder] at hi
    exact hi
  have hmass : Summable (fun k : ℤ =>
      ∫ y in Set.Ioc (K : ℝ) ((n : ℝ) - K),
        ‖gaussianChirpAtom n s θ y k‖) := by
    exact (summable_chi_int s K n hs hKn).congr (fun k => by
      symm
      rw [← intervalIntegral.integral_of_le horder]
      calc
        (∫ y in (K : ℝ)..(n : ℝ) - K,
            ‖gaussianChirpAtom n s θ y k‖) =
            ∫ y in (K : ℝ)..(n : ℝ) - K,
              gaussianKernel s ((k : ℝ) - y) := by
          apply intervalIntegral.integral_congr
          intro y _
          exact norm_gaussianChirpAtom n s θ y k hn hs
        _ = gaussianCutoff s K n k := rfl
        _ = Erdos230.GaussianCutoff.chi s K n (k : ℝ) :=
          gaussianCutoff_eq_chi s K n k hs (by omega))
  have hswap := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (K : ℝ) ((n : ℝ) - K))) hFint hmass
  have hfull : fullIntegerSmoothedChirp n s K θ =
      ∫ y in Set.Ioc (K : ℝ) ((n : ℝ) - K),
        ∑' k : ℤ, gaussianChirpAtom n s θ y k := by
    unfold fullIntegerSmoothedChirp
    rw [intervalIntegral.integral_of_le horder]
  have hterm : (fun k : ℤ =>
      ∫ y in Set.Ioc (K : ℝ) ((n : ℝ) - K),
        gaussianChirpAtom n s θ y k) = cutoffChirpTerm s K n θ := by
    funext k
    rw [← intervalIntegral.integral_of_le horder]
    rw [intervalIntegral_gaussianChirpAtom n s K θ k hn hs]
    rw [gaussianCutoff_eq_chi s K n k hs (by omega)]
    rfl
  rw [hfull]
  rw [← hterm]
  exact hswap.tsum_eq.symm

theorem norm_finiteCutoffChirp_sub_full_le_outside
    (s : ℝ) (K n : ℕ) (θ : ℝ) (hs : 0 < s) (hn0 : 0 < n)
    (hKn : 2 * K ≤ n) :
    ‖finiteCutoffChirp s K n θ - fullIntegerSmoothedChirp n s K θ‖ ≤
      (∑' j : ℕ, Erdos230.GaussianCutoff.outsideLeft s K n j) +
        ∑' j : ℕ, Erdos230.GaussianCutoff.outsideRight s K n j := by
  let f : ℤ → ℂ := cutoffChirpTerm s K n θ
  let right : ℕ → ℂ := fun j => f (j + (n + 1) : ℕ)
  let left : ℕ → ℂ := fun j => f (-((j : ℤ) + 1))
  have hrightNorm : Summable (fun j : ℕ => ‖right j‖) := by
    exact (Erdos230.GaussianCutoff.summable_outsideRight hs hKn).congr (fun j => by
      symm
      simp only [right, f, norm_cutoffChirpTerm s K n θ _ hs hKn,
        Erdos230.GaussianCutoff.outsideRight]
      congr 2
      norm_cast
      omega)
  have hleftNorm : Summable (fun j : ℕ => ‖left j‖) := by
    exact (Erdos230.GaussianCutoff.summable_outsideLeft hs hKn).congr (fun j => by
      symm
      simp only [left, f, norm_cutoffChirpTerm s K n θ _ hs hKn,
        Erdos230.GaussianCutoff.outsideLeft]
      congr 2
      norm_cast)
  have hright : Summable right := Summable.of_norm hrightNorm
  have hleft : Summable left := Summable.of_norm hleftNorm
  have hnat : Summable (fun j : ℕ => f j) := by
    apply (summable_nat_add_iff (n + 1)).mp
    simpa only [right] using hright
  have hdecomp :
      (∑' k : ℤ, f k) = finiteCutoffChirp s K n θ +
          (∑' j : ℕ, right j) + ∑' j : ℕ, left j := by
    rw [tsum_of_nat_of_neg_add_one hnat hleft]
    rw [← hnat.sum_add_tsum_nat_add (n + 1)]
    simp only [finiteCutoffChirp, right, left, f]
  rw [fullIntegerSmoothedChirp_eq_tsum_cutoffChirpTerm s K n θ hs hn0 hKn]
  change ‖finiteCutoffChirp s K n θ - ∑' k : ℤ, f k‖ ≤ _
  rw [hdecomp]
  calc
    ‖finiteCutoffChirp s K n θ -
        (finiteCutoffChirp s K n θ + (∑' j : ℕ, right j) +
          ∑' j : ℕ, left j)‖ =
        ‖(∑' j : ℕ, right j) + ∑' j : ℕ, left j‖ := by
      rw [show finiteCutoffChirp s K n θ -
          (finiteCutoffChirp s K n θ + (∑' j : ℕ, right j) +
            ∑' j : ℕ, left j) =
          - ((∑' j : ℕ, right j) + ∑' j : ℕ, left j) by ring,
        norm_neg]
    _ ≤ ‖∑' j : ℕ, right j‖ + ‖∑' j : ℕ, left j‖ := norm_add_le _ _
    _ ≤ (∑' j : ℕ, ‖right j‖) + ∑' j : ℕ, ‖left j‖ := by
      exact add_le_add (norm_tsum_le_tsum_norm hrightNorm)
        (norm_tsum_le_tsum_norm hleftNorm)
    _ = (∑' j : ℕ, Erdos230.GaussianCutoff.outsideRight s K n j) +
        ∑' j : ℕ, Erdos230.GaussianCutoff.outsideLeft s K n j := by
      congr 1
      · apply tsum_congr
        intro j
        simp only [right, f, norm_cutoffChirpTerm s K n θ _ hs hKn,
          Erdos230.GaussianCutoff.outsideRight]
        congr 2
        norm_cast
        omega
      · apply tsum_congr
        intro j
        simp only [left, f, norm_cutoffChirpTerm s K n θ _ hs hKn,
          Erdos230.GaussianCutoff.outsideLeft]
        congr 2
        norm_cast
    _ = _ := by ring

end GaussianPoisson

end
end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos230/Correction.lean` -/

section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Real

noncomputable section

namespace Correction

def unitDir (a : ℂ) : ℂ := if a = 0 then 1 else (‖a‖ : ℂ)⁻¹ * a

lemma norm_unitDir (a : ℂ) : ‖unitDir a‖ = 1 := by
  simp only [unitDir]
  split_ifs with h
  · simp
  · rw [norm_mul, norm_inv, Complex.norm_real]
    simp [h]

lemma norm_smul_unitDir (a : ℂ) : (‖a‖ : ℂ) * unitDir a = a := by
  simp only [unitDir]
  split_ifs with h
  · simp [h]
  · have hn : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h)
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

def chord (a : ℂ) (sgn : ℝ) : ℂ :=
  ((‖a‖ : ℂ) + sgn * (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ) * Complex.I) * unitDir a

lemma chord_add (a : ℂ) : (chord a 1 + chord a (-1)) / 2 = a := by
  rw [chord, chord, ← add_mul]
  push_cast
  ring_nf
  exact norm_smul_unitDir a

def chordCorrection (a : ℂ) : ℂ :=
  (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ) * Complex.I * unitDir a

lemma chord_eq_add_correction (a : ℂ) (sgn : ℝ) :
    chord a sgn = a + (sgn : ℂ) * chordCorrection a := by
  rw [chord, chordCorrection, add_mul]
  rw [norm_smul_unitDir]
  congr 1
  ring

lemma norm_chordCorrection_le_one (a : ℂ) (ha : ‖a‖ ≤ 1) :
    ‖chordCorrection a‖ ≤ 1 := by
  rw [chordCorrection, norm_mul, norm_mul, norm_unitDir, mul_one, Complex.norm_I,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_one]
  have hsquare : (Real.sqrt (1 - ‖a‖ ^ 2)) ^ 2 = 1 - ‖a‖ ^ 2 := by
    rw [sq_sqrt]
    nlinarith [norm_nonneg a]
  nlinarith [Real.sqrt_nonneg (1 - ‖a‖ ^ 2), norm_nonneg a]

lemma norm_chordCorrection_sq (a : ℂ) (ha : ‖a‖ ≤ 1) :
    ‖chordCorrection a‖ ^ 2 = 1 - ‖a‖ ^ 2 := by
  rw [chordCorrection, norm_mul, norm_mul, norm_unitDir, mul_one, Complex.norm_I,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_one]
  rw [sq_sqrt]
  nlinarith [norm_nonneg a]

/-- The total squared radial defect of coefficients in the closed unit disk. -/
def defect {ι : Type*} [Fintype ι] (a : ι → ℂ) : ℝ :=
  ∑ i, (1 - ‖a i‖ ^ 2)

lemma coe_sum_nnnorm_chordCorrection_sq {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) :
    ((↑(∑ i, ‖chordCorrection (a i)‖₊ ^ 2) : ℝ≥0) : ℝ) =
      defect a := by
  rw [defect]
  push_cast
  exact Finset.sum_congr rfl fun i _ ↦ norm_chordCorrection_sq (a i) (ha i)

lemma defect_term_nonneg {a : ℂ} (ha : ‖a‖ ≤ 1) : 0 ≤ 1 - ‖a‖ ^ 2 := by
  nlinarith [norm_nonneg a]

lemma norm_eq_one_of_defect_eq_zero {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (hzero : defect a = 0) (i : ι) :
    ‖a i‖ = 1 := by
  rw [defect] at hzero
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_hj : j ∈ Finset.univ) ↦ defect_term_nonneg (ha j))).mp hzero i (Finset.mem_univ i)
  nlinarith [norm_nonneg (a i)]

lemma norm_chord (a : ℂ) (ha : ‖a‖ ≤ 1) (sgn : ℝ) (hsgn : sgn ^ 2 = 1) :
    ‖chord a sgn‖ = 1 := by
  rw [chord, norm_mul, norm_unitDir, mul_one]
  rw [Complex.norm_def]
  have hsqrt : (Real.sqrt (1 - ‖a‖ ^ 2)) ^ 2 = 1 - ‖a‖ ^ 2 := by
    rw [sq_sqrt]
    nlinarith [norm_nonneg a]
  have hsq : Complex.normSq
      ((‖a‖ : ℂ) + sgn * (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ) * Complex.I) = 1 := by
    rw [show sgn * (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ) =
      ((sgn * Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ) by norm_num]
    rw [Complex.normSq_add_mul_I]
    nlinarith
  rw [hsq, Real.sqrt_one]

abbrev coinPMF : PMF Bool := PMF.uniformOfFintype Bool

abbrev coinMeasure : Measure Bool := coinPMF.toMeasure

def sign (b : Bool) : ℝ := if b then 1 else -1

lemma integral_sign : ∫ b, sign b ∂coinMeasure = 0 := by
  change ∫ b, sign b ∂coinPMF.toMeasure = 0
  rw [PMF.integral_eq_sum]
  simp [sign, PMF.uniformOfFintype_apply]

lemma sign_mem_Icc : ∀ b, sign b ∈ Set.Icc (-1 : ℝ) 1 := by
  intro b
  cases b <;> simp [sign]

lemma hasSubgaussianMGF_sign : HasSubgaussianMGF sign 1 coinMeasure := by
  convert
    (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (X := sign) (a := (-1 : ℝ)) (b := 1) (by fun_prop)
      (ae_of_all _ sign_mem_Icc) integral_sign) using 1
  norm_num [NNReal.eq]

lemma subgaussian_mono {X : Ω → ℝ} [MeasurableSpace Ω] {c d : ℝ≥0} {P : Measure Ω}
    (h : HasSubgaussianMGF X c P) (hcd : c ≤ d) : HasSubgaussianMGF X d P where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := h.mgf_le t |>.trans <| by
    rw [Real.exp_le_exp]
    gcongr

lemma hasSubgaussianMGF_sign_mul (r : ℝ) (hr : |r| ≤ 1) :
    HasSubgaussianMGF (fun b ↦ r * sign b) 1 coinMeasure := by
  apply subgaussian_mono (hasSubgaussianMGF_sign.const_mul r)
  apply NNReal.coe_le_coe.mp
  change r ^ 2 * 1 ≤ (1 : ℝ)
  rcases abs_le.mp hr with ⟨hrl, hrr⟩
  nlinarith

def sqNNReal (r : ℝ) : ℝ≥0 := ⟨r ^ 2, sq_nonneg r⟩

lemma hasSubgaussianMGF_sign_mul_sq (r : ℝ) :
    HasSubgaussianMGF (fun b ↦ r * sign b) (sqNNReal r) coinMeasure := by
  convert hasSubgaussianMGF_sign.const_mul r using 1
  apply NNReal.eq
  change r ^ 2 = r ^ 2 * 1
  ring

abbrev coinProduct (ι : Type*) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi (fun _ ↦ coinMeasure)

lemma coordinate_subgaussian {ι : Type*} [Fintype ι] (i : ι) (r : ℝ) (hr : |r| ≤ 1) :
    HasSubgaussianMGF (fun ω : ι → Bool ↦ r * sign (ω i)) 1 (coinProduct ι) := by
  have hm := (measurePreserving_eval (fun _ : ι ↦ coinMeasure) i).map_eq
  change HasSubgaussianMGF
    ((fun b ↦ r * sign b) ∘ (fun ω : ι → Bool ↦ ω i)) 1 (coinProduct ι)
  apply HasSubgaussianMGF.of_map (Y := fun ω : ι → Bool ↦ ω i)
    (measurable_pi_apply i).aemeasurable
  change HasSubgaussianMGF (fun b ↦ r * sign b) 1
    (Measure.map (fun ω : ι → Bool ↦ ω i)
      (Measure.pi (fun _ : ι ↦ coinMeasure)))
  rw [hm]
  exact hasSubgaussianMGF_sign_mul r hr

lemma coordinate_subgaussian_weighted {ι : Type*} [Fintype ι]
    (i : ι) (r : ℝ) (v : ℝ≥0) (hrv : sqNNReal r ≤ v) :
    HasSubgaussianMGF (fun ω : ι → Bool ↦ r * sign (ω i)) v (coinProduct ι) := by
  have hm := (measurePreserving_eval (fun _ : ι ↦ coinMeasure) i).map_eq
  change HasSubgaussianMGF
    ((fun b ↦ r * sign b) ∘ (fun ω : ι → Bool ↦ ω i)) v (coinProduct ι)
  apply HasSubgaussianMGF.of_map (Y := fun ω : ι → Bool ↦ ω i)
    (measurable_pi_apply i).aemeasurable
  change HasSubgaussianMGF (fun b ↦ r * sign b) v
    (Measure.map (fun ω : ι → Bool ↦ ω i)
      (Measure.pi (fun _ : ι ↦ coinMeasure)))
  rw [hm]
  exact subgaussian_mono (hasSubgaussianMGF_sign_mul_sq r) hrv

lemma coordinate_iIndep {ι : Type*} [Fintype ι] (r : ι → ℝ) :
    iIndepFun (fun i (ω : ι → Bool) ↦ r i * sign (ω i)) (coinProduct ι) := by
  exact iIndepFun_pi (X := fun i b ↦ r i * sign b)
    (μ := fun _ ↦ coinMeasure) (fun _ ↦ by fun_prop)

lemma real_rademacher_tail {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (hr : ∀ i, |r i| ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real
        {ω | t ≤ ∑ i, r i * sign (ω i)} ≤
      Real.exp (-t ^ 2 / (2 * Fintype.card ι)) := by
  simpa using
    (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (X := fun i (ω : ι → Bool) ↦ r i * sign (ω i))
      (c := fun _ ↦ 1) (s := Finset.univ) (coordinate_iIndep r)
      (fun i _ ↦ coordinate_subgaussian i (r i) (hr i)) ht)

lemma real_rademacher_tail_weighted {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (v : ι → ℝ≥0) (hrv : ∀ i, sqNNReal (r i) ≤ v i) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real
        {ω | t ≤ ∑ i, r i * sign (ω i)} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i, v i)) := by
  simpa using
    (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (X := fun i (ω : ι → Bool) ↦ r i * sign (ω i))
      (c := v) (s := Finset.univ) (coordinate_iIndep r)
      (fun i _ ↦ coordinate_subgaussian_weighted i (r i) (v i) (hrv i)) ht)

def rademacherSum {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (g : κ) (ω : ι → Bool) : ℂ :=
  ∑ i, (sign (ω i) : ℂ) * C i g

lemma rademacher_re_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (hC : ∀ i g, ‖C i g‖ ≤ 1) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ (rademacherSum C g ω).re} ≤
      Real.exp (-t ^ 2 / (2 * Fintype.card ι)) := by
  convert real_rademacher_tail (fun i ↦ (C i g).re) (fun i ↦
    (Complex.abs_re_le_norm (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma rademacher_neg_re_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (hC : ∀ i g, ‖C i g‖ ≤ 1) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ -(rademacherSum C g ω).re} ≤
      Real.exp (-t ^ 2 / (2 * Fintype.card ι)) := by
  convert real_rademacher_tail (fun i ↦ -(C i g).re) (fun i ↦ by
    rw [abs_neg]
    exact (Complex.abs_re_le_norm (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma rademacher_im_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (hC : ∀ i g, ‖C i g‖ ≤ 1) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ (rademacherSum C g ω).im} ≤
      Real.exp (-t ^ 2 / (2 * Fintype.card ι)) := by
  convert real_rademacher_tail (fun i ↦ (C i g).im) (fun i ↦
    (Complex.abs_im_le_norm (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma rademacher_neg_im_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (hC : ∀ i g, ‖C i g‖ ≤ 1) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ -(rademacherSum C g ω).im} ≤
      Real.exp (-t ^ 2 / (2 * Fintype.card ι)) := by
  convert real_rademacher_tail (fun i ↦ -(C i g).im) (fun i ↦ by
    rw [abs_neg]
    exact (Complex.abs_im_le_norm (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma sqNNReal_re_le_nnnorm_sq (z : ℂ) : sqNNReal z.re ≤ ‖z‖₊ ^ 2 := by
  apply NNReal.coe_le_coe.mp
  change z.re ^ 2 ≤ ‖z‖ ^ 2
  exact sq_le_sq.mpr (by simpa using Complex.abs_re_le_norm z)

lemma sqNNReal_im_le_nnnorm_sq (z : ℂ) : sqNNReal z.im ≤ ‖z‖₊ ^ 2 := by
  apply NNReal.coe_le_coe.mp
  change z.im ^ 2 ≤ ‖z‖ ^ 2
  exact sq_le_sq.mpr (by simpa using Complex.abs_im_le_norm z)

lemma weighted_re_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (v : ι → ℝ≥0) (hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ (rademacherSum C g ω).re} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i, v i)) := by
  convert real_rademacher_tail_weighted (fun i ↦ (C i g).re) v
    (fun i ↦ (sqNNReal_re_le_nnnorm_sq (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma weighted_neg_re_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (v : ι → ℝ≥0) (hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ -(rademacherSum C g ω).re} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i, v i)) := by
  convert real_rademacher_tail_weighted (fun i ↦ -(C i g).re) v (fun i ↦ by
    simpa [sqNNReal] using (sqNNReal_re_le_nnnorm_sq (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma weighted_im_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (v : ι → ℝ≥0) (hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ (rademacherSum C g ω).im} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i, v i)) := by
  convert real_rademacher_tail_weighted (fun i ↦ (C i g).im) v
    (fun i ↦ (sqNNReal_im_le_nnnorm_sq (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma weighted_neg_im_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (v : ι → ℝ≥0) (hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i) (g : κ) {t : ℝ} (ht : 0 ≤ t) :
    (coinProduct ι).real {ω | t ≤ -(rademacherSum C g ω).im} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i, v i)) := by
  convert real_rademacher_tail_weighted (fun i ↦ -(C i g).im) v (fun i ↦ by
    simpa [sqNNReal] using (sqNNReal_im_le_nnnorm_sq (C i g)).trans (hC i g)) ht using 1
  congr 1
  ext ω
  simp [rademacherSum, mul_comm]

lemma complex_rademacher_tail_weighted {ι κ : Type*} [Fintype ι]
    (C : ι → κ → ℂ) (v : ι → ℝ≥0) (hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i)
    (g : κ) {R : ℝ} (hR : 0 < R) :
    (coinProduct ι).real {ω | R ≤ ‖rademacherSum C g ω‖} ≤
      4 * Real.exp (-R ^ 2 / (8 * ∑ i, v i)) := by
  let A : Set (ι → Bool) := {ω | R / 2 ≤ (rademacherSum C g ω).re}
  let B : Set (ι → Bool) := {ω | R / 2 ≤ -(rademacherSum C g ω).re}
  let D : Set (ι → Bool) := {ω | R / 2 ≤ (rademacherSum C g ω).im}
  let E : Set (ι → Bool) := {ω | R / 2 ≤ -(rademacherSum C g ω).im}
  have hsub : {ω | R ≤ ‖rademacherSum C g ω‖} ⊆ A ∪ B ∪ D ∪ E := by
    intro ω hnorm
    change R ≤ ‖rademacherSum C g ω‖ at hnorm
    by_contra hmem
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, A, B, D, E, not_le] at hmem
    rcases hmem with ⟨⟨⟨hre, hnre⟩, him⟩, hnim⟩
    have hsq := Complex.sq_norm (rademacherSum C g ω)
    rw [Complex.normSq_apply] at hsq
    have hn := norm_nonneg (rademacherSum C g ω)
    have hre_sq : (rademacherSum C g ω).re ^ 2 < (R / 2) ^ 2 := by nlinarith
    have him_sq : (rademacherSum C g ω).im ^ 2 < (R / 2) ^ 2 := by nlinarith
    have hnorm_sq : R ^ 2 ≤ ‖rademacherSum C g ω‖ ^ 2 := by nlinarith
    nlinarith
  calc
    (coinProduct ι).real {ω | R ≤ ‖rademacherSum C g ω‖}
        ≤ (coinProduct ι).real (A ∪ B ∪ D ∪ E) := measureReal_mono hsub
    _ ≤ (coinProduct ι).real A + (coinProduct ι).real B +
        (coinProduct ι).real D + (coinProduct ι).real E := by
      calc
        _ ≤ (coinProduct ι).real (A ∪ B ∪ D) + (coinProduct ι).real E :=
          measureReal_union_le (A ∪ B ∪ D) E
        _ ≤ ((coinProduct ι).real (A ∪ B) + (coinProduct ι).real D) +
            (coinProduct ι).real E := by gcongr; exact measureReal_union_le (A ∪ B) D
        _ ≤ ((coinProduct ι).real A + (coinProduct ι).real B) +
            (coinProduct ι).real D + (coinProduct ι).real E := by gcongr; exact measureReal_union_le A B
    _ ≤ 4 * Real.exp (-(R / 2) ^ 2 / (2 * ∑ i, v i)) := by
      have hA := weighted_re_tail C v hC g (le_of_lt (half_pos hR))
      have hB := weighted_neg_re_tail C v hC g (le_of_lt (half_pos hR))
      have hD := weighted_im_tail C v hC g (le_of_lt (half_pos hR))
      have hE := weighted_neg_im_tail C v hC g (le_of_lt (half_pos hR))
      linarith
    _ = 4 * Real.exp (-R ^ 2 / (8 * ∑ i, v i)) := by congr 2; ring

lemma complex_rademacher_tail {ι κ : Type*} [Fintype ι] (C : ι → κ → ℂ)
    (hC : ∀ i g, ‖C i g‖ ≤ 1) (g : κ) {R : ℝ} (hR : 0 < R) :
    (coinProduct ι).real {ω | R ≤ ‖rademacherSum C g ω‖} ≤
      4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι)) := by
  let A : Set (ι → Bool) := {ω | R / 2 ≤ (rademacherSum C g ω).re}
  let B : Set (ι → Bool) := {ω | R / 2 ≤ -(rademacherSum C g ω).re}
  let D : Set (ι → Bool) := {ω | R / 2 ≤ (rademacherSum C g ω).im}
  let E : Set (ι → Bool) := {ω | R / 2 ≤ -(rademacherSum C g ω).im}
  have hsub : {ω | R ≤ ‖rademacherSum C g ω‖} ⊆ A ∪ B ∪ D ∪ E := by
    intro ω hnorm
    change R ≤ ‖rademacherSum C g ω‖ at hnorm
    by_contra hmem
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, A, B, D, E, not_le] at hmem
    rcases hmem with ⟨⟨⟨hre, hnre⟩, him⟩, hnim⟩
    have hsq := Complex.sq_norm (rademacherSum C g ω)
    rw [Complex.normSq_apply] at hsq
    have hn := norm_nonneg (rademacherSum C g ω)
    have hre_sq : (rademacherSum C g ω).re ^ 2 < (R / 2) ^ 2 := by nlinarith
    have him_sq : (rademacherSum C g ω).im ^ 2 < (R / 2) ^ 2 := by nlinarith
    have hnorm_sq : R ^ 2 ≤ ‖rademacherSum C g ω‖ ^ 2 := by nlinarith
    nlinarith
  have hA : (coinProduct ι).real A ≤
      Real.exp (-(R / 2) ^ 2 / (2 * Fintype.card ι)) := by
    exact rademacher_re_tail C hC g (le_of_lt (half_pos hR))
  have hB : (coinProduct ι).real B ≤
      Real.exp (-(R / 2) ^ 2 / (2 * Fintype.card ι)) := by
    exact rademacher_neg_re_tail C hC g (le_of_lt (half_pos hR))
  have hD : (coinProduct ι).real D ≤
      Real.exp (-(R / 2) ^ 2 / (2 * Fintype.card ι)) := by
    exact rademacher_im_tail C hC g (le_of_lt (half_pos hR))
  have hE : (coinProduct ι).real E ≤
      Real.exp (-(R / 2) ^ 2 / (2 * Fintype.card ι)) := by
    exact rademacher_neg_im_tail C hC g (le_of_lt (half_pos hR))
  calc
    (coinProduct ι).real {ω | R ≤ ‖rademacherSum C g ω‖}
        ≤ (coinProduct ι).real (A ∪ B ∪ D ∪ E) := measureReal_mono hsub
    _ ≤ (coinProduct ι).real A + (coinProduct ι).real B +
        (coinProduct ι).real D + (coinProduct ι).real E := by
      calc
        _ ≤ (coinProduct ι).real (A ∪ B ∪ D) + (coinProduct ι).real E :=
          measureReal_union_le (A ∪ B ∪ D) E
        _ ≤ ((coinProduct ι).real (A ∪ B) + (coinProduct ι).real D) +
            (coinProduct ι).real E := by
          gcongr
          exact measureReal_union_le (A ∪ B) D
        _ ≤ ((coinProduct ι).real A + (coinProduct ι).real B) +
            (coinProduct ι).real D + (coinProduct ι).real E := by
          gcongr
          exact measureReal_union_le A B
    _ ≤ 4 * Real.exp (-(R / 2) ^ 2 / (2 * Fintype.card ι)) := by linarith
    _ = 4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι)) := by
      congr 2
      ring

lemma exists_rademacher_grid {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : ι → κ → ℂ) (hC : ∀ i g, ‖C i g‖ ≤ 1) {R : ℝ} (hR : 0 < R)
    (hsmall : Fintype.card κ *
      (4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι))) < 1) :
    ∃ ω : ι → Bool, ∀ g, ‖rademacherSum C g ω‖ < R := by
  let Bad : κ → Set (ι → Bool) := fun g ↦ {ω | R ≤ ‖rademacherSum C g ω‖}
  let U : Set (ι → Bool) := ⋃ g, Bad g
  have hU : (coinProduct ι).real U ≤ Fintype.card κ *
      (4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι))) := by
    calc
      (coinProduct ι).real U ≤ ∑ g, (coinProduct ι).real (Bad g) := by
        exact measureReal_iUnion_fintype_le Bad
      _ ≤ ∑ _g : κ, (4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι))) := by
        exact Finset.sum_le_sum fun g _ ↦ complex_rademacher_tail C hC g hR
      _ = Fintype.card κ *
          (4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι))) := by simp
  have hU_lt : (coinProduct ι).real U < 1 := hU.trans_lt hsmall
  have hex : ∃ ω : ι → Bool, ω ∉ U := by
    by_contra! hall
    have h_univ : U = Set.univ := Set.eq_univ_of_forall hall
    rw [h_univ, probReal_univ] at hU_lt
    exact (lt_irrefl 1) hU_lt
  obtain ⟨ω, hω⟩ := hex
  refine ⟨ω, fun g ↦ lt_of_not_ge ?_⟩
  intro hg
  apply hω
  exact Set.mem_iUnion.2 ⟨g, hg⟩

lemma exists_rademacher_grid_weighted {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : ι → κ → ℂ) (v : ι → ℝ≥0) (hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i)
    {R : ℝ} (hR : 0 < R)
    (hsmall : Fintype.card κ *
      (4 * Real.exp (-R ^ 2 / (8 * ∑ i, v i))) < 1) :
    ∃ ω : ι → Bool, ∀ g, ‖rademacherSum C g ω‖ < R := by
  let Bad : κ → Set (ι → Bool) := fun g ↦ {ω | R ≤ ‖rademacherSum C g ω‖}
  let U : Set (ι → Bool) := ⋃ g, Bad g
  have hU : (coinProduct ι).real U ≤ Fintype.card κ *
      (4 * Real.exp (-R ^ 2 / (8 * ∑ i, v i))) := by
    calc
      (coinProduct ι).real U ≤ ∑ g, (coinProduct ι).real (Bad g) :=
        measureReal_iUnion_fintype_le Bad
      _ ≤ ∑ _g : κ, (4 * Real.exp (-R ^ 2 / (8 * ∑ i, v i))) := by
        exact Finset.sum_le_sum fun g _ ↦ complex_rademacher_tail_weighted C v hC g hR
      _ = Fintype.card κ * (4 * Real.exp (-R ^ 2 / (8 * ∑ i, v i))) := by simp
  have hU_lt : (coinProduct ι).real U < 1 := hU.trans_lt hsmall
  have hex : ∃ ω : ι → Bool, ω ∉ U := by
    by_contra! hall
    have h_univ : U = Set.univ := Set.eq_univ_of_forall hall
    rw [h_univ, probReal_univ] at hU_lt
    exact (lt_irrefl 1) hU_lt
  obtain ⟨ω, hω⟩ := hex
  refine ⟨ω, fun g ↦ lt_of_not_ge ?_⟩
  intro hg
  apply hω
  exact Set.mem_iUnion.2 ⟨g, hg⟩

lemma exists_unit_rounding_grid {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (phase : ι → κ → ℂ)
    (hphase : ∀ i g, ‖phase i g‖ ≤ 1) {R : ℝ} (hR : 0 < R)
    (hsmall : Fintype.card κ *
      (4 * Real.exp (-R ^ 2 / (8 * Fintype.card ι))) < 1) :
    ∃ b : ι → ℂ, (∀ i, ‖b i‖ = 1) ∧
      ∀ g, ‖∑ i, (b i - a i) * phase i g‖ < R := by
  let C : ι → κ → ℂ := fun i g ↦ chordCorrection (a i) * phase i g
  have hC : ∀ i g, ‖C i g‖ ≤ 1 := by
    intro i g
    dsimp [C]
    rw [norm_mul]
    exact mul_le_one₀ (norm_chordCorrection_le_one (a i) (ha i))
      (norm_nonneg _) (hphase i g)
  obtain ⟨ω, hω⟩ := exists_rademacher_grid C hC hR hsmall
  let b : ι → ℂ := fun i ↦ chord (a i) (sign (ω i))
  refine ⟨b, ?_, ?_⟩
  · intro i
    apply norm_chord (a i) (ha i) (sign (ω i))
    cases ω i <;> norm_num [sign]
  · intro g
    have heq : (∑ i, (b i - a i) * phase i g) = rademacherSum C g ω := by
      rw [rademacherSum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [b, C]
      rw [chord_eq_add_correction]
      simp only [add_sub_cancel_left]
      ring
    rw [heq]
    exact hω g

lemma exists_unit_rounding_grid_weighted {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (phase : ι → κ → ℂ)
    (hphase : ∀ i g, ‖phase i g‖ ≤ 1) {R : ℝ} (hR : 0 < R)
    (hsmall : Fintype.card κ * (4 * Real.exp
      (-R ^ 2 / (8 * ∑ i, ‖chordCorrection (a i)‖₊ ^ 2))) < 1) :
    ∃ b : ι → ℂ, (∀ i, ‖b i‖ = 1) ∧
      ∀ g, ‖∑ i, (b i - a i) * phase i g‖ < R := by
  let C : ι → κ → ℂ := fun i g ↦ chordCorrection (a i) * phase i g
  let v : ι → ℝ≥0 := fun i ↦ ‖chordCorrection (a i)‖₊ ^ 2
  have hC : ∀ i g, ‖C i g‖₊ ^ 2 ≤ v i := by
    intro i g
    apply NNReal.coe_le_coe.mp
    change ‖chordCorrection (a i) * phase i g‖ ^ 2 ≤ ‖chordCorrection (a i)‖ ^ 2
    rw [norm_mul, mul_pow]
    have hp0 := norm_nonneg (phase i g)
    have hp1 := hphase i g
    have hp2 : ‖phase i g‖ ^ 2 ≤ 1 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left hp2 (sq_nonneg ‖chordCorrection (a i)‖)
  obtain ⟨ω, hω⟩ := exists_rademacher_grid_weighted C v hC hR (by simpa [v] using hsmall)
  let b : ι → ℂ := fun i ↦ chord (a i) (sign (ω i))
  refine ⟨b, ?_, ?_⟩
  · intro i
    apply norm_chord (a i) (ha i) (sign (ω i))
    cases ω i <;> norm_num [sign]
  · intro g
    rw [show (∑ i, (b i - a i) * phase i g) = rademacherSum C g ω by
      rw [rademacherSum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [b, C]
      rw [chord_eq_add_correction]
      simp only [add_sub_cancel_left]
      ring]
    exact hω g

/-- The weighted rounding theorem with its variance parameter written as the exact coefficient
defect `∑ i, (1 - ‖a i‖²)`. -/
lemma exists_unit_rounding_grid_defect {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (phase : ι → κ → ℂ)
    (hphase : ∀ i g, ‖phase i g‖ ≤ 1) {R : ℝ} (hR : 0 < R)
    (hsmall : Fintype.card κ *
      (4 * Real.exp (-R ^ 2 / (8 * defect a))) < 1) :
    ∃ b : ι → ℂ, (∀ i, ‖b i‖ = 1) ∧
      ∀ g, ‖∑ i, (b i - a i) * phase i g‖ < R := by
  apply exists_unit_rounding_grid_weighted a ha phase hphase hR
  rw [coe_sum_nnnorm_chordCorrection_sq a ha]
  exact hsmall

/-- If the exact defect vanishes, no random correction is needed: all input coefficients already
have norm one. -/
lemma exists_unit_rounding_grid_of_defect_eq_zero {ι κ : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (phase : ι → κ → ℂ)
    (hzero : defect a = 0) :
    ∃ b : ι → ℂ, (∀ i, ‖b i‖ = 1) ∧
      ∀ g, ‖∑ i, (b i - a i) * phase i g‖ = 0 := by
  refine ⟨a, fun i ↦ norm_eq_one_of_defect_eq_zero a ha hzero i, ?_⟩
  intro g
  simp

end Correction

end
end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos230/Grid.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Finite circle grids for Erdős Problem 230

The random coefficient correction is first controlled on a finite grid.
These elementary estimates pass from that grid to the whole circle without
using Bernstein's inequality.
-/



noncomputable section

theorem norm_unitPoint_sub_le (theta phi : ℝ) :
    ‖unitPoint theta - unitPoint phi‖ ≤ |theta - phi| := by
  have hfactor : unitPoint theta - unitPoint phi =
      unitPoint phi * (unitPoint (theta - phi) - 1) := by
    rw [unitPoint, unitPoint, unitPoint]
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hfactor, norm_mul, norm_unitPoint, one_mul, unitPoint]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := theta - phi)
  simpa [mul_comm, Real.norm_eq_abs] using h

theorem norm_periodicPoint_sub_le (theta phi : ℝ) :
    ‖periodicPoint theta - periodicPoint phi‖ ≤
      2 * Real.pi * |theta - phi| := by
  rw [periodicPoint, periodicPoint]
  refine (norm_unitPoint_sub_le _ _).trans ?_
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

theorem norm_pow_sub_pow_le_of_norm_eq_one (z w : ℂ)
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (k : ℕ) :
    ‖z ^ k - w ^ k‖ ≤ k * ‖z - w‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      have hid : z ^ k * z - w ^ k * w =
          z ^ k * (z - w) + (z ^ k - w ^ k) * w := by ring
      rw [hid]
      calc
        ‖z ^ k * (z - w) + (z ^ k - w ^ k) * w‖ ≤
            ‖z ^ k * (z - w)‖ + ‖(z ^ k - w ^ k) * w‖ := norm_add_le _ _
        _ = ‖z - w‖ + ‖z ^ k - w ^ k‖ := by
          simp [norm_pow, hz, hw]
        _ ≤ ‖z - w‖ + k * ‖z - w‖ := by gcongr
        _ = ((k + 1 : ℕ) : ℝ) * ‖z - w‖ := by
          norm_num
          ring

/-- Every real phase has a representative within `1 / G` of a point on the
period-one grid indexed by `Fin G`. -/
theorem exists_gridIndex (G : ℕ) (hG : 0 < G) (theta : ℝ) :
    ∃ j : Fin G,
      0 ≤ Int.fract theta - (j : ℕ) / (G : ℝ) ∧
      Int.fract theta - (j : ℕ) / (G : ℝ) < 1 / (G : ℝ) := by
  let j0 : ℕ := ⌊(G : ℝ) * Int.fract theta⌋₊
  have hnonneg : 0 ≤ (G : ℝ) * Int.fract theta :=
    mul_nonneg (by positivity) (Int.fract_nonneg theta)
  have hjlt : j0 < G := by
    apply (Nat.floor_lt hnonneg).2
    have hGreal : (0 : ℝ) < G := by exact_mod_cast hG
    simpa using (mul_lt_mul_of_pos_left (Int.fract_lt_one theta) hGreal)
  let j : Fin G := ⟨j0, hjlt⟩
  refine ⟨j, ?_, ?_⟩
  · have hfloor : (j0 : ℝ) ≤ (G : ℝ) * Int.fract theta :=
      Nat.floor_le hnonneg
    have hGreal : (0 : ℝ) < G := by exact_mod_cast hG
    apply sub_nonneg.mpr
    rw [div_le_iff₀ hGreal]
    simpa [j, j0, mul_comm, add_comm] using hfloor
  · have hfloor : (G : ℝ) * Int.fract theta < (j0 : ℝ) + 1 :=
      Nat.lt_floor_add_one ((G : ℝ) * Int.fract theta)
    have hGreal : (0 : ℝ) < G := by exact_mod_cast hG
    rw [sub_lt_iff_lt_add, ← add_div]
    apply (lt_div_iff₀ hGreal).2
    simpa [j, j0, mul_comm, add_comm] using hfloor

/-- Direct coefficientwise Lipschitz bound for a degree-`n` Fourier sum
whose coefficients have norm at most one. -/
theorem norm_normalizedZerothValue_sub_le_of_norm_le {n : ℕ}
    (c : Fin (n + 1) → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hc : ∀ k, ‖c k‖ ≤ L) (theta phi : ℝ) :
    ‖normalizedZerothValue c theta - normalizedZerothValue c phi‖ ≤
      L * (2 * Real.pi * |theta - phi| * (n + 1) * n) := by
  classical
  rw [normalizedZerothValue, normalizedZerothValue, ← Finset.sum_sub_distrib]
  calc
    ‖∑ k : Fin (n + 1),
        (c k * periodicPoint theta ^ k.1 - c k * periodicPoint phi ^ k.1)‖ ≤
        ∑ k : Fin (n + 1),
          ‖c k * periodicPoint theta ^ k.1 - c k * periodicPoint phi ^ k.1‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k : Fin (n + 1),
        (L * (2 * Real.pi * |theta - phi| * n)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← mul_sub, norm_mul]
      calc
        ‖c k‖ * ‖periodicPoint theta ^ k.1 - periodicPoint phi ^ k.1‖ ≤
            L * ‖periodicPoint theta ^ k.1 - periodicPoint phi ^ k.1‖ := by
          gcongr
          exact hc k
        _ ≤ L * (k.1 * ‖periodicPoint theta - periodicPoint phi‖) := by
          gcongr
          simpa using norm_pow_sub_pow_le_of_norm_eq_one
            (periodicPoint theta) (periodicPoint phi)
            (norm_periodicPoint theta) (norm_periodicPoint phi) k.1
        _ ≤ L * (k.1 * (2 * Real.pi * |theta - phi|)) := by
          gcongr
          exact norm_periodicPoint_sub_le theta phi
        _ ≤ L * (n * (2 * Real.pi * |theta - phi|)) := by
          gcongr
          exact_mod_cast (show k.1 ≤ n by omega)
        _ = L * (2 * Real.pi * |theta - phi| * n) := by ring
    _ = L * (2 * Real.pi * |theta - phi| * (n + 1) * n) := by
      simp
      ring

theorem norm_normalizedZerothValue_sub_le {n : ℕ}
    (c : Fin (n + 1) → ℂ) (hc : ∀ k, ‖c k‖ ≤ 1) (theta phi : ℝ) :
    ‖normalizedZerothValue c theta - normalizedZerothValue c phi‖ ≤
      2 * Real.pi * |theta - phi| * (n + 1) * n := by
  simpa using
    norm_normalizedZerothValue_sub_le_of_norm_le c 1 zero_le_one hc theta phi

theorem normalizedZerothValue_fract {n : ℕ}
    (c : Fin (n + 1) → ℂ) (theta : ℝ) :
    normalizedZerothValue c (Int.fract theta) = normalizedZerothValue c theta := by
  classical
  rw [normalizedZerothValue, normalizedZerothValue]
  apply Finset.sum_congr rfl
  intro k hk
  rw [periodicPoint_fract]

/-- A strict bound on a period-one grid gives a whole-circle bound with an
explicit coefficientwise interpolation loss. -/
theorem norm_normalizedZerothValue_lt_of_grid {n G : ℕ}
    (c : Fin (n + 1) → ℂ) (hc : ∀ k, ‖c k‖ ≤ 2)
    (hG : 0 < G) (R : ℝ)
    (hgrid : ∀ j : Fin G,
      ‖normalizedZerothValue c ((j : ℕ) / (G : ℝ))‖ < R)
    (theta : ℝ) :
    ‖normalizedZerothValue c theta‖ <
      4 * Real.pi * (n + 1) * n / G + R := by
  obtain ⟨j, hj0, hj1⟩ := exists_gridIndex G hG theta
  let x := Int.fract theta
  let y : ℝ := (j : ℕ) / (G : ℝ)
  have hxy : |x - y| ≤ 1 / (G : ℝ) := by
    rw [abs_of_nonneg]
    · exact hj1.le
    · exact hj0
  have hinterp := norm_normalizedZerothValue_sub_le_of_norm_le
    c 2 (by norm_num) hc x y
  have hinterp' :
      ‖normalizedZerothValue c x - normalizedZerothValue c y‖ ≤
        4 * Real.pi * (n + 1) * n / G := by
    calc
      ‖normalizedZerothValue c x - normalizedZerothValue c y‖ ≤
          2 * (2 * Real.pi * |x - y| * (n + 1) * n) := hinterp
      _ ≤ 2 * (2 * Real.pi * (1 / (G : ℝ)) * (n + 1) * n) := by
        gcongr
      _ = 4 * Real.pi * (n + 1) * n / G := by ring
  rw [← normalizedZerothValue_fract c theta]
  calc
    ‖normalizedZerothValue c x‖ =
        ‖(normalizedZerothValue c x - normalizedZerothValue c y) +
          normalizedZerothValue c y‖ := by ring_nf
    _ ≤ ‖normalizedZerothValue c x - normalizedZerothValue c y‖ +
        ‖normalizedZerothValue c y‖ := norm_add_le _ _
    _ < 4 * Real.pi * (n + 1) * n / G + R :=
      add_lt_add_of_le_of_lt hinterp' (hgrid j)

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos230/Rounding.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Whole-circle unimodular rounding for Erdős Problem 230

This combines the finite-grid Rademacher correction with the elementary
grid interpolation estimate.
-/



open scoped BigOperators

noncomputable section

open Correction

/-- The monomial phase on the `G`-point period-one grid. -/
def gridPhase {n G : ℕ} (i : Fin (n + 1)) (j : Fin G) : ℂ :=
  periodicPoint ((j : ℕ) / (G : ℝ)) ^ i.1

@[simp]
theorem norm_gridPhase {n G : ℕ} (i : Fin (n + 1)) (j : Fin G) :
    ‖gridPhase i j‖ = 1 := by
  simp [gridPhase]

/-- Round coefficients in the closed unit disk to the unit circle.  The
random estimate controls the correction on the `G`-point grid, and the
second summand is the explicit interpolation loss. -/
theorem exists_unit_rounding_circle_defect {n G : ℕ}
    (a : Fin (n + 1) → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hG : 0 < G) {R : ℝ} (hR : 0 < R)
    (hsmall : G *
      (4 * Real.exp (-R ^ 2 / (8 * defect a))) < 1) :
    ∃ b : Fin (n + 1) → ℂ, (∀ i, ‖b i‖ = 1) ∧
      ∀ theta : ℝ,
        ‖normalizedZerothValue b theta - normalizedZerothValue a theta‖ <
          4 * Real.pi * (n + 1) * n / G + R := by
  obtain ⟨b, hb, hgrid⟩ := exists_unit_rounding_grid_defect
    a ha gridPhase (fun i j => (norm_gridPhase i j).le) hR (by simpa using hsmall)
  refine ⟨b, hb, ?_⟩
  intro theta
  let c : Fin (n + 1) → ℂ := fun i => b i - a i
  have hc : ∀ i, ‖c i‖ ≤ 2 := by
    intro i
    dsimp [c]
    calc
      ‖b i - a i‖ ≤ ‖b i‖ + ‖a i‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hb i).le (ha i)
      _ = 2 := by norm_num
  have hcirc := norm_normalizedZerothValue_lt_of_grid c hc hG R
    (fun j => by
      simpa [c, normalizedZerothValue, gridPhase] using hgrid j) theta
  rw [normalizedZerothValue, normalizedZerothValue,
    ← Finset.sum_sub_distrib]
  simpa [c, normalizedZerothValue, sub_mul] using hcirc

/-- The zero-defect case needs no random correction. -/
theorem exists_unit_rounding_circle_of_defect_eq_zero {n : ℕ}
    (a : Fin (n + 1) → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1)
    (hzero : defect a = 0) :
    ∃ b : Fin (n + 1) → ℂ, (∀ i, ‖b i‖ = 1) ∧
      ∀ theta : ℝ,
        ‖normalizedZerothValue b theta - normalizedZerothValue a theta‖ = 0 := by
  refine ⟨a, fun i => norm_eq_one_of_defect_eq_zero a ha hzero i, ?_⟩
  intro theta
  simp

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos230/Construction.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The explicit Gaussian chirp for Erdős Problem 230

This file specializes the analytic and probabilistic estimates to the scales
`n = m^18`, `s = m^12`, `K = m^15`, and `r = m^6`.
-/

open scoped BigOperators Interval



noncomputable section

open GaussianCutoff GaussianPoisson Correction MeasureTheory Set

/-- Number of nonconstant coefficients in the construction. -/
def constructionDegree (m : ℕ) : ℕ := m ^ 18

/-- Width of the Gaussian used to smooth the central interval. -/
def constructionScale (m : ℕ) : ℝ := (m : ℝ) ^ 12

/-- Size of each boundary strip removed before Gaussian smoothing. -/
def constructionMargin (m : ℕ) : ℕ := m ^ 15

/-- Damping ratio `s^2 / n`. -/
def constructionRatio (m : ℕ) : ℝ := (m : ℝ) ^ 6

/-- The number of interpolation grid points. -/
def constructionGrid (m : ℕ) : ℕ := constructionDegree m ^ 3

/-- The sub-unimodular Gaussian chirp coefficients. -/
def baseCoefficient (m : ℕ) : Fin (constructionDegree m + 1) → ℂ :=
  fun k =>
    (chi (constructionScale m) (constructionMargin m)
        (constructionDegree m) k.1 : ℂ) *
      e (((k.1 : ℝ) ^ 2) / (2 * constructionDegree m) - (k.1 : ℝ) / 2)

lemma two_margin_le_degree {m : ℕ} (hm : 2 ≤ m) :
    2 * constructionMargin m ≤ constructionDegree m := by
  simp only [constructionMargin, constructionDegree]
  calc
    2 * m ^ 15 ≤ m ^ 3 * m ^ 15 := by
      gcongr
      exact hm.trans (Nat.le_pow (a := m) (b := 3) (by norm_num))
    _ = m ^ 18 := by ring

lemma constructionScale_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < constructionScale m := by
  simp only [constructionScale]
  positivity

lemma constructionRatio_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < constructionRatio m := by
  simp only [constructionRatio]
  positivity

lemma constructionDegree_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < constructionDegree m := by
  simp only [constructionDegree]
  positivity

lemma constructionGrid_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < constructionGrid m := by
  exact pow_pos (constructionDegree_pos hm) 3

@[simp]
lemma norm_baseCoefficient {m : ℕ} (hm : 2 ≤ m)
    (k : Fin (constructionDegree m + 1)) :
    ‖baseCoefficient m k‖ =
      chi (constructionScale m) (constructionMargin m)
        (constructionDegree m) k.1 := by
  rw [baseCoefficient, norm_mul, norm_e, mul_one, Complex.norm_real,
    Real.norm_of_nonneg]
  exact chi_nonneg (constructionScale_pos hm) (two_margin_le_degree hm) k.1

lemma norm_baseCoefficient_le_one {m : ℕ} (hm : 2 ≤ m)
    (k : Fin (constructionDegree m + 1)) :
    ‖baseCoefficient m k‖ ≤ 1 := by
  rw [norm_baseCoefficient hm]
  exact chi_le_one (constructionScale_pos hm) (two_margin_le_degree hm) k.1

/-- The exact chord defect of the Gaussian chirp is the cutoff's loss of
squared mass. -/
lemma defect_baseCoefficient {m : ℕ} (hm : 2 ≤ m) :
    defect (baseCoefficient m) =
      ∑ k : Fin (constructionDegree m + 1),
        (1 - chi (constructionScale m) (constructionMargin m)
          (constructionDegree m) k.1 ^ 2) := by
  rw [defect]
  apply Finset.sum_congr rfl
  intro k _
  rw [norm_baseCoefficient hm]

lemma defect_baseCoefficient_nonneg {m : ℕ} (hm : 2 ≤ m) :
    0 ≤ defect (baseCoefficient m) := by
  rw [defect]
  exact Finset.sum_nonneg fun k _ =>
    defect_term_nonneg (norm_baseCoefficient_le_one hm k)

lemma defect_baseCoefficient_le_raw {m : ℕ} (hm : 2 ≤ m) :
    defect (baseCoefficient m) ≤
      4 * (constructionMargin m : ℝ) + 4 * (constructionScale m + 1) := by
  rw [defect_baseCoefficient hm]
  calc
    (∑ k : Fin (constructionDegree m + 1),
        (1 - chi (constructionScale m) (constructionMargin m)
          (constructionDegree m) k.1 ^ 2)) =
        ∑ k ∈ Finset.range (constructionDegree m + 1),
          (1 - chi (constructionScale m) (constructionMargin m)
            (constructionDegree m) k ^ 2) := by
      exact Fin.sum_univ_eq_sum_range
        (fun k : ℕ => 1 - chi (constructionScale m) (constructionMargin m)
          (constructionDegree m) k ^ 2) (constructionDegree m + 1)
    _ ≤ _ := sum_one_sub_chi_sq_range_le
      (constructionScale_pos hm) (two_margin_le_degree hm)

lemma defect_baseCoefficient_le {m : ℕ} (hm : 2 ≤ m) :
    defect (baseCoefficient m) ≤ 8 * (m : ℝ) ^ 15 := by
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hmone : (1 : ℝ) ≤ m := by linarith
  have hm12 : (1 : ℝ) ≤ (m : ℝ) ^ 12 := one_le_pow₀ hmone
  have hm3 : (2 : ℝ) ≤ (m : ℝ) ^ 3 := by
    calc
      (2 : ℝ) ≤ m := hmreal
      _ = (m : ℝ) ^ 1 := by ring
      _ ≤ (m : ℝ) ^ 3 := pow_le_pow_right₀ hmone (by norm_num)
  have hscale : (m : ℝ) ^ 12 + 1 ≤ (m : ℝ) ^ 15 := by
    calc
      (m : ℝ) ^ 12 + 1 ≤ 2 * (m : ℝ) ^ 12 := by linarith
      _ ≤ (m : ℝ) ^ 3 * (m : ℝ) ^ 12 := by gcongr
      _ = (m : ℝ) ^ 15 := by ring
  calc
    defect (baseCoefficient m) ≤
        4 * (constructionMargin m : ℝ) +
          4 * (constructionScale m + 1) := defect_baseCoefficient_le_raw hm
    _ = 4 * (m : ℝ) ^ 15 + 4 * ((m : ℝ) ^ 12 + 1) := by
      simp [constructionMargin, constructionScale]
    _ ≤ 8 * (m : ℝ) ^ 15 := by nlinarith

lemma constructionGrid_cast (m : ℕ) :
    (constructionGrid m : ℝ) = (m : ℝ) ^ 54 := by
  simp only [constructionGrid, constructionDegree, Nat.cast_pow]
  ring

lemma constructionRatio_eq {m : ℕ} (hm : 2 ≤ m) :
    constructionScale m ^ 2 / (constructionDegree m : ℝ) =
      constructionRatio m := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  simp only [constructionScale, constructionDegree, constructionRatio, Nat.cast_pow]
  field_simp

/-- The full, untruncated smoothed chirp at the construction parameters. -/
def constructionFullValue (m : ℕ) (theta : ℝ) : ℂ :=
  fullIntegerSmoothedChirp (constructionDegree m) (constructionScale m)
    (constructionMargin m) theta

/-- The integer-indexed coefficient series whose integral form is
`constructionFullValue`. -/
def integerChirpCoefficient (m : ℕ) (theta : ℝ) (k : ℤ) : ℂ :=
  (chi (constructionScale m) (constructionMargin m)
      (constructionDegree m) k : ℂ) *
    e (chirpPhase (constructionDegree m) theta k)

@[simp]
lemma norm_integerChirpCoefficient {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) (k : ℤ) :
    ‖integerChirpCoefficient m theta k‖ =
      chi (constructionScale m) (constructionMargin m)
        (constructionDegree m) k := by
  rw [integerChirpCoefficient, norm_mul, norm_e, mul_one, Complex.norm_real,
    Real.norm_of_nonneg]
  exact chi_nonneg (constructionScale_pos hm) (two_margin_le_degree hm) k

lemma norm_integerChirpCoefficient_neg_add_one {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) (j : ℕ) :
    ‖integerChirpCoefficient m theta (-(j + 1 : ℤ))‖ =
      outsideLeft (constructionScale m) (constructionMargin m)
        (constructionDegree m) j := by
  rw [norm_integerChirpCoefficient hm]
  simp [outsideLeft]

lemma norm_integerChirpCoefficient_degree_add_one {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) (j : ℕ) :
    ‖integerChirpCoefficient m theta
        (constructionDegree m + j + 1 : ℤ)‖ =
      outsideRight (constructionScale m) (constructionMargin m)
        (constructionDegree m) j := by
  rw [norm_integerChirpCoefficient hm]
  simp [outsideRight]

lemma summable_norm_integerChirpCoefficient {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) : Summable fun k : ℤ => ‖integerChirpCoefficient m theta k‖ := by
  apply Summable.of_add_one_of_neg_add_one
  · apply (summable_nat_add_iff (constructionDegree m)).mp
    have heq : (fun j : ℕ => ‖integerChirpCoefficient m theta
        (((j + constructionDegree m : ℕ) : ℤ) + 1)‖) =
        outsideRight (constructionScale m) (constructionMargin m)
          (constructionDegree m) := by
      funext j
      convert norm_integerChirpCoefficient_degree_add_one hm theta j using 1 <;>
        push_cast <;> ring
    rw [heq]
    exact summable_outsideRight (constructionScale_pos hm)
      (two_margin_le_degree hm)
  · have heq : (fun j : ℕ => ‖integerChirpCoefficient m theta
        (-((j : ℤ) + 1))‖) =
        outsideLeft (constructionScale m) (constructionMargin m)
          (constructionDegree m) := by
      funext j
      exact norm_integerChirpCoefficient_neg_add_one hm theta j
    rw [heq]
    exact summable_outsideLeft (constructionScale_pos hm)
      (two_margin_le_degree hm)

lemma summable_integerChirpCoefficient {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) : Summable (integerChirpCoefficient m theta) :=
  (summable_norm_integerChirpCoefficient hm theta).of_norm

lemma gaussianKernel_eq_phi {s : ℝ} (hs : 0 < s) (x : ℝ) :
    gaussianKernel s x = phi s x := by
  simp only [gaussianKernel, phi]
  congr 2
  field_simp [hs.ne']

lemma gaussianCutoff_eq_chi {s : ℝ} (hs : 0 < s) {K n : ℕ}
    (hKn : 2 * K ≤ n) (k : ℤ) :
    gaussianCutoff s K n k = chi s K n k := by
  have hKn' : K ≤ n := by omega
  have hcast : ((n - K : ℕ) : ℝ) = (n : ℝ) - K := by
    exact Nat.cast_sub hKn'
  rw [gaussianCutoff, chi, hcast]
  apply intervalIntegral.integral_congr
  intro y _
  exact gaussianKernel_eq_phi hs ((k : ℝ) - y)

lemma intervalIntegral_norm_gaussianChirpAtom_eq_chi {m : ℕ}
    (hm : 2 ≤ m) (theta : ℝ) (k : ℤ) :
    (∫ y in (constructionMargin m : ℝ)..
        (constructionDegree m : ℝ) - constructionMargin m,
        ‖gaussianChirpAtom (constructionDegree m) (constructionScale m)
          theta y k‖) =
      chi (constructionScale m) (constructionMargin m)
        (constructionDegree m) k := by
  have hn : 0 < (constructionDegree m : ℝ) := by
    exact_mod_cast constructionDegree_pos hm
  have hs := constructionScale_pos hm
  have hKn' : constructionMargin m ≤ constructionDegree m := by
    have := two_margin_le_degree hm
    omega
  have hcast : (((constructionDegree m - constructionMargin m : ℕ) : ℝ)) =
      (constructionDegree m : ℝ) - constructionMargin m := by
    exact Nat.cast_sub hKn'
  rw [chi, hcast]
  apply intervalIntegral.integral_congr
  intro y _
  change ‖gaussianChirpAtom (constructionDegree m) (constructionScale m)
    theta y k‖ = phi (constructionScale m) ((k : ℝ) - y)
  rw [gaussianChirpAtom_eq_cutoffIntegrand _ _ _ _ _ hn hs,
    norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_of_nonneg]
  · exact gaussianKernel_eq_phi hs ((k : ℝ) - y)
  · exact mul_nonneg (inv_nonneg.mpr hs.le) (Real.exp_pos _).le

/-- The integral definition used for Poisson summation is exactly the
absolutely convergent integer coefficient series. -/
lemma constructionFullValue_eq_tsum {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    constructionFullValue m theta =
      ∑' k : ℤ, integerChirpCoefficient m theta k := by
  have hn : 0 < (constructionDegree m : ℝ) := by
    exact_mod_cast constructionDegree_pos hm
  have hs := constructionScale_pos hm
  have hK : (constructionMargin m : ℝ) ≤
      (constructionDegree m : ℝ) - constructionMargin m := by
    have hh : 2 * (constructionMargin m : ℝ) ≤ constructionDegree m := by
      exact_mod_cast two_margin_le_degree hm
    linarith
  have hFint (k : ℤ) : Integrable
      (fun y => gaussianChirpAtom (constructionDegree m) (constructionScale m)
        theta y k)
      (volume.restrict (Set.Ioc (constructionMargin m : ℝ)
        ((constructionDegree m : ℝ) - constructionMargin m))) := by
    have hi := (show Continuous (fun y =>
        gaussianChirpAtom (constructionDegree m) (constructionScale m)
          theta y k) by
      unfold gaussianChirpAtom
      fun_prop).intervalIntegrable (μ := volume)
        (constructionMargin m : ℝ)
          ((constructionDegree m : ℝ) - constructionMargin m)
    rw [intervalIntegrable_iff, uIoc_of_le hK] at hi
    exact hi
  have hmass : Summable (fun k : ℤ =>
      ∫ y in Set.Ioc (constructionMargin m : ℝ)
          ((constructionDegree m : ℝ) - constructionMargin m),
        ‖gaussianChirpAtom (constructionDegree m) (constructionScale m)
          theta y k‖) := by
    apply (summable_norm_integerChirpCoefficient hm theta).congr
    intro k
    rw [← intervalIntegral.integral_of_le hK]
    rw [intervalIntegral_norm_gaussianChirpAtom_eq_chi hm theta k]
    exact norm_integerChirpCoefficient hm theta k
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (constructionMargin m : ℝ)
      ((constructionDegree m : ℝ) - constructionMargin m))) hFint hmass
  calc
    constructionFullValue m theta =
        ∫ y in Set.Ioc (constructionMargin m : ℝ)
            ((constructionDegree m : ℝ) - constructionMargin m),
          ∑' k : ℤ, gaussianChirpAtom (constructionDegree m)
            (constructionScale m) theta y k := by
      rw [constructionFullValue, fullIntegerSmoothedChirp,
        intervalIntegral.integral_of_le hK]
    _ = ∑' k : ℤ,
        ∫ y in Set.Ioc (constructionMargin m : ℝ)
            ((constructionDegree m : ℝ) - constructionMargin m),
          gaussianChirpAtom (constructionDegree m) (constructionScale m)
            theta y k := hswap.symm
    _ = ∑' k : ℤ, integerChirpCoefficient m theta k := by
      apply tsum_congr
      intro k
      rw [← intervalIntegral.integral_of_le hK,
        intervalIntegral_gaussianChirpAtom _ _ _ _ _ hn hs,
        gaussianCutoff_eq_chi hs (two_margin_le_degree hm)]
      rfl

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  rw [e, e, e, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma periodicPoint_pow_eq_e (theta : ℝ) (k : ℕ) :
    periodicPoint theta ^ k = e ((k : ℝ) * theta) := by
  rw [periodicPoint, unitPoint, e, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma baseCoefficient_mul_periodicPoint_pow {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) (k : Fin (constructionDegree m + 1)) :
    baseCoefficient m k * periodicPoint theta ^ k.1 =
      integerChirpCoefficient m theta k.1 := by
  rw [baseCoefficient, integerChirpCoefficient, periodicPoint_pow_eq_e,
    mul_assoc, ← e_add]
  congr 2
  simp only [chirpPhase]
  push_cast
  ring

lemma normalizedZerothValue_baseCoefficient {m : ℕ} (hm : 2 ≤ m)
    (theta : ℝ) :
    normalizedZerothValue (baseCoefficient m) theta =
      ∑ k ∈ Finset.range (constructionDegree m + 1),
        integerChirpCoefficient m theta k := by
  rw [normalizedZerothValue, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < constructionDegree m + 1 := Finset.mem_range.mp hk
  rw [dif_pos hk']
  exact baseCoefficient_mul_periodicPoint_pow hm theta ⟨k, hk'⟩

lemma summable_rightIntegerChirp {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    Summable (fun j : ℕ => integerChirpCoefficient m theta
      (constructionDegree m + j + 1 : ℤ)) := by
  apply Summable.of_norm
  apply (summable_outsideRight (constructionScale_pos hm)
    (two_margin_le_degree hm)).congr
  intro j
  exact (norm_integerChirpCoefficient_degree_add_one hm theta j).symm

lemma summable_leftIntegerChirp {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    Summable (fun j : ℕ => integerChirpCoefficient m theta (-(j + 1 : ℤ))) := by
  apply Summable.of_norm
  apply (summable_outsideLeft (constructionScale_pos hm)
    (two_margin_le_degree hm)).congr
  intro j
  exact (norm_integerChirpCoefficient_neg_add_one hm theta j).symm

lemma summable_positiveIntegerChirp {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    Summable (fun j : ℕ => integerChirpCoefficient m theta (j + 1)) := by
  apply (summable_nat_add_iff (constructionDegree m)).mp
  have hright := summable_rightIntegerChirp hm theta
  have heq : (fun j : ℕ => integerChirpCoefficient m theta
      (((j + constructionDegree m : ℕ) : ℤ) + 1)) =
      (fun j : ℕ => integerChirpCoefficient m theta
        (constructionDegree m + j + 1 : ℤ)) := by
    funext j
    congr 1
    push_cast
    ring
  rw [heq]
  exact hright

/-- Truncating the full integer chirp to the coefficients `0, ..., m^18`
costs less than one, uniformly in the angular variable. -/
lemma norm_base_sub_full_lt_one {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    ‖normalizedZerothValue (baseCoefficient m) theta -
        constructionFullValue m theta‖ < 1 := by
  let f : ℤ → ℂ := integerChirpCoefficient m theta
  let right : ℕ → ℂ := fun j => f (constructionDegree m + j + 1)
  let left : ℕ → ℂ := fun j => f (-(j + 1 : ℤ))
  have hpos : Summable (fun j : ℕ => f (j + 1)) :=
    summable_positiveIntegerChirp hm theta
  have hright : Summable right := summable_rightIntegerChirp hm theta
  have hleft : Summable left := summable_leftIntegerChirp hm theta
  have hsplit := hpos.sum_add_tsum_nat_add (constructionDegree m)
  have hfull := tsum_of_add_one_of_neg_add_one hpos hleft
  have hsplit' :
      (∑ i ∈ Finset.range (constructionDegree m), f (i + 1)) +
          (∑' j : ℕ, right j) = ∑' j : ℕ, f (j + 1) := by
    simpa [right, add_assoc, add_comm, add_left_comm] using hsplit
  have hfull' :
      (∑' k : ℤ, f k) = (∑' j : ℕ, f (j + 1)) + f 0 +
          ∑' j : ℕ, left j := by
    simpa [left, add_assoc, add_comm, add_left_comm] using hfull
  have hdecomp : normalizedZerothValue (baseCoefficient m) theta +
      (∑' j : ℕ, right j) + (∑' j : ℕ, left j) =
        constructionFullValue m theta := by
    rw [constructionFullValue_eq_tsum hm theta,
      normalizedZerothValue_baseCoefficient hm theta,
      Finset.sum_range_succ', hfull']
    rw [← hsplit']
    simp only [f, right, left]
    push_cast
    ring
  have hrightNormSumm : Summable (fun j : ℕ => ‖right j‖) := by
    apply (summable_outsideRight (constructionScale_pos hm)
      (two_margin_le_degree hm)).congr
    intro j
    exact (norm_integerChirpCoefficient_degree_add_one hm theta j).symm
  have hleftNormSumm : Summable (fun j : ℕ => ‖left j‖) := by
    apply (summable_outsideLeft (constructionScale_pos hm)
      (two_margin_le_degree hm)).congr
    intro j
    exact (norm_integerChirpCoefficient_neg_add_one hm theta j).symm
  have hrightNorm : ‖∑' j : ℕ, right j‖ ≤
      ∑' j : ℕ, outsideRight (constructionScale m) (constructionMargin m)
        (constructionDegree m) j := by
    calc
      ‖∑' j : ℕ, right j‖ ≤ ∑' j : ℕ, ‖right j‖ :=
        norm_tsum_le_tsum_norm hrightNormSumm
      _ = _ := by
        apply tsum_congr
        intro j
        exact norm_integerChirpCoefficient_degree_add_one hm theta j
  have hleftNorm : ‖∑' j : ℕ, left j‖ ≤
      ∑' j : ℕ, outsideLeft (constructionScale m) (constructionMargin m)
        (constructionDegree m) j := by
    calc
      ‖∑' j : ℕ, left j‖ ≤ ∑' j : ℕ, ‖left j‖ :=
        norm_tsum_le_tsum_norm hleftNormSumm
      _ = _ := by
        apply tsum_congr
        intro j
        exact norm_integerChirpCoefficient_neg_add_one hm theta j
  calc
    ‖normalizedZerothValue (baseCoefficient m) theta -
        constructionFullValue m theta‖ =
        ‖-(∑' j : ℕ, right j) - (∑' j : ℕ, left j)‖ := by
      congr 1
      rw [← hdecomp]
      ring
    _ = ‖(∑' j : ℕ, right j) + (∑' j : ℕ, left j)‖ := by
      rw [show -(∑' j : ℕ, right j) - (∑' j : ℕ, left j) =
          -((∑' j : ℕ, right j) + (∑' j : ℕ, left j)) by ring, norm_neg]
    _ ≤ ‖∑' j : ℕ, right j‖ + ‖∑' j : ℕ, left j‖ := norm_add_le _ _
    _ ≤ (∑' j : ℕ, outsideLeft (constructionScale m) (constructionMargin m)
          (constructionDegree m) j) +
        ∑' j : ℕ, outsideRight (constructionScale m) (constructionMargin m)
          (constructionDegree m) j := by linarith
    _ < 1 := by
      simpa [constructionScale, constructionMargin, constructionDegree,
        Nat.cast_pow] using tsum_outside_pow_lt_one hm

/-- The Poisson estimate at the chosen powers.  The exact main term is even
closer to `m^9`; the additive one is a convenient formal upper bound. -/
lemma norm_constructionFullValue_le {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    ‖constructionFullValue m theta‖ ≤ (m : ℝ) ^ 9 + 1 := by
  have hn : 0 < (constructionDegree m : ℝ) := by
    exact_mod_cast constructionDegree_pos hm
  have hs := constructionScale_pos hm
  have hK0 : 0 ≤ (constructionMargin m : ℝ) := by positivity
  have hK : (constructionMargin m : ℝ) ≤
      (constructionDegree m : ℝ) - constructionMargin m := by
    have hh : 2 * (constructionMargin m : ℝ) ≤ constructionDegree m := by
      exact_mod_cast two_margin_le_degree hm
    linarith
  have hmain := norm_fullIntegerSmoothedChirp_le_exact
    (constructionDegree m : ℝ) (constructionScale m)
      (constructionMargin m : ℝ) theta hn hs hK0 hK
  rw [constructionFullValue]
  calc
    ‖fullIntegerSmoothedChirp (constructionDegree m) (constructionScale m)
        (constructionMargin m) theta‖ ≤
        Real.sqrt (constructionDegree m : ℝ) *
          (1 + (constructionScale m ^ 2 /
            (constructionDegree m : ℝ))⁻¹ ^ 2) ^ (1 / 4 : ℝ) := hmain
    _ = (m : ℝ) ^ 9 *
          (1 + (constructionRatio m)⁻¹ ^ 2) ^ (1 / 4 : ℝ) := by
      rw [constructionRatio_eq hm, constructionDegree, sqrt_nat_pow_eighteen]
    _ ≤ (m : ℝ) ^ 9 * (1 + (constructionRatio m)⁻¹ ^ 2) := by
      gcongr
      apply Real.rpow_le_self_of_one_le
      · exact le_add_of_nonneg_right (sq_nonneg _)
      · norm_num
    _ = (m : ℝ) ^ 9 + 1 / (m : ℝ) ^ 3 := by
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      simp only [constructionRatio]
      field_simp
    _ ≤ (m : ℝ) ^ 9 + 1 := by
      gcongr
      exact (div_le_one (by positivity)).2
        (one_le_pow₀ (by exact_mod_cast (show 1 ≤ m by omega)))

lemma norm_baseCoefficient_value_lt {m : ℕ} (hm : 2 ≤ m) (theta : ℝ) :
    ‖normalizedZerothValue (baseCoefficient m) theta‖ <
      (m : ℝ) ^ 9 + 2 := by
  calc
    ‖normalizedZerothValue (baseCoefficient m) theta‖ ≤
        ‖normalizedZerothValue (baseCoefficient m) theta -
          constructionFullValue m theta‖ + ‖constructionFullValue m theta‖ := by
      simpa [sub_add_cancel] using norm_add_le
        (normalizedZerothValue (baseCoefficient m) theta - constructionFullValue m theta)
        (constructionFullValue m theta)
    _ < 1 + ((m : ℝ) ^ 9 + 1) :=
      add_lt_add_of_lt_of_le (norm_base_sub_full_lt_one hm theta)
        (norm_constructionFullValue_le hm theta)
    _ = (m : ℝ) ^ 9 + 2 := by ring

lemma construction_interpolation_loss_lt_one {m : ℕ} (hm : 2 ≤ m) :
    4 * Real.pi * (constructionDegree m + 1) * constructionDegree m /
        constructionGrid m < 1 := by
  let N : ℝ := constructionDegree m
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast constructionDegree_pos hm
  have hpow : 2 ^ 18 ≤ m ^ 18 := Nat.pow_le_pow_left hm 18
  have hN32 : (32 : ℝ) < N := by
    dsimp [N, constructionDegree]
    exact_mod_cast (show 32 < m ^ 18 by omega)
  have hG : (constructionGrid m : ℝ) = N ^ 3 := by
    rw [constructionGrid_cast]
    dsimp [N, constructionDegree]
    push_cast
    ring
  change 4 * Real.pi * (N + 1) * N / (constructionGrid m : ℝ) < 1
  rw [div_lt_iff₀ (by exact_mod_cast constructionGrid_pos hm)]
  simp only [one_mul]
  calc
    4 * Real.pi * (N + 1) * N < 16 * (N + 1) * N := by
      gcongr
      nlinarith [Real.pi_lt_four]
    _ ≤ 32 * N * N := by
      have : N + 1 ≤ 2 * N := by nlinarith
      calc
        16 * (N + 1) * N ≤ 16 * (2 * N) * N := by gcongr
        _ = 32 * N * N := by ring
    _ < N * N * N := by
      have hmid : 32 * N < N * N := mul_lt_mul_of_pos_right hN32 hNpos
      exact mul_lt_mul_of_pos_right hmid hNpos
    _ = (constructionGrid m : ℝ) := by rw [hG]; ring

/-- A degree-54 polynomial is eventually dominated by the exponential in
the finite-grid union bound. -/
lemma eventually_rounding_exponential_small :
    ∀ᶠ m : ℕ in Filter.atTop,
      4 * (m : ℝ) ^ 54 * Real.exp (-(m : ℝ) / 64) < 1 := by
  have ht : Filter.Tendsto (fun x : ℝ =>
      4 * (x ^ (54 : ℝ) * Real.exp (-(1 / 64 : ℝ) * x)))
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 54 (1 / 64)
        (by norm_num)).const_mul 4
  have hnat := ht.comp tendsto_natCast_atTop_atTop
  have hev := hnat.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with m hm hm1
  simpa [Real.rpow_natCast, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    using hm

/-- The concrete union-bound hypothesis, reduced to the preceding elementary
exponential estimate. -/
lemma rounding_probability_small {m : ℕ} (hm : 2 ≤ m)
    (hdef : defect (baseCoefficient m) ≠ 0)
    (hexp : 4 * (m : ℝ) ^ 54 * Real.exp (-(m : ℝ) / 64) < 1) :
    constructionGrid m *
        (4 * Real.exp (-((m : ℝ) ^ 8) ^ 2 /
          (8 * defect (baseCoefficient m)))) < 1 := by
  have hDpos : 0 < defect (baseCoefficient m) :=
    lt_of_le_of_ne (defect_baseCoefficient_nonneg hm) (Ne.symm hdef)
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hratio : (m : ℝ) / 64 ≤
      ((m : ℝ) ^ 8) ^ 2 / (8 * defect (baseCoefficient m)) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hDpos)]
    calc
      (m : ℝ) / 64 * (8 * defect (baseCoefficient m)) =
          (m : ℝ) * defect (baseCoefficient m) / 8 := by ring
      _ ≤ (m : ℝ) * (8 * (m : ℝ) ^ 15) / 8 := by
        gcongr
        exact defect_baseCoefficient_le hm
      _ = ((m : ℝ) ^ 8) ^ 2 := by ring
  have hexp_le :
      Real.exp (-((m : ℝ) ^ 8) ^ 2 /
          (8 * defect (baseCoefficient m))) ≤
        Real.exp (-(m : ℝ) / 64) := by
    apply Real.exp_le_exp.mpr
    calc
      -((m : ℝ) ^ 8) ^ 2 / (8 * defect (baseCoefficient m)) =
          -(((m : ℝ) ^ 8) ^ 2 / (8 * defect (baseCoefficient m))) := by ring
      _ ≤ -(m : ℝ) / 64 := by simpa only [neg_div] using neg_le_neg hratio
  calc
    constructionGrid m *
        (4 * Real.exp (-((m : ℝ) ^ 8) ^ 2 /
          (8 * defect (baseCoefficient m)))) ≤
        constructionGrid m * (4 * Real.exp (-(m : ℝ) / 64)) := by
      gcongr
    _ = 4 * (m : ℝ) ^ 54 * Real.exp (-(m : ℝ) / 64) := by
      rw [constructionGrid_cast]
      ring
    _ < 1 := hexp

/-- The Gaussian chirp and its finite chord correction provide arbitrarily
large examples with the concrete power bound used by `Asymptotics.lean`. -/
theorem hasPowerUpperExamples : HasPowerUpperExamples := by
  intro M
  have hev : ∀ᶠ m : ℕ in Filter.atTop,
      max 2 M ≤ m ∧
        4 * (m : ℝ) ^ 54 * Real.exp (-(m : ℝ) / 64) < 1 := by
    filter_upwards [Filter.eventually_ge_atTop (max 2 M),
      eventually_rounding_exponential_small] with m hm hsmall
    exact ⟨hm, hsmall⟩
  obtain ⟨m, hmM, hexp⟩ := hev.exists
  have hm : 2 ≤ m := (le_max_left 2 M).trans hmM
  have ha : ∀ i, ‖baseCoefficient m i‖ ≤ 1 :=
    norm_baseCoefficient_le_one hm
  have hm8 : (3 : ℝ) ≤ (m : ℝ) ^ 8 := by
    have hpow : 2 ^ 8 ≤ m ^ 8 := Nat.pow_le_pow_left hm 8
    exact_mod_cast (show 3 ≤ m ^ 8 by omega)
  refine ⟨m, hmM, ?_⟩
  change ∃ a : Fin (constructionDegree m + 1) → ℂ,
    IsUnimodular a ∧ ∀ theta : ℝ,
      ‖zerothValue a theta‖ ≤ (m : ℝ) ^ 9 + 2 * (m : ℝ) ^ 8
  by_cases hdef : defect (baseCoefficient m) = 0
  · obtain ⟨b, hb, hcorr⟩ :=
      exists_unit_rounding_circle_of_defect_eq_zero
        (baseCoefficient m) ha hdef
    refine ⟨b, hb, ?_⟩
    intro theta
    rw [← normalizedZerothValue_div_two_pi b theta]
    have hzero := hcorr (theta / (2 * Real.pi))
    have heq : normalizedZerothValue b (theta / (2 * Real.pi)) =
        normalizedZerothValue (baseCoefficient m) (theta / (2 * Real.pi)) := by
      exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
    rw [heq]
    have hbase := norm_baseCoefficient_value_lt hm (theta / (2 * Real.pi))
    linarith
  · obtain ⟨b, hb, hcorr⟩ := exists_unit_rounding_circle_defect
      (baseCoefficient m) ha (constructionGrid_pos hm)
      (R := (m : ℝ) ^ 8) (by positivity)
      (rounding_probability_small hm hdef hexp)
    refine ⟨b, hb, ?_⟩
    intro theta
    rw [← normalizedZerothValue_div_two_pi b theta]
    let phi : ℝ := theta / (2 * Real.pi)
    have hinterp := construction_interpolation_loss_lt_one hm
    have hcorrection :
        ‖normalizedZerothValue b phi -
          normalizedZerothValue (baseCoefficient m) phi‖ <
            1 + (m : ℝ) ^ 8 := by
      calc
        ‖normalizedZerothValue b phi -
            normalizedZerothValue (baseCoefficient m) phi‖ <
            4 * Real.pi * (constructionDegree m + 1) * constructionDegree m /
              constructionGrid m + (m : ℝ) ^ 8 := hcorr phi
        _ < 1 + (m : ℝ) ^ 8 := add_lt_add_left hinterp _
    have hbase := norm_baseCoefficient_value_lt hm phi
    change ‖normalizedZerothValue b phi‖ ≤ _
    apply le_of_lt
    calc
      ‖normalizedZerothValue b phi‖ ≤
          ‖normalizedZerothValue b phi -
            normalizedZerothValue (baseCoefficient m) phi‖ +
              ‖normalizedZerothValue (baseCoefficient m) phi‖ := by
        simpa [sub_add_cancel] using norm_add_le
          (normalizedZerothValue b phi -
            normalizedZerothValue (baseCoefficient m) phi)
          (normalizedZerothValue (baseCoefficient m) phi)
      _ < (1 + (m : ℝ) ^ 8) + ((m : ℝ) ^ 9 + 2) :=
        add_lt_add hcorrection hbase
      _ ≤ (m : ℝ) ^ 9 + 2 * (m : ℝ) ^ 8 := by linarith

end

end


/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos230.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 230.
https://www.erdosproblems.com/forum/thread/230

Informal authors:
- Jean-Pierre Kahane

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos230.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Erdős Problem 230

Erdős and Newman asked whether every polynomial

`P(z) = a₁ z + ⋯ + aₙ zⁿ`,  `‖aₖ‖ = 1`,

has circle maximum at least `(1 + c) * sqrt n` for some absolute `c > 0`.
The answer is negative.  The Gaussian-smoothed quadratic chirp constructed
in the supporting modules, followed by a finite Rademacher chord correction,
produces arbitrarily large unimodular polynomials with uniform upper norm
`(1 + o(1)) * sqrt n`.
-/



/-- The negative resolution of Erdős Problem 230. -/
theorem erdos_230 :
    ¬ (∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 2 ≤ n →
        ∀ a : Fin n → ℂ, IsUnimodular a →
          (1 + c) * Real.sqrt n ≤ circleMaximum a) :=
  not_erdos230Claim_of_ultraflat_upper
    (hasUltraflatUpper_of_angular
      (hasAngularUltraflatUpper_of_power_examples hasPowerUpperExamples))

end

#print axioms erdos_230
-- 'Erdos230.erdos_230' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos230
