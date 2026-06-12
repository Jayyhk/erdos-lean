/-

This is a Lean formalization of part of Erdős Problem 678.
https://www.erdosproblems.com/forum/thread/678

The actual problem was solved positively by: Stijn Cambie

[Ca24] S. Cambie, Resolution of an Erdős' problem on least common
multiples. arXiv:2410.09138 (2024).


Cambie's paper from the arxiv was auto-formalized by Aristotle (from
Harmonic).  It actually auto-formalized the entire paper, but below we
only include the portion necessary to solve the problem (Theorem 1).

This file includes a statement of the Prime Number Theorem as an
axiom, `pi_alt`.  It is lifted directly from the PrimeNumberTheoremAnd
project.

The final statements are from a mixture of sources.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/



/-
We have formalized the first main result of the paper "Resolution of an Erdős' problem on least common multiples".

**Main Theorem**: We proved `MainTheoremStatement` (Theorem 1 in the paper) assuming the `DensityHypothesis` (which follows from results on prime gaps, e.g., Baker-Harman-Pintz).

The formalization follows the structure of the paper, defining `M`, `m`, `good_x`, `good_y`, and using the Chinese Remainder Theorem and density arguments to construct the required integers. We handled the asymptotic inequalities and p-adic valuation arguments required for the proofs.
-/

import Mathlib

set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Erdos678

open scoped BigOperators
open scoped Nat
open scoped Classical
open scoped Pointwise


set_option maxHeartbeats 0

noncomputable section

open Real

open Filter

open Asymptotics

/-! ## PiAlt vendored proof of pi_alt -/

set_option maxHeartbeats 4000000

/-! ## --- vendored: Mathlib/Algebra/Notation/Support.lean --- -/

section Mathlib_Algebra_Notation_Support


namespace Function

variable {α : Type*} [Zero α]


end Function

end Mathlib_Algebra_Notation_Support

/-! ## --- vendored: SmoothExistence.lean --- -/

section SmoothExistence


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



end SmoothExistence

/-! ## --- vendored: Sobolev.lean --- -/

section Sobolev


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

lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := rfl

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
      (by simpa using (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl

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
  | succ n ih => simpa [iteratedDeriv_succ'] using ih (f := SchwartzMap.derivCLM ℝ ℂ f)

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
    convert CS.hasDerivAt_scale (g : CS 2 ℝ) R v |>.const_sub 1 using 1
    simp [h', CS.deriv_scale', show g.deriv.toFun = deriv g.toFun from rfl]
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
        rw [d1] ; convert (l5.add l7).deriv using 1 ; ring
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
      have evg' : g' =ᶠ[𝓝 0] 0 := by convert ← g.zero.deriv ; exact deriv_const' _
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert ← evg'.deriv ; exact deriv_const' _
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
      · simpa [h] using ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4

end Sobolev

/-! ## --- vendored: Fourier.lean --- -/

section Fourier


open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp)

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

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

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

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


end Fourier

/-! ## --- vendored: Defs.lean --- -/

section Defs


open ArithmeticFunction hiding log
open _root_.Nat hiding log
open Finset Topology
open BigOperators Filter Real Classical Asymptotics
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev


end Defs

/-! ## --- vendored: Mathlib/Analysis/SpecialFunctions/Log/Basic.lean --- -/

section Mathlib_Analysis_SpecialFunctions_Log_Basic


open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end Mathlib_Analysis_SpecialFunctions_Log_Basic

/-! ## --- vendored: Mathlib/Analysis/Asymptotics/Asymptotics.lean --- -/

section Mathlib_Analysis_Asymptotics_Asymptotics


open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics

end Mathlib_Analysis_Asymptotics_Asymptotics

/-! ## --- vendored: Wiener.lean --- -/

section Wiener


set_option lang.lemmaCmd true
set_option linter.style.header false

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
            simp [enorm_eq_nnnorm, ENNReal.tsum_mul_right]
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
    simpa using (integrable_inv_one_add_sq.comp_div hc).const_mul C
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
    · simpa [h] using continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
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

@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]

lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]

lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])

lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)

omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]

omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

end nabla

lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, Finset.sum_range_add, Finset.sum_range_one, add_comm 1] ; rfl

lemma Finset.sum_shift_front' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = (fun _ => u 0) + cumsum (shift u) := by
  ext n ; apply Finset.sum_shift_front

lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]

lemma Finset.sum_shift_back' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = cumsum u + u := by
  ext n ; apply Finset.sum_shift_back

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
  simpa using summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)

lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'

lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := Asymptotics.isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1

lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v :=
  ⟨fun h => Filter.EventuallyEq.summable huv.symm h, fun h => Filter.EventuallyEq.summable huv h⟩

lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, Asymptotics.isBigO_iff, norm_eq_abs, Pi.one_apply, one_mem,
    CStarRing.norm_of_mem_unitary, mul_one, eventually_atTop, ge_iff_le]
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
  have r2 : n - 1 + 1 = n := Nat.sub_add_cancel <| NeZero.one_le.trans hn.le
  simpa [r2] using hC (n - 1) r1

lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift] using Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
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
  ext x
  simp only [Function.comp_apply]
  congr
  field_simp
  simp

lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1; simp only [add_zero]; field_simp

lemma Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
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

lemma Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h

lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply ((log_isbigo_log_div hb).pow 2).trans ; simp_rw [add_comm a]
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
  have l3 := (log_add_div_isBigO_log 1 hb).pow 2
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by simpa using (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)

  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))

lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)

lemma Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)

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
    simp_rw [one_mul, Real.norm_eq_abs, abs_inv, abs_of_pos e1, abs_of_pos e2]
    exact inv_anti₀ e1 e3

  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    simpa [d, nabla] using (nnabla_mul_log_sq ((2 * π) ^ 2) hx)

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
    simpa [a] using IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).comp_tendsto tendsto_natCast_atTop_atTop using 1
    funext n
    simp [nnabla, a]

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
    have : 1 ≤ (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr h
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
    convert l4.pow 2 using 1 ; ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    convert (hasDerivAt_id' t).mul l2 using 1; field_simp; ring
  convert l1.inv e1 using 1; simp only [hh', pp, hh]; field_simp; ring

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
  · trans 0
    · linarith
    · positivity
  · rw [div_lt_iff₀ (by positivity)]
    convert_to 1 * 1 < 2 * π
    · simp
    · simp
    apply mul_lt_mul one_lt_two ?_ zero_lt_one zero_le_two
    trans 2
    · exact one_le_two
    · exact two_le_pi

lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring

lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by

  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa using hf' (n + 1)) (Finset.sum_nonneg' hf) ?_
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
    convert_to ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) ≤ _
    · congr ; ext i ; simp ; ring
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
    apply le_of_eq ; ring_nf

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
  | n + 2 => convert cancel_aux' hf hg hf' hg' (n + 2) using 1 ; simp [cumsum_succ] ; ring

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
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by simp [← diff_eq_compl_inter]
    simp [ae, this]

  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)

  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  convert _root_.add_le_add l1 l3

  have := @intervalIntegral.integral_comp_mul_add ℝ _ _ 1 (n + 1) 1 f one_ne_zero x₀
  rw [intervalIntegral.integral_add_adjacent_intervals]
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
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    convert this using 1 ; field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    convert (l1 x hx).const_mul (a * c / b) using 1
    simp only [g']
    field_simp
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

  apply cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n |>.trans
  gcongr ; simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]

  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  convert_to ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) ≤ _
  · apply Finset.sum_congr rfl (fun i hi => ?_)
    simp at hi
    have : i ≠ 0 := by omega
    simp [this]
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
    simpa using this.mono_set Ioi_subset_Ici_self

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
  convert mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
    (norm_nonneg (f i / i)) using 1
  · simp
  · change _ = _ * (W21.norm ψ * _)
    simp only [W21.norm, mul_inv_rev, one_div, Complex.norm_div, RCLike.norm_natCast]
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
  simpa only [← Summable.tsum_const_smul _ l5] using
    Summable.tsum_mono l1 (by simpa using l5.const_smul (W21.norm ψ)) l6

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
    have : ‖S x _‖ ≤ _ * M := @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply this.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp) (by positivity) W21.norm_nonneg).trans_lt
    have : 0 < 1 + M := by positivity
    convert (mul_lt_mul_iff_left₀ this).mpr hRψ using 1 ; field_simp

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

set_option maxHeartbeats 32000000 in
set_option synthInstance.maxHeartbeats 4000000 in
/-- Auxiliary bound for `toSchwartz`, factored out so its elaboration gets its own
heartbeat budget independent of the `SchwartzMap.mk` structure-literal elaboration. -/
private lemma toSchwartz_decay (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) (k n : ℕ) :
    ∃ C, ∀ x : ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  have hd : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) :=
    h1.iteratedFDeriv_right (mod_cast le_top)
  have l1 : Continuous (fun x : ℝ => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
    (continuous_norm.pow k).mul hd.continuous.norm
  have hi : HasCompactSupport (iteratedFDeriv ℝ n f) :=
    HasCompactSupport.iteratedFDeriv h2 n
  have hi_norm : HasCompactSupport (fun x : ℝ => ‖iteratedFDeriv ℝ n f x‖) :=
    HasCompactSupport.norm hi
  have l2 : HasCompactSupport (fun x : ℝ => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
    HasCompactSupport.mul_left hi_norm
  have hC := l1.bounded_above_of_compact_support l2
  obtain ⟨C, hC⟩ := hC
  refine ⟨C, fun x => ?_⟩
  have hx : (0 : ℝ) ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by positivity
  simpa [Real.norm_of_nonneg hx] using hC x

set_option maxHeartbeats 32000000 in
set_option synthInstance.maxHeartbeats 4000000 in
noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) :=
  ⟨f, h1, toSchwartz_decay f h1 h2⟩

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
    simpa using (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
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
    have r5 : 1 ≤ volume ((Function.support fun y ↦ ψ y) ∩ Ioi 0) := by convert volume.mono r4 ; norm_num
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

lemma le_floor_mul_iff (hb : 0 ≤ b) (hx : 0 < x) : n ≤ ⌊b * x⌋₊ ↔ n / x ≤ b := by
  rw [div_le_iff₀ hx, Nat.le_floor_iff] ; positivity

lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]

lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]

lemma mem_Icc_iff_div (hb : 0 ≤ b) (hx : 0 < x) : n ∈ Finset.Icc ⌈a * x⌉₊ ⌊b * x⌋₊ ↔ n / x ∈ Icc a b := by
  rw [Finset.mem_Icc, mem_Icc, ceil_mul_le_iff hx, le_floor_mul_iff hb hx]

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
  have hceilN : ⌈ε * N⌉₊ ≤ N := by
    simp only [Nat.ceil_le]
    exact mul_le_of_le_one_left N.cast_nonneg hε
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
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
  simpa [← S_sub_S h2.2] using l2.trans_lt h1

theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by

  convert_to Tendsto (S f 0) atTop (𝓝 A) ; · ext N ; simp [S, cumsum]
  apply (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto
  · have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    · intro ε hε
      simpa using WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
  · have : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (this.const_sub 1).const_mul A

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
    simp only [ofReal_inj, indicator_apply_eq_self, mem_setOf_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have l3 : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have l4 : cheby Λ := vonMangoldt_cheby
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm Λ σ') := by
    simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ').norm
  apply WienerIkeharaTheorem' l1 l5 l4 l3 l2

-- #print axioms WeakPNT

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
  letI : MeasurableSpace β := ⊤
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
          simpa [term, LSeries.term, hn] using
            (tendsto_const_nhds.div hden' hnC)
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
    haveI hx_ne' : NeZero (x : ℂ) := ⟨hx_ne⟩
    have hxpow_meas : AEMeasurable fun t : ℝ => ((x : ℂ) ^ (t * Complex.I)) := by
      have hcontℂ : Continuous fun z : ℂ => ((x : ℂ) ^ z) :=
        continuous_const_cpow (z := (x : ℂ))
      have hcont : Continuous fun t : ℝ => ((x : ℂ) ^ ((t : ℂ) * Complex.I)) :=
        hcontℂ.comp (by
          have h : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by
            simpa using (continuous_ofReal.mul continuous_const)
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
    simpa [Function.comp] using hcont.measurable

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
lemma Real.fourierIntegral_convolution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume) = 𝓕 f * 𝓕 g := by
  ext y
  simp only [Pi.mul_apply, FourierTransform.fourier, MeasureTheory.convolution,
    VectorFourier.fourierIntegral, ContinuousLinearMap.mul_apply']
  have h_int : Integrable (fun p : ℝ × ℝ ↦ 𝐞 (-(y * p.1)) • (f p.2 * g (p.1 - p.2))) := by
    simp only [Circle.smul_def, smul_eq_mul]
    refine (Integrable.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf hg).bdd_mul
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

lemma Real.fourierIntegral_conj_neg {f : ℝ → ℂ} (y : ℝ) :
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
  obtain ⟨phi_real, hphiSmooth, hphiCompact, hphiIcc, _, hphisupp⟩ :=
    smooth_urysohn_support_Ioo (a := 1/2) (b := 1) (c := 1) (d := 2) (by norm_num) (by norm_num)
  let phi : ℝ → ℂ := Complex.ofReal ∘ phi_real
  let phi_rev : ℝ → ℂ := fun x ↦ conj (phi (-x))
  let ψ_fun : ℝ → ℂ := convolution phi phi_rev (ContinuousLinearMap.mul ℂ ℂ) volume
  have hphiSmooth' : ContDiff ℝ ∞ phi := contDiff_ofReal.comp hphiSmooth
  have hphiCompact' : HasCompactSupport phi := hphiCompact.comp_left rfl
  have hphiRevSmooth : ContDiff ℝ ∞ phi_rev := Complex.conjCLE.contDiff.comp (hphiSmooth'.comp contDiff_neg)
  have hphiRevCompact : HasCompactSupport phi_rev := (hphiCompact'.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (by simp)
  have hphiInt : Integrable phi := hphiSmooth'.continuous.integrable_of_hasCompactSupport hphiCompact'
  have hphiRevInt : Integrable phi_rev := hphiRevSmooth.continuous.integrable_of_hasCompactSupport hphiRevCompact
  have hψSmooth : ContDiff ℝ ∞ ψ_fun := by
    convert hphiRevCompact.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      (hphiSmooth'.continuous.locallyIntegrable (μ := volume)) hphiRevSmooth
  have hψCompact : HasCompactSupport ψ_fun :=
    HasCompactSupport.convolution (ContinuousLinearMap.mul ℂ ℂ) hphiCompact' hphiRevCompact
  refine ⟨ψ_fun, hψSmooth, hψCompact, fun y ↦ ?_, ?_⟩
  · rw [Real.fourierIntegral_convolution hphiInt hphiRevInt, Pi.mul_apply,
      Real.fourierIntegral_conj_neg y, mul_comm, ← Complex.normSq_eq_conj_mul_self]
    exact ⟨Complex.normSq_nonneg _, rfl⟩
  · have hphi_nonneg : ∀ x, 0 ≤ phi_real x := fun x ↦ by
      have hx := hphiIcc x; by_cases h : x ∈ Set.Icc (1:ℝ) 1
      · simp only [Set.indicator_of_mem h, Pi.one_apply] at hx; linarith
      · simp only [Set.indicator_of_notMem h] at hx; exact hx
    have hvol_supp : (1 : ENNReal) ≤ volume (Function.support phi_real) := by
      have hsub : Set.Ico (1:ℝ) 2 ⊆ Function.support phi_real := fun x hx ↦
        hphisupp.symm ▸ Set.mem_Ioo.mpr ⟨by linarith [hx.1], hx.2⟩
      calc _ = volume (Set.Ico (1:ℝ) 2) := by simp [Real.volume_Ico]; norm_num
           _ ≤ _ := volume.mono hsub
    have hphiint_pos : 0 < ∫ x, phi_real x :=
      (integral_pos_iff_support_of_nonneg_ae (.of_forall hphi_nonneg)
        (hphiSmooth.continuous.integrable_of_hasCompactSupport hphiCompact)).2
        (lt_of_lt_of_le (by simp) hvol_supp)
    have hFphi0_re : 0 < (𝓕 phi 0).re := by
      simp only [phi, fourier_real_eq, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul,
        Function.comp_apply]
      have hint : Integrable (fun x => (phi_real x : ℂ)) :=
        (hphiSmooth.continuous.integrable_of_hasCompactSupport hphiCompact).ofReal
      calc (∫ x, (phi_real x : ℂ)).re = ∫ x, (phi_real x : ℂ).re := (integral_re hint).symm
        _ = ∫ x, phi_real x := by simp only [Complex.ofReal_re]
        _ > 0 := hphiint_pos
    rw [Real.fourierIntegral_convolution hphiInt hphiRevInt, Pi.mul_apply,
      Real.fourierIntegral_conj_neg 0, mul_comm, ← Complex.normSq_eq_conj_mul_self]
    exact Complex.normSq_pos.2 (fun h ↦ (ne_of_gt hFphi0_re) (by simp [h]))


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
    convert (l3.congr' haux.symm).add l2 using 1; ext σ'; simp [S, Pole]
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

end Wiener

/-! ## --- vendored: Consequences.lean --- -/

section Consequences



set_option lang.lemmaCmd true

open ArithmeticFunction hiding log
open _root_.Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

lemma Set.Ico_subset_Ico_of_Icc_subset_Icc {a b c d : ℝ} (h : Set.Icc a b ⊆ Set.Icc c d) :
    Set.Ico a b ⊆ Set.Ico c d := by
  intro z hz
  have hz' := Set.Ico_subset_Icc_self.trans h hz
  have hcd : c ≤ d := by
    contrapose! hz'
    rw [Set.Icc_eq_empty_of_lt hz']
    exact Set.notMem_empty _
  simp only [Set.mem_Ico, Set.mem_Icc] at *
  refine ⟨hz'.1, hz'.2.eq_or_lt.resolve_left ?_⟩
  rintro rfl
  apply hz.2.not_ge
  have := h <| Set.right_mem_Icc.mpr (hz.1.trans hz.2.le)
  simp only [Set.mem_Icc] at this
  exact this.2

lemma th43_b (x : ℝ) (hx : 2 ≤ x) :
    Nat.primeCounting ⌊x⌋₊ =
      θ x / log x + ∫ t in Set.Icc 2 x, θ t / (t * (Real.log t) ^ 2) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx


/-- If u ~ v and w-u = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (w - u) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [Asymptotics.IsEquivalent] at huv ⊢
  have hwv : (w - v) = (w - u) + (u - v) := by
    funext n; simp [Pi.sub_apply, Pi.add_apply]
  rw [hwv]
  exact hwu.add huv

/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [Asymptotics.IsEquivalent] at huv ⊢
  have hwv : (w - v) = (u - v) - (u - w) := by
    funext n; simp [Pi.sub_apply]
  rw [hwv]
  exact huv.sub hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Finset.Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Finset.Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ Finset.range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Finset.Iic N := Finset.mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Finset.Iic_erase]
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
      · convert Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets, ge_iff_le,
        Set.mem_setOf_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop, ge_iff_le]
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
    · convert isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this
theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine Asymptotics.IsEquivalent.add_isLittleO'' (show Asymptotics.IsEquivalent atTop ψ (fun x => x) from WeakPNT'') (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop, ge_iff_le]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · simpa only [mul_assoc] using isLittleO_sqrt_mul_log.const_mul_left 2

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
    simp only [Pi.sub_apply, norm_eq_abs, mul_assoc, eventually_atTop, ge_iff_le, norm_mul,
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
  · simp only [isLittleO_iff, norm_eq_abs, norm_mul, eventually_atTop, ge_iff_le,
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
        simp only
        rw [show (-1 / (x * log x ^ 2)) = (-1 / log x ^ 2) * (x⁻¹) by
          rw [mul_comm x]; field_simp]
        apply HasDerivAt.comp
          (h := fun t => log t) (h₂ := fun t => t⁻¹) (x := x)
        · simpa using HasDerivAt.inv (c := fun t : ℝ => t) (c' := 1) (x := log x)
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
    simp only [Metric.mem_ball, _root_.dist_zero_right, _root_.max_le_iff, norm_eq_abs] at hM hx
    refine ineq x (by linarith) |>.trans ?_
    specialize hM x hx.2
    rw [abs_of_nonneg (by
      apply _root_.div_nonneg
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
      convert hf.mul hf'
      ring
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

end Consequences



/-
Definitions of M and m as in the proof. M is the LCM of 1 to k. m is the product of prime powers p^a dividing M such that p <= sqrt(k).
-/
def M (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id

def m (k : ℕ) : ℕ :=
  let primes_sqrt := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p * p ≤ k)
  Finset.prod primes_sqrt (fun p => p ^ ((M k).factorization p))

/-
Claim: Let $p_1 < p_2 <  \ldots < p_r$ be primes and $w_1, w_2, \ldots, w_r$ be integers, such that the combinations $\sum_{i} c_i w_i$ over all possible combinations with $0 < c_i \le p_i $ lead to all residues modulo $P=p_1p_2\ldots p_r.$ Let $B_i \subset [p_i]$ be a set of size at least $(1-\eps)p_i$ for every $1 \le i \le r$.
    If $\eps(p_1+p_2+\ldots+p_r)< n \le p_1,$ among every $n$ consecutive integers there is at least one which equals $\sum_{i} c_i w_i$ modulo $P$ where $c_i \in B_i$ for every $1 \le i \le r$.
-/
theorem claim_approx (p : List ℕ) (w : List ℤ) (hp_prime : ∀ x ∈ p, x.Prime) (hp_sorted : p.Pairwise (· < ·))
    (h_cover : ∀ r : ℤ, ∃ c : List ℤ, c.length = p.length ∧
        (∀ i : ℕ, 0 < c.getD i 0 ∧ c.getD i 0 ≤ (p.getD i 0 : ℤ)) ∧
      (List.sum (List.zipWith (fun x y => x * y) c w)) ≡ r [ZMOD p.prod])
    (ε : ℝ) (B : List (Set ℤ)) (hB_subset : ∀ i : ℕ, B.getD i ∅ ⊆ Set.Icc 1 (p.getD i 0 : ℤ))
    (hB_size : ∀ i : ℕ, (B.getD i ∅).ncard ≥ (1 - ε) * (p.getD i 0 : ℝ))
    (n : ℕ) (hn : ε * (p.sum : ℝ) < n) (hn_le : n ≤ p.head!) :
    ∀ start : ℤ, ∃ z ∈ Set.Icc start (start + n - 1),
      ∃ c : List ℤ, c.length = p.length ∧ (∀ i : ℕ, c.getD i 0 ∈ B.getD i ∅) ∧
      z ≡ (List.sum (List.zipWith (fun x y => x * y) c w)) [ZMOD p.prod] := by
        contrapose! hB_size;
        revert hB_size hn hn_le hB_subset hB_size hp_prime hp_sorted h_cover;
        intro hprime hsorted hcover hB hε hn;
        cases p <;> simp_all +decide;
        intro x hx;
        use List.length ‹_› + 1;
        obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := hcover x;
        grind

/-
The hypothesis that for any $\epsilon > 0$, for sufficiently large $k$, there exist two distinct primes in $(k/2, (1+\epsilon)k/2)$ and three distinct primes in $((1-\epsilon)k, k)$.
-/
def DensityHypothesis : Prop :=
  ∀ ε > 0, ∃ K, ∀ k ≥ K,
    (∃ p1 p2 : ℕ, (k : ℝ) / 2 < p1 ∧ (p1 : ℝ) < (1 + ε) * k / 2 ∧ (k : ℝ) / 2 < p2 ∧ (p2 : ℝ) < (1 + ε) * k / 2 ∧ p1 ≠ p2 ∧ p1.Prime ∧ p2.Prime) ∧
    (∃ q1 q2 q3 : ℕ, (1 - ε) * k < q1 ∧ (q1 : ℝ) < k ∧ (1 - ε) * k < q2 ∧ (q2 : ℝ) < k ∧ (1 - ε) * k < q3 ∧ (q3 : ℝ) < k ∧
      q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3 ∧ q1.Prime ∧ q2.Prime ∧ q3.Prime)

/-
Algebraic identity: If the maximum of a function on a set is at least e, and at most one element exceeds e, then the sum minus the max equals the sum of mins minus e.
-/
lemma sum_sub_max_eq_sum_min_sub_e (S : Finset ℕ) (f : ℕ → ℕ) (e : ℕ)
  (h_max : S.sup f ≥ e)
  (h_unique : (S.filter (fun i => f i > e)).card ≤ 1) :
  ∑ i ∈ S, f i - S.sup f = (∑ i ∈ S, min (f i) e) - e := by
    by_cases h_empty : S = ∅ <;> simp_all +decide [ Finset.sup ];
    -- Let $i_0$ be the unique element in $S$ such that $f(i_0) > e$.
    by_cases h_exists : ∃ i0 ∈ S, e < f i0 ∧ ∀ i ∈ S, i ≠ i0 → f i ≤ e;
    · obtain ⟨ i0, hi0₁, hi0₂, hi0₃ ⟩ := h_exists;
      -- Since $f(i0) > e$, we have $\max_{i \in S} f(i) = f(i0)$.
      have h_max_eq : Finset.sup S f = f i0 := by
        exact le_antisymm ( Finset.sup_le fun i hi => if hi' : i = i0 then hi'.symm ▸ le_rfl else hi0₃ i hi hi' |> le_trans <| by linarith ) ( Finset.le_sup ( f := f ) hi0₁ );
      -- Since $f(i0) > e$, we can split the sum into two parts: the sum over $S \setminus \{i0\}$ and the term $f(i0)$.
      have h_split_sum : ∑ i ∈ S, f i = ∑ i ∈ S.erase i0, f i + f i0 := by
        rw [ Finset.sum_erase_add _ _ hi0₁ ]
      have h_split_min_sum : ∑ i ∈ S, min (f i) e = ∑ i ∈ S.erase i0, min (f i) e + min (f i0) e := by
        rw [ Finset.sum_erase_add _ _ hi0₁ ]
      simp_all +decide [ Finset.sup ];
      exact Finset.sum_congr rfl fun x hx => by rw [ min_eq_left ( hi0₃ x ( Finset.mem_of_mem_erase hx ) ( by aesop ) ) ] ;
    · -- If no such $i_0$ exists, then for all $i \in S$, we have $f(i) \leq e$.
      have h_le_e : ∀ i ∈ S, f i ≤ e := by
        contrapose! h_exists;
        exact Exists.elim h_exists fun i hi => ⟨ i, hi.1, hi.2, fun j hj hj' => not_lt.1 fun hj'' => h_unique.not_gt <| Finset.one_lt_card.2 ⟨ j, by aesop, i, by aesop ⟩ ⟩;
      rw [ le_antisymm h_max ];
      · rw [ Finset.sum_congr rfl fun x hx => min_eq_left <| by exact Finset.le_sup ( f := f ) hx ];
      · exact Finset.sup_le fun i hi => h_le_e i hi

/-
The p-adic valuation of the ratio of the product to the LCM is equal to the sum of truncated valuations minus e, provided the max valuation is at least e and at most one element exceeds e.
-/
lemma valuation_prod_div_lcm (S : Finset ℕ) (p : ℕ) (e : ℕ)
  (hp : p.Prime)
  (h_max : S.sup (padicValNat p) ≥ e)
  (h_unique : (S.filter (fun i => padicValNat p i > e)).card ≤ 1)
  (h_nonzero : ∀ i ∈ S, i ≠ 0) :
  padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) e) - e := by
    -- By definition of $p$-adic valuation, we know that $v_p(\prod_{i \in S} i) = \sum_{i \in S} v_p(i)$ and $v_p(\text{lcm} S) = \max_{i \in S} v_p(i)$.
    have h_val_prod : padicValNat p (Finset.prod S id) = ∑ i ∈ S, padicValNat p i := by
      have h_padic_prod : ∀ (l : List ℕ), (∀ i ∈ l, i ≠ 0) → padicValNat p (List.prod l) = List.sum (List.map (fun i => padicValNat p i) l) := by
        intros l hl_nonzero
        induction' l with i l ih;
        · simp [padicValNat_one_right];
        · by_cases hi : i = 0 <;> by_cases hl : l.prod = 0 <;> simp_all +decide [ padicValNat.mul ];
          norm_num [ ← ih ] at *;
          exact False.elim <| hl_nonzero.2 0 hl rfl;
      convert h_padic_prod ( S.toList ) _ ; aesop;
      · simp +decide [ Finset.sum_map_toList ];
      · aesop
    have h_val_lcm : padicValNat p (Finset.lcm S id) = Finset.sup S (padicValNat p) := by
      have h_val_lcm : ∀ {T : Finset ℕ}, (∀ i ∈ T, i ≠ 0) → padicValNat p (Finset.lcm T id) = Finset.sup T (padicValNat p) := by
        intros T hT_nonzero
        induction' T using Finset.induction with i T hiT ih;
        · aesop;
        · -- By definition of lcm, we have $\text{lcm}(i, \text{lcm}(T)) = \frac{i \cdot \text{lcm}(T)}{\gcd(i, \text{lcm}(T))}$.
          have h_lcm_def : padicValNat p (Nat.lcm i (Finset.lcm T id)) = max (padicValNat p i) (padicValNat p (Finset.lcm T id)) := by
            haveI := Fact.mk hp; rw [ ← Nat.factorization_def, ← Nat.factorization_def, Nat.factorization_lcm ] <;> simp_all +decide [ Nat.factorization_eq_zero_iff ] ;
            simp_all +decide [ Nat.factorization ];
          aesop;
      apply h_val_lcm; assumption;
    -- By the properties of p-adic valuations, we have $v_p(\prod_{i \in S} i / \text{lcm} S) = v_p(\prod_{i \in S} i) - v_p(\text{lcm} S)$.
    have h_val_ratio : padicValNat p ((∏ i ∈ S, i) / (Finset.lcm S id)) = (∑ i ∈ S, padicValNat p i) - (Finset.sup S (padicValNat p)) := by
      haveI := Fact.mk hp; rw [ ← h_val_prod, ← h_val_lcm, padicValNat.div_of_dvd ] ; aesop;
      exact Finset.lcm_dvd fun x hx => Finset.dvd_prod_of_mem _ hx;
    rw [ h_val_ratio, sum_sub_max_eq_sum_min_sub_e ] <;> aesop

/-
If p is a prime such that n < p^2, and S is a set of n consecutive integers containing a multiple of p, then the p-adic valuation of prod(S)/lcm(S) is the count of multiples of p in S minus 1.
-/
lemma valuation_large_p (S : Finset ℕ) (p : ℕ) (n : ℕ)
  (hp : p.Prime)
  (hS_card : S.card = n)
  (hS_consec : ∃ s, S = Finset.Icc s (s + n - 1))
  (h_len : n < p * p)
  (h_exists : ∃ z ∈ S, p ∣ z)
  (h_nonzero : ∀ z ∈ S, z ≠ 0) :
  padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (S.filter (p ∣ ·)).card - 1 := by
    -- Apply the lemma `valuation_prod_div_lcm` with $e = 1$.
    have h_apply_lemma : padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) 1) - 1 := by
      -- Apply the lemma `valuation_prod_div_lcm` with $e = 1$ and the conditions that the maximum $p$-adic valuation is at least 1 and at most one element has a $p$-adic valuation greater than 1.
      have h_apply_lemma : padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) 1) - 1 := by
        have h_max : S.sup (padicValNat p) ≥ 1 := by
          obtain ⟨ z, hz₁, hz₂ ⟩ := h_exists;
          refine' le_trans _ ( Finset.le_sup hz₁ );
          exact Nat.pos_of_ne_zero ( by intro t; simp_all +decide [ Nat.factorization_eq_zero_iff, hp.ne_one ] )
        have h_unique : (S.filter (fun i => padicValNat p i > 1)).card ≤ 1 := by
          -- If $p^2$ divides $i$, then $i \equiv 0 \pmod{p^2}$, and since $S$ contains $n$ consecutive integers, there can be at most one such $i$ in $S$.
          have h_unique : ∀ i j : ℕ, i ∈ S → j ∈ S → i % (p * p) = 0 → j % (p * p) = 0 → i = j := by
            intro i j hi hj hi' hj'; obtain ⟨ s, rfl ⟩ := hS_consec; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
            rw [ ← Nat.dvd_iff_mod_eq_zero ] at *;
            obtain ⟨ k, hk ⟩ := hi'; obtain ⟨ l, hl ⟩ := hj'; nlinarith [ show k = l by nlinarith [ Nat.sub_add_cancel ( show 1 ≤ s + n from by omega ) ] ] ;
          -- If $padicValNat p i > 1$, then $p^2$ divides $i$, and since $S$ contains $n$ consecutive integers, there can be at most one such $i$ in $S$.
          have h_div_p2 : ∀ i ∈ S, padicValNat p i > 1 → i % (p * p) = 0 := by
            intros i hi hpi
            have h_div_p2 : p ^ 2 ∣ i := by
              have h_div_p2 : p ^ (padicValNat p i) ∣ i := by
                convert Nat.ordProj_dvd i p using 1;
                rw [ Nat.factorization ] ; aesop;
              exact dvd_trans ( pow_dvd_pow _ hpi ) h_div_p2;
            simpa only [ sq ] using Nat.mod_eq_zero_of_dvd h_div_p2;
          exact Finset.card_le_one.mpr fun i hi j hj => h_unique i j ( Finset.filter_subset _ _ hi ) ( Finset.filter_subset _ _ hj ) ( h_div_p2 i ( Finset.filter_subset _ _ hi ) ( Finset.mem_filter.mp hi |>.2 ) ) ( h_div_p2 j ( Finset.filter_subset _ _ hj ) ( Finset.mem_filter.mp hj |>.2 ) )
        convert valuation_prod_div_lcm S p 1 hp h_max h_unique h_nonzero using 1;
      exact h_apply_lemma;
    rw [ h_apply_lemma, Finset.card_filter ];
    refine' congrArg₂ _ ( Finset.sum_congr rfl fun x hx => _ ) rfl;
    by_cases h : p ∣ x <;> simp_all +decide [ Nat.Prime.dvd_iff_one_le_factorization ];
    contrapose! h_nonzero; simp_all +decide [ Nat.factorization_eq_zero_iff ] ;
    grind

/-
The truncated p-adic valuation min(v_p(n), e) is periodic with period p^e for non-zero integers.
-/
lemma truncated_valuation_periodic (p e n k : ℕ) (hp : p.Prime) (h_mod : n ≡ k [MOD p ^ e])
  (hn : n ≠ 0) (hk : k ≠ 0) :
  min (padicValNat p n) e = min (padicValNat p k) e := by
    by_cases h : padicValNat p n ≥ e <;> by_cases h' : padicValNat p k ≥ e <;> simp_all +decide;
    · -- Since $n \equiv k \pmod{p^e}$, we have that $p^e \mid n$ if and only if $p^e \mid k$.
      have h_div : p ^ e ∣ n ↔ p ^ e ∣ k := by
        rw [ Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, h_mod ];
      contrapose! h_div;
      have h_div_n : p ^ e ∣ n :=
        dvd_trans (pow_dvd_pow p h) pow_padicValNat_dvd
      have h_div_k : ¬p ^ e ∣ k := by
        intro H; have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 H; simp_all +decide [ Nat.factorization ] ;
        replace := this p ; simp_all +decide [ Nat.primeFactors_pow ];
        linarith
      exact Or.inl ⟨h_div_n, h_div_k⟩;
    · -- Since $p^e \mid k$, we have $k \equiv 0 \pmod{p^e}$.
      have hk_mod : k ≡ 0 [MOD p ^ e] := by
        rw [ Nat.modEq_zero_iff_dvd ];
        have h_p_div_k : p ^ padicValNat p k ∣ k := by
          exact pow_padicValNat_dvd;
        exact dvd_trans ( pow_dvd_pow _ h' ) h_p_div_k;
      have h_div : p ^ e ∣ n := by
        exact Nat.dvd_of_mod_eq_zero ( h_mod.symm ▸ hk_mod );
      obtain ⟨ q, hq ⟩ := h_div;
      haveI := Fact.mk hp; rw [ hq, padicValNat.mul ] <;> aesop;
    · have h_div : p ^ (padicValNat p n) ∣ n ∧ ¬p ^ (padicValNat p n + 1) ∣ n := by
        haveI := Fact.mk hp; simp +decide [ Nat.ordProj_dvd, padicValNat_dvd_iff ] ;
        assumption;
      have h_div_k : p ^ (padicValNat p n) ∣ k ∧ ¬p ^ (padicValNat p n + 1) ∣ k := by
        have h_div_k : n ≡ k [MOD p ^ (padicValNat p n + 1)] := by
          exact h_mod.of_dvd <| pow_dvd_pow _ <| Nat.succ_le_of_lt h;
        exact ⟨ Nat.dvd_of_mod_eq_zero ( h_div_k.of_dvd ( pow_dvd_pow _ ( Nat.le_succ _ ) ) ▸ Nat.mod_eq_zero_of_dvd h_div.1 ), fun h => h_div.2 ( Nat.dvd_of_mod_eq_zero ( h_div_k.symm ▸ Nat.mod_eq_zero_of_dvd h ) ) ⟩;
      have h_val_eq : padicValNat p k = padicValNat p n := by
        rw [ ← Nat.factorization_def ];
        · exact le_antisymm ( Nat.le_of_not_lt fun h'' => h_div_k.2 <| Nat.dvd_trans ( pow_dvd_pow _ h'' ) <| Nat.ordProj_dvd _ _ ) ( Nat.le_of_not_lt fun h'' => by exact absurd ( Nat.dvd_trans ( pow_dvd_pow _ h'' ) h_div_k.1 ) <| Nat.pow_succ_factorization_not_dvd hk hp );
        · assumption;
      rw [h_val_eq]

/-
The sum of truncated p-adic valuations is invariant under shifting the interval by a multiple of the period p^e.
-/
lemma sum_truncated_valuation_eq (x y k p e : ℕ) (hp : p.Prime) (he : e > 0)
  (hx : x > 0) (hy : y > 0)
  (h_mod : x ≡ y + 1 [MOD p ^ e]) :
  ∑ i ∈ Finset.Icc (y + 1) (y + k), min (padicValNat p i) e =
  ∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e := by
    erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ];
    simp +arith +decide [ Nat.add_sub_add_left, Finset.sum_range_succ' ];
    rw [ Nat.sub_add_cancel ( by linarith ), Nat.add_sub_cancel_left ];
    refine' Finset.sum_congr rfl fun i hi => _;
    apply truncated_valuation_periodic;
    · assumption;
    · simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      ring;
    · positivity;
    · positivity

/-
The p-adic valuation of the LCM of 1 to k is the floor of log base p of k.
-/
lemma padicValNat_lcm_range (k p : ℕ) (hp : p.Prime) (hk : k ≥ 1) :
  padicValNat p (M k) = Nat.log p k := by
    revert k;
    intro k hk;
    -- The p-adic valuation of the least common multiple of a set of numbers is the maximum of the p-adic valuations of those numbers.
    have h_lcm_val : ∀ {S : Finset ℕ}, (∀ i ∈ S, i ≠ 0) → padicValNat p (Finset.lcm S id) = Finset.sup S (padicValNat p) := by
      intros S hS_nonzero
      induction' S using Finset.induction with i S hiS ih;
      · simp +decide [ Nat.lcm ];
      · -- By definition of lcm, we know that $v_p(\text{lcm}(i, S)) = \max(v_p(i), v_p(\text{lcm}(S)))$.
        have h_lcm_def : padicValNat p (Nat.lcm i (Finset.lcm S id)) = max (padicValNat p i) (padicValNat p (Finset.lcm S id)) := by
          haveI := Fact.mk hp;
          rw [ ← Nat.factorization_def, ← Nat.factorization_def, ← Nat.factorization_def ];
          · rw [ Nat.factorization_lcm ] <;> simp +decide [ hS_nonzero ];
            exact fun h => hS_nonzero 0 ( Finset.mem_insert_of_mem h ) rfl;
          · exact hp;
          · exact hp;
          · exact hp;
        aesop;
    -- Apply the lemma that the p-adic valuation of the lcm of a set of numbers is the maximum of the p-adic valuations of those numbers.
    have h_max_val : Finset.sup (Finset.Icc 1 k) (padicValNat p) = Nat.log p k := by
      refine' le_antisymm _ _;
      · simp +zetaDelta at *;
        intro b hb₁ hb₂; rw [ ← Nat.factorization_def ];
        · exact Nat.le_log_of_pow_le hp.one_lt ( Nat.le_trans ( Nat.le_of_dvd hb₁ ( Nat.ordProj_dvd _ _ ) ) hb₂ );
        · assumption;
      · refine' le_trans _ ( Finset.le_sup <| Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, Nat.pow_log_le_self _ <| by linarith ⟩ );
        haveI := Fact.mk hp; rw [ padicValNat.pow ] ; aesop;
        exact hp.ne_zero;
    exact h_max_val ▸ h_lcm_val fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ;

/-
Any interval of length at least m contains a multiple of m.
-/
lemma exists_multiple_of_len_ge (a L m : ℕ) (hm : m > 0) (hL : L ≥ m) :
  ∃ z ∈ Finset.Icc a (a + L - 1), m ∣ z := by
    norm_num +zetaDelta at *;
    -- Let $z = m \cdot \lceil a/m \rceil$. In integer arithmetic, we have $z = m \cdot ((a + m - 1) / m)$.
    use m * ((a + m - 1) / m);
    exact ⟨ ⟨ by linarith [ Nat.div_add_mod ( a + m - 1 ) m, Nat.mod_lt ( a + m - 1 ) hm, Nat.sub_add_cancel ( by linarith : 1 ≤ a + m ) ], Nat.le_sub_one_of_lt ( by linarith [ Nat.div_mul_le_self ( a + m - 1 ) m, Nat.sub_add_cancel ( by linarith : 1 ≤ a + m ) ] ) ⟩, dvd_mul_right _ _ ⟩

/-
An interval of length L <= m contains at most one multiple of m.
-/
lemma at_most_one_multiple_of_len_le (a L m : ℕ) (hm : m > 0) (hL : L ≤ m) :
  (Finset.filter (fun x => m ∣ x) (Finset.Icc a (a + L - 1))).card ≤ 1 := by
    by_contra h_contra;
    obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.mp ( not_le.mp h_contra );
    -- Since $x$ and $y$ are multiples of $m$ and lie in the interval $[a, a + L - 1]$, we have $|x - y| \geq m$.
    have h_diff : |(x : ℤ) - y| ≥ m := by
      exact Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr ( Nat.cast_injective.ne hxy ) ) ) ( by simpa using dvd_sub ( Int.natCast_dvd_natCast.mpr ( Finset.mem_filter.mp hx |>.2 ) ) ( Int.natCast_dvd_natCast.mpr ( Finset.mem_filter.mp hy |>.2 ) ) );
    simp +zetaDelta at *;
    cases abs_cases ( x - y : ℤ ) <;> omega

/-
For small primes p <= sqrt(k), the p-adic valuation of the LHS ratio is e + the p-adic valuation of the RHS ratio, where e = v_p(M).
-/
lemma valuation_small_p (k x y p : ℕ) (hp : p.Prime) (hk : k ≥ 2)
  (hx0 : x > 0) (hy0 : y > 0)
  (h_le_sqrt : p * p ≤ k)
  (hx_mod : x ≡ 1 [MOD p ^ (padicValNat p (M k))])
  (hy_mod : y ≡ 0 [MOD p ^ (padicValNat p (M k))]) :
  padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) =
  padicValNat p (M k) + padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) := by
    -- Let $e = v_p(M(k))$. By `padicValNat_lcm_range`, $e = \lfloor \log_p k \rfloor$.
    set e := padicValNat p (M k) with heq
    have he : e = Nat.log p k := by
      convert padicValNat_lcm_range k p hp ( by linarith ) using 1;
    -- By `valuation_prod_div_lcm`, we have $v_p(\text{LHS}) = \sum_{i=y}^{y+k} \min(v_p(i), e) - e$ and $v_p(\text{RHS}) = \sum_{i=x}^{x+k-1} \min(v_p(i), e) - e$.
    have h_lhs : padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) = (∑ i ∈ Finset.Icc y (y + k), min (padicValNat p i) e) - e := by
      convert valuation_prod_div_lcm _ _ _ hp _ _ _;
      · -- Since $y \equiv 0 \pmod{p^e}$, we have $v_p(y) \geq e$.
        have h_vp_y : padicValNat p y ≥ e := by
          have := Nat.dvd_of_mod_eq_zero hy_mod;
          obtain ⟨ c, rfl ⟩ := this;
          haveI := Fact.mk hp; rw [ padicValNat.mul ] <;> aesop;
        exact le_trans h_vp_y ( Finset.le_sup ( f := padicValNat p ) ( Finset.mem_Icc.mpr ⟨ le_rfl, by linarith ⟩ ) );
      · -- Since $p^{e+1} > k$, there can be at most one multiple of $p^{e+1}$ in the interval $[y, y+k]$.
        have h_unique_multiples : ∀ m1 m2 : ℕ, y ≤ m1 → m1 ≤ y + k → y ≤ m2 → m2 ≤ y + k → p ^ (e + 1) ∣ m1 → p ^ (e + 1) ∣ m2 → m1 = m2 := by
          intros m1 m2 hm1 hm1' hm2 hm2' hm1'' hm2''
          have h_diff : p ^ (e + 1) > k := by
            exact he.symm ▸ Nat.lt_pow_succ_log_self hp.one_lt _;
          obtain ⟨ a, ha ⟩ := hm1''; obtain ⟨ b, hb ⟩ := hm2''; nlinarith [ show a = b by nlinarith ] ;
        have h_unique_multiples : ∀ m ∈ Finset.Icc y (y + k), padicValNat p m > e → p ^ (e + 1) ∣ m := by
          intros m hm hpm;
          have h_div : p ^ (padicValNat p m) ∣ m := by
            convert Nat.ordProj_dvd m p using 1;
            rw [ Nat.factorization_def ] ; aesop;
          exact dvd_trans ( pow_dvd_pow _ hpm ) h_div;
        exact Finset.card_le_one.mpr fun m hm n hn => ‹∀ m1 m2 : ℕ, y ≤ m1 → m1 ≤ y + k → y ≤ m2 → m2 ≤ y + k → p ^ ( e + 1 ) ∣ m1 → p ^ ( e + 1 ) ∣ m2 → m1 = m2› m n ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) |>.2 ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ) ( h_unique_multiples m ( Finset.mem_filter.mp hm |>.1 ) ( Finset.mem_filter.mp hm |>.2 ) ) ( h_unique_multiples n ( Finset.mem_filter.mp hn |>.1 ) ( Finset.mem_filter.mp hn |>.2 ) );
      · exact fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ;
    have h_rhs : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = (∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e) - e := by
      apply valuation_prod_div_lcm;
      · assumption;
      · -- By `exists_multiple_of_len_ge`, there exists a multiple of $p^e$ in the interval $[x, x+k-1]$.
        obtain ⟨z, hz⟩ : ∃ z ∈ Finset.Icc x (x + k - 1), p ^ e ∣ z := by
          have h_exists_multiple : p ^ e ≤ k := by
            exact he.symm ▸ Nat.pow_log_le_self p ( by linarith );
          exact ⟨ p ^ e * ( ( x + k - 1 ) / p ^ e ), Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod ( x + k - 1 ) ( p ^ e ), Nat.mod_lt ( x + k - 1 ) ( pow_pos hp.pos e ), Nat.sub_add_cancel ( show 1 ≤ x + k from by linarith ) ], by linarith [ Nat.div_mul_le_self ( x + k - 1 ) ( p ^ e ), Nat.sub_add_cancel ( show 1 ≤ x + k from by linarith ) ] ⟩, by norm_num ⟩;
        -- Since $p^e \mid z$, we have $v_p(z) \geq e$.
        have hz_val : padicValNat p z ≥ e := by
          obtain ⟨ c, rfl ⟩ := hz.2;
          haveI := Fact.mk hp; rw [ padicValNat.mul ] <;> aesop;
        exact le_trans hz_val ( Finset.le_sup ( f := padicValNat p ) hz.1 );
      · have h_unique : ∀ i ∈ Finset.Icc x (x + k - 1), padicValNat p i > e → i % p ^ (e + 1) = 0 := by
          intros i hi hpi
          have h_div : p ^ (e + 1) ∣ i := by
            have h_div : p ^ (padicValNat p i) ∣ i := by
              convert Nat.ordProj_dvd i p using 1;
              rw [ Nat.factorization_def ] ; aesop;
            exact dvd_trans ( pow_dvd_pow _ hpi ) h_div;
          exact Nat.mod_eq_zero_of_dvd h_div;
        have h_unique : ∀ i j : ℕ, i ∈ Finset.Icc x (x + k - 1) → j ∈ Finset.Icc x (x + k - 1) → padicValNat p i > e → padicValNat p j > e → i = j := by
          intros i j hi hj hi_gt hj_gt
          have h_div : p ^ (e + 1) ∣ i ∧ p ^ (e + 1) ∣ j := by
            exact ⟨ Nat.dvd_of_mod_eq_zero ( h_unique i hi hi_gt ), Nat.dvd_of_mod_eq_zero ( h_unique j hj hj_gt ) ⟩;
          have h_diff : |(i : ℤ) - j| < p ^ (e + 1) := by
            have h_diff : |(i : ℤ) - j| ≤ k - 1 := by
              exact abs_sub_le_iff.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi, Finset.mem_Icc.mp hj, Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ], by linarith [ Finset.mem_Icc.mp hi, Finset.mem_Icc.mp hj, Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ] ⟩;
            have h_diff : k < p ^ (e + 1) := by
              rw [ he ];
              exact Nat.lt_pow_succ_log_self hp.one_lt _;
            grind;
          contrapose! h_diff;
          exact Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr <| mod_cast h_diff ) ) <| by simpa using dvd_sub ( Int.natCast_dvd_natCast.mpr h_div.1 ) ( Int.natCast_dvd_natCast.mpr h_div.2 ) ;
        exact Finset.card_le_one.mpr fun i hi j hj => h_unique i j ( Finset.filter_subset _ _ hi ) ( Finset.filter_subset _ _ hj ) ( Finset.mem_filter.mp hi |>.2 ) ( Finset.mem_filter.mp hj |>.2 );
      · exact fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ;
    -- By `sum_truncated_valuation_eq`, we have $\sum_{i=y}^{y+k} \min(v_p(i), e) = \sum_{i=x}^{x+k-1} \min(v_p(i), e)$.
    have h_sum_eq : ∑ i ∈ Finset.Icc y (y + k), min (padicValNat p i) e = ∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e + e := by
      have h_sum_eq : ∑ i ∈ Finset.Icc (y + 1) (y + k), min (padicValNat p i) e = ∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e := by
        apply sum_truncated_valuation_eq;
        · assumption;
        · exact he.symm ▸ Nat.log_pos hp.one_lt ( by nlinarith only [ hk, h_le_sqrt, hp.two_le ] );
        · linarith;
        · positivity;
        · simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      -- Since $y \equiv 0 \pmod{p^e}$, we have $v_p(y) \geq e$.
      have h_vp_y : padicValNat p y ≥ e := by
        rw [ ← Nat.factorization_def ];
        · exact Nat.le_of_not_lt fun h => absurd ( Nat.dvd_of_mod_eq_zero hy_mod ) ( by exact fun h' => absurd ( Nat.dvd_trans ( pow_dvd_pow _ h ) h' ) ( Nat.pow_succ_factorization_not_dvd hy0.ne' hp ) );
        · assumption;
      erw [ Finset.sum_Ico_eq_sum_range ] at *;
      simp_all +decide [ add_assoc, Finset.sum_range_succ' ];
      simp_all +decide [ add_comm, add_left_comm, add_assoc, Nat.add_sub_add_left ];
    simp_all +decide [ add_comm, mul_comm ];
    rw [ Nat.add_sub_of_le ];
    -- Since $p^e \le k$, there exists some $i \in [x, x+k-1]$ such that $p^e \mid i$.
    obtain ⟨i, hi⟩ : ∃ i ∈ Finset.Icc x (k + x - 1), p ^ e ∣ i := by
      have h_exists_i : p ^ e ≤ k := by
        exact Nat.pow_log_le_self p ( by linarith ) |> le_trans ( pow_le_pow_right₀ hp.one_lt.le ( by linarith ) );
      exact ⟨ p ^ e * ( ( x + p ^ e - 1 ) / p ^ e ), Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod ( x + p ^ e - 1 ) ( p ^ e ), Nat.mod_lt ( x + p ^ e - 1 ) ( pow_pos hp.pos e ), Nat.sub_add_cancel ( by linarith [ pow_pos hp.pos e ] : 1 ≤ x + p ^ e ) ], Nat.le_sub_one_of_lt ( by linarith [ Nat.div_mul_le_self ( x + p ^ e - 1 ) ( p ^ e ), Nat.sub_add_cancel ( by linarith [ pow_pos hp.pos e ] : 1 ≤ x + p ^ e ) ] ) ⟩, by norm_num ⟩;
    refine' le_trans _ ( Finset.single_le_sum ( fun a _ => Nat.zero_le ( min ( padicValNat p a ) ( padicValNat p ( M k ) ) ) ) hi.1 );
    haveI := Fact.mk hp; rw [ padicValNat_dvd_iff ] at hi; aesop;

/-
The number of multiples of p in the interval [a, b] (with a > 0) is floor(b/p) - floor((a-1)/p).
-/
lemma count_multiples_Icc (a b p : ℕ) (hp : p > 0) (ha : a > 0) :
  (Finset.filter (fun x => p ∣ x) (Finset.Icc a b)).card = b / p - (a - 1) / p := by
    rw [ show Finset.filter ( fun x => p ∣ x ) ( Finset.Icc a b ) = Finset.image ( fun x => p * x ) ( Finset.Icc ( ( a - 1 ) / p + 1 ) ( b / p ) ) from ?_, Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ hp.ne' hxy ];
    · simp +arith +decide;
    · ext;
      norm_num +zetaDelta at *;
      constructor;
      · rintro ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩;
        exact ⟨ ha₃.choose, ⟨ Nat.succ_le_of_lt ( Nat.div_lt_of_lt_mul <| by linarith [ Nat.sub_add_cancel ha, ha₃.choose_spec ] ), Nat.le_div_iff_mul_le hp |>.2 <| by linarith [ Nat.sub_add_cancel ha, ha₃.choose_spec ] ⟩, by linarith [ ha₃.choose_spec ] ⟩;
      · rintro ⟨ k, ⟨ hk₁, hk₂ ⟩, rfl ⟩;
        exact ⟨ ⟨ by nlinarith [ Nat.div_add_mod ( a - 1 ) p, Nat.mod_lt ( a - 1 ) hp, Nat.sub_add_cancel ha ], by nlinarith [ Nat.div_mul_le_self b p ] ⟩, dvd_mul_right _ _ ⟩

/-
For primes p with sqrt(k) < p <= k, the number of multiples of p in [x, x+k-1] is k/p, given the modular constraint on x.
-/
lemma count_multiples_large_p_RHS (k x p : ℕ) (hp : p.Prime) (hk : k ≥ 2) (hx0 : x > 0)
  (h_range : k.sqrt < p ∧ p ≤ k)
  (hx_p : 1 ≤ x % p ∧ x % p ≤ p - (k % p)) :
  (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card = k / p := by
    -- Let $x = qp + r$ with $1 \le r < p$. (Since $x \% p \ge 1$).
    obtain ⟨q, r, hx⟩ : ∃ q r : ℕ, 0 < r ∧ r < p ∧ x = q * p + r := by
      exact ⟨ x / p, x % p, hx_p.1, Nat.mod_lt _ hp.pos, by rw [ Nat.div_add_mod' ] ⟩;
    -- The number of multiples of $p$ in the interval $[x, x+k-1]$ is $\lfloor \frac{x+k-1}{p} \rfloor - \lfloor \frac{x-1}{p} \rfloor$.
    have h_count_multiples : (Finset.filter (fun x => p ∣ x) (Finset.Icc x (x + k - 1))).card = (x + k - 1) / p - (x - 1) / p := by
      convert count_multiples_Icc x ( x + k - 1 ) p hp.pos hx0 using 1;
    simp_all +decide [ Nat.add_div, Nat.add_mod, Nat.mod_eq_of_lt ];
    rw [ show q * p + r + k - 1 = ( q * p + r - 1 ) + k by omega, Nat.add_div ];
    · rw [ show q * p + r - 1 = p * q + ( r - 1 ) by rw [ Nat.sub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel hx.1 ] ] ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hx.2.1 ] ;
      rw [ if_neg ] <;> norm_num [ Nat.add_div, hp.pos ];
      rw [ Nat.mod_eq_of_lt ] <;> omega;
    · linarith

/-
For primes p with sqrt(k) < p <= k, the number of multiples of p in [y, y+k] is k/p + 1, given the modular constraint on y.
-/
lemma count_multiples_large_p_LHS (k y p : ℕ) (hp : p.Prime) (hk : k ≥ 2) (hy0 : y > 0)
  (h_range : k.sqrt < p ∧ p ≤ k)
  (hy_p : ∃ b, p - (k % p) ≤ b ∧ b ≤ p ∧ y ≡ b [MOD p]) :
  (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k))).card = k / p + 1 := by
    obtain ⟨ b, hb₁, hb₂, hb₃ ⟩ := hy_p;
    -- The number of multiples of p in the interval [y, y+k] is given by the formula ⌊(y+k)/p⌋ - ⌊(y-1)/p⌋.
    have h_count_formula : (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k))).card = (y + k) / p - (y - 1) / p := by
      convert count_multiples_Icc y ( y + k ) p hp.pos hy0 using 1;
    -- Since $y \equiv b \pmod p$, we have $y = qp + b$ for some integer $q$.
    obtain ⟨ q, hq ⟩ : ∃ q, y = q * p + b := by
      rw [ ← Nat.mod_add_div y p, hb₃ ];
      cases hb₂.eq_or_lt <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · exact ⟨ y / p - 1, by nlinarith [ Nat.sub_add_cancel ( show 1 ≤ y / p from Nat.div_pos ( Nat.le_of_dvd hy0 ( Nat.dvd_of_mod_eq_zero ( by simpa [ Nat.ModEq ] using hb₃ ) ) ) hp.pos ) ] ⟩;
      · exact ⟨ y / p, by ring ⟩;
    -- Substitute $y = qp + b$ into the formula.
    have h_subst : (y + k) / p = q + (k / p) + (if b + k % p ≥ p then 1 else 0) := by
      split_ifs <;> simp_all +decide [ Nat.add_div, hp.pos ];
      split_ifs <;> simp_all +decide [ Nat.div_eq_of_lt, Nat.mod_eq_of_lt ];
      · linarith [ Nat.mod_lt b hp.pos ];
      · linarith [ Nat.mod_lt b hp.pos, Nat.mod_lt k hp.pos ];
      · cases hb₂.eq_or_lt <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        linarith [ Nat.mod_lt k hp.pos ];
      · cases lt_or_eq_of_le hb₂ <;> simp_all +decide [ Nat.div_eq_of_lt ];
        · linarith [ Nat.mod_eq_of_lt ‹_› ];
        · ring;
    -- Since $y = qp + b$, we have $(y - 1) / p = q$.
    have h_div_y_minus_1 : (y - 1) / p = q := by
      rcases b with ( _ | b ) <;> simp_all +decide [ Nat.add_div ];
      · exact absurd hb₁ ( Nat.sub_ne_zero_of_lt ( Nat.mod_lt _ hp.pos ) );
      · nlinarith [ Nat.div_mul_le_self ( q * p + b ) p, Nat.div_add_mod ( q * p + b ) p, Nat.mod_lt ( q * p + b ) hp.pos ];
    grind

/-
If an interval has length at most p, then the p-adic valuation of the ratio of product to LCM is 0.
-/
lemma valuation_very_large_p (S : Finset ℕ) (p : ℕ) (n : ℕ)
  (hp : p.Prime)
  (hS_card : S.card = n)
  (hS_consec : ∃ s, S = Finset.Icc s (s + n - 1))
  (h_len : n ≤ p)
  (h_nonzero : ∀ z ∈ S, z ≠ 0) :
  padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = 0 := by
    -- Apply Theorem 3 with e = 0 to get that the valuation of the ratio is zero.
    have h_val_zero : padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) 0) - 0 := by
      apply valuation_prod_div_lcm S p 0 hp;
      · exact Nat.zero_le _;
      · have h_unique : (Finset.filter (fun x => p ∣ x) S).card ≤ 1 := by
          obtain ⟨ s, rfl ⟩ := hS_consec;
          exact at_most_one_multiple_of_len_le s n p hp.pos h_len;
        refine' le_trans ( Finset.card_mono _ ) h_unique;
        intro x hx; contrapose! hx; aesop;
      · assumption;
    aesop

/-
Extension of valuation_large_p to n <= p^2.
-/
lemma valuation_large_p_le (S : Finset ℕ) (p : ℕ) (n : ℕ)
  (hp : p.Prime)
  (hS_card : S.card = n)
  (hS_consec : ∃ s, S = Finset.Icc s (s + n - 1))
  (h_len : n ≤ p * p)
  (h_exists : ∃ z ∈ S, p ∣ z)
  (h_nonzero : ∀ z ∈ S, z ≠ 0) :
  padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (S.filter (p ∣ ·)).card - 1 := by
    have h_unique : (S.filter (fun i => padicValNat p i > 1)).card ≤ 1 := by
      have h_unique : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → ¬(p^2 ∣ z ∧ p^2 ∣ w) := by
        intros z hz w hw hne hdiv
        have h_diff : Int.natAbs (z - w) < p^2 := by
          rcases hS_consec with ⟨ s, rfl ⟩ ; simp_all +decide [ Finset.mem_Icc ];
          grind;
        exact h_diff.not_ge ( Nat.le_of_dvd ( Int.natAbs_pos.mpr ( sub_ne_zero_of_ne <| mod_cast hne ) ) <| by simpa [ ← Int.natCast_dvd_natCast ] using dvd_sub ( Int.natCast_dvd_natCast.mpr hdiv.1 ) ( Int.natCast_dvd_natCast.mpr hdiv.2 ) );
      have h_unique : ∀ z ∈ S, padicValNat p z > 1 → p^2 ∣ z := by
        intros z hz hpadic
        have h_div : p ^ (padicValNat p z) ∣ z := by
          exact pow_padicValNat_dvd
        generalize_proofs at *;
        exact dvd_trans ( pow_dvd_pow _ hpadic ) h_div;
      exact Finset.card_le_one.mpr fun x hx y hy => Classical.not_not.1 fun hxy => ‹∀ z ∈ S, ∀ w ∈ S, z ≠ w → ¬ ( p ^ 2 ∣ z ∧ p ^ 2 ∣ w ) › x ( Finset.filter_subset _ _ hx ) y ( Finset.filter_subset _ _ hy ) hxy ⟨ h_unique x ( Finset.filter_subset _ _ hx ) ( Finset.mem_filter.mp hx |>.2 ), h_unique y ( Finset.filter_subset _ _ hy ) ( Finset.mem_filter.mp hy |>.2 ) ⟩;
    have h_val_large_p : padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) 1) - 1 := by
      have h_val_large_p : ∀ {S : Finset ℕ} {p : ℕ}, p.Prime → (∀ i ∈ S, i ≠ 0) → (S.sup (padicValNat p)) ≥ 1 → (S.filter (fun i => padicValNat p i > 1)).card ≤ 1 → padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) 1) - 1 := by
        intros S p hp h_nonzero h_max h_unique; exact valuation_prod_div_lcm S p 1 hp h_max h_unique h_nonzero;
      apply h_val_large_p hp h_nonzero;
      · obtain ⟨ z, hz₁, hz₂ ⟩ := h_exists; exact le_trans ( Nat.pos_of_ne_zero ( by intro t; simp_all +decide [ Nat.factorization, hp.ne_one ] ) ) ( Finset.le_sup ( f := padicValNat p ) hz₁ ) ;
      · exact h_unique;
    rw [ h_val_large_p, Finset.card_filter ];
    refine' congr_arg₂ _ ( Finset.sum_congr rfl fun x hx => _ ) rfl;
    by_cases h : p ∣ x <;> simp +decide [ h, hp.dvd_iff_one_le_factorization ];
    exact Nat.pos_of_ne_zero ( by intro t; simp_all +decide [ Nat.factorization_eq_zero_iff, hp.ne_one, hp.ne_zero ] )

/-
Definition of good_x without referencing m k directly.
-/
def good_x_nom (k x m_val : ℕ) : Prop :=
  x > 0 ∧
  x % m_val = 1 ∧
  ∀ p, Nat.Prime p → Nat.sqrt k < p → p ≤ k → 1 ≤ x % p ∧ x % p ≤ p - (k % p)

/-
Definition of good_x using good_x_nom.
-/
def good_x (k x : ℕ) : Prop := good_x_nom k x (m k)

/-
Definition of good_y without referencing m k directly.
-/
def good_y_nom (k y m_val : ℕ) : Prop :=
  y > 0 ∧
  y % m_val = 0 ∧
  ∀ p, Nat.Prime p → Nat.sqrt k < p → p ≤ k → ∃ b, p - (k % p) ≤ b ∧ b ≤ p ∧ y % p = b % p

/-
Definition of good_y using good_y_nom.
-/
def good_y (k y : ℕ) : Prop := good_y_nom k y (m k)

/-
The ratio equality holds for all primes.
-/
theorem ratio_equality_final (k : ℕ) (x y : ℕ) (hk : k ≥ 2)
  (hx0 : x > 0) (hy0 : y > 0)
  (hx_good : good_x k x)
  (hy_good : good_y k y)
  : (∏ i ∈ Finset.Icc y (y + k), (i : ℚ)) / (Finset.Icc y (y + k)).lcm id =
    (M k : ℚ) * (∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (Finset.Icc x (x + k - 1)).lcm id := by
      -- Apply the equality of p-adic valuations for all primes p.
      have h_eq : ∀ p : ℕ, Nat.Prime p → padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) = padicValNat p (M k) + padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) := by
        -- Apply the appropriate lemma based on the value of p relative to k.
        intros p hp
        by_cases h_case : p ≤ Nat.sqrt k;
        · apply valuation_small_p;
          all_goals norm_cast;
          · nlinarith [ Nat.sqrt_le k ];
          · have := hx_good.2.1;
            rw [ ← this, Nat.ModEq, Nat.mod_mod_of_dvd ];
            refine' dvd_trans _ ( Finset.dvd_prod_of_mem _ <| show p ∈ Finset.filter ( fun p => Nat.Prime p ∧ p * p ≤ k ) ( Finset.Icc 1 k ) from Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, by nlinarith [ Nat.sqrt_le k ] ⟩, hp, by nlinarith [ Nat.sqrt_le k ] ⟩ );
            rw [ Nat.factorization ] ; aesop;
          · have h_mod_y : y ≡ 0 [MOD m k] := by
              exact hy_good.2.1;
            refine Nat.modEq_zero_iff_dvd.mpr <| dvd_trans ?_ <| Nat.dvd_of_mod_eq_zero h_mod_y;
            unfold m;
            rw [ Finset.prod_eq_prod_diff_singleton_mul <| show p ∈ Finset.filter ( fun p => Nat.Prime p ∧ p * p ≤ k ) ( Finset.Icc 1 k ) from ?_ ];
            · exact dvd_mul_of_dvd_right ( by rw [ Nat.factorization_def ] ; aesop ) _;
            · exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, by nlinarith [ Nat.sqrt_le k ] ⟩, hp, by nlinarith [ Nat.sqrt_le k ] ⟩;
        · by_cases h_case2 : p > k;
          · -- Since $p > k$, we have $v_p(M) = 0$.
            have h_vp_M_zero : padicValNat p (M k) = 0 := by
              have h_vp_M_zero : Nat.log p k = 0 := by
                exact Nat.log_of_lt h_case2;
              convert padicValNat_lcm_range k p hp ( by linarith ) using 1;
              exact h_vp_M_zero.symm;
            have h_val_zero : ∀ S : Finset ℕ, S.card = k + 1 → (∃ s, S = Finset.Icc s (s + k)) → (∀ z ∈ S, z ≠ 0) → padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = 0 := by
              intros S hS_card hS_consec h_nonzero
              apply valuation_very_large_p S p (k + 1) hp hS_card hS_consec (by
              linarith) h_nonzero;
            have h_val_zero_rhs : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0 := by
              have h_val_zero_rhs : ∀ S : Finset ℕ, S.card = k → (∃ s, S = Finset.Icc s (s + k - 1)) → (∀ z ∈ S, z ≠ 0) → padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = 0 := by
                intros S hS_card hS_consec hS_nonzero
                apply valuation_very_large_p S p k hp hS_card hS_consec (by
                linarith) hS_nonzero;
              apply h_val_zero_rhs;
              · simp +arith +decide [ Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ];
                omega;
              · use x;
              · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
            rw [ h_val_zero _ _ ⟨ y, rfl ⟩ fun z hz => by linarith [ Finset.mem_Icc.mp hz ], h_vp_M_zero, h_val_zero_rhs, zero_add ];
            simp +arith +decide;
            exact Nat.sub_eq_of_eq_add <| by ring;
          · -- Apply the appropriate lemma based on the value of p relative to k and the modular conditions.
            have h_val_large_p : padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) = (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k))).card - 1 := by
              apply valuation_large_p_le;
              exact hp;
              exact rfl;
              · exact ⟨ y, by simp +arith +decide ⟩;
              · norm_num;
                nlinarith only [ h_case, h_case2, Nat.lt_succ_sqrt k ];
              · exact ⟨ p * ( y / p + 1 ), Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod y p, Nat.mod_lt y hp.pos ], by linarith [ Nat.div_mul_le_self y p ] ⟩, by norm_num ⟩;
              · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
            have h_val_large_p_rhs : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card - 1 := by
              apply valuation_large_p_le;
              any_goals tauto;
              · simp +arith +decide [ Nat.sub_add_comm ( by linarith : 1 ≤ x + k ) ];
                exact ⟨ x, by rw [ show k + x - 1 + 1 - x = k by omega ] ; ring_nf ⟩;
              · norm_num;
                have h_sqrt_lt : k.sqrt < p := lt_of_not_ge h_case
                have h_k_lt_sq : k < p * p := by
                  have := Nat.lt_succ_sqrt k
                  nlinarith [Nat.sqrt_lt_self (by linarith : 1 < k), h_sqrt_lt]
                omega
              · have := hx_good.2.2 p hp ( by linarith ) ( by linarith );
                exact ⟨ x + ( p - x % p ), Finset.mem_Icc.mpr ⟨ by omega, by omega ⟩, by exact ⟨ ( x / p ) + 1, by linarith [ Nat.div_add_mod x p, Nat.sub_add_cancel ( show x % p ≤ p from Nat.le_of_lt ( Nat.mod_lt _ hp.pos ) ) ] ⟩ ⟩;
              · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
            have h_count_multiples : (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k))).card = (k / p) + 1 ∧ (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card = (k / p) := by
              apply And.intro;
              · apply count_multiples_large_p_LHS;
                · assumption;
                · grind;
                · assumption;
                · exact ⟨ not_le.mp h_case, not_lt.mp h_case2 ⟩;
                · have := hy_good.2.2 p hp ( by linarith ) ( by linarith ) ; aesop;
              · apply count_multiples_large_p_RHS k x p hp hk hx0 ⟨not_le.mp h_case, not_lt.mp h_case2⟩;
                have := hx_good.2.2 p hp ( not_le.mp h_case ) ( not_lt.mp h_case2 ) ; aesop;
            have h_padicValNat_M : padicValNat p (M k) = 1 := by
              have h_padicValNat_M : padicValNat p (M k) = Nat.log p k := by
                apply padicValNat_lcm_range k p hp (by linarith);
              rw [ h_padicValNat_M, Nat.log_eq_one_iff ];
              exact ⟨ by nlinarith only [ h_case, Nat.lt_succ_sqrt k ], hp.one_lt, le_of_not_gt h_case2 ⟩;
            simp_all +decide [ Nat.div_eq_of_lt ];
            rw [ add_tsub_cancel_of_le ( Nat.div_pos ( by linarith ) hp.pos ) ];
      -- By the properties of p-adic valuations, if the valuations of two numbers are equal for all primes p, then the numbers themselves are equal.
      have h_eq_rat : ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) = (M k) * ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) := by
        apply_mod_cast Nat.factorization_inj <;> norm_num;
        · exact ⟨ hy0.ne', Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) ( Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi ) ⟩;
        · exact ⟨ Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop, hx0.ne', Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) <| Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi ⟩;
        · ext p; by_cases hp : Nat.Prime p <;> simp_all +decide [ Nat.factorization ] ;
          haveI := Fact.mk hp; rw [ padicValNat.mul ] <;> simp_all +decide [ Nat.factorization ] ;
          · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
          · exact ⟨ hx0.ne', Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) ( Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi ) ⟩;
      rw [ Nat.div_eq_iff_eq_mul_left ] at h_eq_rat;
      · rw [ div_eq_div_iff ] <;> norm_cast <;> norm_num;
        · rw [ ← Nat.cast_prod, h_eq_rat ];
          norm_num [ mul_assoc, mul_comm, mul_left_comm ];
          rw_mod_cast [ Nat.mul_div_cancel' ];
          · exact Or.inl <| Or.inl <| by rw [ Nat.cast_prod ] ;
          · exact Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi;
        · linarith;
        · linarith;
      · exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) );
      · exact Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi

/-
The product of (x+i)/(y+i) for i from 0 to k-1 is at least (x/y)^k, given x < y.
-/
lemma product_ratio_lower_bound (x y k : ℕ) (hx : x > 0) (hy : y > 0) (hxy : x < y) :
  (∏ i ∈ Finset.range k, ((x + i : ℚ) / (y + i : ℚ))) ≥ ((x : ℚ) / y) ^ k := by
    -- Since $x < y$, for each $i$ in the range $0$ to $k-1$, we have $\frac{x+i}{y+i} \geq \frac{x}{y}$.
    have h_term_ge : ∀ i ∈ Finset.range k, (x + i : ℝ) / (y + i) ≥ x / y := by
      exact fun i hi => by rw [ ge_iff_le, div_le_div_iff₀ ] <;> norm_cast <;> nlinarith;
    convert Finset.prod_le_prod ?_ h_term_ge using 1 <;> norm_num [ Finset.prod_mul_distrib ];
    · rw [ le_div_iff₀ ( Finset.prod_pos fun _ _ => by positivity ) ] ; ring_nf; norm_num;
      field_simp;
      norm_cast;
    · exact fun _ _ => by positivity;

/-
The ratio of the LCMs is at least M/(y+k) * (x/y)^k.
-/
lemma lcm_ratio_bound (k : ℕ) (x y : ℕ) (hk : k ≥ 2)
  (hx0 : x > 0) (hy0 : y > 0) (hxy : x < y)
  (hx_good : good_x k x)
  (hy_good : good_y k y) :
  (Finset.Icc x (x + k - 1)).lcm id / (Finset.Icc y (y + k)).lcm id ≥
  (M k : ℚ) / (y + k) * ((x : ℚ) / y) ^ k := by
    field_simp;
    -- By the ratio equality, we have:
    have h_ratio_eq : ((M k : ℚ) * (∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (Finset.Icc x (x + k - 1)).lcm id) =
                       ((∏ i ∈ Finset.Icc y (y + k), (i : ℚ)) / (Finset.Icc y (y + k)).lcm id) := by
                         exact Eq.symm (ratio_equality_final k x y hk hx0 hy0 hx_good hy_good);
    -- Using `product_ratio_lower_bound`, the product is $\ge (x/y)^k$.
    have h_prod_ratio_lower_bound : (∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (∏ i ∈ Finset.Icc y (y + k), (i : ℚ)) ≥ ((x : ℚ) / y) ^ k / (↑y + ↑k) := by
      have h_ratio_prod : (∏ i ∈ Finset.range k, ((x + i : ℚ) / (y + i : ℚ))) ≥ ((x : ℚ) / y) ^ k := by
        exact product_ratio_lower_bound x y k hx0 hy0 hxy;
      have h_eqs : (∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) = (∏ i ∈ Finset.range k, (x + i : ℚ)) ∧ (∏ i ∈ Finset.Icc y (y + k), (i : ℚ)) = (∏ i ∈ Finset.range (k + 1), (y + i : ℚ)) := by
        have hk1 : 1 ≤ k := by linarith
        refine ⟨?_, ?_⟩
        · have heq : Finset.Icc x (x + k - 1) = Finset.Ico x (x + k) := by
            rw [← Finset.Ico_succ_right_eq_Icc]
            simp only [Order.succ_eq_add_one]
            congr 1; omega
          rw [heq, Finset.prod_Ico_eq_prod_range]
          have : x + k - x = k := by omega
          rw [this]
          apply Finset.prod_congr rfl
          intros i _; push_cast; ring
        · have heq : Finset.Icc y (y + k) = Finset.Ico y (y + k + 1) := by
            rw [← Finset.Ico_succ_right_eq_Icc]
            simp only [Order.succ_eq_add_one]
          rw [heq, Finset.prod_Ico_eq_prod_range]
          have : y + k + 1 - y = k + 1 := by omega
          rw [this]
          apply Finset.prod_congr rfl
          intros i _; push_cast; ring
      obtain ⟨he1, he2⟩ := h_eqs
      rw [he1, he2, Finset.prod_range_succ, div_mul_eq_div_div]
      have hprod_eq : (∏ i ∈ Finset.range k, ((x : ℚ) + i) / ((y : ℚ) + i)) =
          (∏ i ∈ Finset.range k, ((x : ℚ) + i)) / (∏ i ∈ Finset.range k, ((y : ℚ) + i)) := by
        rw [Finset.prod_div_distrib]
      rw [hprod_eq] at h_ratio_prod
      gcongr
    rw [ ge_iff_le, div_le_iff₀ ] at * <;> try positivity;
    rw [ div_eq_iff ] at h_ratio_eq;
    · convert mul_le_mul_of_nonneg_left h_prod_ratio_lower_bound ( show ( 0 : ℚ ) ≤ ↑ ( M k ) by positivity ) using 1 ; ring_nf;
      simp_all +decide [ add_comm, mul_assoc, mul_comm, mul_left_comm ];
      by_cases h : ∏ x ∈ Finset.Icc y ( k + y ), ( x : ℚ ) = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      exact absurd h_prod_ratio_lower_bound ( not_le_of_gt ( by positivity ) );
    · aesop

/-
If x and y satisfy the given bounds, then the quantity is greater than C.
-/
lemma final_inequality_sufficient (C : ℝ) (hC : C ≥ 1) :
  ∃ K, ∀ k ≥ K, ∀ x y : ℕ,
    x > 0 → y > 0 →
    y < (M k : ℝ) / (4 * C) - k →
    y > (M k : ℝ) / (5 * C) * (1 + 1 / k) →
    (y : ℝ) - x < (M k : ℝ) / (5 * C * k) →
    (M k : ℝ) / (y + k) * ((x : ℝ) / y) ^ k > C := by
      field_simp;
      refine' ⟨ 1, fun k hk x y hx hy h₁ h₂ h₃ => _ ⟩;
      -- We know that $(\frac{x}{y})^k > (\frac{k}{k+1})^k = (1 + \frac{1}{k})^{-k}$.
      have h_exp : ((x : ℝ) / y) ^ k > (1 + 1 / k : ℝ)⁻¹ ^ k := by
        gcongr;
        field_simp at *;
        nlinarith [ ( by norm_cast : ( 1 : ℝ ) ≤ k ), mul_le_mul_of_nonneg_left ( show ( C : ℝ ) ≥ 1 by linarith ) ( show ( 0 : ℝ ) ≤ k by positivity ) ];
      -- Since $(1 + 1/k)^k < 3$ for all $k$, we have $(1 + 1/k)^{-k} > 1/3$.
      have h_inv_exp : (1 + 1 / k : ℝ)⁻¹ ^ k > 1 / 3 := by
        have h_inv_exp : (1 + 1 / k : ℝ) ^ k < 3 := by
          -- We know that $(1 + \frac{1}{k})^k < e$ for all $k$.
          have h_exp_bound : (1 + 1 / k : ℝ) ^ k < Real.exp 1 := by
            rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ];
            exact Real.exp_lt_exp.mpr ( by nlinarith [ one_div_mul_cancel ( by positivity : ( k : ℝ ) ≠ 0 ), Real.log_lt_sub_one_of_pos ( by positivity : 0 < ( 1 + 1 / ( k : ℝ ) ) ) ( by aesop ), ( by norm_cast : ( 1 :ℝ ) ≤ k ) ] );
          exact h_exp_bound.trans_le <| Real.exp_one_lt_d9.le.trans <| by norm_num;
        simpa using inv_strictAnti₀ ( by positivity ) h_inv_exp;
      rw [ lt_div_iff₀ ] at * <;> nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ k ) ]

/-
The number of integers in an interval of length n <= p having residues in Bad is at most |Bad|.
-/
lemma count_bad_residues_interval (p : ℕ) (hp : p > 0) (Bad : Finset ℕ) (n : ℕ) (start : ℤ)
  (hn : n ≤ p)
  (hBad : ∀ x ∈ Bad, x < p) :
  ((Finset.Icc start (start + n - 1)).filter (fun z => (z % (p : ℤ)).toNat ∈ Bad)).card ≤ Bad.card := by
    have h_inj : ∀ z ∈ Finset.Icc start (start + n - 1), ∀ w ∈ Finset.Icc start (start + n - 1), z % p = w % p → z = w := by
      intros z hz w hw h_mod;
      norm_num +zetaDelta at *;
      exact Int.modEq_iff_dvd.mp h_mod.symm |> fun ⟨ k, hk ⟩ => by nlinarith [ show k = 0 by nlinarith ] ;
    have h_card : Finset.card (Finset.image (fun z => Int.toNat (z % p)) (Finset.filter (fun z => Int.toNat (z % p) ∈ Bad) (Finset.Icc start (start + n - 1)))) ≤ Finset.card Bad := by
      exact Finset.card_le_card ( Finset.image_subset_iff.mpr fun x hx => by aesop );
    rwa [ Finset.card_image_of_injOn fun x hx y hy hxy => h_inj x ( Finset.mem_filter.mp hx |>.1 ) y ( Finset.mem_filter.mp hy |>.1 ) <| by linarith [ Int.toNat_of_nonneg ( Int.emod_nonneg x <| Nat.cast_ne_zero.mpr hp.ne' ), Int.toNat_of_nonneg ( Int.emod_nonneg y <| Nat.cast_ne_zero.mpr hp.ne' ) ] ] at h_card

/-
The number of residues modulo p not covered by B is at most epsilon * p.
-/
lemma card_bad_residues (p : ℕ) (hp : p > 0) (B : Set ℤ) (ε : ℝ)
  (hB_subset : B ⊆ Set.Icc 1 p)
  (hB_size : B.ncard ≥ (1 - ε) * p) :
  ((Finset.range p).filter (fun r => ∀ b ∈ B, Int.toNat (b % (p : ℤ)) ≠ r)).card ≤ ε * p := by
    by_cases hB_finite : B.Finite;
    · have hB_image : (Finset.image (fun b : ℤ => (b % p).toNat) (hB_finite.toFinset)).card = B.ncard := by
        have h_inj : ∀ x y : ℤ, x ∈ B → y ∈ B → (x % p).toNat = (y % p).toNat → x = y := by
          intros x y hx hy hxy
          have h_eq_mod : x % p = y % p := by
            linarith [ Int.toNat_of_nonneg ( Int.emod_nonneg x ( by positivity : ( p : ℤ ) ≠ 0 ) ), Int.toNat_of_nonneg ( Int.emod_nonneg y ( by positivity : ( p : ℤ ) ≠ 0 ) ) ];
          have := hB_subset hx; have := hB_subset hy; simp_all ( config := { decide := Bool.true } ) [ Int.emod_eq_of_lt ] ;
          by_contra hxy_ne;
          exact hxy_ne ( by obtain ⟨ k, hk ⟩ := Int.modEq_iff_dvd.mp h_eq_mod.symm; nlinarith [ show k = 0 by nlinarith ] );
        rw [ Finset.card_image_of_injOn fun x hx y hy hxy => h_inj x y ( by simpa using hx ) ( by simpa using hy ) hxy, ← Set.ncard_coe_finset ] ; aesop;
      have hB_complement : (Finset.filter (fun r => ∀ b ∈ hB_finite.toFinset, (b % p).toNat ≠ r) (Finset.range p)).card = p - (Finset.image (fun b : ℤ => (b % p).toNat) (hB_finite.toFinset)).card := by
        rw [ show ( Finset.filter ( fun r => ∀ b ∈ hB_finite.toFinset, ( b % p : ℤ ).toNat ≠ r ) ( Finset.range p ) ) = Finset.range p \ Finset.image ( fun b => ( b % p : ℤ ).toNat ) hB_finite.toFinset from ?_ ];
        · rw [ Finset.card_sdiff ] ; norm_num;
          rw [ Finset.inter_eq_left.mpr ];
          exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_range.mpr <| by linarith [ Int.emod_lt_of_pos x ( by positivity : 0 < ( p : ℤ ) ), Int.toNat_of_nonneg <| Int.emod_nonneg x <| show ( p : ℤ ) ≠ 0 by positivity ] ;
        · ext; aesop;
      simp_all +decide [ Set.subset_def ];
      rw [ Nat.cast_sub ];
      · linarith;
      · have hB_image : (Finset.image (fun b : ℤ => (b % p).toNat) (hB_finite.toFinset)).card ≤ p := by
          exact le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun x hx => Finset.mem_range.mpr <| Int.toNat_lt ( Int.emod_nonneg _ <| by positivity ) |>.2 <| Int.emod_lt_of_pos _ <| by positivity ) ( by simp );
        linarith;
    · exact False.elim <| hB_finite <| Set.Finite.subset ( Set.finite_Icc 1 ( p : ℤ ) ) hB_subset

/-
The number of integers in an interval of length n <= p that do not match any residue in B is at most epsilon * p.
-/
lemma bad_count_bound (p : ℕ) (hp : p > 0) (B : Set ℤ) (ε : ℝ)
  (hB_subset : B ⊆ Set.Icc 1 (p : ℤ))
  (hB_size : B.ncard ≥ (1 - ε) * p)
  (n : ℕ) (start : ℤ) (hn : n ≤ p) :
  ((Finset.Icc start (start + n - 1)).filter (fun z => ∀ b ∈ B, ¬(z ≡ b [ZMOD p]))).card ≤ ε * p := by
    have := @card_bad_residues p hp B ε hB_subset;
    -- Apply the lemma about the count of bad residues in an interval.
    have h_card_bad_residues_interval : ((Finset.Icc start (start + n - 1)).filter (fun z => (z % (p : ℤ)).toNat ∈ ((Finset.range p).filter (fun r => ∀ b ∈ B, Int.toNat (b % (p : ℤ)) ≠ r)))).card ≤ ((Finset.range p).filter (fun r => ∀ b ∈ B, Int.toNat (b % (p : ℤ)) ≠ r)).card := by
      convert count_bad_residues_interval p hp _ n start hn _ using 1;
      aesop;
    refine' le_trans _ ( this hB_size );
    refine' mod_cast le_trans _ h_card_bad_residues_interval;
    refine Finset.card_mono ?_;
    intro z hz; simp_all +decide [ Int.ModEq, Int.emod_nonneg _ ( by positivity : ( p : ℤ ) ≠ 0 ) ] ;
    exact ⟨ Int.emod_lt_of_pos _ ( by positivity ), fun b hb => fun h => hz.2 b hb <| by linarith [ Int.toNat_of_nonneg ( Int.emod_nonneg z ( by positivity : ( p : ℤ ) ≠ 0 ) ), Int.toNat_of_nonneg ( Int.emod_nonneg b ( by positivity : ( p : ℤ ) ≠ 0 ) ) ] ⟩

/-
For two primes p1, p2, and large sets B1, B2, any interval of length n (sufficiently large) contains a number with residues in B1, B2.
-/
lemma claim_approx_2 (p1 p2 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_ne : p1 ≠ p2)
  (ε : ℝ) (B1 B2 : Set ℤ)
  (hB1_subset : B1 ⊆ Set.Icc 1 p1) (hB2_subset : B2 ⊆ Set.Icc 1 p2)
  (hB1_size : B1.ncard ≥ (1 - ε) * p1) (hB2_size : B2.ncard ≥ (1 - ε) * p2)
  (n : ℕ) (hn : ε * (p1 + p2) < n) (hn_le1 : n ≤ p1) (hn_le2 : n ≤ p2) :
  ∀ start : ℤ, ∃ z ∈ Set.Icc start (start + n - 1),
    ∃ c1 ∈ B1, ∃ c2 ∈ B2,
    z ≡ c1 [ZMOD p1] ∧ z ≡ c2 [ZMOD p2] := by
      intro start;
      -- Let $Bad_1 = \{ z \in I \mid \forall b \in B_1, z \not\equiv b \pmod {p_1} \}$.
      set Bad1 := (Finset.Icc start (start + n - 1)).filter (fun z => ∀ b ∈ B1, ¬(z ≡ b [ZMOD p1])) with hBad1_def
      -- Let $Bad_2 = \{ z \in I \mid \forall b \in B_2, z \not\equiv b \pmod {p_2} \}$.
      set Bad2 := (Finset.Icc start (start + n - 1)).filter (fun z => ∀ b ∈ B2, ¬(z ≡ b [ZMOD p2])) with hBad2_def;
      -- By `bad_count_bound`, $|Bad_1| \le \epsilon p_1$ and $|Bad_2| \le \epsilon p_2$.
      have hBad1_card : Bad1.card ≤ ε * p1 := by
        convert bad_count_bound p1 hp1.pos B1 ε hB1_subset hB1_size n start hn_le1 using 1
      have hBad2_card : Bad2.card ≤ ε * p2 := by
        convert bad_count_bound p2 ( Nat.cast_pos.mpr hp2.pos ) B2 ε hB2_subset hB2_size n start ( mod_cast hn_le2 ) using 1;
      -- The set of $z \in I$ that fail the condition for at least one prime is $Bad_1 \cup Bad_2$.
      have h_union_card : (Bad1 ∪ Bad2).card < n := by
        exact_mod_cast ( by linarith [ show ( Finset.card ( Bad1 ∪ Bad2 ) : ℝ ) ≤ Finset.card Bad1 + Finset.card Bad2 by exact_mod_cast Finset.card_union_le _ _ ] : ( Finset.card ( Bad1 ∪ Bad2 ) : ℝ ) < n );
      -- Since $|I| = n$, there exists $z \in I \setminus (Bad_1 \cup Bad_2)$.
      obtain ⟨z, hz⟩ : ∃ z ∈ Finset.Icc start (start + n - 1), z ∉ Bad1 ∪ Bad2 := by
        exact Finset.not_subset.mp fun h => h_union_card.not_ge <| by simpa [ Finset.card_image_of_injective, Function.Injective ] using Finset.card_le_card h;
      simp_all +decide [ Finset.mem_union, Finset.mem_filter ];
      exact ⟨ z, hz.1, by obtain ⟨ x, hx1, hx2 ⟩ := hz.2.1 hz.1.1 hz.1.2; obtain ⟨ y, hy1, hy2 ⟩ := hz.2.2 hz.1.1 hz.1.2; exact ⟨ x, hx1, y, hy1, hx2, hy2 ⟩ ⟩

/-
M_prime is M divided by p1*p2.
-/
def M_prime (k p1 p2 : ℕ) : ℕ := (M k) / (p1 * p2)

/-
p1*p2 divides M k if p1, p2 are distinct primes <= k.
-/
lemma M_prime_dvd (k p1 p2 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_ne : p1 ≠ p2)
  (h_le1 : p1 ≤ k) (h_le2 : p2 ≤ k) :
  p1 * p2 ∣ M k := by
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by simpa [ * ] using Nat.coprime_primes hp1 hp2 ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hp1.pos, h_le1 ⟩ ) ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hp2.pos, h_le2 ⟩ ) )

/-
M_prime is coprime to p1 and p2.
-/
lemma M_prime_coprime (k p1 p2 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_ne : p1 ≠ p2)
  (h_range1 : k / 2 < p1 ∧ p1 ≤ k) (h_range2 : k / 2 < p2 ∧ p2 ≤ k)
  (hk : k ≥ 4) :
  Nat.Coprime (M_prime k p1 p2) p1 ∧ Nat.Coprime (M_prime k p1 p2) p2 := by
    unfold M_prime;
    -- Since $p1$ and $p2$ are distinct primes greater than $k/2$, their squares are greater than $k$, so $p1^2$ and $p2^2$ cannot divide $M k$.
    have h_not_div_p1 : ¬(p1^2 ∣ M k) := by
      have h_not_div_p1 : Nat.factorization (M k) p1 = 1 := by
        have h_val_p1 : Nat.factorization (M k) p1 = Nat.log p1 k := by
          have := @padicValNat_lcm_range k p1 hp1;
          rw [ ← this ( by linarith ), Nat.factorization_def ] ; aesop;
        rw [ h_val_p1, Nat.log_eq_one_iff ];
        exact ⟨ by nlinarith only [ hk, h_range1, Nat.div_add_mod k 2, Nat.mod_lt k two_pos ], hp1.one_lt, h_range1.2 ⟩;
      rw [ ← Nat.factorization_le_iff_dvd ] <;> aesop
    have h_not_div_p2 : ¬(p2^2 ∣ M k) := by
      have h_log_p2 : Nat.log p2 k < 2 := by
        exact Nat.log_lt_of_lt_pow ( by linarith ) ( by nlinarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] );
      have h_log_p2 : padicValNat p2 (M k) = Nat.log p2 k := by
        apply padicValNat_lcm_range;
        · assumption;
        · grind;
      rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
      · intro h; have := h p2; simp_all +decide [ Nat.factorization ] ;
        linarith;
      · exact hp2.ne_zero;
      · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
    constructor;
    · refine' Nat.Coprime.symm ( hp1.coprime_iff_not_dvd.mpr _ );
      rw [ Nat.dvd_div_iff_mul_dvd ];
      · exact fun h => h_not_div_p1 <| dvd_trans ⟨ p2, by ring ⟩ h;
      · exact M_prime_dvd k p1 p2 hp1 hp2 hp_ne h_range1.2 h_range2.2;
    · refine' Nat.Coprime.symm ( hp2.coprime_iff_not_dvd.mpr _ );
      rw [ Nat.dvd_div_iff_mul_dvd ];
      · exact fun h => h_not_div_p2 <| dvd_trans ⟨ p1, by ring ⟩ h;
      · exact M_prime_dvd k p1 p2 hp1 hp2 hp_ne h_range1.2 h_range2.2

/-
Definitions of the intervals for x and y as specified in the proof.
-/
def y_interval (k : ℕ) (C : ℝ) : Set ℝ := Set.Ioo ((M k : ℝ) / (5 * C) * (1 + 1 / k)) ((M k : ℝ) / (4 * C) - k)

def x_interval (k : ℕ) (y : ℕ) (C : ℝ) : Set ℝ := Set.Ioo ((y : ℝ) - (M k : ℝ) / (5 * C * k)) (y : ℝ)

/-
Definition of B_set and its subset property.
-/
def B_set (k p : ℕ) : Set ℤ := Set.Icc ((p : ℤ) - (k % p : ℤ)) (p : ℤ)

lemma B_set_subset (k p : ℕ) (hp : p.Prime) (hk : k > 0) : B_set k p ⊆ Set.Icc 1 p := by
  -- Take any $b \in B_set k p$. By definition, $p - (k \% p) \leq b \leq p$.
  intro b hb
  rw [B_set] at hb
  obtain ⟨hb_lower, hb_upper⟩ := hb
  exact ⟨by linarith [Nat.zero_le (k % p), Nat.mod_lt k hp.pos], by linarith [Nat.zero_le (k % p), Nat.mod_lt k hp.pos]⟩

/-
Definition of B_set_star and its subset property.
-/
def B_set_star (k p M_val : ℕ) : Set ℤ := { c ∈ Set.Icc 1 (p : ℤ) | ∃ b ∈ B_set k p, c * (M_val : ℤ) ≡ b [ZMOD p] }

lemma B_set_star_subset (k p M_val : ℕ) : B_set_star k p M_val ⊆ Set.Icc 1 p := by
  exact fun x hx => hx.1

/-
Cardinality of B_set_star is the same as B_set.
-/
lemma B_set_star_ncard (k p M_val : ℕ) (hp : p.Prime) (h_coprime : Nat.Coprime M_val p) (hk : k > 0) :
  (B_set_star k p M_val).ncard = (B_set k p).ncard := by
    apply le_antisymm;
    · -- Since $M_val$ is coprime to $p$, multiplication by $M_val$ is a bijection on $\mathbb{Z}_p$.
      have h_bijection : ∀ c1 c2 : ℤ, c1 ∈ Set.Icc 1 (p : ℤ) → c2 ∈ Set.Icc 1 (p : ℤ) → c1 * M_val ≡ c2 * M_val [ZMOD p] → c1 ≡ c2 [ZMOD p] := by
        intro c1 c2 hc1 hc2 h; haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
        exact h.resolve_right ( by rw [ ZMod.natCast_eq_zero_iff ] ; exact fun h => by have := Nat.gcd_eq_right h; aesop );
      have h_bijection : ∀ c : ℤ, c ∈ B_set_star k p M_val → ∃ b ∈ B_set k p, c * M_val ≡ b [ZMOD p] := by
        exact fun c hc => by rcases hc with ⟨ hc1, b, hb1, hb2 ⟩ ; exact ⟨ b, hb1, hb2 ⟩ ;
      choose! f hf using h_bijection;
      have h_bijection : Set.InjOn f (B_set_star k p M_val) := by
        intros c1 hc1 c2 hc2 h_eq;
        have := hf c1 hc1; have := hf c2 hc2; simp_all +decide [ Int.ModEq ] ;
        have := h_bijection c1 c2 ( hc1.1.1 ) ( hc1.1.2 ) ( hc2.1.1 ) ( hc2.1.2 ) ; simp_all +decide [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] ;
        exact eq_of_sub_eq_zero ( by obtain ⟨ k, hk ⟩ := this ( by obtain ⟨ a, ha ⟩ := hf c1 hc1 |>.2; obtain ⟨ b, hb ⟩ := hf c2 hc2 |>.2; exact ⟨ a - b, by linarith ⟩ ) ; nlinarith [ hp.two_le, show k = 0 from by nlinarith [ hp.two_le, hc1.1.1, hc1.1.2, hc2.1.1, hc2.1.2 ] ] );
      apply Set.ncard_le_ncard_of_injOn;
      exacts [ fun c hc => hf c hc |>.1, h_bijection, Set.finite_Icc _ _ |> Set.Finite.subset <| fun x hx => ⟨ hx.1, hx.2 ⟩ ];
    · -- Since $M_val$ is coprime to $p$, multiplication by $M_val$ is a bijection on $\mathbb{Z}/p\mathbb{Z}$.
      have h_bijection : ∀ b ∈ B_set k p, ∃ c ∈ B_set_star k p M_val, c * (M_val : ℤ) ≡ b [ZMOD p] := by
        intro b hb
        obtain ⟨c, hc⟩ : ∃ c : ℤ, c * (M_val : ℤ) ≡ b [ZMOD p] ∧ 1 ≤ c ∧ c ≤ p := by
          -- Since $M_val$ is coprime to $p$, there exists an integer $c$ such that $c * M_val \equiv b \pmod{p}$.
          obtain ⟨c, hc⟩ : ∃ c : ℤ, c * (M_val : ℤ) ≡ b [ZMOD p] := by
            have := Nat.gcd_eq_gcd_ab M_val p;
            exact ⟨ b * Nat.gcdA M_val p, by rw [ Int.modEq_iff_dvd ] ; use Nat.gcdB M_val p * b; nlinarith [ hb.1, hb.2 ] ⟩;
          -- Since $c * M_val \equiv b \pmod{p}$, we can take $c' = c \mod p$. Then $c' * M_val \equiv b \pmod{p}$ and $0 \leq c' < p$.
          obtain ⟨c', hc'⟩ : ∃ c' : ℤ, c' * (M_val : ℤ) ≡ b [ZMOD p] ∧ 0 ≤ c' ∧ c' < p := by
            exact ⟨ c % p, by simpa [ Int.ModEq, Int.mul_emod ] using hc, Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr hp.ne_zero ), Int.emod_lt_of_pos _ ( Nat.cast_pos.mpr hp.pos ) ⟩;
          by_cases hc'_zero : c' = 0;
          · simp_all +decide [ Int.ModEq ];
            exact ⟨ p, by simp +decide [ ← hc'.1 ], by linarith, by linarith ⟩;
          · exact ⟨ c', hc'.1, lt_of_le_of_ne hc'.2.1 ( Ne.symm hc'_zero ), hc'.2.2.le ⟩;
        unfold B_set_star; aesop;
      choose! f hf using h_bijection;
      -- Since $f$ is injective, the cardinality of $B_set_star k p M_val$ is at least the cardinality of $B_set k p$.
      have h_inj : Set.InjOn f (B_set k p) := by
        intro b hb b' hb' h; have := hf b hb; have := hf b' hb'; simp_all +decide [ Int.ModEq ] ;
        rw [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] at this;
        simp_all +decide [ B_set ];
        obtain ⟨ a, ha ⟩ := this; nlinarith [ show a = 0 by nlinarith [ Nat.zero_le ( k % p ), Nat.mod_lt k hp.pos ] ] ;
      apply_rules [ Set.ncard_le_ncard_of_injOn ];
      · exact fun x hx => hf x hx |>.1;
      · exact Set.Finite.subset ( Set.finite_Icc 1 ( p : ℤ ) ) fun x hx => hx.1

/-
The density of B_set is at least 1 - 2*epsilon.
-/
lemma B_set_density_bound (k p : ℕ) (ε : ℝ) (hp : p.Prime)
  (h_eps_pos : ε > 0) (h_eps_small : ε ≤ 0.25)
  (h_range : (k : ℝ) / 2 < p ∧ (p : ℝ) < (1 + ε) * k / 2) :
  (B_set k p).ncard ≥ (1 - 2 * ε) * p := by
    unfold B_set;
    norm_num [ Set.ncard_eq_toFinset_card' ];
    erw [ Int.toNat_natCast ];
    norm_num +zetaDelta at *;
    rw [ Nat.mod_eq_sub_mod ];
    · by_cases h_cases : p ≤ k;
      · rw [ Nat.mod_eq_of_lt ];
        · rw [ Nat.cast_sub h_cases ] ; nlinarith [ show ( p : ℝ ) ≤ k by norm_cast ];
        · rw [ div_lt_iff₀ ] at h_range <;> norm_cast at * ; linarith [ Nat.sub_add_cancel h_cases ];
      · rw [ Nat.sub_eq_zero_of_le ( le_of_not_ge h_cases ) ] ; norm_num ; nlinarith [ show ( p : ℝ ) ≥ k + 1 by exact_mod_cast not_le.mp h_cases ];
    · exact Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith )

/-
Definition of the length of the y interval.
-/
def y_interval_length (k : ℕ) (C : ℝ) : ℝ :=
  ((M k : ℝ) / (4 * C) - k) - ((M k : ℝ) / (5 * C) * (1 + 1 / k))

/-
If an interval (A, B) is large enough (scaled length > n), there exists a starting integer such that a block of n integers, when scaled, fits inside (A, B).
-/
lemma exists_start_for_interval (A B : ℝ) (M_val : ℝ) (n : ℕ) (hM : M_val > 0) (h_len : (B - A) / M_val > n) :
  ∃ start : ℤ, ∀ z : ℤ, z ∈ Set.Icc start (start + n - 1) → (z : ℝ) * M_val ∈ Set.Ioo A B := by
    norm_num +zetaDelta at *;
    have h_start : ∃ start : ℤ, (A / M_val : ℝ) < start ∧ start + n - 1 < B / M_val := by
      ring_nf at *;
      exact ⟨ ⌊A * M_val⁻¹⌋ + 1, by push_cast; linarith [ Int.lt_floor_add_one ( A * M_val⁻¹ ) ], by push_cast; linarith [ Int.floor_le ( A * M_val⁻¹ ) ] ⟩;
    cases' h_start with start h_start ; use start ; intro z h₁ h₂
    have h₂' : z ≤ start + (n : ℤ) - 1 := by omega
    constructor <;> nlinarith [ mul_div_cancel₀ A hM.ne', mul_div_cancel₀ B hM.ne', show ( z : ℝ ) ≥ start by exact_mod_cast h₁, show ( z : ℝ ) ≤ start + n - 1 by exact_mod_cast h₂' ]

/-
m(k) divides M_prime(k, p1, p2).
-/
lemma m_dvd_M_prime (k p1 p2 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_ne : p1 ≠ p2)
  (h_range1 : k.sqrt < p1 ∧ p1 ≤ k) (h_range2 : k.sqrt < p2 ∧ p2 ≤ k) :
  m k ∣ M_prime k p1 p2 := by
    -- Since $p1$ and $p2$ are distinct primes greater than $\sqrt{k}$, their product $p1 * p2$ does not divide any of the prime powers in $m$.
    have h_div : ∀ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p * p ≤ k), ¬(p1 ∣ p) ∧ ¬(p2 ∣ p) := by
      norm_num +zetaDelta at *;
      exact fun p hp₁ hp₂ hp₃ hp₄ => ⟨ fun h => by have := Nat.le_of_dvd ( by linarith ) h; nlinarith [ Nat.lt_succ_sqrt k ], fun h => by have := Nat.le_of_dvd ( by linarith ) h; nlinarith [ Nat.lt_succ_sqrt k ] ⟩;
    -- Since $p1$ and $p2$ are distinct primes greater than $\sqrt{k}$, their product $p1 * p2$ does not divide any of the prime powers in $M$.
    have h_div_M : ∀ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p * p ≤ k), ¬(p1 ∣ p) ∧ ¬(p2 ∣ p) → (p ^ ((M k).factorization p)) ∣ M_prime k p1 p2 := by
      intros p hp h_div_p
      have h_div_M : p ^ ((M k).factorization p) ∣ M k := by
        exact Nat.ordProj_dvd _ _;
      refine' Nat.dvd_div_of_mul_dvd _;
      refine' Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ h_div_M;
      · exact Nat.Coprime.mul_left ( hp1.coprime_iff_not_dvd.mpr h_div_p.1 ) ( hp2.coprime_iff_not_dvd.mpr h_div_p.2 ) |> Nat.Coprime.pow_right _;
      · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by simpa [ * ] using Nat.coprime_primes hp1 hp2 ) ( Nat.dvd_trans ( by aesop ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ : p1 ∈ Finset.Icc 1 k ) ) ) ( Nat.dvd_trans ( by aesop ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ : p2 ∈ Finset.Icc 1 k ) ) );
    -- Since the product of coprime divisors divides the number, we can conclude that m(k) divides M_prime.
    have h_coprime_divisors : ∀ p q : ℕ, p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p * p ≤ k) → q ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p * p ≤ k) → p ≠ q → Nat.Coprime (p ^ ((M k).factorization p)) (q ^ ((M k).factorization q)) := by
      intros p q hp hq hpq; exact Nat.coprime_pow_primes _ _ ( by aesop ) ( by aesop ) ( by aesop ) ;
    have h_prod_coprime_divisors : ∀ {S : Finset ℕ}, (∀ p ∈ S, p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p * p ≤ k)) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime (p ^ ((M k).factorization p)) (q ^ ((M k).factorization q))) → (∏ p ∈ S, p ^ ((M k).factorization p)) ∣ M_prime k p1 p2 := by
      intros S hS h_coprime; induction' S using Finset.induction with p S hS ih; aesop;
      rw [ Finset.prod_insert ‹p ∉ S› ];
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by exact Nat.Coprime.prod_right fun q hq => h_coprime p ( Finset.mem_insert_self _ _ ) q ( Finset.mem_insert_of_mem hq ) <| by aesop ) ( h_div_M p ( hS p <| Finset.mem_insert_self _ _ ) <| h_div p ( hS p <| Finset.mem_insert_self _ _ ) ) ( ih ( fun q hq => hS q <| Finset.mem_insert_of_mem hq ) ( fun q hq r hr hqr => h_coprime q ( Finset.mem_insert_of_mem hq ) r ( Finset.mem_insert_of_mem hr ) hqr ) );
    exact h_prod_coprime_divisors ( fun p hp => hp ) ( fun p hp q hq hpq => h_coprime_divisors p q hp hq hpq )

/-
M(k) is positive for k >= 1.
-/
lemma M_pos (k : ℕ) (hk : k ≥ 1) : M k > 0 := by
  exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) )

/-
If z satisfies the modular conditions and y = z * M', then y is good.
-/
lemma good_y_of_mod_conditions (k p1 p2 : ℕ) (z : ℤ) (y : ℕ)
  (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_ne : p1 ≠ p2)
  (h_range1 : k.sqrt < p1 ∧ p1 ≤ k) (h_range2 : k.sqrt < p2 ∧ p2 ≤ k)
  (h_y_eq : (y : ℤ) = z * (M_prime k p1 p2 : ℤ))
  (h_y_pos : y > 0)
  (h_z_mod1 : ∃ c1 ∈ B_set_star k p1 (M_prime k p1 p2), z ≡ c1 [ZMOD p1])
  (h_z_mod2 : ∃ c2 ∈ B_set_star k p2 (M_prime k p1 p2), z ≡ c2 [ZMOD p2]) :
  good_y k y := by
    refine' ⟨ h_y_pos, _, _ ⟩;
    · -- By definition of $y$, we know that $y = z * M'$, and since $M'$ is divisible by $m$, it follows that $y$ is also divisible by $m$.
      have h_div : m k ∣ M_prime k p1 p2 := by
        exact m_dvd_M_prime k p1 p2 hp1 hp2 hp_ne h_range1 h_range2;
      exact Nat.mod_eq_zero_of_dvd <| by exact_mod_cast h_y_eq.symm ▸ dvd_mul_of_dvd_right ( Int.natCast_dvd_natCast.mpr h_div ) _;
    · intro p hp hp_sqrt hp_le_k
      by_cases hp_cases : p = p1 ∨ p = p2;
      · rcases hp_cases with ( rfl | rfl ) <;> simp_all +decide [ ← Int.natCast_mod, Int.ModEq ];
        · obtain ⟨ c1, hc1₁, hc1₂ ⟩ := h_z_mod1;
          obtain ⟨ b, hb₁, hb₂ ⟩ := hc1₁.2;
          refine' ⟨ b.toNat, _, _, _ ⟩ <;> simp_all +decide [ Int.ModEq ];
          · have := hb₁.1; ( have := hb₁.2; ( norm_num [ B_set ] at *; omega; ) );
          · exact hb₁.2;
          · zify;
            simp_all +decide [ Int.emod_eq_emod_iff_emod_sub_eq_zero ];
            rw [ max_eq_left ( by linarith [ Set.mem_Icc.mp ( B_set_subset k p hp1 ( by linarith [ Nat.sqrt_pos.mpr ( show 0 < k from by linarith ) ] ) hb₁ ) ] ) ] ; convert dvd_add ( hc1₂.mul_right ( M_prime k p p2 ) ) hb₂ using 1 ; ring;
        · -- Since $z \equiv c2 \pmod{p}$, we have $z * M_prime \equiv c2 * M_prime \pmod{p}$. Therefore, $y \equiv b \pmod{p}$ for some $b \in B_set k p$.
          obtain ⟨b, hb⟩ : ∃ b ∈ B_set k p, z * M_prime k p1 p ≡ b [ZMOD p] := by
            obtain ⟨ c2, hc2₁, hc2₂ ⟩ := h_z_mod2;
            obtain ⟨ b, hb₁, hb₂ ⟩ := hc2₁;
            exact ⟨ hb₁, hb₂.1, by simpa [ Int.ModEq, Int.mul_emod, hc2₂ ] using hb₂.2 ⟩;
          -- Since $b \in B_set k p$, we have $p - k \% p \leq b \leq p$.
          obtain ⟨hb1, hb2⟩ : p - k % p ≤ b ∧ b ≤ p := by
            exact ⟨ hb.1.1, hb.1.2 ⟩;
          refine' ⟨ Int.toNat b, _, _, _ ⟩;
          · grind;
          · grind;
          · zify;
            rw [ Int.toNat_of_nonneg ( by linarith [ Int.emod_lt_of_pos ( k : ℤ ) ( Nat.cast_pos.mpr hp2.pos ) ] ) ] ; aesop;
      · have h_div : p ∣ M_prime k p1 p2 := by
          refine' Nat.dvd_div_of_mul_dvd _;
          refine' Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ _;
          · rw [ Nat.coprime_mul_iff_left ];
            exact ⟨ hp1.coprime_iff_not_dvd.mpr fun h => hp_cases <| Or.inl <| by rw [ Nat.prime_dvd_prime_iff_eq ] at h <;> tauto, hp2.coprime_iff_not_dvd.mpr fun h => hp_cases <| Or.inr <| by rw [ Nat.prime_dvd_prime_iff_eq ] at h <;> tauto ⟩;
          · exact M_prime_dvd k p1 p2 hp1 hp2 hp_ne h_range1.2 h_range2.2;
          · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hp.pos, hp_le_k ⟩ );
        use p; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
        exact Nat.mod_eq_zero_of_dvd <| by exact_mod_cast h_y_eq.symm ▸ dvd_mul_of_dvd_right ( Int.natCast_dvd_natCast.mpr <| Nat.dvd_of_mod_eq_zero h_div ) _;

/-
If the interval is large enough and densities are good, then y exists.
-/
lemma exists_y_if_large_interval (C : ℝ) (hC : C ≥ 1) (k : ℕ) (p1 p2 : ℕ)
  (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_lt : p1 < p2)
  (h_range1 : k / 2 < p1 ∧ p1 ≤ k) (h_range2 : k / 2 < p2 ∧ p2 ≤ k)
  (h_len : y_interval_length k C / (M_prime k p1 p2 : ℝ) > p1 + p2)
  (h_M_prime_coprime : Nat.Coprime (M_prime k p1 p2) p1 ∧ Nat.Coprime (M_prime k p1 p2) p2)
  (h_B_density : (B_set k p1).ncard ≥ (1 - 1 / (20 * C)) * p1 ∧ (B_set k p2).ncard ≥ (1 - 1 / (20 * C)) * p2)
  (h_eps_small : 1 / (20 * C) * (p1 + p2) < p1) :
  ∃ y : ℕ, (y : ℝ) ∈ y_interval k C ∧ good_y k y := by
    revert h_len;
    intro h_len
    obtain ⟨start, hstart⟩ : ∃ start : ℤ, ∀ z : ℤ, z ∈ Set.Icc start (start + p1 - 1) → (z : ℝ) * (M_prime k p1 p2) ∈ y_interval k C := by
      apply exists_start_for_interval;
      · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) );
      · norm_num +zetaDelta at *;
        convert lt_of_le_of_lt _ h_len using 1;
        · unfold y_interval_length; ring;
        · linarith;
    obtain ⟨z, hz_bounds, hz_mod1, hz_mod2⟩ : ∃ z : ℤ, z ∈ Set.Icc start (start + p1 - 1) ∧ (∃ c1 ∈ B_set_star k p1 (M_prime k p1 p2), z ≡ c1 [ZMOD p1]) ∧ (∃ c2 ∈ B_set_star k p2 (M_prime k p1 p2), z ≡ c2 [ZMOD p2]) := by
      have := claim_approx_2 p1 p2 hp1 hp2 ( ne_of_lt hp_lt ) ( 1 / ( 20 * C ) ) ( B_set_star k p1 ( M_prime k p1 p2 ) ) ( B_set_star k p2 ( M_prime k p1 p2 ) ) ?_ ?_ ?_ ?_ p1 ?_ ?_ ?_ <;> norm_num at *;
      any_goals linarith;
      · exact Exists.imp ( by aesop ) ( this start );
      · exact B_set_star_subset k p1 ( M_prime k p1 p2 );
      · exact B_set_star_subset k p2 ( M_prime k p1 p2 );
      · convert h_B_density.1 using 1;
        rw [ B_set_star_ncard ] ; aesop;
        · exact h_M_prime_coprime.1;
        · grind;
      · convert h_B_density.2 using 1;
        rw [ B_set_star_ncard ];
        · assumption;
        · exact h_M_prime_coprime.2;
        · grind;
    obtain ⟨y, hy_eq⟩ : ∃ y : ℕ, (y : ℤ) = z * (M_prime k p1 p2 : ℤ) ∧ y > 0 := by
      have hy_pos : 0 < (z : ℝ) * (M_prime k p1 p2 : ℝ) := by
        exact hstart z hz_bounds |>.1.trans_le' <| by positivity;
      exact ⟨ Int.natAbs ( z * M_prime k p1 p2 ), by simp +decide [ abs_of_pos ( show 0 < z * M_prime k p1 p2 from by exact_mod_cast hy_pos ) ], Int.natAbs_pos.mpr ( show z * M_prime k p1 p2 ≠ 0 from by exact_mod_cast hy_pos.ne' ) ⟩;
    refine' ⟨ y, _, _ ⟩;
    · convert hstart z hz_bounds using 1 ; norm_cast ; aesop;
    · apply good_y_of_mod_conditions;
      exact hp1;
      exact hp2;
      exact ne_of_lt hp_lt;
      any_goals tauto;
      · exact ⟨ Nat.sqrt_lt.mpr ( by nlinarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] ), h_range1.2 ⟩;
      · exact ⟨ Nat.sqrt_lt.mpr ( by nlinarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] ), h_range2.2 ⟩

/-
Definitions for x interval length, M_prime3, B_set_x, and B_set_x_star.
-/
def x_interval_length (k : ℕ) (C : ℝ) : ℝ := (M k : ℝ) / (5 * C * k)

def M_prime3 (k q1 q2 q3 : ℕ) : ℕ := (M k) / (q1 * q2 * q3)

def B_set_x (k p : ℕ) : Set ℤ := Set.Icc 1 ((p : ℤ) - (k % p : ℤ))

/-
B_set_x is a subset of [1, p].
-/
lemma B_set_x_subset (k p : ℕ) (hp : p.Prime) (hk : k > 0) : B_set_x k p ⊆ Set.Icc 1 p := by
  exact Set.Icc_subset_Icc_right ( by linarith [ Nat.zero_le ( k % p ) ] )

/-
Cardinality of B_set_x for p in (k/2, k).
-/
lemma B_set_x_ncard (k p : ℕ) (hp : p.Prime) (h_range : (1 : ℝ) / 2 * k < p ∧ p < k) :
  (B_set_x k p).ncard = 2 * p - k := by
    rw [ show B_set_x k p = Set.Icc 1 ( p - ( k % p ) : ℤ ) by ext; aesop, Set.ncard_eq_toFinset_card' ] ; norm_num;
    rw [ show ( k : ℤ ) % p = k - p by
          norm_cast at *;
          rw [ Int.subNatNat_of_le h_range.2.le ] ; norm_cast;
          rw [ Nat.mod_eq_sub_mod h_range.2.le ];
          rw [ Nat.mod_eq_of_lt ( by rw [ div_mul_eq_mul_div, div_lt_iff₀ ] at h_range <;> norm_cast at * ; omega ) ] ] ; ring_nf ; aesop

/-
M_prime3 is positive.
-/
lemma M_prime3_pos (k q1 q2 q3 : ℕ) (hk : k ≥ 1) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_le1 : q1 ≤ k) (h_le2 : q2 ≤ k) (h_le3 : q3 ≤ k) : M_prime3 k q1 q2 q3 > 0 := by
    -- Since q1, q2, q3 are distinct primes ≤ k, they divide M(k). Therefore, q1 * q2 * q3 divides M(k), making M_prime3 k q1 q2 q3 positive.
    have h_div : q1 * q2 * q3 ∣ M k := by
      have h_div : q1 ∣ M k ∧ q2 ∣ M k ∧ q3 ∣ M k := by
        exact ⟨ Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hq1.pos, h_le1 ⟩ ), Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hq2.pos, h_le2 ⟩ ), Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hq3.pos, h_le3 ⟩ ) ⟩;
      convert Nat.lcm_dvd ( Nat.lcm_dvd h_div.1 h_div.2.1 ) h_div.2.2 using 1;
      simp_all +decide [ Nat.lcm ];
      have := Nat.coprime_primes hq1 hq2; ( have := Nat.coprime_primes hq1 hq3; ( have := Nat.coprime_primes hq2 hq3; simp_all +decide [ Nat.Coprime, Nat.Coprime.symm, Nat.Coprime.gcd_mul ] ; ) );
    exact Nat.div_pos ( Nat.le_of_dvd ( M_pos k hk ) h_div ) ( Nat.mul_pos ( Nat.mul_pos hq1.pos hq2.pos ) hq3.pos )

/-
m(k) divides M_prime3(k, q1, q2, q3).
-/
lemma m_dvd_M_prime3 (k q1 q2 q3 : ℕ) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_range1 : k.sqrt < q1 ∧ q1 ≤ k) (h_range2 : k.sqrt < q2 ∧ q2 ≤ k) (h_range3 : k.sqrt < q3 ∧ q3 ≤ k) :
  m k ∣ M_prime3 k q1 q2 q3 := by
    refine' Nat.Coprime.dvd_of_dvd_mul_left _ _;
    exact q1 * q2 * q3;
    · -- Since $q1$, $q2$, and $q3$ are distinct primes greater than $\sqrt{k}$, they do not divide $m(k)$.
      have h_not_div : ¬(q1 ∣ m k) ∧ ¬(q2 ∣ m k) ∧ ¬(q3 ∣ m k) := by
        have h_not_div : ∀ p ∈ Finset.filter (fun p => p.Prime ∧ p * p ≤ k) (Finset.Icc 1 k), ¬(q1 ∣ p) ∧ ¬(q2 ∣ p) ∧ ¬(q3 ∣ p) := by
          intro p hp; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
          exact ⟨ by rintro rfl; nlinarith [ Nat.lt_succ_sqrt k ], by rintro rfl; nlinarith [ Nat.lt_succ_sqrt k ], by rintro rfl; nlinarith [ Nat.lt_succ_sqrt k ] ⟩;
        have h_not_div_prod : ∀ {S : Finset ℕ}, (∀ p ∈ S, ¬(q1 ∣ p) ∧ ¬(q2 ∣ p) ∧ ¬(q3 ∣ p)) → ¬(q1 ∣ Finset.prod S (fun p => p ^ (Nat.factorization (Finset.lcm (Finset.Icc 1 k) id) p))) ∧ ¬(q2 ∣ Finset.prod S (fun p => p ^ (Nat.factorization (Finset.lcm (Finset.Icc 1 k) id) p))) ∧ ¬(q3 ∣ Finset.prod S (fun p => p ^ (Nat.factorization (Finset.lcm (Finset.Icc 1 k) id) p))) := by
          intros S hS; induction S using Finset.induction <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
          exact ⟨ Nat.Coprime.mul_right ( Nat.Coprime.pow_right _ hS.1.1 ) ( by tauto ), Nat.Coprime.mul_right ( Nat.Coprime.pow_right _ hS.1.2.1 ) ( by tauto ), Nat.Coprime.mul_right ( Nat.Coprime.pow_right _ hS.1.2.2 ) ( by tauto ) ⟩;
        exact h_not_div_prod h_not_div;
      exact Nat.Coprime.mul_right ( Nat.Coprime.mul_right ( Nat.Coprime.symm <| hq1.coprime_iff_not_dvd.mpr h_not_div.1 ) <| Nat.Coprime.symm <| hq2.coprime_iff_not_dvd.mpr h_not_div.2.1 ) <| Nat.Coprime.symm <| hq3.coprime_iff_not_dvd.mpr h_not_div.2.2;
    · rw [ show M_prime3 k q1 q2 q3 = M k / ( q1 * q2 * q3 ) from rfl ];
      rw [ Nat.mul_div_cancel' ];
      · have h_div : (∏ p ∈ Finset.filter (fun p => p.Prime ∧ p * p ≤ k) (Finset.Icc 1 k), p ^ (M k).factorization p) ∣ (∏ p ∈ Finset.Icc 1 k, p ^ (M k).factorization p) := by
          apply_rules [ Finset.prod_dvd_prod_of_subset, Finset.filter_subset ];
        convert h_div using 1;
        conv_lhs => rw [ ← Nat.prod_factorization_pow_eq_self ( show M k ≠ 0 from Nat.ne_of_gt ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ) ] ;
        rw [ Finsupp.prod_of_support_subset ] <;> norm_num [ Finset.subset_iff ];
        intro p pp dp _; exact ⟨ pp.pos, pp.dvd_factorial.mp ( dvd_trans dp ( Finset.lcm_dvd fun i hi => Nat.dvd_factorial ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hi |>.2 ) ) ) ⟩ ;
      · have h_div : q1 ∣ M k ∧ q2 ∣ M k ∧ q3 ∣ M k := by
          exact ⟨ Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ), Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ), Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) ⟩;
        convert Nat.lcm_dvd ( Nat.lcm_dvd h_div.1 h_div.2.1 ) h_div.2.2 using 1;
        simp +decide [ *, Nat.lcm ];
        have := Nat.coprime_primes hq1 hq2; have := Nat.coprime_primes hq1 hq3; have := Nat.coprime_primes hq2 hq3; simp_all +decide [ Nat.Coprime, Nat.Coprime.symm, Nat.Coprime.gcd_mul ] ;

/-
M_prime3(k, q1, q2, q3) is coprime to q1, q2, and q3.
-/
lemma M_prime3_coprime (k q1 q2 q3 : ℕ) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_range1 : k / 2 < q1 ∧ q1 ≤ k) (h_range2 : k / 2 < q2 ∧ q2 ≤ k) (h_range3 : k / 2 < q3 ∧ q3 ≤ k)
  (hk : k ≥ 9) :
  Nat.Coprime (M_prime3 k q1 q2 q3) q1 ∧ Nat.Coprime (M_prime3 k q1 q2 q3) q2 ∧ Nat.Coprime (M_prime3 k q1 q2 q3) q3 := by
    have h_divides : q1 * q2 * q3 ∣ M k := by
      refine' Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ _;
      · simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.coprime_primes ];
      · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by simpa [ * ] using Nat.coprime_primes hq1 hq2 ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hq1.pos, h_range1.2 ⟩ ) ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hq2.pos, h_range2.2 ⟩ ) );
      · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ], by linarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] ⟩ );
    have h_divides : Nat.factorization (M k) q1 = 1 ∧ Nat.factorization (M k) q2 = 1 ∧ Nat.factorization (M k) q3 = 1 := by
      have h_divides : Nat.factorization (M k) q1 = Nat.log q1 k ∧ Nat.factorization (M k) q2 = Nat.log q2 k ∧ Nat.factorization (M k) q3 = Nat.log q3 k := by
        have h_log : ∀ p : ℕ, Nat.Prime p → p ≤ k → padicValNat p (M k) = Nat.log p k := by
          intros p hp hp_le_k
          apply padicValNat_lcm_range k p hp (by linarith);
        simp_all +decide [ Nat.factorization ];
      have h_log : Nat.log q1 k = 1 ∧ Nat.log q2 k = 1 ∧ Nat.log q3 k = 1 := by
        exact ⟨ Nat.le_antisymm ( Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow ( by linarith ) ( by nlinarith only [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos, h_range1, hk ] ) ) ) ( Nat.log_pos hq1.one_lt ( by linarith ) ), Nat.le_antisymm ( Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow ( by linarith ) ( by nlinarith only [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos, h_range2, hk ] ) ) ) ( Nat.log_pos hq2.one_lt ( by linarith ) ), Nat.le_antisymm ( Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow ( by linarith ) ( by nlinarith only [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos, h_range3, hk ] ) ) ) ( Nat.log_pos hq3.one_lt ( by linarith ) ) ⟩;
      aesop;
    have h_factorization : Nat.factorization (M_prime3 k q1 q2 q3) q1 = 0 ∧ Nat.factorization (M_prime3 k q1 q2 q3) q2 = 0 ∧ Nat.factorization (M_prime3 k q1 q2 q3) q3 = 0 := by
      unfold M_prime3;
      simp_all +decide [ Nat.factorization_mul, hq1.ne_zero, hq2.ne_zero, hq3.ne_zero ];
    simp_all +decide [ Nat.factorization_eq_zero_iff ];
    have h_pos : 0 < M_prime3 k q1 q2 q3 := by
      exact Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ‹q1 * q2 * q3 ∣ M k› ) ( Nat.mul_pos ( Nat.mul_pos hq1.pos hq2.pos ) hq3.pos );
    exact ⟨ Nat.Coprime.symm <| hq1.coprime_iff_not_dvd.mpr <| by aesop, Nat.Coprime.symm <| hq2.coprime_iff_not_dvd.mpr <| by aesop, Nat.Coprime.symm <| hq3.coprime_iff_not_dvd.mpr <| by aesop ⟩

/-
A version of claim_approx for 3 primes.
-/
lemma claim_approx_3 (q1 q2 q3 : ℕ) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (ε : ℝ) (B1 B2 B3 : Set ℤ)
  (hB1_subset : B1 ⊆ Set.Icc 1 q1) (hB2_subset : B2 ⊆ Set.Icc 1 q2) (hB3_subset : B3 ⊆ Set.Icc 1 q3)
  (hB1_size : B1.ncard ≥ (1 - ε) * q1) (hB2_size : B2.ncard ≥ (1 - ε) * q2) (hB3_size : B3.ncard ≥ (1 - ε) * q3)
  (n : ℕ) (hn : ε * (q1 + q2 + q3) < n) (hn_le1 : n ≤ q1) (hn_le2 : n ≤ q2) (hn_le3 : n ≤ q3) :
  ∀ start : ℤ, ∃ z ∈ Set.Icc start (start + n - 1),
    ∃ c1 ∈ B1, ∃ c2 ∈ B2, ∃ c3 ∈ B3,
    z ≡ c1 [ZMOD q1] ∧ z ≡ c2 [ZMOD q2] ∧ z ≡ c3 [ZMOD q3] := by
      intro start;
      -- By the Chinese Remainder Theorem, there exists a $z$ in the interval $[start, start + n - 1]$ such that $z \equiv c1 \pmod{q1}$, $z \equiv c2 \pmod{q2}$, and $z \equiv c3 \pmod{q3}$ for some $c1 \in B1$, $c2 \in B2$, and $c3 \in B3$.
      obtain ⟨c1, hc1⟩ : ∃ c1 ∈ B1, ∃ c2 ∈ B2, ∃ c3 ∈ B3, ∃ z ∈ Set.Icc start (start + n - 1), z ≡ c1 [ZMOD q1] ∧ z ≡ c2 [ZMOD q2] ∧ z ≡ c3 [ZMOD q3] := by
        by_contra h_contra;
        -- Applying the hypothesis `h_contra` to each element in the interval $[start, start + n - 1]$, we get that for each $z$ in this interval, there exists some $c1 \in B1$, $c2 \in B2$, or $c3 \in B3$ such that $z \not\equiv c1 \pmod{q1}$, $z \not\equiv c2 \pmod{q2}$, or $z \not\equiv c3 \pmod{q3}$.
        have h_count : (Finset.Icc start (start + n - 1)).card ≤ (Finset.filter (fun z => ∀ b ∈ B1, ¬(z ≡ b [ZMOD q1])) (Finset.Icc start (start + n - 1))).card + (Finset.filter (fun z => ∀ b ∈ B2, ¬(z ≡ b [ZMOD q2])) (Finset.Icc start (start + n - 1))).card + (Finset.filter (fun z => ∀ b ∈ B3, ¬(z ≡ b [ZMOD q3])) (Finset.Icc start (start + n - 1))).card := by
          have h_count : ∀ z ∈ Finset.Icc start (start + n - 1), (∀ b ∈ B1, ¬(z ≡ b [ZMOD q1])) ∨ (∀ b ∈ B2, ¬(z ≡ b [ZMOD q2])) ∨ (∀ b ∈ B3, ¬(z ≡ b [ZMOD q3])) := by
            norm_num +zetaDelta at *;
            grind;
          have h_count : Finset.Icc start (start + n - 1) ⊆ Finset.filter (fun z => ∀ b ∈ B1, ¬(z ≡ b [ZMOD q1])) (Finset.Icc start (start + n - 1)) ∪ Finset.filter (fun z => ∀ b ∈ B2, ¬(z ≡ b [ZMOD q2])) (Finset.Icc start (start + n - 1)) ∪ Finset.filter (fun z => ∀ b ∈ B3, ¬(z ≡ b [ZMOD q3])) (Finset.Icc start (start + n - 1)) := by
            intro z hz; specialize h_count z hz; aesop;
          exact le_trans ( Finset.card_le_card h_count ) ( Finset.card_union_le _ _ |> le_trans <| Nat.add_le_add_right ( Finset.card_union_le _ _ ) _ );
        -- Applying the hypothesis `h_count` to each element in the interval $[start, start + n - 1]$, we get that for each $z$ in this interval, there exists some $c1 \in B1$, $c2 \in B2$, or $c3 \in B3$ such that $z \not\equiv c1 \pmod{q1}$, $z \not\equiv c2 \pmod{q2}$, or $z \not\equiv c3 \pmod{q3}$.
        have h_card_bound : (Finset.filter (fun z => ∀ b ∈ B1, ¬(z ≡ b [ZMOD q1])) (Finset.Icc start (start + n - 1))).card ≤ ε * q1 ∧ (Finset.filter (fun z => ∀ b ∈ B2, ¬(z ≡ b [ZMOD q2])) (Finset.Icc start (start + n - 1))).card ≤ ε * q2 ∧ (Finset.filter (fun z => ∀ b ∈ B3, ¬(z ≡ b [ZMOD q3])) (Finset.Icc start (start + n - 1))).card ≤ ε * q3 := by
          refine' ⟨ _, _, _ ⟩;
          · convert bad_count_bound q1 hq1.pos B1 ε hB1_subset hB1_size n start ( by linarith ) using 1;
          · convert bad_count_bound q2 hq2.pos B2 ε ( by simpa using hB2_subset ) ( by simpa using hB2_size ) n start ( by linarith ) using 1;
          · convert bad_count_bound q3 hq3.pos B3 ε hB3_subset hB3_size n start ( by linarith ) using 1;
        norm_num at *;
        exact h_count.not_gt <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;
      grind

/-
The set of u in [1, p] such that u*M + 1 mod p is in B_set_x.
-/
def B_set_x_transformed (k p M_val : ℕ) : Set ℤ :=
  { u ∈ Set.Icc 1 (p : ℤ) | ∃ c ∈ B_set_x k p, u * (M_val : ℤ) + 1 ≡ c [ZMOD p] }

/-
B_set_x_transformed is a subset of {1, ..., p}.
-/
lemma B_set_x_transformed_subset (k p M_val : ℕ) :
  B_set_x_transformed k p M_val ⊆ Set.Icc 1 p := by
    exact fun x hx => hx.1

/-
The cardinality of the transformed set is equal to the cardinality of the original set.
-/
lemma B_set_x_transformed_ncard (k p M_val : ℕ) (hp : p.Prime) (h_coprime : Nat.Coprime M_val p) (hk : k > 0) :
  (B_set_x_transformed k p M_val).ncard = (B_set_x k p).ncard := by
    -- Since $M\_val$ is coprime to $p$, the map $u \mapsto u \cdot M\_val + 1$ is a bijection on the set $\{1, \dots, p\}$ modulo $p$.
    have h_bijection : ∀ (u₁ u₂ : ℤ), 1 ≤ u₁ → u₁ ≤ p → 1 ≤ u₂ → u₂ ≤ p → (u₁ * (M_val : ℤ) + 1) % p = (u₂ * (M_val : ℤ) + 1) % p → u₁ % p = u₂ % p := by
      intro u₁ u₂ hu₁ hu₁' hu₂ hu₂' h; haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff' ] ;
      rw [ ZMod.natCast_eq_zero_iff ] at h ; exact h.resolve_right ( by exact fun h' => by have := Nat.gcd_eq_right h'; aesop );
    -- Therefore, the number of solutions to $u \cdot M_val + 1 \equiv c \pmod p$ with $u \in \{1, \dots, p\}$ is 1 for each $c$.
    have h_solutions : ∀ (c : ℤ), c ∈ B_set_x k p → ∃! (u : ℤ), 1 ≤ u ∧ u ≤ p ∧ (u * (M_val : ℤ) + 1) % p = c % p := by
      intro c hc
      obtain ⟨u, hu⟩ : ∃ u : ℤ, 1 ≤ u ∧ u ≤ p ∧ (u * (M_val : ℤ) + 1) ≡ c [ZMOD p] := by
        have h_exists_u : ∃ u : ℤ, u * (M_val : ℤ) + 1 ≡ c [ZMOD p] := by
          -- Since $M_val$ is coprime to $p$, there exists an integer $u$ such that $u * M_val ≡ c - 1 \pmod{p}$.
          have h_exists_u : ∃ u : ℤ, u * (M_val : ℤ) ≡ c - 1 [ZMOD p] := by
            have h_inv : ∃ u : ℤ, u * (M_val : ℤ) ≡ 1 [ZMOD p] := by
              have := Nat.gcd_eq_gcd_ab M_val p;
              exact ⟨ Nat.gcdA M_val p, Int.modEq_iff_dvd.mpr ⟨ Nat.gcdB M_val p, by linarith ⟩ ⟩
            exact ⟨ h_inv.choose * ( c - 1 ), by convert h_inv.choose_spec.mul_right ( c - 1 ) using 1 <;> ring ⟩;
          exact ⟨ h_exists_u.choose, by convert h_exists_u.choose_spec.add_right 1 using 1; ring ⟩;
        obtain ⟨ u, hu ⟩ := h_exists_u;
        refine' ⟨ u % p + if u % p = 0 then p else 0, _, _, _ ⟩ <;> split_ifs <;> simp_all +decide [ Int.ModEq, Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr hp.ne_zero ) ];
        any_goals linarith [ Int.emod_nonneg u ( Nat.cast_ne_zero.mpr hp.ne_zero ), Int.emod_lt_of_pos u ( Nat.cast_pos.mpr hp.pos ) ];
        · exact lt_of_le_of_ne ( Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr hp.ne_zero ) ) ( Ne.symm ( by aesop ) );
        · rw [ Int.emod_eq_zero_of_dvd ‹_› ];
        · simp_all +decide [ Int.add_emod, Int.mul_emod, Int.emod_eq_zero_of_dvd ];
        · simpa [ Int.add_emod, Int.mul_emod ] using hu;
      refine' ⟨ u, ⟨ hu.1, hu.2.1, hu.2.2 ⟩, fun v hv => _ ⟩;
      have := h_bijection v u hv.1 hv.2.1 hu.1 hu.2.1 ( hv.2.2.trans hu.2.2.symm ) ; simp_all +decide [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] ;
      obtain ⟨ a, ha ⟩ := this; nlinarith [ show a = 0 by nlinarith ] ;
    choose! f hf₁ hf₂ using h_solutions;
    -- Therefore, the set $T$ is exactly the image of $S$ under the bijection $f$.
    have h_image : B_set_x_transformed k p M_val = (fun c => f c) '' B_set_x k p := by
      ext; simp [B_set_x_transformed, hf₁, hf₂];
      constructor;
      · rintro ⟨ ⟨ hx₁, hx₂ ⟩, c, hc₁, hc₂ ⟩ ; exact ⟨ c, hc₁, hf₂ c hc₁ _ ⟨ hx₁, hx₂, hc₂ ⟩ ▸ rfl ⟩;
      · rintro ⟨ c, hc, rfl ⟩ ; specialize hf₁ c hc; aesop;
    rw [ h_image, Set.InjOn.ncard_image ];
    intros c₁ hc₁ c₂ hc₂ h_eq;
    -- Since $f(c₁) = f(c₂)$, we have $(f(c₁) * M_val + 1) % p = c₁ % p$ and $(f(c₂) * M_val + 1) % p = c₂ % p$. Given that $f(c₁) = f(c₂)$, it follows that $c₁ % p = c₂ % p$.
    have h_mod_eq : c₁ % p = c₂ % p := by
      have := hf₁ c₁ hc₁; have := hf₁ c₂ hc₂; aesop;
    -- Since $c₁$ and $c₂$ are both in the interval $[1, p]$, and their remainders modulo $p$ are equal, they must be the same number.
    have h_eq : c₁ ≤ p ∧ c₂ ≤ p ∧ c₁ ≥ 1 ∧ c₂ ≥ 1 := by
      exact ⟨ by linarith [ Set.mem_Icc.mp ( B_set_x_subset k p hp hk hc₁ ) ], by linarith [ Set.mem_Icc.mp ( B_set_x_subset k p hp hk hc₂ ) ], by linarith [ Set.mem_Icc.mp ( B_set_x_subset k p hp hk hc₁ ) ], by linarith [ Set.mem_Icc.mp ( B_set_x_subset k p hp hk hc₂ ) ] ⟩;
    exact Int.modEq_iff_dvd.mp h_mod_eq.symm |> fun ⟨ x, hx ⟩ => by nlinarith [ show x = 0 by nlinarith ] ;

/-
If a real interval has length greater than N, it contains N consecutive integers.
-/
lemma exists_integer_interval (A B : ℝ) (N : ℕ) (h_len : B - A > N) :
  ∃ s : ℤ, ∀ z : ℤ, z ∈ Set.Icc s (s + N - 1) → (z : ℝ) ∈ Set.Ioo A B := by
    norm_num +zetaDelta at *;
    -- Since the interval $(A, B - N + 1)$ has length greater than 1, it must contain an integer.
    obtain ⟨s, hs⟩ : ∃ s : ℤ, A < s ∧ s < B - N + 1 := by
      exact ⟨ ⌊A⌋ + 1, by push_cast; linarith [ Int.lt_floor_add_one A ], by push_cast; linarith [ Int.floor_le A ] ⟩;
    refine ⟨ s, fun z hz₁ hz₂ => ⟨ by linarith [ show ( z : ℝ ) ≥ s by exact_mod_cast hz₁ ], ?_ ⟩ ⟩
    have hz₂' : z ≤ s + (N : ℤ) - 1 := by omega
    linarith [ show ( z : ℝ ) ≤ s + N - 1 by exact_mod_cast hz₂' ]

/-
If z satisfies the modular conditions for q1, q2, q3, then x = z*M' + 1 is a good x.
-/
lemma good_x_of_z (k : ℕ) (z : ℕ) (q1 q2 q3 : ℕ)
  (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_range1 : k.sqrt < q1 ∧ q1 ≤ k)
  (h_range2 : k.sqrt < q2 ∧ q2 ≤ k)
  (h_range3 : k.sqrt < q3 ∧ q3 ≤ k)
  (h_z_mod1 : ((z * M_prime3 k q1 q2 q3 + 1) % q1 : ℤ) ∈ B_set_x k q1)
  (h_z_mod2 : ((z * M_prime3 k q1 q2 q3 + 1) % q2 : ℤ) ∈ B_set_x k q2)
  (h_z_mod3 : ((z * M_prime3 k q1 q2 q3 + 1) % q3 : ℤ) ∈ B_set_x k q3)
  : good_x k (z * M_prime3 k q1 q2 q3 + 1) := by
    exists Nat.succ_pos _;
    constructor;
    · -- Since $m(k) \mid M_prime3(k, q1, q2, q3)$, we have $(z * M_prime3 + 1) \equiv 1 \pmod{m(k)}$.
      have h_mod_m : (z * M_prime3 k q1 q2 q3 + 1) % (m k) = 1 % (m k) := by
        rw [ Nat.add_mod, Nat.mul_mod ];
        rw [ Nat.mod_eq_zero_of_dvd ( m_dvd_M_prime3 k q1 q2 q3 hq1 hq2 hq3 h_distinct h_range1 h_range2 h_range3 ) ] ; norm_num;
      rw [ h_mod_m, Nat.mod_eq_of_lt ];
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ m ];
      · linarith;
      · refine' lt_of_lt_of_le _ ( Finset.prod_le_prod' fun p hp => Nat.le_self_pow _ _ );
        · refine' lt_of_lt_of_le _ ( Finset.prod_le_prod_of_subset_of_one_le' ( show Finset.filter ( fun p => Nat.Prime p ∧ p * p ≤ k + 1 + 1 ) ( Finset.Icc 1 ( k + 1 + 1 ) ) ≥ { 2 } from _ ) fun _ _ _ => Nat.Prime.pos <| by aesop ) <;> norm_num;
          rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
          · grind +ring;
          · rcases h_range1 with ⟨ _, _ ⟩ ; rcases h_range2 with ⟨ _, _ ⟩ ; rcases h_range3 with ⟨ _, _ ⟩ ; interval_cases q1 <;> interval_cases q2 <;> interval_cases q3 <;> trivial;
        · simp_all +decide [ Nat.factorization_eq_zero_iff ];
          exact ⟨ Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by nlinarith only [ hp.1.1, hp.2.2 ], by nlinarith only [ hp.1.2, hp.2.2 ] ⟩ ), Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop ⟩;
    · intro p hp h1 h2;
      by_cases hpq : p = q1 ∨ p = q2 ∨ p = q3;
      · rcases hpq with ( rfl | rfl | rfl ) <;> simp_all +decide [ B_set_x ];
        · exact ⟨ mod_cast h_z_mod1.1, Nat.le_sub_of_add_le <| by linarith [ Nat.mod_lt k hq1.pos, Nat.mod_lt ( z * M_prime3 k p q2 q3 + 1 ) hq1.pos ] ⟩;
        · exact ⟨ by linarith, Nat.le_sub_of_add_le <| by linarith [ Nat.mod_lt k hq2.pos, Nat.mod_lt ( z * M_prime3 k q1 p q3 + 1 ) hq2.pos ] ⟩;
        · norm_cast at *;
          rw [ Int.subNatNat_of_le ] at h_z_mod3 <;> norm_cast at * ; linarith [ Nat.mod_lt k hq3.pos ];
      · -- Since $p \neq q1$, $p \neq q2$, and $p \neq q3$, we have $p \mid M_prime3 k q1 q2 q3$.
        have hp_div_M_prime3 : p ∣ M_prime3 k q1 q2 q3 := by
          refine' Nat.dvd_div_of_mul_dvd _;
          apply_mod_cast Nat.Coprime.mul_dvd_of_dvd_of_dvd;
          · simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.coprime_primes ];
            tauto;
          · apply_mod_cast Nat.Coprime.mul_dvd_of_dvd_of_dvd;
            · rw [ Nat.coprime_mul_iff_left ];
              exact ⟨ by have := Nat.coprime_primes hq1 hq3; tauto, by have := Nat.coprime_primes hq2 hq3; tauto ⟩;
            · apply_mod_cast Nat.Coprime.mul_dvd_of_dvd_of_dvd;
              · simpa [ * ] using Nat.coprime_primes hq1 hq2;
              · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ );
              · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ );
            · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ );
          · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hp.pos, h2 ⟩ );
        norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hp_div_M_prime3 ];
        norm_num [ Nat.mod_eq_of_lt hp.one_lt ];
        exact Nat.sub_pos_of_lt ( Nat.mod_lt _ hp.pos )

/-
The epsilon condition is satisfied for primes in the given range.
-/
lemma epsilon_sum_lt_min_corrected (C : ℝ) (hC : C ≥ 1) (k : ℕ) (q1 q2 q3 : ℕ)
  (h_range1_lo : (1 - 1 / (20 * C)) * k < q1) (h_range1_hi : q1 < k)
  (h_range2_lo : (1 - 1 / (20 * C)) * k < q2) (h_range2_hi : q2 < k)
  (h_range3_lo : (1 - 1 / (20 * C)) * k < q3) (h_range3_hi : q3 < k)
  (hk : k > 0) :
  1 / (20 * C) * (q1 + q2 + q3) < min q1 (min q2 q3) := by
    -- Since $q1$, $q2$, and $q3$ are all less than $k$ and greater than $(1 - 1/(20C))k$, we can bound their sum.
    have h_sum_bound : (q1 + q2 + q3 : ℝ) < 3 * k := by
      norm_cast; linarith;
    cases min_cases ( q1 : ℝ ) ( min ( q2 : ℝ ) ( q3 : ℝ ) ) <;> cases min_cases ( q2 : ℝ ) ( q3 : ℝ ) <;> simp_all +decide;
    · nlinarith [ ( by norm_cast : ( q1 : ℝ ) ≤ q2 ), ( by norm_cast : ( q2 : ℝ ) ≤ q3 ), mul_inv_cancel₀ ( by positivity : ( C : ℝ ) ≠ 0 ) ];
    · nlinarith [ inv_mul_cancel₀ ( by linarith : C ≠ 0 ), ( by norm_cast : ( q1 : ℝ ) ≤ q3 ), ( by norm_cast : ( q3 : ℝ ) ≤ q2 ∧ ( q3 : ℝ ) < q2 ) ];
    · nlinarith [ ( by norm_cast : ( q2 : ℝ ) ≤ q1 ∧ ( q2 : ℝ ) < q1 ), ( by norm_cast : ( q2 : ℝ ) ≤ q3 ), inv_mul_cancel₀ ( by positivity : ( C : ℝ ) ≠ 0 ) ];
    · nlinarith [ inv_mul_cancel₀ ( by linarith : C ≠ 0 ) ]

/-
If a real interval is large enough, it contains an integer satisfying the modular conditions for 3 primes.
-/
lemma exists_z_in_real_interval (q1 q2 q3 : ℕ) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (ε : ℝ) (B1 B2 B3 : Set ℤ)
  (hB1_subset : B1 ⊆ Set.Icc 1 q1) (hB2_subset : B2 ⊆ Set.Icc 1 q2) (hB3_subset : B3 ⊆ Set.Icc 1 q3)
  (hB1_size : B1.ncard ≥ (1 - ε) * q1) (hB2_size : B2.ncard ≥ (1 - ε) * q2) (hB3_size : B3.ncard ≥ (1 - ε) * q3)
  (h_eps_cond : ε * (q1 + q2 + q3) < min q1 (min q2 q3))
  (A B : ℝ) (h_len : B - A > q1 + q2 + q3) :
  ∃ z : ℤ, (z : ℝ) ∈ Set.Ioo A B ∧
    (∃ c1 ∈ B1, z ≡ c1 [ZMOD q1]) ∧
    (∃ c2 ∈ B2, z ≡ c2 [ZMOD q2]) ∧
    (∃ c3 ∈ B3, z ≡ c3 [ZMOD q3]) := by
      have := exists_integer_interval A B ( Min.min q1 ( Min.min q2 q3 ) ) ?_;
      · obtain ⟨ s, hs ⟩ := this;
        refine' Exists.elim ( claim_approx_3 q1 q2 q3 hq1 hq2 hq3 h_distinct ε B1 B2 B3 hB1_subset hB2_subset hB3_subset hB1_size hB2_size hB3_size ( Min.min q1 ( Min.min q2 q3 ) ) _ _ _ _ _ ) _;
        any_goals tauto;
        · exact min_le_left _ _;
        · exact le_trans ( min_le_right _ _ ) ( min_le_left _ _ );
        · exact min_le_right _ _ |> le_trans <| min_le_right _ _;
      · exact lt_of_le_of_lt ( mod_cast by simp +decide [ min_le_iff ] ) h_len

/-
Forward direction of the equivalence between modular condition and set membership.
-/
lemma mod_in_B_set_x_of_exists (k p M_val : ℕ) (z : ℤ)
  (hp : p.Prime) (hk : k > 0) (h_range : k / 2 < p ∧ p < k)
  (h_coprime : Nat.Coprime M_val p)
  (h : ∃ u ∈ B_set_x_transformed k p M_val, z ≡ u [ZMOD p]) :
  ((z * (M_val : ℤ) + 1) % p : ℤ) ∈ B_set_x k p := by
    rcases h with ⟨ u, ⟨ hu_mod_p, c, hc₁, hc₂ ⟩, hu_z ⟩;
    -- Since $z \equiv u \pmod p$, we have $z * M_val + 1 \equiv u * M_val + 1 \equiv c \pmod p$.
    have h_cong : (z * M_val + 1) % p = c % p := by
      exact Eq.trans ( Int.ModEq.add ( Int.ModEq.mul_right _ hu_z ) rfl ) hc₂;
    -- Since $p$ is prime and $k \leq p$, we have $2p - k < p$, thus $1 \leq c < p$.
    have h_c_lt_p : 1 ≤ c ∧ c < p := by
      exact ⟨ by linarith [ Set.mem_Icc.mp hc₁ ], by linarith [ Set.mem_Icc.mp hc₁, show ( k % p : ℕ ) > 0 from Nat.pos_of_ne_zero fun h => by have := Nat.dvd_of_mod_eq_zero h; exact absurd ( Nat.dvd_trans ( dvd_refl _ ) this ) ( by rintro ⟨ q, hq ⟩ ; nlinarith [ show q = 1 by nlinarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] ] ) ] ⟩;
    simp_all +decide [ B_set_x ];
    exact ⟨ by rw [ Int.emod_eq_of_lt ] <;> linarith, by rw [ Int.emod_eq_of_lt ] <;> linarith ⟩

/-
Existence of z in the transformed interval satisfying modular conditions.
-/
lemma exists_z_in_z_interval (C : ℝ) (hC : C ≥ 1) (k : ℕ) (y : ℕ) (q1 q2 q3 : ℕ)
  (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_range1_lo : (1 - 1 / (20 * C)) * k < q1) (h_range1_hi : q1 < k)
  (h_range2_lo : (1 - 1 / (20 * C)) * k < q2) (h_range2_hi : q2 < k)
  (h_range3_lo : (1 - 1 / (20 * C)) * k < q3) (h_range3_hi : q3 < k)
  (h_len : x_interval_length k C / (M_prime3 k q1 q2 q3 : ℝ) > q1 + q2 + q3)
  (h_M_prime3_coprime : Nat.Coprime (M_prime3 k q1 q2 q3) q1 ∧ Nat.Coprime (M_prime3 k q1 q2 q3) q2 ∧ Nat.Coprime (M_prime3 k q1 q2 q3) q3)
  (h_B_density : (B_set_x k q1).ncard ≥ (1 - 1 / (20 * C)) * q1 ∧ (B_set_x k q2).ncard ≥ (1 - 1 / (20 * C)) * q2 ∧ (B_set_x k q3).ncard ≥ (1 - 1 / (20 * C)) * q3)
  (hk : k > 0) :
  let M' := M_prime3 k q1 q2 q3
  let L := x_interval_length k C
  let A := ((y : ℝ) - L - 1) / M'
  let B := ((y : ℝ) - 1) / M'
  ∃ z : ℤ, (z : ℝ) ∈ Set.Ioo A B ∧
    ((z * M' + 1) % q1 : ℤ) ∈ B_set_x k q1 ∧
    ((z * M' + 1) % q2 : ℤ) ∈ B_set_x k q2 ∧
    ((z * M' + 1) % q3 : ℤ) ∈ B_set_x k q3 := by
      have h_eps_cond : 1 / (20 * C) * (q1 + q2 + q3) < min q1 (min q2 q3) := by
        apply_rules [ epsilon_sum_lt_min_corrected ];
      have h_exists_z : ∃ z : ℤ, (z : ℝ) ∈ Set.Ioo ((y - x_interval_length k C - 1) / (M_prime3 k q1 q2 q3 : ℝ)) ((y - 1) / (M_prime3 k q1 q2 q3 : ℝ)) ∧
        (∃ c1 ∈ B_set_x_transformed k q1 (M_prime3 k q1 q2 q3), z ≡ c1 [ZMOD q1]) ∧
        (∃ c2 ∈ B_set_x_transformed k q2 (M_prime3 k q1 q2 q3), z ≡ c2 [ZMOD q2]) ∧
        (∃ c3 ∈ B_set_x_transformed k q3 (M_prime3 k q1 q2 q3), z ≡ c3 [ZMOD q3]) := by
          apply exists_z_in_real_interval;
          all_goals try assumption;
          any_goals exact B_set_x_transformed_subset _ _ _;
          · rw [ B_set_x_transformed_ncard ];
            · exact h_B_density.1;
            · assumption;
            · exact h_M_prime3_coprime.1;
            · grind;
          · rw [ B_set_x_transformed_ncard ] <;> aesop;
          · rw [ B_set_x_transformed_ncard ] <;> aesop;
          · ring_nf at *; linarith;
      obtain ⟨ z, hz₁, hz₂, hz₃, hz₄ ⟩ := h_exists_z;
      refine' ⟨ z, hz₁, _, _, _ ⟩ <;> simp_all +decide [ Int.ModEq ];
      · convert mod_in_B_set_x_of_exists k q1 ( M_prime3 k q1 q2 q3 ) z hq1 hk ⟨ _, _ ⟩ _ _ using 1;
        · exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ inv_mul_cancel₀ ( by positivity : ( C : ℝ ) ≠ 0 ) ] ;
        · linarith;
        · exact h_M_prime3_coprime.1;
        · exact ⟨ _, hz₂.choose_spec.1, hz₂.choose_spec.2 ⟩;
      · obtain ⟨ c2, hc2₁, hc2₂ ⟩ := hz₃;
        have := mod_in_B_set_x_of_exists k q2 ( M_prime3 k q1 q2 q3 ) z hq2 hk ⟨ by
          exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ inv_mul_cancel₀ ( by positivity : ( C : ℝ ) ≠ 0 ) ] ;, by
          linarith ⟩ ?_ ?_ <;> aesop;
      · convert mod_in_B_set_x_of_exists k q3 ( M_prime3 k q1 q2 q3 ) z hq3 hk ⟨ by
          rw [ Nat.div_lt_iff_lt_mul ] <;> norm_num at *;
          exact_mod_cast ( by nlinarith [ inv_mul_cancel₀ ( by positivity : ( C : ℝ ) ≠ 0 ) ] : ( k : ℝ ) < q3 * 2 ), by
          exact h_range3_hi ⟩ ( by
          exact h_M_prime3_coprime.2.2 ) _ using 1
        generalize_proofs at *;
        exact ⟨ _, hz₄.choose_spec.1, hz₄.choose_spec.2 ⟩

/-
Existence of a good x in the interval.
-/
lemma exists_x_if_large_interval (C : ℝ) (hC : C ≥ 1) (k : ℕ) (y : ℕ) (q1 q2 q3 : ℕ)
  (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_range1 : (1 - 1 / (20 * C)) * k < q1 ∧ q1 < k)
  (h_range2 : (1 - 1 / (20 * C)) * k < q2 ∧ q2 < k)
  (h_range3 : (1 - 1 / (20 * C)) * k < q3 ∧ q3 < k)
  (h_len : x_interval_length k C / (M_prime3 k q1 q2 q3 : ℝ) > q1 + q2 + q3)
  (h_M_prime3_coprime : Nat.Coprime (M_prime3 k q1 q2 q3) q1 ∧ Nat.Coprime (M_prime3 k q1 q2 q3) q2 ∧ Nat.Coprime (M_prime3 k q1 q2 q3) q3)
  (h_B_density : (B_set_x k q1).ncard ≥ (1 - 1 / (20 * C)) * q1 ∧ (B_set_x k q2).ncard ≥ (1 - 1 / (20 * C)) * q2 ∧ (B_set_x k q3).ncard ≥ (1 - 1 / (20 * C)) * q3)
  (h_eps_small : 1 / (20 * C) * (q1 + q2 + q3) < q1)
  (hy_large : (y : ℝ) > x_interval_length k C) :
  ∃ x : ℕ, (x : ℝ) ∈ x_interval k y C ∧ good_x k x := by
    -- Apply `exists_z_in_z_interval` to find an integer `z` that satisfies the modular conditions.
    obtain ⟨z, hz_mem, hz_mod⟩ : ∃ z : ℤ, (z : ℝ) ∈ Set.Ioo ((y - x_interval_length k C - 1) / (M_prime3 k q1 q2 q3 : ℝ)) ((y - 1) / (M_prime3 k q1 q2 q3 : ℝ)) ∧
      ((z * M_prime3 k q1 q2 q3 + 1) % q1 : ℤ) ∈ B_set_x k q1 ∧
      ((z * M_prime3 k q1 q2 q3 + 1) % q2 : ℤ) ∈ B_set_x k q2 ∧
      ((z * M_prime3 k q1 q2 q3 + 1) % q3 : ℤ) ∈ B_set_x k q3 := by
        apply exists_z_in_z_interval C hC k y q1 q2 q3 hq1 hq2 hq3 h_distinct h_range1.left h_range1.right h_range2.left h_range2.right h_range3.left h_range3.right h_len h_M_prime3_coprime h_B_density (by linarith);
    refine' ⟨ Int.toNat ( z * M_prime3 k q1 q2 q3 + 1 ), _, _ ⟩;
    · rcases z with ( _ | z ) <;> norm_num at *;
      · rw [ lt_div_iff₀ ] at * <;> norm_num at *;
        · constructor;
          · rw [ div_lt_iff₀ ] at hz_mem <;> norm_num [ x_interval_length ] at *;
            · norm_cast at *;
              rw [ Int.subNatNat_eq_coe ] at hz_mem ; push_cast at * ; linarith;
            · grind;
          · norm_cast at *;
            rw [ Int.subNatNat_eq_coe ] at hz_mem ; push_cast at * ; linarith;
        · grind;
        · exact Nat.pos_of_ne_zero ( by aesop_cat );
      · contrapose! hz_mem;
        intro h; rw [ div_add', div_lt_iff₀ ] at * <;> norm_num at *;
        · nlinarith [ show ( M_prime3 k q1 q2 q3 : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr <| by aesop_cat ];
        · exact Nat.pos_of_ne_zero ( by aesop_cat );
        · aesop;
        · aesop;
    · -- Since $q1$, $q2$, and $q3$ are greater than $\sqrt{k}$, we have $k.sqrt < q1$, $k.sqrt < q2$, and $k.sqrt < q3$.
      have h_sqrt_lt_q : k.sqrt < q1 ∧ k.sqrt < q2 ∧ k.sqrt < q3 := by
        have h_sqrt_lt_q : ∀ q : ℕ, Nat.Prime q → (1 - 1 / (20 * C)) * k < q → q < k → k.sqrt < q := by
          intros q hq hq_range hq_lt_k
          have h_sqrt_lt_q : (k : ℝ) / 2 < q := by
            nlinarith [ show ( q : ℝ ) ≥ 2 by exact_mod_cast hq.two_le, show ( k : ℝ ) ≥ q + 1 by exact_mod_cast hq_lt_k, one_div_mul_cancel ( by positivity : ( 20 * C : ℝ ) ≠ 0 ) ];
          rw [ div_lt_iff₀ ] at h_sqrt_lt_q <;> norm_cast at *;
          exact Nat.sqrt_lt.mpr ( by nlinarith only [ h_sqrt_lt_q, hq.two_le ] );
        exact ⟨ h_sqrt_lt_q q1 hq1 h_range1.1 h_range1.2, h_sqrt_lt_q q2 hq2 h_range2.1 h_range2.2, h_sqrt_lt_q q3 hq3 h_range3.1 h_range3.2 ⟩;
      convert good_x_of_z k ( Int.toNat z ) q1 q2 q3 hq1 hq2 hq3 h_distinct ⟨ h_sqrt_lt_q.1, by linarith ⟩ ⟨ h_sqrt_lt_q.2.1, by linarith ⟩ ⟨ h_sqrt_lt_q.2.2, by linarith ⟩ _ _ _;
      · rcases z with ( _ | z ) <;> norm_num at *;
        · norm_cast;
        · rw [ div_add', div_lt_iff₀ ] at hz_mem <;> norm_num at *;
          · nlinarith [ show ( M_prime3 k q1 q2 q3 : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr <| Nat.ne_of_gt <| M_prime3_pos k q1 q2 q3 ( by linarith ) hq1 hq2 hq3 h_distinct ( by linarith ) ( by linarith ) ( by linarith ) ];
          · exact Nat.pos_of_ne_zero ( by aesop_cat );
          · aesop;
      · convert hz_mod.1 using 1;
        rw [ Int.toNat_of_nonneg ];
        contrapose! hz_mem;
        refine' fun h => _;
        rw [ Set.mem_Ioo ] at h;
        rw [ div_lt_iff₀ ] at h;
        · nlinarith [ show ( z : ℝ ) ≤ -1 by exact_mod_cast Int.le_of_lt_add_one hz_mem, show ( M_prime3 k q1 q2 q3 : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by aesop_cat ];
        · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) );
      · convert hz_mod.2.1 using 1;
        rw [ Int.toNat_of_nonneg ];
        contrapose! hz_mem;
        refine' fun h => _;
        rw [ Set.mem_Ioo ] at h;
        rw [ div_lt_iff₀ ] at h;
        · nlinarith [ show ( z : ℝ ) ≤ -1 by exact_mod_cast Int.le_of_lt_add_one hz_mem, show ( M_prime3 k q1 q2 q3 : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by aesop_cat ];
        · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) );
      · convert hz_mod.2.2 using 1;
        rw [ Int.toNat_of_nonneg ];
        contrapose! hz_mem;
        refine' fun h => _;
        rw [ Set.mem_Ioo ] at h;
        rw [ div_lt_iff₀ ] at h;
        · nlinarith [ show ( z : ℝ ) ≤ -1 by exact_mod_cast Int.le_of_lt_add_one hz_mem, show ( M_prime3 k q1 q2 q3 : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by aesop_cat ];
        · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) )

/-
The ratio of y_interval_length to M(k) tends to 1/(20C).
-/
lemma y_len_div_M_limit (C : ℝ) (hC : C ≥ 1) :
  Filter.Tendsto (fun k => y_interval_length k C / M k) Filter.atTop (nhds (1 / (20 * C))) := by
    -- As $k \to \infty$, $k/M k \to 0$ because $M k$ grows exponentially.
    have h_k_div_M_k_zero : Filter.Tendsto (fun k : ℕ => (k : ℝ) / (M k)) Filter.atTop (nhds 0) := by
      -- By definition of $M$, we know that $M(k) \geq k$ for all $k \geq 1$.
      have h_M_ge_k : ∀ k ≥ 1, (M k : ℝ) ≥ k := by
        exact fun k hk => mod_cast Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by unfold M; exact mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hk, le_rfl ⟩ ) );
      -- Since $M(k)$ is the LCM of $1, 2, \ldots, k$, it is divisible by $k$ and $k-1$ for $k \geq 2$. Therefore, $M(k) \geq k(k-1)$.
      have h_M_ge_k_k_minus_1 : ∀ k ≥ 2, (M k : ℝ) ≥ k * (k - 1) := by
        intros k hk_ge_2
        have h_M_ge_k_k_minus_1 : (M k : ℕ) ≥ k * (k - 1) := by
          have h_M_ge_k_k_minus_1 : k * (k - 1) ∣ M k := by
            have h_M_ge_k_k_minus_1 : k ∣ M k ∧ (k - 1) ∣ M k := by
              exact ⟨ Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ), Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.le_sub_one_of_lt ( by linarith ), Nat.sub_le_of_le_add ( by linarith ) ⟩ ) ⟩;
            exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by cases k <;> simp_all +decide [ Nat.succ_eq_add_one ] ) h_M_ge_k_k_minus_1.1 h_M_ge_k_k_minus_1.2;
          exact Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by specialize h_M_ge_k k ( by linarith ) ; aesop ) ) h_M_ge_k_k_minus_1;
        cases k <;> norm_num at * ; norm_cast;
      refine' squeeze_zero_norm' _ _;
      use fun n => 1 / ( n - 1 );
      · filter_upwards [ Filter.eventually_ge_atTop 2 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ div_le_div_iff₀ ] <;> nlinarith [ h_M_ge_k_k_minus_1 n hn, show ( n : ℝ ) ≥ 2 by norm_cast ] ;
      · exact tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
    -- The remaining terms are constants, so their limits are straightforward.
    have h_const_terms : Filter.Tendsto (fun k : ℕ => (M k : ℝ) / (4 * C) / (M k) - (M k : ℝ) / (5 * C) / (M k) - (M k : ℝ) / (5 * C * k) / (M k)) Filter.atTop (nhds ((1 / (4 * C)) - (1 / (5 * C)) - 0)) := by
      have h_const_terms : Filter.Tendsto (fun k : ℕ => (1 / (4 * C)) - (1 / (5 * C)) - (1 / (5 * C * k))) Filter.atTop (nhds ((1 / (4 * C)) - (1 / (5 * C)) - 0)) := by
        exact tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop <| Filter.Tendsto.const_mul_atTop ( by positivity ) <| tendsto_natCast_atTop_atTop );
      refine h_const_terms.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop 1 ] with k hk₁ hk₂; simp [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < M k from Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ] );
    convert h_const_terms.sub h_k_div_M_k_zero using 2 <;> ring_nf;
    unfold y_interval_length; ring;

/-
Arithmetic check for x interval length.
-/
lemma interval_length_check_x_arithmetic (C : ℝ) (hC : C ≥ 1) :
  ∃ K, ∀ k ≥ K, ∀ q1 q2 q3 : ℝ, k / 2 < q1 → q1 ≤ k → k / 2 < q2 → q2 ≤ k → k / 2 < q3 → q3 ≤ k →
  (q1 * q2 * q3) / (5 * C * k) > q1 + q2 + q3 := by
    use 160 * C + 1;
    intro k hk q1 q2 q3 hq1 hq1' hq2 hq2' hq3 hq3';
    rw [ gt_iff_lt, lt_div_iff₀ ] <;> nlinarith [ mul_le_mul_of_nonneg_left hC ( by linarith : 0 ≤ k ), mul_le_mul_of_nonneg_left hC ( by linarith : 0 ≤ q1 ), mul_le_mul_of_nonneg_left hC ( by linarith : 0 ≤ q2 ), mul_le_mul_of_nonneg_left hC ( by linarith : 0 ≤ q3 ), mul_pos ( by linarith : 0 < q1 ) ( by linarith : 0 < q2 ), mul_pos ( by linarith : 0 < q1 ) ( by linarith : 0 < q3 ), mul_pos ( by linarith : 0 < q2 ) ( by linarith : 0 < q3 ) ]

/-
Lower bound for y interval length ratio.
-/
lemma y_len_div_M_lower_bound (C : ℝ) (hC : C ≥ 1) :
  ∃ K, ∀ k ≥ K, y_interval_length k C / M k > 1 / (40 * C) := by
    have := y_len_div_M_limit C hC |> fun h => h.eventually ( lt_mem_nhds <| show 1 / ( 20 * C ) > 1 / ( 40 * C ) by gcongr ; linarith ) ; aesop

/-
Stronger asymptotic check for y interval length.
-/
lemma interval_length_check_y_strong (C : ℝ) (hC : C ≥ 1) :
  ∃ K, ∀ k ≥ K, y_interval_length k C / ((M k : ℝ) / (k * k / 4)) > 2 * k := by
    -- Using the result from y_len_div_M_lower_bound, we can find such a K.
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k ≥ K, y_interval_length k C / M k > 1 / (40 * C) := by
      apply y_len_div_M_lower_bound C hC;
    -- We need to find K such that for all k ≥ K, (k * k / 4) * (1 / (40 * C)) > 2 * k.
    have h_arith : ∃ K : ℕ, ∀ k ≥ K, (k * k / 4 : ℝ) * (1 / (40 * C)) > 2 * k := by
      exact ⟨ ⌈2 * 40 * C * 4⌉₊ + 1, fun k hk => by nlinarith [ Nat.le_ceil ( 2 * 40 * C * 4 ), show ( k : ℝ ) ≥ ⌈2 * 40 * C * 4⌉₊ + 1 by exact_mod_cast hk, show ( 0 : ℝ ) ≤ 40 * C by positivity, mul_div_cancel₀ ( 1 : ℝ ) ( by positivity : ( 40 * C ) ≠ 0 ) ] ⟩;
    obtain ⟨ K', hK' ⟩ := h_arith; use Max.max K K'; intro k hk; specialize hK k ( le_trans ( le_max_left _ _ ) hk ) ; specialize hK' k ( le_trans ( le_max_right _ _ ) hk ) ; simp_all +decide [ div_eq_mul_inv ] ;
    nlinarith [ show ( 0 : ℝ ) ≤ k * k * 4⁻¹ by positivity ]

/-
m(k) grows faster than k.
-/
lemma m_gt_k (k : ℕ) : ∃ K, ∀ k ≥ K, m k > k + 1 := by
  -- Since $\sqrt{k}$ grows faster than $k$, we can find a $K$ such that for all $k \geq K$, $\sqrt{k} > k + 1$.
  use 16; intros k hk; (
  -- We'll use that $m(k)$ is the product of $p^{\lfloor \log_p k \rfloor}$ for $p \leq \sqrt{k}$.
  have h_m_prod : m k = ∏ p ∈ Finset.filter (fun p => p.Prime ∧ p * p ≤ k) (Finset.Icc 1 k), p ^ (Nat.log p k) := by
    refine' Finset.prod_congr rfl fun p hp => _;
    -- Since $p$ is a prime and $p \leq \sqrt{k}$, the highest power of $p$ that divides $M(k)$ is $p^{\log_p k}$.
    have h_factorization : Nat.factorization (M k) p = Nat.log p k := by
      convert padicValNat_lcm_range k p _ _ using 1;
      · rw [ Nat.factorization_def ] ; aesop;
      · aesop;
      · linarith;
    exact h_factorization ▸ rfl;
  -- Since $k \geq 16$, we have $\sqrt{k} \geq 4$. Therefore, $m(k)$ includes at least the primes $2$ and $3$ raised to their respective powers.
  have h_prime_factors : 2 ^ (Nat.log 2 k) * 3 ^ (Nat.log 3 k) ≤ m k := by
    rw [ h_m_prod, ← Finset.prod_sdiff <| show { 2, 3 } ⊆ Finset.filter ( fun p => Nat.Prime p ∧ p * p ≤ k ) ( Finset.Icc 1 k ) from ?_ ];
    · simp +zetaDelta at *;
      exact Finset.prod_pos fun x hx => pow_pos ( Nat.Prime.pos ( by aesop ) ) _;
    · exact Finset.insert_subset_iff.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by norm_num, by linarith ⟩, by norm_num, by linarith ⟩, Finset.singleton_subset_iff.mpr <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by norm_num, by linarith ⟩, by norm_num, by linarith ⟩ ⟩;
  rcases k with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | k ) <;> simp +arith +decide [ Nat.pow_succ' ] at *;
  have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) ( k + 9 ) ; ( have := Nat.lt_pow_succ_log_self ( by decide : 1 < 3 ) ( k + 9 ) ; ( norm_num [ Nat.pow_succ' ] at * ; nlinarith; ) ))

/-
Difference between good y and good x is at least m(k) - 1.
-/
lemma good_xy_diff (k x y : ℕ) (hx : good_x k x) (hy : good_y k y) (hxy : x < y) : y - x ≥ m k - 1 := by
  -- From good_x, we have x ≡ 1 [MOD m k].
  have hx_mod : x ≡ 1 [MOD m k] := by
    obtain ⟨hx0, hxmod, hx_res⟩ := hx;
    rw [ ← hxmod, Nat.ModEq, Nat.mod_mod ]

  -- From good_y, we have y ≡ 0 [MOD m k].
  have hy_mod : y ≡ 0 [MOD m k] := by
    cases hy ; aesop;
  rw [ Nat.modEq_zero_iff_dvd ] at hy_mod; obtain ⟨ c, hc ⟩ := hy_mod; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
  -- Since $x \equiv 1 \pmod{m k}$, we can write $x = m k * q + 1$ for some integer $q$.
  obtain ⟨ q, hq ⟩ : ∃ q, x = m k * q + 1 := by
    rw [ ← Nat.div_add_mod x ( m k ), hx_mod ];
    rcases hk : m k with ( _ | _ | m ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
    cases hx ; aesop;
  rw [ tsub_add_eq_add_tsub ( by nlinarith ), le_tsub_iff_left ] <;> nlinarith [ show c > q by nlinarith [ show m k > 0 from Nat.pos_of_ne_zero ( by intro t; simp_all +decide [ good_x ] ) ] ]

/-
L(a, b) is the LCM of integers in [a, b].
-/
def L (a b : ℕ) : ℕ := (Finset.Icc a b).lcm id

/-
lcm_real(s) is the LCM of elements in s, cast to Real.
-/
def lcm_real (s : Finset ℕ) : ℝ := (s.lcm id : ℕ)

/-
The statement of the main theorem.
-/
def MainTheoremStatement : Prop :=
  ∀ C : ℝ, C ≥ 1 →
  ∃ K, ∀ k ≥ K, ∃ x y : ℕ,
    0 < x ∧ x < y ∧ y > x + k ∧
    lcm_real (Finset.Icc x (x + k - 1)) > C * lcm_real (Finset.Icc y (y + k))

/-
Structure GoodPrimes.
-/
structure GoodPrimes (C : ℝ) (k : ℕ) where
  p1 : ℕ
  p2 : ℕ
  q1 : ℕ
  q2 : ℕ
  q3 : ℕ
  hp1 : p1.Prime
  hp2 : p2.Prime
  hq1 : q1.Prime
  hq2 : q2.Prime
  hq3 : q3.Prime
  hp_lt : p1 < p2
  hq_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3
  h_range_p1 : (k : ℝ) / 2 < p1 ∧ p1 ≤ k
  h_range_p2 : (k : ℝ) / 2 < p2 ∧ p2 ≤ k
  h_range_q1 : (1 - 1 / (20 * C)) * k < q1 ∧ (q1 : ℝ) < k
  h_range_q2 : (1 - 1 / (20 * C)) * k < q2 ∧ (q2 : ℝ) < k
  h_range_q3 : (1 - 1 / (20 * C)) * k < q3 ∧ (q3 : ℝ) < k

lemma epsilon_condition_y (C : ℝ) (hC : C ≥ 1) (k : ℕ) (p1 p2 : ℕ)
  (hp1_lo : (k : ℝ) / 2 < p1)
  (hp2_hi : (p2 : ℝ) < (1 + 1 / (40 * C)) * k / 2)
  (hk : k > 0) :
  1 / (20 * C) * (p1 + p2) < p1 := by
    field_simp at *;
    nlinarith [ ( by norm_cast : ( 0 :ℝ ) < k ) ]

lemma construct_xy (C : ℝ) (hC : C ≥ 1) (k : ℕ) (p1 p2 q1 q2 q3 : ℕ)
  (hp1 : p1.Prime) (hp2 : p2.Prime) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (hp_lt : p1 < p2) (hq_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_range_p1 : (k : ℝ) / 2 < p1 ∧ (p1 : ℝ) < (1 + 1 / (40 * C)) * k / 2)
  (h_range_p2 : (k : ℝ) / 2 < p2 ∧ (p2 : ℝ) < (1 + 1 / (40 * C)) * k / 2)
  (h_range_q1 : (1 - 1 / (40 * C)) * k < q1 ∧ (q1 : ℝ) < k)
  (h_range_q2 : (1 - 1 / (40 * C)) * k < q2 ∧ (q2 : ℝ) < k)
  (h_range_q3 : (1 - 1 / (40 * C)) * k < q3 ∧ (q3 : ℝ) < k)
  (hk_large : k ≥ 10)
  (h_len_y : y_interval_length k C / (M_prime k p1 p2 : ℝ) > p1 + p2)
  (h_len_x : x_interval_length k C / (M_prime3 k q1 q2 q3 : ℝ) > q1 + q2 + q3)
  : ∃ x y : ℕ, good_x k x ∧ good_y k y ∧ (x : ℝ) ∈ x_interval k y C ∧ (y : ℝ) ∈ y_interval k C := by
    -- Apply `exists_y_if_large_interval` with `p1`, `p2`.
    obtain ⟨y, hy⟩ : ∃ y : ℕ, (y : ℝ) ∈ y_interval k C ∧ good_y k y := by
      apply exists_y_if_large_interval C hC k p1 p2 hp1 hp2 hp_lt ⟨ by
        exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;, by
        exact_mod_cast ( by nlinarith [ show ( k : ℝ ) ≥ 10 by norm_cast, one_div_mul_cancel ( by positivity : ( 40 * C : ℝ ) ≠ 0 ) ] : ( p1 : ℝ ) ≤ k ) ⟩ ⟨ by
        exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;, by
        exact_mod_cast ( by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] : ( p2 : ℝ ) ≤ k ) ⟩ h_len_y ⟨ by
        apply (M_prime_coprime k p1 p2 hp1 hp2 hp_lt.ne ⟨ by
          exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;, by
          exact_mod_cast ( by nlinarith [ show ( k : ℝ ) ≥ 10 by norm_cast, one_div_mul_cancel ( by positivity : ( 40 * C : ℝ ) ≠ 0 ) ] : ( p1 : ℝ ) ≤ k ) ⟩ ⟨ by
          exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;, by
          exact_mod_cast ( by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] : ( p2 : ℝ ) ≤ k ) ⟩ (by linarith)).left
        skip, by
        apply (M_prime_coprime k p1 p2 hp1 hp2 (by
        linarith) ⟨by
        exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;, by
          exact_mod_cast ( by nlinarith [ show ( k : ℝ ) ≥ 10 by norm_cast, one_div_mul_cancel ( by positivity : ( 40 * C : ℝ ) ≠ 0 ) ] : ( p1 : ℝ ) ≤ k )⟩ ⟨by
        exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;, by
          exact_mod_cast ( by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] : ( p2 : ℝ ) ≤ k )⟩ (by
        grind)).right
        skip ⟩ ⟨ by
        have := B_set_density_bound k p1 ( 1 / ( 40 * C ) ) hp1 ( by positivity ) ( by nlinarith [ mul_div_cancel₀ ( 1 : ℝ ) ( by positivity : ( 40 * C ) ≠ 0 ) ] ) ⟨ by linarith, by linarith ⟩ ; norm_num at * ; linarith;, by
        have := B_set_density_bound k p2 ( 1 / ( 40 * C ) ) hp2 ( by positivity ) ( by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C : ℝ ) ≠ 0 ) ] ) ⟨ by linarith, by linarith ⟩ ; norm_num at * ; linarith; ⟩
      generalize_proofs at *;
      linarith [ epsilon_condition_y C hC k p1 p2 h_range_p1.1 h_range_p2.2 ( by linarith ) ];
    -- Apply `exists_x_if_large_interval` with `q1`, `q2`, `q3`.
    obtain ⟨x, hx⟩ : ∃ x : ℕ, (x : ℝ) ∈ x_interval k y C ∧ good_x k x := by
      apply exists_x_if_large_interval C hC k y q1 q2 q3 hq1 hq2 hq3 hq_distinct ⟨ by
        nlinarith [ show ( k : ℝ ) ≥ 10 by norm_cast, one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ), one_div_mul_cancel ( by positivity : ( 20 * C ) ≠ 0 ) ], by
        exact_mod_cast h_range_q1.2 ⟩ ⟨ by
        nlinarith [ one_div_mul_cancel ( by linarith : ( 40 * C ) ≠ 0 ), one_div_mul_cancel ( by linarith : ( 20 * C ) ≠ 0 ) ], by
        exact_mod_cast h_range_q2.2 ⟩ ⟨ by
        nlinarith [ show ( k : ℝ ) ≥ 10 by norm_cast, one_div_mul_cancel ( by positivity : ( 40 * C : ℝ ) ≠ 0 ), one_div_mul_cancel ( by positivity : ( 20 * C : ℝ ) ≠ 0 ) ], by
        exact_mod_cast h_range_q3.2 ⟩ h_len_x
      generalize_proofs at *;
      · apply M_prime3_coprime k q1 q2 q3 hq1 hq2 hq3 hq_distinct ⟨ by
          exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( 0 : ℝ ) < 1 / ( 40 * C ) by positivity, one_div_mul_cancel ( show ( 40 * C : ℝ ) ≠ 0 by positivity ) ] ;, by
          exact_mod_cast h_range_q1.2.le ⟩ ⟨ by
          exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( 1 : ℝ ) / ( 40 * C ) ≤ 1 / 40 by gcongr ; linarith ] ;, by
          exact_mod_cast h_range_q2.2.le ⟩ ⟨ by
          exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( k : ℝ ) ≥ 10 by norm_cast, one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] ;, by
          exact_mod_cast h_range_q3.2.le ⟩ ( by linarith );
      · have h_B_density : ∀ q : ℕ, Nat.Prime q → (1 - 1 / (40 * C)) * k < q → q < k → (B_set_x k q).ncard ≥ (1 - 1 / (20 * C)) * q := by
          intros q hq hq1 hq2
          have hB_density : (B_set_x k q).ncard = 2 * q - k := by
            convert B_set_x_ncard k q hq _ using 1
            generalize_proofs at *;
            exact ⟨ by nlinarith [ show ( q : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr hq.pos, show ( k : ℝ ) ≥ 10 by exact_mod_cast hk_large, one_div_mul_cancel ( by positivity : ( 40 * C : ℝ ) ≠ 0 ) ], hq2 ⟩
          generalize_proofs at *;
          rw [ hB_density, Nat.cast_sub ] <;> norm_num;
          · nlinarith [ ( by norm_cast : ( q : ℝ ) + 1 ≤ k ), inv_mul_cancel₀ ( by linarith : C ≠ 0 ), one_div_mul_cancel ( by linarith : ( 40 * C ) ≠ 0 ) ];
          · exact_mod_cast ( by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] : ( k : ℝ ) ≤ 2 * q )
        generalize_proofs at *; aesop;
      · simp +zetaDelta at *;
        nlinarith [ inv_mul_cancel₀ ( by linarith : C ≠ 0 ), ( by norm_cast; linarith : ( q1 : ℝ ) < k ), ( by norm_cast; linarith : ( q2 : ℝ ) < k ), ( by norm_cast; linarith : ( q3 : ℝ ) < k ) ];
      · unfold y_interval x_interval_length at *;
        norm_num +zetaDelta at *;
        ring_nf at *; nlinarith [ inv_mul_cancel₀ ( by positivity : ( k : ℝ ) ≠ 0 ), inv_mul_cancel₀ ( by positivity : ( C : ℝ ) ≠ 0 ), ( by norm_cast : ( 10 : ℝ ) ≤ k ) ] ;
    exact ⟨ x, y, hx.2, hy.2, hx.1, hy.1 ⟩

lemma y_len_div_M_gt_8_div_k (C : ℝ) (k : ℕ) (hk : k > 0)
  (h_interval_check : y_interval_length k C / ((M k : ℝ) / (k * k / 4)) > 2 * k) :
  y_interval_length k C / (M k : ℝ) > 8 / k := by
    field_simp at *; ( ring_nf at *; (
    -- The goal is already satisfied by h_interval_check.
    exact h_interval_check); )

/-
If the y interval length satisfies the strong condition, then it is large enough relative to M_prime and p1+p2.
-/
lemma sufficient_length_y (C : ℝ) (hC : C ≥ 1) (k : ℕ) (p1 p2 : ℕ)
  (hk : k ≥ 10)
  (hp1_prime : p1.Prime) (hp2_prime : p2.Prime) (hp_ne : p1 ≠ p2)
  (hp1 : (k : ℝ) / 2 < p1) (hp2 : (k : ℝ) / 2 < p2)
  (h_le1 : p1 ≤ k) (h_le2 : p2 ≤ k)
  (h_y_len_strong : y_interval_length k C / ((M k : ℝ) / (k * k / 4)) > 2 * k) :
  y_interval_length k C / (M_prime k p1 p2 : ℝ) > p1 + p2 := by
    have h_cross : (8 / (k : ℝ)) * (p1 * p2 : ℝ) > (p1 + p2 : ℝ) := by
      rw [ div_mul_eq_mul_div, gt_iff_lt, lt_div_iff₀ ] <;> nlinarith [ ( by norm_cast : ( 10 :ℝ ) ≤ k ) ];
    -- Substitute M_prime into the ratio and use the inequality from h_cross.
    have h_ratio : y_interval_length k C / (M_prime k p1 p2 : ℝ) = (y_interval_length k C / (M k : ℝ)) * (p1 * p2 : ℝ) := by
      rw [ show M_prime k p1 p2 = M k / ( p1 * p2 ) from rfl, Nat.cast_div ];
      · rw [ div_div_eq_mul_div ] ; push_cast ; ring;
      · exact M_prime_dvd k p1 p2 hp1_prime hp2_prime hp_ne h_le1 h_le2;
      · exact Nat.cast_ne_zero.mpr ( mul_ne_zero hp1_prime.ne_zero hp2_prime.ne_zero );
    have h_final : y_interval_length k C / (M k : ℝ) > 8 / (k : ℝ) := by
      have := y_len_div_M_gt_8_div_k C k (by linarith) h_y_len_strong
      exact this;
    exact h_ratio.symm ▸ by nlinarith [ show 0 < ( p1 : ℝ ) * p2 by exact mul_pos ( Nat.cast_pos.mpr hp1_prime.pos ) ( Nat.cast_pos.mpr hp2_prime.pos ) ] ;

/-
If the arithmetic condition holds, then the x interval length is sufficient relative to M_prime3 and q1+q2+q3.
-/
lemma sufficient_length_x (C : ℝ) (hC : C ≥ 1) (k : ℕ) (q1 q2 q3 : ℕ)
  (hk : k ≥ 10)
  (hq1_prime : q1.Prime) (hq2_prime : q2.Prime) (hq3_prime : q3.Prime)
  (hq_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (hq1 : (k : ℝ) / 2 < q1) (hq2 : (k : ℝ) / 2 < q2) (hq3 : (k : ℝ) / 2 < q3)
  (h_le1 : q1 ≤ k) (h_le2 : q2 ≤ k) (h_le3 : q3 ≤ k)
  (h_arithmetic : (q1 * q2 * q3 : ℝ) / (5 * C * k) > q1 + q2 + q3) :
  x_interval_length k C / (M_prime3 k q1 q2 q3 : ℝ) > q1 + q2 + q3 := by
    refine' lt_of_lt_of_le h_arithmetic _;
    rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| M_prime3_pos k q1 q2 q3 ( by linarith ) hq1_prime hq2_prime hq3_prime hq_distinct h_le1 h_le2 h_le3 ) ];
    unfold x_interval_length M_prime3; ring_nf;
    field_simp;
    exact_mod_cast Nat.mul_div_le _ _

/-
For sufficiently large k, there exist x and y satisfying the good conditions and interval bounds.
-/
lemma exists_xy_for_large_k (C : ℝ) (hC : C ≥ 1) (h_density : DensityHypothesis) :
  ∃ K, ∀ k ≥ K, ∃ x y, good_x k x ∧ good_y k y ∧ (x : ℝ) ∈ x_interval k y C ∧ (y : ℝ) ∈ y_interval k C := by
    -- Let's choose ε = 1/(40C) and obtain K_density.
    set ε := 1 / (40 * C)
    have hK_density : ∃ K_density, ∀ k ≥ K_density, ∃ p1 p2 q1 q2 q3 : ℕ,
      p1.Prime ∧ p2.Prime ∧ q1.Prime ∧ q2.Prime ∧ q3.Prime ∧
      p1 < p2 ∧ q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3 ∧
      (k : ℝ) / 2 < p1 ∧ p1 < (1 + ε) * k / 2 ∧
      (k : ℝ) / 2 < p2 ∧ p2 < (1 + ε) * k / 2 ∧
      (1 - ε) * k < q1 ∧ q1 < k ∧
      (1 - ε) * k < q2 ∧ q2 < k ∧
      (1 - ε) * k < q3 ∧ q3 < k := by
        have := h_density ε ( by positivity );
        obtain ⟨ K, hK ⟩ := this;
        use Nat.ceil K;
        intro k hk;
        obtain ⟨ ⟨ p1, p2, hp1, hp2, hp3, hp4, hp5, hp6 ⟩, q1, q2, q3, hq1, hq2, hq3, hq4, hq5, hq6, hq7 ⟩ := hK k ( le_trans ( Nat.le_ceil _ ) hk );
        cases lt_or_gt_of_ne hp5 <;> [ exact ⟨ p1, p2, q1, q2, q3, hp6.1, hp6.2, hq7.2.2.2.1, hq7.2.2.2.2.1, hq7.2.2.2.2.2, by linarith, by tauto ⟩ ; exact ⟨ p2, p1, q1, q2, q3, hp6.2, hp6.1, hq7.2.2.2.1, hq7.2.2.2.2.1, hq7.2.2.2.2.2, by linarith, by tauto ⟩ ];
    obtain ⟨ K_density, hK_density ⟩ := hK_density;
    -- Obtain K_y and K_x from the interval length conditions.
    obtain ⟨K_y, hK_y⟩ : ∃ K_y, ∀ k ≥ K_y, y_interval_length k C / ((M k : ℝ) / (k * k / 4)) > 2 * k := by
      exact interval_length_check_y_strong C hC
    obtain ⟨K_x, hK_x⟩ : ∃ K_x, ∀ k ≥ K_x, ∀ q1 q2 q3 : ℝ, k / 2 < q1 → q1 ≤ k → k / 2 < q2 → q2 ≤ k → k / 2 < q3 → q3 ≤ k → (q1 * q2 * q3 : ℝ) / (5 * C * k) > q1 + q2 + q3 := by
      exact interval_length_check_x_arithmetic C hC;
    use Nat.max ( Nat.ceil K_density ) ( Nat.max K_y ( Nat.ceil K_x + 10 ) );
    intros k hk_ge
    obtain ⟨p1, p2, q1, q2, q3, hp1, hp2, hq1, hq2, hq3, hp_lt, hq_distinct, h_range_p1, h_range_p2, h_range_q1, h_range_q2, h_range_q3⟩ := hK_density k (by
    exact le_trans ( Nat.le_ceil _ ) ( Nat.cast_le.mpr ( le_trans ( Nat.le_max_left _ _ ) hk_ge ) ));
    apply construct_xy C hC k p1 p2 q1 q2 q3 hp1 hp2 hq1 hq2 hq3 hp_lt ⟨ hq_distinct, h_range_p1, h_range_p2 ⟩ ⟨ h_range_q1, h_range_q2 ⟩ ⟨ h_range_q3.1, h_range_q3.2.1 ⟩ ⟨ h_range_q3.2.2.1, h_range_q3.2.2.2.1 ⟩ ⟨ h_range_q3.2.2.2.2.1, h_range_q3.2.2.2.2.2.1 ⟩ ⟨ h_range_q3.2.2.2.2.2.2.1, h_range_q3.2.2.2.2.2.2.2 ⟩ (by
    linarith [ Nat.le_max_right ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_right K_y ( ⌈K_x⌉₊ + 10 ) ]) (by
    apply sufficient_length_y C hC k p1 p2 (by
    linarith [ Nat.le_max_right ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_right K_y ( ⌈K_x⌉₊ + 10 ) ]) hp1 hp2 (by
    linarith) h_range_q1 h_range_q3.1 (by
    exact_mod_cast ( by nlinarith [ show ( ε : ℝ ) ≤ 1 / 40 by rw [ div_le_iff₀ ] <;> linarith ] : ( p1 : ℝ ) ≤ k )) (by
    exact_mod_cast ( by nlinarith [ mul_div_cancel₀ ( 1 : ℝ ) ( by positivity : ( 40 * C ) ≠ 0 ) ] : ( p2 : ℝ ) ≤ k )) (by
    exact hK_y k ( by linarith [ Nat.le_max_left ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_right ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_left K_y ( ⌈K_x⌉₊ + 10 ), Nat.le_max_right K_y ( ⌈K_x⌉₊ + 10 ) ] ))) (by
    apply sufficient_length_x C hC k q1 q2 q3 (by
    linarith [ Nat.le_max_right ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_right K_y ( ⌈K_x⌉₊ + 10 ) ]) hq1 hq2 hq3 ⟨ hq_distinct, h_range_p1, h_range_p2 ⟩ (by
    linarith [ show ( 1 - ε ) * k ≥ k / 2 by nlinarith [ show ( ε : ℝ ) ≤ 1 / 40 by rw [ div_le_iff₀ ] <;> linarith ] ]) (by
    linarith [ show ( 1 - ε ) * k ≥ k / 2 by nlinarith [ show ( ε : ℝ ) ≤ 1 / 2 by rw [ div_le_iff₀ ] <;> linarith ] ]) (by
    linarith [ show ( 1 - ε ) * k ≥ k / 2 by nlinarith [ show ( ε : ℝ ) ≤ 1 / 4 by rw [ div_le_iff₀ ] <;> linarith ] ]) (by
    exact_mod_cast h_range_q3.2.2.2.1.le) (by
    exact_mod_cast h_range_q3.2.2.2.2.2.1.le) (by
    exact_mod_cast h_range_q3.2.2.2.2.2.2.2.le) (by
    apply hK_x k (by
    exact le_trans ( Nat.le_ceil _ ) ( by norm_cast; linarith [ Nat.le_max_left ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_right ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_left K_y ( ⌈K_x⌉₊ + 10 ), Nat.le_max_right K_y ( ⌈K_x⌉₊ + 10 ) ] )) q1 q2 q3 (by
    linarith [ show ( 1 - ε ) * k ≥ k / 2 by nlinarith [ show ( ε : ℝ ) ≤ 1 / 40 by rw [ div_le_iff₀ ] <;> linarith ] ]) (by
    linarith) (by
    linarith [ show ( 1 - ε ) * k ≥ k / 2 by nlinarith [ show ( ε : ℝ ) ≤ 1 / 2 by rw [ div_le_iff₀ ] <;> linarith ] ]) (by
    linarith) (by
    linarith [ show ( 1 - ε ) * k ≥ k / 2 by nlinarith [ show ( ε : ℝ ) ≤ 1 / 4 by rw [ div_le_iff₀ ] <;> linarith ] ]) (by
    linarith)))

/-
The main theorem holds, conditional on the density hypothesis.
-/
theorem main_theorem (h_density : DensityHypothesis) : MainTheoremStatement := by
  intro C hC_ge_1
  -- Obtain `K1` from `exists_xy_for_large_k`.
  obtain ⟨K1, hK1⟩ := exists_xy_for_large_k C hC_ge_1 h_density
  -- Obtain `K2` from `final_inequality_sufficient`.
  obtain ⟨K2, hK2⟩ := final_inequality_sufficient C hC_ge_1
  -- Obtain `K3` from `m_gt_k`.
  obtain ⟨K3, hK3⟩ := m_gt_k 200000
  -- Let `K = max(K1, K2, K3, 2)`.
  set K := Nat.max (Nat.max (Nat.max K1 K2) K3) 2;
  use K;
  intro k hk_ge_K
  obtain ⟨x, y, hx, hy, hx_interval, hy_interval⟩ := hK1 k (by
  exact le_trans ( Nat.le_max_left _ _ ) ( le_trans ( Nat.le_max_left _ _ ) ( le_trans ( Nat.le_max_left _ _ ) hk_ge_K ) ))
  have hx_pos : 0 < x := by
    exact hx.1
  have hy_pos : 0 < y := by
    exact hy.1
  have hy_gt_x : y > x := by
    cases hx_interval ; cases hy_interval ; aesop
  have hy_gt_x_plus_k : y > x + k := by
    have := good_xy_diff k x y hx hy hy_gt_x;
    grind
  have h_ratio : (Finset.Icc x (x + k - 1)).lcm id / (Finset.Icc y (y + k)).lcm id ≥ (M k : ℚ) / (y + k) * ((x : ℚ) / y) ^ k := by
    apply lcm_ratio_bound k x y (by
    linarith [ show k ≥ 2 by exact le_trans ( by norm_num ) ( Nat.le_trans ( Nat.le_max_right _ _ ) hk_ge_K ) ]) hx_pos hy_pos hy_gt_x hx hy
  have h_final : (M k : ℚ) / (y + k) * ((x : ℚ) / y) ^ k > C := by
    apply hK2 k (by
    exact le_trans ( Nat.le_max_right _ _ ) ( le_trans ( Nat.le_max_left _ _ ) ( le_trans ( Nat.le_max_left _ _ ) hk_ge_K ) )) x y hx_pos hy_pos (by
    exact hy_interval.2) (by
    exact hy_interval.1) (by
    unfold x_interval at hx_interval; linarith [ hx_interval.1, hx_interval.2 ] ;)
  have h_lcm : lcm_real (Finset.Icc x (x + k - 1)) > C * lcm_real (Finset.Icc y (y + k)) := by
    refine' lt_of_lt_of_le ( mul_lt_mul_of_pos_right h_final ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero _ ) ) _;
    · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
    · convert le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| ?_ ) |>.1 h_ratio using 1 <;> norm_cast;
      · rw [ lcm_real ];
        rw [ lcm_real ] ; norm_cast;
      · norm_num [ Finset.lcm_eq_zero_iff ];
        linarith
  use x, y

lemma prime_counting_interval_tendsto_atTop (a b : ℝ) (ha : 0 < a) (hb : a < b) :
  Tendsto (fun x => (Nat.primeCounting (Nat.floor (b * x)) : ℝ) - (Nat.primeCounting (Nat.floor (a * x)) : ℝ)) atTop atTop := by
    have pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
        ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
          exact pi_alt;
    obtain ⟨c, hc⟩ := pi_alt;
    have hc_inf : Filter.Tendsto (fun x => ((1 + c (b * x)) * (b * x) / Real.log (b * x)) - ((1 + c (a * x)) * (a * x) / Real.log (a * x))) Filter.atTop Filter.atTop := by
      -- We can factor out $x / \log x$ from the expression.
      suffices h_factor : Filter.Tendsto (fun x => x / Real.log x * ((b * (1 + c (b * x))) / (1 + Real.log b / Real.log x) - (a * (1 + c (a * x))) / (1 + Real.log a / Real.log x))) Filter.atTop Filter.atTop by
        refine h_factor.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( 1 / b ), Filter.eventually_gt_atTop ( 1 / a ) ] with x hx₁ hx₂ hx₃ ; rw [ Real.log_mul, Real.log_mul ] <;> ring_nf <;> try linarith;
        have hlog_ne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx₁)
        field_simp
      -- As $x \to \infty$, $\frac{x}{\log x} \to \infty$ and $(1 + \frac{\log b}{\log x})^{-1} \to 1$.
      have h_frac_inf : Filter.Tendsto (fun x => x / Real.log x) Filter.atTop Filter.atTop := by
        -- We can use the change of variables $u = \log x$ to transform the limit expression.
        suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp u / u) Filter.atTop Filter.atTop by
          have := h_log.comp Real.tendsto_log_atTop;
          exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
        simpa using Real.tendsto_exp_div_pow_atTop 1;
      -- Since $c(x)$ is $o(1)$, we have $c(bx) \to 0$ and $c(ax) \to 0$ as $x \to \infty$.
      have h_c_zero : Filter.Tendsto (fun x => c (b * x)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x => c (a * x)) Filter.atTop (nhds 0) := by
        exact ⟨ by simpa using hc.1.tendsto_div_nhds_zero.comp ( Filter.tendsto_id.const_mul_atTop ( by linarith ) ), by simpa using hc.1.tendsto_div_nhds_zero.comp ( Filter.tendsto_id.const_mul_atTop ( by linarith ) ) ⟩;
      -- As $x \to \infty$, $(1 + \frac{\log b}{\log x})^{-1} \to 1$ and $(1 + \frac{\log a}{\log x})^{-1} \to 1$.
      have h_inv_one : Filter.Tendsto (fun x => 1 + Real.log b / Real.log x) Filter.atTop (nhds 1) ∧ Filter.Tendsto (fun x => 1 + Real.log a / Real.log x) Filter.atTop (nhds 1) := by
        exact ⟨ by simpa using tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ), by simpa using tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) ⟩;
      apply Filter.Tendsto.atTop_mul_pos;
      exact sub_pos_of_lt ( by nlinarith : b > a );
      · exact h_frac_inf;
      · convert Filter.Tendsto.sub ( Filter.Tendsto.div ( tendsto_const_nhds.mul ( tendsto_const_nhds.add h_c_zero.1 ) ) h_inv_one.1 _ ) ( Filter.Tendsto.div ( tendsto_const_nhds.mul ( tendsto_const_nhds.add h_c_zero.2 ) ) h_inv_one.2 _ ) using 2 <;> norm_num;
    grind

/-
For any `0 < a < b` and `n`, for sufficiently large `k`, there exist `n` distinct primes in `(ak, bk)`.
-/
open Real Filter

lemma exists_distinct_primes_in_interval (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : a < b) :
  ∀ᶠ k in atTop, ∃ (S : Finset ℕ), S.card = n ∧ ∀ p ∈ S, p.Prime ∧ a * k < p ∧ p < b * k := by
    have := prime_counting_interval_tendsto_atTop a b ha hb;
    -- For sufficiently large `k`, the number of primes in `(floor(ak), floor(bk)]` is at least `n + 1`.
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ x ≥ K, (Nat.primeCounting ⌊b * x⌋₊ : ℝ) - (Nat.primeCounting ⌊a * x⌋₊ : ℝ) > n + 1 := by
      exact Filter.eventually_atTop.mp ( this.eventually_gt_atTop _ );
    -- Let `P` be the set of primes in `(floor(ak), floor(bk)]`.
    have hP : ∀ x ≥ K, ∃ P : Finset ℕ, P.card ≥ n + 1 ∧ ∀ p ∈ P, Nat.Prime p ∧ a * x < p ∧ p ≤ b * x := by
      intro x hx
      have hP_card : (Nat.primeCounting ⌊b * x⌋₊ : ℝ) - (Nat.primeCounting ⌊a * x⌋₊ : ℝ) ≥ n + 2 := by
        exact_mod_cast hK x hx;
      have hP_def : Finset.card (Finset.filter Nat.Prime (Finset.Icc (⌊a * x⌋₊ + 1) ⌊b * x⌋₊)) ≥ n + 2 := by
        have hP_def : Finset.card (Finset.filter Nat.Prime (Finset.Icc 1 ⌊b * x⌋₊)) - Finset.card (Finset.filter Nat.Prime (Finset.Icc 1 ⌊a * x⌋₊)) ≥ n + 2 := by
          have hP_def : Finset.card (Finset.filter Nat.Prime (Finset.Icc 1 ⌊b * x⌋₊)) = Nat.primeCounting ⌊b * x⌋₊ ∧ Finset.card (Finset.filter Nat.Prime (Finset.Icc 1 ⌊a * x⌋₊)) = Nat.primeCounting ⌊a * x⌋₊ := by
            norm_num [ Nat.primeCounting ];
            norm_num [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
            exact ⟨ by rw [ Finset.range_eq_Ico ] ; rfl, by rw [ Finset.range_eq_Ico ] ; rfl ⟩;
          exact Nat.le_sub_of_add_le ( by rw [ ← @Nat.cast_le ℝ ] ; push_cast [ hP_def ] ; linarith );
        refine le_trans hP_def ?_;
        refine' Nat.sub_le_of_le_add _;
        rw [ ← Finset.card_union_of_disjoint ];
        · exact Finset.card_mono fun p hp => by cases le_or_gt p ⌊a * x⌋₊ <;> aesop;
        · exact Finset.disjoint_left.mpr fun p hp₁ hp₂ => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hp₂ |>.1 ) ] ;
      exact ⟨ _, by linarith, fun p hp => ⟨ Finset.mem_filter.mp hp |>.2, Nat.lt_of_floor_lt <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1, Nat.floor_le ( show 0 ≤ b * x by exact mul_nonneg ( by linarith ) <| by linarith [ show 0 ≤ x by exact le_trans ( show 0 ≤ K by exact le_of_not_gt fun h => by have := hK 0 ( by linarith ) ; norm_num at this ; linarith ) hx ] ) |> le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ) ⟩ ⟩;
    filter_upwards [ Filter.eventually_ge_atTop K, Filter.eventually_gt_atTop ( b / ( b - a ) ) ] with x hx₁ hx₂;
    obtain ⟨ P, hP₁, hP₂ ⟩ := hP x hx₁;
    -- The number of primes in `P` with `p = bk` is at most 1.
    have hP_eq_bk : (Finset.filter (fun p => p = Nat.floor (b * x)) P).card ≤ 1 := by
      exact Finset.card_le_one.mpr ( by aesop );
    -- So the number of primes in `P` with `p < bk` is at least `|P| - 1 ≥ (n + 1) - 1 = n`.
    have hP_lt_bk : (Finset.filter (fun p => p < Nat.floor (b * x)) P).card ≥ n := by
      have hP_lt_bk : (Finset.filter (fun p => p < Nat.floor (b * x)) P).card + (Finset.filter (fun p => p = Nat.floor (b * x)) P).card = P.card := by
        rw [ Finset.card_filter, Finset.card_filter ];
        rw [ ← Finset.sum_add_distrib, Finset.card_eq_sum_ones ];
        exact Finset.sum_congr rfl fun p hp => by split_ifs <;> first | linarith | cases lt_or_eq_of_le ( Nat.le_of_lt_succ <| show p < ⌊b * x⌋₊ + 1 from Nat.lt_succ_of_le <| Nat.le_floor <| by linarith [ hP₂ p hp ] ) <;> aesop;
      linarith;
    obtain ⟨ S, hS ⟩ := Finset.exists_subset_card_eq hP_lt_bk;
    exact ⟨ S, hS.2, fun p hp => ⟨ hP₂ p ( Finset.mem_filter.mp ( hS.1 hp ) |>.1 ) |>.1, hP₂ p ( Finset.mem_filter.mp ( hS.1 hp ) |>.1 ) |>.2.1, by nlinarith [ hP₂ p ( Finset.mem_filter.mp ( hS.1 hp ) |>.1 ) |>.2.2, show ( p : ℝ ) < ⌊b * x⌋₊ from mod_cast Finset.mem_filter.mp ( hS.1 hp ) |>.2, Nat.floor_le ( show 0 ≤ b * x by nlinarith [ div_nonneg ( show 0 ≤ b by linarith ) ( show 0 ≤ b - a by linarith ) ] ) ] ⟩ ⟩

/--
The density hypothesis follows from the PNT (axiom).
-/
theorem density_proof : DensityHypothesis := by
  intro ε hε;
  -- Apply `exists_distinct_primes_in_interval` to find primes for the first condition.
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, ∀ k ≥ K1, ∃ (S : Finset ℕ), S.card = 2 ∧ ∀ p ∈ S, p.Prime ∧ (k / 2 : ℝ) < p ∧ p < ((1 + ε) * k / 2 : ℝ) := by
    have := exists_distinct_primes_in_interval ( 1 / 2 ) ( ( 1 + ε ) / 2 ) 2 ( by norm_num ) ( by linarith );
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ K1, hK1 ⟩ ; exact ⟨ K1, fun k hk => by obtain ⟨ S, hS₁, hS₂ ⟩ := hK1 k hk; exact ⟨ S, hS₁, fun p hp => ⟨ hS₂ p hp |>.1, by linarith [ hS₂ p hp |>.2.1 ], by linarith [ hS₂ p hp |>.2.2 ] ⟩ ⟩ ⟩ ;
  -- Apply `exists_distinct_primes_in_interval` to find primes for the second condition.
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, ∀ k ≥ K2, ∃ (S : Finset ℕ), S.card = 3 ∧ ∀ p ∈ S, p.Prime ∧ ((1 - ε) * k : ℝ) < p ∧ p < k := by
    have := exists_distinct_primes_in_interval ( 1 - Min.min ε ( 1 / 2 ) ) 1 3 ?_ ?_ <;> norm_num at *;
    · exact ⟨ this.choose, fun k hk => by obtain ⟨ S, hS₁, hS₂ ⟩ := this.choose_spec k hk; exact ⟨ S, hS₁, fun p hp => ⟨ hS₂ p hp |>.1, by nlinarith [ hS₂ p hp |>.2, min_le_left ε ( 1 / 2 ), min_le_right ε ( 1 / 2 ) ], hS₂ p hp |>.2.2 ⟩ ⟩ ⟩;
    · exact hε;
  use Max.max K1 K2; intro k hk; rcases hK1 k ( le_trans ( le_max_left _ _ ) hk ) with ⟨ S1, hS1, hS1' ⟩ ; rcases hK2 k ( le_trans ( le_max_right _ _ ) hk ) with ⟨ S2, hS2, hS2' ⟩ ; simp_all +decide [ Finset.card_eq_two, Finset.card_eq_three ] ;
  rcases hS1 with ⟨ x, y, hxy, rfl ⟩ ; rcases hS2 with ⟨ u, v, huv, w, huw, hvw, rfl ⟩ ; simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ] ;
  exact ⟨ ⟨ x, hS1'.1.2.1, hS1'.1.2.2, y, hS1'.2.2.1, hS1'.2.2.2, hxy, hS1'.1.1, hS1'.2.1 ⟩, ⟨ u, hS2'.1.2.1, hS2'.1.2.2, v, hS2'.2.1.2.1, hS2'.2.1.2.2, w, hS2'.2.2.2.1, hS2'.2.2.2.2, by tauto ⟩ ⟩

/-
The LCM of k consecutive integers starting at x is bounded by (x+k)^k.
-/
lemma lcm_le_pow (x k : ℕ) : (Finset.Icc x (x + k - 1)).lcm id ≤ (x + k) ^ k := by
  -- The least common multiple (LCM) of a set of numbers is at most their product.
  have h_lcm_le_prod : ∀ (S : Finset ℕ), (S.lcm id) ≤ S.prod id := by
    intro S
    induction' S using Finset.induction with p S ih;
    · norm_num +zetaDelta at *;
    · rw [ Finset.lcm_insert, Finset.prod_insert ih ];
      exact Nat.le_trans ( Nat.div_le_self _ _ ) ( Nat.mul_le_mul_left _ ‹_› );
  refine le_trans ( h_lcm_le_prod _ ) ?_;
  erw [ Finset.prod_Ico_eq_prod_range ];
  rcases k with _ | k
  · cases x with
    | zero => simp
    | succ x =>
      have h : x + 1 - 1 + 1 - (x + 1) = 0 := by omega
      simp [h]
  · simp only [show x + (k + 1) - 1 + 1 - x = k + 1 from by omega]
    exact le_trans ( Finset.prod_le_prod' fun _ _ => show x + _ ≤ x + ( k + 1 ) by linarith [ Finset.mem_range.mp ‹_› ] ) ( by norm_num )

/-
The binomial coefficient binom(n, k) is at least (n/k)^k.
-/
lemma choose_ge_pow (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ k) : ((n : ℝ) / k) ^ k ≤ Nat.choose n k := by
  -- Apply the lemma h_prod_ge that states the product of fractions is at least (n/k)^k.
  have h_prod_ge_k : (∏ i ∈ Finset.range k, (n - i : ℝ)) / k ! ≥ (n / k : ℝ) ^ k := by
    have h_prod_ge_k : (∏ i ∈ Finset.range k, (n - i : ℝ)) ≥ (n / k : ℝ) ^ k * k ! := by
      have h_prod_ge_k : ∀ i ∈ Finset.range k, (n - i : ℝ) ≥ (n / k : ℝ) * (k - i) := by
        intros i hi
        field_simp;
        nlinarith only [ show ( i : ℝ ) + 1 ≤ k by norm_cast; linarith [ Finset.mem_range.mp hi ], show ( n : ℝ ) ≥ k by norm_cast ];
      refine' le_trans _ ( Finset.prod_le_prod _ h_prod_ge_k );
      · norm_num [ Finset.prod_mul_distrib ];
        exact le_of_eq ( by rw [ show ( ∏ x ∈ Finset.range k, ( k - x : ℝ ) ) = ( k ! : ℝ ) by exact Nat.recOn k ( by norm_num ) fun n ih => by rw [ Finset.prod_range_succ' ] ; simp +decide [ Nat.factorial_succ, ih, mul_comm, mul_assoc, mul_left_comm ] ] ; ring );
      · exact fun i hi => mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg.2 ( Nat.cast_le.2 ( Finset.mem_range_le hi ) ) );
    exact le_div_iff₀ ( by positivity ) |>.2 h_prod_ge_k;
  convert h_prod_ge_k.le using 1;
  rw [ eq_div_iff ] <;> norm_cast <;> try positivity;
  rw [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
  rw [ Nat.descFactorial_eq_prod_range ];
  rw [ Nat.cast_prod, Finset.prod_congr rfl ] ; intros ; rw [ Int.subNatNat_of_le ] ; linarith [ Finset.mem_range.mp ‹_› ]

/-
The p-adic valuation of binom(n, k) is at most the p-adic valuation of the LCM of the interval (n-k, n].
-/
lemma valuation_choose_le_valuation_lcm (n k : ℕ) (p : ℕ) (hp : p.Prime) :
  padicValNat p (Nat.choose n k) ≤ padicValNat p ((Finset.Icc (n - k + 1) n).lcm id) := by
    by_cases hk : k ≤ n;
    · have h_val : padicValNat p (Nat.choose n k) = ∑ i ∈ Finset.Icc 1 (Nat.log p n), (Nat.floor ((n : ℝ) / (p ^ i)) - Nat.floor ((k : ℝ) / (p ^ i)) - Nat.floor (((n - k) : ℝ) / (p ^ i))) := by
        haveI := Fact.mk hp;
        rw [ padicValNat_choose ];
        any_goals exact Nat.lt_succ_self _;
        · have h_sum_eq : ∀ i ∈ Finset.Icc 1 (Nat.log p n), ⌊(n : ℝ) / p ^ i⌋₊ - ⌊(k : ℝ) / p ^ i⌋₊ - ⌊((n - k) : ℝ) / p ^ i⌋₊ = if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0 := by
            intro i hi
            have h_floor_eq : ⌊(n : ℝ) / p ^ i⌋₊ = n / p ^ i ∧ ⌊(k : ℝ) / p ^ i⌋₊ = k / p ^ i ∧ ⌊((n - k) : ℝ) / p ^ i⌋₊ = (n - k) / p ^ i := by
              norm_cast;
              exact ⟨ by rw [ Nat.floor_div_natCast, Nat.floor_natCast ], by rw [ Nat.floor_div_natCast, Nat.floor_natCast ], by rw [ Nat.floor_div_natCast, Nat.floor_natCast ] ⟩;
            split_ifs <;> simp_all +decide [ Nat.div_eq_of_lt, Nat.mod_eq_of_lt ];
            · rw [ show n = k + ( n - k ) by rw [ Nat.add_sub_of_le hk ] ] ; norm_num [ Nat.add_div, hp.pos ];
              split_ifs ; omega;
            · rw [ show n = k + ( n - k ) by rw [ Nat.add_sub_of_le hk ] ] ; norm_num [ Nat.add_div ( pow_pos hp.pos _ ) ] ;
              split_ifs <;> omega;
          rw [ Finset.sum_congr rfl h_sum_eq, Finset.sum_ite ] ; aesop;
        · linarith;
      -- The term in the sum is 1 if there is a carry at position $i$, and 0 otherwise.
      have h_carry : ∀ i ∈ Finset.Icc 1 (Nat.log p n), (Nat.floor ((n : ℝ) / (p ^ i)) - Nat.floor ((k : ℝ) / (p ^ i)) - Nat.floor (((n - k) : ℝ) / (p ^ i))) ≤ if ∃ j ∈ Finset.Icc (n - k + 1) n, p ^ i ∣ j then 1 else 0 := by
        intro i hi
        set m := Nat.floor ((n : ℝ) / (p ^ i))
        set l := Nat.floor ((k : ℝ) / (p ^ i))
        set r := Nat.floor (((n - k) : ℝ) / (p ^ i))
        have h_floor : m = n / p ^ i ∧ l = k / p ^ i ∧ r = (n - k) / p ^ i := by
          norm_num +zetaDelta at *;
          norm_cast;
          exact ⟨ by rw [ Nat.floor_div_natCast, Nat.floor_natCast ], by rw [ Nat.floor_div_natCast, Nat.floor_natCast ], by rw [ Nat.floor_div_natCast, Nat.floor_natCast ] ⟩;
        split_ifs <;> simp_all +decide [ Nat.div_eq_of_lt ];
        · rw [ show n = n - k + k by rw [ Nat.sub_add_cancel hk ] ] ; norm_num [ Nat.add_div, hp.pos ] ;
          grind;
        · rw [ Nat.sub_sub, tsub_eq_zero_iff_le.mpr ];
          rw [ Nat.le_iff_lt_or_eq ];
          refine' lt_or_eq_of_le ( Nat.le_of_lt_succ _ );
          rw [ Nat.div_lt_iff_lt_mul <| pow_pos hp.pos _ ];
          contrapose! h_floor;
          exact fun _ _ => False.elim <| ‹∀ x : ℕ, n - k + 1 ≤ x → x ≤ n → ¬p ^ i ∣ x› ( ( k / p ^ i + ( n - k ) / p ^ i + 1 ) * p ^ i ) ( by nlinarith [ Nat.div_add_mod k ( p ^ i ), Nat.mod_lt k ( pow_pos hp.pos i ), Nat.div_add_mod ( n - k ) ( p ^ i ), Nat.mod_lt ( n - k ) ( pow_pos hp.pos i ), Nat.sub_add_cancel hk ] ) ( by nlinarith [ Nat.div_add_mod k ( p ^ i ), Nat.mod_lt k ( pow_pos hp.pos i ), Nat.div_add_mod ( n - k ) ( p ^ i ), Nat.mod_lt ( n - k ) ( pow_pos hp.pos i ), Nat.sub_add_cancel hk ] ) <| dvd_mul_left _ _;
      -- The maximum $i$ where there's a carry is at most the maximum $i$ where $p^i$ divides the LCM.
      have h_max_i : ∀ i ∈ Finset.Icc 1 (Nat.log p n), (∃ j ∈ Finset.Icc (n - k + 1) n, p ^ i ∣ j) → i ≤ Nat.factorization (Finset.lcm (Finset.Icc (n - k + 1) n) id) p := by
        intros i hi h_div
        obtain ⟨j, hj₁, hj₂⟩ := h_div
        have h_div_lcm : p ^ i ∣ Finset.lcm (Finset.Icc (n - k + 1) n) id := by
          exact dvd_trans hj₂ ( Finset.dvd_lcm hj₁ );
        rw [ ← Nat.factorization_le_iff_dvd ] at h_div_lcm <;> aesop;
      have h_sum_carry : ∑ i ∈ Finset.Icc 1 (Nat.log p n), (if ∃ j ∈ Finset.Icc (n - k + 1) n, p ^ i ∣ j then 1 else 0) ≤ Nat.factorization (Finset.lcm (Finset.Icc (n - k + 1) n) id) p := by
        simp +zetaDelta at *;
        exact le_trans ( Finset.card_le_card fun x hx => Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, h_max_i x ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) _ ( Finset.mem_filter.mp hx |>.2.choose_spec.1.1 ) ( Finset.mem_filter.mp hx |>.2.choose_spec.1.2 ) ( Finset.mem_filter.mp hx |>.2.choose_spec.2 ) ⟩ ) ( by simp );
      convert h_sum_carry.trans' ( Finset.sum_le_sum h_carry ) using 1;
      rw [ Nat.factorization_def ] ; aesop;
    · simp +decide [ Nat.choose_eq_zero_of_lt ( not_le.mp hk ) ]

/-
The binomial coefficient binom(y+k, k+1) divides the LCM of the interval [y, y+k].
-/
lemma choose_dvd_lcm (y k : ℕ) : Nat.choose (y + k) (k + 1) ∣ (Finset.Icc y (y + k)).lcm id := by
  by_cases hy : y = 0;
  · simp +decide [ hy, Nat.choose_eq_zero_of_lt ];
  · -- Apply the lemma `valuation_choose_le_valuation_lcm` with $n = y + k$ and $m = k + 1$.
    have h_val : ∀ p, p.Prime → padicValNat p (Nat.choose (y + k) (k + 1)) ≤ padicValNat p ((Finset.Icc y (y + k)).lcm id) := by
      convert valuation_choose_le_valuation_lcm ( y + k ) ( k + 1 ) using 1;
      grind;
    rw [ ← Nat.factorization_le_iff_dvd ];
    · intro p; by_cases hp : Nat.Prime p <;> simp_all +decide [ Nat.factorization ] ;
    · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith [ Nat.pos_of_ne_zero hy ] ;
    · norm_num [ Finset.lcm_eq_zero_iff ];
      assumption

/-
The statement is false because the LCM of the y-interval (length k+1) grows asymptotically faster than the LCM of the x-interval (length k).
-/
theorem infinitely_many_examples_false :
  ¬ (∀ C : ℝ, C ≥ 1 →
  ∃ K, ∀ k ≥ K,
  ∀ X : ℕ, ∃ x y : ℕ,
    X < x ∧ x < y ∧ y > x + k ∧
    lcm_real (Finset.Icc x (x + k - 1)) > C * lcm_real (Finset.Icc y (y + k))) := by
      push Not;
      refine' ⟨ 1, by norm_num, _ ⟩;
      intros x
      obtain ⟨k, hk⟩ : ∃ k ≥ x, ∃ X : ℕ, ∀ x y : ℕ, X < x → x < y → y > x + k → Nat.choose (y + k) (k + 1) > (x + k) ^ k := by
        have h_choose_growth : ∀ k ≥ 1, ∃ X : ℕ, ∀ x y : ℕ, X < x → x < y → y > x + k → Nat.choose (y + k) (k + 1) > (x + k) ^ k := by
          intro k hk
          have h_choose_growth : ∀ y : ℕ, y > k → Nat.choose (y + k) (k + 1) ≥ (y : ℝ) ^ (k + 1) / (k + 1) ^ (k + 1) := by
            intro y hy
            have h_choose_ge_pow : (Nat.choose (y + k) (k + 1) : ℝ) ≥ ((y + k) / (k + 1)) ^ (k + 1) := by
              have := choose_ge_pow ( y + k ) ( k + 1 ) ( by linarith ) ( by linarith ) ; aesop;
            exact le_trans ( by rw [ div_pow ] ; gcongr ; norm_cast ; linarith ) h_choose_ge_pow;
          -- Choose $X$ such that for all $x > X$, $(x + k)^k < \frac{(x + k + 1)^{k + 1}}{(k + 1)^{k + 1}}$.
          obtain ⟨X, hX⟩ : ∃ X : ℕ, ∀ x : ℕ, x > X → (x + k : ℝ) ^ k < (x + k + 1) ^ (k + 1) / (k + 1) ^ (k + 1) := by
            have h_choose_growth : Filter.Tendsto (fun x : ℕ => ((x + k + 1 : ℝ) ^ (k + 1) / (k + 1) ^ (k + 1)) / ((x + k : ℝ) ^ k)) Filter.atTop Filter.atTop := by
              -- We can factor out $(x + k)^k$ from the numerator and denominator.
              suffices h_factor : Filter.Tendsto (fun x : ℕ => ((x + k + 1 : ℝ) / (x + k)) ^ k * ((x + k + 1 : ℝ) / ((k + 1) ^ (k + 1)))) Filter.atTop Filter.atTop by
                convert h_factor using 2 ; ring_nf;
                simpa only [ mul_assoc, ← mul_pow ] using by ring;
              -- We can simplify the expression inside the limit.
              suffices h_simplify : Filter.Tendsto (fun x : ℕ => (1 + 1 / (x + k : ℝ)) ^ k * ((x + k + 1 : ℝ) / ((k + 1) ^ (k + 1)))) Filter.atTop Filter.atTop by
                field_simp;
                refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ one_add_div ( by positivity ) ] ; ring );
              -- We can use the fact that $(1 + 1 / (x + k))^k$ tends to $1$ as $x$ tends to infinity.
              have h_exp : Filter.Tendsto (fun x : ℕ => (1 + 1 / (x + k : ℝ)) ^ k) Filter.atTop (nhds 1) := by
                exact le_trans ( Filter.Tendsto.pow ( tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) _ ) <| by norm_num;
              apply Filter.Tendsto.pos_mul_atTop;
              exacts [ zero_lt_one, h_exp, Filter.Tendsto.atTop_div_const ( by positivity ) ( Filter.tendsto_atTop_add_const_right _ _ <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ];
            have := h_choose_growth.eventually_gt_atTop 1;
            rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ X, hX ⟩ ; exact ⟨ X, fun x hx => by have := hX x hx.le; rw [ lt_div_iff₀ ( by positivity ) ] at this; linarith ⟩ ;
          use X + k + 1;
          intros x y hx hy hxy
          have h_choose : Nat.choose (y + k) (k + 1) ≥ (y : ℝ) ^ (k + 1) / (k + 1) ^ (k + 1) := by
            exact h_choose_growth y ( by linarith );
          contrapose! h_choose;
          refine' lt_of_le_of_lt ( Nat.cast_le.mpr h_choose ) _;
          refine' lt_of_lt_of_le ( mod_cast hX x ( by linarith ) ) _;
          field_simp;
          norm_cast ; rw [ mul_comm ] ; gcongr ; linarith;
        exact ⟨ x + 1, by linarith, h_choose_growth _ <| by linarith ⟩;
      obtain ⟨ X, hX ⟩ := hk.2; use k, hk.1, X; intros x y hx hy hxy; have := hX x y hx hy hxy; norm_num at *; (
      -- By combining the inequalities from hX and the bounds on the LCMs, we get the desired result.
      have h_lcm_bound : (Finset.Icc x (x + k - 1)).lcm id ≤ (x + k) ^ k ∧ (Finset.Icc y (y + k)).lcm id ≥ (y + k).choose (k + 1) := by
        exact ⟨ lcm_le_pow x k, Nat.le_of_dvd ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ( choose_dvd_lcm y k ) ⟩;
      convert h_lcm_bound.1.trans this.le |> le_trans <| h_lcm_bound.2 using 1;
      unfold lcm_real; aesop;);

/-- The least common multiple of ${n+1, \dotsc, n+k}$. -/
def lcmInterval {α : Type*} [AddMonoid α] [CommMonoidWithZero α] [IsCancelMulZero α]
    [NormalizedGCDMonoid α] [Preorder α] [LocallyFiniteOrder α] (n k : α) : α :=
  (Finset.Ioc n (n + k)).lcm id

lemma lcmInterval_ge_choose (n k : ℕ) : lcmInterval n k ≥ Nat.choose (n + k) k := by
  have h_eq : lcmInterval n k = (Finset.Icc (n + 1) (n + k)).lcm id := by
    exact congr_arg _ ( Finset.ext fun x => by aesop );
  have := choose_dvd_lcm ( n + 1 ) ( k - 1 ) ; rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.choose_succ_succ, add_assoc ] ;
  · linarith;
  · exact Nat.le_of_dvd ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ( by simpa only [ add_comm, add_left_comm, add_assoc ] using this )

theorem lcmInterval_growth : ∀ᶠ k in Filter.atTop, ∃ N, ∀ n ≥ N, ∀ m ≥ n + k, lcmInterval m (k + 1) > lcmInterval n k := by
  refine' Filter.eventually_atTop.mpr ⟨ 1, _ ⟩;
  -- Fix a $k \ge 1$.
  intro k hk
  -- Consider the expression $\binom{n+2k+1}{k+1} - (n+k+1)^k$.
  suffices h_suff : ∃ N, ∀ n ≥ N, Nat.choose (n + 2 * k + 1) (k + 1) > (n + k + 1) ^ k by
    -- By combining the inequalities from h_suff and the properties of lcmInterval, we can conclude the proof.
    obtain ⟨N, hN⟩ := h_suff;
    use N;
    intro n hn m hm;
    have h_lcm_m : lcmInterval m (k + 1) ≥ Nat.choose (n + 2 * k + 1) (k + 1) := by
      have h_lcm_m : lcmInterval m (k + 1) ≥ Nat.choose (m + k + 1) (k + 1) := by
        exact lcmInterval_ge_choose m (k + 1);
      exact le_trans ( Nat.choose_le_choose _ ( by linarith ) ) h_lcm_m
    have h_lcm_n : lcmInterval n k ≤ (n + k + 1) ^ k := by
      convert lcm_le_pow ( n + 1 ) k using 1;
      · exact congr_arg₂ _ ( Finset.ext fun x => by aesop ) rfl;
      · ring
    exact lt_of_le_of_lt (by
    exact h_lcm_n) (h_lcm_m.trans_lt' (hN n hn));
  -- We can bound the binomial coefficient from below by $\frac{(n+k+1)^{k+1}}{(k+1)!}$.
  have h_binom_bound : ∀ n ≥ k, Nat.choose (n + 2 * k + 1) (k + 1) ≥ (n + k + 1) ^ (k + 1) / (k + 1)! := by
    intro n hn
    have h_binom_bound : Nat.choose (n + 2 * k + 1) (k + 1) ≥ (n + k + 1) ^ (k + 1) / (k + 1)! := by
      have h_prod : ∏ i ∈ Finset.range (k + 1), (n + 2 * k + 1 - i) ≥ (n + k + 1) ^ (k + 1) := by
        exact le_trans ( by norm_num ) ( Finset.prod_le_prod' fun i hi => show n + 2 * k + 1 - i ≥ n + k + 1 from Nat.le_sub_of_add_le <| by linarith [ Finset.mem_range.mp hi ] )
      have h_binom_bound : Nat.choose (n + 2 * k + 1) (k + 1) * (k + 1)! = ∏ i ∈ Finset.range (k + 1), (n + 2 * k + 1 - i) := by
        rw [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
        rw [ Nat.descFactorial_eq_prod_range ];
      exact Nat.div_le_of_le_mul <| by linarith;
    exact h_binom_bound;
  -- Since $(k+1)!$ is a constant, for sufficiently large $n$, $(n+k+1)^{k+1} / (k+1)!$ will be greater than $(n+k+1)^k$.
  have h_const_bound : ∃ N, ∀ n ≥ N, (n + k + 1) ^ (k + 1) / (k + 1)! > (n + k + 1) ^ k := by
    refine' ⟨ ( k + 1 ) ! + 1, fun n hn => Nat.le_div_iff_mul_le ( Nat.factorial_pos _ ) |>.2 _ ⟩;
    rw [ pow_succ' ];
    nlinarith [ Nat.factorial_pos ( k + 1 ), Nat.pow_le_pow_right ( by linarith : 1 ≤ n + k + 1 ) hk ];
  exact ⟨ Nat.max k h_const_bound.choose, fun n hn => lt_of_lt_of_le ( h_const_bound.choose_spec n ( le_trans ( le_max_right _ _ ) hn ) ) ( h_binom_bound n ( le_trans ( le_max_left _ _ ) hn ) ) ⟩

/--
The main theorem holds, conditional on the PNT (axiom)
-/
theorem main_theorem_given_pnt : MainTheoremStatement := by
  -- Apply the main theorem with the density hypothesis to conclude the proof.
  apply main_theorem; exact density_proof

/--
The main theorem spelled out, just for concreteness.  As before, it's proven assuming
the PNT as an axiom.
-/
theorem main_theorem_expanded :
  ∀ C : ℝ, C ≥ 1 →
  ∃ K, ∀ k ≥ K, ∃ x y : ℕ,
    0 < x ∧ x < y ∧ y > x + k ∧
    lcm_real (Finset.Icc x (x + k - 1)) > C * lcm_real (Finset.Icc y (y + k)) := by
  -- The main theorem holds, conditional on the PNT (axiom) by applying the `main_theorem` theorem.
  apply main_theorem_given_pnt

theorem erdos_678_cambie_strong :
  ∃ K, ∀ k ≥ K,
  ∃ x y : ℕ,
    0 < x ∧ x < y ∧ y > x + k ∧
    lcm_real (Finset.Icc x (x + k - 1)) > lcm_real (Finset.Icc y (y + k)) := by
  -- Apply the main theorem to conclude the proof.
  obtain ⟨K, hK⟩ := main_theorem_given_pnt 1 (by norm_num);
  -- Since $1 * lcm_real (Finset.Icc y (y + k)) = lcm_real (Finset.Icc y (y + k))$, we can conclude the proof.
  use K
  intro k hk
  obtain ⟨x, y, hx_pos, hx_lt_y, hy_gt_xk, h_lcm⟩ := hK k hk
  use x, y
  aesop

theorem not_erdos_678_fc :
    ¬(∀ᶠ k in atTop, {(m, n) | n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Infinite) := by
  -- By `lcmInterval_growth`, for large enough $k$, there are no such pairs $(m, n)$ in $S_k$.
  have h_finite : ∀ᶠ k in Filter.atTop, ∃ N, ∀ n ≥ N, ∀ m ≥ n + k, lcmInterval m (k + 1) > lcmInterval n k := by
    exact lcmInterval_growth;
  intro h_inf;
  obtain ⟨ k, hk ⟩ := h_finite.and h_inf |> fun h => h.exists;
  obtain ⟨ ⟨ N, hN ⟩, h_inf ⟩ := hk;
  -- For a fixed $n < N$, the condition $\text{lcmInterval}(m, k+1) < \text{lcmInterval}(n, k)$ implies $m+1 < \text{lcmInterval}(n, k)$, so there are finitely many such $m$.
  have h_finite_fixed_n : ∀ n < N, Set.Finite {m | lcmInterval m (k + 1) < lcmInterval n k} := by
    intro n hn
    have h_bound : ∀ m, lcmInterval m (k + 1) ≥ m + 1 := by
      intro m; exact (by
      exact Nat.le_of_dvd ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ( Finset.dvd_lcm ( Finset.mem_Ioc.mpr ⟨ by linarith, by linarith ⟩ ) ));
    exact Set.finite_iff_bddAbove.mpr ⟨ lcmInterval n k, fun m hm => by linarith [ h_bound m, hm.out ] ⟩;
  -- Therefore, $S_k$ is a finite union of finite sets, so it is finite.
  have h_finite_union : Set.Finite {x : ℕ × ℕ | x.2 < N ∧ x.2 + k ≤ x.1 ∧ lcmInterval x.1 (k + 1) < lcmInterval x.2 k} := by
    exact Set.Finite.subset ( Set.Finite.prod ( Set.Finite.biUnion ( Set.finite_lt_nat N ) fun n hn => h_finite_fixed_n n hn ) ( Set.finite_lt_nat N ) ) fun x hx => by aesop;
  exact h_inf <| h_finite_union.subset fun x hx => ⟨ lt_of_not_ge fun hx' => by linarith [ hN _ hx' _ hx.1, hx.2 ], hx.1, hx.2 ⟩

theorem erdos_678 :
    {(k, m, n) | 3 ≤ k ∧ n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Infinite := by
  -- Assume that for every $k \geq 3$ there exists an $M_k$ such that if $n \geq M_k$ then $\mathrm{lcm}(n+k+1,\ldots,n+2k+1) > \mathrm{lcm}(n+1,\ldots,n+k)$.
  by_contra h_contra;
  -- If the set were finite, there would be a maximum k, say K. For all k ≥ K, the inequality wouldn't hold. But we know that for large k, the LCM of [n+k+1, n+2k+1] is larger than that of [n+1, n+k]. So if the set were finite, we could find a k larger than K where the inequality holds, which contradicts the assumption. Therefore, the set must be infinite.
  obtain ⟨K, hK⟩ : ∃ K, ∀ k ≥ K, ∀ n m, n + k ≤ m → lcmInterval m (k + 1) ≥ lcmInterval n k := by
    -- Since the set is finite, there exists a maximum k, say K_max, in the set.
    obtain ⟨K_max, hK_max⟩ : ∃ K_max, ∀ k ≥ K_max, ∀ n m, n + k ≤ m → lcmInterval m (k + 1) ≥ lcmInterval n k := by
      have h_finite : Set.Finite {k | ∃ n m, 3 ≤ k ∧ n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k} := by
        exact Set.Finite.subset ( Set.not_infinite.mp h_contra |> Set.Finite.image fun x => x.1 ) fun x hx => by aesop;
      obtain ⟨ K_max, hK_max ⟩ := h_finite.bddAbove;
      exact ⟨ K_max + 3, fun k hk n m hnm => not_lt.1 fun contra => by linarith [ hK_max ⟨ n, m, by linarith, hnm, contra ⟩ ] ⟩;
    use K_max + 3, fun k hk n m hnm => hK_max k ( by linarith ) n m hnm;
  -- Apply the valuation_ineq_good_p_aux lemma to obtain a contradiction with the assumption that the set is finite.
  have h_contradiction : ∃ k ≥ K, ∃ n m : ℕ, n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k := by
    -- Apply the main theorem to obtain the existence of such a k.
    obtain ⟨k, hk⟩ : ∃ k ≥ K, ∃ n m : ℕ, n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k := by
      have := main_theorem_given_pnt
      -- Apply the main theorem to obtain the existence of such a k, n, and m.
      obtain ⟨k, hk⟩ := this 1 (by norm_num);
      simp +zetaDelta at *;
      obtain ⟨ x, hx, y, hy, hxy, h ⟩ := hk ( k + K + 3 ) ( by linarith ) ; use k + K + 3 ; simp_all +decide [ lcmInterval, show ∀ a b : ℕ, Finset.Ioc a b = Finset.Icc (a + 1) b from fun a b => by rw [show a + 1 = Order.succ a from rfl, Finset.Icc_succ_left_eq_Ioc] ] ;
      refine' ⟨ by linarith, x - 1, y - 1, _, _ ⟩ <;> rcases x with ( _ | x ) <;> rcases y with ( _ | y ) <;> norm_num at * <;> try linarith;
      convert h using 1;
      unfold lcm_real; norm_cast; simp +arith +decide [ show ∀ a b : ℕ, Finset.Icc (a + 1) b = Finset.Ioc a b from fun a b => by rw [show a + 1 = Order.succ a from rfl, Finset.Icc_succ_left_eq_Ioc] ] ;
    exact ⟨ k, hk ⟩;
  obtain ⟨ k, hk₁, n, m, hnm, hkm ⟩ := h_contradiction; exact not_le_of_gt hkm <| hK k hk₁ n m hnm;

end

#print axioms erdos_678
-- 'Erdos678.erdos_678' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos678
