import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos21

attribute [local fun_prop] Real.continuous_fourierChar
attribute [local fun_prop] measurable_coe_nnreal_ennreal

/-
# Problem Description

Erdős Problem 21 ($500), conjectured by Erdős and Lovász. Let `f(n)` be minimal such that
there is an intersecting family `𝓕` of `n`-sets with `|𝓕| = f(n)` for which every set `S`
with `|S| ≤ n - 1` is disjoint from at least one member. Is `f(n) ≪ n`? `erdos_21` proves
that it is. Solved by Kahn, after Erdős--Lovász gave `(8/3)n - 3 ≤ f(n) ≪ n^(3/2) log n` and
Kahn improved the upper bound to `n log n`.

`erdosLovaszF n` is `sInf {m | ∃ F, IsErdosLovaszFamily n F ∧ F.card = m}`, where
`IsErdosLovaszFamily n F` is `IsUniform n F ∧ IsIntersecting F ∧ AvoidsAllSmallSets n F`,
and the conclusion is `∃ C N, ∀ n ≥ N, erdosLovaszF n ≤ C * n`, a natural-number rendering
of `≪`.

A caveat on reading the statement. `sInf` on `ℕ` returns `0` on an empty set, so a bound of
the form `erdosLovaszF n ≤ C * n` would hold vacuously for any `n` at which no such family
existed; at `n = 0` the candidate set is indeed empty. This is not what happens here. The
proof runs through `erdosLovaszF_le_of_dualConstruction`, which applies
`dualFamily_isErdosLovaszFamily` to *construct* a family `H.dualFamily` witnessing
`IsErdosLovaszFamily n` and then bounds its cardinality, so the infimum is taken over a
nonempty set exactly where the theorem asserts the bound. Families also exist for every
`n ≥ 1` independently of the construction — for `n = 1`, `{{x}}` is one.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` -/

section

open Filter Real

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

theorem WienerIkeharaTheorem'' (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) :=
  WienerIkeharaTheorem' hpos hf (auto_cheby (f := f) (A := A) (G := G) hpos hf hG hG') hG hG'

end auto_cheby

theorem WeakPNT_AP_prelim {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : Nat.Coprime a q) (ha' : a < q) :
    ∃ G: ℂ → ℂ, (ContinuousOn G {s | 1 ≤ s.re}) ∧
    (Set.EqOn G (fun s ↦ LSeries (fun n ↦ if n % q = a then Λ n else 0) s - 1 /
      ((Nat.totient q) * (s - 1))) {s | 1 < s.re}) := by
  have : NeZero q := NeZero.of_pos hq
  have hG : ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ Set.EqOn G
      (fun s ↦ LSeries (fun n ↦ if (n : ZMod q) = a then Λ n else 0) s - (q.totient : ℂ)⁻¹ / (s - 1)) {s | 1 < s.re} := by
    use vonMangoldt.LFunctionResidueClassAux (a : ZMod q), vonMangoldt.continuousOn_LFunctionResidueClassAux (q := q) (a := a)
    have := vonMangoldt.eqOn_LFunctionResidueClassAux ((ZMod.isUnit_iff_coprime a q).mpr ha)
    convert this using 6; split <;> simp_all
  convert hG using 6
  · simp [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha']
  · rw [inv_eq_one_div, div_div]

/-- The von Mangoldt function divided by `n ^ s` is summable for `s > 1`. -/
lemma summable_vonMangoldt_div_rpow {s : ℝ} (hs : 1 < s) : Summable (fun n ↦ Λ n / n ^ s) := by
  have h_log_bound : ∀ n : ℕ, (Λ n : ℝ) ≤ Real.log n := fun n ↦ vonMangoldt_le_log
  suffices h_log_sum : Summable fun n : ℕ ↦ Real.log n / (n : ℝ) ^ s by
    exact .of_nonneg_of_le (fun n ↦ div_nonneg vonMangoldt_nonneg (by positivity))
      (fun n ↦ div_le_div_of_nonneg_right (h_log_bound n) (by positivity)) h_log_sum
  have h_log_le_n_eps : ∀ ε > 0, ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n / (n : ℝ) ^ s ≤ C * (n : ℝ) ^ (ε - s) := by
    intro ε hε_pos
    obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n ≤ C * (n : ℝ) ^ ε := by
      refine ⟨1 / ε, by positivity, fun n hn ↦ ?_⟩
      have := log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) ^ ε)
      rw [log_rpow (by positivity)] at this
      nlinarith [rpow_pos_of_pos (by positivity : 0 < (n : ℝ)) ε, mul_div_cancel₀ 1 hε_pos.ne']
    refine ⟨C, hC_pos, fun n hn ↦ ?_⟩
    rw [rpow_sub (by positivity)]
    exact le_trans (div_le_div_of_nonneg_right (hC n hn) (by positivity)) (by rw [div_eq_mul_inv]; ring_nf; norm_num)
  obtain ⟨C, _, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n / (n : ℝ) ^ s ≤ C * (n : ℝ) ^ ((s - 1) / 2 - s) :=
    h_log_le_n_eps ((s - 1) / 2) (by linarith)
  rw [← summable_nat_add_iff 2]
  exact Summable.of_nonneg_of_le (fun n ↦ div_nonneg (log_nonneg (by norm_cast; omega))
    (rpow_nonneg (by positivity) _)) (fun n ↦ hC _ (by omega)) (Summable.mul_left _ <| by
      simpa using summable_nat_add_iff 2 |>.2 <| summable_nat_rpow.2 <| by linarith)

theorem WeakPNT_AP {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
    Tendsto (fun N ↦ cumsum (fun n ↦ if n % q = a then Λ n else 0) N / N) atTop (𝓝 (1 / q.totient)) := by
  have h_summable : ∀ s : ℝ, 1 < s → Summable (fun n ↦ (if n % q = a then Λ n else 0) / n ^ s) := by
    intro s hs
    refine .of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) (summable_vonMangoldt_div_rpow hs)
    · split_ifs <;> positivity
    · split_ifs <;> norm_num; exact div_nonneg vonMangoldt_nonneg (by positivity)
  obtain ⟨G, hG₁, hG₂⟩ := WeakPNT_AP_prelim hq ha ha'
  convert WienerIkeharaTheorem'' _ _ _ _ using 1
  · use G
  · intro n
    simp_all only [ge_iff_le, one_div, mul_inv_rev, Pi.ofNat_apply]
    split
    next h => subst h; simp_all only [vonMangoldt_nonneg]
    next h => simp_all only [le_refl]
  · intro σ' hσ'
    specialize h_summable σ' hσ'
    simp_all only [ge_iff_le, one_div, mul_inv_rev]
    convert h_summable using 1
    ext
    simp only [nterm, norm_real, norm_eq_abs]
    ring_nf
    split_ifs <;> simp [*, mul_comm]
  · assumption
  · convert hG₂ using 3
    · exact tsum_congr fun n ↦ by cases n <;> aesop
    · norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Consequences.lean` -/

section
set_option lang.lemmaCmd true

open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

/-- If u ~ v and u-w = o(v) then w ~ v. -/
private theorem _root_.Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact Asymptotics.IsEquivalent.sub_isLittleO huv hwu

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

/-- `(⌊x⌋₊ + 1) / x → 1` as `x → ∞`. -/
lemma tendsto_floor_add_one_div_self : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ + 1 : ℝ) / x) atTop (nhds 1) := by
  have h := Asymptotics.isEquivalent_nat_floor (R := ℝ)
  have h' : IsEquivalent atTop (fun x : ℝ ↦ (⌊x⌋₊ : ℝ) + 1) _root_.id :=
    h.add_isLittleO (isLittleO_const_id_atTop 1)
  have hne : ∀ᶠ x : ℝ in atTop, _root_.id x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact ne_of_gt hx
  convert (isEquivalent_iff_tendsto_one hne).mp h' using 1
  ext x
  rfl

/-- `x =Θ x / c` for nonzero constant `c`. -/
lemma isTheta_self_div_const {c : ℝ} (hc : c ≠ 0) : (fun x : ℝ ↦ x) =Θ[atTop] fun x ↦ x / c := by
  have : (fun x : ℝ ↦ x / c) = fun x ↦ c⁻¹ * x := by ext x; ring
  exact this ▸ (isTheta_const_mul_left (inv_ne_zero hc)).mpr (isTheta_refl ..) |>.symm

/-- Filtered sum over `Iic n` equals filtered sum over `Icc 1 n` for primes. -/
lemma filter_prime_Iic_eq_Icc (n : ℕ) : filter Prime (Iic n) = filter Prime (Icc 1 n) := by
  ext p; simp only [mem_filter, mem_Iic, mem_Icc, and_congr_left_iff]
  exact fun hp ↦ ⟨fun h ↦ ⟨hp.one_lt.le, h⟩, fun ⟨_, h⟩ ↦ h⟩

/-- `Icc 0 n = insert 0 (Icc 1 n)` -/
lemma Icc_zero_eq_insert (n : ℕ) : Icc 0 n = insert 0 (Icc 1 n) := by
  ext m; simp [mem_Icc]; omega

-- one could also consider adding a version with p < x instead of p \leq x

noncomputable def R (x : ℝ) : ℝ := Psi x - x

theorem chebyshev_asymptotic_pnt
    {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
    (fun x ↦ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0) ~[atTop]
      fun x ↦ x / q.totient := by
  let ψ_aq : ℝ → ℝ := fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, if n % q = a then Λ n else 0
  have htot_pos : (0 : ℝ) < q.totient := cast_pos.mpr (totient_pos.mpr hq)
  have hψ_equiv : ψ_aq ~[atTop] fun x ↦ x / q.totient := by
    have hW := WeakPNT_AP hq ha ha'
    simp only [cumsum, ← Iio_eq_range] at hW
    have hψ_eq x : ψ_aq x = ∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0 := by
      simp only [ψ_aq, show Icc 1 ⌊x⌋₊ = (Iio (⌊x⌋₊ + 1)).filter (1 ≤ ·) by
        ext n; simp [mem_Icc, mem_filter]; tauto, sum_filter]
      refine sum_congr rfl fun n _ ↦ ?_
      by_cases hn : 1 ≤ n <;> simp only [hn, ↓reduceIte]
      push Not at hn; interval_cases n; simp
    refine (isEquivalent_iff_tendsto_one ?_).mpr ?_
    · filter_upwards [eventually_ge_atTop 1] with x hx; exact div_ne_zero (by linarith) htot_pos.ne'
    have hlim1 : Tendsto (fun x : ℝ ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) /
        (⌊x⌋₊ + 1 : ℝ)) atTop (nhds (1 / q.totient)) := by
      have heq : (fun x : ℝ ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) /
          (⌊x⌋₊ + 1 : ℝ)) = (fun N ↦ (∑ n ∈ Iio N, if n % q = a then Λ n else 0) / N) ∘
          (fun x : ℝ ↦ ⌊x⌋₊ + 1) := by ext x; simp [Function.comp_apply]
      exact heq ▸ hW.comp ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)
    have hgoal_eq : (ψ_aq / fun x ↦ x / (q.totient : ℝ)) =
        fun x ↦ ψ_aq x / x * q.totient := by ext x; simp only [Pi.div_apply, div_div_eq_mul_div]; ring
    rw [hgoal_eq, show (1 : ℝ) = 1 / q.totient * 1 * q.totient by field_simp]
    refine Tendsto.mul ?_ tendsto_const_nhds
    have heq' : (fun x ↦ ψ_aq x / x) =ᶠ[atTop]
        fun x ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) / (⌊x⌋₊ + 1 : ℝ) * ((⌊x⌋₊ + 1 : ℝ) / x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [hψ_eq]; field_simp
    exact Tendsto.congr' heq'.symm (hlim1.mul tendsto_floor_add_one_div_self)
  refine hψ_equiv.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, eventually_atTop.mpr ⟨2, fun x hx ↦ ?_⟩⟩
    simp only [Pi.sub_apply, norm_eq_abs, one_mul]
    have hdiff_nonneg : 0 ≤ ψ_aq x - ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0 := by
      simp only [ψ_aq, sub_nonneg]
      calc (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else (0 : ℝ))
          ≤ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then Λ p else (0 : ℝ) :=
            sum_le_sum fun p hp ↦ by split_ifs <;> simp [vonMangoldt_apply_prime (mem_filter.mp hp).2]
        _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, if n % q = a then Λ n else (0 : ℝ) :=
            sum_le_sum_of_subset_of_nonneg
              (fun p hp ↦ by simp only [mem_filter, mem_Iic, mem_Icc] at hp ⊢; exact ⟨hp.2.one_lt.le, hp.1⟩)
              (fun n _ _ ↦ by split_ifs <;> [exact vonMangoldt_nonneg; rfl])
    have hdiff_le : ψ_aq x - (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else (0 : ℝ)) ≤ ψ x - θ x := by
      simp only [ψ_aq, Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
      conv_rhs => rw [Icc_zero_eq_insert, sum_insert (by simp : (0 : ℕ) ∉ Icc 1 ⌊x⌋₊),
        show Λ 0 = 0 by simp only [ArithmeticFunction.map_zero], zero_add,
        show filter Nat.Prime (insert 0 (Icc 1 ⌊x⌋₊)) = filter Nat.Prime (Icc 1 ⌊x⌋₊) by
          simp [filter_insert, Nat.not_prime_zero]]
      rw [filter_prime_Iic_eq_Icc, ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊) Nat.Prime,
        show (∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), if p % q = a then log p else (0 : ℝ)) =
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), if p % q = a then Λ p else (0 : ℝ) from
          sum_congr rfl fun p hp ↦ by simp only [mem_filter] at hp; split_ifs <;> simp [vonMangoldt_apply_prime hp.2],
        ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊) Nat.Prime,
        show (∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Λ p) = ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), log p from
          sum_congr rfl fun p hp ↦ vonMangoldt_apply_prime (mem_filter.mp hp).2]
      have h1 : (∑ n ∈ (Icc 1 ⌊x⌋₊).filter (¬Nat.Prime ·), if n % q = a then Λ n else (0 : ℝ)) ≤
          ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (¬Nat.Prime ·), Λ n :=
        sum_le_sum fun n _ ↦ by split_ifs <;> [exact le_refl _; exact vonMangoldt_nonneg]
      linarith
    rw [abs_of_nonneg hdiff_nonneg, abs_of_nonneg (by bound)]
    exact hdiff_le.trans ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith)))
  · simpa only [mul_assoc] using
      (isLittleO_sqrt_mul_log.const_mul_left 2).trans_isTheta (isTheta_self_div_const htot_pos.ne')

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos387/AnalyticInputs.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Analytic inputs for the BNPZ covering theorem

This module derives the fixed-modulus estimates needed by the public BNPZ
covering construction from the repository's proof of the prime number theorem
in arithmetic progressions.  No result in this file is postulated.
-/

open Filter Finset Asymptotics Real

namespace Erdos387

/-- Chebyshev's theta function restricted to a reduced residue class. -/
noncomputable def thetaAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
    if p % q = a then Real.log p else 0

/-- Primes in a real interval and in the residue class `a mod q`. -/
noncomputable def primeIntervalAP (q a : ℕ) (u v : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun p => p.Prime ∧ p % q = a)

/-- Rewrite `thetaAP` as an unweighted finite-set restriction followed by a
logarithmic sum. -/
theorem thetaAP_eq_sum_filter (q a : ℕ) (x : ℝ) :
    thetaAP q a x =
      ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a),
        Real.log p := by
  classical
  unfold thetaAP
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime <;> by_cases hres : p % q = a <;>
    simp [hprime, hres]

/-- The increment of `thetaAP` is exactly the logarithmic sum over the
corresponding interval. -/
theorem thetaAP_sub_eq_sum_interval (q a : ℕ) {u v : ℝ}
    (huv : u ≤ v) :
    thetaAP q a v - thetaAP q a u =
      ∑ p ∈ primeIntervalAP q a u v, Real.log p := by
  classical
  rw [thetaAP_eq_sum_filter, thetaAP_eq_sum_filter]
  let pred : ℕ → Prop := fun p => p.Prime ∧ p % q = a
  let left := (Finset.Iic ⌊u⌋₊).filter pred
  let block := (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter pred
  have hfloor : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_mono huv
  have hdis : Disjoint left block := by
    exact (Finset.Iic_disjoint_Ioc le_rfl).mono
      (Finset.filter_subset pred (Finset.Iic ⌊u⌋₊))
      (Finset.filter_subset pred (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊))
  have hunion : left ∪ block = (Finset.Iic ⌊v⌋₊).filter pred := by
    dsimp [left, block]
    rw [← Finset.filter_union, Finset.Iic_union_Ioc_eq_Iic hfloor]
  have hsum := Finset.sum_union hdis (f := fun p : ℕ => Real.log p)
  rw [hunion] at hsum
  dsimp [left, block, pred] at hsum
  rw [primeIntervalAP]
  linarith

/-- Removing logarithmic weights on a dyadic interval costs only replacing
`log p` by the endpoint bounds `log x` and `log (2*x)`. -/
theorem primeIntervalAP_log_bounds (q a : ℕ) {x u v : ℝ} (hx : 0 < x)
    (hxu : x ≤ u) (huv : u ≤ v) (hvx : v ≤ 2 * x) :
    (((primeIntervalAP q a u v).card : ℕ) : ℝ) * Real.log x ≤
        thetaAP q a v - thetaAP q a u ∧
      thetaAP q a v - thetaAP q a u ≤
        (((primeIntervalAP q a u v).card : ℕ) : ℝ) * Real.log (2 * x) := by
  classical
  rw [thetaAP_sub_eq_sum_interval q a huv]
  constructor
  · calc
      (((primeIntervalAP q a u v).card : ℕ) : ℝ) * Real.log x =
          ∑ p ∈ primeIntervalAP q a u v, Real.log x := by simp
      _ ≤ ∑ p ∈ primeIntervalAP q a u v, Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        have hpI := (Finset.mem_filter.mp hp).1
        have hup : u < (p : ℝ) := Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hpI).1
        exact Real.log_le_log hx (hxu.trans_lt hup).le
  · calc
      (∑ p ∈ primeIntervalAP q a u v, Real.log p) ≤
          ∑ p ∈ primeIntervalAP q a u v, Real.log (2 * x) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpdata := Finset.mem_filter.mp hp
        have hpI := Finset.mem_Ioc.mp hpdata.1
        have hpprime : p.Prime := hpdata.2.1
        have hpv : (p : ℝ) ≤ v :=
          (Nat.cast_le.mpr hpI.2).trans
            (Nat.floor_le (hx.le.trans (hxu.trans huv)))
        exact Real.log_le_log (by exact_mod_cast hpprime.pos) (hpv.trans hvx)
      _ = (((primeIntervalAP q a u v).card : ℕ) : ℝ) * Real.log (2 * x) := by
        simp

/-- On large dyadic blocks, replacing `log x` by `log (2*x)` has arbitrarily
small relative cost. -/
theorem eventually_log_two_mul_le {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.log (2 * x) ≤ (1 + ρ) * Real.log x := by
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log 2 / ρ ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log 2 / ρ))
  filter_upwards [hlarge, eventually_gt_atTop (0 : ℝ)] with x hxlog hx
  rw [Real.log_mul (by norm_num) hx.ne']
  have hρlog : Real.log 2 ≤ ρ * Real.log x := by
    simpa [mul_comm] using (div_le_iff₀ hρ).mp hxlog
  nlinarith

/-- The elementary coefficient inequality used when logarithmic weights are
removed. -/
private theorem one_sub_two_mul_le_ratio {ρ : ℝ} (hρ : 0 ≤ ρ) (_hρlt : ρ < 1) :
    1 - 2 * ρ ≤ (1 - ρ) / (1 + ρ) := by
  apply (le_div_iff₀ (by linarith)).2
  nlinarith [sq_nonneg ρ]

/-- Removing logarithmic weights from an assumed family of uniform theta
estimates.  Separating this elementary implication keeps the analytic input
visible. -/
theorem primeIntervalAP_card_estimate_of_theta {q a : ℕ} (hq : 1 ≤ q)
    (δ ε : ℝ) (hε : 0 < ε)
    (hTheta : ∀ η : ℝ, 0 < η →
      ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ u v : ℝ, x ≤ u → u < v → v ≤ 2 * x → δ * x ≤ v - u →
          |(thetaAP q a v - thetaAP q a u) -
              (v - u) / q.totient| ≤
            η * ((v - u) / q.totient)) :
    ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ u v : ℝ, x ≤ u → u < v → v ≤ 2 * x → δ * x ≤ v - u →
        |(((primeIntervalAP q a u v).card : ℕ) : ℝ) -
            (v - u) / q.totient / Real.log x| ≤
          ε * ((v - u) / q.totient / Real.log x) := by
  let ρ : ℝ := min (ε / 8) (1 / 8)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by positivity) (by norm_num)
  have hρ_le_eps : ρ ≤ ε / 8 := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_eighth : ρ ≤ 1 / 8 := by
    dsimp [ρ]
    exact min_le_right _ _
  have htwoρ_le_eps : 2 * ρ ≤ ε := by nlinarith
  have hρ_le_eps' : ρ ≤ ε := by nlinarith
  have hρlt : ρ < 1 := lt_of_le_of_lt hρ_le_eighth (by norm_num)
  obtain ⟨Xθ, hXθ3, hXθ⟩ := hTheta ρ hρ
  obtain ⟨Xlog, hXlog⟩ := eventually_atTop.mp (eventually_log_two_mul_le hρ)
  refine ⟨max Xθ Xlog, hXθ3.trans (le_max_left _ _), ?_⟩
  intro x hx u v hxu huv hvx hlen
  have hxθ : Xθ ≤ x := (le_max_left Xθ Xlog).trans hx
  have hxlog : Xlog ≤ x := (le_max_right Xθ Xlog).trans hx
  have hx3 : 3 ≤ x := hXθ3.trans hxθ
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx3
  have hlogpos : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le (by norm_num) hx3)
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  let C : ℝ := (((primeIntervalAP q a u v).card : ℕ) : ℝ)
  let A : ℝ := (v - u) / (q.totient : ℝ)
  let L : ℝ := A / Real.log x
  let S : ℝ := thetaAP q a v - thetaAP q a u
  have hApos : 0 < A := by
    dsimp [A]
    exact div_pos (sub_pos.mpr huv) hφ
  have hLpos : 0 < L := by
    dsimp [L]
    exact div_pos hApos hlogpos
  have htheta := hXθ x hxθ u v hxu huv hvx hlen
  have htheta' : |S - A| ≤ ρ * A := by
    simpa only [S, A] using htheta
  have hthetaBounds : (1 - ρ) * A ≤ S ∧ S ≤ (1 + ρ) * A := by
    rw [abs_le] at htheta'
    constructor <;> linarith
  have hlogs := primeIntervalAP_log_bounds q a hxpos hxu huv.le hvx
  have hlogs' : C * Real.log x ≤ S ∧ S ≤ C * Real.log (2 * x) := by
    simpa only [C, S] using hlogs
  have hlogDist : Real.log (2 * x) ≤ (1 + ρ) * Real.log x := hXlog x hxlog
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hSupper : S ≤ C * ((1 + ρ) * Real.log x) :=
    hlogs'.2.trans (mul_le_mul_of_nonneg_left hlogDist hCnonneg)
  have hCupper : C ≤ (1 + ρ) * L := by
    rw [show (1 + ρ) * L = ((1 + ρ) * A) / Real.log x by
      dsimp [L]
      ring]
    exact (le_div_iff₀ hlogpos).2 (hlogs'.1.trans hthetaBounds.2)
  have hRatioLower : ((1 - ρ) / (1 + ρ)) * L ≤ C := by
    rw [show ((1 - ρ) / (1 + ρ)) * L =
        ((1 - ρ) * A) / ((1 + ρ) * Real.log x) by
      dsimp [L]
      field_simp]
    apply (div_le_iff₀ (mul_pos (by linarith) hlogpos)).2
    exact hthetaBounds.1.trans hSupper
  have hClower : (1 - 2 * ρ) * L ≤ C := by
    exact (mul_le_mul_of_nonneg_right
      (one_sub_two_mul_le_ratio hρ.le hρlt) hLpos.le).trans hRatioLower
  change |C - L| ≤ ε * L
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr htwoρ_le_eps) hLpos.le]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hρ_le_eps') hLpos.le]

/-- The unconditional PNT in arithmetic progressions already available in this
repository, restated using `thetaAP`. -/
theorem thetaAP_isEquivalent {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q)
    (haq : a < q) :
    thetaAP q a ~[Filter.atTop] (fun x : ℝ => x / q.totient) := by
  change
    (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
      if p % q = a then Real.log p else 0) ~[Filter.atTop]
        (fun x : ℝ => x / q.totient)
  exact chebyshev_asymptotic_pnt hq ha haq

/-- Arbitrarily accurate relative control of `thetaAP` beyond a fixed
threshold. -/
theorem eventually_thetaAP_ratio_close {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in Filter.atTop,
      |thetaAP q a x / (x / q.totient) - 1| < η := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hden : ∀ᶠ x : ℝ in Filter.atTop, x / (q.totient : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_ne_zero hx.ne' hφ.ne'
  have hratio : Filter.Tendsto
      (fun x : ℝ => thetaAP q a x / (x / q.totient))
      Filter.atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hden).mp
      (thetaAP_isEquivalent hq ha haq)
  exact hratio.eventually (Metric.ball_mem_nhds 1 hη)

/-- Relative ratio control rewritten as an additive error estimate. -/
theorem eventually_thetaAP_abs_sub_le {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in Filter.atTop,
      |thetaAP q a x - x / q.totient| ≤ η * (x / q.totient) := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  filter_upwards [eventually_thetaAP_ratio_close hq ha haq hη,
    eventually_gt_atTop (0 : ℝ)] with x hxclose hx
  have hmain : 0 < x / (q.totient : ℝ) := div_pos hx hφ
  have hid :
      thetaAP q a x - x / q.totient =
        (thetaAP q a x / (x / q.totient) - 1) * (x / q.totient) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos hmain]
  exact mul_le_mul_of_nonneg_right hxclose.le hmain.le

/-- Uniform control of theta increments on every interval of relative length
at least `δ` inside a dyadic block.  This is the weighted fixed-modulus PNT
input used before removing logarithmic weights. -/
theorem thetaAP_dyadic_interval_estimate {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ u v : ℝ, x ≤ u → u < v → v ≤ 2 * x → δ * x ≤ v - u →
        |(thetaAP q a v - thetaAP q a u) -
            (v - u) / q.totient| ≤
          ε * ((v - u) / q.totient) := by
  let η : ℝ := ε * δ / 8
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (eventually_thetaAP_abs_sub_le hq ha haq hη)
  refine ⟨max 3 X, le_max_left _ _, ?_⟩
  intro x hx u v hxu huv hvx hlen
  have hXu : X ≤ u := le_trans (le_trans (le_max_right 3 X) hx) hxu
  have hXv : X ≤ v := hXu.trans huv.le
  have huerr := hX u hXu
  have hverr := hX v hXv
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left 3 X) hx)
  have hupos : 0 < u := hxpos.trans_le hxu
  have hvpos : 0 < v := hupos.trans huv
  have hrewrite :
      (thetaAP q a v - thetaAP q a u) - (v - u) / q.totient =
        (thetaAP q a v - v / q.totient) -
          (thetaAP q a u - u / q.totient) := by
    ring
  rw [hrewrite]
  calc
    |(thetaAP q a v - v / q.totient) -
        (thetaAP q a u - u / q.totient)|
        ≤ |thetaAP q a v - v / q.totient| +
            |thetaAP q a u - u / q.totient| := abs_sub _ _
    _ ≤ η * (v / q.totient) + η * (u / q.totient) :=
      add_le_add hverr huerr
    _ ≤ η * ((4 * x) / q.totient) := by
      have hu_le : u ≤ 2 * x := huv.le.trans hvx
      have huvsum : u + v ≤ 4 * x := by linarith
      rw [show η * (v / (q.totient : ℝ)) + η * (u / q.totient) =
        η * ((u + v) / q.totient) by ring]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right huvsum hφ.le) hη.le
    _ ≤ ε * ((v - u) / q.totient) := by
      rw [show η * ((4 * x) / (q.totient : ℝ)) =
        ε * ((δ * x / 2) / q.totient) by
          dsimp [η]
          ring]
      apply mul_le_mul_of_nonneg_left _ hε.le
      apply div_le_div_of_nonneg_right _ hφ.le
      nlinarith

/-- Fixed-modulus PNT on all relatively long subintervals of a dyadic block,
in the exact unweighted form needed by the covering argument. -/
theorem primeIntervalAP_card_estimate {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ u v : ℝ, x ≤ u → u < v → v ≤ 2 * x → δ * x ≤ v - u →
        |(((primeIntervalAP q a u v).card : ℕ) : ℝ) -
            (v - u) / q.totient / Real.log x| ≤
          ε * ((v - u) / q.totient / Real.log x) := by
  apply primeIntervalAP_card_estimate_of_theta hq δ ε hε
  intro η hη
  exact thetaAP_dyadic_interval_estimate hq ha haq δ η hδ hη

/-- The fixed-modulus analytic input used by the public covering
formalization, now proved from `WeakPNT_AP` rather than assumed. -/
theorem PNT_fixed_modulus (q a : ℕ) (hq : 1 ≤ q) (haq : a < q)
    (hcop : a.Coprime q) (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ u v : ℝ, x ≤ u → u < v → v ≤ 2 * x → δ * x ≤ v - u →
        |(((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter
            (fun p => p.Prime ∧ p % q = a)).card : ℝ)
          - (v - u) / ((Nat.totient q : ℝ) * Real.log x)|
        ≤ ε * (v - u) / ((Nat.totient q : ℝ) * Real.log x) := by
  obtain ⟨x₀, hx₀, hmain⟩ :=
    primeIntervalAP_card_estimate hq hcop haq δ ε hδ hε
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx u v hxu huv hvx hlen
  have h := hmain x hx u v hxu huv hvx hlen
  simpa only [primeIntervalAP, div_div, mul_div_assoc] using h

/- Namespace-compatible adapter for the authors' public cover files. -/
namespace ANT

theorem PNT_fixed_modulus (q a : ℕ) (hq : 1 ≤ q) (haq : a < q)
    (hcop : a.Coprime q) (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ u v : ℝ, x ≤ u → u < v → v ≤ 2 * x → δ * x ≤ v - u →
        |(((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter
            (fun p => p.Prime ∧ p % q = a)).card : ℝ)
          - (v - u) / ((Nat.totient q : ℝ) * Real.log x)|
        ≤ ε * (v - u) / ((Nat.totient q : ℝ) * Real.log x) :=
  Erdos387.PNT_fixed_modulus q a hq haq hcop δ hδ ε hε

end ANT

end Erdos387

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos21.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 21.
https://www.erdosproblems.com/forum/thread/21

Informal authors:
- Jeff Kahn

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos21.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

/-!
# Erdős Problem 21

For `n > 0`, `erdosLovaszF n` is the least cardinality of an intersecting
family of `n`-element finite subsets of `ℕ` such that every set of at most
`n - 1` points is disjoint from a member of the family.  The main theorem
formalizes Kahn's resolution `erdosLovaszF n = O(n)`.

The detailed mathematical reconstruction and the map from its lemmas to this
development are in `tex/21.tex`.
-/

open Finset Filter

attribute [local instance] Classical.propDecidable

/-! ## The literal problem -/

/-- Every member of `F` has cardinality `n`. -/
def IsUniform {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, A.card = n

/-- Every two (not necessarily distinct) members of `F` meet.  Quantifying
also over equal members rules out the empty edge. -/
def IsIntersecting {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty

/-- The avoidance condition in the statement of Problem 21. -/
def AvoidsAllSmallSets {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ S : Finset α, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A

/-- A family is one of the families over which the Erdős--Lovász minimum is
taken. -/
def IsErdosLovaszFamily {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  IsUniform n F ∧ IsIntersecting F ∧ AvoidsAllSmallSets n F

/-- The exact extremal function from Problem 21.  At `n = 0` the candidate
set is empty and the natural-number infimum is `0`; the theorem concerns the
eventual, positive range. -/
noncomputable def erdosLovaszF (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily n F ∧ F.card = m}

/-- A finite set meeting every member of `F`. -/
def IsVertexCover {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (S : Finset α) : Prop :=
  ∀ A ∈ F, ¬ Disjoint S A

/-- The statement that every vertex cover has at least `n` points. -/
def CoverNumberAtLeast {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ S : Finset α, IsVertexCover F S → n ≤ S.card

lemma avoidsAllSmallSets_iff_coverNumberAtLeast {α : Type*} [DecidableEq α]
    (n : ℕ) (hn : 0 < n) (F : Finset (Finset α)) :
    AvoidsAllSmallSets n F ↔ CoverNumberAtLeast n F := by
  constructor
  · intro h S hS
    by_contra hnS
    have hcard : S.card ≤ n - 1 := by omega
    obtain ⟨A, hAF, hdisj⟩ := h S hcard
    exact hS A hAF hdisj
  · intro h S hcard
    by_contra hnone
    push Not at hnone
    have hcover : IsVertexCover F S := by
      intro A hAF
      exact hnone A hAF
    have hlower := h S hcover
    omega

/-! ## Relabelling a finite ground set by natural numbers -/

/-- Relabel every point of every edge along an embedding. -/
def relabel {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (F : Finset (Finset α)) : Finset (Finset β) :=
  F.map (Finset.mapEmbedding e).toEmbedding

@[simp]
lemma card_relabel {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (F : Finset (Finset α)) :
    (relabel e F).card = F.card := by
  simp [relabel]

lemma isErdosLovaszFamily_relabel {α β : Type*}
    [DecidableEq α] [DecidableEq β] {n : ℕ}
    (e : α ↪ β) {F : Finset (Finset α)}
    (hF : IsErdosLovaszFamily n F) :
    IsErdosLovaszFamily n (relabel e F) := by
  classical
  rcases hF with ⟨huniform, hinter, hsmall⟩
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    rw [relabel, Finset.mem_map] at hB
    obtain ⟨A, hAF, rfl⟩ := hB
    simpa using huniform A hAF
  · intro A hAF B hBF
    rw [relabel, Finset.mem_map] at hAF hBF
    obtain ⟨A, hAF, rfl⟩ := hAF
    obtain ⟨B, hBF, rfl⟩ := hBF
    obtain ⟨x, hx⟩ := hinter A hAF B hBF
    refine ⟨e x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_map.mpr ⟨x, (Finset.mem_inter.mp hx).1, rfl⟩
    · exact Finset.mem_map.mpr ⟨x, (Finset.mem_inter.mp hx).2, rfl⟩
  · intro S hS
    let T : Finset α := S.preimage e e.injective.injOn
    have hTcard : T.card ≤ S.card := by
      rw [show T = S.preimage e e.injective.injOn from rfl,
        Finset.card_preimage]
      exact Finset.card_filter_le _ _
    obtain ⟨A, hAF, hdisj⟩ := hsmall T (hTcard.trans hS)
    refine ⟨A.map e, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨A, hAF, rfl⟩
    · rw [Finset.disjoint_left]
      intro y hyS hyA
      obtain ⟨x, hxA, rfl⟩ := Finset.mem_map.mp hyA
      exact Finset.disjoint_left.mp hdisj
        (Finset.mem_preimage.mpr hyS) hxA

/-- A canonical embedding of any finite type into `ℕ`. -/
noncomputable def finiteNatEmbedding (α : Type*) [Fintype α] : α ↪ ℕ :=
  (Fintype.equivFin α).toEmbedding.trans Fin.valEmbedding

lemma erdosLovaszF_le_of_finite_family {α : Type*}
    [Fintype α] [DecidableEq α] {n M : ℕ}
    {F : Finset (Finset α)} (hF : IsErdosLovaszFamily n F)
    (hcard : F.card ≤ M) : erdosLovaszF n ≤ M := by
  let e := finiteNatEmbedding α
  have hmem : (relabel e F).card ∈
      {m : ℕ | ∃ G : Finset (Finset ℕ),
        IsErdosLovaszFamily n G ∧ G.card = m} :=
    ⟨relabel e F, isErdosLovaszFamily_relabel e hF, rfl⟩
  have hle : erdosLovaszF n ≤ (relabel e F).card := by
    exact Nat.sInf_le hmem
  exact hle.trans (by simpa using hcard)

/-! ## Indexed hypergraphs and point-set duality -/

/-- A finite hypergraph whose edge labels are retained.  This avoids silently
discarding multiplicities during the construction. -/
structure IndexedHypergraph (V E : Type*) [Fintype V] [Fintype E]
    [DecidableEq V] where
  edge : E → Finset V

namespace IndexedHypergraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

/-- Edge labels incident with a vertex. -/
def incident (H : IndexedHypergraph V E) (v : V) : Finset E :=
  Finset.univ.filter fun e ↦ v ∈ H.edge e

@[simp]
lemma mem_incident (H : IndexedHypergraph V E) (v : V) (e : E) :
    e ∈ H.incident v ↔ v ∈ H.edge e := by
  simp [incident]

/-- Every vertex has degree `r`. -/
def IsRegular (H : IndexedHypergraph V E) (r : ℕ) : Prop :=
  ∀ v, (H.incident v).card = r

/-- Every two distinct vertices occur together in some edge. -/
def PairCovered (H : IndexedHypergraph V E) : Prop :=
  ∀ ⦃x y : V⦄, x ≠ y → ∃ e : E, x ∈ H.edge e ∧ y ∈ H.edge e

/-- A set of edge labels covering every vertex. -/
def IsEdgeCover (H : IndexedHypergraph V E) (C : Finset E) : Prop :=
  ∀ v : V, ∃ e ∈ C, v ∈ H.edge e

/-- No edge cover uses fewer than `r` labels. -/
def EdgeCoverNumberAtLeast (H : IndexedHypergraph V E) (r : ℕ) : Prop :=
  ∀ C : Finset E, H.IsEdgeCover C → r ≤ C.card

/-- The dual edge belonging to a primal vertex. -/
def dualEdge (H : IndexedHypergraph V E) (v : V) : Finset E :=
  H.incident v

/-- The point-set dual, with duplicate edges collapsed only at the final
problem-facing boundary. -/
def dualFamily (H : IndexedHypergraph V E) : Finset (Finset E) :=
  Finset.univ.image H.dualEdge

lemma dualFamily_card_le (H : IndexedHypergraph V E) :
    H.dualFamily.card ≤ Fintype.card V := by
  simpa [dualFamily] using
    (Finset.card_image_le (s := (Finset.univ : Finset V))
      (f := H.dualEdge))

lemma dualFamily_isErdosLovaszFamily (H : IndexedHypergraph V E)
    {r : ℕ} (hr : 0 < r) (hreg : H.IsRegular r)
    (hpairs : H.PairCovered) (hcover : H.EdgeCoverNumberAtLeast r) :
    IsErdosLovaszFamily r H.dualFamily := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro A hA
    simp only [dualFamily, Finset.mem_image] at hA
    obtain ⟨v, _, rfl⟩ := hA
    exact hreg v
  · intro A hA B hB
    simp only [dualFamily, Finset.mem_image] at hA hB
    obtain ⟨x, _, rfl⟩ := hA
    obtain ⟨y, _, rfl⟩ := hB
    by_cases hxy : x = y
    · subst y
      have hpos : 0 < (H.dualEdge x).card := by
        simpa [dualEdge, hreg x] using hr
      rw [Finset.inter_self]
      exact Finset.card_pos.mp hpos
    · obtain ⟨e, hex, hey⟩ := hpairs hxy
      exact ⟨e, Finset.mem_inter.mpr ⟨by simpa [dualEdge] using hex,
        by simpa [dualEdge] using hey⟩⟩
  · rw [avoidsAllSmallSets_iff_coverNumberAtLeast r hr]
    intro C hC
    apply hcover C
    intro v
    have hdual : H.dualEdge v ∈ H.dualFamily := by
      simp [dualFamily]
    have hnondisj : ¬ Disjoint C (H.dualEdge v) := hC _ hdual
    obtain ⟨e, heC, heinc⟩ := Finset.not_disjoint_iff.mp hnondisj
    exact ⟨e, heC, by simpa [dualEdge] using heinc⟩

theorem erdosLovaszF_le_of_dualConstruction (H : IndexedHypergraph V E)
    {r M : ℕ} (hr : 0 < r) (hreg : H.IsRegular r)
    (hpairs : H.PairCovered) (hcover : H.EdgeCoverNumberAtLeast r)
    (hvertices : Fintype.card V ≤ M) :
    erdosLovaszF r ≤ M := by
  apply erdosLovaszF_le_of_finite_family
    (dualFamily_isErdosLovaszFamily H hr hreg hpairs hcover)
  exact (dualFamily_card_le H).trans hvertices

end IndexedHypergraph

/-- A concrete, quantifier-level version of the affirmative answer.  A
natural constant is equivalent to the usual real-valued Vinogradov bound. -/
def Erdos21Question : Prop :=
  ∃ C N : ℕ, ∀ n : ℕ, N ≤ n → erdosLovaszF n ≤ C * n

/-- A completely finite dual witness with an explicit linear vertex bound.
Using `Fin v` and `Fin e` avoids existential type-class data in the eventual
construction theorem. -/
def HasDualWitness (C r : ℕ) : Prop :=
  ∃ v e : ℕ, ∃ H : IndexedHypergraph (Fin v) (Fin e),
    H.IsRegular r ∧ H.PairCovered ∧ H.EdgeCoverNumberAtLeast r ∧ v ≤ C * r

lemma erdosLovaszF_le_of_hasDualWitness {C r : ℕ} (hr : 0 < r)
    (h : HasDualWitness C r) : erdosLovaszF r ≤ C * r := by
  obtain ⟨v, e, H, hreg, hpairs, hcover, hv⟩ := h
  exact H.erdosLovaszF_le_of_dualConstruction hr hreg hpairs hcover
    (by simpa using hv)

/-- Once the finite Kahn witnesses have been built, this lemma performs the
entire asymptotic and problem-facing assembly. -/
lemma erdos21_of_eventual_dualWitness
    (h : ∃ C N : ℕ, ∀ r : ℕ, N ≤ r → HasDualWitness C r) :
    Erdos21Question := by
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, max N 1, ?_⟩
  intro r hr
  apply erdosLovaszF_le_of_hasDualWitness (by omega)
  exact hC r (le_trans (le_max_left N 1) hr)

/-! ## Transversal templates as orthogonal arrays -/

namespace Transversal

/-- An orthogonal array of strength two.  Rows are indexed by `Fin t × Fin t`;
any two columns give a bijection onto `Fin t × Fin t`.  This is the exact
form of a `TD(k,t)` used in Kahn's construction. -/
structure OrthogonalArray (k t : ℕ) where
  entry : (Fin t × Fin t) → Fin k → Fin t
  pair_bijective : ∀ ⦃i j : Fin k⦄, i ≠ j →
    Function.Bijective fun b ↦ (entry b i, entry b j)

namespace OrthogonalArray

variable {k t : ℕ}

/-- Delete the final column of an array with `k+1` columns.  A row becomes a
transversal edge on `k` groups of `t` points. -/
def block (D : OrthogonalArray (k + 1) t) (b : Fin t × Fin t) :
    Finset (Fin k × Fin t) :=
  Finset.univ.image fun i : Fin k ↦ (i, D.entry b i.castSucc)

@[simp]
lemma mem_block_iff (D : OrthogonalArray (k + 1) t)
    (b : Fin t × Fin t) (i : Fin k) (x : Fin t) :
    (i, x) ∈ D.block b ↔ D.entry b i.castSucc = x := by
  simp [block, Prod.ext_iff]

/-- The indexed hypergraph supplied by the deleted array. -/
def hypergraph (D : OrthogonalArray (k + 1) t) :
    IndexedHypergraph (Fin k × Fin t) (Fin t × Fin t) where
  edge := D.block

@[simp]
lemma mem_hypergraph_edge_iff (D : OrthogonalArray (k + 1) t)
    (b : Fin t × Fin t) (i : Fin k) (x : Fin t) :
    (i, x) ∈ (D.hypergraph.edge b) ↔ D.entry b i.castSucc = x :=
  D.mem_block_iff b i x

lemma castSucc_ne_last (i : Fin k) :
    i.castSucc ≠ (Fin.last k : Fin (k + 1)) := by
  exact Fin.castSucc_ne_last i

/-- Rows taking a prescribed value in a non-final column. -/
def fiber (D : OrthogonalArray (k + 1) t) (i : Fin k) (x : Fin t) :
    Finset (Fin t × Fin t) :=
  Finset.univ.filter fun b ↦ D.entry b i.castSucc = x

@[simp]
lemma mem_fiber_iff (D : OrthogonalArray (k + 1) t)
    (i : Fin k) (x : Fin t) (b : Fin t × Fin t) :
    b ∈ D.fiber i x ↔ D.entry b i.castSucc = x := by
  simp [fiber]

lemma fiber_card (D : OrthogonalArray (k + 1) t)
    (i : Fin k) (x : Fin t) : (D.fiber i x).card = t := by
  classical
  let f : Fin t × Fin t → Fin t := fun b ↦ D.entry b (Fin.last k)
  have hinj : Set.InjOn f (D.fiber i x : Set (Fin t × Fin t)) := by
    intro a ha b hb hab
    apply (D.pair_bijective (castSucc_ne_last i)).1
    apply Prod.ext
    · simpa [fiber] using (show D.entry a i.castSucc = D.entry b i.castSucc from
        (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    · exact hab
  have hsurj : (D.fiber i x).image f = Finset.univ := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, iff_true]
    obtain ⟨b, hb⟩ :=
      (D.pair_bijective (castSucc_ne_last i)).2 (x, y)
    refine ⟨b, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, congrArg Prod.fst hb⟩
    · exact congrArg Prod.snd hb
  calc
    (D.fiber i x).card = ((D.fiber i x).image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = t := by simp [hsurj]

lemma hypergraph_regular (D : OrthogonalArray (k + 1) t) :
    D.hypergraph.IsRegular t := by
  intro ix
  rcases ix with ⟨i, x⟩
  have hinc : D.hypergraph.incident (i, x) = D.fiber i x := by
    ext b
    simp [IndexedHypergraph.incident, fiber]
  rw [hinc]
  exact D.fiber_card i x

/-- The rows having one fixed value in the deleted column form a cover of
exactly `t` rows. -/
def parallelClass (D : OrthogonalArray (k + 1) t) (z : Fin t) :
    Finset (Fin t × Fin t) :=
  Finset.univ.filter fun b ↦ D.entry b (Fin.last k) = z

lemma parallelClass_card (D : OrthogonalArray (k + 1) t)
    (hk : 0 < k) (z : Fin t) : (D.parallelClass z).card = t := by
  let i : Fin k := ⟨0, hk⟩
  -- Swap the two columns in the fiber count.
  classical
  let f : Fin t × Fin t → Fin t := fun b ↦ D.entry b i.castSucc
  have hinj : Set.InjOn f (D.parallelClass z : Set (Fin t × Fin t)) := by
    intro a ha b hb hab
    apply (D.pair_bijective (castSucc_ne_last i)).1
    apply Prod.ext
    · exact hab
    · simpa [parallelClass] using
        (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
  have hsurj : (D.parallelClass z).image f = Finset.univ := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, iff_true]
    obtain ⟨b, hb⟩ :=
      (D.pair_bijective (castSucc_ne_last i)).2 (x, z)
    refine ⟨b, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, congrArg Prod.snd hb⟩
    · exact congrArg Prod.fst hb
  calc
    (D.parallelClass z).card = ((D.parallelClass z).image f).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ = t := by simp [hsurj]

lemma parallelClass_isEdgeCover (D : OrthogonalArray (k + 1) t)
    (z : Fin t) : D.hypergraph.IsEdgeCover (D.parallelClass z) := by
  intro ix
  rcases ix with ⟨i, x⟩
  obtain ⟨b, hb⟩ :=
    (D.pair_bijective (castSucc_ne_last i)).2 (x, z)
  refine ⟨b, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, congrArg Prod.snd hb⟩
  · rw [mem_hypergraph_edge_iff]
    exact congrArg Prod.fst hb

/-! ### Algebraic and product constructions -/

/-- The invertible affine map that underlies the strength-two finite-field
orthogonal array. -/
def affinePairEquiv {F : Type*} [Field F] (a b : F) (hab : a ≠ b) :
    F × F ≃ F × F where
  toFun p := (p.1 + a * p.2, p.1 + b * p.2)
  invFun p :=
    let y := (p.2 - p.1) / (b - a)
    (p.1 - a * y, y)
  left_inv p := by
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    apply Prod.ext <;> dsimp
    · field_simp [hba]
      ring
    · field_simp [hba]
      ring
  right_inv p := by
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    apply Prod.ext <;> dsimp
    · ring
    · field_simp [hba]
      ring

/-- Restrict an orthogonal array to an injected initial set of columns. -/
def restrictColumns (D : OrthogonalArray k' t) (hk : k ≤ k') :
    OrthogonalArray k t where
  entry row i := D.entry row (Fin.castLE hk i)
  pair_bijective := by
    intro i j hij
    apply D.pair_bijective
    exact fun h ↦ hij (Fin.castLE_injective hk h)

/-- The full affine-plane array has one column for every field element and
one additional vertical column. -/
noncomputable def fullOfFiniteField (F : Type*) [Fintype F] [Field F] :
    OrthogonalArray (Fintype.card F + 1) (Fintype.card F) := by
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  let slope : Fin (Fintype.card F + 1) ≃ Option F :=
    (finSuccEquiv (Fintype.card F)).trans (Equiv.optionCongr e)
  let value : (F × F) → Option F → F
    | p, none => p.2
    | p, some a => p.1 + a * p.2
  refine
    { entry := fun row i ↦ e.symm (value (e row.1, e row.2) (slope i))
      pair_bijective := ?_ }
  intro i j hij
  have hslope : slope i ≠ slope j := fun h ↦ hij (slope.injective h)
  let rowEquiv :
      (Fin (Fintype.card F) × Fin (Fintype.card F)) ≃ F × F :=
    Equiv.prodCongr e e
  let outEquiv : F × F ≃
      (Fin (Fintype.card F) × Fin (Fintype.card F)) :=
    Equiv.prodCongr e.symm e.symm
  rcases hi : slope i with _ | a
  · rcases hj : slope j with _ | b
    · exact (hslope (hi.trans hj.symm)).elim
    · let pairEquiv : F × F ≃ F × F :=
        { toFun := fun p ↦ (p.2, p.1 + b * p.2)
          invFun := fun p ↦ (p.2 - b * p.1, p.1)
          left_inv := by intro p; apply Prod.ext <;> dsimp <;> ring
          right_inv := by intro p; apply Prod.ext <;> dsimp <;> ring }
      let total := rowEquiv.trans (pairEquiv.trans outEquiv)
      simpa [total, rowEquiv, pairEquiv, outEquiv, value, hi, hj] using
        total.bijective
  · rcases hj : slope j with _ | b
    · let pairEquiv : F × F ≃ F × F :=
        { toFun := fun p ↦ (p.1 + a * p.2, p.2)
          invFun := fun p ↦ (p.1 - a * p.2, p.2)
          left_inv := by intro p; apply Prod.ext <;> dsimp <;> ring
          right_inv := by intro p; apply Prod.ext <;> dsimp <;> ring }
      let total := rowEquiv.trans (pairEquiv.trans outEquiv)
      simpa [total, rowEquiv, pairEquiv, outEquiv, value, hi, hj] using
        total.bijective
    · have hab : a ≠ b := by
        intro h
        apply hslope
        rw [hi, hj, h]
      let total := rowEquiv.trans ((affinePairEquiv a b hab).trans outEquiv)
      simpa [total, rowEquiv, outEquiv, value, hi, hj, affinePairEquiv] using
        total.bijective

/-- A finite field of cardinality `t` supplies a strength-two orthogonal
array with any number of columns at most `t+1`. -/
noncomputable def ofFiniteFieldSucc (F : Type*) [Fintype F] [Field F]
    (k : ℕ) (hk : k ≤ Fintype.card F + 1) :
    OrthogonalArray k (Fintype.card F) :=
  restrictColumns (fullOfFiniteField F) hk

/-- Direct products preserve strength-two orthogonal arrays. -/
def product (D₁ : OrthogonalArray k t) (D₂ : OrthogonalArray k t') :
    OrthogonalArray k (t * t') where
  entry row i :=
    finProdFinEquiv
      (D₁.entry
          ((finProdFinEquiv.symm row.1).1,
            (finProdFinEquiv.symm row.2).1) i,
        D₂.entry
          ((finProdFinEquiv.symm row.1).2,
            (finProdFinEquiv.symm row.2).2) i)
  pair_bijective := by
    intro i j hij
    constructor
    · intro u v huv
      have hfirst := congrArg Prod.fst huv
      have hsecond := congrArg Prod.snd huv
      have hfirst' := finProdFinEquiv.injective hfirst
      have hsecond' := finProdFinEquiv.injective hsecond
      have hD₁i :
          D₁.entry ((finProdFinEquiv.symm u.1).1,
              (finProdFinEquiv.symm u.2).1) i =
            D₁.entry ((finProdFinEquiv.symm v.1).1,
              (finProdFinEquiv.symm v.2).1) i :=
        congrArg (fun z : Fin t × Fin t' ↦ z.1) hfirst'
      have hD₂i :
          D₂.entry ((finProdFinEquiv.symm u.1).2,
              (finProdFinEquiv.symm u.2).2) i =
            D₂.entry ((finProdFinEquiv.symm v.1).2,
              (finProdFinEquiv.symm v.2).2) i :=
        congrArg (fun z : Fin t × Fin t' ↦ z.2) hfirst'
      have hD₁j :
          D₁.entry ((finProdFinEquiv.symm u.1).1,
              (finProdFinEquiv.symm u.2).1) j =
            D₁.entry ((finProdFinEquiv.symm v.1).1,
              (finProdFinEquiv.symm v.2).1) j :=
        congrArg (fun z : Fin t × Fin t' ↦ z.1) hsecond'
      have hD₂j :
          D₂.entry ((finProdFinEquiv.symm u.1).2,
              (finProdFinEquiv.symm u.2).2) j =
            D₂.entry ((finProdFinEquiv.symm v.1).2,
              (finProdFinEquiv.symm v.2).2) j :=
        congrArg (fun z : Fin t × Fin t' ↦ z.2) hsecond'
      have hD₁ :
          ((finProdFinEquiv.symm u.1).1, (finProdFinEquiv.symm u.2).1) =
            ((finProdFinEquiv.symm v.1).1, (finProdFinEquiv.symm v.2).1) := by
        apply (D₁.pair_bijective hij).1
        exact Prod.ext_iff.mpr ⟨hD₁i, hD₁j⟩
      have hD₂ :
          ((finProdFinEquiv.symm u.1).2, (finProdFinEquiv.symm u.2).2) =
            ((finProdFinEquiv.symm v.1).2, (finProdFinEquiv.symm v.2).2) := by
        apply (D₂.pair_bijective hij).1
        exact Prod.ext_iff.mpr ⟨hD₂i, hD₂j⟩
      have hu1 : finProdFinEquiv.symm u.1 = finProdFinEquiv.symm v.1 :=
        Prod.ext_iff.mpr
          ⟨congrArg (fun z : Fin t × Fin t ↦ z.1) hD₁,
            congrArg (fun z : Fin t' × Fin t' ↦ z.1) hD₂⟩
      have hu2 : finProdFinEquiv.symm u.2 = finProdFinEquiv.symm v.2 :=
        Prod.ext_iff.mpr
          ⟨congrArg (fun z : Fin t × Fin t ↦ z.2) hD₁,
            congrArg (fun z : Fin t' × Fin t' ↦ z.2) hD₂⟩
      exact Prod.ext_iff.mpr
        ⟨finProdFinEquiv.symm.injective hu1,
          finProdFinEquiv.symm.injective hu2⟩
    · intro target
      obtain ⟨row₁, hrow₁⟩ := (D₁.pair_bijective hij).2
        ((finProdFinEquiv.symm target.1).1,
          (finProdFinEquiv.symm target.2).1)
      obtain ⟨row₂, hrow₂⟩ := (D₂.pair_bijective hij).2
        ((finProdFinEquiv.symm target.1).2,
          (finProdFinEquiv.symm target.2).2)
      have hrow₁i : D₁.entry row₁ i = (finProdFinEquiv.symm target.1).1 :=
        congrArg (fun z : Fin t × Fin t ↦ z.1) hrow₁
      have hrow₁j : D₁.entry row₁ j = (finProdFinEquiv.symm target.2).1 :=
        congrArg (fun z : Fin t × Fin t ↦ z.2) hrow₁
      have hrow₂i : D₂.entry row₂ i = (finProdFinEquiv.symm target.1).2 :=
        congrArg (fun z : Fin t' × Fin t' ↦ z.1) hrow₂
      have hrow₂j : D₂.entry row₂ j = (finProdFinEquiv.symm target.2).2 :=
        congrArg (fun z : Fin t' × Fin t' ↦ z.2) hrow₂
      refine ⟨(finProdFinEquiv (row₁.1, row₂.1),
          finProdFinEquiv (row₁.2, row₂.2)), ?_⟩
      have htarget1 :
          (D₁.entry row₁ i, D₂.entry row₂ i) =
            finProdFinEquiv.symm target.1 :=
        Prod.ext_iff.mpr ⟨hrow₁i, hrow₂i⟩
      have htarget2 :
          (D₁.entry row₁ j, D₂.entry row₂ j) =
            finProdFinEquiv.symm target.2 :=
        Prod.ext_iff.mpr ⟨hrow₁j, hrow₂j⟩
      apply Prod.ext_iff.mpr
      constructor
      · apply finProdFinEquiv.symm.injective
        simpa using htarget1
      · apply finProdFinEquiv.symm.injective
        simpa using htarget2

/-- The one-symbol orthogonal array, used as the empty direct product. -/
def singleton (k : ℕ) : OrthogonalArray k 1 where
  entry _ _ := 0
  pair_bijective := by
    intro i j hij
    constructor
    · intro x y hxy
      exact Subsingleton.elim x y
    · intro y
      exact ⟨(0, 0), Subsingleton.elim _ _⟩

/-- The prime-order finite-field array. -/
noncomputable def ofPrime (k p : ℕ) (hp : p.Prime) (hkp : k ≤ p + 1) :
    OrthogonalArray k p := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa using ofFiniteFieldSucc (ZMod p) k (by simpa using hkp)

/-- Iterate the direct-product construction over a list of prime orders. -/
noncomputable def ofPrimeList (k : ℕ) :
    (L : List ℕ) →
      (∀ p ∈ L, p.Prime) →
      (∀ p ∈ L, k ≤ p + 1) →
      OrthogonalArray k L.prod
  | [], _, _ => singleton k
  | p :: L, hprime, hlarge => by
      simpa using product
        (ofPrime k p (hprime p (by simp)) (hlarge p (by simp)))
        (ofPrimeList k L
          (fun q hq ↦ hprime q (by simp [hq]))
          (fun q hq ↦ hlarge q (by simp [hq])))

/-- If every prime divisor of `n` is at least the requested number of
columns, multiplying the prime-field arrays gives an array of order `n`.
This elementary criterion is the design input used by the strengthened
congruence choice in the construction. -/
noncomputable def ofNatOfPrimeFactorsLarge (k n : ℕ) (hn : n ≠ 0)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ n → k ≤ p + 1) :
    OrthogonalArray k n := by
  have hprime : ∀ p ∈ n.primeFactorsList, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList hp
  have hlistlarge : ∀ p ∈ n.primeFactorsList, k ≤ p + 1 := by
    intro p hp
    exact hlarge p (Nat.prime_of_mem_primeFactorsList hp)
      (Nat.dvd_of_mem_primeFactorsList hp)
  simpa [Nat.prod_primeFactorsList hn] using
    ofPrimeList k n.primeFactorsList hprime hlistlarge

/-- The distinguished symbols `d^2` in columns of slope `d` form a
parabolic arc: a row cannot contain three of them at distinct slopes. -/
lemma parabolic_third_slope_eq {F : Type*} [Field F]
    {u v d e f : F} (hde : d ≠ e) (hdf : d ≠ f)
    (hd : u + d * v = d ^ 2) (he : u + e * v = e ^ 2)
    (hf : u + f * v = f ^ 2) : e = f := by
  have hdeprod : (d - e) * (v - (d + e)) = 0 := by
    linear_combination hd - he
  have hdfprod : (d - f) * (v - (d + f)) = 0 := by
    linear_combination hd - hf
  have hvde : v = d + e := by
    rcases mul_eq_zero.mp hdeprod with h | h
    · exact (hde (sub_eq_zero.mp h)).elim
    · exact sub_eq_zero.mp h
  have hvdf : v = d + f := by
    rcases mul_eq_zero.mp hdfprod with h | h
    · exact (hdf (sub_eq_zero.mp h)).elim
    · exact sub_eq_zero.mp h
  exact add_left_cancel (hvde.symm.trans hvdf)

lemma parabolic_no_three {F : Type*} [Field F]
    {u v d e f : F} (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hd : u + d * v = d ^ 2) (he : u + e * v = e ^ 2)
    (hf : u + f * v = f ^ 2) : False :=
  hef (parabolic_third_slope_eq hde hdf hd he hf)

end OrthogonalArray

end Transversal

/-! ## A coordinate projective plane -/

namespace Projective

/-- Affine points, finite-slope points at infinity, and the vertical point at
infinity. -/
abbrev Point (F : Type*) := (F × F) ⊕ (F ⊕ Unit)

/-- Graph lines, vertical lines, and the line at infinity. -/
abbrev Line (F : Type*) := (F × F) ⊕ (F ⊕ Unit)

def affine {F : Type*} (x y : F) : Point F := Sum.inl (x, y)
def slope {F : Type*} (m : F) : Point F := Sum.inr (Sum.inl m)
def verticalInfinity {F : Type*} : Point F := Sum.inr (Sum.inr ())

def graph {F : Type*} (m b : F) : Line F := Sum.inl (m, b)
def verticalLine {F : Type*} (c : F) : Line F := Sum.inr (Sum.inl c)
def horizon {F : Type*} : Line F := Sum.inr (Sum.inr ())

/-- Incidence in the standard affine chart of `PG(2,F)`. -/
def Incident {F : Type*} [Mul F] [Add F] [DecidableEq F] :
    Point F → Line F → Prop
  | Sum.inl (x, y), Sum.inl (m, b) => y = m * x + b
  | Sum.inl (x, _), Sum.inr (Sum.inl c) => x = c
  | Sum.inl _, Sum.inr (Sum.inr _) => False
  | Sum.inr (Sum.inl s), Sum.inl (m, _) => s = m
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inl _) => False
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => True
  | Sum.inr (Sum.inr _), Sum.inl _ => False
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _) => True

@[simp] lemma incident_affine_graph {F : Type*} [Mul F] [Add F]
    [DecidableEq F] (x y m b : F) :
    Incident (affine x y) (graph m b) ↔ y = m * x + b := Iff.rfl

@[simp] lemma incident_affine_vertical {F : Type*} [Mul F] [Add F]
    [DecidableEq F] (x y c : F) :
    Incident (affine x y) (verticalLine c) ↔ x = c := Iff.rfl

@[simp] lemma incident_slope_graph {F : Type*} [Mul F] [Add F]
    [DecidableEq F] (s m b : F) :
    Incident (slope s) (graph m b) ↔ s = m := Iff.rfl

@[simp] lemma incident_slope_horizon {F : Type*} [Mul F] [Add F]
    [DecidableEq F] (s : F) : Incident (slope s) (horizon : Line F) := trivial

@[simp] lemma incident_vertical_vertical {F : Type*} [Mul F] [Add F]
    [DecidableEq F] (c : F) :
    Incident (verticalInfinity : Point F) (verticalLine c) := trivial

@[simp] lemma incident_vertical_horizon {F : Type*} [Mul F] [Add F]
    [DecidableEq F] :
    Incident (verticalInfinity : Point F) (horizon : Line F) := trivial

@[simp] lemma card_point {F : Type*} [Fintype F] :
    Fintype.card (Point F) = Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp [Point, pow_two, Nat.add_assoc]

@[simp] lemma card_line {F : Type*} [Fintype F] :
    Fintype.card (Line F) = Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp [Line, pow_two, Nat.add_assoc]

/-- Any two projective points lie on a common coordinate line. -/
lemma pair_on_line {F : Type*} [Field F] [DecidableEq F]
    (p q : Point F) : ∃ l : Line F, Incident p l ∧ Incident q l := by
  rcases p with p | p
  · rcases p with ⟨x, y⟩
    rcases q with q | q
    · rcases q with ⟨x', y'⟩
      by_cases hxx : x = x'
      · subst x'
        exact ⟨verticalLine x,
          (incident_affine_vertical x y x).2 rfl,
          (incident_affine_vertical x y' x).2 rfl⟩
      · let m := (y' - y) / (x' - x)
        let b := y - m * x
        refine ⟨graph m b, ?_, ?_⟩
        · change y = m * x + b
          dsimp [b]
          ring
        · change y' = m * x' + b
          dsimp [m, b]
          field_simp [sub_ne_zero.mpr (Ne.symm hxx)]
          ring
    · rcases q with s | u
      · refine ⟨graph s (y - s * x), ?_, ?_⟩
        · change y = s * x + (y - s * x)
          ring
        · exact (incident_slope_graph s s (y - s * x)).2 rfl
      · exact ⟨verticalLine x,
          (incident_affine_vertical x y x).2 rfl,
          incident_vertical_vertical x⟩
  · rcases p with s | u
    · rcases q with q | q
      · rcases q with ⟨x, y⟩
        refine ⟨graph s (y - s * x), ?_, ?_⟩
        · exact (incident_slope_graph s s (y - s * x)).2 rfl
        · change y = s * x + (y - s * x)
          ring
      · rcases q with m | v
        · exact ⟨horizon, incident_slope_horizon s,
            incident_slope_horizon m⟩
        · exact ⟨horizon, incident_slope_horizon s,
            incident_vertical_horizon⟩
    · rcases q with q | q
      · rcases q with ⟨x, y⟩
        exact ⟨verticalLine x, incident_vertical_vertical x,
          (incident_affine_vertical x y x).2 rfl⟩
      · rcases q with m | v
        · exact ⟨horizon, incident_vertical_horizon,
            incident_slope_horizon m⟩
        · exact ⟨horizon, incident_vertical_horizon,
            incident_vertical_horizon⟩

/-- The explicit one-or-two-to-one assignment used at the exceptional
positions of the small templates. -/
def assignedLine {F : Type*} [Ring F] : Point F → Line F
  | Sum.inl (x, y) => graph x (y - x ^ 2)
  | Sum.inr (Sum.inl m) => graph m 0
  | Sum.inr (Sum.inr _) => horizon

lemma incident_assignedLine {F : Type*} [CommRing F] [DecidableEq F]
    {p : Point F} (hp : p ≠ verticalInfinity) :
    Incident p (assignedLine p) := by
  rcases p with p | p
  · rcases p with ⟨x, y⟩
    change y = x * x + (y - x ^ 2)
    ring
  · rcases p with m | u
    · exact (incident_slope_graph m m 0).2 rfl
    · exact (hp rfl).elim

/-- A graph line has one assigned affine point and possibly its slope point;
in particular every assignment fibre has at most two points. -/
lemma assignedLine_fiber_subsingleton_after_affine
    {F : Type*} [CommRing F] [DecidableEq F]
    {m b : F} {p : Point F} (hp : assignedLine p = graph m b) :
    p = affine m (b + m ^ 2) ∨ (b = 0 ∧ p = slope m) := by
  rcases p with p | p
  · rcases p with ⟨x, y⟩
    simp only [assignedLine, graph, Sum.inl.injEq, Prod.mk.injEq] at hp
    rcases hp with ⟨hx, hb⟩
    left
    simp only [affine, Sum.inl.injEq, Prod.mk.injEq]
    refine ⟨hx, ?_⟩
    rw [← hb, ← hx]
    ring
  · rcases p with s | u
    · simp only [assignedLine, graph, Sum.inl.injEq, Prod.mk.injEq] at hp
      exact Or.inr ⟨hp.2.symm, congrArg slope hp.1⟩
    · simp [assignedLine, graph, horizon] at hp

/-! ### Finite incidence sets -/

noncomputable def pointsOnLine {F : Type*} [Fintype F] [Mul F] [Add F] [DecidableEq F]
    (l : Line F) : Finset (Point F) :=
  Finset.univ.filter fun p ↦ Incident p l

@[simp] lemma mem_pointsOnLine_iff {F : Type*} [Fintype F]
    [Mul F] [Add F] [DecidableEq F] (p : Point F) (l : Line F) :
    p ∈ pointsOnLine l ↔ Incident p l := by
  simp [pointsOnLine]

/-- Every coordinate projective line is parametrized by the field together
with its one point at infinity. -/
noncomputable def pointsOnLineEquiv {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (l : Line F) :
    (F ⊕ Unit) ≃ {p : Point F // Incident p l} := by
  rcases l with mb | l
  · rcases mb with ⟨m, b⟩
    refine
      { toFun := fun z ↦ match z with
          | Sum.inl x => ⟨affine x (m * x + b), rfl⟩
          | Sum.inr _ => ⟨slope m, rfl⟩
        invFun := fun p ↦ match p.1 with
          | Sum.inl xy => Sum.inl xy.1
          | Sum.inr (Sum.inl _) => Sum.inr ()
          | Sum.inr (Sum.inr _) => Sum.inr ()
        left_inv := ?_
        right_inv := ?_ }
    · intro z
      rcases z with x | u <;> rfl
    · intro p
      rcases p with ⟨p, hp⟩
      apply Subtype.ext
      rcases p with xy | p
      · rcases xy with ⟨x, y⟩
        change y = m * x + b at hp
        simp [affine, hp]
      · rcases p with s | u
        · change s = m at hp
          subst s
          rfl
        · change False at hp
          exact hp.elim
  · rcases l with c | u
    · refine
        { toFun := fun z ↦ match z with
            | Sum.inl y => ⟨affine c y, rfl⟩
            | Sum.inr _ => ⟨verticalInfinity, trivial⟩
          invFun := fun p ↦ match p.1 with
            | Sum.inl xy => Sum.inl xy.2
            | Sum.inr (Sum.inl _) => Sum.inr ()
            | Sum.inr (Sum.inr _) => Sum.inr ()
          left_inv := ?_
          right_inv := ?_ }
      · intro z
        rcases z with y | u <;> rfl
      · intro p
        rcases p with ⟨p, hp⟩
        apply Subtype.ext
        rcases p with xy | p
        · rcases xy with ⟨x, y⟩
          change x = c at hp
          subst x
          rfl
        · rcases p with s | u
          · change False at hp
            exact hp.elim
          · rfl
    · refine
        { toFun := fun z ↦ match z with
            | Sum.inl m => ⟨slope m, trivial⟩
            | Sum.inr _ => ⟨verticalInfinity, trivial⟩
          invFun := fun p ↦ match p.1 with
            | Sum.inl _ => Sum.inr ()
            | Sum.inr (Sum.inl m) => Sum.inl m
            | Sum.inr (Sum.inr _) => Sum.inr ()
          left_inv := ?_
          right_inv := ?_ }
      · intro z
        rcases z with m | u <;> rfl
      · intro p
        rcases p with ⟨p, hp⟩
        apply Subtype.ext
        rcases p with xy | p
        · change False at hp
          exact hp.elim
        · rcases p with m | u <;> rfl

lemma card_pointsOnLine {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (l : Line F) :
    (pointsOnLine l).card = Fintype.card F + 1 := by
  classical
  calc
    (pointsOnLine l).card = Fintype.card {p : Point F // Incident p l} := by
      simpa [pointsOnLine] using
        (Fintype.card_subtype (fun p : Point F ↦ Incident p l)).symm
    _ = Fintype.card (F ⊕ Unit) :=
      (Fintype.card_congr (pointsOnLineEquiv l)).symm
    _ = Fintype.card F + 1 := by simp

noncomputable def linesThrough {F : Type*} [Fintype F] [Mul F] [Add F]
    [DecidableEq F] (p : Point F) : Finset (Line F) :=
  Finset.univ.filter fun l ↦ Incident p l

@[simp] lemma mem_linesThrough_iff {F : Type*} [Fintype F]
    [Mul F] [Add F] [DecidableEq F] (p : Point F) (l : Line F) :
    l ∈ linesThrough p ↔ Incident p l := by
  simp [linesThrough]

/-- Dually, the lines through a point are parametrized by the field and one
vertical or infinite line. -/
noncomputable def linesThroughEquiv {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (p : Point F) :
    (F ⊕ Unit) ≃ {l : Line F // Incident p l} := by
  rcases p with xy | p
  · rcases xy with ⟨x, y⟩
    refine
      { toFun := fun z ↦ match z with
          | Sum.inl m => ⟨graph m (y - m * x), by
              change y = m * x + (y - m * x)
              ring⟩
          | Sum.inr _ => ⟨verticalLine x, rfl⟩
        invFun := fun l ↦ match l.1 with
          | Sum.inl mb => Sum.inl mb.1
          | Sum.inr (Sum.inl _) => Sum.inr ()
          | Sum.inr (Sum.inr _) => Sum.inr ()
        left_inv := ?_
        right_inv := ?_ }
    · intro z
      rcases z with m | u <;> rfl
    · intro l
      rcases l with ⟨l, hl⟩
      apply Subtype.ext
      rcases l with mb | l
      · rcases mb with ⟨m, b⟩
        change y = m * x + b at hl
        simp only [graph, Sum.inl.injEq, Prod.mk.injEq, true_and]
        linear_combination hl
      · rcases l with c | u
        · change x = c at hl
          subst c
          rfl
        · change False at hl
          exact hl.elim
  · rcases p with s | u
    · refine
        { toFun := fun z ↦ match z with
            | Sum.inl b => ⟨graph s b, rfl⟩
            | Sum.inr _ => ⟨horizon, trivial⟩
          invFun := fun l ↦ match l.1 with
            | Sum.inl mb => Sum.inl mb.2
            | Sum.inr (Sum.inl _) => Sum.inr ()
            | Sum.inr (Sum.inr _) => Sum.inr ()
          left_inv := ?_
          right_inv := ?_ }
      · intro z
        rcases z with b | u <;> rfl
      · intro l
        rcases l with ⟨l, hl⟩
        apply Subtype.ext
        rcases l with mb | l
        · rcases mb with ⟨m, b⟩
          change s = m at hl
          subst m
          rfl
        · rcases l with c | u
          · change False at hl
            exact hl.elim
          · rfl
    · refine
        { toFun := fun z ↦ match z with
            | Sum.inl c => ⟨verticalLine c, trivial⟩
            | Sum.inr _ => ⟨horizon, trivial⟩
          invFun := fun l ↦ match l.1 with
            | Sum.inl _ => Sum.inr ()
            | Sum.inr (Sum.inl c) => Sum.inl c
            | Sum.inr (Sum.inr _) => Sum.inr ()
          left_inv := ?_
          right_inv := ?_ }
      · intro z
        rcases z with c | u <;> rfl
      · intro l
        rcases l with ⟨l, hl⟩
        apply Subtype.ext
        rcases l with mb | l
        · change False at hl
          exact hl.elim
        · rcases l with c | u <;> rfl

lemma card_linesThrough {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (p : Point F) :
    (linesThrough p).card = Fintype.card F + 1 := by
  classical
  calc
    (linesThrough p).card = Fintype.card {l : Line F // Incident p l} := by
      simpa [linesThrough] using
        (Fintype.card_subtype (fun l : Line F ↦ Incident p l)).symm
    _ = Fintype.card (F ⊕ Unit) :=
      (Fintype.card_congr (linesThroughEquiv p)).symm
    _ = Fintype.card F + 1 := by simp

/-- A convenient polarity of the coordinate plane. -/
def dualPoint {F : Type*} [Neg F] : Line F → Point F
  | Sum.inl (m, b) => affine m (-b)
  | Sum.inr (Sum.inl c) => slope c
  | Sum.inr (Sum.inr _) => verticalInfinity

def dualLine {F : Type*} [Neg F] : Point F → Line F
  | Sum.inl (x, y) => graph x (-y)
  | Sum.inr (Sum.inl s) => verticalLine s
  | Sum.inr (Sum.inr _) => horizon

@[simp] lemma dualLine_dualPoint {F : Type*} [AddGroup F]
    (l : Line F) : dualLine (dualPoint l) = l := by
  rcases l with mb | l
  · rcases mb with ⟨m, b⟩
    simp [dualPoint, dualLine, affine, graph]
  · rcases l with c | u <;> rfl

@[simp] lemma dualPoint_dualLine {F : Type*} [AddGroup F]
    (p : Point F) : dualPoint (dualLine p) = p := by
  rcases p with xy | p
  · rcases xy with ⟨x, y⟩
    simp [dualPoint, dualLine, affine, graph]
  · rcases p with s | u <;> rfl

lemma dualPoint_injective {F : Type*} [AddGroup F] :
    Function.Injective (dualPoint : Line F → Point F) := by
  intro l m h
  have := congrArg dualLine h
  simpa using this

lemma dualLine_injective {F : Type*} [AddGroup F] :
    Function.Injective (dualLine : Point F → Line F) := by
  intro p q h
  have := congrArg dualPoint h
  simpa using this

/-- Incidence is symmetric under the chosen polarity. -/
lemma incident_dual {F : Type*} [CommRing F] [DecidableEq F]
    (p : Point F) (l : Line F) :
    Incident p l ↔ Incident (dualPoint l) (dualLine p) := by
  rcases p with xy | p
  · rcases xy with ⟨x, y⟩
    rcases l with mb | l
    · rcases mb with ⟨m, b⟩
      change y = m * x + b ↔ -b = x * m + -y
      constructor <;> intro h <;> linear_combination h
    · rcases l with c | u
      · simp [Incident, dualPoint, dualLine, slope, graph, affine,
          verticalLine, eq_comm]
      · rfl
  · rcases p with s | u
    · rcases l with mb | l
      · rcases mb with ⟨m, b⟩
        simp [Incident, dualPoint, dualLine, slope, graph, affine,
          verticalLine, eq_comm]
      · rcases l with c | u <;> rfl
    · rcases l with mb | l
      · rcases mb with ⟨m, b⟩
        rfl
      · rcases l with c | u <;> rfl

private lemma line_eq_vertical_of_two_affine_same_x
    {F : Type*} [Field F] [DecidableEq F] {x y z : F} (hyz : y ≠ z)
    {l : Line F} (hy : Incident (affine x y) l)
    (hz : Incident (affine x z) l) : l = verticalLine x := by
  rcases l with mb | l
  · rcases mb with ⟨m, b⟩
    change y = m * x + b at hy
    change z = m * x + b at hz
    exact (hyz (hy.trans hz.symm)).elim
  · rcases l with c | u
    · change x = c at hy
      subst c
      rfl
    · change False at hy
      exact hy.elim

private lemma line_eq_of_two_affine_distinct_x
    {F : Type*} [Field F] [DecidableEq F]
    {x y x' y' : F} (hxx : x ≠ x') {l m : Line F}
    (hl : Incident (affine x y) l) (hl' : Incident (affine x' y') l)
    (hm : Incident (affine x y) m) (hm' : Incident (affine x' y') m) :
    l = m := by
  have lgraph : ∃ a b : F, l = graph a b := by
    rcases l with ab | l
    · exact ⟨ab.1, ab.2, rfl⟩
    · rcases l with c | u
      · change x = c at hl
        change x' = c at hl'
        exact (hxx (hl.trans hl'.symm)).elim
      · change False at hl
        exact hl.elim
  have mgraph : ∃ c d : F, m = graph c d := by
    rcases m with cd | m
    · exact ⟨cd.1, cd.2, rfl⟩
    · rcases m with c | u
      · change x = c at hm
        change x' = c at hm'
        exact (hxx (hm.trans hm'.symm)).elim
      · change False at hm
        exact hm.elim
  obtain ⟨a, b, rfl⟩ := lgraph
  obtain ⟨c, d, rfl⟩ := mgraph
  change y = a * x + b at hl
  change y' = a * x' + b at hl'
  change y = c * x + d at hm
  change y' = c * x' + d at hm'
  have ha : a * (x' - x) = y' - y := by
    rw [hl', hl]
    ring
  have hc : c * (x' - x) = y' - y := by
    rw [hm', hm]
    ring
  have hacprod : (a - c) * (x' - x) = 0 := by
    calc
      (a - c) * (x' - x) = a * (x' - x) - c * (x' - x) := by ring
      _ = 0 := by rw [ha, hc, sub_self]
  have hdiff : x' - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxx)
  have hac : a = c := sub_eq_zero.mp ((mul_eq_zero.mp hacprod).resolve_right hdiff)
  subst c
  have hbd : b = d := by
    calc
      b = y - a * x := by rw [hl]; ring
      _ = d := by rw [hm]; ring
  subst d
  rfl

private lemma line_eq_graph_of_affine_slope
    {F : Type*} [Field F] [DecidableEq F] {x y s : F} {l : Line F}
    (ha : Incident (affine x y) l) (hs : Incident (slope s) l) :
    l = graph s (y - s * x) := by
  rcases l with mb | l
  · rcases mb with ⟨m, b⟩
    change y = m * x + b at ha
    change s = m at hs
    subst m
    simp only [graph, Sum.inl.injEq, Prod.mk.injEq, true_and]
    rw [ha]
    ring
  · rcases l with c | u
    · change False at hs
      exact hs.elim
    · change False at ha
      exact ha.elim

private lemma line_eq_vertical_of_affine_verticalInfinity
    {F : Type*} [Field F] [DecidableEq F] {x y : F} {l : Line F}
    (ha : Incident (affine x y) l) (hv : Incident verticalInfinity l) :
    l = verticalLine x := by
  rcases l with mb | l
  · change False at hv
    exact hv.elim
  · rcases l with c | u
    · change x = c at ha
      subst c
      rfl
    · change False at ha
      exact ha.elim

private lemma line_eq_horizon_of_two_distinct_slopes
    {F : Type*} [Field F] [DecidableEq F] {s u : F} (hsu : s ≠ u)
    {l : Line F} (hs : Incident (slope s) l) (hu : Incident (slope u) l) :
    l = horizon := by
  rcases l with mb | l
  · rcases mb with ⟨m, b⟩
    change s = m at hs
    change u = m at hu
    exact (hsu (hs.trans hu.symm)).elim
  · rcases l with c | v
    · change False at hs
      exact hs.elim
    · rfl

private lemma line_eq_horizon_of_slope_verticalInfinity
    {F : Type*} [Field F] [DecidableEq F] {s : F} {l : Line F}
    (hs : Incident (slope s) l) (hv : Incident verticalInfinity l) :
    l = horizon := by
  rcases l with mb | l
  · change False at hv
    exact hv.elim
  · rcases l with c | u
    · change False at hs
      exact hs.elim
    · rfl

/-- Two distinct projective points determine at most one coordinate line. -/
lemma line_unique_of_two_points {F : Type*} [Field F] [DecidableEq F]
    {p q : Point F} (hpq : p ≠ q) {l m : Line F}
    (hpl : Incident p l) (hql : Incident q l)
    (hpm : Incident p m) (hqm : Incident q m) : l = m := by
  rcases p with xy | p
  · rcases xy with ⟨x, y⟩
    rcases q with xy' | q
    · rcases xy' with ⟨x', y'⟩
      by_cases hxx : x = x'
      · subst x'
        have hyy : y ≠ y' := by
          intro h
          apply hpq
          simp [h]
        exact (line_eq_vertical_of_two_affine_same_x hyy hpl hql).trans
          (line_eq_vertical_of_two_affine_same_x hyy hpm hqm).symm
      · exact line_eq_of_two_affine_distinct_x hxx hpl hql hpm hqm
    · rcases q with s | u
      · exact (line_eq_graph_of_affine_slope hpl hql).trans
          (line_eq_graph_of_affine_slope hpm hqm).symm
      · exact (line_eq_vertical_of_affine_verticalInfinity hpl hql).trans
          (line_eq_vertical_of_affine_verticalInfinity hpm hqm).symm
  · rcases p with s | u
    · rcases q with xy | q
      · rcases xy with ⟨x, y⟩
        exact (line_eq_graph_of_affine_slope hql hpl).trans
          (line_eq_graph_of_affine_slope hqm hpm).symm
      · rcases q with v | u
        · have hsv : s ≠ v := by
            intro h
            apply hpq
            simp [h]
          exact (line_eq_horizon_of_two_distinct_slopes hsv hpl hql).trans
            (line_eq_horizon_of_two_distinct_slopes hsv hpm hqm).symm
        · exact (line_eq_horizon_of_slope_verticalInfinity hpl hql).trans
            (line_eq_horizon_of_slope_verticalInfinity hpm hqm).symm
    · rcases q with xy | q
      · rcases xy with ⟨x, y⟩
        exact (line_eq_vertical_of_affine_verticalInfinity hql hpl).trans
          (line_eq_vertical_of_affine_verticalInfinity hqm hpm).symm
      · rcases q with s | v
        · exact (line_eq_horizon_of_slope_verticalInfinity hql hpl).trans
            (line_eq_horizon_of_slope_verticalInfinity hqm hpm).symm
        · exact (hpq rfl).elim

/-- Dually, two distinct projective lines meet in at most one point. -/
lemma point_unique_of_two_lines {F : Type*} [Field F] [DecidableEq F]
    {l m : Line F} (hlm : l ≠ m) {p q : Point F}
    (hpl : Incident p l) (hpm : Incident p m)
    (hql : Incident q l) (hqm : Incident q m) : p = q := by
  apply dualLine_injective
  apply line_unique_of_two_points (dualPoint_injective.ne hlm)
  · exact (incident_dual p l).mp hpl
  · exact (incident_dual p m).mp hpm
  · exact (incident_dual q l).mp hql
  · exact (incident_dual q m).mp hqm

/-- Any two coordinate projective lines have a common point. -/
lemma pair_lines_meet {F : Type*} [Field F] [DecidableEq F]
    (l m : Line F) : ∃ p : Point F, Incident p l ∧ Incident p m := by
  obtain ⟨n, hln, hmn⟩ := pair_on_line (dualPoint l) (dualPoint m)
  refine ⟨dualPoint n, ?_, ?_⟩
  · exact (incident_dual (dualPoint n) l).mpr (by simpa using hln)
  · exact (incident_dual (dualPoint n) m).mpr (by simpa using hmn)

/-- A chosen intersection point of two coordinate projective lines. -/
noncomputable def intersectionPoint {F : Type*} [Field F] [DecidableEq F]
    (l m : Line F) : Point F :=
  Classical.choose (pair_lines_meet l m)

lemma intersectionPoint_incident_left {F : Type*} [Field F] [DecidableEq F]
    (l m : Line F) : Incident (intersectionPoint l m) l :=
  (Classical.choose_spec (pair_lines_meet l m)).1

lemma intersectionPoint_incident_right {F : Type*} [Field F] [DecidableEq F]
    (l m : Line F) : Incident (intersectionPoint l m) m :=
  (Classical.choose_spec (pair_lines_meet l m)).2

lemma intersectionPoint_eq_of_ne {F : Type*} [Field F] [DecidableEq F]
    {l m : Line F} (hlm : l ≠ m) {p : Point F}
    (hpl : Incident p l) (hpm : Incident p m) :
    intersectionPoint l m = p := by
  exact point_unique_of_two_lines hlm
    (intersectionPoint_incident_left l m)
    (intersectionPoint_incident_right l m) hpl hpm

lemma intersectionPoint_comm_of_ne {F : Type*} [Field F] [DecidableEq F]
    {l m : Line F} (hlm : l ≠ m) :
    intersectionPoint l m = intersectionPoint m l := by
  apply point_unique_of_two_lines hlm
  · exact intersectionPoint_incident_left l m
  · exact intersectionPoint_incident_right l m
  · exact intersectionPoint_incident_right m l
  · exact intersectionPoint_incident_left m l

/-- A chosen projective line through two points.  It is only used with
distinct points, where projective uniqueness makes the choice canonical. -/
noncomputable def lineThroughPoints {F : Type*} [Field F] [DecidableEq F]
    (p q : Point F) : Line F :=
  Classical.choose (pair_on_line p q)

lemma lineThroughPoints_incident_left {F : Type*} [Field F]
    [DecidableEq F] (p q : Point F) :
    Incident p (lineThroughPoints p q) :=
  (Classical.choose_spec (pair_on_line p q)).1

lemma lineThroughPoints_incident_right {F : Type*} [Field F]
    [DecidableEq F] (p q : Point F) :
    Incident q (lineThroughPoints p q) :=
  (Classical.choose_spec (pair_on_line p q)).2

lemma lineThroughPoints_eq_of_ne {F : Type*} [Field F]
    [DecidableEq F] {p q : Point F} (hpq : p ≠ q) {l : Line F}
    (hpl : Incident p l) (hql : Incident q l) :
    lineThroughPoints p q = l := by
  exact line_unique_of_two_points hpq
    (lineThroughPoints_incident_left p q)
    (lineThroughPoints_incident_right p q) hpl hql

end Projective

/-! ## Incidence labels on the fixed projective plane -/

namespace Labels

open Projective

/-! ### A finite Boolean equality count -/

/-- A Boolean function is constant on the indicated finite set. -/
def ConstantOn {I : Type*} [DecidableEq I]
    (S : Finset I) (f : I → Bool) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, f i = f j

/-- Boolean functions constant on `S`. -/
def ConstantFunctions (I : Type*) [Fintype I] [DecidableEq I]
    (S : Finset I) := {f : I → Bool // ConstantOn S f}

noncomputable instance {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) : Fintype (ConstantFunctions I S) := by
  letI : Finite (ConstantFunctions I S) :=
    Finite.of_injective (fun f : ConstantFunctions I S ↦ f.1)
      Subtype.coe_injective
  exact Fintype.ofFinite _

/-- Once one value on a nonempty constant set is retained, the remaining
free data are precisely the values off that set. -/
noncomputable def constantFunctionsEquivOfNonempty
    {I : Type*} [Fintype I] [DecidableEq I]
    {S : Finset I} (hS : S.Nonempty) :
    ConstantFunctions I S ≃ Bool × ({i : I // i ∉ S} → Bool) := by
  let s : I := hS.choose
  have hs : s ∈ S := hS.choose_spec
  refine
    { toFun := fun f ↦ (f.1 s, fun i ↦ f.1 i.1)
      invFun := fun bg ↦
        ⟨fun i ↦ if hi : i ∈ S then bg.1 else bg.2 ⟨i, hi⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro i hi j hj
    simp [hi, hj]
  · intro f
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceDIte]
      exact (f.2 i hi s hs).symm
    · simp [hi]
  · intro bg
    apply Prod.ext
    · simp [hs]
    · funext i
      simp [i.2]

/-- Requiring `d` Boolean variables to be equal removes exactly `d-1`
binary degrees of freedom.  This cross-multiplied formulation also covers
the empty set without a separate exponent convention. -/
lemma card_constantFunctions_mul_pow
    {I : Type*} [Fintype I] [DecidableEq I] (S : Finset I) :
    Fintype.card (ConstantFunctions I S) * 2 ^ (S.card - 1) =
      2 ^ Fintype.card I := by
  classical
  by_cases hS : S.Nonempty
  · have hScard : 0 < S.card := Finset.card_pos.mpr hS
    have hSle : S.card ≤ Fintype.card I := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    rw [Fintype.card_congr (constantFunctionsEquivOfNonempty hS),
      Fintype.card_prod, Fintype.card_bool, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_subtype_compl]
    have hmemcard : Fintype.card {i : I // i ∈ S} = S.card := by simp
    rw [hmemcard]
    calc
      2 * 2 ^ (Fintype.card I - S.card) * 2 ^ (S.card - 1) =
          2 ^ ((Fintype.card I - S.card) + 1 + (S.card - 1)) := by
        rw [← pow_succ', ← pow_add]
      _ = 2 ^ Fintype.card I := by congr 1; omega
  · have hSempt : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    let e : ConstantFunctions I ∅ ≃ (I → Bool) :=
      { toFun := fun f ↦ f.1
        invFun := fun f ↦ ⟨f, by simp [ConstantOn]⟩
        left_inv := fun _ ↦ Subtype.ext rfl
        right_inv := fun _ ↦ rfl }
    rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool]
    simp

/-- A Boolean label on every line--point incidence. -/
abbrev Labeling (F : Type*) [Mul F] [Add F] [DecidableEq F] :=
  (l : Line F) → {p : Point F // Incident p l} → Bool

/-- A single incidence coordinate. -/
abbrev Incidence (F : Type*) [Mul F] [Add F] [DecidableEq F] :=
  Σ l : Line F, {p : Point F // Incident p l}

/-- Curry/uncurry a labeling into a Boolean function on the incidence set. -/
def labelingEquivFlat {F : Type*} [Mul F] [Add F] [DecidableEq F] :
    Labeling F ≃ (Incidence F → Bool) where
  toFun a z := a z.1 z.2
  invFun a l p := a ⟨l, p⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_incidence {F : Type*} [Fintype F] [Field F] [DecidableEq F] :
    Fintype.card (Incidence F) =
      (Fintype.card F ^ 2 + Fintype.card F + 1) *
        (Fintype.card F + 1) := by
  classical
  rw [Fintype.card_sigma]
  calc
    ∑ l : Line F, Fintype.card {p : Point F // Incident p l} =
        ∑ _l : Line F, (Fintype.card F + 1) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Fintype.card_subtype]
      simpa [pointsOnLine] using card_pointsOnLine l
    _ = (Fintype.card F ^ 2 + Fintype.card F + 1) *
        (Fintype.card F + 1) := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
        card_line]

lemma card_labeling {F : Type*} [Fintype F] [Field F] [DecidableEq F] :
    Fintype.card (Labeling F) =
      2 ^ ((Fintype.card F ^ 2 + Fintype.card F + 1) *
        (Fintype.card F + 1)) := by
  rw [Fintype.card_congr labelingEquivFlat, Fintype.card_fun,
    Fintype.card_bool, card_incidence]

/-- Two distinct lines agree when their labels at their intersection agree.
The definition is also total when the lines coincide, though only the
distinct-line case is used. -/
def Agree {F : Type*} [Field F] [DecidableEq F]
    (a : Labeling F) (l m : Line F) : Prop :=
  a l ⟨intersectionPoint l m, intersectionPoint_incident_left l m⟩ =
    a m ⟨intersectionPoint l m, intersectionPoint_incident_right l m⟩

/-- Incidences on a line at which its label differs from a proposed global
point-labeling. -/
noncomputable def mismatches {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (a : Labeling F) (gamma : Point F → Bool)
    (l : Line F) : Finset {p : Point F // Incident p l} :=
  Finset.univ.filter fun p ↦ a l p ≠ gamma p.1

@[simp] lemma mem_mismatches_iff {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (a : Labeling F) (gamma : Point F → Bool)
    (l : Line F) (p : {p : Point F // Incident p l}) :
    p ∈ mismatches a gamma l ↔ a l p ≠ gamma p.1 := by
  simp [mismatches]

/-- Kahn's balance condition on every pencil viewed from an exterior line.
The integer form avoids square roots; later we instantiate `balance` by a
fixed quantity that is `K/2+o(K)`. -/
def IsBalanced {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (balance : ℕ) (a : Labeling F) : Prop :=
  ∀ (x : Point F) (m : Line F), ¬ Incident x m →
    ((linesThrough x).filter fun l ↦ Agree a l m).card ≤ balance ∧
    ((linesThrough x).filter fun l ↦ ¬ Agree a l m).card ≤ balance

/-- The robust concentration condition needed in the cover argument.  If a
large set of line labels is close to one global labeling, all but fewer than
`4*C0` of those lines form one pencil. -/
def IsPencilForcing {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (C0 : ℕ) (a : Labeling F) : Prop :=
  ∀ (gamma : Point F → Bool) (T : Finset (Line F)),
    3 * Fintype.card F ≤ 4 * T.card →
    (∀ l ∈ T, (mismatches a gamma l).card ≤ C0) →
    ∃ x : Point F,
      (T.filter fun l ↦ ¬ Incident x l).card < 4 * C0

/-- The two fixed-plane properties, bundled for use by the global
construction. -/
structure IsGood {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (balance C0 : ℕ) (a : Labeling F) : Prop where
  balanced : IsBalanced balance a
  pencilForcing : IsPencilForcing C0 a

/-! ### Compatibility configurations and their exact label count -/

/-- Exceptional incidences attached only to the selected lines. -/
abbrev Exceptions {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (T : Finset (Line F)) :=
  (l : {l : Line F // l ∈ T}) → Finset {p : Point F // Incident p l.1}

/-- The selected lines whose incidence at `p` is not exceptional. -/
noncomputable def activeLines {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (T : Finset (Line F)) (Z : Exceptions T)
    (p : Point F) : Finset {l : Line F // Incident p l} :=
  Finset.univ.filter fun l ↦
    ∃ h : l.1 ∈ T,
      (⟨p, l.2⟩ : {q : Point F // Incident q l.1}) ∉ Z ⟨l.1, h⟩

@[simp] lemma mem_activeLines_iff {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (T : Finset (Line F)) (Z : Exceptions T)
    (p : Point F) (l : {l : Line F // Incident p l}) :
    l ∈ activeLines T Z p ↔
      ∃ h : l.1 ∈ T,
        (⟨p, l.2⟩ : {q : Point F // Incident q l.1}) ∉ Z ⟨l.1, h⟩ := by
  simp [activeLines]

/-- At each point all selected nonexceptional incidence labels agree. -/
def Compatible {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (a : Labeling F) (T : Finset (Line F)) (Z : Exceptions T) : Prop :=
  ∀ p : Point F,
    ConstantOn (activeLines T Z p)
      (fun l ↦ a l.1 ⟨p, l.2⟩)

/-- The number of independent equality constraints in a configuration. -/
noncomputable def energy {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (T : Finset (Line F)) (Z : Exceptions T) : ℕ :=
  ∑ p : Point F, ((activeLines T Z p).card - 1)

/-- Re-index incidence labels by their point rather than by their line. -/
def labelingEquivByPoint {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] :
    Labeling F ≃ ((p : Point F) → {l : Line F // Incident p l} → Bool) where
  toFun a p l := a l.1 ⟨p, l.2⟩
  invFun a l p := a p.1 ⟨l, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Compatible labelings factor independently over the points. -/
noncomputable def compatibleLabelingsEquiv
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (T : Finset (Line F)) (Z : Exceptions T) :
    {a : Labeling F // Compatible a T Z} ≃
      ((p : Point F) →
        ConstantFunctions {l : Line F // Incident p l} (activeLines T Z p)) :=
  { toFun := fun a p ↦ ⟨labelingEquivByPoint a.1 p, a.2 p⟩
    invFun := fun g ↦
      ⟨labelingEquivByPoint.symm (fun p ↦ (g p).1), fun p ↦ (g p).2⟩
    left_inv := by intro a; apply Subtype.ext; rfl
    right_inv := by intro g; rfl }

noncomputable instance {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (T : Finset (Line F)) (Z : Exceptions T) :
    Fintype {a : Labeling F // Compatible a T Z} := by
  letI : Finite {a : Labeling F // Compatible a T Z} :=
    Finite.of_injective (fun a : {a : Labeling F // Compatible a T Z} ↦ a.1)
      Subtype.coe_injective
  exact Fintype.ofFinite _

/-- Kahn's probability `2^{-energy}` with all division removed. -/
lemma card_compatible_mul_pow_energy
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (T : Finset (Line F)) (Z : Exceptions T) :
    Fintype.card {a : Labeling F // Compatible a T Z} *
        2 ^ energy T Z = Fintype.card (Labeling F) := by
  classical
  rw [Fintype.card_congr (compatibleLabelingsEquiv T Z), Fintype.card_pi]
  have hprod :
      (∏ p : Point F,
          Fintype.card
            (ConstantFunctions {l : Line F // Incident p l}
              (activeLines T Z p))) *
          (∏ p : Point F, 2 ^ ((activeLines T Z p).card - 1)) =
        ∏ p : Point F, 2 ^ Fintype.card {l : Line F // Incident p l} := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    exact card_constantFunctions_mul_pow (activeLines T Z p)
  change
    (∏ p : Point F,
        Fintype.card
          (ConstantFunctions {l : Line F // Incident p l}
            (activeLines T Z p))) *
      2 ^ (∑ p : Point F, ((activeLines T Z p).card - 1)) =
        Fintype.card (Labeling F)
  have hpow :
      2 ^ (∑ p : Point F, ((activeLines T Z p).card - 1)) =
        ∏ p : Point F, 2 ^ ((activeLines T Z p).card - 1) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Point F))
        (fun p ↦ (activeLines T Z p).card - 1) 2).symm
  rw [hpow, hprod]
  rw [card_labeling]
  simp only [Fintype.card_subtype]
  have hpencil : ∀ p : Point F,
      #{l : Line F | Incident p l} = Fintype.card F + 1 := by
    intro p
    simpa [linesThrough] using card_linesThrough p
  simp_rw [hpencil]
  rw [Finset.prod_const, Finset.card_univ, card_point, Nat.pow_mul]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Exceptional sets of one prescribed cardinality on one line. -/
def ExactExceptionSet {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (l : Line F) (C0 : ℕ) :=
  {Z : Finset {p : Point F // Incident p l} // Z.card = C0}

noncomputable def exactExceptionSetEquivPowersetCard
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (l : Line F) (C0 : ℕ) :
    ExactExceptionSet l C0 ≃
      {Z : Finset {p : Point F // Incident p l} //
        Z ∈ Finset.univ.powersetCard C0} where
  toFun Z := ⟨Z.1, by simp [Z.2]⟩
  invFun Z := ⟨Z.1, (Finset.mem_powersetCard.mp Z.2).2⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; rfl

noncomputable instance {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (l : Line F) (C0 : ℕ) :
    Fintype (ExactExceptionSet l C0) :=
  Fintype.ofEquiv
    {Z : Finset {p : Point F // Incident p l} //
      Z ∈ Finset.univ.powersetCard C0}
    (exactExceptionSetEquivPowersetCard l C0).symm

lemma card_exactExceptionSet {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (l : Line F) (C0 : ℕ) :
    Fintype.card (ExactExceptionSet l C0) =
      (Fintype.card F + 1).choose C0 := by
  classical
  rw [Fintype.card_congr (exactExceptionSetEquivPowersetCard l C0),
    Fintype.card_coe, Finset.card_powersetCard]
  have hline : Fintype.card {p : Point F // Incident p l} =
      Fintype.card F + 1 := by
    rw [Fintype.card_subtype]
    simpa [pointsOnLine] using card_pointsOnLine l
  rw [Finset.card_univ, hline]

/-- Assign one exact exceptional set to every selected line. -/
def ExactExceptions {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (T : Finset (Line F)) (C0 : ℕ) :=
  {Z : Exceptions T // ∀ l, (Z l).card = C0}

noncomputable def exactExceptionsEquiv
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (T : Finset (Line F)) (C0 : ℕ) :
    ExactExceptions T C0 ≃
      ((l : {l : Line F // l ∈ T}) → ExactExceptionSet l.1 C0) where
  toFun Z l := ⟨Z.1 l, Z.2 l⟩
  invFun Z := ⟨fun l ↦ (Z l).1, fun l ↦ (Z l).2⟩
  left_inv Z := by apply Subtype.ext; rfl
  right_inv _ := rfl

noncomputable instance {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (T : Finset (Line F)) (C0 : ℕ) :
    Fintype (ExactExceptions T C0) :=
  Fintype.ofEquiv
    ((l : {l : Line F // l ∈ T}) → ExactExceptionSet l.1 C0)
    (exactExceptionsEquiv T C0).symm

lemma card_exactExceptions_le
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (T : Finset (Line F)) (C0 : ℕ) :
    Fintype.card (ExactExceptions T C0) ≤
      (Fintype.card F + 1) ^ (C0 * T.card) := by
  classical
  rw [Fintype.card_congr (exactExceptionsEquiv T C0), Fintype.card_pi]
  calc
    (∏ l : {l : Line F // l ∈ T},
        Fintype.card (ExactExceptionSet l.1 C0)) ≤
        ∏ _l : {l : Line F // l ∈ T},
          (Fintype.card F + 1) ^ C0 := by
      apply Finset.prod_le_prod
      · intro l _
        exact Nat.zero_le _
      intro l _
      rw [card_exactExceptionSet]
      exact Nat.choose_le_pow _ _
    _ = ((Fintype.card F + 1) ^ C0) ^ T.card := by simp
    _ = (Fintype.card F + 1) ^ (C0 * T.card) := by rw [pow_mul]

/-- Sets of at most `C0` bad incidences may be enlarged to exact size
`C0`, provided a line has at least that many points. -/
lemma exists_exactExceptions_superset
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {C0 : ℕ} (hC0 : C0 ≤ Fintype.card F + 1)
    (a : Labeling F) (gamma : Point F → Bool) (T : Finset (Line F))
    (hbad : ∀ l ∈ T, (mismatches a gamma l).card ≤ C0) :
    ∃ Z : ExactExceptions T C0,
      ∀ l, mismatches a gamma l.1 ⊆ Z.1 l := by
  classical
  have hline : ∀ l : Line F,
      C0 ≤ Fintype.card {p : Point F // Incident p l} := by
    intro l
    have hc : Fintype.card {p : Point F // Incident p l} =
        Fintype.card F + 1 := by
      rw [Fintype.card_subtype]
      simpa [pointsOnLine] using card_pointsOnLine l
    rw [hc]
    exact hC0
  have hchoice : ∀ l : {l : Line F // l ∈ T},
      ∃ Z : Finset {p : Point F // Incident p l.1},
        mismatches a gamma l.1 ⊆ Z ∧ Z.card = C0 := by
    intro l
    exact Finset.exists_superset_card_eq (hbad l.1 l.2) (hline l.1)
  choose Z hZsub hZcard using hchoice
  exact ⟨⟨Z, hZcard⟩, hZsub⟩

lemma compatible_of_mismatches_subset
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (a : Labeling F) (gamma : Point F → Bool) (T : Finset (Line F))
    (Z : Exceptions T)
    (hsub : ∀ l, mismatches a gamma l.1 ⊆ Z l) :
    Compatible a T Z := by
  intro p l hl m hm
  obtain ⟨hlT, hlZ⟩ := (mem_activeLines_iff T Z p l).mp hl
  obtain ⟨hmT, hmZ⟩ := (mem_activeLines_iff T Z p m).mp hm
  have hlnot :
      (⟨p, l.2⟩ : {q : Point F // Incident q l.1}) ∉
        mismatches a gamma l.1 := by
    intro h
    exact hlZ (hsub ⟨l.1, hlT⟩ h)
  have hmnot :
      (⟨p, m.2⟩ : {q : Point F // Incident q m.1}) ∉
        mismatches a gamma m.1 := by
    intro h
    exact hmZ (hsub ⟨m.1, hmT⟩ h)
  have hla : a l.1 ⟨p, l.2⟩ = gamma p := by
    by_contra h
    exact hlnot ((mem_mismatches_iff a gamma l.1 _).mpr h)
  have hma : a m.1 ⟨p, m.2⟩ = gamma p := by
    by_contra h
    exact hmnot ((mem_mismatches_iff a gamma m.1 _).mpr h)
  exact hla.trans hma.symm

/-! ### The incidence-energy double count -/

/-- Number of selected lines through a point. -/
noncomputable def lineDegree {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (T : Finset (Line F)) (p : Point F) : ℕ :=
  (T.filter fun l ↦ Incident p l).card

/-- Ordered distinct pairs of selected lines. -/
noncomputable def selectedPairs {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (T : Finset (Line F)) :
    Finset ({l : Line F // l ∈ T} × {l : Line F // l ∈ T}) :=
  (Finset.univ : Finset {l : Line F // l ∈ T}).offDiag

lemma card_selectedPairs {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (T : Finset (Line F)) :
    (selectedPairs T).card = T.card * (T.card - 1) := by
  classical
  rw [selectedPairs, Finset.offDiag_card]
  simp
  rw [Nat.mul_sub_left_distrib, mul_one]

noncomputable def pairIntersectionLeft {F : Type*} [Field F] [DecidableEq F]
    {T : Finset (Line F)}
    (e : {l : Line F // l ∈ T} × {l : Line F // l ∈ T}) :
    {p : Point F // Incident p e.1.1} :=
  ⟨intersectionPoint e.1.1 e.2.1,
    intersectionPoint_incident_left e.1.1 e.2.1⟩

noncomputable def pairIntersectionRight {F : Type*} [Field F] [DecidableEq F]
    {T : Finset (Line F)}
    (e : {l : Line F // l ∈ T} × {l : Line F // l ∈ T}) :
    {p : Point F // Incident p e.2.1} :=
  ⟨intersectionPoint e.1.1 e.2.1,
    intersectionPoint_incident_right e.1.1 e.2.1⟩

/-- Ordered pairs destroyed by an exception on their first line. -/
noncomputable def leftBadPairs {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)} (Z : Exceptions T) :
    Finset ({l : Line F // l ∈ T} × {l : Line F // l ∈ T}) :=
  (selectedPairs T).filter fun e ↦ pairIntersectionLeft e ∈ Z e.1

/-- Ordered pairs destroyed by an exception on their second line. -/
noncomputable def rightBadPairs {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)} (Z : Exceptions T) :
    Finset ({l : Line F // l ∈ T} × {l : Line F // l ∈ T}) :=
  (selectedPairs T).filter fun e ↦ pairIntersectionRight e ∈ Z e.2

/-- Selected lines through the underlying point of an exceptional
incidence, paired with one fixed first line. -/
noncomputable def leftCandidates {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)}
    (l : {l : Line F // l ∈ T})
    (z : {p : Point F // Incident p l.1}) :
    Finset ({l : Line F // l ∈ T} × {l : Line F // l ∈ T}) :=
  ((Finset.univ : Finset {m : Line F // m ∈ T}).filter
      fun m ↦ Incident z.1 m.1).image fun m ↦ (l, m)

lemma card_selected_through {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (T : Finset (Line F)) (p : Point F) :
    ((Finset.univ : Finset {m : Line F // m ∈ T}).filter
      fun m ↦ Incident p m.1).card = lineDegree T p := by
  classical
  let e : {m : Line F // m ∈ T} ↪ Line F :=
    { toFun := Subtype.val
      inj' := Subtype.coe_injective }
  have himage :
      (((Finset.univ : Finset {m : Line F // m ∈ T}).filter
        fun m ↦ Incident p m.1).map e) =
          T.filter fun m ↦ Incident p m := by
    ext m
    simp [e, and_comm]
  have hcard := congrArg Finset.card himage
  rw [Finset.card_map] at hcard
  simpa [lineDegree] using hcard

lemma card_leftCandidates_le {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)}
    (hdegree : ∀ p : Point F, lineDegree T p ≤ H)
    (l : {l : Line F // l ∈ T})
    (z : {p : Point F // Incident p l.1}) :
    (leftCandidates l z).card ≤ H := by
  calc
    (leftCandidates l z).card ≤
        ((Finset.univ : Finset {m : Line F // m ∈ T}).filter
          fun m ↦ Incident z.1 m.1).card := Finset.card_image_le
    _ = lineDegree T z.1 := card_selected_through T z.1
    _ ≤ H := hdegree z.1

lemma leftBadPairs_subset_candidates {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)} (Z : Exceptions T) :
    leftBadPairs Z ⊆
      (Finset.univ : Finset {l : Line F // l ∈ T}).biUnion fun l ↦
        (Z l).attach.biUnion fun z ↦ leftCandidates l z.1 := by
  intro e he
  have hbad := (Finset.mem_filter.mp he).2
  apply Finset.mem_biUnion.mpr
  refine ⟨e.1, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨pairIntersectionLeft e, hbad⟩, Finset.mem_attach _ _, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨e.2, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact intersectionPoint_incident_right e.1.1 e.2.1

lemma card_leftBadPairs_le {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)} {C0 H : ℕ}
    (Z : ExactExceptions T C0)
    (hdegree : ∀ p : Point F, lineDegree T p ≤ H) :
    (leftBadPairs Z.1).card ≤ T.card * C0 * H := by
  classical
  calc
    (leftBadPairs Z.1).card ≤
        ((Finset.univ : Finset {l : Line F // l ∈ T}).biUnion fun l ↦
          (Z.1 l).attach.biUnion fun z ↦ leftCandidates l z.1).card :=
      Finset.card_le_card (leftBadPairs_subset_candidates Z.1)
    _ ≤ T.card * (C0 * H) := by
      have hout := Finset.card_biUnion_le_card_mul
        (s := (Finset.univ : Finset {l : Line F // l ∈ T}))
        (f := fun l ↦ (Z.1 l).attach.biUnion fun z ↦ leftCandidates l z.1)
        (n := C0 * H) (by
          intro l _
          have hin := Finset.card_biUnion_le_card_mul
            (s := (Z.1 l).attach)
            (f := fun z ↦ leftCandidates l z.1) (n := H)
            (fun z _ ↦ card_leftCandidates_le hdegree l z.1)
          simpa [Z.2 l] using hin)
      simpa using hout
    _ = T.card * C0 * H := by ring

/-- The symmetric candidate family for an exception on the second line. -/
noncomputable def rightCandidates {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)}
    (l : {l : Line F // l ∈ T})
    (z : {p : Point F // Incident p l.1}) :
    Finset ({l : Line F // l ∈ T} × {l : Line F // l ∈ T}) :=
  ((Finset.univ : Finset {m : Line F // m ∈ T}).filter
      fun m ↦ Incident z.1 m.1).image fun m ↦ (m, l)

lemma card_rightCandidates_le {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)}
    (hdegree : ∀ p : Point F, lineDegree T p ≤ H)
    (l : {l : Line F // l ∈ T})
    (z : {p : Point F // Incident p l.1}) :
    (rightCandidates l z).card ≤ H := by
  calc
    (rightCandidates l z).card ≤
        ((Finset.univ : Finset {m : Line F // m ∈ T}).filter
          fun m ↦ Incident z.1 m.1).card := Finset.card_image_le
    _ = lineDegree T z.1 := card_selected_through T z.1
    _ ≤ H := hdegree z.1

lemma rightBadPairs_subset_candidates {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)} (Z : Exceptions T) :
    rightBadPairs Z ⊆
      (Finset.univ : Finset {l : Line F // l ∈ T}).biUnion fun l ↦
        (Z l).attach.biUnion fun z ↦ rightCandidates l z.1 := by
  intro e he
  have hbad := (Finset.mem_filter.mp he).2
  apply Finset.mem_biUnion.mpr
  refine ⟨e.2, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨pairIntersectionRight e, hbad⟩, Finset.mem_attach _ _, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨e.1, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, intersectionPoint_incident_left e.1.1 e.2.1⟩

lemma card_rightBadPairs_le {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)} {C0 H : ℕ}
    (Z : ExactExceptions T C0)
    (hdegree : ∀ p : Point F, lineDegree T p ≤ H) :
    (rightBadPairs Z.1).card ≤ T.card * C0 * H := by
  classical
  calc
    (rightBadPairs Z.1).card ≤
        ((Finset.univ : Finset {l : Line F // l ∈ T}).biUnion fun l ↦
          (Z.1 l).attach.biUnion fun z ↦ rightCandidates l z.1).card :=
      Finset.card_le_card (rightBadPairs_subset_candidates Z.1)
    _ ≤ T.card * (C0 * H) := by
      have hout := Finset.card_biUnion_le_card_mul
        (s := (Finset.univ : Finset {l : Line F // l ∈ T}))
        (f := fun l ↦ (Z.1 l).attach.biUnion fun z ↦ rightCandidates l z.1)
        (n := C0 * H) (by
          intro l _
          have hin := Finset.card_biUnion_le_card_mul
            (s := (Z.1 l).attach)
            (f := fun z ↦ rightCandidates l z.1) (n := H)
            (fun z _ ↦ card_rightCandidates_le hdegree l z.1)
          simpa [Z.2 l] using hin)
      simpa using hout
    _ = T.card * C0 * H := by ring

/-- Ordered selected pairs whose intersection is nonexceptional on both
lines. -/
noncomputable def goodPairs {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)} (Z : Exceptions T) :
    Finset ({l : Line F // l ∈ T} × {l : Line F // l ∈ T}) :=
  (selectedPairs T).filter fun e ↦
    pairIntersectionLeft e ∉ Z e.1 ∧ pairIntersectionRight e ∉ Z e.2

lemma selectedPairs_subset_good_bad {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)} (Z : Exceptions T) :
    selectedPairs T ⊆ goodPairs Z ∪ (leftBadPairs Z ∪ rightBadPairs Z) := by
  intro e he
  by_cases hl : pairIntersectionLeft e ∈ Z e.1
  · simp [leftBadPairs, he, hl]
  by_cases hr : pairIntersectionRight e ∈ Z e.2
  · simp [rightBadPairs, he, hr]
  · simp [goodPairs, he, hl, hr]

lemma card_selectedPairs_le_good_bad {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)} (Z : Exceptions T) :
    (selectedPairs T).card ≤ (goodPairs Z).card +
      (leftBadPairs Z).card + (rightBadPairs Z).card := by
  calc
    (selectedPairs T).card ≤
        (goodPairs Z ∪ (leftBadPairs Z ∪ rightBadPairs Z)).card :=
      Finset.card_le_card (selectedPairs_subset_good_bad Z)
    _ ≤ (goodPairs Z).card +
        ((leftBadPairs Z).card + (rightBadPairs Z).card) :=
      Finset.card_union_le _ _ |>.trans
        (Nat.add_le_add_left (Finset.card_union_le _ _) _)
    _ = (goodPairs Z).card + (leftBadPairs Z).card +
        (rightBadPairs Z).card := by omega

/-- Good ordered pairs whose chosen intersection is `p`. -/
noncomputable def goodPairsAt {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)} (Z : Exceptions T)
    (p : Point F) :
    Finset ({l : Line F // l ∈ T} × {l : Line F // l ∈ T}) :=
  (goodPairs Z).filter fun e ↦ intersectionPoint e.1.1 e.2.1 = p

lemma goodPairs_subset_biUnion_at {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)} (Z : Exceptions T) :
    goodPairs Z ⊆
      (Finset.univ : Finset (Point F)).biUnion (goodPairsAt Z) := by
  intro e he
  apply Finset.mem_biUnion.mpr
  exact ⟨intersectionPoint e.1.1 e.2.1, Finset.mem_univ _,
    Finset.mem_filter.mpr ⟨he, rfl⟩⟩

lemma card_activeLines_le_degree {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] (T : Finset (Line F)) (Z : Exceptions T)
    (p : Point F) : (activeLines T Z p).card ≤ lineDegree T p := by
  classical
  let e : {l : Line F // Incident p l} ↪ Line F :=
    { toFun := Subtype.val
      inj' := Subtype.coe_injective }
  have hsub : (activeLines T Z p).map e ⊆
      T.filter fun l ↦ Incident p l := by
    intro l hl
    obtain ⟨l', hlactive, rfl⟩ := Finset.mem_map.mp hl
    obtain ⟨hlT, _⟩ := (mem_activeLines_iff T Z p l').mp hlactive
    exact Finset.mem_filter.mpr ⟨hlT, l'.2⟩
  calc
    (activeLines T Z p).card = ((activeLines T Z p).map e).card :=
      (Finset.card_map e).symm
    _ ≤ (T.filter fun l ↦ Incident p l).card := Finset.card_le_card hsub
    _ = lineDegree T p := rfl

lemma card_goodPairsAt_le {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)} (Z : Exceptions T)
    (p : Point F) :
    (goodPairsAt Z p).card ≤
      (activeLines T Z p).card * ((activeLines T Z p).card - 1) := by
  classical
  let A := ↥(activeLines T Z p)
  let P := {e : ({l : Line F // l ∈ T} × {l : Line F // l ∈ T}) //
    e ∈ goodPairsAt Z p}
  let f : P → A × A := fun e ↦ by
    let ee := e.1
    have heAt := (Finset.mem_filter.mp e.2)
    have heGood := (Finset.mem_filter.mp heAt.1)
    have heSel := heGood.1
    have hEq : intersectionPoint ee.1.1 ee.2.1 = p := heAt.2
    have hlInc : Incident p ee.1.1 := by
      have h0 := intersectionPoint_incident_left ee.1.1 ee.2.1
      exact hEq ▸ h0
    have hrInc : Incident p ee.2.1 := by
      have h0 := intersectionPoint_incident_right ee.1.1 ee.2.1
      exact hEq ▸ h0
    let l : {l : Line F // Incident p l} := ⟨ee.1.1, hlInc⟩
    let r : {l : Line F // Incident p l} := ⟨ee.2.1, hrInc⟩
    have hlAct : l ∈ activeLines T Z p := by
      apply (mem_activeLines_iff T Z p l).mpr
      refine ⟨ee.1.2, ?_⟩
      have hpoint : pairIntersectionLeft ee =
          (⟨p, hlInc⟩ : {q : Point F // Incident q ee.1.1}) := by
        apply Subtype.ext
        exact hEq
      rw [← hpoint]
      simpa [ee] using heGood.2.1
    have hrAct : r ∈ activeLines T Z p := by
      apply (mem_activeLines_iff T Z p r).mpr
      refine ⟨ee.2.2, ?_⟩
      have hpoint : pairIntersectionRight ee =
          (⟨p, hrInc⟩ : {q : Point F // Incident q ee.2.1}) := by
        apply Subtype.ext
        exact hEq
      rw [← hpoint]
      simpa [ee] using heGood.2.2
    exact (⟨l, hlAct⟩, ⟨r, hrAct⟩)
  have hfInj : Function.Injective f := by
    intro e e' h
    have h1 := congrArg (fun z : A × A ↦ z.1.1.1) h
    have h2 := congrArg (fun z : A × A ↦ z.2.1.1) h
    change e.1.1.1 = e'.1.1.1 at h1
    change e.1.2.1 = e'.1.2.1 at h2
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · exact h1
    · exact h2
  have hfNe : ∀ e : P, (f e).1 ≠ (f e).2 := by
    intro e h
    have heSel := (Finset.mem_filter.mp
      (Finset.mem_filter.mp e.2).1).1
    have hne := (Finset.mem_offDiag.mp heSel).2.2
    apply hne
    apply Subtype.ext
    exact congrArg (fun z : A ↦ z.1.1) h
  let emb : P ↪ {e : A × A // e.1 ≠ e.2} :=
    { toFun := fun e ↦ ⟨f e, hfNe e⟩
      inj' := fun _ _ h ↦ hfInj (congrArg Subtype.val h) }
  have hcard := Fintype.card_le_of_injective emb emb.injective
  change (goodPairsAt Z p).card ≤ _
  rw [← Fintype.card_coe]
  refine hcard.trans_eq ?_
  rw [Fintype.card_subtype]
  have hoff : (Finset.univ.filter fun e : A × A ↦ e.1 ≠ e.2) =
      (Finset.univ : Finset A).offDiag := by
    ext e
    simp
  rw [hoff, Finset.offDiag_card]
  have hA : Fintype.card A = (activeLines T Z p).card := by
    change Fintype.card ↥(activeLines T Z p) = _
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp
  simp only [Finset.card_univ, hA]
  rw [Nat.mul_sub_left_distrib, mul_one]

lemma card_goodPairs_le_energy_mul {F : Type*} [Fintype F] [Field F]
    [DecidableEq F] {T : Finset (Line F)} (Z : Exceptions T) {H : ℕ}
    (hdegree : ∀ p : Point F, lineDegree T p ≤ H) :
    (goodPairs Z).card ≤ H * energy T Z := by
  classical
  calc
    (goodPairs Z).card ≤
        ((Finset.univ : Finset (Point F)).biUnion (goodPairsAt Z)).card :=
      Finset.card_le_card (goodPairs_subset_biUnion_at Z)
    _ ≤ ∑ p : Point F, (goodPairsAt Z p).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ p : Point F,
        H * ((activeLines T Z p).card - 1) := by
      apply Finset.sum_le_sum
      intro p _
      calc
        (goodPairsAt Z p).card ≤ (activeLines T Z p).card *
            ((activeLines T Z p).card - 1) := card_goodPairsAt_le Z p
        _ ≤ H * ((activeLines T Z p).card - 1) := by
          gcongr
          exact (card_activeLines_le_degree T Z p).trans (hdegree p)
    _ = H * energy T Z := by
      rw [energy, Finset.mul_sum]

/-- If every pencil has at most `H` selected lines, the ordered-pair count
forces large compatibility energy after paying for the two exceptional
ends of a pair. -/
lemma selected_pairs_energy_inequality
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {T : Finset (Line F)} {C0 H : ℕ} (Z : ExactExceptions T C0)
    (hdegree : ∀ p : Point F, lineDegree T p ≤ H) :
    T.card * (T.card - 1) ≤
      H * energy T Z.1 + 2 * T.card * C0 * H := by
  rw [← card_selectedPairs T]
  calc
    (selectedPairs T).card ≤ (goodPairs Z.1).card +
        (leftBadPairs Z.1).card + (rightBadPairs Z.1).card :=
      card_selectedPairs_le_good_bad Z.1
    _ ≤ H * energy T Z.1 + (T.card * C0 * H) +
        (T.card * C0 * H) := by
      gcongr
      · exact card_goodPairs_le_energy_mul Z.1 hdegree
      · exact card_leftBadPairs_le Z hdegree
      · exact card_rightBadPairs_le Z hdegree
    _ = H * energy T Z.1 + 2 * T.card * C0 * H := by ring

lemma energy_ge_of_large_selected_set
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {T : Finset (Line F)} {C0 H E0 : ℕ} (Z : ExactExceptions T C0)
    (hH : 0 < H) (hdegree : ∀ p : Point F, lineDegree T p ≤ H)
    (hsize : H * (E0 + 2 * C0) ≤ T.card - 1) :
    E0 * T.card ≤ energy T Z.1 := by
  have hpairs := selected_pairs_energy_inequality Z hdegree
  have hlow :
      H * (E0 * T.card) + 2 * T.card * C0 * H ≤
        T.card * (T.card - 1) := by
    calc
      H * (E0 * T.card) + 2 * T.card * C0 * H =
          T.card * (H * (E0 + 2 * C0)) := by ring
      _ ≤ T.card * (T.card - 1) := Nat.mul_le_mul_left T.card hsize
  have hcancel : H * (E0 * T.card) ≤ H * energy T Z.1 := by
    apply Nat.le_of_add_le_add_right (b := 2 * T.card * C0 * H)
    exact hlow.trans hpairs
  exact le_of_mul_le_mul_left hcancel hH

/-! ### Counting configurations with no large pencil -/

noncomputable def lowEnergyBadFor
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {C0 : ℕ} (H : ℕ) (T : Finset (Line F)) (Z : ExactExceptions T C0) :
    Finset (Labeling F) :=
  Finset.univ.filter fun a ↦
    Compatible a T Z.1 ∧ ∀ p : Point F, lineDegree T p ≤ H

noncomputable def lowEnergyBadAt
    (F : Type*) [Fintype F] [Field F] [DecidableEq F]
    (C0 H s : ℕ) : Finset (Labeling F) :=
    (Finset.univ.powersetCard s).biUnion fun T ↦
    (Finset.univ : Finset (ExactExceptions T C0)).biUnion fun Z ↦
      lowEnergyBadFor H T Z

lemma card_lowEnergyBadFor_mul_pow
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {C0 H E0 s : ℕ} {T : Finset (Line F)} (hT : T.card = s)
    (Z : ExactExceptions T C0) (hH : 0 < H)
    (hsize : H * (E0 + 2 * C0) ≤ s - 1) :
    (lowEnergyBadFor H T Z).card * 2 ^ (E0 * s) ≤
      Fintype.card (Labeling F) := by
  classical
  by_cases hdegree : ∀ p : Point F, lineDegree T p ≤ H
  · have hbad : lowEnergyBadFor H T Z =
        Finset.univ.filter fun a ↦ Compatible a T Z.1 := by
      ext a
      simp [lowEnergyBadFor, hdegree]
    rw [hbad]
    have hcard :
        (Finset.univ.filter fun a : Labeling F ↦ Compatible a T Z.1).card =
          Fintype.card {a : Labeling F // Compatible a T Z.1} := by
      rw [Fintype.card_subtype]
    rw [hcard]
    have henergy : E0 * s ≤ energy T Z.1 := by
      rw [← hT]
      apply energy_ge_of_large_selected_set Z hH hdegree
      simpa [hT] using hsize
    calc
      Fintype.card {a : Labeling F // Compatible a T Z.1} *
          2 ^ (E0 * s) ≤
          Fintype.card {a : Labeling F // Compatible a T Z.1} *
            2 ^ energy T Z.1 := by
        exact Nat.mul_le_mul_left _ (pow_le_pow_right' (by norm_num) henergy)
      _ = Fintype.card (Labeling F) := card_compatible_mul_pow_energy T Z.1
  · have hbad : lowEnergyBadFor H T Z = ∅ := by
      ext a
      have hiff : (Compatible a T Z.1 ∧
          ∀ p : Point F, lineDegree T p ≤ H) ↔ False := by
        constructor
        · exact fun ha ↦ (hdegree ha.2).elim
        · exact False.elim
      simpa [lowEnergyBadFor] using hiff
    simp [hbad]

lemma card_lowEnergyBadAt_cross
    (F : Type*) [Fintype F] [Field F] [DecidableEq F]
    {C0 H E0 s : ℕ} (hH : 0 < H)
    (hsize : H * (E0 + 2 * C0) ≤ s - 1) :
    (lowEnergyBadAt F C0 H s).card * 2 ^ (E0 * s) ≤
      ((Fintype.card F ^ 2 + Fintype.card F + 1).choose s *
        (Fintype.card F + 1) ^ (C0 * s)) *
          Fintype.card (Labeling F) := by
  classical
  let L := (Finset.univ : Finset (Line F)).powersetCard s
  let P := 2 ^ (E0 * s)
  have houter : (lowEnergyBadAt F C0 H s).card ≤
      ∑ T ∈ L, ∑ Z : ExactExceptions T C0,
        (lowEnergyBadFor H T Z).card := by
    calc
      (lowEnergyBadAt F C0 H s).card ≤
          ∑ T ∈ L,
            ((Finset.univ : Finset (ExactExceptions T C0)).biUnion
              fun Z ↦ lowEnergyBadFor H T Z).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ T ∈ L, ∑ Z : ExactExceptions T C0,
            (lowEnergyBadFor H T Z).card := by
        apply Finset.sum_le_sum
        intro T _
        exact Finset.card_biUnion_le
  have hfixed : ∀ T ∈ L, ∀ Z : ExactExceptions T C0,
      (lowEnergyBadFor H T Z).card * P ≤ Fintype.card (Labeling F) := by
    intro T hT Z
    apply card_lowEnergyBadFor_mul_pow (Z := Z)
      (Finset.mem_powersetCard.mp hT).2 hH hsize
  change (lowEnergyBadAt F C0 H s).card * P ≤
    ((Fintype.card F ^ 2 + Fintype.card F + 1).choose s *
      (Fintype.card F + 1) ^ (C0 * s)) * Fintype.card (Labeling F)
  exact calc
    (lowEnergyBadAt F C0 H s).card * P ≤
        (∑ T ∈ L, ∑ Z : ExactExceptions T C0,
          (lowEnergyBadFor H T Z).card) * P := Nat.mul_le_mul_right P houter
    _ = ∑ T ∈ L, ∑ Z : ExactExceptions T C0,
          (lowEnergyBadFor H T Z).card * P := by
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ T ∈ L, ∑ _Z : ExactExceptions T C0,
          Fintype.card (Labeling F) := by
      apply Finset.sum_le_sum
      intro T hT
      apply Finset.sum_le_sum
      intro Z _
      exact hfixed T hT Z
    _ ≤ ∑ _T ∈ L, (Fintype.card F + 1) ^ (C0 * s) *
          Fintype.card (Labeling F) := by
      apply Finset.sum_le_sum
      intro T hT
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
      gcongr
      have hz := card_exactExceptions_le T C0
      simpa [(Finset.mem_powersetCard.mp hT).2] using hz
    _ ≤ ((Fintype.card F ^ 2 + Fintype.card F + 1).choose s *
        (Fintype.card F + 1) ^ (C0 * s)) *
          Fintype.card (Labeling F) := by
      have hLcard : L.card =
          (Fintype.card F ^ 2 + Fintype.card F + 1).choose s := by
        simp only [L, Finset.card_powersetCard, Finset.card_univ,
          Projective.card_line]
      rw [Finset.sum_const, Nat.nsmul_eq_mul, hLcard]
      exact le_of_eq (by ring)

/-! ### Separated pencil grids -/

/-- A rectangular cell consists of one line from each of two finite line
families. -/
abbrev GridCell {F : Type*} [DecidableEq F]
    (A B : Finset (Line F)) :=
  {l : Line F // l ∈ A} × {m : Line F // m ∈ B}

/-- `A` consists of lines avoiding `x`, `B` of lines through `x`, and no
line in `B` passes through the intersection of two distinct lines of `A`.
This last clause is exactly what makes the rectangular intersections
pairwise distinct. -/
def IsSeparatedGrid {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (A B : Finset (Line F)) : Prop :=
  (∀ l ∈ A, ¬ Incident x l) ∧
  (∀ m ∈ B, Incident x m) ∧
  ∀ l ∈ A, ∀ l' ∈ A, l ≠ l' →
    lineThroughPoints x (intersectionPoint l l') ∉ B

noncomputable def gridCellPoint
    {F : Type*} [Field F] [DecidableEq F]
    {A B : Finset (Line F)} (c : GridCell A B) : Point F :=
  intersectionPoint c.1.1 c.2.1

lemma separatedGrid_left_ne_right
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {x : Point F} {A B : Finset (Line F)}
    (hgrid : IsSeparatedGrid x A B) (c : GridCell A B) :
    c.1.1 ≠ c.2.1 := by
  intro h
  have hxA := hgrid.1 c.1.1 c.1.2
  apply hxA
  rw [h]
  exact hgrid.2.1 c.2.1 c.2.2

lemma gridCellPoint_injective
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {x : Point F} {A B : Finset (Line F)}
    (hgrid : IsSeparatedGrid x A B) :
    Function.Injective (gridCellPoint : GridCell A B → Point F) := by
  intro c d hpoint
  have hxc : x ≠ gridCellPoint c := by
    intro h
    exact hgrid.1 c.1.1 c.1.2 (by
      rw [h]
      exact intersectionPoint_incident_left c.1.1 c.2.1)
  have hm : c.2.1 = d.2.1 := by
    apply line_unique_of_two_points hxc
    · exact hgrid.2.1 c.2.1 c.2.2
    · exact intersectionPoint_incident_right c.1.1 c.2.1
    · exact hgrid.2.1 d.2.1 d.2.2
    · rw [hpoint]
      exact intersectionPoint_incident_right d.1.1 d.2.1
  have hl : c.1.1 = d.1.1 := by
    by_contra hne
    have hpOnD : Incident (gridCellPoint c) d.1.1 := by
      rw [hpoint]
      exact intersectionPoint_incident_left d.1.1 d.2.1
    have hinter : intersectionPoint c.1.1 d.1.1 = gridCellPoint c := by
      exact intersectionPoint_eq_of_ne hne
        (intersectionPoint_incident_left c.1.1 c.2.1) hpOnD
    have hjoin :
        lineThroughPoints x (intersectionPoint c.1.1 d.1.1) = c.2.1 := by
      apply lineThroughPoints_eq_of_ne
      · rw [hinter]
        exact hxc
      · exact hgrid.2.1 c.2.1 c.2.2
      · rw [hinter]
        exact intersectionPoint_incident_right c.1.1 c.2.1
    have hnot := hgrid.2.2 c.1.1 c.1.2 d.1.1 d.1.2 hne
    exact hnot (by simpa [hjoin] using c.2.2)
  apply Prod.ext
  · exact Subtype.ext hl
  · exact Subtype.ext hm

/-- Grid cells whose incidence on the `A`-line is exceptional.  The
existential proof only records membership in the ambient selected set; proof
irrelevance makes its particular value immaterial. -/
noncomputable def gridLeftBad
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {T : Finset (Line F)} (Z : Exceptions T)
    (A B : Finset (Line F)) : Finset (GridCell A B) :=
  Finset.univ.filter fun c ↦
    ∃ h : c.1.1 ∈ T,
      (⟨gridCellPoint c, intersectionPoint_incident_left c.1.1 c.2.1⟩ :
        {p : Point F // Incident p c.1.1}) ∈ Z ⟨c.1.1, h⟩

/-- Grid cells whose incidence on the `B`-line is exceptional. -/
noncomputable def gridRightBad
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {T : Finset (Line F)} (Z : Exceptions T)
    (A B : Finset (Line F)) : Finset (GridCell A B) :=
  Finset.univ.filter fun c ↦
    ∃ h : c.2.1 ∈ T,
      (⟨gridCellPoint c, intersectionPoint_incident_right c.1.1 c.2.1⟩ :
        {p : Point F // Incident p c.2.1}) ∈ Z ⟨c.2.1, h⟩

/-- Cells nonexceptional at both ends. -/
noncomputable def gridGood
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {T : Finset (Line F)} (Z : Exceptions T)
    (A B : Finset (Line F)) : Finset (GridCell A B) :=
  Finset.univ.filter fun c ↦
    c ∉ gridLeftBad Z A B ∧ c ∉ gridRightBad Z A B

lemma card_gridLeftBad_le
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {x : Point F} {T A B : Finset (Line F)} {C0 : ℕ}
    (Z : ExactExceptions T C0) (hgrid : IsSeparatedGrid x A B)
    (hAT : A ⊆ T) :
    (gridLeftBad Z.1 A B).card ≤ A.card * C0 := by
  classical
  let S := ↥(gridLeftBad Z.1 A B)
  let R := Σ l : {l : Line F // l ∈ A},
    {p : {p : Point F // Incident p l.1} //
      p ∈ Z.1 ⟨l.1, hAT l.2⟩}
  let f : S → R := fun c ↦ by
    have hcBad := (Finset.mem_filter.mp c.2).2
    let hcT := Classical.choose hcBad
    have hcZ := Classical.choose_spec hcBad
    refine ⟨c.1.1, ?_⟩
    refine ⟨⟨gridCellPoint c.1,
      intersectionPoint_incident_left c.1.1.1 c.1.2.1⟩, ?_⟩
    simpa only using hcZ
  have hf : Function.Injective f := by
    intro c d h
    apply Subtype.ext
    apply gridCellPoint_injective hgrid
    have hp := congrArg (fun z : R ↦ z.2.1.1) h
    dsimp only [f] at hp
    change gridCellPoint c.1 = gridCellPoint d.1 at hp
    exact hp
  have hcard := Fintype.card_le_of_injective f hf
  change (gridLeftBad Z.1 A B).card ≤ _
  rw [← Fintype.card_coe]
  refine hcard.trans_eq ?_
  dsimp [R]
  rw [Fintype.card_sigma]
  calc
    ∑ l : {l : Line F // l ∈ A},
        Fintype.card {p : {p : Point F // Incident p l.1} //
          p ∈ Z.1 ⟨l.1, hAT l.2⟩} =
        ∑ _l : {l : Line F // l ∈ A}, C0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Fintype.card_subtype]
      simpa using Z.2 ⟨l.1, hAT l.2⟩
    _ = A.card * C0 := by simp

lemma card_gridRightBad_le
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {x : Point F} {T A B : Finset (Line F)} {C0 : ℕ}
    (Z : ExactExceptions T C0) (hgrid : IsSeparatedGrid x A B)
    (hBT : B ⊆ T) :
    (gridRightBad Z.1 A B).card ≤ B.card * C0 := by
  classical
  let S := ↥(gridRightBad Z.1 A B)
  let R := Σ m : {m : Line F // m ∈ B},
    {p : {p : Point F // Incident p m.1} //
      p ∈ Z.1 ⟨m.1, hBT m.2⟩}
  let f : S → R := fun c ↦ by
    have hcBad := (Finset.mem_filter.mp c.2).2
    let hcT := Classical.choose hcBad
    have hcZ := Classical.choose_spec hcBad
    refine ⟨c.1.2, ?_⟩
    refine ⟨⟨gridCellPoint c.1,
      intersectionPoint_incident_right c.1.1.1 c.1.2.1⟩, ?_⟩
    simpa only using hcZ
  have hf : Function.Injective f := by
    intro c d h
    apply Subtype.ext
    apply gridCellPoint_injective hgrid
    have hp := congrArg (fun z : R ↦ z.2.1.1) h
    dsimp only [f] at hp
    change gridCellPoint c.1 = gridCellPoint d.1 at hp
    exact hp
  have hcard := Fintype.card_le_of_injective f hf
  change (gridRightBad Z.1 A B).card ≤ _
  rw [← Fintype.card_coe]
  refine hcard.trans_eq ?_
  dsimp [R]
  rw [Fintype.card_sigma]
  calc
    ∑ m : {m : Line F // m ∈ B},
        Fintype.card {p : {p : Point F // Incident p m.1} //
          p ∈ Z.1 ⟨m.1, hBT m.2⟩} =
        ∑ _m : {m : Line F // m ∈ B}, C0 := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Fintype.card_subtype]
      simpa using Z.2 ⟨m.1, hBT m.2⟩
    _ = B.card * C0 := by simp

lemma card_gridCells_le_good_bad
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {T A B : Finset (Line F)} (Z : Exceptions T) :
    A.card * B.card ≤
      (gridGood Z A B).card + (gridLeftBad Z A B).card +
        (gridRightBad Z A B).card := by
  classical
  have hcover : (Finset.univ : Finset (GridCell A B)) ⊆
      gridGood Z A B ∪ (gridLeftBad Z A B ∪ gridRightBad Z A B) := by
    intro c _
    by_cases hl : c ∈ gridLeftBad Z A B
    · simp [hl]
    by_cases hr : c ∈ gridRightBad Z A B
    · simp [hr]
    · simp [gridGood, hl, hr]
  calc
    A.card * B.card = Fintype.card (GridCell A B) := by simp
    _ = (Finset.univ : Finset (GridCell A B)).card := by simp
    _ ≤ (gridGood Z A B ∪
        (gridLeftBad Z A B ∪ gridRightBad Z A B)).card :=
      Finset.card_le_card hcover
    _ ≤ (gridGood Z A B).card +
        ((gridLeftBad Z A B).card + (gridRightBad Z A B).card) :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (Finset.card_union_le _ _) _)
    _ = (gridGood Z A B).card + (gridLeftBad Z A B).card +
        (gridRightBad Z A B).card := by omega

lemma card_gridGood_le_energy
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {x : Point F} {T A B : Finset (Line F)} {C0 : ℕ}
    (Z : ExactExceptions T C0) (hgrid : IsSeparatedGrid x A B)
    (hAT : A ⊆ T) (hBT : B ⊆ T) :
    (gridGood Z.1 A B).card ≤ energy T Z.1 := by
  classical
  let G := gridGood Z.1 A B
  let P := G.image gridCellPoint
  have hpointInj : Set.InjOn gridCellPoint G :=
    (gridCellPoint_injective hgrid).injOn
  have hPcard : P.card = G.card := by
    exact Finset.card_image_of_injOn hpointInj
  have hone : ∀ p ∈ P, 1 ≤ (activeLines T Z.1 p).card - 1 := by
    intro p hp
    obtain ⟨c, hcG, rfl⟩ := Finset.mem_image.mp hp
    have hcGood := (Finset.mem_filter.mp hcG).2
    have hleftNot :
        (⟨gridCellPoint c,
          intersectionPoint_incident_left c.1.1 c.2.1⟩ :
            {p : Point F // Incident p c.1.1}) ∉
          Z.1 ⟨c.1.1, hAT c.1.2⟩ := by
      intro hz
      apply hcGood.1
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, ⟨hAT c.1.2, hz⟩⟩
    have hrightNot :
        (⟨gridCellPoint c,
          intersectionPoint_incident_right c.1.1 c.2.1⟩ :
            {p : Point F // Incident p c.2.1}) ∉
          Z.1 ⟨c.2.1, hBT c.2.2⟩ := by
      intro hz
      apply hcGood.2
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, ⟨hBT c.2.2, hz⟩⟩
    let l : {l : Line F // Incident (gridCellPoint c) l} :=
      ⟨c.1.1, intersectionPoint_incident_left c.1.1 c.2.1⟩
    let m : {l : Line F // Incident (gridCellPoint c) l} :=
      ⟨c.2.1, intersectionPoint_incident_right c.1.1 c.2.1⟩
    have hl : l ∈ activeLines T Z.1 (gridCellPoint c) := by
      apply (mem_activeLines_iff T Z.1 (gridCellPoint c) l).mpr
      exact ⟨hAT c.1.2, hleftNot⟩
    have hm : m ∈ activeLines T Z.1 (gridCellPoint c) := by
      apply (mem_activeLines_iff T Z.1 (gridCellPoint c) m).mpr
      exact ⟨hBT c.2.2, hrightNot⟩
    have hlm : l ≠ m := by
      intro h
      exact separatedGrid_left_ne_right hgrid c
        (congrArg Subtype.val h)
    have hpair : ({l, m} : Finset
        {l : Line F // Incident (gridCellPoint c) l}).card = 2 := by
      simp [hlm]
    have hsub : ({l, m} : Finset
        {l : Line F // Incident (gridCellPoint c) l}) ⊆
          activeLines T Z.1 (gridCellPoint c) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hl
      · exact hm
    have htwo : 2 ≤ (activeLines T Z.1 (gridCellPoint c)).card := by
      rw [← hpair]
      exact Finset.card_le_card hsub
    omega
  calc
    (gridGood Z.1 A B).card = G.card := rfl
    _ = P.card := hPcard.symm
    _ = ∑ p ∈ P, 1 := by simp
    _ ≤ ∑ p ∈ P, ((activeLines T Z.1 p).card - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hone p hp
    _ ≤ ∑ p : Point F, ((activeLines T Z.1 p).card - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P)
      intro p _ _
      exact Nat.zero_le _
    _ = energy T Z.1 := rfl

/-- A separated `A × B` grid contributes one unit of compatibility energy
per surviving cell; an exceptional incidence destroys at most one cell in
its row or column. -/
lemma grid_energy_inequality
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {x : Point F} {T A B : Finset (Line F)} {C0 : ℕ}
    (Z : ExactExceptions T C0) (hgrid : IsSeparatedGrid x A B)
    (hAT : A ⊆ T) (hBT : B ⊆ T) :
    A.card * B.card ≤
      energy T Z.1 + A.card * C0 + B.card * C0 := by
  calc
    A.card * B.card ≤ (gridGood Z.1 A B).card +
        (gridLeftBad Z.1 A B).card + (gridRightBad Z.1 A B).card :=
      card_gridCells_le_good_bad Z.1
    _ ≤ energy T Z.1 + A.card * C0 + B.card * C0 := by
      gcongr
      · exact card_gridGood_le_energy Z hgrid hAT hBT
      · exact card_gridLeftBad_le Z hgrid hAT
      · exact card_gridRightBad_le Z hgrid hBT

lemma agree_comm_of_ne
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (a : Labeling F) {l m : Line F} (hlm : l ≠ m) :
    Agree a l m ↔ Agree a m l := by
  have hp := intersectionPoint_comm_of_ne hlm
  have hmEq :
      (⟨intersectionPoint m l, intersectionPoint_incident_left m l⟩ :
        {p : Point F // Incident p m}) =
      ⟨intersectionPoint l m, intersectionPoint_incident_right l m⟩ :=
    Subtype.ext hp.symm
  have hlEq :
      (⟨intersectionPoint m l, intersectionPoint_incident_right m l⟩ :
        {p : Point F // Incident p l}) =
      ⟨intersectionPoint l m, intersectionPoint_incident_left l m⟩ :=
    Subtype.ext hp.symm
  unfold Agree
  rw [hmEq, hlEq]
  exact eq_comm

lemma agree_of_mem_gridGood
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {x : Point F} {T A B : Finset (Line F)}
    {a : Labeling F} {Z : Exceptions T}
    (hcomp : Compatible a T Z) (hgrid : IsSeparatedGrid x A B)
    (hAT : A ⊆ T) (hBT : B ⊆ T)
    {c : GridCell A B} (hc : c ∈ gridGood Z A B) :
    Agree a c.1.1 c.2.1 := by
  have hcGood := (Finset.mem_filter.mp hc).2
  have hleftNot :
      (⟨gridCellPoint c,
        intersectionPoint_incident_left c.1.1 c.2.1⟩ :
          {p : Point F // Incident p c.1.1}) ∉
        Z ⟨c.1.1, hAT c.1.2⟩ := by
    intro hz
    apply hcGood.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ⟨hAT c.1.2, hz⟩⟩
  have hrightNot :
      (⟨gridCellPoint c,
        intersectionPoint_incident_right c.1.1 c.2.1⟩ :
          {p : Point F // Incident p c.2.1}) ∉
        Z ⟨c.2.1, hBT c.2.2⟩ := by
    intro hz
    apply hcGood.2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ⟨hBT c.2.2, hz⟩⟩
  let l : {l : Line F // Incident (gridCellPoint c) l} :=
    ⟨c.1.1, intersectionPoint_incident_left c.1.1 c.2.1⟩
  let m : {l : Line F // Incident (gridCellPoint c) l} :=
    ⟨c.2.1, intersectionPoint_incident_right c.1.1 c.2.1⟩
  have hl : l ∈ activeLines T Z (gridCellPoint c) := by
    apply (mem_activeLines_iff T Z (gridCellPoint c) l).mpr
    exact ⟨hAT c.1.2, hleftNot⟩
  have hm : m ∈ activeLines T Z (gridCellPoint c) := by
    apply (mem_activeLines_iff T Z (gridCellPoint c) m).mpr
    exact ⟨hBT c.2.2, hrightNot⟩
  exact hcomp (gridCellPoint c) l hl m hm

/-- Under balance, the number of surviving cells in a separated grid is at
most `balance` per off-pencil row. -/
lemma card_gridGood_le_balance
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {x : Point F} {T A B : Finset (Line F)} {balance : ℕ}
    {a : Labeling F} {Z : Exceptions T}
    (hcomp : Compatible a T Z) (hbal : IsBalanced balance a)
    (hgrid : IsSeparatedGrid x A B) (hAT : A ⊆ T) (hBT : B ⊆ T) :
    (gridGood Z A B).card ≤ A.card * balance := by
  classical
  let R := Σ l : {l : Line F // l ∈ A},
    {m : {m : Line F // m ∈ B} // Agree a m.1 l.1}
  let f : ↥(gridGood Z A B) → R := fun c ↦ by
    refine ⟨c.1.1, ⟨c.1.2, ?_⟩⟩
    have hagree := agree_of_mem_gridGood hcomp hgrid hAT hBT c.2
    exact (agree_comm_of_ne a (separatedGrid_left_ne_right hgrid c.1)).mp hagree
  have hf : Function.Injective f := by
    intro c d h
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun z : R ↦ z.1.1) h)
    · exact Subtype.ext (congrArg (fun z : R ↦ z.2.1.1) h)
  have hR : Fintype.card R ≤ A.card * balance := by
    rw [Fintype.card_sigma]
    calc
      ∑ l : {l : Line F // l ∈ A},
          Fintype.card {m : {m : Line F // m ∈ B} // Agree a m.1 l.1} ≤
          ∑ _l : {l : Line F // l ∈ A}, balance := by
        apply Finset.sum_le_sum
        intro l _
        have hlx : ¬ Incident x l.1 := hgrid.1 l.1 l.2
        have hsub : B ⊆ linesThrough x := by
          intro m hm
          exact (mem_linesThrough_iff x m).mpr (hgrid.2.1 m hm)
        calc
          Fintype.card {m : {m : Line F // m ∈ B} // Agree a m.1 l.1} =
              (B.filter fun m ↦ Agree a m l.1).card := by
            rw [Fintype.card_subtype, Finset.univ_eq_attach,
              Finset.filter_attach (fun m : Line F ↦ Agree a m l.1) B,
              Finset.card_map, Finset.card_attach]
          _ ≤ ((linesThrough x).filter fun m ↦ Agree a m l.1).card := by
            apply Finset.card_le_card
            intro m hm
            have hm' := Finset.mem_filter.mp hm
            exact Finset.mem_filter.mpr ⟨hsub hm'.1, hm'.2⟩
          _ ≤ balance := (hbal x l.1 hlx).1
      _ = A.card * balance := by simp
  calc
    (gridGood Z A B).card = Fintype.card ↥(gridGood Z A B) := by simp
    _ ≤ Fintype.card R := Fintype.card_le_of_injective f hf
    _ ≤ A.card * balance := hR

/-- Pencil lines which would create a collision between two distinct
`A`-rows. -/
noncomputable def badPencilLines
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (A : Finset (Line F)) : Finset (Line F) :=
  A.offDiag.image fun e ↦
    lineThroughPoints x (intersectionPoint e.1 e.2)

lemma card_badPencilLines_le
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (A : Finset (Line F)) :
    (badPencilLines x A).card ≤ A.card * (A.card - 1) := by
  calc
    (badPencilLines x A).card ≤ A.offDiag.card := Finset.card_image_le
    _ = A.card * (A.card - 1) := by
      rw [Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]

lemma separatedGrid_of_subsets
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {x : Point F} {A P B : Finset (Line F)}
    (hAoff : ∀ l ∈ A, ¬ Incident x l)
    (hPpencil : ∀ m ∈ P, Incident x m)
    (hB : B ⊆ P \ badPencilLines x A) :
    IsSeparatedGrid x A B := by
  refine ⟨hAoff, ?_, ?_⟩
  · intro m hm
    exact hPpencil m (Finset.mem_sdiff.mp (hB hm)).1
  · intro l hl l' hl' hne hmem
    have hbad : lineThroughPoints x (intersectionPoint l l') ∈
        badPencilLines x A := by
      apply Finset.mem_image.mpr
      refine ⟨(l, l'), ?_, rfl⟩
      exact Finset.mem_offDiag.mpr ⟨hl, hl', hne⟩
    exact (Finset.mem_sdiff.mp (hB hmem)).2 hbad

/-- Extract a separated subpencil after discarding at most one line for each
ordered pair of off-pencil rows. -/
lemma exists_separated_subpencil
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {x : Point F} {A P : Finset (Line F)} {M : ℕ}
    (hAoff : ∀ l ∈ A, ¬ Incident x l)
    (hPpencil : ∀ m ∈ P, Incident x m)
    (hlarge : M + A.card * (A.card - 1) ≤ P.card) :
    ∃ B : Finset (Line F), B.card = M ∧ B ⊆ P ∧
      IsSeparatedGrid x A B := by
  classical
  let D := P \ badPencilLines x A
  have hinter : (P ∩ badPencilLines x A).card ≤
      (badPencilLines x A).card :=
    Finset.card_le_card Finset.inter_subset_right
  have hdecomp := Finset.card_sdiff_add_card_inter P (badPencilLines x A)
  have hD : M ≤ D.card := by
    dsimp [D]
    have hbad := card_badPencilLines_le x A
    omega
  obtain ⟨B, hBD, hBcard⟩ := Finset.exists_subset_card_eq hD
  refine ⟨B, hBcard, ?_, separatedGrid_of_subsets hAoff hPpencil hBD⟩
  exact hBD.trans Finset.sdiff_subset

/-- Restrict exact exception data from a selected line family to a
subfamily. -/
noncomputable def restrictExactExceptions
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {T U : Finset (Line F)} {C0 : ℕ}
    (Z : ExactExceptions T C0) (hUT : U ⊆ T) :
    ExactExceptions U C0 :=
  ⟨fun l ↦ Z.1 ⟨l.1, hUT l.2⟩,
    fun l ↦ Z.2 ⟨l.1, hUT l.2⟩⟩

lemma compatible_restrict
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {T U : Finset (Line F)} {C0 : ℕ}
    {a : Labeling F} {Z : ExactExceptions T C0}
    (hcomp : Compatible a T Z.1) (hUT : U ⊆ T) :
    Compatible a U (restrictExactExceptions Z hUT).1 := by
  intro p l hl m hm
  apply hcomp p
  · apply (mem_activeLines_iff T Z.1 p l).mpr
    obtain ⟨hlU, hlZ⟩ :=
      (mem_activeLines_iff U (restrictExactExceptions Z hUT).1 p l).mp hl
    exact ⟨hUT hlU, hlZ⟩
  · apply (mem_activeLines_iff T Z.1 p m).mpr
    obtain ⟨hmU, hmZ⟩ :=
      (mem_activeLines_iff U (restrictExactExceptions Z hUT).1 p m).mp hm
    exact ⟨hUT hmU, hmZ⟩

/-! ### Counting large separated grids -/

noncomputable def gridBadFor
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {C0 : ℕ} (x : Point F) (A B : Finset (Line F))
    (Z : ExactExceptions (A ∪ B) C0) : Finset (Labeling F) :=
  Finset.univ.filter fun a ↦
    IsSeparatedGrid x A B ∧ Compatible a (A ∪ B) Z.1

noncomputable def gridBad
    (F : Type*) [Fintype F] [Field F] [DecidableEq F]
    (C0 M : ℕ) : Finset (Labeling F) :=
  (Finset.univ : Finset (Point F)).biUnion fun x ↦
    (Finset.univ.powersetCard M).biUnion fun A ↦
      (Finset.univ.powersetCard M).biUnion fun B ↦
        (Finset.univ : Finset (ExactExceptions (A ∪ B) C0)).biUnion
          fun Z ↦ gridBadFor x A B Z

lemma card_gridBadFor_mul_pow
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {C0 M E0 : ℕ} (x : Point F)
    {A B : Finset (Line F)} (hA : A.card = M) (hB : B.card = M)
    (Z : ExactExceptions (A ∪ B) C0)
    (hE : E0 + 2 * M * C0 ≤ M * M) :
    (gridBadFor x A B Z).card * 2 ^ E0 ≤
      Fintype.card (Labeling F) := by
  classical
  by_cases hgrid : IsSeparatedGrid x A B
  · have hbad : gridBadFor x A B Z =
        Finset.univ.filter fun a ↦ Compatible a (A ∪ B) Z.1 := by
      ext a
      simp [gridBadFor, hgrid]
    rw [hbad]
    have hcard :
        (Finset.univ.filter fun a : Labeling F ↦
          Compatible a (A ∪ B) Z.1).card =
          Fintype.card {a : Labeling F // Compatible a (A ∪ B) Z.1} := by
      rw [Fintype.card_subtype]
    rw [hcard]
    have henergy0 := grid_energy_inequality Z hgrid
      Finset.subset_union_left Finset.subset_union_right
    have hE' : E0 + M * C0 + M * C0 ≤ M * M := by
      calc
        E0 + M * C0 + M * C0 = E0 + 2 * M * C0 := by ring
        _ ≤ M * M := hE
    have henergy : E0 ≤ energy (A ∪ B) Z.1 := by
      rw [hA, hB] at henergy0
      omega
    calc
      Fintype.card {a : Labeling F // Compatible a (A ∪ B) Z.1} *
          2 ^ E0 ≤
          Fintype.card {a : Labeling F // Compatible a (A ∪ B) Z.1} *
            2 ^ energy (A ∪ B) Z.1 := by
        exact Nat.mul_le_mul_left _ (pow_le_pow_right' (by norm_num) henergy)
      _ = Fintype.card (Labeling F) :=
        card_compatible_mul_pow_energy (A ∪ B) Z.1
  · have hbad : gridBadFor x A B Z = ∅ := by
      ext a
      simp [gridBadFor, hgrid]
    simp [hbad]

lemma card_gridBad_cross
    (F : Type*) [Fintype F] [Field F] [DecidableEq F]
    {C0 M E0 : ℕ} (hE : E0 + 2 * M * C0 ≤ M * M) :
    (gridBad F C0 M).card * 2 ^ E0 ≤
      ((Fintype.card F ^ 2 + Fintype.card F + 1) *
        ((Fintype.card F ^ 2 + Fintype.card F + 1).choose M) ^ 2 *
        (Fintype.card F + 1) ^ (2 * C0 * M)) *
          Fintype.card (Labeling F) := by
  classical
  let S := (Finset.univ : Finset (Line F)).powersetCard M
  let Q := 2 ^ E0
  have houter : (gridBad F C0 M).card ≤
      ∑ x : Point F, ∑ A ∈ S, ∑ B ∈ S,
        ∑ Z : ExactExceptions (A ∪ B) C0,
          (gridBadFor x A B Z).card := by
    calc
      (gridBad F C0 M).card ≤
          ∑ x : Point F,
            ((Finset.univ.powersetCard M).biUnion fun A ↦
              (Finset.univ.powersetCard M).biUnion fun B ↦
                (Finset.univ : Finset (ExactExceptions (A ∪ B) C0)).biUnion
                  fun Z ↦ gridBadFor x A B Z).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ x : Point F, ∑ A ∈ S,
            ((Finset.univ.powersetCard M).biUnion fun B ↦
              (Finset.univ : Finset (ExactExceptions (A ∪ B) C0)).biUnion
                fun Z ↦ gridBadFor x A B Z).card := by
        apply Finset.sum_le_sum
        intro x _
        exact Finset.card_biUnion_le
      _ ≤ ∑ x : Point F, ∑ A ∈ S, ∑ B ∈ S,
            ((Finset.univ : Finset (ExactExceptions (A ∪ B) C0)).biUnion
              fun Z ↦ gridBadFor x A B Z).card := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro A _
        exact Finset.card_biUnion_le
      _ ≤ ∑ x : Point F, ∑ A ∈ S, ∑ B ∈ S,
          ∑ Z : ExactExceptions (A ∪ B) C0,
            (gridBadFor x A B Z).card := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro A _
        apply Finset.sum_le_sum
        intro B _
        exact Finset.card_biUnion_le
  have hfixed : ∀ x : Point F, ∀ A ∈ S, ∀ B ∈ S,
      ∀ Z : ExactExceptions (A ∪ B) C0,
        (gridBadFor x A B Z).card * Q ≤ Fintype.card (Labeling F) := by
    intro x A hA B hB Z
    apply card_gridBadFor_mul_pow x
      (Finset.mem_powersetCard.mp hA).2
      (Finset.mem_powersetCard.mp hB).2 Z hE
  change (gridBad F C0 M).card * Q ≤ _
  exact calc
    (gridBad F C0 M).card * Q ≤
        (∑ x : Point F, ∑ A ∈ S, ∑ B ∈ S,
          ∑ Z : ExactExceptions (A ∪ B) C0,
            (gridBadFor x A B Z).card) * Q :=
      Nat.mul_le_mul_right Q houter
    _ = ∑ x : Point F, ∑ A ∈ S, ∑ B ∈ S,
          ∑ Z : ExactExceptions (A ∪ B) C0,
            (gridBadFor x A B Z).card * Q := by
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ x : Point F, ∑ A ∈ S, ∑ B ∈ S,
          ∑ _Z : ExactExceptions (A ∪ B) C0,
            Fintype.card (Labeling F) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro A hA
      apply Finset.sum_le_sum
      intro B hB
      apply Finset.sum_le_sum
      intro Z _
      exact hfixed x A hA B hB Z
    _ ≤ ∑ _x : Point F, ∑ _A ∈ S, ∑ _B ∈ S,
          (Fintype.card F + 1) ^ (2 * C0 * M) *
            Fintype.card (Labeling F) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro A hA
      apply Finset.sum_le_sum
      intro B hB
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
      gcongr
      have hz := card_exactExceptions_le (A ∪ B) C0
      calc
        Fintype.card (ExactExceptions (A ∪ B) C0) ≤
            (Fintype.card F + 1) ^ (C0 * (A ∪ B).card) := hz
        _ ≤ (Fintype.card F + 1) ^ (2 * C0 * M) := by
          apply pow_le_pow_right' (by omega)
          have hAB := Finset.card_union_le A B
          have hAc := (Finset.mem_powersetCard.mp hA).2
          have hBc := (Finset.mem_powersetCard.mp hB).2
          calc
            C0 * (A ∪ B).card ≤ C0 * (A.card + B.card) :=
              Nat.mul_le_mul_left C0 hAB
            _ = 2 * C0 * M := by rw [hAc, hBc]; ring
    _ ≤ ((Fintype.card F ^ 2 + Fintype.card F + 1) *
        ((Fintype.card F ^ 2 + Fintype.card F + 1).choose M) ^ 2 *
        (Fintype.card F + 1) ^ (2 * C0 * M)) *
          Fintype.card (Labeling F) := by
      have hScard : S.card =
          (Fintype.card F ^ 2 + Fintype.card F + 1).choose M := by
        simp only [S, Finset.card_powersetCard, Finset.card_univ,
          Projective.card_line]
      simp only [Finset.sum_const, Nat.nsmul_eq_mul, hScard,
        Finset.card_univ, Projective.card_point]
      exact le_of_eq (by ring)

lemma mem_gridBad_of_large_pencil
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {C0 M : ℕ} {a : Labeling F} {T : Finset (Line F)}
    (Z : ExactExceptions T C0) (hcomp : Compatible a T Z.1)
    (x : Point F)
    (hoff : M ≤ (T.filter fun l ↦ ¬ Incident x l).card)
    (hpencil : M + M * (M - 1) ≤ lineDegree T x) :
    a ∈ gridBad F C0 M := by
  classical
  let O := T.filter fun l ↦ ¬ Incident x l
  let P := T.filter fun l ↦ Incident x l
  obtain ⟨A, hAO, hAcard⟩ := Finset.exists_subset_card_eq hoff
  have hAoff : ∀ l ∈ A, ¬ Incident x l := by
    intro l hl
    exact (Finset.mem_filter.mp (hAO hl)).2
  have hPpencil : ∀ m ∈ P, Incident x m := by
    intro m hm
    exact (Finset.mem_filter.mp hm).2
  have hPcard : P.card = lineDegree T x := rfl
  have hlarge : M + A.card * (A.card - 1) ≤ P.card := by
    rw [hAcard, hPcard]
    exact hpencil
  obtain ⟨B, hBcard, hBP, hgrid⟩ :=
    exists_separated_subpencil hAoff hPpencil hlarge
  have hAT : A ⊆ T := by
    exact hAO.trans (Finset.filter_subset _ _)
  have hBT : B ⊆ T := by
    exact hBP.trans (Finset.filter_subset _ _)
  have hUT : A ∪ B ⊆ T := Finset.union_subset hAT hBT
  let Z' := restrictExactExceptions Z hUT
  apply Finset.mem_biUnion.mpr
  refine ⟨x, Finset.mem_univ _, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨A, ?_, ?_⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ A, hAcard⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨B, ?_, ?_⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ B, hBcard⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨Z', Finset.mem_univ _, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hgrid, compatible_restrict hcomp hUT⟩

/-! ### A finite binomial tail bound -/

noncomputable def boolSupport
    {I : Type*} [Fintype I] [DecidableEq I] (f : I → Bool) : Finset I :=
  Finset.univ.filter fun i ↦ f i = true

noncomputable def boolFunFinsetEquiv
    (I : Type*) [Fintype I] [DecidableEq I] :
    (I → Bool) ≃ Finset I where
  toFun := boolSupport
  invFun := fun S i ↦ decide (i ∈ S)
  left_inv := by
    intro f
    funext i
    by_cases hi : f i = true
    · simp [boolSupport, hi]
    · have hfalse : f i = false := Bool.eq_false_of_not_eq_true hi
      simp [boolSupport, hi, hfalse]
  right_inv := by
    intro S
    ext i
    simp [boolSupport]

lemma card_boolFunctions_support_eq
    {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ) :
    (Finset.univ.filter fun f : I → Bool ↦ (boolSupport f).card = k).card =
      (Fintype.card I).choose k := by
  classical
  let e : {f : I → Bool // (boolSupport f).card = k} ≃
      {S : Finset I // S.card = k} :=
    { toFun := fun f ↦ ⟨boolSupport f.1, f.2⟩
      invFun := fun S ↦
        ⟨(boolFunFinsetEquiv I).symm S.1, by
          have hEq := (boolFunFinsetEquiv I).apply_symm_apply S.1
          change boolSupport ((boolFunFinsetEquiv I).symm S.1) = S.1 at hEq
          rw [hEq]
          exact S.2⟩
      left_inv := fun f ↦ Subtype.ext ((boolFunFinsetEquiv I).symm_apply_apply f.1)
      right_inv := fun S ↦ Subtype.ext ((boolFunFinsetEquiv I).apply_symm_apply S.1) }
  have hcard :
      (Finset.univ.filter fun f : I → Bool ↦
        (boolSupport f).card = k).card =
        Fintype.card {f : I → Bool // (boolSupport f).card = k} := by
    rw [Fintype.card_subtype]
  rw [hcard, Fintype.card_congr e]
  rw [Fintype.card_subtype]
  simpa using Finset.card_powersetCard (Finset.univ : Finset I) k

def binomialTail (n b : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc b n, n.choose k

lemma card_boolFunctions_support_ge_le_tail
    {I : Type*} [Fintype I] [DecidableEq I] (b : ℕ) :
    (Finset.univ.filter fun f : I → Bool ↦ b ≤ (boolSupport f).card).card ≤
      binomialTail (Fintype.card I) b := by
  classical
  let E := fun k : ℕ ↦
    Finset.univ.filter fun f : I → Bool ↦ (boolSupport f).card = k
  have hsub : (Finset.univ.filter fun f : I → Bool ↦
      b ≤ (boolSupport f).card) ⊆
      (Finset.Icc b (Fintype.card I)).biUnion E := by
    intro f hf
    have hf' := (Finset.mem_filter.mp hf).2
    apply Finset.mem_biUnion.mpr
    refine ⟨(boolSupport f).card, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hf', by
        simpa using Finset.card_le_card (Finset.subset_univ (boolSupport f))⟩
    · simp [E]
  calc
    (Finset.univ.filter fun f : I → Bool ↦
        b ≤ (boolSupport f).card).card ≤
        ((Finset.Icc b (Fintype.card I)).biUnion E).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.Icc b (Fintype.card I), (E k).card :=
      Finset.card_biUnion_le
    _ = binomialTail (Fintype.card I) b := by
      apply Finset.sum_congr rfl
      intro k _
      exact card_boolFunctions_support_eq k

lemma binomialTail_eq (n b : ℕ) (hbn : b ≤ n) :
    binomialTail n b = n.choose b + binomialTail n (b + 1) := by
  have hIcc : Finset.Icc b n = insert b (Finset.Icc (b + 1) n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [binomialTail, hIcc]
  simp [binomialTail]

lemma thirteen_choose_succ_le_twelve_choose
    (n k : ℕ) (hkn : k < n) (hratio : 13 * n ≤ 25 * k + 12) :
    13 * n.choose (k + 1) ≤ 12 * n.choose k := by
  have hlinear : 13 * (n - k) ≤ 12 * (k + 1) := by omega
  have hmul : (13 * n.choose (k + 1)) * (k + 1) ≤
      (12 * n.choose k) * (k + 1) := by
    calc
      (13 * n.choose (k + 1)) * (k + 1) =
          13 * (n.choose (k + 1) * (k + 1)) := by ring
      _ = 13 * (n.choose k * (n - k)) := by
        rw [Nat.choose_succ_right_eq]
      _ = n.choose k * (13 * (n - k)) := by ring
      _ ≤ n.choose k * (12 * (k + 1)) :=
        Nat.mul_le_mul_left (n.choose k) hlinear
      _ = (12 * n.choose k) * (k + 1) := by ring
  exact le_of_mul_le_mul_right hmul (by omega)

lemma binomialTail_le_thirteen_choose
    (n b : ℕ) (hbn : b ≤ n) (hratio : 13 * n ≤ 25 * b + 12) :
    binomialTail n b ≤ 13 * n.choose b := by
  revert hratio
  induction hbn using Nat.decreasingInduction with
  | self =>
      intro _
      simp [binomialTail]
  | of_succ k hk ih =>
      intro hratio
      rw [binomialTail_eq n k (Nat.le_of_lt hk)]
      have hi := ih (by omega)
      have hs := thirteen_choose_succ_le_twelve_choose n k hk hratio
      omega

lemma choose_mul_thirteen_twelve_le
    (n k : ℕ) :
    n.choose k * 13 ^ k * 12 ^ (n - k) ≤ 25 ^ n := by
  by_cases hkn : k ≤ n
  · have hterm :
        n.choose k * 13 ^ k * 12 ^ (n - k) ≤
          ∑ j ∈ Finset.range (n + 1),
            n.choose j * 13 ^ j * 12 ^ (n - j) := by
      exact Finset.single_le_sum
        (s := Finset.range (n + 1))
        (f := fun j ↦ n.choose j * 13 ^ j * 12 ^ (n - j))
        (fun j _ ↦ Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))
    calc
      n.choose k * 13 ^ k * 12 ^ (n - k) ≤
          ∑ j ∈ Finset.range (n + 1),
            n.choose j * 13 ^ j * 12 ^ (n - j) := hterm
      _ = ((13 : ℕ) + 12) ^ n := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Nat.cast_id]
        ring
      _ = (25 : ℕ) ^ n := by norm_num
  · have hk : n < k := by omega
    simp [Nat.choose_eq_zero_of_lt hk]

lemma binomialTail_weighted_le
    (n b : ℕ) (hbn : b ≤ n) (hratio : 13 * n ≤ 25 * b + 12) :
    binomialTail n b * (13 ^ b * 12 ^ (n - b)) ≤
      13 * 25 ^ n := by
  calc
    binomialTail n b * (13 ^ b * 12 ^ (n - b)) ≤
        (13 * n.choose b) * (13 ^ b * 12 ^ (n - b)) :=
      Nat.mul_le_mul_right _ (binomialTail_le_thirteen_choose n b hbn hratio)
    _ = 13 * (n.choose b * 13 ^ b * 12 ^ (n - b)) := by ring
    _ ≤ 13 * 25 ^ n :=
      Nat.mul_le_mul_left 13 (choose_mul_thirteen_twelve_le n b)

/-! ### Independent finite Boolean coordinates -/

noncomputable def functionSplitEquiv
    {I : Type*} [Fintype I] [DecidableEq I] (S : Finset I) :
    (I → Bool) ≃
      (({i : I // i ∈ S} → Bool) × ({i : I // i ∉ S} → Bool)) where
  toFun f := (fun i ↦ f i.1, fun i ↦ f i.1)
  invFun g i := if hi : i ∈ S then g.1 ⟨i, hi⟩ else g.2 ⟨i, hi⟩
  left_inv := by
    intro f
    funext i
    by_cases hi : i ∈ S <;> simp [hi]
  right_inv := by
    intro g
    apply Prod.ext <;> funext i
    · simp [i.2]
    · simp [i.2]

noncomputable def trueOn
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (f : I → Bool) : Finset I :=
  S.filter fun i ↦ f i = true

lemma trueOn_card_eq_support_split
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (f : I → Bool) :
    (trueOn S f).card =
      (boolSupport ((functionSplitEquiv S f).1)).card := by
  classical
  let e : {i : I // i ∈ S} ↪ I :=
    { toFun := Subtype.val, inj' := Subtype.coe_injective }
  have hmap :
      (boolSupport ((functionSplitEquiv S f).1)).map e = trueOn S f := by
    ext i
    by_cases hi : i ∈ S
    · simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach,
        true_and, trueOn, hi, Finset.mem_filter, e, functionSplitEquiv]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact (Finset.mem_filter.mp hj).2
      · intro hf
        refine ⟨⟨i, hi⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
    · simp [boolSupport, trueOn, e, functionSplitEquiv, hi]
  have hc := congrArg Finset.card hmap
  rw [Finset.card_map] at hc
  exact hc.symm

lemma card_functions_trueOn_ge_mul_pow
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (b : ℕ) :
    (Finset.univ.filter fun f : I → Bool ↦
      b ≤ (trueOn S f).card).card * 2 ^ S.card ≤
      binomialTail S.card b * 2 ^ Fintype.card I := by
  classical
  let BadS := {g : ({i : I // i ∈ S} → Bool) //
    b ≤ (boolSupport g).card}
  let Rest := {i : I // i ∉ S} → Bool
  let e : {f : I → Bool // b ≤ (trueOn S f).card} ≃ BadS × Rest :=
    ((functionSplitEquiv S).subtypeEquiv (fun f ↦ by
      rw [trueOn_card_eq_support_split])).trans
        Equiv.prodSubtypeFstEquivSubtypeProd
  have hbadcard :
      (Finset.univ.filter fun f : I → Bool ↦
        b ≤ (trueOn S f).card).card =
        Fintype.card {f : I → Bool // b ≤ (trueOn S f).card} := by
    rw [Fintype.card_subtype]
  have hBadS : Fintype.card BadS ≤ binomialTail S.card b := by
    change Fintype.card {g : ({i : I // i ∈ S} → Bool) //
      b ≤ (boolSupport g).card} ≤ _
    have hc : Fintype.card {g : ({i : I // i ∈ S} → Bool) //
        b ≤ (boolSupport g).card} =
        (Finset.univ.filter fun g : ({i : I // i ∈ S} → Bool) ↦
          b ≤ (boolSupport g).card).card := by
      rw [Fintype.card_subtype]
    rw [hc]
    simpa using
      (card_boolFunctions_support_ge_le_tail
        (I := {i : I // i ∈ S}) b)
  have hRest : Fintype.card Rest = 2 ^ (Fintype.card I - S.card) := by
    dsimp [Rest]
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl]
    simp
  rw [hbadcard, Fintype.card_congr e, Fintype.card_prod, hRest]
  calc
    Fintype.card BadS * 2 ^ (Fintype.card I - S.card) * 2 ^ S.card ≤
        binomialTail S.card b * 2 ^ (Fintype.card I - S.card) *
          2 ^ S.card := by gcongr
    _ = binomialTail S.card b * 2 ^ Fintype.card I := by
      have hSle : S.card ≤ Fintype.card I := by
        simpa using Finset.card_le_card (Finset.subset_univ S)
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hSle]

def equalityBit (u v : Bool) : Bool := decide (u = v)

def decodeEqualityBit (b v : Bool) : Bool := if b then v else !v

@[simp] lemma decodeEqualityBit_equalityBit (u v : Bool) :
    decodeEqualityBit (equalityBit u v) v = u := by
  cases u <;> cases v <;> decide

@[simp] lemma equalityBit_decodeEqualityBit (b v : Bool) :
    equalityBit (decodeEqualityBit b v) v = b := by
  cases b <;> cases v <;> decide

/-- Replace each selected Boolean coordinate by its equality bit with an
unselected partner.  Because partners lie outside `S`, this triangular
change of variables is an equivalence. -/
def equalityCoordinateEquiv
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (partner : {i : I // i ∈ S} → I)
    (hpartner : ∀ i, partner i ∉ S) :
    (I → Bool) ≃ (I → Bool) where
  toFun f i := if hi : i ∈ S then
    equalityBit (f i) (f (partner ⟨i, hi⟩)) else f i
  invFun g i := if hi : i ∈ S then
    decodeEqualityBit (g i) (g (partner ⟨i, hi⟩)) else g i
  left_inv := by
    intro f
    funext i
    by_cases hi : i ∈ S
    · simp [hi, hpartner]
    · simp [hi]
  right_inv := by
    intro g
    funext i
    by_cases hi : i ∈ S
    · simp [hi, hpartner]
    · simp [hi]

/-! ### Agreement coordinates in a projective pencil -/

noncomputable def pencilSourceIncidence
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (m : Line F)
    (l : {l : Line F // l ∈ linesThrough x}) : Incidence F :=
  ⟨l.1, ⟨intersectionPoint l.1 m,
    intersectionPoint_incident_left l.1 m⟩⟩

noncomputable def pencilSourceSet
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (m : Line F) : Finset (Incidence F) :=
  (linesThrough x).attach.image (pencilSourceIncidence x m)

lemma pencilSourceIncidence_injective
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (m : Line F) :
    Function.Injective (pencilSourceIncidence x m) := by
  intro l l' h
  apply Subtype.ext
  exact congrArg Sigma.fst h

lemma card_pencilSourceSet
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (m : Line F) :
    (pencilSourceSet x m).card = Fintype.card F + 1 := by
  rw [pencilSourceSet,
    Finset.card_image_iff.mpr (pencilSourceIncidence_injective x m).injOn,
    Finset.card_attach, card_linesThrough]

noncomputable def pencilPartnerIncidence
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (m : Line F)
    (z : {z : Incidence F // z ∈ pencilSourceSet x m}) : Incidence F := by
  have hz := Finset.mem_image.mp z.2
  let l := Classical.choose hz
  have hl := (Classical.choose_spec hz).2
  refine ⟨m, ⟨z.1.2.1, ?_⟩⟩
  have hp := congrArg (fun w : Incidence F ↦ w.2.1) hl
  change intersectionPoint l.1 m = z.1.2.1 at hp
  rw [← hp]
  exact intersectionPoint_incident_right l.1 m

lemma pencilPartnerIncidence_not_mem
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {x : Point F} {m : Line F} (hxm : ¬ Incident x m)
    (z : {z : Incidence F // z ∈ pencilSourceSet x m}) :
    pencilPartnerIncidence x m z ∉ pencilSourceSet x m := by
  intro hmem
  obtain ⟨l, _hl, heq⟩ := Finset.mem_image.mp hmem
  have hline := congrArg Sigma.fst heq
  change l.1 = m at hline
  apply hxm
  rw [← hline]
  exact (mem_linesThrough_iff x l.1).mp l.2

noncomputable def pencilEncodingEquiv
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (m : Line F) (hxm : ¬ Incident x m) :
    Labeling F ≃ (Incidence F → Bool) :=
  labelingEquivFlat.trans
    (equalityCoordinateEquiv (pencilSourceSet x m)
      (pencilPartnerIncidence x m)
      (pencilPartnerIncidence_not_mem hxm))

lemma pencilEncoding_source_value
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (a : Labeling F) (x : Point F) (m : Line F)
    (hxm : ¬ Incident x m)
    (l : {l : Line F // l ∈ linesThrough x}) :
    pencilEncodingEquiv x m hxm a (pencilSourceIncidence x m l) =
      equalityBit
        (a l.1 ⟨intersectionPoint l.1 m,
          intersectionPoint_incident_left l.1 m⟩)
        (a m ⟨intersectionPoint l.1 m,
          intersectionPoint_incident_right l.1 m⟩) := by
  classical
  have hmem : pencilSourceIncidence x m l ∈ pencilSourceSet x m := by
    apply Finset.mem_image.mpr
    exact ⟨l, Finset.mem_attach _ _, rfl⟩
  change (if hi : pencilSourceIncidence x m l ∈ pencilSourceSet x m then
      equalityBit
        (a l.1 ⟨intersectionPoint l.1 m,
          intersectionPoint_incident_left l.1 m⟩)
        (a (pencilPartnerIncidence x m
            ⟨pencilSourceIncidence x m l, hi⟩).1
          (pencilPartnerIncidence x m
            ⟨pencilSourceIncidence x m l, hi⟩).2)
    else a l.1 ⟨intersectionPoint l.1 m,
      intersectionPoint_incident_left l.1 m⟩) = _
  rw [dif_pos hmem]
  congr 2

lemma equalityBit_eq_true_iff (u v : Bool) :
    equalityBit u v = true ↔ u = v := by
  cases u <;> cases v <;> decide

lemma agree_count_eq_trueOn_encoding
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (a : Labeling F) (x : Point F) (m : Line F)
    (hxm : ¬ Incident x m) :
    ((linesThrough x).filter fun l ↦ Agree a l m).card =
      (trueOn (pencilSourceSet x m) (pencilEncodingEquiv x m hxm a)).card := by
  classical
  let e : {l : Line F // l ∈ linesThrough x} ↪ Incidence F :=
    { toFun := pencilSourceIncidence x m
      inj' := pencilSourceIncidence_injective x m }
  have hmap :
      ((linesThrough x).attach.filter fun l ↦ Agree a l.1 m).map e =
        trueOn (pencilSourceSet x m) (pencilEncodingEquiv x m hxm a) := by
    ext z
    constructor
    · intro hz
      obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hz
      have hl' := (Finset.mem_filter.mp hl).2
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · apply Finset.mem_image.mpr
        exact ⟨l, Finset.mem_attach _ _, rfl⟩
      · change pencilEncodingEquiv x m hxm a
            (pencilSourceIncidence x m l) = true
        rw [pencilEncoding_source_value]
        exact (equalityBit_eq_true_iff _ _).mpr hl'
    · intro hz
      have hz' := Finset.mem_filter.mp hz
      obtain ⟨l, _hl, heq⟩ := Finset.mem_image.mp hz'.1
      apply Finset.mem_map.mpr
      refine ⟨l, ?_, heq⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_attach _ _, ?_⟩
      have hval := hz'.2
      rw [← heq, pencilEncoding_source_value] at hval
      exact (equalityBit_eq_true_iff _ _).mp hval
  have hc := congrArg Finset.card hmap
  rw [Finset.card_map,
    Finset.filter_attach (fun l : Line F ↦ Agree a l m) (linesThrough x),
    Finset.card_map, Finset.card_attach] at hc
  exact hc

/-- Labelings for which an exterior line agrees with at least `b` lines of
the pencil through `x`. -/
noncomputable def agreementBadAt
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (m : Line F) (b : ℕ) : Finset (Labeling F) :=
  Finset.univ.filter fun a ↦
    b ≤ ((linesThrough x).filter fun l ↦ Agree a l m).card

lemma card_agreementBadAt_mul_pow
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (m : Line F) (hxm : ¬ Incident x m) (b : ℕ) :
    (agreementBadAt x m b).card * 2 ^ (Fintype.card F + 1) ≤
      binomialTail (Fintype.card F + 1) b *
        Fintype.card (Labeling F) := by
  classical
  let e :
      {a : Labeling F //
        b ≤ ((linesThrough x).filter fun l ↦ Agree a l m).card} ≃
      {f : Incidence F → Bool //
        b ≤ (trueOn (pencilSourceSet x m) f).card} :=
    (pencilEncodingEquiv x m hxm).subtypeEquiv (fun a ↦ by
      rw [agree_count_eq_trueOn_encoding a x m hxm])
  have hcard :
      (agreementBadAt x m b).card =
        (Finset.univ.filter fun f : Incidence F → Bool ↦
          b ≤ (trueOn (pencilSourceSet x m) f).card).card := by
    calc
      (agreementBadAt x m b).card =
          Fintype.card {a : Labeling F //
            b ≤ ((linesThrough x).filter fun l ↦ Agree a l m).card} := by
        rw [Fintype.card_subtype]
        rfl
      _ = Fintype.card {f : Incidence F → Bool //
            b ≤ (trueOn (pencilSourceSet x m) f).card} :=
        Fintype.card_congr e
      _ = (Finset.univ.filter fun f : Incidence F → Bool ↦
            b ≤ (trueOn (pencilSourceSet x m) f).card).card := by
        rw [Fintype.card_subtype]
  rw [hcard, ← card_pencilSourceSet x m]
  calc
    (Finset.univ.filter fun f : Incidence F → Bool ↦
        b ≤ (trueOn (pencilSourceSet x m) f).card).card *
          2 ^ (pencilSourceSet x m).card ≤
        binomialTail (pencilSourceSet x m).card b *
          2 ^ Fintype.card (Incidence F) :=
      card_functions_trueOn_ge_mul_pow (pencilSourceSet x m) b
    _ = binomialTail (pencilSourceSet x m).card b *
          Fintype.card (Labeling F) := by
      rw [card_labeling, card_incidence]

/-- Flip every incidence label on one line. -/
def flipLineLabel
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (m : Line F) : Labeling F ≃ Labeling F where
  toFun a l p := if l = m then !(a l p) else a l p
  invFun a l p := if l = m then !(a l p) else a l p
  left_inv := by
    intro a
    funext l p
    by_cases h : l = m <;> simp [h]
  right_inv := by
    intro a
    funext l p
    by_cases h : l = m <;> simp [h]

lemma agree_flipLineLabel_iff_not
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (a : Labeling F) {l m : Line F} (hlm : l ≠ m) :
    Agree (flipLineLabel m a) l m ↔ ¬ Agree a l m := by
  unfold Agree
  simp only [flipLineLabel, Equiv.coe_fn_mk]
  rw [if_neg hlm]
  simp only [if_true]
  generalize a l ⟨intersectionPoint l m,
    intersectionPoint_incident_left l m⟩ = u
  generalize a m ⟨intersectionPoint l m,
    intersectionPoint_incident_right l m⟩ = v
  cases u <;> cases v <;> decide

lemma disagreement_count_flipLineLabel
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (a : Labeling F) (x : Point F) (m : Line F)
    (hxm : ¬ Incident x m) :
    ((linesThrough x).filter fun l ↦ ¬ Agree a l m).card =
      ((linesThrough x).filter fun l ↦
        Agree (flipLineLabel m a) l m).card := by
  classical
  congr 1
  ext l
  by_cases hl : l ∈ linesThrough x
  · have hlm : l ≠ m := by
      intro h
      subst l
      exact hxm ((mem_linesThrough_iff x m).mp hl)
    simp only [Finset.mem_filter, hl, true_and]
    exact (agree_flipLineLabel_iff_not a hlm).symm
  · simp [hl]

/-- Labelings for which an exterior line disagrees with at least `b` lines
of a pencil. -/
noncomputable def disagreementBadAt
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (m : Line F) (b : ℕ) : Finset (Labeling F) :=
  Finset.univ.filter fun a ↦
    b ≤ ((linesThrough x).filter fun l ↦ ¬ Agree a l m).card

lemma card_disagreementBadAt_eq
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (m : Line F) (hxm : ¬ Incident x m) (b : ℕ) :
    (disagreementBadAt x m b).card = (agreementBadAt x m b).card := by
  classical
  let e :
      {a : Labeling F //
        b ≤ ((linesThrough x).filter fun l ↦ ¬ Agree a l m).card} ≃
      {a : Labeling F //
        b ≤ ((linesThrough x).filter fun l ↦ Agree a l m).card} :=
    (flipLineLabel m).subtypeEquiv (fun a ↦ by
      rw [disagreement_count_flipLineLabel a x m hxm])
  calc
    (disagreementBadAt x m b).card =
        Fintype.card {a : Labeling F //
          b ≤ ((linesThrough x).filter fun l ↦ ¬ Agree a l m).card} := by
      rw [Fintype.card_subtype]
      rfl
    _ = Fintype.card {a : Labeling F //
          b ≤ ((linesThrough x).filter fun l ↦ Agree a l m).card} :=
      Fintype.card_congr e
    _ = (agreementBadAt x m b).card := by
      rw [Fintype.card_subtype]
      rfl

lemma card_disagreementBadAt_mul_pow
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (m : Line F) (hxm : ¬ Incident x m) (b : ℕ) :
    (disagreementBadAt x m b).card * 2 ^ (Fintype.card F + 1) ≤
      binomialTail (Fintype.card F + 1) b *
        Fintype.card (Labeling F) := by
  rw [card_disagreementBadAt_eq x m hxm b]
  exact card_agreementBadAt_mul_pow x m hxm b

/-- The union of the two tails which violate balance at one exterior
point--line pair.  Incident pairs impose no condition. -/
noncomputable def balanceBadAt
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (m : Line F) (b : ℕ) : Finset (Labeling F) :=
  if ¬ Incident x m then
    agreementBadAt x m b ∪ disagreementBadAt x m b
  else ∅

lemma card_balanceBadAt_mul_pow
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    (x : Point F) (m : Line F) (b : ℕ) :
    (balanceBadAt x m b).card * 2 ^ (Fintype.card F + 1) ≤
      2 * binomialTail (Fintype.card F + 1) b *
        Fintype.card (Labeling F) := by
  classical
  by_cases hxm : ¬ Incident x m
  · rw [balanceBadAt, if_pos hxm]
    calc
      (agreementBadAt x m b ∪ disagreementBadAt x m b).card *
          2 ^ (Fintype.card F + 1) ≤
          ((agreementBadAt x m b).card +
            (disagreementBadAt x m b).card) *
              2 ^ (Fintype.card F + 1) :=
        Nat.mul_le_mul_right _
          (Finset.card_union_le (agreementBadAt x m b)
            (disagreementBadAt x m b))
      _ = (agreementBadAt x m b).card *
            2 ^ (Fintype.card F + 1) +
          (disagreementBadAt x m b).card *
            2 ^ (Fintype.card F + 1) := by ring
      _ ≤ binomialTail (Fintype.card F + 1) b *
            Fintype.card (Labeling F) +
          binomialTail (Fintype.card F + 1) b *
            Fintype.card (Labeling F) :=
        Nat.add_le_add
          (card_agreementBadAt_mul_pow x m hxm b)
          (card_disagreementBadAt_mul_pow x m hxm b)
      _ = 2 * binomialTail (Fintype.card F + 1) b *
            Fintype.card (Labeling F) := by ring
  · simp [balanceBadAt, hxm]

/-- Every balance violation, over all point--line pairs of the plane. -/
noncomputable def balanceBad
    (F : Type*) [Fintype F] [Field F] [DecidableEq F]
    (balance : ℕ) : Finset (Labeling F) :=
  (Finset.univ : Finset (Point F)).biUnion fun x ↦
    (Finset.univ : Finset (Line F)).biUnion fun m ↦
      balanceBadAt x m (balance + 1)

lemma card_balanceBad_mul_pow
    (F : Type*) [Fintype F] [Field F] [DecidableEq F]
    (balance : ℕ) :
    (balanceBad F balance).card * 2 ^ (Fintype.card F + 1) ≤
      (Fintype.card F ^ 2 + Fintype.card F + 1) ^ 2 *
        (2 * binomialTail (Fintype.card F + 1) (balance + 1)) *
          Fintype.card (Labeling F) := by
  classical
  have hcard : (balanceBad F balance).card ≤
      ∑ x : Point F, ∑ m : Line F,
        (balanceBadAt x m (balance + 1)).card := by
    calc
      (balanceBad F balance).card ≤
          ∑ x : Point F,
            ((Finset.univ : Finset (Line F)).biUnion fun m ↦
              balanceBadAt x m (balance + 1)).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ x : Point F, ∑ m : Line F,
            (balanceBadAt x m (balance + 1)).card := by
        apply Finset.sum_le_sum
        intro x _
        exact Finset.card_biUnion_le
  calc
    (balanceBad F balance).card * 2 ^ (Fintype.card F + 1) ≤
        (∑ x : Point F, ∑ m : Line F,
          (balanceBadAt x m (balance + 1)).card) *
            2 ^ (Fintype.card F + 1) :=
      Nat.mul_le_mul_right _ hcard
    _ = ∑ x : Point F, ∑ m : Line F,
          (balanceBadAt x m (balance + 1)).card *
            2 ^ (Fintype.card F + 1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
    _ ≤ ∑ _x : Point F, ∑ _m : Line F,
          2 * binomialTail (Fintype.card F + 1) (balance + 1) *
            Fintype.card (Labeling F) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro m _
      exact card_balanceBadAt_mul_pow x m (balance + 1)
    _ = (Fintype.card F ^ 2 + Fintype.card F + 1) ^ 2 *
          (2 * binomialTail (Fintype.card F + 1) (balance + 1)) *
            Fintype.card (Labeling F) := by
      simp only [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ,
        Projective.card_point, Projective.card_line]
      ring

lemma isBalanced_of_not_mem_balanceBad
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {balance : ℕ} {a : Labeling F} (ha : a ∉ balanceBad F balance) :
    IsBalanced balance a := by
  classical
  intro x m hxm
  have hlocal : a ∉ balanceBadAt x m (balance + 1) := by
    intro hmem
    apply ha
    apply Finset.mem_biUnion.mpr
    refine ⟨x, Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨m, Finset.mem_univ _, hmem⟩
  rw [balanceBadAt, if_pos hxm] at hlocal
  have hagree : ¬ balance + 1 ≤
      ((linesThrough x).filter fun l ↦ Agree a l m).card := by
    intro h
    apply hlocal
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have hdisagree : ¬ balance + 1 ≤
      ((linesThrough x).filter fun l ↦ ¬ Agree a l m).card := by
    intro h
    apply hlocal
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  omega

/-! ### The fixed numerical form of the labeling lemma -/

def fixedC0 : ℕ := 4000
def fixedDegree : ℕ := 2 ^ 70
def fixedSample : ℕ := 2 ^ 110
def fixedGrid : ℕ := 1000000000
def fixedEnergy : ℕ := 2 ^ 20

def fixedBalance (K : ℕ) : ℕ := 13 * ((K + 1) / 25) + 12

lemma fixedBalance_ratio (K : ℕ) :
    13 * (K + 1) ≤ 25 * (fixedBalance K + 1) + 12 := by
  have hmod := Nat.mod_lt (K + 1) (by norm_num : 0 < 25)
  have hdiv := Nat.div_add_mod (K + 1) 25
  unfold fixedBalance
  omega

lemma fixedBalance_succ_le (K : ℕ) (hK : 50 ≤ K + 1) :
    fixedBalance K + 1 ≤ K + 1 := by
  have hmod := Nat.mod_lt (K + 1) (by norm_num : 0 < 25)
  have hdiv := Nat.div_add_mod (K + 1) 25
  unfold fixedBalance
  omega

/-- Avoiding the three explicitly counted exceptional sets gives the
deterministic concentration statement needed later.  The remaining two
hypotheses are transparent integer checks for each of our two fields. -/
lemma isPencilForcing_of_avoids_fixed_bad
    {F : Type*} [Fintype F] [Field F] [DecidableEq F]
    {a : Labeling F} {balance : ℕ}
    (hC0 : fixedC0 ≤ Fintype.card F + 1)
    (hsample : 4 * fixedSample ≤ 3 * Fintype.card F)
    (hnumeric :
      16 * (balance + fixedC0) +
          12 * ((4 * fixedC0) * (4 * fixedC0 - 1) + (fixedGrid - 1)) <
        9 * Fintype.card F)
    (hbal : IsBalanced balance a)
    (hlow : a ∉ lowEnergyBadAt F fixedC0 fixedDegree fixedSample)
    (hgridbad : a ∉ gridBad F fixedC0 fixedGrid) :
    IsPencilForcing fixedC0 a := by
  classical
  intro gamma T hT hbad
  obtain ⟨Z, hZsub⟩ :=
    exists_exactExceptions_superset hC0 a gamma T hbad
  have hcomp : Compatible a T Z.1 :=
    compatible_of_mismatches_subset a gamma T Z.1 hZsub
  have hsampleT : fixedSample ≤ T.card := by
    have hmul : 4 * fixedSample ≤ 4 * T.card := hsample.trans hT
    exact le_of_mul_le_mul_left hmul (by norm_num)
  obtain ⟨U, hUT, hUcard⟩ := Finset.exists_subset_card_eq hsampleT
  let ZU := restrictExactExceptions Z hUT
  have hcompU : Compatible a U ZU.1 := compatible_restrict hcomp hUT
  have hnotdegree : ¬ ∀ p : Point F, lineDegree U p ≤ fixedDegree := by
    intro hdegree
    apply hlow
    apply Finset.mem_biUnion.mpr
    refine ⟨U, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ U, hUcard⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨ZU, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hcompU, hdegree⟩
  push Not at hnotdegree
  obtain ⟨x, hxU⟩ := hnotdegree
  have hdegree_mono : lineDegree U x ≤ lineDegree T x := by
    apply Finset.card_le_card
    intro l hl
    have hl' := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨hUT hl'.1, hl'.2⟩
  have hxT : fixedDegree < lineDegree T x := hxU.trans_le hdegree_mono
  let O := T.filter fun l ↦ ¬ Incident x l
  have hOsmall : O.card < fixedGrid := by
    by_contra h
    have hoff : fixedGrid ≤ O.card := by omega
    apply hgridbad
    apply mem_gridBad_of_large_pencil Z hcomp x hoff
    have hthreshold :
        fixedGrid + fixedGrid * (fixedGrid - 1) ≤ fixedDegree + 1 := by
      norm_num [fixedGrid, fixedDegree]
    omega
  refine ⟨x, ?_⟩
  by_contra hconcentrated
  have hAlarge : 4 * fixedC0 ≤ O.card := by
    push Not at hconcentrated
    exact hconcentrated
  obtain ⟨A, hAO, hAcard⟩ := Finset.exists_subset_card_eq hAlarge
  let P := T.filter fun l ↦ Incident x l
  let B := P \ badPencilLines x A
  have hAoff : ∀ l ∈ A, ¬ Incident x l := by
    intro l hl
    exact (Finset.mem_filter.mp (hAO hl)).2
  have hPpencil : ∀ m ∈ P, Incident x m := by
    intro m hm
    exact (Finset.mem_filter.mp hm).2
  have hBsub : B ⊆ P \ badPencilLines x A := by rfl
  have hsep : IsSeparatedGrid x A B :=
    separatedGrid_of_subsets hAoff hPpencil hBsub
  have hAT : A ⊆ T :=
    hAO.trans (Finset.filter_subset _ _)
  have hBT : B ⊆ T :=
    (Finset.sdiff_subset.trans (Finset.filter_subset _ _))
  have hcells : A.card * B.card ≤
      A.card * balance + A.card * fixedC0 + B.card * fixedC0 := by
    calc
      A.card * B.card ≤
          (gridGood Z.1 A B).card + (gridLeftBad Z.1 A B).card +
            (gridRightBad Z.1 A B).card :=
        card_gridCells_le_good_bad Z.1
      _ ≤ A.card * balance + A.card * fixedC0 + B.card * fixedC0 := by
        gcongr
        · exact card_gridGood_le_balance hcomp hbal hsep hAT hBT
        · exact card_gridLeftBad_le Z hsep hAT
        · exact card_gridRightBad_le Z hsep hBT
  have hthree : 3 * B.card ≤ 4 * (balance + fixedC0) := by
    have hcancel : 12000 * B.card ≤
        16000 * balance + 16000 * 4000 := by
      apply Nat.le_of_add_le_add_right (b := 4000 * B.card)
      calc
        12000 * B.card + 4000 * B.card = 16000 * B.card := by ring
        _ = A.card * B.card := by rw [hAcard]; rfl
        _ ≤ A.card * balance + A.card * fixedC0 +
              B.card * fixedC0 := hcells
        _ = (16000 * balance + 16000 * 4000) +
              4000 * B.card := by
          rw [hAcard]
          simp [fixedC0, Nat.mul_comm]
    norm_num [fixedC0]
    omega
  have hPO : P.card + O.card = T.card := by
    exact Finset.card_filter_add_card_filter_not
      (s := T) (fun l ↦ Incident x l)
  have hBdecomp :
      B.card + (P ∩ badPencilLines x A).card = P.card := by
    exact Finset.card_sdiff_add_card_inter P (badPencilLines x A)
  have hinter : (P ∩ badPencilLines x A).card ≤ 16000 * 15999 := by
    calc
      (P ∩ badPencilLines x A).card ≤ (badPencilLines x A).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ ≤ A.card * (A.card - 1) := card_badPencilLines_le x A
      _ = 16000 * 15999 := by rw [hAcard]; rfl
  have hOupper : O.card ≤ 999999999 := by
    norm_num [fixedGrid] at hOsmall
    omega
  have h12B : 12 * B.card ≤ 16 * (balance + fixedC0) := by
    omega
  have h12B' : 12 * B.card ≤ 16 * (balance + 4000) := by
    simpa [fixedC0] using h12B
  norm_num [fixedC0, fixedGrid] at hnumeric
  omega

lemma fixed_order_parameter_bounds (K : ℕ) (hKpos : 1 ≤ K)
    (hKupper : K ≤ 2 ^ 256) :
    K + 1 ≤ 2 ^ 257 ∧ K ^ 2 + K + 1 ≤ 2 ^ 514 := by
  have hp : 1 ≤ 2 ^ 256 := one_le_pow₀ (by norm_num)
  have hsucc : K + 1 ≤ 2 ^ 257 := by
    calc
      K + 1 ≤ 2 ^ 256 + 2 ^ 256 := Nat.add_le_add hKupper hp
      _ = 2 ^ 257 := by rw [show 257 = 256 + 1 by omega, pow_succ]; omega
  have hKself : K ≤ K ^ 2 := by
    rw [pow_two]
    simpa using Nat.mul_le_mul_left K hKpos
  have hone : 1 ≤ K ^ 2 := one_le_pow₀ hKpos
  have hLrough : K ^ 2 + K + 1 ≤ 4 * K ^ 2 := by omega
  have hsq : K ^ 2 ≤ (2 ^ 256) ^ 2 := Nat.pow_le_pow_left hKupper 2
  have hL : K ^ 2 + K + 1 ≤ 2 ^ 514 := by
    calc
      K ^ 2 + K + 1 ≤ 4 * K ^ 2 := hLrough
      _ ≤ 4 * (2 ^ 256) ^ 2 := Nat.mul_le_mul_left 4 hsq
      _ = 2 ^ 514 := by
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
  exact ⟨hsucc, hL⟩

lemma four_mul_card_le_of_cross
    {A B P N : ℕ} (hB : 0 < B)
    (hcross : A * P ≤ B * N) (hscale : 4 * B ≤ P) :
    4 * A ≤ N := by
  apply le_of_mul_le_mul_left (a := B) (by
    calc
      B * (4 * A) = A * (4 * B) := by ring
      _ ≤ A * P := Nat.mul_le_mul_left A hscale
      _ ≤ B * N := hcross) hB

lemma four_mul_two_pow_blocks (a u b v : ℕ) :
    4 * ((2 ^ a) ^ u * (2 ^ b) ^ v) =
      2 ^ (2 + a * u + b * v) := by
  rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul,
    ← pow_add, ← pow_add]
  congr 1
  omega

lemma four_mul_two_pow_grid (a m b v : ℕ) :
    4 * ((2 ^ a) * ((2 ^ a) ^ m) ^ 2 * (2 ^ b) ^ v) =
      2 ^ (2 + a + 2 * (a * m) + b * v) := by
  rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul,
    ← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

lemma low_prefactor_le_pow
    (K C S E : ℕ) (hKpos : 1 ≤ K) (hKupper : K ≤ 2 ^ 256)
    (htwo : 2 ≤ S) (hcoeff : 1 + 514 + 257 * C ≤ E) :
    4 * ((K ^ 2 + K + 1).choose S * (K + 1) ^ (C * S)) ≤
      2 ^ (E * S) := by
  obtain ⟨hK1, hL⟩ := fixed_order_parameter_bounds K hKpos hKupper
  have hexp :
      2 + 514 * S + 257 * (C * S) ≤ E * S := by
    calc
      2 + 514 * S + 257 * (C * S) ≤
          S + 514 * S + 257 * (C * S) := by omega
      _ = (1 + 514 + 257 * C) * S := by ring
      _ ≤ E * S := Nat.mul_le_mul_right _ hcoeff
  have hchoose : (K ^ 2 + K + 1).choose S ≤ (2 ^ 514) ^ S :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hL S)
  have hlabels : (K + 1) ^ (C * S) ≤ (2 ^ 257) ^ (C * S) :=
    Nat.pow_le_pow_left hK1 _
  have hmono :
      4 * ((K ^ 2 + K + 1).choose S * (K + 1) ^ (C * S)) ≤
        4 * ((2 ^ 514) ^ S * (2 ^ 257) ^ (C * S)) :=
    Nat.mul_le_mul_left 4 (Nat.mul_le_mul hchoose hlabels)
  have heq : 4 * ((2 ^ 514) ^ S * (2 ^ 257) ^ (C * S)) =
      2 ^ (2 + 514 * S + 257 * (C * S)) :=
    four_mul_two_pow_blocks 514 S 257 (C * S)
  have hpow : 2 ^ (2 + 514 * S + 257 * (C * S)) ≤ 2 ^ (E * S) := by
    exact pow_le_pow_right' (by norm_num) hexp
  exact hmono.trans (heq.le.trans hpow)

def fixedGridEnergy : ℕ :=
  fixedGrid * fixedGrid - 2 * fixedGrid * fixedC0

lemma fixed_grid_energy_budget :
    fixedGridEnergy + 2 * fixedGrid * fixedC0 ≤
      fixedGrid * fixedGrid := by
  norm_num [fixedGridEnergy, fixedGrid, fixedC0]

lemma grid_prefactor_le_pow
    (K C M E : ℕ) (hKpos : 1 ≤ K) (hKupper : K ≤ 2 ^ 256)
    (hexp :
      2 + 514 + 2 * (514 * M) + 257 * (2 * C * M) ≤ E) :
    4 * ((K ^ 2 + K + 1) *
      ((K ^ 2 + K + 1).choose M) ^ 2 *
      (K + 1) ^ (2 * C * M)) ≤
        2 ^ E := by
  obtain ⟨hK1, hL⟩ := fixed_order_parameter_bounds K hKpos hKupper
  have hchoose : (K ^ 2 + K + 1).choose M ≤ (2 ^ 514) ^ M :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hL M)
  have hchoose2 : ((K ^ 2 + K + 1).choose M) ^ 2 ≤
      ((2 ^ 514) ^ M) ^ 2 := Nat.pow_le_pow_left hchoose 2
  have hlabels : (K + 1) ^ (2 * C * M) ≤
      (2 ^ 257) ^ (2 * C * M) :=
    Nat.pow_le_pow_left hK1 _
  have hmono :
      4 * ((K ^ 2 + K + 1) *
        ((K ^ 2 + K + 1).choose M) ^ 2 *
        (K + 1) ^ (2 * C * M)) ≤
        4 * ((2 ^ 514) *
          ((2 ^ 514) ^ M) ^ 2 *
          (2 ^ 257) ^ (2 * C * M)) :=
    Nat.mul_le_mul_left 4
      (Nat.mul_le_mul (Nat.mul_le_mul hL hchoose2) hlabels)
  have heq : 4 * ((2 ^ 514) * ((2 ^ 514) ^ M) ^ 2 *
      (2 ^ 257) ^ (2 * C * M)) =
      2 ^ (2 + 514 + 2 * (514 * M) + 257 * (2 * C * M)) :=
    four_mul_two_pow_grid 514 M 257 (2 * C * M)
  have hpow : 2 ^ (2 + 514 + 2 * (514 * M) +
      257 * (2 * C * M)) ≤ 2 ^ E := by
    exact pow_le_pow_right' (by norm_num) hexp
  exact hmono.trans (heq.le.trans hpow)

lemma four_mul_lowEnergyBad_le_of_exponent
    (F : Type*) [Fintype F] [Field F] [DecidableEq F]
    (C H S E : ℕ)
    (hKpos : 1 ≤ Fintype.card F)
    (hKupper : Fintype.card F ≤ 2 ^ 256)
    (hSample : S ≤ Fintype.card F) (htwo : 2 ≤ S) (hH : 0 < H)
    (hsize : H * (E + 2 * C) ≤ S - 1)
    (hcoeff : 1 + 514 + 257 * C ≤ E) :
    4 * (lowEnergyBadAt F C H S).card ≤
      Fintype.card (Labeling F) := by
  let B := (Fintype.card F ^ 2 + Fintype.card F + 1).choose S *
    (Fintype.card F + 1) ^ (C * S)
  have hcross := card_lowEnergyBadAt_cross F
    (C0 := C) (H := H) (E0 := E) (s := S) hH hsize
  have hscale : 4 * B ≤ 2 ^ (E * S) := by
    exact low_prefactor_le_pow (Fintype.card F) C S E
      hKpos hKupper htwo hcoeff
  have hB : 0 < B := by
    dsimp [B]
    have hsL : S ≤
        Fintype.card F ^ 2 + Fintype.card F + 1 := by
      have hKL : Fintype.card F ≤
          Fintype.card F ^ 2 + Fintype.card F + 1 := by omega
      exact hSample.trans hKL
    exact Nat.mul_pos (Nat.choose_pos hsL)
      (Nat.pow_pos (by omega))
  exact four_mul_card_le_of_cross hB hcross hscale

lemma four_mul_lowEnergyBad_le
    (F : Type*) [Fintype F] [Field F] [DecidableEq F]
    (hKpos : 1 ≤ Fintype.card F)
    (hKupper : Fintype.card F ≤ 2 ^ 256)
    (hSample : fixedSample ≤ Fintype.card F) :
    4 * (lowEnergyBadAt F fixedC0 fixedDegree fixedSample).card ≤
      Fintype.card (Labeling F) := by
  refine four_mul_lowEnergyBad_le_of_exponent F fixedC0 fixedDegree
    fixedSample fixedEnergy hKpos hKupper hSample ?_ ?_ ?_ ?_
  · norm_num [fixedSample]
  · exact Nat.pow_pos (by norm_num)
  · norm_num [fixedDegree, fixedEnergy, fixedC0, fixedSample]
  · norm_num [fixedC0, fixedEnergy]

lemma four_mul_gridBad_le_of_exponent
    (F : Type*) [Fintype F] [Field F] [DecidableEq F]
    (C M E : ℕ)
    (hKpos : 1 ≤ Fintype.card F)
    (hKupper : Fintype.card F ≤ 2 ^ 256)
    (hGrid : M ≤ Fintype.card F)
    (hbudget : E + 2 * M * C ≤ M * M)
    (hexp : 2 + 514 + 2 * (514 * M) + 257 * (2 * C * M) ≤ E) :
    4 * (gridBad F C M).card ≤
      Fintype.card (Labeling F) := by
  let B := (Fintype.card F ^ 2 + Fintype.card F + 1) *
    ((Fintype.card F ^ 2 + Fintype.card F + 1).choose M) ^ 2 *
    (Fintype.card F + 1) ^ (2 * C * M)
  have hcross := card_gridBad_cross F (C0 := C) (M := M) (E0 := E) hbudget
  have hscale : 4 * B ≤ 2 ^ E := by
    exact grid_prefactor_le_pow (Fintype.card F) C M E
      hKpos hKupper hexp
  have hB : 0 < B := by
    dsimp [B]
    have hGL : M ≤
        Fintype.card F ^ 2 + Fintype.card F + 1 := by
      have hKL : Fintype.card F ≤
          Fintype.card F ^ 2 + Fintype.card F + 1 := by omega
      exact hGrid.trans hKL
    have hc : 0 < (Fintype.card F ^ 2 + Fintype.card F + 1).choose M :=
      Nat.choose_pos hGL
    exact Nat.mul_pos
      (Nat.mul_pos (by omega) (Nat.pow_pos hc))
      (Nat.pow_pos (by omega))
  exact four_mul_card_le_of_cross hB hcross hscale

lemma four_mul_gridBad_le
    (F : Type*) [Fintype F] [Field F] [DecidableEq F]
    (hKpos : 1 ≤ Fintype.card F)
    (hKupper : Fintype.card F ≤ 2 ^ 256)
    (hGrid : fixedGrid ≤ Fintype.card F) :
    4 * (gridBad F fixedC0 fixedGrid).card ≤
      Fintype.card (Labeling F) := by
  apply four_mul_gridBad_le_of_exponent F fixedC0 fixedGrid fixedGridEnergy
    hKpos hKupper hGrid fixed_grid_energy_budget
  norm_num [fixedGrid, fixedC0, fixedGridEnergy]

/-! The balance tail gains a fixed factor on each block of `35 * 25`
coordinates.  These are ordinary finite integer inequalities. -/

lemma balance_block_base :
    25 ^ 25 ≤ 2 ^ 25 * 13 ^ 13 * 12 ^ 12 := by
  norm_num

lemma balance_block_gain :
    2 * (25 ^ 25) ^ 35 ≤
      (2 ^ 25 * 13 ^ 13 * 12 ^ 12) ^ 35 := by
  norm_num

lemma balance_many_block_gain (q : ℕ) (hq : 70000 ≤ q) :
    2 ^ 2000 * (25 ^ 25) ^ q ≤
      (2 ^ 25 * 13 ^ 13 * 12 ^ 12) ^ q := by
  let r := q - 70000
  have hqeq : q = 70000 + r := by dsimp [r]; omega
  have hcore : (2 * (25 ^ 25) ^ 35) ^ 2000 =
      2 ^ 2000 * (25 ^ 25) ^ 70000 := by
    rw [mul_pow, ← pow_mul]
  have hleft :
      2 ^ 2000 * (25 ^ 25) ^ q =
        (2 * (25 ^ 25) ^ 35) ^ 2000 * (25 ^ 25) ^ r := by
    rw [hqeq, pow_add, hcore]
    ring
  have hright :
      (2 ^ 25 * 13 ^ 13 * 12 ^ 12) ^ q =
        ((2 ^ 25 * 13 ^ 13 * 12 ^ 12) ^ 35) ^ 2000 *
          (2 ^ 25 * 13 ^ 13 * 12 ^ 12) ^ r := by
    rw [hqeq, pow_add, ← pow_mul]
  rw [hleft, hright]
  exact Nat.mul_le_mul
    (Nat.pow_le_pow_left balance_block_gain 2000)
    (Nat.pow_le_pow_left balance_block_base r)

lemma balance_residue_cost :
    2 ^ 1035 * 25 ^ 24 * 12 ^ 24 ≤ 2 ^ 2000 := by
  have h25 : 25 ^ 24 ≤ (2 ^ 5) ^ 24 :=
    Nat.pow_le_pow_left (by norm_num) 24
  have h12 : 12 ^ 24 ≤ (2 ^ 4) ^ 24 :=
    Nat.pow_le_pow_left (by norm_num) 24
  calc
    2 ^ 1035 * 25 ^ 24 * 12 ^ 24 ≤
        2 ^ 1035 * (2 ^ 5) ^ 24 * (2 ^ 4) ^ 24 := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h25) h12
    _ = 2 ^ (1035 + 5 * 24 + 4 * 24) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    _ ≤ 2 ^ 2000 := pow_le_pow_right' (by norm_num) (by norm_num)

lemma balance_plane_coefficient
    (K : ℕ) (hKpos : 1 ≤ K) (hKupper : K ≤ 2 ^ 256) :
    8 * (K ^ 2 + K + 1) ^ 2 * 13 ≤ 2 ^ 1035 := by
  have hL := (fixed_order_parameter_bounds K hKpos hKupper).2
  calc
    8 * (K ^ 2 + K + 1) ^ 2 * 13 ≤
        (2 ^ 3) * (2 ^ 514) ^ 2 * (2 ^ 4) := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hL 2))
        (by norm_num)
    _ = 2 ^ (3 + 514 * 2 + 4) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
    _ = 2 ^ 1035 := by norm_num

lemma balance_block_pow (q : ℕ) :
    (2 ^ 25 * 13 ^ 13 * 12 ^ 12) ^ q =
      2 ^ (25 * q) * 13 ^ (13 * q) * 12 ^ (12 * q) := by
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]

lemma balance_base_pow (q : ℕ) :
    (25 ^ 25) ^ q = 25 ^ (25 * q) := by
  rw [← pow_mul]

lemma balance_weight_domination
    (K : ℕ) (hKpos : 1 ≤ K) (hKupper : K ≤ 2 ^ 256)
    (hqLarge : 70000 ≤ (K + 1) / 25) :
    8 * (K ^ 2 + K + 1) ^ 2 * 13 * 25 ^ (K + 1) ≤
      2 ^ (K + 1) * 13 ^ (fixedBalance K + 1) *
        12 ^ ((K + 1) - (fixedBalance K + 1)) := by
  let n := K + 1
  let q := n / 25
  let r := n % 25
  let b := fixedBalance K + 1
  have hr : r < 25 := Nat.mod_lt n (by norm_num)
  have hdecomp : n = 25 * q + r := by
    have h := Nat.div_add_mod n 25
    dsimp [q, r]
    omega
  have hqL : 70000 ≤ q := by simpa [q, n] using hqLarge
  have hn50 : 50 ≤ n := by
    omega
  have hbn : b ≤ n := by
    dsimp [b, n]
    exact fixedBalance_succ_le K hn50
  have h25q : 25 * q ≤ n := by omega
  have h13q : 13 * q ≤ b := by
    dsimp [b, q, n, fixedBalance]
    omega
  have h12q : 12 * q ≤ n - b + 24 := by
    dsimp [b, q, r, n, fixedBalance] at hdecomp hr ⊢
    omega
  have h2pow : 2 ^ (25 * q) ≤ 2 ^ n :=
    pow_le_pow_right' (by norm_num) h25q
  have h13pow : 13 ^ (13 * q) ≤ 13 ^ b :=
    pow_le_pow_right' (by norm_num) h13q
  have h12pow : 12 ^ (12 * q) ≤ 12 ^ (n - b + 24) :=
    pow_le_pow_right' (by norm_num) h12q
  have hlower :
      (2 ^ 25 * 13 ^ 13 * 12 ^ 12) ^ q ≤
        (2 ^ n * 13 ^ b * 12 ^ (n - b)) * 12 ^ 24 := by
    rw [balance_block_pow]
    calc
      2 ^ (25 * q) * 13 ^ (13 * q) * 12 ^ (12 * q) ≤
          2 ^ n * 13 ^ b * 12 ^ (n - b + 24) :=
        Nat.mul_le_mul (Nat.mul_le_mul h2pow h13pow) h12pow
      _ = (2 ^ n * 13 ^ b * 12 ^ (n - b)) * 12 ^ 24 := by
        rw [pow_add]
        ring
  have h25pow : 25 ^ n ≤ (25 ^ 25) ^ q * 25 ^ 24 := by
    rw [hdecomp, pow_add, balance_base_pow]
    exact Nat.mul_le_mul_left _
      (pow_le_pow_right' (by norm_num) (by omega : r ≤ 24))
  have hcoef := balance_plane_coefficient K hKpos hKupper
  have hupper :
      (8 * (K ^ 2 + K + 1) ^ 2 * 13 * 25 ^ n) * 12 ^ 24 ≤
        2 ^ 2000 * (25 ^ 25) ^ q := by
    calc
      (8 * (K ^ 2 + K + 1) ^ 2 * 13 * 25 ^ n) * 12 ^ 24 ≤
          (2 ^ 1035 * ((25 ^ 25) ^ q * 25 ^ 24)) * 12 ^ 24 := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hcoef h25pow)
      _ = (2 ^ 1035 * 25 ^ 24 * 12 ^ 24) * (25 ^ 25) ^ q := by ring
      _ ≤ 2 ^ 2000 * (25 ^ 25) ^ q :=
        Nat.mul_le_mul_right _ balance_residue_cost
  have hgain := balance_many_block_gain q hqL
  have hmul :
      (8 * (K ^ 2 + K + 1) ^ 2 * 13 * 25 ^ n) * 12 ^ 24 ≤
        (2 ^ n * 13 ^ b * 12 ^ (n - b)) * 12 ^ 24 :=
    hupper.trans (hgain.trans hlower)
  have hcancel := le_of_mul_le_mul_right hmul (by positivity : 0 < 12 ^ 24)
  simpa [n, b] using hcancel

/-- Cancel the positive binomial weight after combining the weighted tail
estimate with the plane-order domination estimate.  Keeping this arithmetic
generic prevents the elaborator from repeatedly normalizing the enormous
concrete expressions used for the two fixed planes. -/
lemma balance_scale_cancel (P T n W : ℕ) (hW : 0 < W)
    (hweighted : T * W ≤ 13 * 25 ^ n)
    (hdom : 8 * P * 13 * 25 ^ n ≤ 2 ^ n * W) :
    4 * (P * (2 * T)) ≤ 2 ^ n := by
  have hmul : (4 * (P * (2 * T))) * W ≤ (2 ^ n) * W := by
    calc
      (4 * (P * (2 * T))) * W = 8 * P * (T * W) := by ring
      _ ≤ 8 * P * (13 * 25 ^ n) := Nat.mul_le_mul_left _ hweighted
      _ = 8 * P * 13 * 25 ^ n := by ring
      _ ≤ 2 ^ n * W := hdom
  exact le_of_mul_le_mul_right hmul hW

lemma fixed_balance_weighted_tail (K : ℕ)
    (hqLarge : 70000 ≤ (K + 1) / 25) :
    binomialTail (K + 1) (fixedBalance K + 1) *
        (13 ^ (fixedBalance K + 1) *
          12 ^ ((K + 1) - (fixedBalance K + 1))) ≤
      13 * 25 ^ (K + 1) := by
  have hn50 : 50 ≤ K + 1 := by
    have hdiv : 25 * ((K + 1) / 25) ≤ K + 1 := Nat.mul_div_le _ _
    omega
  have hbn : fixedBalance K + 1 ≤ K + 1 :=
    fixedBalance_succ_le K hn50
  exact binomialTail_weighted_le (K + 1) (fixedBalance K + 1) hbn
    (fixedBalance_ratio K)

lemma fixed_balance_scale (K : ℕ) (hKpos : 1 ≤ K)
    (hKupper : K ≤ 2 ^ 256) (hqLarge : 70000 ≤ (K + 1) / 25) :
    4 * ((K ^ 2 + K + 1) ^ 2 *
      (2 * binomialTail (K + 1) (fixedBalance K + 1))) ≤
        2 ^ (K + 1) := by
  apply balance_scale_cancel
    ((K ^ 2 + K + 1) ^ 2)
    (binomialTail (K + 1) (fixedBalance K + 1)) (K + 1)
    (13 ^ (fixedBalance K + 1) *
      12 ^ ((K + 1) - (fixedBalance K + 1)))
  · exact Nat.mul_pos (Nat.pow_pos (by norm_num)) (Nat.pow_pos (by norm_num))
  · exact fixed_balance_weighted_tail K hqLarge
  · simpa only [mul_assoc] using
      balance_weight_domination K hKpos hKupper hqLarge

lemma fixed_balance_cross_coefficient_pos (K : ℕ)
    (hqLarge : 70000 ≤ (K + 1) / 25) :
    0 < (K ^ 2 + K + 1) ^ 2 *
      (2 * binomialTail (K + 1) (fixedBalance K + 1)) := by
  have hn50 : 50 ≤ K + 1 := by
    have hdiv : 25 * ((K + 1) / 25) ≤ K + 1 := Nat.mul_div_le _ _
    omega
  have hbn : fixedBalance K + 1 ≤ K + 1 :=
    fixedBalance_succ_le K hn50
  have htail : 0 < binomialTail (K + 1) (fixedBalance K + 1) := by
    rw [binomialTail_eq (K + 1) (fixedBalance K + 1) hbn]
    exact Nat.add_pos_left (Nat.choose_pos hbn) _
  positivity

lemma four_mul_balanceBad_le
    (F : Type*) [Fintype F] [Field F] [DecidableEq F]
    (hKpos : 1 ≤ Fintype.card F)
    (hKupper : Fintype.card F ≤ 2 ^ 256)
    (hqLarge : 70000 ≤ (Fintype.card F + 1) / 25) :
    4 * (balanceBad F (fixedBalance (Fintype.card F))).card ≤
      Fintype.card (Labeling F) := by
  have hcross := card_balanceBad_mul_pow F (fixedBalance (Fintype.card F))
  exact four_mul_card_le_of_cross
    (fixed_balance_cross_coefficient_pos (Fintype.card F) hqLarge)
    hcross (fixed_balance_scale (Fintype.card F) hKpos hKupper hqLarge)

/-- The three bad-label sets occupy at most three quarters of all
labelings.  Consequently, every finite field satisfying the displayed
numerical hypotheses has one labeling with both properties required by the
global construction. -/
lemma exists_good_labeling
    (F : Type*) [Fintype F] [Field F] [DecidableEq F]
    (hKpos : 1 ≤ Fintype.card F)
    (hKupper : Fintype.card F ≤ 2 ^ 256)
    (hSample : fixedSample ≤ Fintype.card F)
    (hGrid : fixedGrid ≤ Fintype.card F)
    (hqLarge : 70000 ≤ (Fintype.card F + 1) / 25)
    (hC0 : fixedC0 ≤ Fintype.card F + 1)
    (hsampleForcing : 4 * fixedSample ≤ 3 * Fintype.card F)
    (hnumeric :
      16 * (fixedBalance (Fintype.card F) + fixedC0) +
          12 * ((4 * fixedC0) * (4 * fixedC0 - 1) + (fixedGrid - 1)) <
        9 * Fintype.card F) :
    ∃ a : Labeling F,
      IsGood (fixedBalance (Fintype.card F)) fixedC0 a := by
  classical
  let A := lowEnergyBadAt F fixedC0 fixedDegree fixedSample
  let B := gridBad F fixedC0 fixedGrid
  let C := balanceBad F (fixedBalance (Fintype.card F))
  let D := (A ∪ B) ∪ C
  let N := Fintype.card (Labeling F)
  have hA : 4 * A.card ≤ N := by
    simpa [A, N] using
      four_mul_lowEnergyBad_le F hKpos hKupper hSample
  have hB : 4 * B.card ≤ N := by
    simpa [B, N] using four_mul_gridBad_le F hKpos hKupper hGrid
  have hC : 4 * C.card ≤ N := by
    simpa [C, N] using four_mul_balanceBad_le F hKpos hKupper hqLarge
  have hDcard : D.card ≤ A.card + B.card + C.card := by
    calc
      D.card ≤ (A ∪ B).card + C.card := by
        simpa [D] using Finset.card_union_le (A ∪ B) C
      _ ≤ (A.card + B.card) + C.card :=
        Nat.add_le_add_right (Finset.card_union_le A B) C.card
  have hNpos : 0 < N := by
    dsimp [N]
    exact Fintype.card_pos_iff.mpr ⟨fun _ _ ↦ false⟩
  have hDlt : D.card < N := by omega
  have hDltUniv : D.card < (Finset.univ : Finset (Labeling F)).card := by
    simpa [N] using hDlt
  obtain ⟨a, _haUniv, haD⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hDltUniv
  have haParts : a ∉ A ∧ a ∉ B ∧ a ∉ C := by
    simpa [D, Finset.mem_union, not_or] using haD
  have hbalanced :
      IsBalanced (fixedBalance (Fintype.card F)) a :=
    isBalanced_of_not_mem_balanceBad (by simpa [C] using haParts.2.2)
  refine ⟨a, hbalanced, ?_⟩
  exact isPencilForcing_of_avoids_fixed_bad hC0 hsampleForcing hnumeric
    hbalanced (by simpa [A] using haParts.1)
      (by simpa [B] using haParts.2.1)

end Labels

/-! ## The two fixed projective planes -/

local instance erdos21_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

lemma erdos21_mersenne127_prime : (mersenne 127).Prime :=
  lucas_lehmer_sufficiency _ (by norm_num) (by norm_num)

local instance erdos21_prime_mersenne127 : Fact (Nat.Prime (mersenne 127)) :=
  ⟨erdos21_mersenne127_prime⟩

/-- The even-order plane used when the target uniformity is odd. -/
def EvenField := GaloisField 2 111

/-- The odd-prime-order plane used when the target uniformity is even. -/
abbrev OddField := ZMod (mersenne 127)

noncomputable local instance evenFieldField : Field EvenField :=
  inferInstanceAs (Field (GaloisField 2 111))

local instance evenFieldFinite : Finite EvenField :=
  inferInstanceAs (Finite (GaloisField 2 111))

noncomputable local instance evenFieldFintype : Fintype EvenField :=
  Fintype.ofFinite EvenField

noncomputable local instance evenFieldDecidableEq : DecidableEq EvenField :=
  Classical.decEq EvenField

noncomputable local instance oddFieldField : Field OddField :=
  inferInstanceAs (Field (ZMod (mersenne 127)))

local instance oddFieldFinite : Finite OddField :=
  inferInstanceAs (Finite (ZMod (mersenne 127)))

noncomputable local instance oddFieldFintype : Fintype OddField :=
  inferInstanceAs (Fintype (ZMod (mersenne 127)))

noncomputable local instance oddFieldDecidableEq : DecidableEq OddField :=
  Classical.decEq OddField

def evenOrder : ℕ := 2 ^ 111

def oddOrder : ℕ := 2 ^ 127 - 1

lemma card_evenField : Fintype.card EvenField = 2 ^ 111 := by
  rw [Fintype.card_eq_nat_card]
  change Nat.card (GaloisField 2 111) = 2 ^ 111
  rw [GaloisField.card]
  norm_num

lemma card_oddField : Fintype.card OddField = 2 ^ 127 - 1 := by
  rw [ZMod.card]
  rfl

lemma card_evenField_eq_evenOrder : Fintype.card EvenField = evenOrder := by
  rw [card_evenField]
  rfl

lemma card_oddField_eq_oddOrder : Fintype.card OddField = oddOrder := by
  rw [card_oddField]
  rfl

lemma evenField_good_parameters :
    1 ≤ Fintype.card EvenField ∧
    Fintype.card EvenField ≤ 2 ^ 256 ∧
    Labels.fixedSample ≤ Fintype.card EvenField ∧
    Labels.fixedGrid ≤ Fintype.card EvenField ∧
    70000 ≤ (Fintype.card EvenField + 1) / 25 ∧
    Labels.fixedC0 ≤ Fintype.card EvenField + 1 ∧
    4 * Labels.fixedSample ≤ 3 * Fintype.card EvenField ∧
    16 * (Labels.fixedBalance (Fintype.card EvenField) + Labels.fixedC0) +
        12 * ((4 * Labels.fixedC0) * (4 * Labels.fixedC0 - 1) +
          (Labels.fixedGrid - 1)) <
      9 * Fintype.card EvenField := by
  rw [card_evenField]
  norm_num [Labels.fixedSample, Labels.fixedGrid, Labels.fixedC0,
    Labels.fixedBalance]

lemma oddField_good_parameters :
    1 ≤ Fintype.card OddField ∧
    Fintype.card OddField ≤ 2 ^ 256 ∧
    Labels.fixedSample ≤ Fintype.card OddField ∧
    Labels.fixedGrid ≤ Fintype.card OddField ∧
    70000 ≤ (Fintype.card OddField + 1) / 25 ∧
    Labels.fixedC0 ≤ Fintype.card OddField + 1 ∧
    4 * Labels.fixedSample ≤ 3 * Fintype.card OddField ∧
    16 * (Labels.fixedBalance (Fintype.card OddField) + Labels.fixedC0) +
        12 * ((4 * Labels.fixedC0) * (4 * Labels.fixedC0 - 1) +
          (Labels.fixedGrid - 1)) <
      9 * Fintype.card OddField := by
  rw [card_oddField]
  norm_num [Labels.fixedSample, Labels.fixedGrid, Labels.fixedC0,
    Labels.fixedBalance]

lemma exists_evenField_goodLabeling :
    ∃ a : Labels.Labeling EvenField,
      Labels.IsGood (Labels.fixedBalance (Fintype.card EvenField))
        Labels.fixedC0 a := by
  rcases evenField_good_parameters with
    ⟨hpos, hupper, hsample, hgrid, hq, hC0, hforce, hnumeric⟩
  exact Labels.exists_good_labeling EvenField hpos hupper hsample hgrid hq
    hC0 hforce hnumeric

lemma exists_oddField_goodLabeling :
    ∃ a : Labels.Labeling OddField,
      Labels.IsGood (Labels.fixedBalance (Fintype.card OddField))
        Labels.fixedC0 a := by
  rcases oddField_good_parameters with
    ⟨hpos, hupper, hsample, hgrid, hq, hC0, hforce, hnumeric⟩
  exact Labels.exists_good_labeling OddField hpos hupper hsample hgrid hq
    hC0 hforce hnumeric

/-! ## The two matching partitions supplied by an expander -/

namespace Expander

/-- The union of `d` bipartite perfect matchings, represented by their
permutations.  Its dual vertex set is `Fin d × Fin t`. -/
structure System (d t : ℕ) where
  perm : Fin d → Equiv.Perm (Fin t)

namespace System

variable {d t : ℕ}

/-- Blocks in the first matching partition. -/
def leftBlock (D : System d t) (x : Fin t) : Finset (Fin d × Fin t) :=
  Finset.univ.filter fun v ↦ v.2 = x

/-- Blocks in the second matching partition. -/
def rightBlock (D : System d t) (y : Fin t) : Finset (Fin d × Fin t) :=
  Finset.univ.filter fun v ↦ D.perm v.1 v.2 = y

@[simp] lemma mem_leftBlock_iff (D : System d t) (v : Fin d × Fin t)
    (x : Fin t) : v ∈ D.leftBlock x ↔ v.2 = x := by
  simp [leftBlock]

@[simp] lemma mem_rightBlock_iff (D : System d t) (v : Fin d × Fin t)
    (y : Fin t) : v ∈ D.rightBlock y ↔ D.perm v.1 v.2 = y := by
  simp [rightBlock]

/-- Neighbours of a set in the first part. -/
def rightNeighbors (D : System d t) (S : Finset (Fin t)) : Finset (Fin t) :=
  Finset.univ.filter fun y ↦ ∃ j : Fin d, ∃ x ∈ S, D.perm j x = y

/-- Neighbours of a set in the second part. -/
def leftNeighbors (D : System d t) (S : Finset (Fin t)) : Finset (Fin t) :=
  Finset.univ.filter fun x ↦ ∃ j : Fin d, ∃ y ∈ S, D.perm j x = y

@[simp] lemma mem_rightNeighbors_iff (D : System d t)
    (S : Finset (Fin t)) (y : Fin t) :
    y ∈ D.rightNeighbors S ↔ ∃ j : Fin d, ∃ x ∈ S, D.perm j x = y := by
  simp [rightNeighbors]

@[simp] lemma mem_leftNeighbors_iff (D : System d t)
    (S : Finset (Fin t)) (x : Fin t) :
    x ∈ D.leftNeighbors S ↔ ∃ j : Fin d, ∃ y ∈ S, D.perm j x = y := by
  simp [leftNeighbors]

/-- The two expansion estimates used in the waste argument, written with
integer coefficients. -/
def HasKahnExpansion (D : System d t) : Prop :=
  (∀ S : Finset (Fin t), 2 * S.card ≤ t →
      11 * S.card ≤ 10 * (D.rightNeighbors S).card) ∧
  (∀ S : Finset (Fin t), 10 * S.card ≤ t →
      3 * S.card ≤ (D.rightNeighbors S).card) ∧
  (∀ S : Finset (Fin t), 2 * S.card ≤ t →
      11 * S.card ≤ 10 * (D.leftNeighbors S).card) ∧
  (∀ S : Finset (Fin t), 10 * S.card ≤ t →
      3 * S.card ≤ (D.leftNeighbors S).card)

/-- A choice of original blocks from both matching partitions covers every
vertex of the dual bipartite system. -/
def CoversByIndices (D : System d t) (L R : Finset (Fin t)) : Prop :=
  ∀ v : Fin d × Fin t, v.2 ∈ L ∨ D.perm v.1 v.2 ∈ R

lemma rightNeighbors_subset_of_covers (D : System d t)
    {L R S : Finset (Fin t)} (hcover : D.CoversByIndices L R)
    (hS : S ⊆ Finset.univ \ L) : D.rightNeighbors S ⊆ R := by
  intro y hy
  obtain ⟨j, x, hxS, hxy⟩ := (D.mem_rightNeighbors_iff S y).mp hy
  rcases hcover (j, x) with hxL | hyR
  · exact (Finset.mem_sdiff.mp (hS hxS)).2 hxL |>.elim
  · simpa [hxy] using hyR

lemma leftNeighbors_subset_of_covers (D : System d t)
    {L R S : Finset (Fin t)} (hcover : D.CoversByIndices L R)
    (hS : S ⊆ Finset.univ \ R) : D.leftNeighbors S ⊆ L := by
  intro x hx
  obtain ⟨j, y, hyS, hxy⟩ := (D.mem_leftNeighbors_iff S x).mp hx
  rcases hcover (j, x) with hxL | hyR
  · exact hxL
  · exact (Finset.mem_sdiff.mp (hS hyS)).2 (by simpa [hxy] using hyR) |>.elim

lemma choose_omitted_indices {U : Finset (Fin t)} {a : ℕ}
    (ha : a ≤ t) (hcard : U.card ≤ t - a) :
    ∃ S : Finset (Fin t), S ⊆ Finset.univ \ U ∧ S.card = a := by
  have hcomp : a ≤ (Finset.univ \ U).card := by
    rw [Finset.card_sdiff]
    simp only [Finset.card_univ, Fintype.card_fin, Finset.inter_univ]
    omega
  exact Finset.exists_subset_card_eq hcomp

/-- Expansion forces many original blocks on the opposite side whenever the
chosen blocks on one side fit into at most `t-a` indices. -/
lemma opposite_original_blocks_of_expansion (D : System d t)
    (hexp : D.HasKahnExpansion) {L R : Finset (Fin t)}
    (hcover : D.CoversByIndices L R) {a : ℕ} (ha : a ≤ t)
    (hL : L.card ≤ t - a) :
    (2 * a ≤ t → 11 * a ≤ 10 * R.card) ∧
      (10 * a ≤ t → 3 * a ≤ R.card) := by
  obtain ⟨S, hS, hScard⟩ := choose_omitted_indices ha hL
  constructor
  · intro ha
    calc
      11 * a = 11 * S.card := by rw [hScard]
      _ ≤ 10 * (D.rightNeighbors S).card := hexp.1 S (by simpa [hScard] using ha)
      _ ≤ 10 * R.card := Nat.mul_le_mul_left 10
        (Finset.card_le_card (D.rightNeighbors_subset_of_covers hcover hS))
  · intro ha
    calc
      3 * a = 3 * S.card := by rw [hScard]
      _ ≤ (D.rightNeighbors S).card := hexp.2.1 S (by simpa [hScard] using ha)
      _ ≤ R.card := Finset.card_le_card
        (D.rightNeighbors_subset_of_covers hcover hS)

lemma opposite_original_blocks_of_expansion_symm (D : System d t)
    (hexp : D.HasKahnExpansion) {L R : Finset (Fin t)}
    (hcover : D.CoversByIndices L R) {a : ℕ} (ha : a ≤ t)
    (hR : R.card ≤ t - a) :
    (2 * a ≤ t → 11 * a ≤ 10 * L.card) ∧
      (10 * a ≤ t → 3 * a ≤ L.card) := by
  obtain ⟨S, hS, hScard⟩ := choose_omitted_indices ha hR
  constructor
  · intro ha
    calc
      11 * a = 11 * S.card := by rw [hScard]
      _ ≤ 10 * (D.leftNeighbors S).card := hexp.2.2.1 S
        (by simpa [hScard] using ha)
      _ ≤ 10 * L.card := Nat.mul_le_mul_left 10
        (Finset.card_le_card (D.leftNeighbors_subset_of_covers hcover hS))
  · intro ha
    calc
      3 * a = 3 * S.card := by rw [hScard]
      _ ≤ (D.leftNeighbors S).card := hexp.2.2.2 S
        (by simpa [hScard] using ha)
      _ ≤ L.card := Finset.card_le_card
        (D.leftNeighbors_subset_of_covers hcover hS)

end System

end Expander

/-! ## Finite counting for the expander input -/

namespace Expander.Random

open Equiv

variable {t : ℕ}

/-- Permutations which extend one prescribed map on a finite subset. -/
def ExtensionFiber (S : Finset (Fin t)) (r : S → Fin t) :=
  {p : Equiv.Perm (Fin t) // ∀ x : S, p x = r x}

noncomputable instance (S : Finset (Fin t)) (r : S → Fin t) :
    Fintype (ExtensionFiber S r) := by
  letI : Finite (ExtensionFiber S r) :=
    Finite.of_injective (fun p : ExtensionFiber S r ↦ p.1) Subtype.coe_injective
  exact Fintype.ofFinite _

/-- Two extensions of the same prescribed map differ by a permutation of
the complement.  This is the factorial cancellation behind the elementary
random-permutation estimate. -/
lemma extensionFiber_card_le (S : Finset (Fin t)) (r : S → Fin t) :
    Fintype.card (ExtensionFiber S r) ≤ Nat.factorial (t - S.card) := by
  classical
  by_cases hne : Nonempty (ExtensionFiber S r)
  · let p₀ : ExtensionFiber S r := Classical.choice hne
    let fixedOnS :=
      {g : Equiv.Perm (Fin t) // ∀ x : Fin t, x ∈ S → g x = x}
    let encode : ExtensionFiber S r → fixedOnS := fun p ↦
      ⟨p.1.trans p₀.1.symm, by
        intro x hx
        apply p₀.1.injective
        simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
        exact (p.2 ⟨x, hx⟩).trans (p₀.2 ⟨x, hx⟩).symm⟩
    have hencode : Function.Injective encode := by
      intro p q hpq
      apply Subtype.ext
      apply Equiv.ext
      intro x
      have hval := congrArg (fun g : fixedOnS ↦ p₀.1 (g.1 x)) hpq
      simpa [encode] using hval
    calc
      Fintype.card (ExtensionFiber S r) ≤ Fintype.card fixedOnS :=
        Fintype.card_le_of_injective encode hencode
      _ = Fintype.card (Equiv.Perm {x : Fin t // x ∉ S}) := by
        let e := Equiv.Perm.subtypeEquivSubtypePerm (fun x : Fin t ↦ x ∉ S)
        simpa [fixedOnS] using (Fintype.card_congr e).symm
      _ = Nat.factorial (t - S.card) := by
        rw [Fintype.card_perm]
        congr 1
        simp
  · haveI : IsEmpty (ExtensionFiber S r) := not_nonempty_iff.mp hne
    simp

/-- Permutations carrying every member of `S` into `T`. -/
def RestrictedPerm (S T : Finset (Fin t)) :=
  {p : Equiv.Perm (Fin t) // ∀ x : Fin t, x ∈ S → p x ∈ T}

noncomputable instance (S T : Finset (Fin t)) : Fintype (RestrictedPerm S T) := by
  letI : Finite (RestrictedPerm S T) :=
    Finite.of_injective (fun p : RestrictedPerm S T ↦ p.1) Subtype.coe_injective
  exact Fintype.ofFinite _

/-- Restrict a constrained permutation to a function between the two finite
subsets. -/
def restriction (S T : Finset (Fin t)) (p : RestrictedPerm S T) : S ↪ T where
  toFun x := ⟨p.1 x, p.2 x x.2⟩
  inj' x y h := Subtype.ext (p.1.injective (congrArg Subtype.val h))

/-- At most `|T|^|S| (t-|S|)!` permutations map `S` into `T`. -/
lemma restrictedPerm_card_le (S T : Finset (Fin t)) :
    Fintype.card (RestrictedPerm S T) ≤
      T.card.descFactorial S.card * Nat.factorial (t - S.card) := by
  classical
  have hfiber : ∀ r : S ↪ T,
      ((Finset.univ : Finset (RestrictedPerm S T)).filter
        fun p ↦ restriction S T p = r).card ≤ Nat.factorial (t - S.card) := by
    intro r
    let A := (Finset.univ : Finset (RestrictedPerm S T)).filter
      fun p ↦ restriction S T p = r
    let e : A ↪ ExtensionFiber S (fun x ↦ (r x).1) :=
      { toFun := fun p ↦ ⟨p.1.1, by
        intro x
        have hp : restriction S T p.1 = r := by
          simpa [A] using (Finset.mem_filter.mp p.2).2
        exact congrArg Subtype.val (congrFun (congrArg DFunLike.coe hp) x)⟩,
        inj' := by
          intro p q hpq
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg
            (fun z : ExtensionFiber S (fun x ↦ (r x).1) ↦ z.1) hpq }
    have hcard := Fintype.card_le_of_injective e e.injective
    change A.card ≤ Nat.factorial (t - S.card)
    rw [← Fintype.card_coe]
    exact hcard.trans (extensionFiber_card_le S (fun x ↦ (r x).1))
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (RestrictedPerm S T)))
    (t := (Finset.univ : Finset (S ↪ T)))
    (f := restriction S T) (by simp)]
  calc
    ∑ r : S ↪ T, ((Finset.univ : Finset (RestrictedPerm S T)).filter
        fun p ↦ restriction S T p = r).card
      ≤ ∑ _r : S ↪ T, Nat.factorial (t - S.card) := by
        exact Finset.sum_le_sum fun r _ ↦ hfiber r
    _ = T.card.descFactorial S.card * Nat.factorial (t - S.card) := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
        Fintype.card_embedding_eq, Fintype.card_coe]

/-- Forget the wrapper around a family of permutations. -/
def systemEquivFamily (d t : ℕ) :
    Expander.System d t ≃ (Fin d → Equiv.Perm (Fin t)) where
  toFun D := D.perm
  invFun p := ⟨p⟩
  left_inv D := by cases D; rfl
  right_inv _ := rfl

noncomputable instance (d t : ℕ) : Fintype (Expander.System d t) :=
  Fintype.ofEquiv (Fin d → Equiv.Perm (Fin t)) (systemEquivFamily d t).symm

lemma card_system (d t : ℕ) :
    Fintype.card (Expander.System d t) = Nat.factorial t ^ d := by
  rw [Fintype.card_congr (systemEquivFamily d t), Fintype.card_fun,
    Fintype.card_fin, Fintype.card_perm, Fintype.card_fin]

/-- Systems for which every matching sends `S` into `T`. -/
def RestrictedSystem (d : ℕ) (S T : Finset (Fin t)) :=
  {D : Expander.System d t //
    ∀ j : Fin d, ∀ x : Fin t, x ∈ S → D.perm j x ∈ T}

noncomputable instance (d : ℕ) (S T : Finset (Fin t)) :
    Fintype (RestrictedSystem d S T) := by
  letI : Finite (RestrictedSystem d S T) :=
    Finite.of_injective (fun D : RestrictedSystem d S T ↦ D.1) Subtype.coe_injective
  exact Fintype.ofFinite _

/-- Constraining a whole system is the independent product of the
single-permutation constraints. -/
def restrictedSystemEquiv (d : ℕ) (S T : Finset (Fin t)) :
    RestrictedSystem d S T ≃ (Fin d → RestrictedPerm S T) where
  toFun D j := ⟨D.1.perm j, D.2 j⟩
  invFun p := ⟨⟨fun j ↦ (p j).1⟩, fun j ↦ (p j).2⟩
  left_inv D := by
    apply Subtype.ext
    cases D.1
    rfl
  right_inv p := by
    funext j
    apply Subtype.ext
    rfl

lemma restrictedSystem_card_le (d : ℕ) (S T : Finset (Fin t)) :
    Fintype.card (RestrictedSystem d S T) ≤
      (T.card.descFactorial S.card * Nat.factorial (t - S.card)) ^ d := by
  rw [Fintype.card_congr (restrictedSystemEquiv d S T), Fintype.card_fun,
    Fintype.card_fin]
  exact Nat.pow_le_pow_left (restrictedPerm_card_le S T) d

/-- Sampling without replacement is at least as concentrated as independent
sampling: `(u)_s/(t)_s ≤ (u/t)^s`.  The cross-multiplied natural-number
form avoids every division-by-zero side condition. -/
lemma descFactorial_mul_pow_le (u t s : ℕ) (hut : u ≤ t) :
    u.descFactorial s * t ^ s ≤ t.descFactorial s * u ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
      by_cases hsu : s + 1 ≤ u
      · have hst : s + 1 ≤ t := hsu.trans hut
        have hcoef : (u - s) * t ≤ (t - s) * u := by
          calc
            (u - s) * t = u * t - s * t := by rw [Nat.sub_mul]
            _ ≤ t * u - s * u := by
              rw [Nat.mul_comm u t]
              exact Nat.sub_le_sub_left (Nat.mul_le_mul_left s hut) _
            _ = (t - s) * u := by rw [Nat.sub_mul]
        rw [Nat.descFactorial_succ, Nat.descFactorial_succ,
          pow_succ, pow_succ]
        calc
          (u - s) * u.descFactorial s * (t ^ s * t) =
              ((u - s) * t) * (u.descFactorial s * t ^ s) := by ac_rfl
          _ ≤ ((t - s) * u) * (t.descFactorial s * u ^ s) :=
            Nat.mul_le_mul hcoef ih
          _ = (t - s) * t.descFactorial s * (u ^ s * u) := by ac_rfl
      · have hus : u < s + 1 := by omega
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr hus, zero_mul]
        exact Nat.zero_le _

/-- A deliberately coarse Stirling consequence.  The constant `3` is
chosen so that the ensuing finite union bound can be discharged using only
integer arithmetic. -/
lemma pow_div_three_le_factorial (k : ℕ) :
    ((k : ℝ) / 3) ^ k ≤ (Nat.factorial k : ℝ) := by
  by_cases hk : k = 0
  · simp [hk]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk)
  have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hbase : (k : ℝ) / 3 ≤ (k : ℝ) / Real.exp 1 := by
    exact div_le_div_of_nonneg_left hkpos.le (Real.exp_pos 1) hexp.le
  have hsqrt : (1 : ℝ) ≤ √(2 * Real.pi * k) := by
    rw [Real.one_le_sqrt]
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hkone : (1 : ℝ) ≤ k := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
    calc
      (1 : ℝ) ≤ 2 * 3 * 1 := by norm_num
      _ ≤ 2 * Real.pi * 1 := by nlinarith
      _ ≤ 2 * Real.pi * k :=
        mul_le_mul_of_nonneg_left hkone (by positivity)
  calc
    ((k : ℝ) / 3) ^ k ≤ ((k : ℝ) / Real.exp 1) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    _ ≤ √(2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k := by
      exact le_mul_of_one_le_left (by positivity) hsqrt
    _ ≤ (Nat.factorial k : ℝ) := Stirling.le_factorial_stirling k

/-- Entropy-free binomial estimate sufficient for the small-set union bound. -/
lemma choose_le_three_mul_div_pow (n k : ℕ) (hk : 0 < k) :
    (n.choose k : ℝ) ≤ ((3 : ℝ) * n / k) ^ k := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hfact := pow_div_three_le_factorial k
  have hchoose : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (Nat.factorial k : ℝ) :=
    Nat.choose_le_pow_div k n
  calc
    (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (Nat.factorial k : ℝ) := hchoose
    _ ≤ (n : ℝ) ^ k / (((k : ℝ) / 3) ^ k) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfact
    _ = ((3 : ℝ) * n / k) ^ k := by
      rw [← div_pow]
      congr 1
      field_simp

/-- The finite set represented by `RestrictedSystem`. -/
noncomputable def mappedInto (d : ℕ) (S T : Finset (Fin t)) :
    Finset (Expander.System d t) :=
  Finset.univ.filter fun D ↦
    ∀ j : Fin d, ∀ x : Fin t, x ∈ S → D.perm j x ∈ T

@[simp] lemma mem_mappedInto_iff (d : ℕ) (S T : Finset (Fin t))
    (D : Expander.System d t) :
    D ∈ mappedInto d S T ↔
      ∀ j : Fin d, ∀ x : Fin t, x ∈ S → D.perm j x ∈ T := by
  simp [mappedInto]

lemma card_mappedInto (d : ℕ) (S T : Finset (Fin t)) :
    (mappedInto d S T).card = Fintype.card (RestrictedSystem d S T) := by
  classical
  let P : Expander.System d t → Prop := fun D ↦
    ∀ j : Fin d, ∀ x : Fin t, x ∈ S → D.perm j x ∈ T
  let e : {D : Expander.System d t // P D} ≃ RestrictedSystem d S T :=
    { toFun := fun D ↦ ⟨D.1, D.2⟩
      invFun := fun D ↦ ⟨D.1, D.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    (mappedInto d S T).card = Fintype.card {D : Expander.System d t // P D} := by
      simpa only [mappedInto, P] using
        (Fintype.card_subtype P).symm
    _ = Fintype.card (RestrictedSystem d S T) := Fintype.card_congr e

/-- A cardinality bound depending only on the sizes of the constrained
domain and target. -/
def restrictionBound (d t s u : ℕ) : ℕ :=
  (u.descFactorial s * Nat.factorial (t - s)) ^ d

lemma card_mappedInto_le_restrictionBound (d : ℕ)
    (S T : Finset (Fin t)) :
    (mappedInto d S T).card ≤ restrictionBound d t S.card T.card := by
  rw [card_mappedInto]
  exact restrictedSystem_card_le d S T

lemma restrictionBound_cross_bound (d t s u : ℕ) (hsu : s ≤ u)
    (hut : u ≤ t) :
    restrictionBound d t s u * t ^ (d * s) ≤
      Fintype.card (Expander.System d t) * u ^ (d * s) := by
  have hst : s ≤ t := hsu.trans hut
  have hratio := descFactorial_mul_pow_le u t s hut
  have hfactor :
      u.descFactorial s * Nat.factorial (t - s) * t ^ s ≤
        (t.descFactorial s * Nat.factorial (t - s)) * u ^ s := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_le_mul_right (Nat.factorial (t - s)) hratio
  calc
    restrictionBound d t s u * t ^ (d * s) =
        (u.descFactorial s * Nat.factorial (t - s)) ^ d *
          (t ^ s) ^ d := by
      simp only [restrictionBound]
      congr 1
      rw [← pow_mul, Nat.mul_comm d s]
    _ = ((u.descFactorial s * Nat.factorial (t - s)) * t ^ s) ^ d :=
      (mul_pow _ _ _).symm
    _ ≤ ((t.descFactorial s * Nat.factorial (t - s)) * u ^ s) ^ d :=
      Nat.pow_le_pow_left hfactor d
    _ = (t.descFactorial s * Nat.factorial (t - s)) ^ d *
          (u ^ s) ^ d := by rw [mul_pow]
    _ = Nat.factorial t ^ d * u ^ (d * s) := by
      congr 1
      · simpa [mul_comm] using congrArg (fun z ↦ z ^ d)
          (Nat.factorial_mul_descFactorial hst)
      · rw [← pow_mul, Nat.mul_comm s d]
    _ = Fintype.card (Expander.System d t) * u ^ (d * s) := by
      rw [card_system]

/-- For one small-set certificate, the product of the number of choices of
the two sets and the number of compatible degree-100 systems is geometrically
smaller than the total number of systems. -/
lemma small_certificate_bound {s : ℕ} (hs : 0 < s) (hst : 10 * s ≤ t) :
    ((t.choose s * t.choose (3 * s) *
        restrictionBound 100 t s (3 * s) : ℕ) : ℝ) ≤
      (Fintype.card (Expander.System 100 t) : ℝ) * (1 / 4 : ℝ) ^ s := by
  have ht : 0 < t := by omega
  have hsreal : (0 : ℝ) < s := by exact_mod_cast hs
  have htreal : (0 : ℝ) < t := by exact_mod_cast ht
  have hcrossNat := restrictionBound_cross_bound 100 t s (3 * s) (by omega)
    (by omega)
  have hcross :
      (restrictionBound 100 t s (3 * s) : ℝ) * (t : ℝ) ^ (100 * s) ≤
        (Fintype.card (Expander.System 100 t) : ℝ) *
          (3 * s : ℝ) ^ (100 * s) := by
    exact_mod_cast hcrossNat
  have hmap : (restrictionBound 100 t s (3 * s) : ℝ) ≤
      (Fintype.card (Expander.System 100 t) : ℝ) *
        (((3 : ℝ) * s / t) ^ 100) ^ s := by
    rw [← pow_mul]
    calc
      (restrictionBound 100 t s (3 * s) : ℝ) ≤
          ((Fintype.card (Expander.System 100 t) : ℝ) *
              ((3 : ℝ) * s) ^ (100 * s)) / (t : ℝ) ^ (100 * s) := by
        exact (le_div_iff₀ (by positivity)).2 (by simpa using hcross)
      _ = (Fintype.card (Expander.System 100 t) : ℝ) *
          (((3 : ℝ) * s / t) ^ (100 * s)) := by
        rw [div_pow]
        ring
  have hchooseS := choose_le_three_mul_div_pow t s hs
  have hchooseT := choose_le_three_mul_div_pow t (3 * s) (by omega)
  have hchooseT' : (t.choose (3 * s) : ℝ) ≤
      (((t : ℝ) / s) ^ 3) ^ s := by
    calc
      (t.choose (3 * s) : ℝ) ≤
          ((3 : ℝ) * t / (3 * s)) ^ (3 * s) := by
            simpa only [Nat.cast_mul, Nat.cast_ofNat] using hchooseT
      _ = (((t : ℝ) / s) ^ 3) ^ s := by
        rw [pow_mul]
        congr 1
        field_simp
  have hratio : (s : ℝ) / t ≤ 1 / 10 := by
    apply (div_le_iff₀ htreal).2
    have hst' : (10 : ℝ) * s ≤ t := by exact_mod_cast hst
    nlinarith
  have hbase :
      ((3 : ℝ) * t / s) * ((t : ℝ) / s) ^ 3 *
          (((3 : ℝ) * s / t) ^ 100) ≤ 1 / 4 := by
    have heq :
        ((3 : ℝ) * t / s) * ((t : ℝ) / s) ^ 3 *
            (((3 : ℝ) * s / t) ^ 100) =
          (3 : ℝ) ^ 101 * ((s : ℝ) / t) ^ 96 := by
      field_simp
    rw [heq]
    calc
      (3 : ℝ) ^ 101 * ((s : ℝ) / t) ^ 96 ≤
          (3 : ℝ) ^ 101 * (1 / 10 : ℝ) ^ 96 := by
        gcongr
      _ ≤ 1 / 4 := by norm_num
  push_cast
  calc
    (t.choose s : ℝ) * t.choose (3 * s) * restrictionBound 100 t s (3 * s) ≤
        (((3 : ℝ) * t / s) ^ s) *
          ((((t : ℝ) / s) ^ 3) ^ s) *
          ((Fintype.card (Expander.System 100 t) : ℝ) *
            ((((3 : ℝ) * s / t) ^ 100) ^ s)) := by
      gcongr
    _ = (Fintype.card (Expander.System 100 t) : ℝ) *
          (((3 : ℝ) * t / s) * ((t : ℝ) / s) ^ 3 *
            (((3 : ℝ) * s / t) ^ 100) : ℝ) ^ s := by
      rw [mul_pow, mul_pow]
      ring
    _ ≤ (Fintype.card (Expander.System 100 t) : ℝ) * (1 / 4 : ℝ) ^ s := by
      gcongr

/-- Systems admitting a fixed-cardinality certificate for failure of the
factor-three right expansion. -/
noncomputable def smallBadAt (t s : ℕ) : Finset (Expander.System 100 t) :=
  (Finset.univ.powersetCard s).biUnion fun S ↦
    (Finset.univ.powersetCard (3 * s)).biUnion fun T ↦
      mappedInto 100 S T

lemma card_smallBadAt_le (t s : ℕ) :
    (smallBadAt t s).card ≤
      t.choose s * t.choose (3 * s) * restrictionBound 100 t s (3 * s) := by
  classical
  calc
    (smallBadAt t s).card ≤
        (Finset.univ.powersetCard s).card *
          (t.choose (3 * s) * restrictionBound 100 t s (3 * s)) := by
      apply Finset.card_biUnion_le_card_mul
      intro S hS
      have hScard := (Finset.mem_powersetCard.mp hS).2
      calc
        ((Finset.univ.powersetCard (3 * s)).biUnion fun T ↦
            mappedInto 100 S T).card ≤
            (Finset.univ.powersetCard (3 * s)).card *
              restrictionBound 100 t s (3 * s) := by
          apply Finset.card_biUnion_le_card_mul
          intro T hT
          have hTcard := (Finset.mem_powersetCard.mp hT).2
          simpa [hScard, hTcard] using
            card_mappedInto_le_restrictionBound 100 S T
        _ = t.choose (3 * s) * restrictionBound 100 t s (3 * s) := by
          simp
    _ = t.choose s * t.choose (3 * s) *
          restrictionBound 100 t s (3 * s) := by simp [mul_assoc]

lemma card_smallBadAt_real_le {t s : ℕ} (hs : 0 < s)
    (hst : 10 * s ≤ t) :
    ((smallBadAt t s).card : ℝ) ≤
      (Fintype.card (Expander.System 100 t) : ℝ) * (1 / 4 : ℝ) ^ s := by
  calc
    ((smallBadAt t s).card : ℝ) ≤
        ((t.choose s * t.choose (3 * s) *
          restrictionBound 100 t s (3 * s) : ℕ) : ℝ) := by
      exact_mod_cast card_smallBadAt_le t s
    _ ≤ (Fintype.card (Expander.System 100 t) : ℝ) * (1 / 4 : ℝ) ^ s :=
      small_certificate_bound hs hst

/-- All factor-three right-expansion certificates, indexed by `s-1` so the
geometric sum starts with exponent one. -/
noncomputable def smallBad (t : ℕ) : Finset (Expander.System 100 t) :=
  ((Finset.range t).filter fun i ↦ 10 * (i + 1) ≤ t).biUnion fun i ↦
    smallBadAt t (i + 1)

lemma geometric_quarter_shifted (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 4 : ℝ) ^ (i + 1)) ≤ 1 / 3 := by
  have hpow : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
  rw [show (∑ i ∈ Finset.range n, (1 / 4 : ℝ) ^ (i + 1)) =
      (1 / 4 : ℝ) * ∑ i ∈ Finset.range n, (1 / 4 : ℝ) ^ i by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ']]
  rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
  have heq : (1 / 4 : ℝ) * (((1 / 4 : ℝ) ^ n - 1) / (1 / 4 - 1)) =
      (1 - (1 / 4 : ℝ) ^ n) / 3 := by
    field_simp
    ring
  rw [heq]
  nlinarith

lemma card_smallBad_real_le (t : ℕ) :
    ((smallBad t).card : ℝ) ≤
      (Fintype.card (Expander.System 100 t) : ℝ) / 3 := by
  classical
  let I := (Finset.range t).filter fun i ↦ 10 * (i + 1) ≤ t
  have hcard : (smallBad t).card ≤ ∑ i ∈ I, (smallBadAt t (i + 1)).card := by
    exact Finset.card_biUnion_le
  have hterm : ∀ i ∈ I,
      ((smallBadAt t (i + 1)).card : ℝ) ≤
        (Fintype.card (Expander.System 100 t) : ℝ) *
          (1 / 4 : ℝ) ^ (i + 1) := by
    intro i hi
    exact card_smallBadAt_real_le (by omega)
      (Finset.mem_filter.mp hi).2
  have hI : I ⊆ Finset.range t := by
    dsimp [I]
    exact Finset.filter_subset _ _
  calc
    ((smallBad t).card : ℝ) ≤
        ∑ i ∈ I, ((smallBadAt t (i + 1)).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ i ∈ I, (Fintype.card (Expander.System 100 t) : ℝ) *
          (1 / 4 : ℝ) ^ (i + 1) := Finset.sum_le_sum hterm
    _ = (Fintype.card (Expander.System 100 t) : ℝ) *
          ∑ i ∈ I, (1 / 4 : ℝ) ^ (i + 1) := by
      rw [Finset.mul_sum]
    _ ≤ (Fintype.card (Expander.System 100 t) : ℝ) *
          ∑ i ∈ Finset.range t, (1 / 4 : ℝ) ^ (i + 1) := by
      gcongr
    _ ≤ (Fintype.card (Expander.System 100 t) : ℝ) * (1 / 3 : ℝ) := by
      gcongr
      exact geometric_quarter_shifted t
    _ = (Fintype.card (Expander.System 100 t) : ℝ) / 3 := by ring

/-- A medium certificate uses a target of size `⌊6s/5⌋`.  The factor `6/5`
is comfortably above the forbidden `11/10` neighbourhood size and at most
`3/5` of the opposite part when `s ≤ t/2`. -/
lemma medium_certificate_bound {t s : ℕ} (ht : 0 < t)
    (hsmall : 2 * s ≤ t) (hmedium : t < 10 * s) :
    ((t.choose s * t.choose (6 * s / 5) *
        restrictionBound 100 t s (6 * s / 5) : ℕ) : ℝ) ≤
      (Fintype.card (Expander.System 100 t) : ℝ) * (1 / 32 : ℝ) ^ t := by
  have hs : 0 < s := by omega
  have hsreal : (0 : ℝ) < s := by exact_mod_cast hs
  have htreal : (0 : ℝ) < t := by exact_mod_cast ht
  have hsu : s ≤ 6 * s / 5 := by omega
  have hut : 6 * s / 5 ≤ t := by omega
  have hcrossNat := restrictionBound_cross_bound 100 t s (6 * s / 5) hsu hut
  have hcross :
      (restrictionBound 100 t s (6 * s / 5) : ℝ) *
          (t : ℝ) ^ (100 * s) ≤
        (Fintype.card (Expander.System 100 t) : ℝ) *
          (6 * s / 5 : ℕ) ^ (100 * s) := by
    exact_mod_cast hcrossNat
  have hmap : (restrictionBound 100 t s (6 * s / 5) : ℝ) ≤
      (Fintype.card (Expander.System 100 t) : ℝ) *
        ((((6 * s / 5 : ℕ) : ℝ) / t) ^ (100 * s)) := by
    calc
      (restrictionBound 100 t s (6 * s / 5) : ℝ) ≤
          ((Fintype.card (Expander.System 100 t) : ℝ) *
            ((6 * s / 5 : ℕ) : ℝ) ^ (100 * s)) /
              (t : ℝ) ^ (100 * s) := by
        exact (le_div_iff₀ (by positivity)).2 (by simpa using hcross)
      _ = (Fintype.card (Expander.System 100 t) : ℝ) *
          ((((6 * s / 5 : ℕ) : ℝ) / t) ^ (100 * s)) := by
        rw [div_pow]
        ring
  have huratio : (((6 * s / 5 : ℕ) : ℝ) / t) ≤ 3 / 5 := by
    have hu : 5 * (6 * s / 5) ≤ 3 * t := by omega
    apply (div_le_iff₀ htreal).2
    have hu' : (5 : ℝ) * (6 * s / 5 : ℕ) ≤ 3 * t := by
      exact_mod_cast hu
    nlinarith
  have hexp : 10 * t ≤ 100 * s := by omega
  have hratioPow :
      ((((6 * s / 5 : ℕ) : ℝ) / t) ^ (100 * s)) ≤
        (3 / 5 : ℝ) ^ (10 * t) := by
    calc
      ((((6 * s / 5 : ℕ) : ℝ) / t) ^ (100 * s)) ≤
          (3 / 5 : ℝ) ^ (100 * s) := by gcongr
      _ ≤ (3 / 5 : ℝ) ^ (10 * t) := by
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
  have hchooseS : (t.choose s : ℝ) ≤ (2 : ℝ) ^ t := by
    exact_mod_cast Nat.choose_le_two_pow t s
  have hchooseU : (t.choose (6 * s / 5) : ℝ) ≤ (2 : ℝ) ^ t := by
    exact_mod_cast Nat.choose_le_two_pow t (6 * s / 5)
  push_cast
  calc
    (t.choose s : ℝ) * t.choose (6 * s / 5) *
        restrictionBound 100 t s (6 * s / 5) ≤
      (2 : ℝ) ^ t * (2 : ℝ) ^ t *
        ((Fintype.card (Expander.System 100 t) : ℝ) *
          (((6 * s / 5 : ℕ) : ℝ) / t) ^ (100 * s)) := by
      gcongr
    _ ≤ (2 : ℝ) ^ t * (2 : ℝ) ^ t *
        ((Fintype.card (Expander.System 100 t) : ℝ) *
          (3 / 5 : ℝ) ^ (10 * t)) := by gcongr
    _ = (Fintype.card (Expander.System 100 t) : ℝ) *
        ((4 : ℝ) * (3 / 5 : ℝ) ^ 10) ^ t := by
      rw [pow_mul]
      have htwo : (2 : ℝ) ^ t * 2 ^ t = 4 ^ t := by
        rw [← mul_pow]
        norm_num
      calc
        (2 : ℝ) ^ t * 2 ^ t *
            ((Fintype.card (Expander.System 100 t) : ℝ) *
              ((3 / 5 : ℝ) ^ 10) ^ t) =
            (Fintype.card (Expander.System 100 t) : ℝ) *
              (((2 : ℝ) ^ t * 2 ^ t) * ((3 / 5 : ℝ) ^ 10) ^ t) := by ring
        _ = (Fintype.card (Expander.System 100 t) : ℝ) *
              ((4 : ℝ) ^ t * ((3 / 5 : ℝ) ^ 10) ^ t) := by rw [htwo]
        _ = (Fintype.card (Expander.System 100 t) : ℝ) *
            ((4 : ℝ) * (3 / 5 : ℝ) ^ 10) ^ t := by
          rw [mul_pow]
    _ ≤ (Fintype.card (Expander.System 100 t) : ℝ) * (1 / 32 : ℝ) ^ t := by
      gcongr
      norm_num

noncomputable def mediumBadAt (t s : ℕ) : Finset (Expander.System 100 t) :=
  (Finset.univ.powersetCard s).biUnion fun S ↦
    (Finset.univ.powersetCard (6 * s / 5)).biUnion fun T ↦
      mappedInto 100 S T

lemma card_mediumBadAt_le (t s : ℕ) :
    (mediumBadAt t s).card ≤
      t.choose s * t.choose (6 * s / 5) *
        restrictionBound 100 t s (6 * s / 5) := by
  classical
  calc
    (mediumBadAt t s).card ≤
        (Finset.univ.powersetCard s).card *
          (t.choose (6 * s / 5) * restrictionBound 100 t s (6 * s / 5)) := by
      apply Finset.card_biUnion_le_card_mul
      intro S hS
      have hScard := (Finset.mem_powersetCard.mp hS).2
      calc
        ((Finset.univ.powersetCard (6 * s / 5)).biUnion fun T ↦
            mappedInto 100 S T).card ≤
            (Finset.univ.powersetCard (6 * s / 5)).card *
              restrictionBound 100 t s (6 * s / 5) := by
          apply Finset.card_biUnion_le_card_mul
          intro T hT
          have hTcard := (Finset.mem_powersetCard.mp hT).2
          simpa [hScard, hTcard] using
            card_mappedInto_le_restrictionBound 100 S T
        _ = t.choose (6 * s / 5) * restrictionBound 100 t s (6 * s / 5) := by
          simp
    _ = t.choose s * t.choose (6 * s / 5) *
          restrictionBound 100 t s (6 * s / 5) := by simp [mul_assoc]

lemma card_mediumBadAt_real_le {t s : ℕ} (ht : 0 < t)
    (hsmall : 2 * s ≤ t) (hmedium : t < 10 * s) :
    ((mediumBadAt t s).card : ℝ) ≤
      (Fintype.card (Expander.System 100 t) : ℝ) * (1 / 32 : ℝ) ^ t := by
  calc
    ((mediumBadAt t s).card : ℝ) ≤
        ((t.choose s * t.choose (6 * s / 5) *
          restrictionBound 100 t s (6 * s / 5) : ℕ) : ℝ) := by
      exact_mod_cast card_mediumBadAt_le t s
    _ ≤ (Fintype.card (Expander.System 100 t) : ℝ) * (1 / 32 : ℝ) ^ t :=
      medium_certificate_bound ht hsmall hmedium

noncomputable def mediumBad (t : ℕ) : Finset (Expander.System 100 t) :=
  ((Finset.range t).filter fun s ↦ 2 * s ≤ t ∧ t < 10 * s).biUnion fun s ↦
    mediumBadAt t s

lemma nat_mul_32_le_pow_32 {n : ℕ} (hn : 0 < n) : n * 32 ≤ 32 ^ n := by
  induction n using Nat.case_strong_induction_on with
  | hz => omega
  | hi n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        calc
          (n + 1) * 32 ≤ (n * 32) * 32 := by omega
          _ ≤ 32 ^ n * 32 := Nat.mul_le_mul_right 32 (ih n (by omega) hnpos)
          _ = 32 ^ (n + 1) := by rw [pow_succ]

lemma nat_mul_geometric_32 {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * (1 / 32 : ℝ) ^ n ≤ 1 / 32 := by
  have hcast : (n : ℝ) * 32 ≤ (32 : ℝ) ^ n := by
    exact_mod_cast nat_mul_32_le_pow_32 hn
  have hdiv : (n : ℝ) / (32 : ℝ) ^ n ≤ (1 : ℝ) / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    simpa using hcast
  simpa [div_eq_mul_inv, inv_pow] using hdiv

lemma card_mediumBad_real_le {t : ℕ} (ht : 0 < t) :
    ((mediumBad t).card : ℝ) ≤
      (Fintype.card (Expander.System 100 t) : ℝ) / 32 := by
  classical
  let I := (Finset.range t).filter fun s ↦ 2 * s ≤ t ∧ t < 10 * s
  have hcard : (mediumBad t).card ≤ ∑ s ∈ I, (mediumBadAt t s).card :=
    Finset.card_biUnion_le
  have hterm : ∀ s ∈ I,
      ((mediumBadAt t s).card : ℝ) ≤
        (Fintype.card (Expander.System 100 t) : ℝ) * (1 / 32 : ℝ) ^ t := by
    intro s hs
    exact card_mediumBadAt_real_le ht
      (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp hs).2.2
  have hIcard : I.card ≤ t := by
    exact (Finset.card_le_card (by
      dsimp [I]
      exact Finset.filter_subset _ _)).trans_eq (Finset.card_range t)
  calc
    ((mediumBad t).card : ℝ) ≤
        ∑ s ∈ I, ((mediumBadAt t s).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _s ∈ I, (Fintype.card (Expander.System 100 t) : ℝ) *
          (1 / 32 : ℝ) ^ t := Finset.sum_le_sum hterm
    _ = (I.card : ℝ) *
          ((Fintype.card (Expander.System 100 t) : ℝ) *
            (1 / 32 : ℝ) ^ t) := by simp
    _ ≤ (t : ℝ) *
          ((Fintype.card (Expander.System 100 t) : ℝ) *
            (1 / 32 : ℝ) ^ t) := by
      gcongr
    _ = (Fintype.card (Expander.System 100 t) : ℝ) *
          ((t : ℝ) * (1 / 32 : ℝ) ^ t) := by ring
    _ ≤ (Fintype.card (Expander.System 100 t) : ℝ) * (1 / 32 : ℝ) := by
      gcongr
      exact nat_mul_geometric_32 ht
    _ = (Fintype.card (Expander.System 100 t) : ℝ) / 32 := by ring

lemma mem_mappedInto_of_rightNeighbors_subset
    (D : Expander.System 100 t) (S T : Finset (Fin t))
    (hsub : D.rightNeighbors S ⊆ T) : D ∈ mappedInto 100 S T := by
  rw [mem_mappedInto_iff]
  intro j x hx
  apply hsub
  exact (D.mem_rightNeighbors_iff S (D.perm j x)).mpr ⟨j, x, hx, rfl⟩

lemma mem_smallBadAt_of_rightNeighbors_subset
    (D : Expander.System 100 t) {s : ℕ} (S T : Finset (Fin t))
    (hS : S.card = s) (hT : T.card = 3 * s)
    (hsub : D.rightNeighbors S ⊆ T) : D ∈ smallBadAt t s := by
  classical
  rw [smallBadAt]
  apply Finset.mem_biUnion.mpr
  refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT⟩,
    mem_mappedInto_of_rightNeighbors_subset D S T hsub⟩

lemma mem_smallBad_of_factor_three_failure
    (D : Expander.System 100 t) (S : Finset (Fin t))
    (hsize : 10 * S.card ≤ t)
    (hfail : ¬3 * S.card ≤ (D.rightNeighbors S).card) :
    D ∈ smallBad t := by
  classical
  have hs : 0 < S.card := by omega
  have hneighbors : (D.rightNeighbors S).card ≤ 3 * S.card := by omega
  have htarget : 3 * S.card ≤ Fintype.card (Fin t) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨T, hsub, hT⟩ :=
    Finset.exists_superset_card_eq hneighbors htarget
  rw [smallBad]
  apply Finset.mem_biUnion.mpr
  refine ⟨S.card - 1, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), by omega⟩
  · have hindex : S.card - 1 + 1 = S.card := by omega
    simpa [hindex] using
      mem_smallBadAt_of_rightNeighbors_subset D S T rfl hT hsub

lemma mem_mediumBadAt_of_rightNeighbors_subset
    (D : Expander.System 100 t) {s : ℕ} (S T : Finset (Fin t))
    (hS : S.card = s) (hT : T.card = 6 * s / 5)
    (hsub : D.rightNeighbors S ⊆ T) : D ∈ mediumBadAt t s := by
  classical
  rw [mediumBadAt]
  apply Finset.mem_biUnion.mpr
  refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT⟩,
    mem_mappedInto_of_rightNeighbors_subset D S T hsub⟩

lemma mem_mediumBad_of_eleven_tenths_failure
    (D : Expander.System 100 t) (S : Finset (Fin t))
    (hhalf : 2 * S.card ≤ t) (hmedium : t < 10 * S.card)
    (hfail : ¬11 * S.card ≤ 10 * (D.rightNeighbors S).card) :
    D ∈ mediumBad t := by
  classical
  have hs : 0 < S.card := by omega
  have hneighbors : (D.rightNeighbors S).card ≤ 6 * S.card / 5 := by
    omega
  have htarget : 6 * S.card / 5 ≤ Fintype.card (Fin t) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨T, hsub, hT⟩ :=
    Finset.exists_superset_card_eq hneighbors htarget
  rw [mediumBad]
  apply Finset.mem_biUnion.mpr
  refine ⟨S.card, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), hhalf, hmedium⟩
  · exact mem_mediumBadAt_of_rightNeighbors_subset D S T rfl hT hsub

noncomputable def rightBad (t : ℕ) : Finset (Expander.System 100 t) :=
  smallBad t ∪ mediumBad t

lemma right_expansion_of_not_mem_rightBad {t : ℕ} (ht : 0 < t)
    (D : Expander.System 100 t) (hD : D ∉ rightBad t) :
    (∀ S : Finset (Fin t), 2 * S.card ≤ t →
        11 * S.card ≤ 10 * (D.rightNeighbors S).card) ∧
      (∀ S : Finset (Fin t), 10 * S.card ≤ t →
        3 * S.card ≤ (D.rightNeighbors S).card) := by
  constructor
  · intro S hhalf
    by_contra hfail
    apply hD
    rw [rightBad, Finset.mem_union]
    by_cases hsmall : 10 * S.card ≤ t
    · left
      apply mem_smallBad_of_factor_three_failure D S hsmall
      intro hthree
      apply hfail
      omega
    · right
      exact mem_mediumBad_of_eleven_tenths_failure D S hhalf (by omega) hfail
  · intro S hsmall
    by_contra hfail
    apply hD
    rw [rightBad, Finset.mem_union]
    exact Or.inl (mem_smallBad_of_factor_three_failure D S hsmall hfail)

lemma card_rightBad_real_le {t : ℕ} (ht : 0 < t) :
    ((rightBad t).card : ℝ) ≤
      (Fintype.card (Expander.System 100 t) : ℝ) * (35 / 96 : ℝ) := by
  have hunion : (rightBad t).card ≤ (smallBad t).card + (mediumBad t).card := by
    simpa [rightBad] using Finset.card_union_le (smallBad t) (mediumBad t)
  calc
    ((rightBad t).card : ℝ) ≤
        ((smallBad t).card : ℝ) + (mediumBad t).card := by exact_mod_cast hunion
    _ ≤ (Fintype.card (Expander.System 100 t) : ℝ) / 3 +
          (Fintype.card (Expander.System 100 t) : ℝ) / 32 :=
      add_le_add (card_smallBad_real_le t) (card_mediumBad_real_le ht)
    _ = (Fintype.card (Expander.System 100 t) : ℝ) * (35 / 96 : ℝ) := by ring

/-- Reverse every matching.  This interchanges the two bipartite parts. -/
def inverseSystem {d t : ℕ} (D : Expander.System d t) :
    Expander.System d t := ⟨fun j ↦ (D.perm j).symm⟩

@[simp] lemma inverseSystem_perm {d t : ℕ} (D : Expander.System d t)
    (j : Fin d) : (inverseSystem D).perm j = (D.perm j).symm := rfl

@[simp] lemma inverseSystem_inverseSystem {d t : ℕ}
    (D : Expander.System d t) : inverseSystem (inverseSystem D) = D := by
  cases D
  rfl

lemma rightNeighbors_inverseSystem {d t : ℕ} (D : Expander.System d t)
    (S : Finset (Fin t)) :
    (inverseSystem D).rightNeighbors S = D.leftNeighbors S := by
  ext x
  simp only [Expander.System.mem_rightNeighbors_iff,
    Expander.System.mem_leftNeighbors_iff, inverseSystem_perm]
  constructor
  · rintro ⟨j, y, hy, hxy⟩
    refine ⟨j, y, hy, ?_⟩
    have := congrArg (D.perm j) hxy
    simpa using this.symm
  · rintro ⟨j, y, hy, hxy⟩
    refine ⟨j, y, hy, ?_⟩
    rw [Equiv.symm_apply_eq]
    exact hxy.symm

/-- The finite probabilistic construction, with all normalization removed:
for every nonempty part size there is a degree-100 permutation system having
both expansion estimates on both sides. -/
theorem exists_kahn_expander (t : ℕ) (ht : 0 < t) :
    ∃ D : Expander.System 100 t, D.HasKahnExpansion := by
  classical
  let B := rightBad t
  let forbidden := B ∪ B.image inverseSystem
  have hforbiddenNat : forbidden.card ≤ 2 * B.card := by
    calc
      forbidden.card ≤ B.card + (B.image inverseSystem).card :=
        by simpa [forbidden] using
          Finset.card_union_le B
            (B.image (inverseSystem : Expander.System 100 t →
              Expander.System 100 t))
      _ ≤ B.card + B.card := Nat.add_le_add_left Finset.card_image_le B.card
      _ = 2 * B.card := by omega
  have hforbiddenReal : (forbidden.card : ℝ) ≤
      2 * (Fintype.card (Expander.System 100 t) : ℝ) * (35 / 96 : ℝ) := by
    calc
      (forbidden.card : ℝ) ≤ 2 * (B.card : ℝ) := by exact_mod_cast hforbiddenNat
      _ ≤ 2 * ((Fintype.card (Expander.System 100 t) : ℝ) *
          (35 / 96 : ℝ)) := by
        gcongr
        exact card_rightBad_real_le ht
      _ = 2 * (Fintype.card (Expander.System 100 t) : ℝ) *
          (35 / 96 : ℝ) := by ring
  have htotalpos : (0 : ℝ) < Fintype.card (Expander.System 100 t) := by
    rw [card_system]
    positivity
  have hforbidden : forbidden.card < Fintype.card (Expander.System 100 t) := by
    exact_mod_cast (show (forbidden.card : ℝ) <
        Fintype.card (Expander.System 100 t) by
      calc
        (forbidden.card : ℝ) ≤
            2 * (Fintype.card (Expander.System 100 t) : ℝ) *
              (35 / 96 : ℝ) := hforbiddenReal
        _ < Fintype.card (Expander.System 100 t) := by nlinarith)
  have hexists : ∃ D : Expander.System 100 t, D ∉ forbidden := by
    by_contra hnone
    push_neg at hnone
    have heq : forbidden = Finset.univ := Finset.eq_univ_of_forall hnone
    have hcardeq := congrArg Finset.card heq
    simp only [Finset.card_univ] at hcardeq
    omega
  obtain ⟨D, hD⟩ := hexists
  have hDright : D ∉ rightBad t := by
    intro hbad
    exact hD (Finset.mem_union.mpr (Or.inl hbad))
  have hInvRight : inverseSystem D ∉ rightBad t := by
    intro hbad
    apply hD
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr ⟨inverseSystem D, hbad, by simp⟩
  have hright := right_expansion_of_not_mem_rightBad ht D hDright
  have hleftAsRight :=
    right_expansion_of_not_mem_rightBad ht (inverseSystem D) hInvRight
  refine ⟨D, hright.1, hright.2, ?_, ?_⟩
  · intro S hS
    simpa [rightNeighbors_inverseSystem] using hleftAsRight.1 S hS
  · intro S hS
    simpa [rightNeighbors_inverseSystem] using hleftAsRight.2 S hS

end Expander.Random

/-! ## Compressing `t` matching blocks to `q` pieces -/

namespace Compression

/-- Pair the first `2(t-q)` indices and leave the rest single. -/
def index (q t : ℕ) (hq : q ≤ t) (ht : t ≤ 2 * q) : Fin t → Fin q :=
  fun i ↦
    if h : i.1 < 2 * (t - q) then
      ⟨i.1 / 2, by
        have hd : i.1 / 2 < t - q := by
          apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).2
          simpa [mul_comm] using h
        omega⟩
    else
      ⟨(t - q) + (i.1 - 2 * (t - q)), by omega⟩

lemma index_apply_of_lt {q t : ℕ} (hq : q ≤ t) (ht : t ≤ 2 * q)
    (i : Fin t) (hi : i.1 < 2 * (t - q)) :
    (index q t hq ht i).1 = i.1 / 2 := by
  simp [index, hi]

lemma index_apply_of_ge {q t : ℕ} (hq : q ≤ t) (ht : t ≤ 2 * q)
    (i : Fin t) (hi : 2 * (t - q) ≤ i.1) :
    (index q t hq ht i).1 = (t - q) + (i.1 - 2 * (t - q)) := by
  simp [index, not_lt.mpr hi]

/-- Every compressed piece has an original block. -/
lemma index_surjective {q t : ℕ} (hqpos : 0 < q) (hq : q ≤ t)
    (ht : t ≤ 2 * q) : Function.Surjective (index q t hq ht) := by
  intro c
  by_cases hc : c.1 < t - q
  · have h2ct : 2 * c.1 < t := by omega
    let i : Fin t := ⟨2 * c.1, h2ct⟩
    refine ⟨i, Fin.ext ?_⟩
    rw [index_apply_of_lt hq ht i (by dsimp [i]; omega)]
    simp [i]
  · have hdc : t - q ≤ c.1 := not_lt.mp hc
    have hct : c.1 + (t - q) < t := by omega
    let i : Fin t := ⟨c.1 + (t - q), hct⟩
    refine ⟨i, Fin.ext ?_⟩
    rw [index_apply_of_ge hq ht i (by dsimp [i]; omega)]
    dsimp [i]
    omega

/-- The original matching blocks belonging to one compressed piece. -/
def fiber {q t : ℕ} (hq : q ≤ t) (ht : t ≤ 2 * q) (c : Fin q) :
    Finset (Fin t) :=
  Finset.univ.filter fun i ↦ index q t hq ht i = c

@[simp] lemma mem_fiber_iff {q t : ℕ} (hq : q ≤ t) (ht : t ≤ 2 * q)
    (c : Fin q) (i : Fin t) :
    i ∈ fiber hq ht c ↔ index q t hq ht i = c := by
  simp [fiber]

lemma fiber_card_le_two {q t : ℕ} (hq : q ≤ t) (ht : t ≤ 2 * q)
    (c : Fin q) : (fiber hq ht c).card ≤ 2 := by
  let d := t - q
  by_cases hc : c.1 < d
  · have h2d : 2 * d ≤ t := by dsimp [d]; omega
    let a : Fin t := ⟨2 * c.1, by omega⟩
    let b : Fin t := ⟨2 * c.1 + 1, by omega⟩
    have hsubset : fiber hq ht c ⊆ {a, b} := by
      intro i hi
      have heq := (mem_fiber_iff hq ht c i).mp hi
      have heqval := congrArg Fin.val heq
      by_cases hilow : i.1 < 2 * d
      · have hdiv : i.1 / 2 = c.1 := by
          simpa [d, index_apply_of_lt hq ht i (by simpa [d] using hilow)] using heqval
        rcases Nat.mod_two_eq_zero_or_one i.1 with hmod | hmod
        · have hid : i.1 = 2 * c.1 := by
            have hdecomp := Nat.mod_add_div i.1 2
            omega
          simp [a, b, Fin.ext_iff, hid]
        · have hid : i.1 = 2 * c.1 + 1 := by
            have hdecomp := Nat.mod_add_div i.1 2
            omega
          simp [a, b, Fin.ext_iff, hid]
      · have hilarge : 2 * d ≤ i.1 := not_lt.mp hilow
        have hval := index_apply_of_ge hq ht i (by simpa [d] using hilarge)
        rw [hval] at heqval
        dsimp [d] at hc heqval
        omega
    have hpair : ({a, b} : Finset (Fin t)).card ≤ 2 := by
      have h := Finset.card_insert_le a ({b} : Finset (Fin t))
      simpa using h
    exact (Finset.card_le_card hsubset).trans hpair
  · have hdc : d ≤ c.1 := not_lt.mp hc
    have hct : c.1 + d < t := by dsimp [d] at *; omega
    let a : Fin t := ⟨c.1 + d, hct⟩
    have hsubset : fiber hq ht c ⊆ {a} := by
      intro i hi
      have heq := (mem_fiber_iff hq ht c i).mp hi
      have heqval := congrArg Fin.val heq
      by_cases hilow : i.1 < 2 * d
      · have hval := index_apply_of_lt hq ht i (by simpa [d] using hilow)
        rw [hval] at heqval
        have hdivlt : i.1 / 2 < d := by
          apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).2
          simpa [mul_comm] using hilow
        omega
      · have hilarge : 2 * d ≤ i.1 := not_lt.mp hilow
        have hval := index_apply_of_ge hq ht i (by simpa [d] using hilarge)
        rw [hval] at heqval
        have hid : i.1 = c.1 + d := by
          dsimp [d] at heqval hilarge ⊢
          omega
        simp [a, Fin.ext_iff, hid]
    exact (Finset.card_le_card hsubset).trans (by simp)

/-- Original matching indices contained in a selected family of compressed
pieces. -/
def lift {q t : ℕ} (hq : q ≤ t) (ht : t ≤ 2 * q)
    (C : Finset (Fin q)) : Finset (Fin t) :=
  Finset.univ.filter fun i ↦ index q t hq ht i ∈ C

@[simp] lemma mem_lift_iff {q t : ℕ} (hq : q ≤ t) (ht : t ≤ 2 * q)
    (C : Finset (Fin q)) (i : Fin t) :
    i ∈ lift hq ht C ↔ index q t hq ht i ∈ C := by
  simp [lift]

@[simp] lemma lift_empty {q t : ℕ} (hq : q ≤ t) (ht : t ≤ 2 * q) :
    lift hq ht ∅ = ∅ := by
  ext i
  simp

lemma lift_subset_biUnion_fiber {q t : ℕ} (hq : q ≤ t)
    (ht : t ≤ 2 * q) (C : Finset (Fin q)) :
    lift hq ht C ⊆ C.biUnion (fiber hq ht) := by
  intro i hi
  have hic := (mem_lift_iff hq ht C i).mp hi
  exact Finset.mem_biUnion.mpr
    ⟨index q t hq ht i, hic, (mem_fiber_iff hq ht _ i).mpr rfl⟩

/-- Every compressed piece is a union of at most two original blocks. -/
lemma lift_card_le_twice {q t : ℕ} (hq : q ≤ t) (ht : t ≤ 2 * q)
    (C : Finset (Fin q)) : (lift hq ht C).card ≤ 2 * C.card := by
  calc
    (lift hq ht C).card ≤ (C.biUnion (fiber hq ht)).card :=
      Finset.card_le_card (lift_subset_biUnion_fiber hq ht C)
    _ ≤ C.card * 2 := Finset.card_biUnion_le_card_mul C (fiber hq ht) 2
      (fun c _ ↦ fiber_card_le_two hq ht c)
    _ = 2 * C.card := by omega

lemma image_complement_lift {q t : ℕ} (hqpos : 0 < q) (hq : q ≤ t)
    (ht : t ≤ 2 * q) (C : Finset (Fin q)) :
    (Finset.univ \ lift hq ht C).image (index q t hq ht) =
      Finset.univ \ C := by
  ext c
  constructor
  · intro hc
    obtain ⟨i, hi, hic⟩ := Finset.mem_image.mp hc
    have hi' := Finset.mem_sdiff.mp hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hcC
    apply hi'.2
    apply (mem_lift_iff hq ht C i).mpr
    simpa [hic] using hcC
  · intro hc
    have hc' := Finset.mem_sdiff.mp hc
    obtain ⟨i, hi⟩ := index_surjective hqpos hq ht c
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, hi⟩
    intro hilift
    exact hc'.2 (by simpa [hi] using (mem_lift_iff hq ht C i).mp hilift)

/-- Merging `t` original blocks into `q` nonempty pieces creates only
`t-q` possible excess original blocks. -/
lemma lift_card_le_add_defect {q t : ℕ} (hqpos : 0 < q) (hq : q ≤ t)
    (ht : t ≤ 2 * q) (C : Finset (Fin q)) :
    (lift hq ht C).card ≤ C.card + (t - q) := by
  have himage := image_complement_lift hqpos hq ht C
  have hcomp : (Finset.univ \ C).card ≤
      (Finset.univ \ lift hq ht C).card := by
    rw [← himage]
    exact Finset.card_image_le
  rw [Finset.card_sdiff, Finset.card_sdiff] at hcomp
  simp only [Finset.card_univ, Fintype.card_fin, Finset.inter_univ] at hcomp
  have hCcard : C.card ≤ q := by
    simpa using Finset.card_le_card (Finset.subset_univ C)
  have hliftcard : (lift hq ht C).card ≤ t := by
    simpa using Finset.card_le_card (Finset.subset_univ (lift hq ht C))
  omega

end Compression

/-! ## Local matching blocks and compressed pieces -/

namespace Local

open Expander Compression

/-- The index of the unique matching block of the chosen side containing a
local vertex.  `false` is the left partition and `true` the right one. -/
def blockIndex {d t : ℕ} (D : Expander.System d t) (side : Bool)
    (v : Fin d × Fin t) : Fin t :=
  if side then D.perm v.1 v.2 else v.2

/-- One original matching block. -/
def originalBlock {d t : ℕ} (D : Expander.System d t) (side : Bool)
    (x : Fin t) : Finset (Fin d × Fin t) :=
  Finset.univ.filter fun v ↦ blockIndex D side v = x

@[simp] lemma mem_originalBlock_iff {d t : ℕ} (D : Expander.System d t)
    (side : Bool) (x : Fin t) (v : Fin d × Fin t) :
    v ∈ originalBlock D side x ↔ blockIndex D side v = x := by
  simp [originalBlock]

@[simp] lemma originalBlock_false {d t : ℕ} (D : Expander.System d t)
    (x : Fin t) : originalBlock D false x = D.leftBlock x := by
  ext v
  simp [originalBlock, blockIndex, Expander.System.leftBlock]

@[simp] lemma originalBlock_true {d t : ℕ} (D : Expander.System d t)
    (x : Fin t) : originalBlock D true x = D.rightBlock x := by
  ext v
  simp [originalBlock, blockIndex, Expander.System.rightBlock]

/-- A compressed piece is the union of the one or two original blocks in a
compression fibre. -/
def compressedPiece {d q t : ℕ} (D : Expander.System d t)
    (side : Bool) (hq : q ≤ t) (ht : t ≤ 2 * q) (c : Fin q) :
    Finset (Fin d × Fin t) :=
  Finset.univ.filter fun v ↦ index q t hq ht (blockIndex D side v) = c

@[simp] lemma mem_compressedPiece_iff {d q t : ℕ}
    (D : Expander.System d t) (side : Bool) (hq : q ≤ t)
    (ht : t ≤ 2 * q) (c : Fin q) (v : Fin d × Fin t) :
    v ∈ compressedPiece D side hq ht c ↔
      index q t hq ht (blockIndex D side v) = c := by
  simp [compressedPiece]

/-- A packet is obtained by grouping compressed pieces according to a map on
their `q` indices.  Surjectivity is not needed for membership or regularity;
the packet maps used later are surjective. -/
def packet {d q t h : ℕ} (D : Expander.System d t) (side : Bool)
    (hq : q ≤ t) (ht : t ≤ 2 * q) (group : Fin q → Fin h) (e : Fin h) :
    Finset (Fin d × Fin t) :=
  Finset.univ.filter fun v ↦
    group (index q t hq ht (blockIndex D side v)) = e

@[simp] lemma mem_packet_iff {d q t h : ℕ} (D : Expander.System d t)
    (side : Bool) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (group : Fin q → Fin h) (e : Fin h) (v : Fin d × Fin t) :
    v ∈ packet D side hq ht group e ↔
      group (index q t hq ht (blockIndex D side v)) = e := by
  simp [packet]

end Local

/-! ## Fixed-relative prime intervals -/

namespace Arithmetic

/-- The exact package of numerical parameters needed by the finite
construction, uniformly for all sufficiently large integers in one parity
class.  Naming this proposition keeps specializations at the two very large
field orders from repeatedly reducing the same long dependent type. -/
def EventuallyUsableParameters (K parity : ℕ) : Prop :=
  ∃ R : ℕ, ∀ r : ℕ, R ≤ r → r % 2 = parity →
    ∃ q t : ℕ, q.Prime ∧ q % 4 = 3 ∧ q < t ∧ t ≤ 2 * q ∧
      20 * (t - q) + 20 ≤ q ∧ 2 * K + 1 ≤ q ∧
      K ^ 2 * t ≤ (K ^ 2 + 1) * q ∧ r = K * q + t ∧
      ∀ p : ℕ, p.Prime → p ∣ t → K ≤ p

/-- Odd primes strictly below the fixed plane order. -/
def smallOddPrimes (K : ℕ) : Finset ℕ :=
  (Finset.range K).filter fun p ↦ p.Prime ∧ p ≠ 2

@[simp] lemma mem_smallOddPrimes_iff {K p : ℕ} :
    p ∈ smallOddPrimes K ↔ p.Prime ∧ p < K ∧ p ≠ 2 := by
  simp [smallOddPrimes, and_assoc, and_left_comm, and_comm]

lemma smallOddPrimes_pairwise_coprime (K : ℕ) :
    Set.Pairwise (smallOddPrimes K : Set ℕ) Nat.Coprime := by
  intro p hp q hq hpq
  exact (Nat.coprime_primes
    (mem_smallOddPrimes_iff.mp hp).1
    (mem_smallOddPrimes_iff.mp hq).1).mpr hpq

/-- The local CRT choice: use `1`, except that when this would make
`r-K*q` vanish modulo `p`, use `2`. -/
def avoidingResidue (K r p : ℕ) : ℕ :=
  if r ≡ K [MOD p] then 2 else 1

lemma avoidingResidue_eq_one_or_two (K r p : ℕ) :
    avoidingResidue K r p = 1 ∨ avoidingResidue K r p = 2 := by
  simp only [avoidingResidue]
  split <;> simp

lemma avoidingResidue_coprime {K r p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (avoidingResidue K r p).Coprime p := by
  rcases avoidingResidue_eq_one_or_two K r p with h | h <;> rw [h]
  · exact Nat.coprime_one_left p
  · exact (Nat.coprime_of_lt_prime (by norm_num)
      (lt_of_le_of_ne hp.two_le (Ne.symm hp2)) hp).symm

lemma avoidingResidue_prevents_dvd {K r p q : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ K) (hKqr : K * q ≤ r)
    (hq : q ≡ avoidingResidue K r p [MOD p]) :
    ¬ p ∣ r - K * q := by
  letI : Fact p.Prime := ⟨hp⟩
  intro hdiv
  have hsub : ((r - K * q : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 hdiv
  have hrq : (r : ZMod p) = (K : ZMod p) * (q : ZMod p) := by
    rw [Nat.cast_sub hKqr] at hsub
    push_cast at hsub
    exact sub_eq_zero.mp hsub
  have hqcast : (q : ZMod p) = (avoidingResidue K r p : ℕ) :=
    (ZMod.natCast_eq_natCast_iff q (avoidingResidue K r p) p).2 hq
  by_cases hrK : r ≡ K [MOD p]
  · have hres : avoidingResidue K r p = 2 := by simp [avoidingResidue, hrK]
    have hrKcast : (r : ZMod p) = (K : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff r K p).2 hrK
    have hKzero : (K : ZMod p) = 0 := by
      rw [hqcast, hres] at hrq
      push_cast at hrq
      rw [hrKcast] at hrq
      linear_combination -hrq
    exact hpK ((ZMod.natCast_eq_zero_iff K p).1 hKzero)
  · have hres : avoidingResidue K r p = 1 := by simp [avoidingResidue, hrK]
    have hrKcast : (r : ZMod p) = (K : ZMod p) := by
      rw [hqcast, hres] at hrq
      simpa using hrq
    exact hrK ((ZMod.natCast_eq_natCast_iff r K p).1 hrKcast)

/-- Product of the odd prime moduli used by the CRT refinement. -/
def oddPrimeModulus (K : ℕ) : ℕ := ∏ p ∈ smallOddPrimes K, p

lemma oddPrimeModulus_pos (K : ℕ) : 0 < oddPrimeModulus K := by
  apply Finset.prod_pos
  intro p hp
  exact (mem_smallOddPrimes_iff.mp hp).1.pos

lemma four_coprime_oddPrimeModulus (K : ℕ) :
    Nat.Coprime 4 (oddPrimeModulus K) := by
  rw [oddPrimeModulus, Nat.coprime_prod_right_iff]
  intro p hp
  have hp' := mem_smallOddPrimes_iff.mp hp
  have h2p : Nat.Coprime 2 p :=
    Nat.coprime_two_left.mpr (hp'.1.odd_of_ne_two hp'.2.2)
  simpa using h2p.pow_left 2

/-- CRT solution for all odd primes below `K`. -/
noncomputable def oddCRTResidue (K r : ℕ) : ℕ :=
  Nat.chineseRemainderOfFinset (avoidingResidue K r) id (smallOddPrimes K)
    (fun p hp ↦ (mem_smallOddPrimes_iff.mp hp).1.ne_zero)
    (smallOddPrimes_pairwise_coprime K)

lemma oddCRTResidue_modEq (K r : ℕ) {p : ℕ} (hp : p ∈ smallOddPrimes K) :
    oddCRTResidue K r ≡ avoidingResidue K r p [MOD p] := by
  exact (Nat.chineseRemainderOfFinset (avoidingResidue K r) id
    (smallOddPrimes K)
    (fun p hp ↦ (mem_smallOddPrimes_iff.mp hp).1.ne_zero)
    (smallOddPrimes_pairwise_coprime K)).prop p hp

def kahnModulus (K : ℕ) : ℕ := 4 * oddPrimeModulus K

/-- Combine the odd-prime CRT solution with the class `3 mod 4`. -/
noncomputable def kahnResidue (K r : ℕ) : ℕ :=
  Nat.chineseRemainder (four_coprime_oddPrimeModulus K) 3 (oddCRTResidue K r)

lemma kahnResidue_lt (K r : ℕ) : kahnResidue K r < kahnModulus K := by
  exact Nat.chineseRemainder_lt_mul (four_coprime_oddPrimeModulus K)
    3 (oddCRTResidue K r) (by norm_num) (oddPrimeModulus_pos K).ne'

lemma kahnResidue_modEq_four (K r : ℕ) : kahnResidue K r ≡ 3 [MOD 4] :=
  (Nat.chineseRemainder (four_coprime_oddPrimeModulus K)
    3 (oddCRTResidue K r)).prop.1

lemma kahnResidue_modEq_oddModulus (K r : ℕ) :
    kahnResidue K r ≡ oddCRTResidue K r [MOD oddPrimeModulus K] :=
  (Nat.chineseRemainder (four_coprime_oddPrimeModulus K)
    3 (oddCRTResidue K r)).prop.2

lemma kahnResidue_mod_four (K r : ℕ) : kahnResidue K r % 4 = 3 := by
  simpa [Nat.ModEq] using kahnResidue_modEq_four K r

lemma kahnResidue_modEq_smallOddPrime (K r : ℕ) {p : ℕ}
    (hp : p ∈ smallOddPrimes K) :
    kahnResidue K r ≡ avoidingResidue K r p [MOD p] := by
  have hpdiv : p ∣ oddPrimeModulus K := by
    exact Finset.dvd_prod_of_mem id hp
  exact (kahnResidue_modEq_oddModulus K r).of_dvd hpdiv |>.trans
    (oddCRTResidue_modEq K r hp)

lemma kahnResidue_coprime (K r : ℕ) :
    (kahnResidue K r).Coprime (kahnModulus K) := by
  have hfour : (kahnResidue K r).Coprime 4 := by
    have hodd : Odd (kahnResidue K r) := by
      rw [← Nat.coprime_two_right]
      rw [Nat.coprime_iff_gcd_eq_one,
        (kahnResidue_modEq_four K r).of_dvd (by norm_num : 2 ∣ 4) |>.gcd_eq]
      norm_num
    have htwo : (kahnResidue K r).Coprime 2 := hodd.coprime_two_right
    simpa using htwo.pow_right 2
  have hoddmod : (kahnResidue K r).Coprime (oddPrimeModulus K) := by
    rw [oddPrimeModulus, Nat.coprime_prod_right_iff]
    intro p hp
    have hp' := mem_smallOddPrimes_iff.mp hp
    rw [Nat.coprime_iff_gcd_eq_one,
      (kahnResidue_modEq_smallOddPrime K r hp).gcd_eq]
    exact avoidingResidue_coprime hp'.1 hp'.2.2
  exact Nat.coprime_mul_iff_right.mpr ⟨hfour, hoddmod⟩

/-- A reduced class modulo `Q` which simultaneously fixes `q = 3 (mod 4)`
and prevents every prime below `K` from dividing the remainder `r-K*q`. -/
def IsKahnResidue (K Q r a : ℕ) : Prop :=
  a < Q ∧ a.Coprime Q ∧ a % 4 = 3 ∧
    ∀ q : ℕ, q % Q = a → K * q ≤ r →
      ∀ p : ℕ, p.Prime → p < K →
      ¬ p ∣ r - K * q

/-- The fixed modulus `kahnModulus K` supplies a good class whenever `K`
and `r` have opposite parity and no odd prime below `K` divides `K`.  The
latter holds for the two plane orders used in the proof (a power of two and
an odd prime). -/
lemma exists_kahnResidue (K r : ℕ)
    (hparity : K % 2 ≠ r % 2)
    (hKprimeFactors : ∀ p : ℕ, p.Prime → p < K → p ∣ K → p = 2) :
    ∃ a : ℕ, IsKahnResidue K (kahnModulus K) r a := by
  refine ⟨kahnResidue K r, kahnResidue_lt K r,
    kahnResidue_coprime K r, kahnResidue_mod_four K r, ?_⟩
  intro q hqmod hKqr p hp hpK
  by_cases hp2 : p = 2
  · subst p
    intro hdiv
    have hq4 : q % 4 = 3 := by
      calc
        q % 4 = (q % kahnModulus K) % 4 := by
          apply (Nat.mod_mod_of_dvd q ?_).symm
          exact dvd_mul_right 4 (oddPrimeModulus K)
        _ = kahnResidue K r % 4 := by rw [hqmod]
        _ = 3 := kahnResidue_mod_four K r
    have hq2 : q ≡ 1 [MOD 2] := by
      show q % 2 = 1 % 2
      rw [← Nat.mod_mod_of_dvd q (by norm_num : 2 ∣ 4), hq4]
    have hKqK : K * q ≡ K [MOD 2] := by
      simpa using hq2.mul_left K
    have hKqrmod : K * q ≡ r [MOD 2] :=
      Nat.modEq_of_dvd' hKqr hdiv
    apply hparity
    exact show K % 2 = r % 2 from hKqK.symm.trans hKqrmod
  · have hpMem : p ∈ smallOddPrimes K :=
      mem_smallOddPrimes_iff.mpr ⟨hp, hpK, hp2⟩
    have hpNotK : ¬ p ∣ K := fun h ↦ hp2 (hKprimeFactors p hp hpK h)
    have hqQ : q ≡ kahnResidue K r [MOD kahnModulus K] := by
      show q % kahnModulus K = kahnResidue K r % kahnModulus K
      rw [hqmod, Nat.mod_eq_of_lt (kahnResidue_lt K r)]
    have hpdivQ : p ∣ kahnModulus K := by
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id hpMem) 4
    have hqp : q ≡ avoidingResidue K r p [MOD p] :=
      (hqQ.of_dvd hpdivQ).trans (kahnResidue_modEq_smallOddPrime K r hpMem)
    exact avoidingResidue_prevents_dvd hp hp2 hpNotK hKqr hqp

/-- A fixed reduced residue class contains a prime in every sufficiently
large interval whose endpoints are two fixed positive multiples.  This is
the exact qualitative consequence of the repository's proved PNT in
arithmetic progressions that is needed for Kahn's parameter choice. -/
lemma eventually_exists_prime_between_fixed_multiples
    {Q a : ℕ} (hQ : 1 ≤ Q) (ha : a.Coprime Q) (haQ : a < Q)
    {A B : ℝ} (hB : 0 < B) (hBA : B < A) (hA2B : A ≤ 2 * B) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
      ∃ p : ℕ, p.Prime ∧ p % Q = a ∧
        (r : ℝ) / A < p ∧ (p : ℝ) ≤ (r : ℝ) / B := by
  have hA : 0 < A := hB.trans hBA
  let δ : ℝ := (A - B) / (2 * B)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨x₀, hx₀, hcount⟩ :=
    Erdos387.PNT_fixed_modulus Q a hQ haQ ha δ hδ (1 / 2) (by norm_num)
  refine ⟨Nat.ceil (A * x₀) + 1, ?_⟩
  intro r hr
  let x : ℝ := (r : ℝ) / A
  let v : ℝ := (r : ℝ) / B
  have hx₀x : x₀ ≤ x := by
    have hceil : A * x₀ ≤ (Nat.ceil (A * x₀) : ℝ) := Nat.le_ceil _
    have hcast : (Nat.ceil (A * x₀) : ℝ) < r := by
      exact_mod_cast (lt_of_lt_of_le (Nat.lt_succ_self _) hr)
    dsimp [x]
    apply (le_div_iff₀ hA).2
    simpa [mul_comm] using hceil.trans hcast.le
  have hxpos : 0 < x := lt_of_lt_of_le (by linarith [hx₀]) hx₀x
  have hrnat : 0 < r := by omega
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hrnat
  have hxv : x < v := by
    dsimp [x, v]
    rw [div_lt_div_iff₀ hA hB]
    nlinarith
  have hv2x : v ≤ 2 * x := by
    dsimp [x, v]
    field_simp [hA.ne', hB.ne']
    nlinarith
  have hlength : δ * x ≤ v - x := by
    have heq : v - x = 2 * (δ * x) := by
      dsimp [δ, x, v]
      field_simp [hA.ne', hB.ne']
    rw [heq]
    nlinarith [mul_nonneg hδ.le hxpos.le]
  have hest := hcount x hx₀x x v le_rfl hxv hv2x hlength
  let S := (Finset.Ioc ⌊x⌋₊ ⌊v⌋₊).filter
    (fun p : ℕ => p.Prime ∧ p % Q = a)
  have htot : (0 : ℝ) < Q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hQ
  have hlog : 0 < Real.log x := Real.log_pos (by linarith [hx₀])
  have hmain : 0 < (v - x) / ((Q.totient : ℝ) * Real.log x) := by
    positivity
  have hcardpos : 0 < S.card := by
    have hest' :
        |(S.card : ℝ) - (v - x) / ((Q.totient : ℝ) * Real.log x)| ≤
          (1 / 2 : ℝ) * ((v - x) / ((Q.totient : ℝ) * Real.log x)) := by
      simpa [S, div_eq_mul_inv, mul_assoc] using hest
    have hhalf :
        (1 / 2 : ℝ) * ((v - x) / ((Q.totient : ℝ) * Real.log x)) ≤
          (S.card : ℝ) := by
      have hlower := (neg_le_abs
        (((S.card : ℝ) - (v - x) / ((Q.totient : ℝ) * Real.log x)))).trans hest'
      linarith
    have hhalfpos : (0 : ℝ) <
        (1 / 2 : ℝ) * ((v - x) / ((Q.totient : ℝ) * Real.log x)) :=
      mul_pos (by norm_num) hmain
    have hcast : (0 : ℝ) < S.card := hhalfpos.trans_le hhalf
    exact_mod_cast hcast
  obtain ⟨p, hpS⟩ := Finset.card_pos.mp hcardpos
  have hp := Finset.mem_filter.mp hpS
  have hpIoc := Finset.mem_Ioc.mp hp.1
  refine ⟨p, hp.2.1, hp.2.2, ?_, ?_⟩
  · calc
      x < (⌊x⌋₊ + 1 : ℕ) := by simpa using Nat.lt_floor_add_one x
      _ ≤ p := by exact_mod_cast (show ⌊x⌋₊ + 1 ≤ p by omega)
  · exact (Nat.cast_le.mpr hpIoc.2).trans (Nat.floor_le (hxpos.trans hxv).le)

/-- The threshold in the preceding theorem can be chosen uniformly over all
reduced residue classes of one fixed modulus.  This is the finite-uniformity
step needed because Kahn's CRT residue depends on `r`. -/
lemma eventually_exists_prime_between_fixed_multiples_uniform
    {Q : ℕ} (hQ : 1 ≤ Q) {A B : ℝ} (hB : 0 < B) (hBA : B < A)
    (hA2B : A ≤ 2 * B) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → ∀ a : ℕ, a < Q → a.Coprime Q →
      ∃ p : ℕ, p.Prime ∧ p % Q = a ∧
        (r : ℝ) / A < p ∧ (p : ℝ) ≤ (r : ℝ) / B := by
  let P : Fin Q → ℕ → Prop := fun a r ↦
    a.1.Coprime Q →
      ∃ p : ℕ, p.Prime ∧ p % Q = a.1 ∧
        (r : ℝ) / A < p ∧ (p : ℝ) ≤ (r : ℝ) / B
  have h_each : ∀ a : Fin Q, ∀ᶠ r in atTop, P a r := by
    intro a
    by_cases ha : a.1.Coprime Q
    · obtain ⟨R, hR⟩ := eventually_exists_prime_between_fixed_multiples
        hQ ha a.2 hB hBA hA2B
      filter_upwards [eventually_ge_atTop R] with r hr
      exact fun _ ↦ hR r hr
    · exact Filter.Eventually.of_forall fun _ hcop ↦ (ha hcop).elim
  have h_all : ∀ᶠ r : ℕ in atTop, ∀ a : Fin Q, P a r :=
    Filter.eventually_all.mpr h_each
  rw [eventually_atTop] at h_all
  obtain ⟨R, hR⟩ := h_all
  refine ⟨R, ?_⟩
  intro r hr a haQ hacop
  exact hR r hr ⟨a, haQ⟩ hacop

/-- Once the finite CRT step supplies a good reduced class for every `r`,
the uniform prime-interval theorem gives all of Kahn's numerical parameters,
including the prime-factor condition needed by the elementary product OA. -/
lemma eventually_exists_refined_parameters_of_residues
    (K Q : ℕ) (P : ℕ → Prop) (hK : 2 ≤ K) (hQ : 1 ≤ Q) (h4Q : 4 ∣ Q)
    (hres : ∀ r : ℕ, P r → ∃ a : ℕ, IsKahnResidue K Q r a) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → P r →
      ∃ q t : ℕ, q.Prime ∧ q % 4 = 3 ∧ q < t ∧
        K ^ 2 * t ≤ (K ^ 2 + 1) * q ∧ r = K * q + t ∧
        ∀ p : ℕ, p.Prime → p ∣ t → K ≤ p := by
  let A : ℝ := (K : ℝ) + 1 + 1 / (K : ℝ) ^ 2
  let B : ℝ := (K : ℝ) + 1 + 1 / (2 * (K : ℝ) ^ 2)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hBA : B < A := by
    dsimp [A, B]
    have hKpos : (0 : ℝ) < K := by positivity
    have hsq : (0 : ℝ) < (K : ℝ) ^ 2 := sq_pos_of_pos hKpos
    field_simp
    nlinarith
  have hA2B : A ≤ 2 * B := by
    dsimp [A, B]
    have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
    have hsq : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
    field_simp
    nlinarith
  obtain ⟨R, hR⟩ := eventually_exists_prime_between_fixed_multiples_uniform
    hQ hB hBA hA2B
  refine ⟨R, ?_⟩
  intro r hr hPr
  obtain ⟨a, haQ, hacop, ha4, havoid⟩ := hres r hPr
  obtain ⟨q, hqprime, hqmodQ, hqlower, hqupper⟩ :=
    hR r hr a haQ hacop
  have hqmod4 : q % 4 = 3 := by
    calc
      q % 4 = (q % Q) % 4 := (Nat.mod_mod_of_dvd q h4Q).symm
      _ = a % 4 := by rw [hqmodQ]
      _ = 3 := ha4
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
  have hrpos : (0 : ℝ) < r := by
    have : (0 : ℝ) < (r : ℝ) / B := hqpos.trans_le hqupper
    have hmul := mul_pos this hB
    simpa [div_mul_cancel₀ _ hB.ne'] using hmul
  have hKq_lt_r : K * q < r := by
    have hBgt : (K : ℝ) < B := by
      have hfrac : (0 : ℝ) < 1 / (2 * (K : ℝ) ^ 2) := by positivity
      dsimp [B]
      linarith
    have hreal : (K : ℝ) * q < r := by
      have hmul := mul_le_mul_of_nonneg_left hqupper hB.le
      have hqK : (K : ℝ) * q < B * q :=
        mul_lt_mul_of_pos_right hBgt hqpos
      calc
        (K : ℝ) * q < B * q := hqK
        _ ≤ B * ((r : ℝ) / B) := hmul
        _ = r := by field_simp
    exact_mod_cast hreal
  let t := r - K * q
  have hsum : r = K * q + t := by
    dsimp [t]
    omega
  have hqt : q < t := by
    have hBgt : (K : ℝ) + 1 < B := by
      have hfrac : (0 : ℝ) < 1 / (2 * (K : ℝ) ^ 2) := by positivity
      dsimp [B]
      linarith
    have hreal : ((K + 1) * q : ℕ) < r := by
      exact_mod_cast (calc
        ((K + 1 : ℕ) : ℝ) * q < B * q := by
          push_cast
          exact mul_lt_mul_of_pos_right hBgt hqpos
        _ ≤ r := by
          calc
            B * q ≤ B * ((r : ℝ) / B) :=
              mul_le_mul_of_nonneg_left hqupper hB.le
            _ = r := by field_simp)
    have hreal' : K * q + q < r := by simpa [add_mul] using hreal
    dsimp [t]
    omega
  have hrange : K ^ 2 * t ≤ (K ^ 2 + 1) * q := by
    have hreal : ((K ^ 2 * t : ℕ) : ℝ) < (((K ^ 2 + 1) * q : ℕ) : ℝ) := by
      have hKA : (K : ℝ) ^ 2 * A =
          (K : ℝ) ^ 2 * ((K : ℝ) + 1) + 1 := by
        dsimp [A]
        field_simp
      have hrA : (r : ℝ) < A * q := by
        rw [mul_comm]
        exact (div_lt_iff₀ (hB.trans hBA)).mp hqlower
      have hscaled := mul_lt_mul_of_pos_left hrA
        (show (0 : ℝ) < (K : ℝ) ^ 2 by positivity)
      rw [hsum] at hscaled
      push_cast at hscaled ⊢
      rw [← mul_assoc, hKA] at hscaled
      nlinarith
    exact_mod_cast hreal.le
  have hfactors : ∀ p : ℕ, p.Prime → p ∣ t → K ≤ p := by
    intro p hp hpt
    by_contra hnot
    have hpK : p < K := by omega
    exact (havoid q hqmodQ hKq_lt_r.le p hp hpK) (by simpa [t] using hpt)
  exact ⟨q, t, hqprime, hqmod4, hqt, hrange, hsum, hfactors⟩

end Arithmetic

/-! ## The global Kahn construction -/

namespace Construction

open Projective Labels Expander Compression Local Transversal

variable {F : Type*} [Fintype F] [Field F] [DecidableEq F]

local instance primeNeZero (q : ℕ) [Fact q.Prime] : NeZero q :=
  ⟨(Fact.out : q.Prime).ne_zero⟩

/-- The distinguished point removed from the fixed projective plane. -/
def basePoint : Point F := verticalInfinity

/-- The points indexing the disjoint expander copies. -/
abbrev BasePoint (F : Type*) [Zero F] :=
  {x : Point F // x ≠ (basePoint : Point F)}

/-- Vertices in the copy indexed by `x`. -/
abbrev Vertex (F : Type*) [Zero F] (t : ℕ) :=
  BasePoint F × (Fin 100 × Fin t)

lemma card_basePoint : Fintype.card (BasePoint F) =
    Fintype.card F ^ 2 + Fintype.card F := by
  classical
  change Fintype.card {x : Point F // x ≠ verticalInfinity} = _
  rw [Fintype.card_subtype_compl
    (fun x : Point F ↦ x = verticalInfinity),
    Fintype.card_subtype_eq, Projective.card_point]
  omega

lemma card_vertex (t : ℕ) : Fintype.card (Vertex F t) =
    100 * (Fintype.card F ^ 2 + Fintype.card F) * t := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, card_basePoint]
  ring

/-- Points of a line after deleting the distinguished point.  The proof that
the distinguished point lies on the line is retained so the deleted element
is definitionally available. -/
abbrev LargePoint (l : Line F) (hl : Incident (basePoint : Point F) l) :=
  {p : {p : Point F // Incident p l} //
    p ≠ (⟨basePoint, hl⟩ : {p : Point F // Incident p l})}

lemma card_largePoint (l : Line F) (hl : Incident (basePoint : Point F) l) :
    Fintype.card (LargePoint l hl) = Fintype.card F := by
  classical
  have hinc : Fintype.card {p : Point F // Incident p l} =
      Fintype.card F + 1 := by
    calc
      Fintype.card {p : Point F // Incident p l} =
          (pointsOnLine l).card := by
        simpa [pointsOnLine] using
          Fintype.card_subtype (fun p : Point F ↦ Incident p l)
      _ = Fintype.card F + 1 := card_pointsOnLine l
  rw [Fintype.card_subtype_compl
    (fun p : {p : Point F // Incident p l} ↦
      p = (⟨basePoint, hl⟩ : {p : Point F // Incident p l})),
    Fintype.card_subtype_eq, hinc]
  omega

/-- A canonical enumeration of the `K` non-base points on a base line. -/
noncomputable def largePointEquiv (l : Line F)
    (hl : Incident (basePoint : Point F) l) :
    LargePoint l hl ≃ Fin (Fintype.card F) := by
  apply Fintype.equivOfCardEq
  simpa using card_largePoint l hl

/-- Regard an incident global point as a member of the punctured line. -/
def toLargePoint (l : Line F) (hl : Incident (basePoint : Point F) l)
    (x : BasePoint F) (hxl : Incident x.1 l) : LargePoint l hl :=
  ⟨⟨x.1, hxl⟩, by
    intro h
    apply x.2
    exact congrArg Subtype.val h⟩

/-- The explicit assignment fibre on a line avoiding the base point. -/
noncomputable def assignedFiber (l : Line F) : Finset (BasePoint F) :=
  Finset.univ.filter fun x ↦ assignedLine x.1 = l

@[simp] lemma mem_assignedFiber_iff (l : Line F) (x : BasePoint F) :
    x ∈ assignedFiber l ↔ assignedLine x.1 = l := by
  simp [assignedFiber]

lemma assignedFiber_nonempty (l : Line F)
    (hl : ¬ Incident (basePoint : Point F) l) :
    (assignedFiber l).Nonempty := by
  classical
  rcases l with mb | c
  · rcases mb with ⟨m, b⟩
    let x : BasePoint F :=
      ⟨affine m (b + m ^ 2), by simp [basePoint, affine, verticalInfinity]⟩
    refine ⟨x, (mem_assignedFiber_iff _ _).mpr ?_⟩
    change graph m ((b + m ^ 2) - m ^ 2) = graph m b
    congr 2
    ring
  · rcases c with c | u
    · exact (hl (incident_vertical_horizon (F := F))).elim
    · exact (hl (incident_vertical_horizon (F := F))).elim

lemma assignedFiber_card_le_two (l : Line F)
    (hl : ¬ Incident (basePoint : Point F) l) :
    (assignedFiber l).card ≤ 2 := by
  classical
  rcases l with mb | c
  · rcases mb with ⟨m, b⟩
    let a : BasePoint F :=
      ⟨affine m (b + m ^ 2), by simp [basePoint, affine, verticalInfinity]⟩
    let s : BasePoint F :=
      ⟨slope m, by simp [basePoint, Projective.slope, verticalInfinity]⟩
    have hsub : assignedFiber (graph m b) ⊆ {a, s} := by
      intro x hx
      have hxline := (mem_assignedFiber_iff _ _).mp hx
      rcases assignedLine_fiber_subsingleton_after_affine hxline with ha | hs
      · have hxa : x = a := by
          apply Subtype.ext
          exact ha
        simp [hxa]
      · have hxs : x = s := by
          apply Subtype.ext
          exact hs.2
        simp [hxs]
    calc
      (assignedFiber (graph m b)).card ≤ ({a, s} : Finset (BasePoint F)).card :=
        Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  · rcases c with c | u
    · exact (hl (incident_vertical_horizon (F := F))).elim
    · exact (hl (incident_vertical_horizon (F := F))).elim

/-- The assignment fibre, as a finite type. -/
abbrev AssignedPoint (l : Line F) := {x : BasePoint F // x ∈ assignedFiber l}

lemma card_assignedPoint_le_two (l : Line F)
    (hl : ¬ Incident (basePoint : Point F) l) :
    Fintype.card (AssignedPoint l) ≤ 2 := by
  classical
  rw [Fintype.card_coe]
  exact assignedFiber_card_le_two l hl

lemma assignedPoint_incident (l : Line F) (x : AssignedPoint l) :
    Incident x.1.1 l := by
  have hx := (mem_assignedFiber_iff l x.1).mp x.2
  simpa only [hx] using incident_assignedLine x.1.2

/-- Non-base points on a line.  For a line avoiding the base point this is
the whole `K+1` point line. -/
noncomputable def smallLinePoints (l : Line F) : Finset (BasePoint F) :=
  Finset.univ.filter fun x ↦ Incident x.1 l

@[simp] lemma mem_smallLinePoints_iff (l : Line F) (x : BasePoint F) :
    x ∈ smallLinePoints l ↔ Incident x.1 l := by
  simp [smallLinePoints]

lemma card_smallLinePoints (l : Line F)
    (hl : ¬ Incident (basePoint : Point F) l) :
    (smallLinePoints l).card = Fintype.card F + 1 := by
  classical
  let e : {x : BasePoint F // Incident x.1 l} ≃
      {p : Point F // Incident p l} :=
    { toFun := fun x ↦ ⟨x.1.1, x.2⟩
      invFun := fun p ↦ ⟨⟨p.1, by
        intro hp
        apply hl
        simpa only [hp] using p.2⟩, p.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    (smallLinePoints l).card =
        Fintype.card {x : BasePoint F // Incident x.1 l} := by
      simpa [smallLinePoints] using
        (Fintype.card_subtype (fun x : BasePoint F ↦ Incident x.1 l)).symm
    _ = Fintype.card {p : Point F // Incident p l} := Fintype.card_congr e
    _ = (pointsOnLine l).card := by
      simpa [pointsOnLine] using
        Fintype.card_subtype (fun p : Point F ↦ Incident p l)
    _ = Fintype.card F + 1 := card_pointsOnLine l

lemma assignedFiber_subset_smallLinePoints (l : Line F) :
    assignedFiber l ⊆ smallLinePoints l := by
  intro x hx
  apply (mem_smallLinePoints_iff l x).mpr
  have hxline := (mem_assignedFiber_iff l x).mp hx
  rw [← hxline]
  exact incident_assignedLine x.2

/-- Ordinary positions of a small template: the assigned positions have
been removed from the line. -/
noncomputable def ordinaryPoints (l : Line F) : Finset (BasePoint F) :=
  smallLinePoints l \ assignedFiber l

abbrev OrdinaryPoint (l : Line F) := {x : BasePoint F // x ∈ ordinaryPoints l}

lemma card_ordinaryPoint_le (l : Line F)
    (hl : ¬ Incident (basePoint : Point F) l) :
    Fintype.card (OrdinaryPoint l) ≤ Fintype.card F := by
  classical
  have hsub := assignedFiber_subset_smallLinePoints l
  have hpos : 0 < (assignedFiber l).card :=
    Finset.card_pos.mpr (assignedFiber_nonempty l hl)
  rw [Fintype.card_coe, ordinaryPoints, Finset.card_sdiff_of_subset hsub,
    card_smallLinePoints l hl]
  omega

/-- Number of packet labels allotted to each exceptional point.  For
`q = 3 (mod 4)` it is `(q+1)/4`. -/
def packetCount (q : ℕ) : ℕ := q / 4 + 1

lemma packetCount_pos (q : ℕ) : 0 < packetCount q := by
  simp [packetCount]

lemma q_le_four_packetCount (q : ℕ) : q ≤ 4 * packetCount q := by
  have hmod := Nat.mod_lt q (by norm_num : 0 < 4)
  have hdiv := Nat.div_add_mod q 4
  unfold packetCount
  omega

lemma two_packetCount_le_sub_of_mod_three {q K : ℕ}
    (hqmod : q % 4 = 3) (hqK : 2 * K + 1 ≤ q) :
    2 * packetCount q ≤ q - K := by
  have hdiv := Nat.div_add_mod q 4
  unfold packetCount
  omega

/-- Exceptional columns consist of one packet label for each point in the
assignment fibre. -/
abbrev ExceptionColumn (l : Line F) (q : ℕ) :=
  AssignedPoint l × Fin (packetCount q)

/-- All retained affine columns in a small template. -/
abbrev SmallColumn (l : Line F) (q : ℕ) :=
  OrdinaryPoint l ⊕ ExceptionColumn l q

lemma card_smallColumn_le (l : Line F) {q : ℕ}
    (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q) :
    Fintype.card (SmallColumn l q) ≤ q := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have hord := card_ordinaryPoint_le l hl
  have hass := card_assignedPoint_le_two l hl
  have hpack := two_packetCount_le_sub_of_mod_three hqmod hqK
  have hex : Fintype.card (AssignedPoint l) * packetCount q ≤
      2 * packetCount q := Nat.mul_le_mul_right _ hass
  omega

/-- Inject all ordinary and exceptional columns into distinct finite slopes
of the prime field. -/
noncomputable def smallColumnEmbedding (l : Line F) {q : ℕ}
    (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q) :
    SmallColumn l q ↪ Fin q where
  toFun c := ⟨(Fintype.equivFin (SmallColumn l q) c).1,
    (Fintype.equivFin (SmallColumn l q) c).2.trans_le
      (card_smallColumn_le l hl hqmod hqK)⟩
  inj' := by
    intro c d h
    apply (Fintype.equivFin (SmallColumn l q)).injective
    apply Fin.ext
    exact congrArg (fun z : Fin q ↦ z.1) h

/-- Round-robin grouping of the `q` compressed pieces into
`packetCount q` packets. -/
def groupFour (q : ℕ) : Fin q → Fin (packetCount q) := fun i ↦
  ⟨i.1 % packetCount q, Nat.mod_lt _ (packetCount_pos q)⟩

noncomputable def groupFourFiber (q : ℕ) (e : Fin (packetCount q)) :
    Finset (Fin q) := Finset.univ.filter fun i ↦ groupFour q i = e

@[simp] lemma mem_groupFourFiber_iff (q : ℕ)
    (e : Fin (packetCount q)) (i : Fin q) :
    i ∈ groupFourFiber q e ↔ groupFour q i = e := by
  simp [groupFourFiber]

lemma card_groupFourFiber_le_four (q : ℕ)
    (e : Fin (packetCount q)) :
    (groupFourFiber q e).card ≤ 4 := by
  classical
  let S := {i : Fin q // i ∈ groupFourFiber q e}
  let f : S → Fin 4 := fun i ↦
    ⟨i.1.1 / packetCount q, by
      apply (Nat.div_lt_iff_lt_mul (packetCount_pos q)).2
      exact i.1.2.trans_le (q_le_four_packetCount q)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have hquot : i.1.1 / packetCount q = j.1.1 / packetCount q :=
      Fin.ext_iff.mp hij
    have hiMem := (mem_groupFourFiber_iff q e i.1).mp i.2
    have hjMem := (mem_groupFourFiber_iff q e j.1).mp j.2
    have hrem : i.1.1 % packetCount q = j.1.1 % packetCount q := by
      exact congrArg Fin.val (hiMem.trans hjMem.symm)
    calc
      i.1.1 = i.1.1 % packetCount q + packetCount q *
          (i.1.1 / packetCount q) := (Nat.mod_add_div _ _).symm
      _ = j.1.1 % packetCount q + packetCount q *
          (j.1.1 / packetCount q) := by rw [hrem, hquot]
      _ = j.1.1 := Nat.mod_add_div _ _
  have hcard : Fintype.card S ≤ Fintype.card (Fin 4) :=
    Fintype.card_le_of_injective f hf
  rw [← Fintype.card_coe]
  change Fintype.card S ≤ 4
  simpa using hcard

/-- The finite-field element represented by a compressed-piece index. -/
noncomputable def indexValue (q : ℕ) (hqmod : q % 4 = 3) : Fin q ≃ ZMod q := by
  letI : NeZero q := ⟨by omega⟩
  exact (finCongr (ZMod.card q).symm).trans (Fintype.equivFin (ZMod q)).symm

/-- The finite slope assigned injectively to a retained small-template
column. -/
noncomputable def smallSlope (l : Line F) {q : ℕ}
    (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (c : SmallColumn l q) : ZMod q :=
  indexValue q hqmod (smallColumnEmbedding l hl hqmod hqK c)

lemma smallSlope_injective (l : Line F) {q : ℕ}
    (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q) :
    Function.Injective (smallSlope l hl hqmod hqK) := by
  intro c d h
  apply (smallColumnEmbedding l hl hqmod hqK).injective
  exact (indexValue q hqmod).injective h

/-- The affine-array value in a finite-slope column. -/
def affineValue {q : ℕ} (row : ZMod q × ZMod q) (slope : ZMod q) :
    ZMod q := row.1 + slope * row.2

/-- The edge labels.  One summand is active on a base line and the other on
a line avoiding the base point; labels in the inactive summand denote the
empty edge. -/
abbrev Edge (F : Type*) [Zero F] (q t : ℕ) :=
  Line F × ((Fin t × Fin t) ⊕ (ZMod q × ZMod q))

/-- The compressed-piece index of a local vertex on a specified side. -/
def compressedIndex {q t : ℕ} (D : Expander.System 100 t)
    (hq : q ≤ t) (ht : t ≤ 2 * q) (side : Bool)
    (v : Fin 100 × Fin t) : Fin q :=
  index q t hq ht (blockIndex D side v)

/-- The unique retained column which contains a given local vertex in a
small template. -/
def smallVertexColumn {q t : ℕ} (D : Expander.System 100 t)
    (a : Labeling F) (l : Line F)
    (hl : ¬ Incident (basePoint : Point F) l)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (x : BasePoint F) (hxl : Incident x.1 l) (v : Fin 100 × Fin t) :
    SmallColumn l q := by
  let side := a l ⟨x.1, hxl⟩
  let c := compressedIndex D hq ht side v
  by_cases hx : assignedLine x.1 = l
  · exact Sum.inr
      (⟨x, (mem_assignedFiber_iff l x).mpr hx⟩, groupFour q c)
  · exact Sum.inl ⟨x, Finset.mem_sdiff.mpr
      ⟨(mem_smallLinePoints_iff l x).mpr hxl,
        by simpa [mem_assignedFiber_iff] using hx⟩⟩

lemma smallVertexColumn_point {q t : ℕ} (D : Expander.System 100 t)
    (a : Labeling F) (l : Line F)
    (hl : ¬ Incident (basePoint : Point F) l)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (x : BasePoint F) (hxl : Incident x.1 l) (v : Fin 100 × Fin t) :
    (smallVertexColumn D a l hl hq ht x hxl v).elim
        (fun z ↦ z.1) (fun z ↦ z.1.1) = x := by
  simp only [smallVertexColumn]
  split <;> rfl

/-- The symbol prescribed by the local vertex in its retained column. -/
noncomputable def smallVertexTarget {q t : ℕ}
    (D : Expander.System 100 t) (a : Labeling F) (l : Line F)
    (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (x : BasePoint F) (hxl : Incident x.1 l) (v : Fin 100 × Fin t) :
    ZMod q :=
  let c := smallVertexColumn D a l hl hq ht x hxl v
  match c with
  | Sum.inl _ =>
      indexValue q hqmod (compressedIndex D hq ht (a l ⟨x.1, hxl⟩) v)
  | Sum.inr _ => (smallSlope l hl hqmod hqK c) ^ 2

/-- The global indexed hypergraph. -/
noncomputable def hypergraph {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q) :
    IndexedHypergraph (Vertex F t) (Edge F q t) where
  edge e := Finset.univ.filter fun z ↦
    if hl : Incident (basePoint : Point F) e.1 then
      match e.2 with
      | Sum.inl row =>
          if hzl : Incident z.1.1 e.1 then
            blockIndex D (a e.1 ⟨z.1.1, hzl⟩) z.2 =
              A.entry row
                ((largePointEquiv e.1 hl
                  (toLargePoint e.1 hl z.1 hzl)).castSucc)
          else False
      | Sum.inr _ => False
    else
      match e.2 with
      | Sum.inl _ => False
      | Sum.inr row =>
          if hzl : Incident z.1.1 e.1 then
            affineValue row
                (smallSlope e.1 hl hqmod hqK
                  (smallVertexColumn D a e.1 hl hq ht z.1 hzl z.2)) =
              smallVertexTarget D a e.1 hl hqmod hqK hq ht z.1 hzl z.2
          else False

@[simp] lemma mem_hypergraph_large {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (l : Line F) (hl : Incident (basePoint : Point F) l)
    (row : Fin t × Fin t) (z : Vertex F t) :
    z ∈ (hypergraph D a A hqmod hqK hq ht).edge (l, Sum.inl row) ↔
      ∃ hzl : Incident z.1.1 l,
        blockIndex D (a l ⟨z.1.1, hzl⟩) z.2 =
          A.entry row
            ((largePointEquiv l hl (toLargePoint l hl z.1 hzl)).castSucc) := by
  simp only [hypergraph, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [dif_pos hl]
  constructor
  · split <;> simp_all
  · rintro ⟨hzl, h⟩
    simp [hzl, h]

@[simp] lemma mem_hypergraph_small {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (l : Line F) (hl : ¬ Incident (basePoint : Point F) l)
    (row : ZMod q × ZMod q) (z : Vertex F t) :
    z ∈ (hypergraph D a A hqmod hqK hq ht).edge (l, Sum.inr row) ↔
      ∃ hzl : Incident z.1.1 l,
        affineValue row
            (smallSlope l hl hqmod hqK
              (smallVertexColumn D a l hl hq ht z.1 hzl z.2)) =
          smallVertexTarget D a l hl hqmod hqK hq ht z.1 hzl z.2 := by
  simp only [hypergraph, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [dif_neg hl]
  constructor
  · split <;> simp_all
  · rintro ⟨hzl, h⟩
    simp [hzl, h]

@[simp] lemma hypergraph_wrong_large_empty {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (l : Line F) (hl : ¬ Incident (basePoint : Point F) l)
    (row : Fin t × Fin t) :
    (hypergraph D a A hqmod hqK hq ht).edge (l, Sum.inl row) = ∅ := by
  ext z
  simp [hypergraph, hl]

@[simp] lemma hypergraph_wrong_small_empty {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (l : Line F) (hl : Incident (basePoint : Point F) l)
    (row : ZMod q × ZMod q) :
    (hypergraph D a A hqmod hqK hq ht).edge (l, Sum.inr row) = ∅ := by
  ext z
  simp [hypergraph, hl]

lemma exists_affine_row {q : ℕ} [Fact q.Prime]
    {s₁ s₂ y₁ y₂ : ZMod q} (hs : s₁ ≠ s₂) :
    ∃ row : ZMod q × ZMod q,
      affineValue row s₁ = y₁ ∧ affineValue row s₂ = y₂ := by
  let e := OrthogonalArray.affinePairEquiv s₁ s₂ hs
  refine ⟨e.symm (y₁, y₂), ?_⟩
  have h := e.apply_symm_apply (y₁, y₂)
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

lemma base_not_incident_assignedLine (x : BasePoint F) :
    ¬ Incident (basePoint : Point F) (assignedLine x.1) := by
  rcases x with ⟨x, hx⟩
  rcases x with xy | s
  · rcases xy with ⟨u, v⟩
    simp [basePoint, assignedLine, Incident, verticalInfinity, graph]
  · rcases s with m | u
    · simp [basePoint, assignedLine, Incident, verticalInfinity, graph]
    · exact (hx rfl).elim

lemma smallVertexColumn_of_assigned {q t : ℕ}
    (D : Expander.System 100 t) (a : Labeling F) (l : Line F)
    (hl : ¬ Incident (basePoint : Point F) l)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (x : BasePoint F) (hxl : Incident x.1 l) (hx : assignedLine x.1 = l)
    (v : Fin 100 × Fin t) :
    smallVertexColumn D a l hl hq ht x hxl v =
      Sum.inr
        (⟨x, (mem_assignedFiber_iff l x).mpr hx⟩,
          groupFour q
            (compressedIndex D hq ht (a l ⟨x.1, hxl⟩) v)) := by
  simp [smallVertexColumn, hx, compressedIndex]

lemma smallVertexTarget_of_assigned {q t : ℕ}
    (D : Expander.System 100 t) (a : Labeling F) (l : Line F)
    (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (x : BasePoint F) (hxl : Incident x.1 l) (hx : assignedLine x.1 = l)
    (v : Fin 100 × Fin t) :
    smallVertexTarget D a l hl hqmod hqK hq ht x hxl v =
      (smallSlope l hl hqmod hqK
        (smallVertexColumn D a l hl hq ht x hxl v)) ^ 2 := by
  rw [smallVertexTarget]
  rw [smallVertexColumn_of_assigned D a l hl hq ht x hxl hx v]

/-- Every two distinct global vertices occur together in one template edge. -/
lemma hypergraph_pairCovered {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q) :
    (hypergraph D a A hqmod hqK hq ht).PairCovered := by
  intro z w hzw
  by_cases hxw : z.1 = w.1
  · have hvw : z.2 ≠ w.2 := by
      intro h
      exact hzw (Prod.ext hxw h)
    have hw : (z.1, w.2) = w := Prod.ext hxw rfl
    let l := assignedLine z.1.1
    have hl : ¬ Incident (basePoint : Point F) l :=
      base_not_incident_assignedLine z.1
    have hzl : Incident z.1.1 l := incident_assignedLine z.1.2
    let c₁ := smallVertexColumn D a l hl hq ht z.1 hzl z.2
    let c₂ := smallVertexColumn D a l hl hq ht z.1 hzl w.2
    let s₁ := smallSlope l hl hqmod hqK c₁
    let s₂ := smallSlope l hl hqmod hqK c₂
    let y₁ := smallVertexTarget D a l hl hqmod hqK hq ht z.1 hzl z.2
    let y₂ := smallVertexTarget D a l hl hqmod hqK hq ht z.1 hzl w.2
    by_cases hc : c₁ = c₂
    · have hy : y₁ = s₁ ^ 2 := by
        dsimp [y₁, s₁, c₁, l]
        exact smallVertexTarget_of_assigned D a (assignedLine z.1.1) hl
          hqmod hqK hq ht z.1 hzl rfl z.2
      have hy₂ : y₂ = s₁ ^ 2 := by
        have htarget := smallVertexTarget_of_assigned D a
          (assignedLine z.1.1) hl hqmod hqK hq ht z.1 hzl rfl w.2
        dsimp [y₂, s₁, c₁, l]
        rw [htarget]
        congr 1
        exact congrArg (smallSlope (assignedLine z.1.1) hl hqmod hqK) hc.symm
      let row : ZMod q × ZMod q := (s₁ ^ 2, 0)
      refine ⟨(l, Sum.inr row), ?_, ?_⟩
      · apply (mem_hypergraph_small D a A hqmod hqK hq ht l hl row z).2
        refine ⟨hzl, ?_⟩
        simp [row, affineValue, y₁, s₁, c₁, hy]
      · rw [← hw]
        apply (mem_hypergraph_small D a A hqmod hqK hq ht l hl row
          (z.1, w.2)).2
        refine ⟨hzl, ?_⟩
        simp [row, affineValue, y₂, s₁, s₂, c₁, c₂, hc, hy₂]
    · have hs : s₁ ≠ s₂ := by
        exact fun h ↦ hc (smallSlope_injective l hl hqmod hqK h)
      obtain ⟨row, hr₁, hr₂⟩ := exists_affine_row hs
      refine ⟨(l, Sum.inr row), ?_, ?_⟩
      · apply (mem_hypergraph_small D a A hqmod hqK hq ht l hl row z).2
        exact ⟨hzl, by simpa [s₁, y₁, c₁] using hr₁⟩
      · rw [← hw]
        apply (mem_hypergraph_small D a A hqmod hqK hq ht l hl row
          (z.1, w.2)).2
        exact ⟨hzl, by simpa [s₂, y₂, c₂] using hr₂⟩
  · let l := lineThroughPoints z.1.1 w.1.1
    have hzl : Incident z.1.1 l := lineThroughPoints_incident_left _ _
    have hwl : Incident w.1.1 l := lineThroughPoints_incident_right _ _
    by_cases hl : Incident (basePoint : Point F) l
    · let i := (largePointEquiv l hl (toLargePoint l hl z.1 hzl)).castSucc
      let j := (largePointEquiv l hl (toLargePoint l hl w.1 hwl)).castSucc
      have hij : i ≠ j := by
        intro h
        have hfin : largePointEquiv l hl (toLargePoint l hl z.1 hzl) =
            largePointEquiv l hl (toLargePoint l hl w.1 hwl) := by
          exact Fin.castSucc_injective _ h
        have hp := (largePointEquiv l hl).injective hfin
        apply hxw
        apply Subtype.ext
        exact congrArg (fun u : LargePoint l hl ↦ u.1.1) hp
      let bx := blockIndex D (a l ⟨z.1.1, hzl⟩) z.2
      let bw := blockIndex D (a l ⟨w.1.1, hwl⟩) w.2
      obtain ⟨row, hrow⟩ := (A.pair_bijective hij).2 (bx, bw)
      refine ⟨(l, Sum.inl row), ?_, ?_⟩
      · apply (mem_hypergraph_large D a A hqmod hqK hq ht l hl row z).2
        exact ⟨hzl, by simpa [i, bx] using (congrArg Prod.fst hrow).symm⟩
      · apply (mem_hypergraph_large D a A hqmod hqK hq ht l hl row w).2
        exact ⟨hwl, by simpa [j, bw] using (congrArg Prod.snd hrow).symm⟩
    · let c₁ := smallVertexColumn D a l hl hq ht z.1 hzl z.2
      let c₂ := smallVertexColumn D a l hl hq ht w.1 hwl w.2
      have hc : c₁ ≠ c₂ := by
        intro h
        have hp := congrArg
          (fun c : SmallColumn l q ↦ c.elim (fun u ↦ u.1) (fun u ↦ u.1.1)) h
        have hz := smallVertexColumn_point D a l hl hq ht z.1 hzl z.2
        have hw := smallVertexColumn_point D a l hl hq ht w.1 hwl w.2
        exact hxw (hz.symm.trans (hp.trans hw))
      let s₁ := smallSlope l hl hqmod hqK c₁
      let s₂ := smallSlope l hl hqmod hqK c₂
      have hs : s₁ ≠ s₂ := fun h ↦
        hc (smallSlope_injective l hl hqmod hqK h)
      let y₁ := smallVertexTarget D a l hl hqmod hqK hq ht z.1 hzl z.2
      let y₂ := smallVertexTarget D a l hl hqmod hqK hq ht w.1 hwl w.2
      obtain ⟨row, hr₁, hr₂⟩ := exists_affine_row hs
      refine ⟨(l, Sum.inr row), ?_, ?_⟩
      · apply (mem_hypergraph_small D a A hqmod hqK hq ht l hl row z).2
        exact ⟨hzl, by simpa [s₁, y₁, c₁] using hr₁⟩
      · apply (mem_hypergraph_small D a A hqmod hqK hq ht l hl row w).2
        exact ⟨hwl, by simpa [s₂, y₂, c₂] using hr₂⟩

/-- One affine equation in two variables has exactly `q` solutions. -/
noncomputable def affineFiberEquiv {q : ℕ} [Fact q.Prime]
    (s y : ZMod q) : ZMod q ≃
      {row : ZMod q × ZMod q // affineValue row s = y} where
  toFun v := ⟨(y - s * v, v), by simp [affineValue]⟩
  invFun row := row.1.2
  left_inv _ := rfl
  right_inv row := by
    apply Subtype.ext
    apply Prod.ext
    · have h := row.2
      dsimp [affineValue] at h
      dsimp
      calc
        y - s * row.1.2 = (row.1.1 + s * row.1.2) - s * row.1.2 :=
          congrArg (fun z : ZMod q ↦ z - s * row.1.2) h.symm
        _ = row.1.1 := by ring
    · rfl

lemma card_edgeTags_large {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (l : Line F) (hl : Incident (basePoint : Point F) l)
    (z : Vertex F t) (hzl : Incident z.1.1 l) :
    Fintype.card {tag : (Fin t × Fin t) ⊕ (ZMod q × ZMod q) //
      z ∈ (hypergraph D a A hqmod hqK hq ht).edge (l, tag)} = t := by
  classical
  let i := largePointEquiv l hl (toLargePoint l hl z.1 hzl)
  let y := blockIndex D (a l ⟨z.1.1, hzl⟩) z.2
  let e : {tag : (Fin t × Fin t) ⊕ (ZMod q × ZMod q) //
      z ∈ (hypergraph D a A hqmod hqK hq ht).edge (l, tag)} ≃
      {row : Fin t × Fin t // row ∈ A.fiber i y} := by
    refine
      { toFun := ?_
        invFun := ?_
        left_inv := ?_
        right_inv := ?_ }
    · intro tag
      rcases tag with ⟨row | row, hrow⟩
      · refine ⟨row, (A.mem_fiber_iff i y row).mpr ?_⟩
        obtain ⟨hzl', h⟩ :=
          (mem_hypergraph_large D a A hqmod hqK hq ht l hl row z).mp hrow
        simpa [i, y] using h.symm
      · have hempty := hypergraph_wrong_small_empty D a A hqmod hqK hq ht
          l hl row
        rw [hempty] at hrow
        exact (by simpa using hrow)
    · intro row
      refine ⟨Sum.inl row.1, ?_⟩
      apply (mem_hypergraph_large D a A hqmod hqK hq ht l hl row.1 z).2
      refine ⟨hzl, ?_⟩
      simpa [i, y] using (A.mem_fiber_iff i y row.1).mp row.2 |>.symm
    · rintro ⟨row | row, hrow⟩
      · rfl
      · have hempty := hypergraph_wrong_small_empty D a A hqmod hqK hq ht
          l hl row
        rw [hempty] at hrow
        simp at hrow
    · intro row
      rfl
  rw [Fintype.card_congr e, Fintype.card_coe]
  exact A.fiber_card i y

lemma card_edgeTags_small {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (l : Line F) (hl : ¬ Incident (basePoint : Point F) l)
    (z : Vertex F t) (hzl : Incident z.1.1 l) :
    Fintype.card {tag : (Fin t × Fin t) ⊕ (ZMod q × ZMod q) //
      z ∈ (hypergraph D a A hqmod hqK hq ht).edge (l, tag)} = q := by
  classical
  let c := smallVertexColumn D a l hl hq ht z.1 hzl z.2
  let s := smallSlope l hl hqmod hqK c
  let y := smallVertexTarget D a l hl hqmod hqK hq ht z.1 hzl z.2
  let e : {tag : (Fin t × Fin t) ⊕ (ZMod q × ZMod q) //
      z ∈ (hypergraph D a A hqmod hqK hq ht).edge (l, tag)} ≃
      {row : ZMod q × ZMod q // affineValue row s = y} := by
    refine
      { toFun := ?_
        invFun := ?_
        left_inv := ?_
        right_inv := ?_ }
    · intro tag
      rcases tag with ⟨row | row, hrow⟩
      · have hempty := hypergraph_wrong_large_empty D a A hqmod hqK hq ht
          l hl row
        rw [hempty] at hrow
        exact (by simpa using hrow)
      · refine ⟨row, ?_⟩
        obtain ⟨hzl', h⟩ :=
          (mem_hypergraph_small D a A hqmod hqK hq ht l hl row z).mp hrow
        simpa [c, s, y] using h
    · intro row
      refine ⟨Sum.inr row.1, ?_⟩
      apply (mem_hypergraph_small D a A hqmod hqK hq ht l hl row.1 z).2
      exact ⟨hzl, by simpa [c, s, y] using row.2⟩
    · rintro ⟨row | row, hrow⟩
      · have hempty := hypergraph_wrong_large_empty D a A hqmod hqK hq ht
          l hl row
        rw [hempty] at hrow
        simp at hrow
      · rfl
    · intro row
      rfl
  calc
    Fintype.card {tag : (Fin t × Fin t) ⊕ (ZMod q × ZMod q) //
        z ∈ (hypergraph D a A hqmod hqK hq ht).edge (l, tag)} =
        Fintype.card {row : ZMod q × ZMod q // affineValue row s = y} :=
      Fintype.card_congr e
    _ = Fintype.card (ZMod q) :=
      (Fintype.card_congr (affineFiberEquiv s y)).symm
    _ = q := ZMod.card q

lemma card_edgeTags_not_incident {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (l : Line F) (z : Vertex F t) (hzl : ¬ Incident z.1.1 l) :
    Fintype.card {tag : (Fin t × Fin t) ⊕ (ZMod q × ZMod q) //
      z ∈ (hypergraph D a A hqmod hqK hq ht).edge (l, tag)} = 0 := by
  classical
  rw [Fintype.card_eq_zero_iff]
  refine ⟨?_⟩
  rintro ⟨tag, htag⟩
  rcases tag with row | row
  · by_cases hl : Incident (basePoint : Point F) l
    · obtain ⟨h, _⟩ :=
        (mem_hypergraph_large D a A hqmod hqK hq ht l hl row z).mp htag
      exact (hzl h).elim
    · rw [hypergraph_wrong_large_empty D a A hqmod hqK hq ht l hl row] at htag
      simpa using htag
  · by_cases hl : Incident (basePoint : Point F) l
    · rw [hypergraph_wrong_small_empty D a A hqmod hqK hq ht l hl row] at htag
      simpa using htag
    · obtain ⟨h, _⟩ :=
        (mem_hypergraph_small D a A hqmod hqK hq ht l hl row z).mp htag
      exact (hzl h).elim

lemma incident_card_as_line_sum {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q) (z : Vertex F t) :
    ((hypergraph D a A hqmod hqK hq ht).incident z).card =
      ∑ l : Line F,
        Fintype.card {tag : (Fin t × Fin t) ⊕ (ZMod q × ZMod q) //
          z ∈ (hypergraph D a A hqmod hqK hq ht).edge (l, tag)} := by
  classical
  let H := hypergraph D a A hqmod hqK hq ht
  let e : {e : Edge F q t // z ∈ H.edge e} ≃
      Σ l : Line F,
        {tag : (Fin t × Fin t) ⊕ (ZMod q × ZMod q) //
          z ∈ H.edge (l, tag)} :=
    { toFun := fun u ↦ ⟨u.1.1, u.1.2, u.2⟩
      invFun := fun u ↦ ⟨(u.1, u.2.1), u.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let eIncident : ↥(H.incident z) ≃ {e : Edge F q t // z ∈ H.edge e} :=
    { toFun := fun u ↦ ⟨u.1, (IndexedHypergraph.mem_incident H z u.1).mp u.2⟩
      invFun := fun u ↦ ⟨u.1, (IndexedHypergraph.mem_incident H z u.1).mpr u.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    (H.incident z).card = Fintype.card {e : Edge F q t // z ∈ H.edge e} := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr eIncident
    _ = Fintype.card (Σ l : Line F,
        {tag : (Fin t × Fin t) ⊕ (ZMod q × ZMod q) //
          z ∈ H.edge (l, tag)}) := Fintype.card_congr e
    _ = ∑ l : Line F,
        Fintype.card {tag : (Fin t × Fin t) ⊕ (ZMod q × ZMod q) //
          z ∈ H.edge (l, tag)} := Fintype.card_sigma

lemma base_lines_through_filter (x : BasePoint F) :
    (linesThrough x.1).filter
        (fun l ↦ Incident (basePoint : Point F) l) =
      {lineThroughPoints (basePoint : Point F) x.1} := by
  classical
  ext l
  simp only [Finset.mem_filter, mem_linesThrough_iff,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hxl, hbase⟩
    apply line_unique_of_two_points (Ne.symm x.2) hbase hxl
      (lineThroughPoints_incident_left _ _)
      (lineThroughPoints_incident_right _ _)
  · rintro rfl
    exact ⟨lineThroughPoints_incident_right _ _,
      lineThroughPoints_incident_left _ _⟩

lemma line_degree_sum (x : BasePoint F) (q t : ℕ) :
    (∑ l : Line F,
      if Incident x.1 l then
        if Incident (basePoint : Point F) l then t else q
      else 0) = t + Fintype.card F * q := by
  classical
  let S := linesThrough x.1
  have hfilter : S.filter (fun l ↦ Incident (basePoint : Point F) l) =
      {lineThroughPoints (basePoint : Point F) x.1} :=
    base_lines_through_filter x
  have hScard : S.card = Fintype.card F + 1 := card_linesThrough x.1
  have hnotcard :
      (S.filter fun l ↦ ¬ Incident (basePoint : Point F) l).card =
        Fintype.card F := by
    have hparts := Finset.card_filter_add_card_filter_not
      (s := S) (p := fun l ↦ Incident (basePoint : Point F) l)
    rw [hfilter] at hparts
    simp only [Finset.card_singleton] at hparts
    omega
  calc
    (∑ l : Line F,
      if Incident x.1 l then
        if Incident (basePoint : Point F) l then t else q
      else 0) =
        ∑ l ∈ S,
          if Incident (basePoint : Point F) l then t else q := by
      simp [S, linesThrough, Finset.sum_filter]
    _ = (∑ l ∈ S.filter (fun l ↦ Incident (basePoint : Point F) l),
          if Incident (basePoint : Point F) l then t else q) +
        ∑ l ∈ S.filter (fun l ↦ ¬ Incident (basePoint : Point F) l),
          if Incident (basePoint : Point F) l then t else q := by
      exact (Finset.sum_filter_add_sum_filter_not S
        (fun l ↦ Incident (basePoint : Point F) l)
        (fun l ↦ if Incident (basePoint : Point F) l then t else q)).symm
    _ = t + Fintype.card F * q := by
      rw [hfilter]
      simp only [Finset.sum_singleton, lineThroughPoints_incident_left,
        if_pos]
      have hsum :
          (∑ l ∈ S.filter (fun l ↦ ¬ Incident (basePoint : Point F) l),
            if Incident (basePoint : Point F) l then t else q) =
            (S.filter fun l ↦ ¬ Incident (basePoint : Point F) l).card * q := by
        apply Finset.sum_const_nat
        intro l hl
        exact if_neg (Finset.mem_filter.mp hl).2
      rw [hsum, hnotcard]

lemma hypergraph_regular {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q) :
    (hypergraph D a A hqmod hqK hq ht).IsRegular
      (t + Fintype.card F * q) := by
  intro z
  rw [incident_card_as_line_sum D a A hqmod hqK hq ht z]
  have hlocal : ∀ l : Line F,
      Fintype.card {tag : (Fin t × Fin t) ⊕ (ZMod q × ZMod q) //
        z ∈ (hypergraph D a A hqmod hqK hq ht).edge (l, tag)} =
      if Incident z.1.1 l then
        if Incident (basePoint : Point F) l then t else q
      else 0 := by
    intro l
    by_cases hzl : Incident z.1.1 l
    · by_cases hl : Incident (basePoint : Point F) l
      · simpa [hzl, hl] using
          card_edgeTags_large D a A hqmod hqK hq ht l hl z hzl
      · simpa [hzl, hl] using
          card_edgeTags_small D a A hqmod hqK hq ht l hl z hzl
    · simpa [hzl] using
        card_edgeTags_not_incident D a A hqmod hqK hq ht l z hzl
  simp_rw [hlocal]
  exact line_degree_sum z.1 q t

/-- Edge labels belonging to one projective-line template. -/
def templateSlice {q t : ℕ} (C : Finset (Edge F q t)) (l : Line F) :
    Finset (Edge F q t) := C.filter fun e ↦ e.1 = l

@[simp] lemma mem_templateSlice_iff {q t : ℕ}
    (C : Finset (Edge F q t)) (l : Line F) (e : Edge F q t) :
    e ∈ templateSlice C l ↔ e ∈ C ∧ e.1 = l := by
  simp [templateSlice]

/-- All nonempty-branch labels of one template. -/
noncomputable def activeTemplate {q t : ℕ} [Fact q.Prime] (l : Line F) :
    Finset (Edge F q t) :=
  if Incident (basePoint : Point F) l then
    (Finset.univ : Finset (Fin t × Fin t)).image fun row ↦ (l, Sum.inl row)
  else
    (Finset.univ : Finset (ZMod q × ZMod q)).image fun row ↦ (l, Sum.inr row)

lemma activeTemplate_card_large {q t : ℕ} [Fact q.Prime] (l : Line F)
    (hl : Incident (basePoint : Point F) l) :
    (activeTemplate (q := q) (t := t) l).card = t ^ 2 := by
  rw [activeTemplate, if_pos hl, Finset.card_image_iff.mpr]
  · simp [pow_two]
  · intro x _ y _ h
    simpa using h

lemma activeTemplate_card_small {q t : ℕ} [Fact q.Prime] (l : Line F)
    (hl : ¬ Incident (basePoint : Point F) l) :
    (activeTemplate (q := q) (t := t) l).card = q ^ 2 := by
  rw [activeTemplate, if_neg hl, Finset.card_image_iff.mpr]
  · simp [pow_two, ZMod.card]
  · intro x _ y _ h
    simpa using h

lemma activeTemplate_first {q t : ℕ} [Fact q.Prime] (l : Line F) {e : Edge F q t}
    (he : e ∈ activeTemplate (q := q) (t := t) l) : e.1 = l := by
  by_cases hl : Incident (basePoint : Point F) l
  · rw [activeTemplate, if_pos hl] at he
    obtain ⟨row, _, rfl⟩ := Finset.mem_image.mp he
    rfl
  · rw [activeTemplate, if_neg hl] at he
    obtain ⟨row, _, rfl⟩ := Finset.mem_image.mp he
    rfl

/-- A fixed internal cover of a base-line template. -/
noncomputable def largeCanonical {q t : ℕ}
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (ht : 0 < t) (l : Line F) : Finset (Edge F q t) :=
  (A.parallelClass ⟨0, ht⟩).image fun row ↦ (l, Sum.inl row)

lemma largeCanonical_card {q t : ℕ}
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (ht : 0 < t) (l : Line F) :
    (largeCanonical (q := q) A ht l).card = t := by
  rw [largeCanonical, Finset.card_image_iff.mpr]
  · exact A.parallelClass_card Fintype.card_pos ⟨0, ht⟩
  · intro x _ y _ h
    simpa using h

lemma largeCanonical_subset_active {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (ht : 0 < t) (l : Line F)
    (hl : Incident (basePoint : Point F) l) :
    largeCanonical (q := q) A ht l ⊆ activeTemplate l := by
  intro e he
  obtain ⟨row, _, rfl⟩ := Finset.mem_image.mp he
  rw [activeTemplate, if_pos hl]
  exact Finset.mem_image.mpr ⟨row, Finset.mem_univ _, rfl⟩

lemma largeCanonical_covers_on_line {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (htq : t ≤ 2 * q) (ht : 0 < t)
    (l : Line F) (hl : Incident (basePoint : Point F) l)
    (z : Vertex F t) (hzl : Incident z.1.1 l) :
    ∃ e ∈ largeCanonical (q := q) A ht l,
      z ∈ (hypergraph D a A hqmod hqK hq htq).edge e := by
  let i := largePointEquiv l hl (toLargePoint l hl z.1 hzl)
  let y := blockIndex D (a l ⟨z.1.1, hzl⟩) z.2
  obtain ⟨row, hrowClass, hrow⟩ := A.parallelClass_isEdgeCover
    ⟨0, ht⟩ (i, y)
  refine ⟨(l, Sum.inl row), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨row, hrowClass, rfl⟩
  · apply (mem_hypergraph_large D a A hqmod hqK hq htq l hl row z).2
    exact ⟨hzl, by
      simpa [i, y] using (A.mem_hypergraph_edge_iff row i y).mp hrow |>.symm⟩

/-- A fixed `q`-row cover of a small affine template. -/
noncomputable def smallCanonical {q t : ℕ} [Fact q.Prime]
    (l : Line F) : Finset (Edge F q t) :=
  (Finset.univ : Finset (ZMod q)).image fun u ↦
    (l, Sum.inr (u, 0))

lemma smallCanonical_card {q t : ℕ} [Fact q.Prime] (l : Line F) :
    (smallCanonical (q := q) (t := t) l).card = q := by
  rw [smallCanonical, Finset.card_image_iff.mpr]
  · simp [ZMod.card]
  · intro x _ y _ h
    exact congrArg (fun e : Edge F q t ↦ (Sum.elim (fun _ ↦ (0 : ZMod q))
      Prod.fst e.2)) h

lemma smallCanonical_subset_active {q t : ℕ} [Fact q.Prime] (l : Line F)
    (hl : ¬ Incident (basePoint : Point F) l) :
    smallCanonical (q := q) (t := t) l ⊆ activeTemplate l := by
  intro e he
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
  rw [activeTemplate, if_neg hl]
  exact Finset.mem_image.mpr ⟨(u, 0), Finset.mem_univ _, rfl⟩

lemma smallCanonical_covers_on_line {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (l : Line F) (hl : ¬ Incident (basePoint : Point F) l)
    (z : Vertex F t) (hzl : Incident z.1.1 l) :
    ∃ e ∈ smallCanonical (q := q) (t := t) l,
      z ∈ (hypergraph D a A hqmod hqK hq ht).edge e := by
  let y := smallVertexTarget D a l hl hqmod hqK hq ht z.1 hzl z.2
  refine ⟨(l, Sum.inr (y, 0)), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩
  · apply (mem_hypergraph_small D a A hqmod hqK hq ht l hl (y, 0) z).2
    exact ⟨hzl, by simp [affineValue, y]⟩

noncomputable def templateCap (q t : ℕ) (l : Line F) : ℕ :=
  if Incident (basePoint : Point F) l then t else q

noncomputable def canonicalTemplate {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t) (ht : 0 < t)
    (l : Line F) : Finset (Edge F q t) :=
  if Incident (basePoint : Point F) l then largeCanonical A ht l
  else smallCanonical l

lemma canonicalTemplate_card {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t) (ht : 0 < t)
    (l : Line F) :
    (canonicalTemplate (q := q) A ht l).card = templateCap q t l := by
  by_cases hl : Incident (basePoint : Point F) l
  · simp [canonicalTemplate, templateCap, hl, largeCanonical_card]
  · simp [canonicalTemplate, templateCap, hl, smallCanonical_card]

lemma canonicalTemplate_subset_active {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t) (ht : 0 < t)
    (l : Line F) :
    canonicalTemplate (q := q) A ht l ⊆ activeTemplate l := by
  by_cases hl : Incident (basePoint : Point F) l
  · simpa [canonicalTemplate, hl] using
      largeCanonical_subset_active (q := q) A ht l hl
  · simpa [canonicalTemplate, hl] using
      smallCanonical_subset_active (q := q) (t := t) l hl

lemma canonicalTemplate_covers_on_line {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (htq : t ≤ 2 * q) (ht : 0 < t)
    (l : Line F) (z : Vertex F t) (hzl : Incident z.1.1 l) :
    ∃ e ∈ canonicalTemplate (q := q) A ht l,
      z ∈ (hypergraph D a A hqmod hqK hq htq).edge e := by
  by_cases hl : Incident (basePoint : Point F) l
  · simpa [canonicalTemplate, hl] using
      largeCanonical_covers_on_line D a A hqmod hqK hq htq ht l hl z hzl
  · simpa [canonicalTemplate, hl] using
      smallCanonical_covers_on_line D a A hqmod hqK hq htq l hl z hzl

lemma edge_empty_of_not_active {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q) (e : Edge F q t)
    (he : e ∉ activeTemplate e.1) :
    (hypergraph D a A hqmod hqK hq ht).edge e = ∅ := by
  rcases e with ⟨l, row | row⟩
  · by_cases hl : Incident (basePoint : Point F) l
    · exfalso
      apply he
      rw [activeTemplate, if_pos hl]
      exact Finset.mem_image.mpr ⟨row, Finset.mem_univ _, rfl⟩
    · exact hypergraph_wrong_large_empty D a A hqmod hqK hq ht l hl row
  · by_cases hl : Incident (basePoint : Point F) l
    · exact hypergraph_wrong_small_empty D a A hqmod hqK hq ht l hl row
    · exfalso
      apply he
      rw [activeTemplate, if_neg hl]
      exact Finset.mem_image.mpr ⟨row, Finset.mem_univ _, rfl⟩

/-- Remove all inactive (hence empty) edge labels. -/
noncomputable def activePart {q t : ℕ} [Fact q.Prime] (C : Finset (Edge F q t)) :
    Finset (Edge F q t) := C.filter fun e ↦ e ∈ activeTemplate e.1

lemma activePart_subset {q t : ℕ} [Fact q.Prime] (C : Finset (Edge F q t)) :
    activePart C ⊆ C := Finset.filter_subset _ _

lemma activePart_isEdgeCover {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)}
    (hC : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C) :
    (hypergraph D a A hqmod hqK hq ht).IsEdgeCover (activePart C) := by
  intro z
  obtain ⟨e, heC, hze⟩ := hC z
  have heActive : e ∈ activeTemplate e.1 := by
    by_contra he
    rw [edge_empty_of_not_active D a A hqmod hqK hq ht e he] at hze
    simpa using hze
  exact ⟨e, Finset.mem_filter.mpr ⟨heC, heActive⟩, hze⟩

noncomputable def activeSlice {q t : ℕ} [Fact q.Prime]
    (C : Finset (Edge F q t)) (l : Line F) : Finset (Edge F q t) :=
  templateSlice (activePart C) l

lemma activeSlice_subset_activeTemplate {q t : ℕ} [Fact q.Prime]
    (C : Finset (Edge F q t)) (l : Line F) :
    activeSlice C l ⊆ activeTemplate l := by
  intro e he
  have he' := (mem_templateSlice_iff (activePart C) l e).mp he
  have hactive := (Finset.mem_filter.mp he'.1).2
  simpa [he'.2] using hactive

/-- Replace an overfull template slice by its canonical internal cover. -/
noncomputable def normalizedSlice {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t) (ht : 0 < t)
    (C : Finset (Edge F q t)) (l : Line F) : Finset (Edge F q t) :=
  if (activeSlice C l).card ≤ templateCap q t l then activeSlice C l
  else canonicalTemplate A ht l

noncomputable def normalize {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t) (ht : 0 < t)
    (C : Finset (Edge F q t)) : Finset (Edge F q t) :=
  (Finset.univ : Finset (Line F)).biUnion fun l ↦ normalizedSlice A ht C l

lemma normalizedSlice_card_le_activeSlice {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t) (ht : 0 < t)
    (C : Finset (Edge F q t)) (l : Line F) :
    (normalizedSlice A ht C l).card ≤ (activeSlice C l).card := by
  rw [normalizedSlice]
  split
  · rfl
  · rw [canonicalTemplate_card]
    omega

lemma normalizedSlice_card_le_cap {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t) (ht : 0 < t)
    (C : Finset (Edge F q t)) (l : Line F) :
    (normalizedSlice A ht C l).card ≤ templateCap q t l := by
  rw [normalizedSlice]
  split
  · assumption
  · rw [canonicalTemplate_card]

lemma normalize_card_le {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t) (ht : 0 < t)
    (C : Finset (Edge F q t)) : (normalize A ht C).card ≤ C.card := by
  classical
  have hsumActive :
      ∑ l : Line F, (activeSlice C l).card = (activePart C).card := by
    symm
    apply Finset.card_eq_sum_card_fiberwise
    intro e he
    exact Finset.mem_univ e.1
  calc
    (normalize A ht C).card ≤
        ∑ l : Line F, (normalizedSlice A ht C l).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ l : Line F, (activeSlice C l).card := by
      exact Finset.sum_le_sum fun l _ ↦ normalizedSlice_card_le_activeSlice A ht C l
    _ = (activePart C).card := hsumActive
    _ ≤ C.card := Finset.card_le_card (activePart_subset C)

lemma normalize_isEdgeCover {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (htq : t ≤ 2 * q) (ht : 0 < t)
    {C : Finset (Edge F q t)}
    (hC : (hypergraph D a A hqmod hqK hq htq).IsEdgeCover C) :
    (hypergraph D a A hqmod hqK hq htq).IsEdgeCover (normalize A ht C) := by
  have hactive := activePart_isEdgeCover D a A hqmod hqK hq htq hC
  intro z
  obtain ⟨e, he, hze⟩ := hactive z
  let l := e.1
  have heSlice : e ∈ activeSlice C l := by
    exact (mem_templateSlice_iff (activePart C) l e).mpr ⟨he, rfl⟩
  by_cases hle : (activeSlice C l).card ≤ templateCap q t l
  · refine ⟨e, ?_, hze⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨l, Finset.mem_univ _, by simpa [normalizedSlice, hle] using heSlice⟩
  · have hzl : Incident z.1.1 l := by
      rcases e with ⟨m, row | row⟩
      · by_cases hl : Incident (basePoint : Point F) l
        · exact ((mem_hypergraph_large D a A hqmod hqK hq htq l hl row z).mp hze).1
        · rw [hypergraph_wrong_large_empty D a A hqmod hqK hq htq l hl row] at hze
          simpa using hze
      · by_cases hl : Incident (basePoint : Point F) l
        · rw [hypergraph_wrong_small_empty D a A hqmod hqK hq htq l hl row] at hze
          simpa using hze
        · exact ((mem_hypergraph_small D a A hqmod hqK hq htq l hl row z).mp hze).1
    obtain ⟨f, hfCanon, hzf⟩ :=
      canonicalTemplate_covers_on_line D a A hqmod hqK hq htq ht l z hzl
    refine ⟨f, ?_, hzf⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨l, Finset.mem_univ _, by simpa [normalizedSlice, hle] using hfCanon⟩

noncomputable def IsNormal {q t : ℕ} (C : Finset (Edge F q t)) : Prop :=
  ∀ l : Line F, (templateSlice C l).card ≤ templateCap q t l

lemma normalize_normal {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t) (ht : 0 < t)
    (C : Finset (Edge F q t)) : IsNormal (normalize A ht C) := by
  intro l
  have hsub : templateSlice (normalize A ht C) l ⊆ normalizedSlice A ht C l := by
    intro e he
    have he' := (mem_templateSlice_iff (normalize A ht C) l e).mp he
    obtain ⟨m, _, hem⟩ := Finset.mem_biUnion.mp he'.1
    have hmfirst : e.1 = m := by
      rw [normalizedSlice] at hem
      split at hem
      · exact (mem_templateSlice_iff (activePart C) m e).mp hem |>.2
      · exact activeTemplate_first m
          (canonicalTemplate_subset_active A ht m hem)
    have hml : m = l := hmfirst.symm.trans he'.2
    simpa [hml] using hem
  exact (Finset.card_le_card hsub).trans
    (normalizedSlice_card_le_cap A ht C l)

noncomputable def IsActive {q t : ℕ} [Fact q.Prime]
    (C : Finset (Edge F q t)) : Prop :=
  ∀ e ∈ C, e ∈ activeTemplate e.1

lemma normalizedSlice_subset_active {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t) (ht : 0 < t)
    (C : Finset (Edge F q t)) (l : Line F) :
    normalizedSlice A ht C l ⊆ activeTemplate l := by
  rw [normalizedSlice]
  split
  · exact activeSlice_subset_activeTemplate C l
  · exact canonicalTemplate_subset_active A ht l

lemma normalize_active {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t) (ht : 0 < t)
    (C : Finset (Edge F q t)) : IsActive (normalize A ht C) := by
  intro e he
  obtain ⟨l, _, hel⟩ := Finset.mem_biUnion.mp he
  have heActive := normalizedSlice_subset_active A ht C l hel
  have hfirst := activeTemplate_first l heActive
  simpa [hfirst] using heActive

lemma templateCap_le_active_card {q t : ℕ} [Fact q.Prime] (hq : 0 < q) (ht : 0 < t)
    (l : Line F) :
    templateCap q t l ≤ (activeTemplate (q := q) (t := t) l).card := by
  by_cases hl : Incident (basePoint : Point F) l
  · rw [templateCap, if_pos hl, activeTemplate_card_large l hl]
    nlinarith
  · rw [templateCap, if_neg hl, activeTemplate_card_small l hl]
    nlinarith

lemma templateSlice_subset_active_of_active {q t : ℕ} [Fact q.Prime]
    {C : Finset (Edge F q t)} (hactive : IsActive C) (l : Line F) :
    templateSlice C l ⊆ activeTemplate l := by
  intro e he
  have he' := (mem_templateSlice_iff C l e).mp he
  have ha := hactive e he'.1
  simpa [he'.2] using ha

/-- Extend one normal active slice to exactly its permitted capacity. -/
noncomputable def templateExtension {q t : ℕ} [Fact q.Prime]
    (hq : 0 < q) (ht : 0 < t)
    (C : Finset (Edge F q t)) (hactive : IsActive C) (hnormal : IsNormal C)
    (l : Line F) : Finset (Edge F q t) :=
  Classical.choose (Finset.exists_subsuperset_card_eq
    (templateSlice_subset_active_of_active hactive l)
    (hnormal l) (templateCap_le_active_card hq ht l))

lemma templateSlice_subset_extension {q t : ℕ} [Fact q.Prime]
    (hq : 0 < q) (ht : 0 < t)
    (C : Finset (Edge F q t)) (hactive : IsActive C) (hnormal : IsNormal C)
    (l : Line F) :
    templateSlice C l ⊆ templateExtension hq ht C hactive hnormal l :=
  (Classical.choose_spec (Finset.exists_subsuperset_card_eq
    (templateSlice_subset_active_of_active hactive l)
    (hnormal l) (templateCap_le_active_card hq ht l))).1

lemma templateExtension_subset_active {q t : ℕ} [Fact q.Prime]
    (hq : 0 < q) (ht : 0 < t)
    (C : Finset (Edge F q t)) (hactive : IsActive C) (hnormal : IsNormal C)
    (l : Line F) :
    templateExtension hq ht C hactive hnormal l ⊆ activeTemplate l :=
  (Classical.choose_spec (Finset.exists_subsuperset_card_eq
    (templateSlice_subset_active_of_active hactive l)
    (hnormal l) (templateCap_le_active_card hq ht l))).2.1

lemma templateExtension_card {q t : ℕ} [Fact q.Prime]
    (hq : 0 < q) (ht : 0 < t)
    (C : Finset (Edge F q t)) (hactive : IsActive C) (hnormal : IsNormal C)
    (l : Line F) :
    (templateExtension hq ht C hactive hnormal l).card = templateCap q t l :=
  (Classical.choose_spec (Finset.exists_subsuperset_card_eq
    (templateSlice_subset_active_of_active hactive l)
    (hnormal l) (templateCap_le_active_card hq ht l))).2.2

noncomputable def fullExtension {q t : ℕ} [Fact q.Prime]
    (hq : 0 < q) (ht : 0 < t)
    (C : Finset (Edge F q t)) (hactive : IsActive C) (hnormal : IsNormal C) :
    Finset (Edge F q t) :=
  (Finset.univ : Finset (Line F)).biUnion fun l ↦
    templateExtension hq ht C hactive hnormal l

lemma subset_fullExtension {q t : ℕ} [Fact q.Prime]
    (hq : 0 < q) (ht : 0 < t)
    (C : Finset (Edge F q t)) (hactive : IsActive C) (hnormal : IsNormal C) :
    C ⊆ fullExtension hq ht C hactive hnormal := by
  intro e he
  apply Finset.mem_biUnion.mpr
  refine ⟨e.1, Finset.mem_univ _, ?_⟩
  apply templateSlice_subset_extension hq ht C hactive hnormal e.1
  exact (mem_templateSlice_iff C e.1 e).mpr ⟨he, rfl⟩

lemma fullExtension_slice {q t : ℕ} [Fact q.Prime]
    (hq : 0 < q) (ht : 0 < t)
    (C : Finset (Edge F q t)) (hactive : IsActive C) (hnormal : IsNormal C)
    (l : Line F) :
    templateSlice (fullExtension hq ht C hactive hnormal) l =
      templateExtension hq ht C hactive hnormal l := by
  ext e
  constructor
  · intro he
    have he' := (mem_templateSlice_iff _ l e).mp he
    obtain ⟨m, _, hem⟩ := Finset.mem_biUnion.mp he'.1
    have hmfirst := activeTemplate_first m
      (templateExtension_subset_active hq ht C hactive hnormal m hem)
    have hml : m = l := hmfirst.symm.trans he'.2
    simpa [hml] using hem
  · intro he
    apply (mem_templateSlice_iff _ l e).mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, he⟩, ?_⟩
    exact activeTemplate_first l
      (templateExtension_subset_active hq ht C hactive hnormal l he)

lemma fullExtension_normal {q t : ℕ} [Fact q.Prime]
    (hq : 0 < q) (ht : 0 < t)
    (C : Finset (Edge F q t)) (hactive : IsActive C) (hnormal : IsNormal C) :
    IsNormal (fullExtension hq ht C hactive hnormal) := by
  intro l
  rw [fullExtension_slice, templateExtension_card]

lemma fullExtension_card {q t : ℕ} [Fact q.Prime]
    (hq : 0 < q) (ht : 0 < t)
    (C : Finset (Edge F q t)) (hactive : IsActive C) (hnormal : IsNormal C) :
    (fullExtension hq ht C hactive hnormal).card =
      ∑ l : Line F, templateCap q t l := by
  classical
  have hdisj : ((Finset.univ : Finset (Line F)) : Set (Line F)).PairwiseDisjoint
      (templateExtension hq ht C hactive hnormal) := by
    intro l _ m _ hlm
    apply Finset.disjoint_left.mpr
    intro e hel hem
    have helFirst := activeTemplate_first l
      (templateExtension_subset_active hq ht C hactive hnormal l hel)
    have hemFirst := activeTemplate_first m
      (templateExtension_subset_active hq ht C hactive hnormal m hem)
    exact hlm (helFirst.symm.trans hemFirst)
  rw [fullExtension, Finset.card_biUnion hdisj]
  simp_rw [templateExtension_card]

lemma target_degree_le_total_capacity (x : BasePoint F) (q t : ℕ) :
    t + Fintype.card F * q ≤ ∑ l : Line F, templateCap q t l := by
  rw [← line_degree_sum x q t]
  apply Finset.sum_le_sum
  intro l _
  by_cases hxl : Incident x.1 l
  · simp [hxl, templateCap]
  · simp [hxl, templateCap]

/-- A normal active cover of size at most the target degree can be padded,
inside the per-template capacities, to one of exactly the target size. -/
lemma exists_normal_cover_card_eq {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (htq : t ≤ 2 * q) (hqpos : 0 < q) (htpos : 0 < t)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq htq).IsEdgeCover C)
    (hactive : IsActive C) (hnormal : IsNormal C)
    (hcard : C.card ≤ t + Fintype.card F * q) :
    ∃ P : Finset (Edge F q t),
      C ⊆ P ∧
      (hypergraph D a A hqmod hqK hq htq).IsEdgeCover P ∧
      IsActive P ∧ IsNormal P ∧ P.card = t + Fintype.card F * q := by
  let U := fullExtension hqpos htpos C hactive hnormal
  have hCU : C ⊆ U := subset_fullExtension hqpos htpos C hactive hnormal
  have htargetU : t + Fintype.card F * q ≤ U.card := by
    rw [fullExtension_card]
    exact target_degree_le_total_capacity
      (⟨affine 0 0, by simp [basePoint, affine, verticalInfinity]⟩ : BasePoint F) q t
  obtain ⟨P, hCP, hPU, hPcard⟩ :=
    Finset.exists_subsuperset_card_eq hCU hcard htargetU
  refine ⟨P, hCP, ?_, ?_, ?_, hPcard⟩
  · intro z
    obtain ⟨e, he, hze⟩ := hcover z
    exact ⟨e, hCP he, hze⟩
  · intro e he
    have heU := hPU he
    obtain ⟨l, _, hel⟩ := Finset.mem_biUnion.mp heU
    have ha := templateExtension_subset_active hqpos htpos C hactive hnormal l hel
    have hfirst := activeTemplate_first l ha
    simpa [hfirst] using ha
  · intro l
    have hsub : templateSlice P l ⊆ templateSlice U l := by
      intro e he
      have he' := (mem_templateSlice_iff P l e).mp he
      exact (mem_templateSlice_iff U l e).mpr ⟨hPU he'.1, he'.2⟩
    exact (Finset.card_le_card hsub).trans
      (fullExtension_normal hqpos htpos C hactive hnormal l)

/-- Exceptional columns selected by one affine row. -/
noncomputable def acceptedExceptions {q : ℕ}
    (l : Line F) (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (row : ZMod q × ZMod q) : Finset (ExceptionColumn l q) :=
  Finset.univ.filter fun c ↦
    affineValue row (smallSlope l hl hqmod hqK (Sum.inr c)) =
      (smallSlope l hl hqmod hqK (Sum.inr c)) ^ 2

@[simp] lemma mem_acceptedExceptions_iff {q : ℕ}
    (l : Line F) (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (row : ZMod q × ZMod q) (c : ExceptionColumn l q) :
    c ∈ acceptedExceptions l hl hqmod hqK row ↔
      affineValue row (smallSlope l hl hqmod hqK (Sum.inr c)) =
        (smallSlope l hl hqmod hqK (Sum.inr c)) ^ 2 := by
  simp [acceptedExceptions]

lemma acceptedExceptions_card_le_two {q : ℕ} [Fact q.Prime]
    (l : Line F) (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (row : ZMod q × ZMod q) :
    (acceptedExceptions l hl hqmod hqK row).card ≤ 2 := by
  classical
  let S := acceptedExceptions l hl hqmod hqK row
  by_cases hS : S.Nonempty
  · let c₁ := hS.choose
    have hc₁ : c₁ ∈ S := hS.choose_spec
    by_cases hR : (S.erase c₁).Nonempty
    · let c₂ := hR.choose
      have hc₂R : c₂ ∈ S.erase c₁ := hR.choose_spec
      have hc₂ : c₂ ∈ S := (Finset.mem_erase.mp hc₂R).2
      have hc₁₂ : c₁ ≠ c₂ := Ne.symm (Finset.mem_erase.mp hc₂R).1
      have hsub : S ⊆ {c₁, c₂} := by
        intro c hc
        by_contra hcPair
        have hcne : c ≠ c₁ ∧ c ≠ c₂ := by simpa using hcPair
        have hcne₁ : c ≠ c₁ := hcne.1
        have hcne₂ : c ≠ c₂ := hcne.2
        let s₁ := smallSlope l hl hqmod hqK (Sum.inr c₁)
        let s₂ := smallSlope l hl hqmod hqK (Sum.inr c₂)
        let s := smallSlope l hl hqmod hqK (Sum.inr c)
        have hs₁₂ : s₁ ≠ s₂ := by
          intro h
          exact hc₁₂ (Sum.inr.inj
            (smallSlope_injective l hl hqmod hqK h))
        have hs₁s : s₁ ≠ s := by
          intro h
          exact hcne₁ (Sum.inr.inj
            (smallSlope_injective l hl hqmod hqK h.symm))
        have hs₂s : s₂ ≠ s := by
          intro h
          exact hcne₂ (Sum.inr.inj
            (smallSlope_injective l hl hqmod hqK h.symm))
        have h₁ := (mem_acceptedExceptions_iff l hl hqmod hqK row c₁).mp hc₁
        have h₂ := (mem_acceptedExceptions_iff l hl hqmod hqK row c₂).mp hc₂
        have h := (mem_acceptedExceptions_iff l hl hqmod hqK row c).mp hc
        exact OrthogonalArray.parabolic_no_three hs₁₂ hs₁s hs₂s
          (by simpa [affineValue, s₁] using h₁)
          (by simpa [affineValue, s₂] using h₂)
          (by simpa [affineValue, s] using h)
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    · have hsub : S ⊆ {c₁} := by
        intro c hc
        by_contra hne
        apply hR
        have hne' : c ≠ c₁ := by simpa using hne
        exact ⟨c, Finset.mem_erase.mpr ⟨hne', hc⟩⟩
      exact (Finset.card_le_card hsub).trans (by simp)
  · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have haccepted : acceptedExceptions l hl hqmod hqK row = ∅ := by
      simpa [S] using hS0
    rw [haccepted]
    simp

/-- Number of compressed matching pieces supplied at all exceptional
positions by one affine row. -/
noncomputable def exceptionalWeight {q : ℕ}
    (l : Line F) (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (row : ZMod q × ZMod q) : ℕ :=
  ∑ c ∈ acceptedExceptions l hl hqmod hqK row,
    (groupFourFiber q c.2).card

lemma exceptionalWeight_le_eight {q : ℕ} [Fact q.Prime]
    (l : Line F) (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (row : ZMod q × ZMod q) :
    exceptionalWeight l hl hqmod hqK row ≤ 8 := by
  calc
    exceptionalWeight l hl hqmod hqK row ≤
        (acceptedExceptions l hl hqmod hqK row).card * 4 := by
      exact Finset.sum_le_card_nsmul _ _ 4 fun c _ ↦
        card_groupFourFiber_le_four q c.2
    _ ≤ 2 * 4 := Nat.mul_le_mul_right 4
      (acceptedExceptions_card_le_two l hl hqmod hqK row)
    _ = 8 := by norm_num

/-- Exceptional compressed-piece weight contributed at one assigned point. -/
noncomputable def exceptionalWeightAt {q : ℕ}
    (l : Line F) (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (row : ZMod q × ZMod q) (x : BasePoint F) : ℕ :=
  if hx : assignedLine x.1 = l then
    ∑ e : Fin (packetCount q),
      if (⟨⟨x, (mem_assignedFiber_iff l x).mpr hx⟩, e⟩ : ExceptionColumn l q) ∈
          acceptedExceptions l hl hqmod hqK row then
        (groupFourFiber q e).card
      else 0
  else 0

lemma exceptionalWeightAt_of_assigned {q : ℕ}
    (l : Line F) (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (row : ZMod q × ZMod q) (x : BasePoint F)
    (hx : assignedLine x.1 = l) :
    exceptionalWeightAt l hl hqmod hqK row x =
      ∑ e : Fin (packetCount q),
        if (⟨⟨x, (mem_assignedFiber_iff l x).mpr hx⟩, e⟩ : ExceptionColumn l q) ∈
            acceptedExceptions l hl hqmod hqK row then
          (groupFourFiber q e).card
        else 0 := by
  simp [exceptionalWeightAt, hx]

lemma sum_exceptionalWeightAt {q : ℕ}
    (l : Line F) (hl : ¬ Incident (basePoint : Point F) l)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (row : ZMod q × ZMod q) :
    (∑ x ∈ assignedFiber l,
      exceptionalWeightAt l hl hqmod hqK row x) =
      exceptionalWeight l hl hqmod hqK row := by
  classical
  rw [exceptionalWeight]
  let E := acceptedExceptions l hl hqmod hqK row
  calc
    (∑ x ∈ assignedFiber l,
      exceptionalWeightAt l hl hqmod hqK row x) =
        ∑ x : AssignedPoint l, ∑ e : Fin (packetCount q),
          if (⟨x, e⟩ : ExceptionColumn l q) ∈ E then
            (groupFourFiber q e).card else 0 := by
      rw [← Finset.sum_attach, Finset.attach_eq_univ]
      apply Finset.sum_congr rfl
      intro x _
      simpa [E] using exceptionalWeightAt_of_assigned l hl hqmod hqK row x.1
        ((mem_assignedFiber_iff l x.1).mp x.2)
    _ = ∑ c : ExceptionColumn l q,
          if c ∈ E then (groupFourFiber q c.2).card else 0 := by
      symm
      exact Fintype.sum_prod_type _
    _ = ∑ c ∈ E, (groupFourFiber q c.2).card := by
      rw [← Finset.sum_filter]
      simp

/-- Compressed-piece weight of one global edge at one expander copy. -/
noncomputable def edgeWeightAt {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (e : Edge F q t) (x : BasePoint F) : ℕ :=
  if hxl : Incident x.1 e.1 then
    if hl : Incident (basePoint : Point F) e.1 then
      match e.2 with
      | Sum.inl _ => 1
      | Sum.inr _ => 0
    else
      match e.2 with
      | Sum.inl _ => 0
      | Sum.inr row =>
          if hx : assignedLine x.1 = e.1 then
            exceptionalWeightAt e.1 hl hqmod hqK row x
          else 1
  else 0

noncomputable def totalEdgeWeight {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (e : Edge F q t) : ℕ :=
  ∑ x : BasePoint F, edgeWeightAt a hqmod hqK e x

lemma card_smallLinePoints_of_base (l : Line F)
    (hl : Incident (basePoint : Point F) l) :
    (smallLinePoints l).card = Fintype.card F := by
  classical
  let e : {x : BasePoint F // Incident x.1 l} ≃ LargePoint l hl :=
    { toFun := fun x ↦ toLargePoint l hl x.1 x.2
      invFun := fun p ↦ ⟨⟨p.1.1, by
        intro h
        apply p.2
        apply Subtype.ext
        exact h⟩, p.1.2⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro p; apply Subtype.ext; apply Subtype.ext; rfl }
  calc
    (smallLinePoints l).card =
        Fintype.card {x : BasePoint F // Incident x.1 l} := by
      simpa [smallLinePoints] using
        (Fintype.card_subtype (fun x : BasePoint F ↦ Incident x.1 l)).symm
    _ = Fintype.card (LargePoint l hl) := Fintype.card_congr e
    _ = Fintype.card F := card_largePoint l hl

lemma totalEdgeWeight_large {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (l : Line F) (hl : Incident (basePoint : Point F) l)
    (row : Fin t × Fin t) :
    totalEdgeWeight a hqmod hqK (l, Sum.inl row) = Fintype.card F := by
  classical
  rw [totalEdgeWeight, ← card_smallLinePoints_of_base l hl,
    Finset.card_eq_sum_ones]
  symm
  calc
    (∑ _x ∈ smallLinePoints l, 1) =
        ∑ x ∈ smallLinePoints l,
          edgeWeightAt a hqmod hqK (l, Sum.inl row) x := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxl := (mem_smallLinePoints_iff l x).mp hx
      simp [edgeWeightAt, hxl, hl]
    _ = ∑ x : BasePoint F,
          edgeWeightAt a hqmod hqK (l, Sum.inl row) x := by
      apply Finset.sum_subset (Finset.subset_univ (smallLinePoints l))
      intro x _ hxnot
      have hnot : ¬ Incident x.1 l := by
        simpa [mem_smallLinePoints_iff] using hxnot
      simp [edgeWeightAt, hnot]

lemma totalEdgeWeight_small {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (l : Line F) (hl : ¬ Incident (basePoint : Point F) l)
    (row : ZMod q × ZMod q) :
    totalEdgeWeight a hqmod hqK
        (l, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) =
      (ordinaryPoints l).card + exceptionalWeight l hl hqmod hqK row := by
  classical
  rw [totalEdgeWeight]
  have hpartition : ordinaryPoints l ∪ assignedFiber l = smallLinePoints l := by
    rw [ordinaryPoints, Finset.sdiff_union_of_subset
      (assignedFiber_subset_smallLinePoints l)]
  have hdisj : Disjoint (ordinaryPoints l) (assignedFiber l) :=
    Finset.sdiff_disjoint
  calc
    (∑ x : BasePoint F, edgeWeightAt a hqmod hqK (l, Sum.inr row) x) =
        ∑ x ∈ smallLinePoints l,
          edgeWeightAt a hqmod hqK (l, Sum.inr row) x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ (smallLinePoints l))
      · intro x _ hxnot
        have hnot : ¬ Incident x.1 l := by
          simpa [mem_smallLinePoints_iff] using hxnot
        simp [edgeWeightAt, hnot]
    _ = (∑ x ∈ ordinaryPoints l,
          edgeWeightAt a hqmod hqK (l, Sum.inr row) x) +
        ∑ x ∈ assignedFiber l,
          edgeWeightAt a hqmod hqK (l, Sum.inr row) x := by
      rw [← Finset.sum_union hdisj, hpartition]
    _ = (ordinaryPoints l).card +
        ∑ x ∈ assignedFiber l,
          exceptionalWeightAt l hl hqmod hqK row x := by
      congr 1
      · rw [Finset.card_eq_sum_ones]
        apply Finset.sum_congr rfl
        intro x hx
        have hxl := (mem_smallLinePoints_iff l x).mp
          (Finset.mem_sdiff.mp hx).1
        have hxa : assignedLine x.1 ≠ l := by
          simpa [mem_assignedFiber_iff] using (Finset.mem_sdiff.mp hx).2
        simp [edgeWeightAt, hxl, hl, hxa]
      · apply Finset.sum_congr rfl
        intro x hx
        have hxl := (mem_smallLinePoints_iff l x).mp
          (assignedFiber_subset_smallLinePoints l hx)
        have hxa := (mem_assignedFiber_iff l x).mp hx
        simp [edgeWeightAt, hxl, hl, hxa]
    _ = (ordinaryPoints l).card + exceptionalWeight l hl hqmod hqK row := by
      rw [sum_exceptionalWeightAt]

lemma totalEdgeWeight_le {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q) (e : Edge F q t) :
    totalEdgeWeight a hqmod hqK e ≤ Fintype.card F + 8 := by
  rcases e with ⟨l, row | row⟩
  · by_cases hl : Incident (basePoint : Point F) l
    · rw [totalEdgeWeight_large a hqmod hqK l hl row]
      omega
    · simp [totalEdgeWeight, edgeWeightAt, hl]
  · by_cases hl : Incident (basePoint : Point F) l
    · simp [totalEdgeWeight, edgeWeightAt, hl]
    · rw [totalEdgeWeight_small a hqmod hqK l hl row]
      exact Nat.add_le_add
        (by simpa only [Fintype.card_coe] using card_ordinaryPoint_le l hl)
        (exceptionalWeight_le_eight l hl hqmod hqK row)

/-- Side of an edge at an incident fixed-plane point. -/
noncomputable def edgeSideAt {q t : ℕ} (a : Labeling F) (e : Edge F q t)
    (x : BasePoint F) : Bool :=
  if h : Incident x.1 e.1 then a e.1 ⟨x.1, h⟩ else false

/-- Compressed pieces supplied by a small-template edge at one point. -/
noncomputable def smallPiecesAt {q t : ℕ}
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (e : Edge F q t) (x : BasePoint F) : Finset (Fin q) :=
  if hxl : Incident x.1 e.1 then
    if hl : ¬ Incident (basePoint : Point F) e.1 then
      match e.2 with
      | Sum.inl _ => ∅
      | Sum.inr row =>
          if hx : assignedLine x.1 = e.1 then
            Finset.univ.filter fun c ↦
              (⟨⟨x, (mem_assignedFiber_iff e.1 x).mpr hx⟩, groupFour q c⟩ :
                  ExceptionColumn e.1 q) ∈
                acceptedExceptions e.1 hl hqmod hqK row
          else
            { (indexValue q hqmod).symm
                (affineValue row
                  (smallSlope e.1 hl hqmod hqK
                    (Sum.inl ⟨x, Finset.mem_sdiff.mpr
                      ⟨(mem_smallLinePoints_iff e.1 x).mpr hxl,
                        by simpa [mem_assignedFiber_iff] using hx⟩⟩))) }
    else ∅
  else ∅

lemma smallPiecesAt_card_eq_weight {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (e : Edge F q t) (x : BasePoint F)
    (hsmall : ¬ Incident (basePoint : Point F) e.1) :
    (smallPiecesAt hqmod hqK e x).card = edgeWeightAt a hqmod hqK e x := by
  classical
  by_cases hxl : Incident x.1 e.1
  · rcases e with ⟨l, row | row⟩
    · simp [smallPiecesAt, edgeWeightAt, hxl, hsmall]
    · have hsmall' : ¬ Incident (basePoint : Point F) l := by simpa using hsmall
      have hxl' : Incident x.1 l := by simpa using hxl
      by_cases hx : assignedLine x.1 = l
      · simp only [smallPiecesAt, hxl', hsmall', hx, dite_true, edgeWeightAt,
          Finset.card_filter]
        simp only [not_false_eq_true, if_true, if_false, dite_true, dite_false]
        rw [exceptionalWeightAt_of_assigned l hsmall' hqmod hqK row x hx]
        let E := acceptedExceptions l hsmall' hqmod hqK row
        let P : Fin q → Prop := fun c ↦
          (⟨⟨x, (mem_assignedFiber_iff l x).mpr hx⟩, groupFour q c⟩ :
            ExceptionColumn l q) ∈ E
        have hdisj : ((Finset.univ : Finset (Fin (packetCount q))) :
            Set (Fin (packetCount q))).PairwiseDisjoint
              (fun e ↦ (groupFourFiber q e).filter fun c ↦
                (⟨⟨x, (mem_assignedFiber_iff l x).mpr hx⟩, e⟩ :
                  ExceptionColumn l q) ∈ E) := by
          intro e _ f _ hef
          apply Finset.disjoint_left.mpr
          intro c hce hcf
          exact hef (((mem_groupFourFiber_iff q e c).mp
            (Finset.mem_filter.mp hce).1).symm.trans
              ((mem_groupFourFiber_iff q f c).mp
                (Finset.mem_filter.mp hcf).1))
        have hunion :
            (Finset.univ : Finset (Fin (packetCount q))).biUnion
                (fun e ↦ (groupFourFiber q e).filter fun c ↦
                  (⟨⟨x, (mem_assignedFiber_iff l x).mpr hx⟩, e⟩ :
                    ExceptionColumn l q) ∈ E) =
              (Finset.univ : Finset (Fin q)).filter P := by
          ext c
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
            Finset.mem_filter, P]
          constructor
          · rintro ⟨e, hce, he⟩
            have hgroup : groupFour q c = e :=
              (mem_groupFourFiber_iff q e c).mp hce
            simpa [hgroup] using he
          · intro hc
            refine ⟨groupFour q c, (mem_groupFourFiber_iff q _ c).mpr rfl, ?_⟩
            simpa using hc
        change ((Finset.univ : Finset (Fin q)).filter P).card = _
        calc
          ((Finset.univ : Finset (Fin q)).filter P).card =
              ((Finset.univ : Finset (Fin (packetCount q))).biUnion
                (fun e ↦ (groupFourFiber q e).filter fun c ↦
                  (⟨⟨x, (mem_assignedFiber_iff l x).mpr hx⟩, e⟩ :
                    ExceptionColumn l q) ∈ E)).card := by rw [hunion]
          _ = ∑ e : Fin (packetCount q),
              ((groupFourFiber q e).filter (fun c ↦
                (⟨⟨x, (mem_assignedFiber_iff l x).mpr hx⟩, e⟩ :
                    ExceptionColumn l q) ∈ E)).card := by
            exact Finset.card_biUnion hdisj
          _ = ∑ e : Fin (packetCount q),
              if (⟨⟨x, (mem_assignedFiber_iff l x).mpr hx⟩, e⟩ :
                  ExceptionColumn l q) ∈ E then
                (groupFourFiber q e).card else 0 := by
            apply Finset.sum_congr rfl
            intro e _
            by_cases he :
                (⟨⟨x, (mem_assignedFiber_iff l x).mpr hx⟩, e⟩ :
                  ExceptionColumn l q) ∈ E
            · simp [he]
            · simp [he]
      · simp [smallPiecesAt, edgeWeightAt, hxl', hsmall', hx]
  · simp [smallPiecesAt, edgeWeightAt, hxl]

/-- Original matching blocks supplied by a base-line edge. -/
noncomputable def largeOriginalAt {q t : ℕ}
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (e : Edge F q t) (x : BasePoint F) : Finset (Fin t) :=
  if hxl : Incident x.1 e.1 then
    if hl : Incident (basePoint : Point F) e.1 then
      match e.2 with
      | Sum.inl row =>
          {A.entry row
            ((largePointEquiv e.1 hl (toLargePoint e.1 hl x hxl)).castSucc)}
      | Sum.inr _ => ∅
    else ∅
  else ∅

lemma largeOriginalAt_card_le_weight {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (e : Edge F q t) (x : BasePoint F) :
    (largeOriginalAt A e x).card ≤ edgeWeightAt a hqmod hqK e x := by
  classical
  by_cases hxl : Incident x.1 e.1
  · by_cases hl : Incident (basePoint : Point F) e.1
    · rcases e with ⟨l, row | row⟩ <;>
        simp [largeOriginalAt, edgeWeightAt, hxl, hl]
    · simp [largeOriginalAt, hxl, hl]
  · simp [largeOriginalAt, edgeWeightAt, hxl]

/-- Original blocks selected on one side of one expander copy. -/
noncomputable def selectedLargeOriginal {q t : ℕ}
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (a : Labeling F) (C : Finset (Edge F q t))
    (x : BasePoint F) (side : Bool) : Finset (Fin t) :=
  C.biUnion fun e ↦ if edgeSideAt a e x = side then largeOriginalAt A e x else ∅

noncomputable def selectedSmallPieces {q t : ℕ}
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (x : BasePoint F) (side : Bool) :
    Finset (Fin q) :=
  C.biUnion fun e ↦ if edgeSideAt a e x = side then
    smallPiecesAt hqmod hqK e x else ∅

noncomputable def selectedOriginal {q t : ℕ}
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (C : Finset (Edge F q t)) (x : BasePoint F) (side : Bool) :
    Finset (Fin t) :=
  selectedLargeOriginal A a C x side ∪
    Compression.lift hq ht (selectedSmallPieces a hqmod hqK C x side)

noncomputable def sideWeight {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (x : BasePoint F) (side : Bool) : ℕ :=
  ∑ e ∈ C, if edgeSideAt a e x = side then
    edgeWeightAt a hqmod hqK e x else 0

lemma smallPiecesAt_card_le_weight {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (e : Edge F q t) (x : BasePoint F) :
    (smallPiecesAt hqmod hqK e x).card ≤ edgeWeightAt a hqmod hqK e x := by
  by_cases hsmall : ¬ Incident (basePoint : Point F) e.1
  · exact (smallPiecesAt_card_eq_weight a hqmod hqK e x hsmall).le
  · push_neg at hsmall
    simp [smallPiecesAt, hsmall]

lemma selectedSmallPieces_card_le {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (x : BasePoint F) (side : Bool) :
    (selectedSmallPieces a hqmod hqK C x side).card ≤
      sideWeight a hqmod hqK C x side := by
  calc
    (selectedSmallPieces a hqmod hqK C x side).card ≤
        ∑ e ∈ C, (if edgeSideAt a e x = side then
          smallPiecesAt hqmod hqK e x else ∅).card := Finset.card_biUnion_le
    _ ≤ ∑ e ∈ C, if edgeSideAt a e x = side then
          edgeWeightAt a hqmod hqK e x else 0 := by
      apply Finset.sum_le_sum
      intro e _
      split
      · exact smallPiecesAt_card_le_weight a hqmod hqK e x
      · simp
    _ = sideWeight a hqmod hqK C x side := rfl

lemma large_small_card_le_weight {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (e : Edge F q t) (x : BasePoint F) :
    (largeOriginalAt A e x).card + (smallPiecesAt hqmod hqK e x).card ≤
      edgeWeightAt a hqmod hqK e x := by
  by_cases hl : Incident (basePoint : Point F) e.1
  · have hs : (smallPiecesAt hqmod hqK e x).card = 0 := by
      simp [smallPiecesAt, hl]
    rw [hs, Nat.add_zero]
    exact largeOriginalAt_card_le_weight a A hqmod hqK e x
  · have hlarge : (largeOriginalAt A e x).card = 0 := by
      simp [largeOriginalAt, hl]
    rw [hlarge, Nat.zero_add]
    exact smallPiecesAt_card_le_weight a hqmod hqK e x

lemma selected_parts_card_le {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (x : BasePoint F) (side : Bool) :
    (selectedLargeOriginal A a C x side).card +
        (selectedSmallPieces a hqmod hqK C x side).card ≤
      sideWeight a hqmod hqK C x side := by
  have hL : (selectedLargeOriginal A a C x side).card ≤
      ∑ e ∈ C, (if edgeSideAt a e x = side then
        largeOriginalAt A e x else ∅).card := Finset.card_biUnion_le
  have hS : (selectedSmallPieces a hqmod hqK C x side).card ≤
      ∑ e ∈ C, (if edgeSideAt a e x = side then
        smallPiecesAt hqmod hqK e x else ∅).card := Finset.card_biUnion_le
  calc
    (selectedLargeOriginal A a C x side).card +
        (selectedSmallPieces a hqmod hqK C x side).card ≤
      (∑ e ∈ C, (if edgeSideAt a e x = side then
        largeOriginalAt A e x else ∅).card) +
      ∑ e ∈ C, (if edgeSideAt a e x = side then
        smallPiecesAt hqmod hqK e x else ∅).card := Nat.add_le_add hL hS
    _ = ∑ e ∈ C,
        ((if edgeSideAt a e x = side then largeOriginalAt A e x else ∅).card +
        (if edgeSideAt a e x = side then
          smallPiecesAt hqmod hqK e x else ∅).card) := by
      rw [← Finset.sum_add_distrib]
    _ ≤ ∑ e ∈ C, if edgeSideAt a e x = side then
          edgeWeightAt a hqmod hqK e x else 0 := by
      apply Finset.sum_le_sum
      intro e _
      split
      · exact large_small_card_le_weight a A hqmod hqK e x
      · simp
    _ = sideWeight a hqmod hqK C x side := rfl

lemma selectedOriginal_card_le_add_defect {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (C : Finset (Edge F q t)) (x : BasePoint F) (side : Bool) :
    (selectedOriginal A a hqmod hqK hq ht C x side).card ≤
      sideWeight a hqmod hqK C x side + (t - q) := by
  calc
    (selectedOriginal A a hqmod hqK hq ht C x side).card ≤
        (selectedLargeOriginal A a C x side).card +
          (Compression.lift hq ht
            (selectedSmallPieces a hqmod hqK C x side)).card :=
      Finset.card_union_le _ _
    _ ≤ (selectedLargeOriginal A a C x side).card +
        ((selectedSmallPieces a hqmod hqK C x side).card + (t - q)) :=
      Nat.add_le_add_left
        (Compression.lift_card_le_add_defect hqpos hq ht _) _
    _ = ((selectedLargeOriginal A a C x side).card +
        (selectedSmallPieces a hqmod hqK C x side).card) + (t - q) := by omega
    _ ≤ sideWeight a hqmod hqK C x side + (t - q) :=
      Nat.add_le_add_right
        (selected_parts_card_le A a hqmod hqK C x side) _

lemma selectedOriginal_card_le_weight_add_defect {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (C : Finset (Edge F q t)) (x : BasePoint F) (side : Bool) :
    (selectedOriginal A a hqmod hqK hq ht C x side).card ≤
      sideWeight a hqmod hqK C x side + (t - q) :=
  selectedOriginal_card_le_add_defect A a hqmod hqK hqpos hq ht C x side

lemma selectedOriginal_card_le_twice_weight {q t : ℕ} [Fact q.Prime]
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (C : Finset (Edge F q t)) (x : BasePoint F) (side : Bool) :
    (selectedOriginal A a hqmod hqK hq ht C x side).card ≤
      2 * sideWeight a hqmod hqK C x side := by
  calc
    (selectedOriginal A a hqmod hqK hq ht C x side).card ≤
        (selectedLargeOriginal A a C x side).card +
          (Compression.lift hq ht
            (selectedSmallPieces a hqmod hqK C x side)).card :=
      Finset.card_union_le _ _
    _ ≤ (selectedLargeOriginal A a C x side).card +
        2 * (selectedSmallPieces a hqmod hqK C x side).card :=
      Nat.add_le_add_left (Compression.lift_card_le_twice hq ht _) _
    _ ≤ 2 * ((selectedLargeOriginal A a C x side).card +
        (selectedSmallPieces a hqmod hqK C x side).card) := by omega
    _ ≤ 2 * sideWeight a hqmod hqK C x side :=
      Nat.mul_le_mul_left 2 (selected_parts_card_le A a hqmod hqK C x side)

lemma covered_block_mem_selectedOriginal {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} {x : BasePoint F} {v : Fin 100 × Fin t}
    {e : Edge F q t} (heC : e ∈ C)
    (hve : (x, v) ∈ (hypergraph D a A hqmod hqK hq ht).edge e) :
    blockIndex D (edgeSideAt a e x) v ∈
      selectedOriginal A a hqmod hqK hq ht C x (edgeSideAt a e x) := by
  classical
  rcases e with ⟨l, row | row⟩
  · by_cases hl : Incident (basePoint : Point F) l
    · obtain ⟨hxl, hblock⟩ :=
        (mem_hypergraph_large D a A hqmod hqK hq ht l hl row (x, v)).mp hve
      have hside : edgeSideAt a
          (l, (Sum.inl row : Fin t × Fin t ⊕ ZMod q × ZMod q)) x =
          a l ⟨x.1, hxl⟩ := by
        simp [edgeSideAt, hxl]
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨(l, Sum.inl row), heC, ?_⟩
      rw [if_pos rfl]
      simp only [largeOriginalAt, hxl, hl, dite_true, Finset.mem_singleton]
      simpa [hside] using hblock
    · rw [hypergraph_wrong_large_empty D a A hqmod hqK hq ht l hl row] at hve
      simpa using hve
  · by_cases hl : Incident (basePoint : Point F) l
    · rw [hypergraph_wrong_small_empty D a A hqmod hqK hq ht l hl row] at hve
      simpa using hve
    · obtain ⟨hxl, hrow⟩ :=
        (mem_hypergraph_small D a A hqmod hqK hq ht l hl row (x, v)).mp hve
      have hside : edgeSideAt a
          (l, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) x =
          a l ⟨x.1, hxl⟩ := by
        simp [edgeSideAt, hxl]
      let c := compressedIndex D hq ht (a l ⟨x.1, hxl⟩) v
      have hc : c ∈ smallPiecesAt hqmod hqK
          (l, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) x := by
        by_cases hx : assignedLine x.1 = l
        · simp only [smallPiecesAt, hxl, hl, hx, dite_true]
          simp
          have hcol := smallVertexColumn_of_assigned D a l hl hq ht x hxl hx v
          have htarget := smallVertexTarget_of_assigned D a l hl hqmod hqK
            hq ht x hxl hx v
          simpa [c, hcol, htarget] using hrow
        · simp only [smallPiecesAt, hxl, hl, hx, dite_true]
          simp
          apply (indexValue q hqmod).injective
          simp only [Equiv.apply_symm_apply]
          have htarget :
              smallVertexTarget D a l hl hqmod hqK hq ht x hxl v =
                indexValue q hqmod c := by
            simp [smallVertexTarget, smallVertexColumn, hx, c,
              compressedIndex]
          simpa [smallVertexColumn, hx] using (hrow.trans htarget).symm
      apply Finset.mem_union_right
      apply (Compression.mem_lift_iff hq ht _ _).mpr
      apply Finset.mem_biUnion.mpr
      refine ⟨(l, Sum.inr row), heC, ?_⟩
      rw [if_pos rfl]
      simpa [c, compressedIndex, hside] using hc

lemma selectedOriginal_covers {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (a : Labeling F)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (x : BasePoint F) :
    D.CoversByIndices
      (selectedOriginal A a hqmod hqK hq ht C x false)
      (selectedOriginal A a hqmod hqK hq ht C x true) := by
  intro v
  obtain ⟨e, heC, hve⟩ := hcover (x, v)
  have hmem := covered_block_mem_selectedOriginal D a A hqmod hqK hq ht
    heC hve
  cases hs : edgeSideAt a e x
  · left
    simpa [blockIndex, hs] using hmem
  · right
    simpa [blockIndex, hs] using hmem

noncomputable def majoritySide {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (x : BasePoint F) : Bool :=
  decide (sideWeight a hqmod hqK C x false ≤
    sideWeight a hqmod hqK C x true)

noncomputable def matchingWeight {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (x : BasePoint F) : ℕ :=
  sideWeight a hqmod hqK C x (majoritySide a hqmod hqK C x)

noncomputable def mismatchingWeight {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (x : BasePoint F) : ℕ :=
  sideWeight a hqmod hqK C x (!(majoritySide a hqmod hqK C x))

lemma mismatch_le_match {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (x : BasePoint F) :
    mismatchingWeight a hqmod hqK C x ≤ matchingWeight a hqmod hqK C x := by
  by_cases h : sideWeight a hqmod hqK C x false ≤
      sideWeight a hqmod hqK C x true
  · simpa [mismatchingWeight, matchingWeight, majoritySide, h] using h
  · have h' : sideWeight a hqmod hqK C x true ≤
        sideWeight a hqmod hqK C x false := (Nat.lt_of_not_ge h).le
    simpa [mismatchingWeight, matchingWeight, majoritySide, h] using h'

lemma two_sideWeight_eq {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (x : BasePoint F) :
    sideWeight a hqmod hqK C x false + sideWeight a hqmod hqK C x true =
      ∑ e ∈ C, edgeWeightAt a hqmod hqK e x := by
  rw [sideWeight, sideWeight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  cases h : edgeSideAt a e x <;> simp [h]

lemma match_add_mismatch_eq {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (x : BasePoint F) :
    matchingWeight a hqmod hqK C x + mismatchingWeight a hqmod hqK C x =
      ∑ e ∈ C, edgeWeightAt a hqmod hqK e x := by
  unfold matchingWeight mismatchingWeight
  cases h : majoritySide a hqmod hqK C x
  · simpa [h] using two_sideWeight_eq a hqmod hqK C x
  · simpa [h, add_comm] using two_sideWeight_eq a hqmod hqK C x

lemma global_weight_bound {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) :
    (∑ x : BasePoint F, matchingWeight a hqmod hqK C x) +
        ∑ x : BasePoint F, mismatchingWeight a hqmod hqK C x ≤
      (Fintype.card F + 8) * C.card := by
  calc
    (∑ x : BasePoint F, matchingWeight a hqmod hqK C x) +
        ∑ x : BasePoint F, mismatchingWeight a hqmod hqK C x =
        ∑ x : BasePoint F,
          (matchingWeight a hqmod hqK C x +
            mismatchingWeight a hqmod hqK C x) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ x : BasePoint F, ∑ e ∈ C, edgeWeightAt a hqmod hqK e x := by
      apply Finset.sum_congr rfl
      intro x _
      exact match_add_mismatch_eq a hqmod hqK C x
    _ = ∑ e ∈ C, totalEdgeWeight a hqmod hqK e := by
      rw [Finset.sum_comm]
      rfl
    _ ≤ C.card * (Fintype.card F + 8) :=
      Finset.sum_le_card_nsmul C _ _ fun e _ ↦
        totalEdgeWeight_le a hqmod hqK e
    _ = (Fintype.card F + 8) * C.card := Nat.mul_comm _ _

lemma majority_deficit_small {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hclose : 20 * (t - q) + 20 ≤ q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (x : BasePoint F) :
    2 * (q - matchingWeight a hqmod hqK C x) ≤ t := by
  let f := matchingWeight a hqmod hqK C x
  let g := mismatchingWeight a hqmod hqK C x
  by_cases hfq : q ≤ f
  · omega
  · have hfq' : f ≤ q := by omega
    by_contra hbad
    have ha : t / 2 ≤ q - f := by omega
    have haT : t / 2 ≤ t := Nat.div_le_self _ _
    have hselected :
        (selectedOriginal A a hqmod hqK hq ht C x
          (majoritySide a hqmod hqK C x)).card ≤ t - t / 2 := by
      have hadd := selectedOriginal_card_le_weight_add_defect A a hqmod hqK
        hqpos hq ht C x (majoritySide a hqmod hqK C x)
      have hfeq : sideWeight a hqmod hqK C x
          (majoritySide a hqmod hqK C x) = f := rfl
      rw [hfeq] at hadd
      omega
    have hcov := selectedOriginal_covers D a A hqmod hqK hq ht hcover x
    have hexpLower : 11 * (t / 2) ≤
        10 * (selectedOriginal A a hqmod hqK hq ht C x
          (!(majoritySide a hqmod hqK C x))).card := by
      cases hs : majoritySide a hqmod hqK C x
      · exact (D.opposite_original_blocks_of_expansion hexp hcov haT
          (by simpa [hs] using hselected)).1 (by omega)
      · exact (D.opposite_original_blocks_of_expansion_symm hexp hcov haT
          (by simpa [hs] using hselected)).1 (by omega)
    have hother := selectedOriginal_card_le_weight_add_defect A a hqmod hqK
      hqpos hq ht C x (!(majoritySide a hqmod hqK C x))
    have hgeq : sideWeight a hqmod hqK C x
        (!(majoritySide a hqmod hqK C x)) = g := rfl
    rw [hgeq] at hother
    have hgf : g ≤ f := mismatch_le_match a hqmod hqK C x
    omega

lemma local_weak_waste {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hclose : 20 * (t - q) + 20 ≤ q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (x : BasePoint F) :
    11 * (q - matchingWeight a hqmod hqK C x) ≤
      10 * (mismatchingWeight a hqmod hqK C x + (t - q)) := by
  let f := matchingWeight a hqmod hqK C x
  let g := mismatchingWeight a hqmod hqK C x
  by_cases hfq : q ≤ f
  · omega
  · have hfq' : f ≤ q := by omega
    have hsmall := majority_deficit_small D hexp a A hqmod hqK hqpos hq ht
      hclose hcover x
    have hcov := selectedOriginal_covers D a A hqmod hqK hq ht hcover x
    have hmain : 11 * (q - f) ≤
        10 * (selectedOriginal A a hqmod hqK hq ht C x
          (!(majoritySide a hqmod hqK C x))).card := by
      have hmajor := selectedOriginal_card_le_weight_add_defect A a hqmod hqK
        hqpos hq ht C x (majoritySide a hqmod hqK C x)
      have hfeq : sideWeight a hqmod hqK C x
          (majoritySide a hqmod hqK C x) = f := rfl
      rw [hfeq] at hmajor
      have hmajor' :
          (selectedOriginal A a hqmod hqK hq ht C x
            (majoritySide a hqmod hqK C x)).card ≤ t - (q - f) := by
        have heq : t - (q - f) = f + (t - q) := by omega
        rw [heq]
        exact hmajor
      cases hs : majoritySide a hqmod hqK C x
      · exact (D.opposite_original_blocks_of_expansion hexp hcov
          (by omega : q - f ≤ t) (by simpa [hs] using hmajor')).1
            (by simpa [f] using hsmall)
      · exact (D.opposite_original_blocks_of_expansion_symm hexp hcov
          (by omega : q - f ≤ t) (by simpa [hs] using hmajor')).1
            (by simpa [f] using hsmall)
    have hother := selectedOriginal_card_le_weight_add_defect A a hqmod hqK
      hqpos hq ht C x (!(majoritySide a hqmod hqK C x))
    have hgeq : sideWeight a hqmod hqK C x
        (!(majoritySide a hqmod hqK C x)) = g := rfl
    rw [hgeq] at hother
    exact hmain.trans (Nat.mul_le_mul_left 10 hother)

lemma global_mismatch_arithmetic (K q t : ℕ) (hK : 1 ≤ K)
    (hqt : q ≤ t) (hrange : K ^ 2 * t ≤ (K ^ 2 + 1) * q) :
    11 * (K + 8) * (t + K * q) +
        10 * (K ^ 2 + K) * (t - q) -
          11 * (K ^ 2 + K) * q ≤
      100 * (t + K * q) := by
  have hdelta : K ^ 2 * (t - q) ≤ q := by
    have hsplit : K ^ 2 * t = K ^ 2 * q + K ^ 2 * (t - q) := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hqt]
    rw [hsplit, Nat.add_mul] at hrange
    omega
  have hcoeff : 10 * K ^ 2 + 21 * K - 12 ≤ 12 * (K + 1) * K ^ 2 := by
    have hKsq : K ≤ K ^ 2 := by
      rw [pow_two]
      simpa using Nat.mul_le_mul_left K hK
    by_cases hKone : K = 1
    · subst K
      norm_num
    · have hKtwo : 2 ≤ K := by omega
      calc
        10 * K ^ 2 + 21 * K - 12 ≤ 10 * K ^ 2 + 21 * K := Nat.sub_le _ _
        _ ≤ 31 * K ^ 2 := by
          have h21 : 21 * K ≤ 21 * K ^ 2 := Nat.mul_le_mul_left 21 hKsq
          omega
        _ ≤ 12 * (K + 1) * K ^ 2 := by
          have h31 : 31 ≤ 12 * (K + 1) := by omega
          exact Nat.mul_le_mul_right (K ^ 2) h31
  have hdeltaBound : (10 * K ^ 2 + 21 * K - 12) * (t - q) ≤
      12 * (K + 1) * q := by
    calc
      (10 * K ^ 2 + 21 * K - 12) * (t - q) ≤
          (12 * (K + 1) * K ^ 2) * (t - q) :=
        Nat.mul_le_mul_right _ hcoeff
      _ = 12 * (K + 1) * (K ^ 2 * (t - q)) := by ring
      _ ≤ 12 * (K + 1) * q := Nat.mul_le_mul_left _ hdelta
  have htSplit : t = q + (t - q) := (Nat.add_sub_of_le hqt).symm
  rw [htSplit]
  have hnonneg : 11 * (K ^ 2 + K) * q ≤
      11 * (K + 8) * (q + (t - q) + K * q) +
        10 * (K ^ 2 + K) * (q + (t - q) - q) := by
    nlinarith
  rw [Nat.sub_le_iff_le_add]
  rw [show q + (t - q) - q = t - q by omega]
  have hid :
      11 * (K + 8) * (q + (t - q) + K * q) +
          10 * (K ^ 2 + K) * (t - q) =
        11 * (K ^ 2 + K) * q +
          88 * (K + 1) * q +
            (10 * K ^ 2 + 21 * K + 88) * (t - q) := by ring
  rw [hid]
  have hrewrite : (10 * K ^ 2 + 21 * K + 88) * (t - q) =
      (10 * K ^ 2 + 21 * K - 12) * (t - q) + 100 * (t - q) := by
    have h12 : 12 ≤ 10 * K ^ 2 + 21 * K := by nlinarith
    have hcoeffeq : 10 * K ^ 2 + 21 * K + 88 =
        (10 * K ^ 2 + 21 * K - 12) + 100 := by omega
    rw [hcoeffeq, Nat.add_mul]
  have hbound :
      11 * (K ^ 2 + K) * q + 88 * (K + 1) * q +
          (10 * K ^ 2 + 21 * K + 88) * (t - q) ≤
        11 * (K ^ 2 + K) * q + 100 * (K + 1) * q +
          100 * (t - q) := by
    calc
      11 * (K ^ 2 + K) * q + 88 * (K + 1) * q +
            (10 * K ^ 2 + 21 * K + 88) * (t - q) =
          11 * (K ^ 2 + K) * q + 88 * (K + 1) * q +
            ((10 * K ^ 2 + 21 * K - 12) * (t - q) +
              100 * (t - q)) := by rw [hrewrite]
      _ = 11 * (K ^ 2 + K) * q +
          (88 * (K + 1) * q +
            (10 * K ^ 2 + 21 * K - 12) * (t - q)) +
              100 * (t - q) := by ring
      _ ≤ 11 * (K ^ 2 + K) * q +
            (88 * (K + 1) * q + 12 * (K + 1) * q) +
              100 * (t - q) := by
          exact Nat.add_le_add_right
            (Nat.add_le_add_left
              (Nat.add_le_add_left hdeltaBound (88 * (K + 1) * q))
              (11 * (K ^ 2 + K) * q))
            (100 * (t - q))
      _ = 11 * (K ^ 2 + K) * q + 100 * (K + 1) * q +
            100 * (t - q) := by ring
  calc
    11 * (K ^ 2 + K) * q + 88 * (K + 1) * q +
        (10 * K ^ 2 + 21 * K + 88) * (t - q) ≤
      11 * (K ^ 2 + K) * q + 100 * (K + 1) * q +
        100 * (t - q) := hbound
    _ = 11 * (K ^ 2 + K) * q +
        100 * (q + (t - q) + K * q) := by ring
    _ = 100 * (q + (t - q) + K * q) +
        11 * (K ^ 2 + K) * q := Nat.add_comm _ _

lemma global_mismatchingWeight_le {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hclose : 20 * (t - q) + 20 ≤ q)
    (hrange : Fintype.card F ^ 2 * t ≤
      (Fintype.card F ^ 2 + 1) * q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (hcard : C.card = t + Fintype.card F * q) :
    (∑ x : BasePoint F, mismatchingWeight a hqmod hqK C x) ≤
      100 * (t + Fintype.card F * q) := by
  let K := Fintype.card F
  let L := K ^ 2 + K
  let FS : ℕ := Finset.univ.sum fun x : BasePoint F ↦
    matchingWeight a hqmod hqK C x
  let GS : ℕ := Finset.univ.sum fun x : BasePoint F ↦
    mismatchingWeight a hqmod hqK C x
  let DS : ℕ := Finset.univ.sum fun x : BasePoint F ↦
    q - matchingWeight a hqmod hqK C x
  have hwaste : 11 * DS ≤ 10 * (GS + L * (t - q)) := by
    dsimp [DS, GS, L]
    calc
      11 * (Finset.univ.sum fun x : BasePoint F ↦
          q - matchingWeight a hqmod hqK C x) =
          Finset.univ.sum fun x : BasePoint F ↦
            11 * (q - matchingWeight a hqmod hqK C x) := by
        rw [Finset.mul_sum]
      _ ≤ Finset.univ.sum fun x : BasePoint F ↦
          10 * (mismatchingWeight a hqmod hqK C x + (t - q)) := by
        exact Finset.sum_le_sum fun x _ ↦
          local_weak_waste D hexp a A hqmod hqK hqpos hq ht hclose hcover x
      _ = 10 * ((Finset.univ.sum fun x : BasePoint F ↦
          mismatchingWeight a hqmod hqK C x) +
            (K ^ 2 + K) * (t - q)) := by
        rw [← Finset.mul_sum]
        congr 2
        rw [Finset.sum_add_distrib]
        simp [card_basePoint, K, mul_comm]
        ring
  have hdeficit : L * q ≤ FS + DS := by
    dsimp [L, FS, DS]
    have hcardBP : Fintype.card F ^ 2 + Fintype.card F =
        Fintype.card (BasePoint F) := by
      simp [card_basePoint, pow_two]
    rw [hcardBP]
    calc
      Fintype.card (BasePoint F) * q =
          Finset.univ.sum (fun _x : BasePoint F ↦ q) := by simp
      _ ≤
          Finset.univ.sum fun x : BasePoint F ↦
            (matchingWeight a hqmod hqK C x +
              (q - matchingWeight a hqmod hqK C x)) := by
        exact Finset.sum_le_sum fun _x _ ↦ by omega
      _ = (Finset.univ.sum fun x : BasePoint F ↦
          matchingWeight a hqmod hqK C x) +
          Finset.univ.sum fun x : BasePoint F ↦
            (q - matchingWeight a hqmod hqK C x) :=
        Finset.sum_add_distrib
  have hweight := global_weight_bound a hqmod hqK C
  have hweight' : FS + GS ≤ (K + 8) * (t + K * q) := by
    simpa [FS, GS, K, hcard] using hweight
  let W := (K + 8) * (t + K * q)
  let Q := L * (t - q)
  have hB : 11 * (L * q) + GS ≤ 11 * W + 10 * Q := by
    calc
      11 * (L * q) + GS ≤ 11 * (FS + DS) + GS :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 11 hdeficit) GS
      _ = 11 * FS + 11 * DS + GS := by ring
      _ ≤ 11 * FS + 10 * (GS + Q) + GS :=
        Nat.add_le_add_right (Nat.add_le_add_left hwaste (11 * FS)) GS
      _ = 11 * (FS + GS) + 10 * Q := by ring
      _ ≤ 11 * W + 10 * Q :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 11 (by simpa [W] using hweight')) _
  have hnonneg : 11 * L * q ≤ 11 * W + 10 * Q := by
    calc
      11 * L * q = 11 * (L * q) := by ring
      _ ≤ 11 * (L * q) + GS := Nat.le_add_right _ _
      _ ≤ 11 * W + 10 * Q := hB
  have hrough : GS ≤
      11 * (K + 8) * (t + K * q) + 10 * L * (t - q) - 11 * L * q := by
    rw [show 11 * (K + 8) * (t + K * q) + 10 * L * (t - q) =
        11 * W + 10 * Q by simp [W, Q]; ring]
    exact (Nat.le_sub_iff_add_le' hnonneg).2 (by simpa [mul_assoc] using hB)
  exact hrough.trans (by
    simpa [K, L] using global_mismatch_arithmetic K q t Fintype.card_pos hq hrange)

noncomputable def edgeMismatch {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (e : Edge F q t) : ℕ :=
  ∑ x : BasePoint F,
    if edgeSideAt a e x ≠ majoritySide a hqmod hqK C x then
      edgeWeightAt a hqmod hqK e x else 0

lemma sum_edgeMismatch_eq {q t : ℕ}
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) :
    ∑ e ∈ C, edgeMismatch a hqmod hqK C e =
      ∑ x : BasePoint F, mismatchingWeight a hqmod hqK C x := by
  unfold edgeMismatch
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  unfold mismatchingWeight sideWeight
  apply Finset.sum_congr rfl
  intro e _
  cases hm : majoritySide a hqmod hqK C x <;>
    cases hs : edgeSideAt a e x <;> simp [hm, hs]

noncomputable def goodCoverEdges {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) : Finset (Edge F q t) :=
  C.filter fun e ↦ edgeMismatch a hqmod hqK C e ≤ 3998

lemma goodCoverEdges_card {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hclose : 20 * (t - q) + 20 ≤ q)
    (hrange : Fintype.card F ^ 2 * t ≤
      (Fintype.card F ^ 2 + 1) * q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (hcard : C.card = t + Fintype.card F * q) :
    39 * (goodCoverEdges a hqmod hqK C).card ≥ 38 * C.card := by
  let G := goodCoverEdges a hqmod hqK C
  let B := C \ G
  have hpartition : G.card + B.card = C.card := by
    have hsub : G ⊆ C := Finset.filter_subset _ _
    have hGC : G.card ≤ C.card := Finset.card_le_card hsub
    dsimp [B]
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  have hbad : 3999 * B.card ≤ ∑ e ∈ C, edgeMismatch a hqmod hqK C e := by
    calc
      3999 * B.card = ∑ _e ∈ B, 3999 := by simp [mul_comm]
      _ ≤ ∑ e ∈ B, edgeMismatch a hqmod hqK C e := by
        apply Finset.sum_le_sum
        intro e he
        have he' := Finset.mem_sdiff.mp he
        have hnot : ¬ edgeMismatch a hqmod hqK C e ≤ 3998 := by
          simpa [G, goodCoverEdges, he'.1] using he'.2
        omega
      _ ≤ ∑ e ∈ C, edgeMismatch a hqmod hqK C e := by
        exact Finset.sum_le_sum_of_subset (Finset.sdiff_subset)
  have hglobal := global_mismatchingWeight_le D hexp a A hqmod hqK hqpos
    hq ht hclose hrange hcover hcard
  rw [sum_edgeMismatch_eq] at hbad
  have hbad' : 3999 * B.card ≤ 100 * C.card := by
    simpa [hcard] using hbad.trans hglobal
  have hscaled : 100 * (39 * B.card) ≤ 100 * C.card := by
    calc
      100 * (39 * B.card) = 3900 * B.card := by ring
      _ ≤ 3999 * B.card := Nat.mul_le_mul_right B.card (by norm_num)
      _ ≤ 100 * C.card := hbad'
  have h39 : 39 * B.card ≤ C.card :=
    Nat.le_of_mul_le_mul_left hscaled (by norm_num)
  change 38 * C.card ≤ 39 * G.card
  omega

noncomputable def goodLines {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) : Finset (Line F) :=
  (goodCoverEdges a hqmod hqK C).image Prod.fst

lemma goodEdges_card_le_lines_mul_t {q t : ℕ}
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) {C : Finset (Edge F q t)} (hnormal : IsNormal C) :
    (goodCoverEdges a hqmod hqK C).card ≤
      (goodLines a hqmod hqK C).card * t := by
  let G := goodCoverEdges a hqmod hqK C
  let T := goodLines a hqmod hqK C
  have hsum : G.card = ∑ l ∈ T, (templateSlice G l).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro e he
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  rw [hsum]
  calc
    ∑ l ∈ T, (templateSlice G l).card ≤ ∑ _l ∈ T, t := by
      apply Finset.sum_le_sum
      intro l _
      have hsub : templateSlice G l ⊆ templateSlice C l := by
        intro e he
        have he' := (mem_templateSlice_iff G l e).mp he
        exact (mem_templateSlice_iff C l e).mpr
          ⟨(Finset.mem_filter.mp he'.1).1, he'.2⟩
      have hcap := (Finset.card_le_card hsub).trans (hnormal l)
      unfold templateCap at hcap
      split at hcap
      · exact hcap
      · exact hcap.trans hq
    _ = T.card * t := by simp

lemma goodLines_large {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hclose : 20 * (t - q) + 20 ≤ q)
    (hrange : Fintype.card F ^ 2 * t ≤
      (Fintype.card F ^ 2 + 1) * q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (hactive : IsActive C) (hnormal : IsNormal C)
    (hcard : C.card = t + Fintype.card F * q) :
    3 * Fintype.card F ≤
      4 * (goodLines a hqmod hqK C).card := by
  have hgood := goodCoverEdges_card D hexp a A hqmod hqK hqpos hq ht
    hclose hrange hcover hcard
  have hline := goodEdges_card_le_lines_mul_t a hqmod hqK hq hnormal
  have harith : 12 * Fintype.card F * t ≤
      15 * (t + Fintype.card F * q) := by
    have hdelta : Fintype.card F ^ 2 * (t - q) ≤ q := by
      have hsplit : Fintype.card F ^ 2 * t =
          Fintype.card F ^ 2 * q +
            Fintype.card F ^ 2 * (t - q) := by
        rw [← Nat.mul_add, Nat.add_sub_of_le hq]
      rw [hsplit, Nat.add_mul] at hrange
      omega
    have hrough : Fintype.card F * (t - q) ≤ q := by
      have hself : Fintype.card F ≤ Fintype.card F ^ 2 := by
        rw [pow_two]
        simpa using Nat.mul_le_mul_left (Fintype.card F) Fintype.card_pos
      exact (Nat.mul_le_mul_right _ hself).trans hdelta
    have hsplit : t = q + (t - q) := (Nat.add_sub_of_le hq).symm
    have hrough12 : 12 * (Fintype.card F * (t - q)) ≤ 12 * q :=
      Nat.mul_le_mul_left 12 hrough
    calc
      12 * Fintype.card F * t =
          12 * (Fintype.card F * q) +
            12 * (Fintype.card F * (t - q)) := by
          conv_lhs => rw [hsplit]
          ring
      _ ≤ 12 * (Fintype.card F * q) + 12 * q :=
        Nat.add_le_add_left hrough12 _
      _ ≤ 15 * (t + Fintype.card F * q) := by
        conv_rhs => rw [hsplit]
        omega
  let G := (goodCoverEdges a hqmod hqK C).card
  let L := (goodLines a hqmod hqK C).card
  have harithC : 12 * Fintype.card F * t ≤ 15 * C.card := by
    simpa [hcard] using harith
  have hscaled : 456 * Fintype.card F * t ≤ 608 * L * t := by
    calc
      456 * Fintype.card F * t = 38 * (12 * Fintype.card F * t) := by ring
      _ ≤ 38 * (15 * C.card) := Nat.mul_le_mul_left 38 harithC
      _ = 15 * (38 * C.card) := by ring
      _ ≤ 15 * (39 * G) := Nat.mul_le_mul_left 15 (by simpa [G] using hgood)
      _ = 585 * G := by ring
      _ ≤ 585 * (L * t) := Nat.mul_le_mul_left 585 (by simpa [G, L] using hline)
      _ ≤ 608 * (L * t) := Nat.mul_le_mul_right (L * t) (by norm_num)
      _ = 608 * L * t := by ring
  have htpos : 0 < t := hqpos.trans_le hq
  have hscaled' : (152 * (3 * Fintype.card F)) * t ≤
      (152 * (4 * L)) * t := by
    calc
      (152 * (3 * Fintype.card F)) * t = 456 * Fintype.card F * t := by ring
      _ ≤ 608 * L * t := hscaled
      _ = (152 * (4 * L)) * t := by ring
  have hcancelT : 152 * (3 * Fintype.card F) ≤ 152 * (4 * L) := by
    exact Nat.le_of_mul_le_mul_right hscaled' htpos
  have hresult : 3 * Fintype.card F ≤ 4 * L :=
    Nat.le_of_mul_le_mul_left hcancelT (by norm_num)
  simpa [L] using hresult

/-- The majority side, extended arbitrarily to the removed base point. -/
noncomputable def coverGamma {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (p : Point F) : Bool :=
  if hp : p = (basePoint : Point F) then false
  else majoritySide a hqmod hqK C ⟨p, hp⟩

@[simp] lemma coverGamma_base {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) :
    coverGamma a hqmod hqK C (basePoint : Point F) = false := by
  simp [coverGamma]

@[simp] lemma coverGamma_nonbase {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (x : BasePoint F) :
    coverGamma a hqmod hqK C x.1 = majoritySide a hqmod hqK C x := by
  simp [coverGamma, x.2]

/-- The at most two incidences where an edge need not carry positive weight:
the base point on a large line, or the assignment fibre on a small line. -/
noncomputable def ignoredIncidences (l : Line F) :
    Finset {p : Point F // Incident p l} :=
  if hl : Incident (basePoint : Point F) l then {⟨basePoint, hl⟩}
  else (assignedFiber l).attach.image fun x ↦
    (⟨x.1.1, assignedPoint_incident l x⟩ :
      {p : Point F // Incident p l})

lemma ignoredIncidences_card_le_two (l : Line F) :
    (ignoredIncidences l).card ≤ 2 := by
  classical
  by_cases hl : Incident (basePoint : Point F) l
  · simp [ignoredIncidences, hl]
  · rw [ignoredIncidences, dif_neg hl]
    calc
      ((assignedFiber l).attach.image fun x ↦
          (⟨x.1.1, assignedPoint_incident l x⟩ :
            {p : Point F // Incident p l})).card ≤
          (assignedFiber l).attach.card := Finset.card_image_le
      _ = (assignedFiber l).card := by simp
      _ ≤ 2 := assignedFiber_card_le_two l hl

lemma edge_mismatches_card_le {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (e : Edge F q t)
    (heActive : e ∈ activeTemplate e.1) :
    (mismatches a (coverGamma a hqmod hqK C) e.1).card ≤
      edgeMismatch a hqmod hqK C e + 2 := by
  classical
  let M := mismatches a (coverGamma a hqmod hqK C) e.1
  let I := ignoredIncidences e.1
  let R := M \ I
  have hbase_of_relevant (p : {p : Point F // Incident p e.1})
      (hp : p ∈ R) : p.1 ≠ (basePoint : Point F) := by
    intro hpeq
    have hpR := Finset.mem_sdiff.mp hp
    by_cases hl : Incident (basePoint : Point F) e.1
    · apply hpR.2
      change p ∈ ignoredIncidences e.1
      have hpEq : p = ⟨basePoint, hl⟩ := Subtype.ext hpeq
      simp [ignoredIncidences, hl, hpEq]
    · exact hl (by simpa [hpeq] using p.2)
  let f : {p : {p : Point F // Incident p e.1} // p ∈ R} → BasePoint F :=
    fun p ↦ ⟨p.1.1, hbase_of_relevant p.1 p.2⟩
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : BasePoint F ↦ x.1) h
  have hRcard : R.card = ((Finset.univ :
      Finset {p : {p : Point F // Incident p e.1} // p ∈ R}).image f).card := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro p _ q _ h
      exact hf h
  have hpoint (p : {p : {p : Point F // Incident p e.1} // p ∈ R}) :
      1 ≤ if edgeSideAt a e (f p) ≠
          majoritySide a hqmod hqK C (f p) then
        edgeWeightAt a hqmod hqK e (f p) else 0 := by
    have hpM := (Finset.mem_sdiff.mp p.2).1
    have hpNotI := (Finset.mem_sdiff.mp p.2).2
    have hmismatch := (mem_mismatches_iff a
      (coverGamma a hqmod hqK C) e.1 p.1).mp hpM
    have hside : edgeSideAt a e (f p) = a e.1 p.1 := by
      simp [edgeSideAt, f, p.1.2]
    have hgamma : coverGamma a hqmod hqK C p.1.1 =
        majoritySide a hqmod hqK C (f p) := by
      simpa [f] using coverGamma_nonbase a hqmod hqK C (f p)
    have hne : edgeSideAt a e (f p) ≠
        majoritySide a hqmod hqK C (f p) := by
      simpa [hside, hgamma] using hmismatch
    rw [if_pos hne]
    by_cases hl : Incident (basePoint : Point F) e.1
    · rcases e with ⟨l, row | row⟩
      · simp [edgeWeightAt, f, p.1.2, hl]
      · have : (l, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) ∉
            activeTemplate l := by
          rw [activeTemplate, if_pos hl]
          simp
        exact (this heActive).elim
    · rcases e with ⟨l, row | row⟩
      · have : (l, (Sum.inl row : Fin t × Fin t ⊕ ZMod q × ZMod q)) ∉
            activeTemplate l := by
          rw [activeTemplate, if_neg hl]
          simp
        exact (this heActive).elim
      · have hnotassigned : assignedLine p.1.1 ≠ l := by
          intro ha
          apply hpNotI
          change p.1 ∈ ignoredIncidences l
          simp only [ignoredIncidences, hl, dite_false]
          apply Finset.mem_image.mpr
          let x0 : BasePoint F := ⟨p.1.1, hbase_of_relevant p.1 p.2⟩
          let x : AssignedPoint l := ⟨x0, (mem_assignedFiber_iff l x0).mpr ha⟩
          refine ⟨x, by simp, ?_⟩
          apply Subtype.ext
          rfl
        simp [edgeWeightAt, f, p.1.2, hl, hnotassigned]
  have himage :
      ((Finset.univ : Finset {p : {p : Point F // Incident p e.1} // p ∈ R}).image f).card ≤
        edgeMismatch a hqmod hqK C e := by
    rw [← hRcard]
    calc
      R.card = ∑ _p ∈ R, 1 := by simp
      _ = ∑ p : {p : {p : Point F // Incident p e.1} // p ∈ R}, 1 := by simp
      _ ≤ ∑ p : {p : {p : Point F // Incident p e.1} // p ∈ R},
          (if edgeSideAt a e (f p) ≠ majoritySide a hqmod hqK C (f p) then
            edgeWeightAt a hqmod hqK e (f p) else 0) :=
        Finset.sum_le_sum fun p _ ↦ hpoint p
      _ ≤ ∑ x : BasePoint F,
          (if edgeSideAt a e x ≠ majoritySide a hqmod hqK C x then
            edgeWeightAt a hqmod hqK e x else 0) := by
        let w : BasePoint F → ℕ := fun x ↦
          if edgeSideAt a e x ≠ majoritySide a hqmod hqK C x then
            edgeWeightAt a hqmod hqK e x else 0
        calc
          (∑ p : {p : {p : Point F // Incident p e.1} // p ∈ R}, w (f p)) =
              ∑ x ∈ (Finset.univ :
                Finset {p : {p : Point F // Incident p e.1} // p ∈ R}).image f,
                w x := by
            symm
            exact Finset.sum_image (fun p _ q _ hpq ↦ hf hpq)
          _ ≤ ∑ x : BasePoint F, w x :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = edgeMismatch a hqmod hqK C e := rfl
  have hdecomp : M.card ≤ R.card + I.card :=
    Finset.card_le_card_sdiff_add_card
  have hI := ignoredIncidences_card_le_two e.1
  have hI' : I.card ≤ 2 := by simpa [I] using hI
  change M.card ≤ edgeMismatch a hqmod hqK C e + 2
  omega

lemma goodLine_mismatch_bound {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) (hactive : IsActive C) {l : Line F}
    (hl : l ∈ goodLines a hqmod hqK C) :
    (mismatches a (coverGamma a hqmod hqK C) l).card ≤ Labels.fixedC0 := by
  obtain ⟨e, heGood, hel⟩ := Finset.mem_image.mp hl
  have heC := (Finset.mem_filter.mp heGood).1
  have heBound := (Finset.mem_filter.mp heGood).2
  have heActive : e ∈ activeTemplate e.1 := hactive e heC
  subst l
  exact (edge_mismatches_card_le a hqmod hqK C e heActive).trans (by
    norm_num [Labels.fixedC0] at *
    omega)

noncomputable def pencilEdges {q t : ℕ}
    (C : Finset (Edge F q t)) (x : Point F) :
    Finset (Edge F q t) := C.filter fun e ↦ Incident x e.1

lemma strongly_almost_concentrated {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F)
    (hgood : IsGood (fixedBalance (Fintype.card F)) fixedC0 a)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hclose : 20 * (t - q) + 20 ≤ q)
    (hrange : Fintype.card F ^ 2 * t ≤
      (Fintype.card F ^ 2 + 1) * q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (hactive : IsActive C) (hnormal : IsNormal C)
    (hcard : C.card = t + Fintype.card F * q) :
    ∃ x : Point F,
      39 * (C \ pencilEdges C x).card <
        C.card + 156 * fixedC0 * t := by
  let G := goodCoverEdges a hqmod hqK C
  let T := goodLines a hqmod hqK C
  have hTlarge : 3 * Fintype.card F ≤ 4 * T.card :=
    goodLines_large D hexp a A hqmod hqK hqpos hq ht hclose hrange
      hcover hactive hnormal hcard
  have hTmismatch : ∀ l ∈ T,
      (mismatches a (coverGamma a hqmod hqK C) l).card ≤ fixedC0 := by
    intro l hl
    exact goodLine_mismatch_bound a hqmod hqK C hactive hl
  obtain ⟨x, hx⟩ := hgood.pencilForcing
    (coverGamma a hqmod hqK C) T hTlarge hTmismatch
  refine ⟨x, ?_⟩
  let TB := T.filter fun l ↦ ¬ Incident x l
  let GB := G.filter fun e ↦ ¬ Incident x e.1
  have hGB : GB.card ≤ TB.card * t := by
    have hsum : GB.card = ∑ l ∈ TB, (templateSlice GB l).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro e he
      have he' := Finset.mem_filter.mp he
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨e, he'.1, rfl⟩, he'.2⟩
    rw [hsum]
    calc
      ∑ l ∈ TB, (templateSlice GB l).card ≤ ∑ _l ∈ TB, t := by
        apply Finset.sum_le_sum
        intro l _
        have hsub : templateSlice GB l ⊆ templateSlice C l := by
          intro e he
          have he' := (mem_templateSlice_iff GB l e).mp he
          exact (mem_templateSlice_iff C l e).mpr
            ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he'.1).1).1, he'.2⟩
        have hc := (Finset.card_le_card hsub).trans (hnormal l)
        unfold templateCap at hc
        split at hc
        · exact hc
        · exact hc.trans hq
      _ = TB.card * t := by simp
  have hTB : TB.card < 4 * fixedC0 := by simpa [TB, T] using hx
  have hbad : 39 * (C \ G).card ≤ C.card := by
    have hG := goodCoverEdges_card D hexp a A hqmod hqK hqpos hq ht
      hclose hrange hcover hcard
    have hG' : 38 * C.card ≤ 39 * G.card := by simpa [G] using hG
    have hsub : G ⊆ C := Finset.filter_subset _ _
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  have houtSub : C \ pencilEdges C x ⊆ (C \ G) ∪ GB := by
    intro e he
    have he' := Finset.mem_sdiff.mp he
    by_cases heG : e ∈ G
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨heG, by
        simpa [pencilEdges, he'.1] using he'.2⟩))
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_sdiff.mpr ⟨he'.1, heG⟩))
  have hout : (C \ pencilEdges C x).card ≤ (C \ G).card + GB.card :=
    (Finset.card_le_card houtSub).trans (Finset.card_union_le _ _)
  have hGBstrict : 39 * GB.card < 156 * fixedC0 * t := by
    have htpos : 0 < t := hqpos.trans_le hq
    calc
      39 * GB.card ≤ 39 * (TB.card * t) := Nat.mul_le_mul_left 39 hGB
      _ < 39 * ((4 * fixedC0) * t) := by
        exact Nat.mul_lt_mul_of_pos_left
          (Nat.mul_lt_mul_of_pos_right hTB htpos) (by norm_num)
      _ = 156 * fixedC0 * t := by ring
  omega

/-- Points on a pencil line at which the small template is ordinary, with
the pencil centre itself removed. -/
noncomputable def usefulPoints (x : BasePoint F) (l : Line F) :
    Finset (BasePoint F) :=
  (smallLinePoints l \ assignedFiber l).erase x

lemma usefulPoints_subset_line (x : BasePoint F) (l : Line F) :
    usefulPoints x l ⊆ smallLinePoints l := by
  exact (Finset.erase_subset _ _).trans Finset.sdiff_subset

lemma usefulPoint_not_assigned {x : BasePoint F} {l : Line F}
    {z : BasePoint F} (hz : z ∈ usefulPoints x l) : assignedLine z.1 ≠ l := by
  have hz' := Finset.mem_erase.mp hz
  simpa [mem_assignedFiber_iff] using (Finset.mem_sdiff.mp hz'.2).2

lemma usefulPoint_ne_center {x : BasePoint F} {l : Line F}
    {z : BasePoint F} (hz : z ∈ usefulPoints x l) : z ≠ x :=
  (Finset.mem_erase.mp hz).1

lemma usefulPoints_card_ge (x : BasePoint F) (l : Line F)
    (hxl : Incident x.1 l) :
    Fintype.card F - 2 ≤ (usefulPoints x l).card := by
  classical
  by_cases hl : Incident (basePoint : Point F) l
  · have hassign : assignedFiber l = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hzline := (mem_assignedFiber_iff l z).mp hz
      exact base_not_incident_assignedLine z (by simpa [hzline] using hl)
    rw [usefulPoints, hassign, Finset.sdiff_empty]
    have hxmem : x ∈ smallLinePoints l := (mem_smallLinePoints_iff l x).mpr hxl
    rw [Finset.card_erase_of_mem hxmem, card_smallLinePoints_of_base l hl]
    omega
  · have hline := card_smallLinePoints l hl
    have hassign := assignedFiber_card_le_two l hl
    have hsdiff : (smallLinePoints l \ assignedFiber l).card =
        (smallLinePoints l).card - (assignedFiber l).card :=
      Finset.card_sdiff_of_subset (assignedFiber_subset_smallLinePoints l)
    rw [usefulPoints]
    by_cases hx : x ∈ smallLinePoints l \ assignedFiber l
    · rw [Finset.card_erase_of_mem hx, hsdiff, hline]
      omega
    · rw [Finset.erase_eq_of_notMem hx, hsdiff, hline]
      omega

lemma pencil_slice_card_sum {q t : ℕ} (C : Finset (Edge F q t))
    (x : Point F) :
    (pencilEdges C x).card =
      ∑ l ∈ linesThrough x, (templateSlice C l).card := by
  classical
  have hmap : Set.MapsTo Prod.fst
      ((pencilEdges C x : Finset (Edge F q t)) : Set (Edge F q t))
      ((linesThrough x : Finset (Line F)) : Set (Line F)) := by
    intro e he
    exact (mem_linesThrough_iff x e.1).mpr (Finset.mem_filter.mp he).2
  have hfiber := Finset.card_eq_sum_card_fiberwise hmap
  calc
    (pencilEdges C x).card =
        ∑ l ∈ linesThrough x,
          ((pencilEdges C x).filter fun e ↦ e.1 = l).card := hfiber
    _ = ∑ l ∈ linesThrough x, (templateSlice C l).card := by
      apply Finset.sum_congr rfl
      intro l hl
      congr 1
      ext e
      have hxl := (mem_linesThrough_iff x l).mp hl
      simp only [Finset.mem_filter, mem_templateSlice_iff]
      constructor
      · rintro ⟨he, hel⟩
        exact ⟨(Finset.mem_filter.mp he).1, hel⟩
      · rintro ⟨heC, hel⟩
        refine ⟨Finset.mem_filter.mpr ⟨heC, ?_⟩, hel⟩
        simpa [hel] using hxl

lemma pencil_capacity_sum (x : BasePoint F) (q t : ℕ) :
    ∑ l ∈ linesThrough x.1, templateCap q t l =
      t + Fintype.card F * q := by
  rw [← line_degree_sum x q t]
  simp [linesThrough, Finset.sum_filter, templateCap]

lemma deficit_sum_eq_outside {q t : ℕ}
    (C : Finset (Edge F q t)) (hnormal : IsNormal C)
    (x : BasePoint F) (hcard : C.card = t + Fintype.card F * q) :
    ∑ l ∈ linesThrough x.1,
        (templateCap q t l - (templateSlice C l).card) =
      (C \ pencilEdges C x.1).card := by
  have hslices := pencil_slice_card_sum C x.1
  have hcaps := pencil_capacity_sum x q t
  have hsub : pencilEdges C x.1 ⊆ C := Finset.filter_subset _ _
  have hout : (C \ pencilEdges C x.1).card =
      C.card - (pencilEdges C x.1).card := Finset.card_sdiff_of_subset hsub
  rw [hout, hcard]
  have hsumsub :
      ∑ l ∈ linesThrough x.1,
          (templateCap q t l - (templateSlice C l).card) =
        (∑ l ∈ linesThrough x.1, templateCap q t l) -
          ∑ l ∈ linesThrough x.1, (templateSlice C l).card := by
    induction linesThrough x.1 using Finset.induction_on with
    | empty => simp
    | @insert l S hl ih =>
        rw [Finset.sum_insert hl, Finset.sum_insert hl, Finset.sum_insert hl, ih]
        have hlcap := hnormal l
        have hScap : (∑ m ∈ S, (templateSlice C m).card) ≤
            ∑ m ∈ S, templateCap q t m := by
          exact Finset.sum_le_sum fun m _ ↦ hnormal m
        omega
  rw [hsumsub, hcaps, hslices]

/-- Side prescribed by the pencil through `x` at `z`. -/
noncomputable def pencilSide (a : Labeling F) (x : Point F)
    (z : BasePoint F) : Bool :=
  a (lineThroughPoints x z.1)
    ⟨z.1, lineThroughPoints_incident_right x z.1⟩

/-- The label of a point on a specified line, extended by `false` away from
the line so that it can be used in ordinary (proof-free) finite sums. -/
noncomputable def lineSide (a : Labeling F) (m : Line F)
    (z : BasePoint F) : Bool :=
  if hzm : Incident z.1 m then a m ⟨z.1, hzm⟩ else false

@[simp] lemma lineSide_of_incident (a : Labeling F) (m : Line F)
    (z : BasePoint F) (hzm : Incident z.1 m) :
    lineSide a m z = a m ⟨z.1, hzm⟩ := by
  simp [lineSide, hzm]

lemma pencilLine_ne_exterior {x : Point F} {z : BasePoint F} {m : Line F}
    (hxm : ¬ Incident x m) (hzm : Incident z.1 m) :
    lineThroughPoints x z.1 ≠ m := by
  intro h
  apply hxm
  rw [← h]
  exact lineThroughPoints_incident_left x z.1

lemma pencilSide_eq_edgeSide_iff_agree
    (a : Labeling F) {x : Point F} {z : BasePoint F} {m : Line F}
    (hxm : ¬ Incident x m) (hzm : Incident z.1 m) :
    pencilSide a x z = a m ⟨z.1, hzm⟩ ↔
      Agree a (lineThroughPoints x z.1) m := by
  let l := lineThroughPoints x z.1
  have hlm : l ≠ m := pencilLine_ne_exterior hxm hzm
  have hinter : intersectionPoint l m = z.1 :=
    intersectionPoint_eq_of_ne hlm (lineThroughPoints_incident_right x z.1) hzm
  simp only [Agree, pencilSide]
  simpa [l, hinter]

lemma pencilLine_injective_on_exterior (x : Point F) (m : Line F)
    (hxm : ¬ Incident x m) :
    Set.InjOn (fun z : BasePoint F ↦ lineThroughPoints x z.1)
      {z | Incident z.1 m} := by
  intro z hz w hw hline
  apply Subtype.ext
  let l := lineThroughPoints x z.1
  have hlm : l ≠ m := pencilLine_ne_exterior hxm hz
  apply point_unique_of_two_lines hlm
  · exact lineThroughPoints_incident_right x z.1
  · exact hz
  · change Incident w.1 (lineThroughPoints x z.1)
    have hline' : lineThroughPoints x z.1 = lineThroughPoints x w.1 := hline
    exact hline'.symm ▸ lineThroughPoints_incident_right x w.1
  · exact hw

lemma ordinary_match_card_le_balance
    (a : Labeling F) {balance : ℕ} (hbal : IsBalanced balance a)
    (x : Point F) (m : Line F) (hxm : ¬ Incident x m)
    (S : Finset (BasePoint F)) (hS : ∀ z ∈ S, Incident z.1 m)
    (side : Bool) :
    (S.filter fun z ↦ (pencilSide a x z = lineSide a m z) = side).card ≤
      balance := by
  classical
  let U := S.filter fun z ↦
    (pencilSide a x z = lineSide a m z) = side
  let f : BasePoint F → Line F := fun z ↦ lineThroughPoints x z.1
  have hinj : Set.InjOn f U := by
    intro z hz w hw
    apply pencilLine_injective_on_exterior x m hxm
    · exact hS z (Finset.mem_filter.mp hz).1
    · exact hS w (Finset.mem_filter.mp hw).1
  have hcard : U.card = (U.image f).card :=
    (Finset.card_image_of_injOn hinj).symm
  rw [hcard]
  cases side
  · have hsub : U.image f ⊆
        (linesThrough x).filter fun l ↦ ¬ Agree a l m := by
      intro l hl
      obtain ⟨z, hzU, rfl⟩ := Finset.mem_image.mp hl
      have hz := Finset.mem_filter.mp hzU
      apply Finset.mem_filter.mpr
      refine ⟨(mem_linesThrough_iff x _).mpr
        (lineThroughPoints_incident_left x z.1), ?_⟩
      have heq := (pencilSide_eq_edgeSide_iff_agree a hxm (hS z hz.1))
      have hne : ¬ pencilSide a x z = a m ⟨z.1, hS z hz.1⟩ := by
        intro h
        simpa [lineSide, hS z hz.1, h] using hz.2
      exact fun hagree ↦ hne (heq.mpr hagree)
    exact (Finset.card_le_card hsub).trans (hbal x m hxm).2
  · have hsub : U.image f ⊆
        (linesThrough x).filter fun l ↦ Agree a l m := by
      intro l hl
      obtain ⟨z, hzU, rfl⟩ := Finset.mem_image.mp hl
      have hz := Finset.mem_filter.mp hzU
      apply Finset.mem_filter.mpr
      refine ⟨(mem_linesThrough_iff x _).mpr
        (lineThroughPoints_incident_left x z.1), ?_⟩
      apply (pencilSide_eq_edgeSide_iff_agree a hxm (hS z hz.1)).mp
      simpa [lineSide, hS z hz.1] using hz.2
    exact (Finset.card_le_card hsub).trans (hbal x m hxm).1

noncomputable def edgePencilWeight {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (center : Point F) (e : Edge F q t) (matchSide : Bool) : ℕ :=
  ∑ z : BasePoint F,
    if (pencilSide a center z = edgeSideAt a e z) = matchSide then
      edgeWeightAt a hqmod hqK e z else 0

lemma edgePencilWeight_le {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) {balance : ℕ} (hbal : IsBalanced balance a)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (center : Point F) (e : Edge F q t)
    (hcenter : ¬ Incident center e.1) (heActive : e ∈ activeTemplate e.1)
    (matchSide : Bool) :
    edgePencilWeight a hqmod hqK center e matchSide ≤ balance + 8 := by
  classical
  rcases e with ⟨m, row | row⟩
  · by_cases hm : Incident (basePoint : Point F) m
    · let S := smallLinePoints m
      have hS : ∀ z ∈ S, Incident z.1 m := fun z hz ↦
        (mem_smallLinePoints_iff m z).mp hz
      let U := S.filter fun z ↦
        (pencilSide a center z = lineSide a m z) = matchSide
      have hU := ordinary_match_card_le_balance a hbal center m hcenter S hS matchSide
      calc
        edgePencilWeight a hqmod hqK center (m, Sum.inl row) matchSide = U.card := by
          rw [edgePencilWeight, Finset.card_eq_sum_ones]
          let Q : BasePoint F → ℕ := fun z ↦
            if (pencilSide a center z =
                edgeSideAt a
                  (m, (Sum.inl row : Fin t × Fin t ⊕ ZMod q × ZMod q)) z) =
                matchSide then
              edgeWeightAt a hqmod hqK
                (m, (Sum.inl row : Fin t × Fin t ⊕ ZMod q × ZMod q)) z else 0
          change (∑ z : BasePoint F, Q z) = ∑ _z ∈ U, 1
          calc
            (∑ z : BasePoint F, Q z) = ∑ z ∈ U, Q z := by
              symm
              apply Finset.sum_subset (Finset.subset_univ U)
              intro z _ hznot
              by_cases hzm : Incident z.1 m
              · have hzS : z ∈ S := (mem_smallLinePoints_iff m z).mpr hzm
                have hpred : ¬ (pencilSide a center z =
                    lineSide a m z) = matchSide := by
                  simpa [U, hzS] using hznot
                cases matchSide <;>
                  simp_all [Q, edgeWeightAt, edgeSideAt, lineSide]
              · simp [Q, edgeWeightAt, hzm]
            _ = ∑ _z ∈ U, 1 := by
              apply Finset.sum_congr rfl
              intro z hzU
              have hz := Finset.mem_filter.mp hzU
              have hzm := hS z hz.1
              cases matchSide <;>
                simp_all [Q, edgeWeightAt, edgeSideAt, lineSide]
        _ ≤ balance := hU
        _ ≤ balance + 8 := by omega
    · have : (m, (Sum.inl row : Fin t × Fin t ⊕ ZMod q × ZMod q)) ∉
          activeTemplate m := by
        rw [activeTemplate, if_neg hm]
        simp
      exact (this heActive).elim
  · by_cases hm : Incident (basePoint : Point F) m
    · have : (m, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) ∉
          activeTemplate m := by
        rw [activeTemplate, if_pos hm]
        simp
      exact (this heActive).elim
    · let S := ordinaryPoints m
      have hS : ∀ z ∈ S, Incident z.1 m := fun z hz ↦
        (mem_smallLinePoints_iff m z).mp (Finset.mem_sdiff.mp hz).1
      let U := S.filter fun z ↦
        (pencilSide a center z = lineSide a m z) = matchSide
      have hU := ordinary_match_card_le_balance a hbal center m hcenter S hS matchSide
      have hordinary :
          (∑ z ∈ S,
            if (pencilSide a center z = edgeSideAt a
                (m, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) z) =
                matchSide then edgeWeightAt a hqmod hqK
                  (m, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) z
              else 0) = U.card := by
        rw [Finset.card_eq_sum_ones]
        change _ = ∑ z ∈ S.filter (fun z ↦
          (pencilSide a center z = lineSide a m z) = matchSide), 1
        rw [← Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro z hz
        rcases Finset.mem_filter.mp hz with ⟨hzS, hp⟩
        have hzm := hS z hzS
        have hza : assignedLine z.1 ≠ m := by
          simpa [mem_assignedFiber_iff] using (Finset.mem_sdiff.mp hzS).2
        simp [edgeSideAt, edgeWeightAt, lineSide, hzm, hm, hza, hp]
      have hexception :
          (∑ z ∈ assignedFiber m,
            if (pencilSide a center z = edgeSideAt a
                (m, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) z) =
                matchSide then edgeWeightAt a hqmod hqK
                  (m, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) z
              else 0) ≤ exceptionalWeight m hm hqmod hqK row := by
        calc
          _ ≤ ∑ z ∈ assignedFiber m,
              edgeWeightAt a hqmod hqK
                (m, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) z := by
            apply Finset.sum_le_sum
            intro z _
            split <;> simp
          _ = exceptionalWeight m hm hqmod hqK row := by
            calc
              _ = ∑ z ∈ assignedFiber m,
                  exceptionalWeightAt m hm hqmod hqK row z := by
                apply Finset.sum_congr rfl
                intro z hz
                have hzm := (mem_smallLinePoints_iff m z).mp
                  (assignedFiber_subset_smallLinePoints m hz)
                have hza := (mem_assignedFiber_iff m z).mp hz
                simp [edgeWeightAt, hzm, hm, hza]
              _ = _ := sum_exceptionalWeightAt m hm hqmod hqK row
      have hsupport :
          edgePencilWeight a hqmod hqK center
            (m, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) matchSide ≤
            (∑ z ∈ S,
              if (pencilSide a center z = edgeSideAt a
                  (m, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) z) =
                  matchSide then edgeWeightAt a hqmod hqK
                    (m, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) z
                else 0) +
            ∑ z ∈ assignedFiber m,
              if (pencilSide a center z = edgeSideAt a
                  (m, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) z) =
                  matchSide then edgeWeightAt a hqmod hqK
                    (m, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) z
                else 0 := by
        rw [edgePencilWeight]
        let P := fun z : BasePoint F ↦
          if (pencilSide a center z = edgeSideAt a
              (m, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) z) =
              matchSide then edgeWeightAt a hqmod hqK
                (m, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) z else 0
        have hpartition : S ∪ assignedFiber m = smallLinePoints m := by
          exact Finset.sdiff_union_of_subset (assignedFiber_subset_smallLinePoints m)
        have hdisj : Disjoint S (assignedFiber m) := Finset.sdiff_disjoint
        change (∑ z : BasePoint F, P z) ≤
          (∑ z ∈ S, P z) + ∑ z ∈ assignedFiber m, P z
        calc
          ∑ z : BasePoint F, P z = ∑ z ∈ smallLinePoints m, P z := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro z _ hznot
            have hnot : ¬ Incident z.1 m := by
              simpa [mem_smallLinePoints_iff] using hznot
            simp [P, edgeWeightAt, hnot]
          _ = (∑ z ∈ S, P z) + ∑ z ∈ assignedFiber m, P z := by
            rw [← Finset.sum_union hdisj, hpartition]
          _ ≤ _ := le_rfl
      rw [hordinary] at hsupport
      exact hsupport.trans (Nat.add_le_add hU
        (hexception.trans (exceptionalWeight_le_eight m hm hqmod hqK row)))

/-- All original matching blocks supplied by one edge at one copy. -/
noncomputable def originalAt {q t : ℕ}
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (e : Edge F q t) (x : BasePoint F) : Finset (Fin t) :=
  largeOriginalAt A e x ∪
    Compression.lift hq ht (smallPiecesAt hqmod hqK e x)

lemma originalAt_card_le_twice_weight {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (e : Edge F q t) (x : BasePoint F) :
    (originalAt A hqmod hqK hq ht e x).card ≤
      2 * edgeWeightAt a hqmod hqK e x := by
  calc
    (originalAt A hqmod hqK hq ht e x).card ≤
        (largeOriginalAt A e x).card +
          (Compression.lift hq ht (smallPiecesAt hqmod hqK e x)).card :=
      Finset.card_union_le _ _
    _ ≤ (largeOriginalAt A e x).card +
        2 * (smallPiecesAt hqmod hqK e x).card :=
      Nat.add_le_add_left (Compression.lift_card_le_twice hq ht _) _
    _ ≤ 2 * ((largeOriginalAt A e x).card +
        (smallPiecesAt hqmod hqK e x).card) := by omega
    _ ≤ 2 * edgeWeightAt a hqmod hqK e x :=
      Nat.mul_le_mul_left 2 (large_small_card_le_weight a A hqmod hqK e x)

lemma edgeWeightAt_le_eight_of_active {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (e : Edge F q t) (x : BasePoint F) (he : e ∈ activeTemplate e.1) :
    edgeWeightAt a hqmod hqK e x ≤ 8 := by
  rcases e with ⟨l, row | row⟩
  · by_cases hl : Incident (basePoint : Point F) l
    · by_cases hxl : Incident x.1 l <;> simp [edgeWeightAt, hl, hxl]
    · have : (l, (Sum.inl row : Fin t × Fin t ⊕ ZMod q × ZMod q)) ∉
          activeTemplate l := by
        rw [activeTemplate, if_neg hl]
        simp
      exact (this he).elim
  · by_cases hl : Incident (basePoint : Point F) l
    · have : (l, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) ∉
          activeTemplate l := by
        rw [activeTemplate, if_pos hl]
        simp
      exact (this he).elim
    · by_cases hxl : Incident x.1 l
      · by_cases hx : assignedLine x.1 = l
        · simp only [edgeWeightAt, hxl, hl, hx, dite_true]
          have hpart : exceptionalWeightAt l hl hqmod hqK row x ≤
              exceptionalWeight l hl hqmod hqK row := by
            have hxmem : x ∈ assignedFiber l := (mem_assignedFiber_iff l x).mpr hx
            calc
              exceptionalWeightAt l hl hqmod hqK row x ≤
                  ∑ z ∈ assignedFiber l,
                    exceptionalWeightAt l hl hqmod hqK row z := by
                exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hxmem
              _ = exceptionalWeight l hl hqmod hqK row :=
                sum_exceptionalWeightAt l hl hqmod hqK row
          exact hpart.trans (exceptionalWeight_le_eight l hl hqmod hqK row)
        · simp [edgeWeightAt, hxl, hl, hx]
      · simp [edgeWeightAt, hxl]

/-- For the unique pencil line through the base point, count original blocks
rather than compressed pieces.  This removes the compression error on that
line in the exact-concentration argument. -/
noncomputable def exactEdgeWeightAt {q t : ℕ}
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (center : Point F) (e : Edge F q t) (z : BasePoint F) : ℕ :=
  if Incident (basePoint : Point F) (lineThroughPoints center z.1) then
    (originalAt A hqmod hqK hq ht e z).card
  else edgeWeightAt a hqmod hqK e z

noncomputable def exactSideWeight {q t : ℕ}
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (center : Point F) (C : Finset (Edge F q t))
    (z : BasePoint F) (side : Bool) : ℕ :=
  ∑ e ∈ C, if edgeSideAt a e z = side then
    exactEdgeWeightAt a A hqmod hqK hq ht center e z else 0

noncomputable def exactMatchWeight {q t : ℕ}
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (center : Point F) (C : Finset (Edge F q t)) (z : BasePoint F) : ℕ :=
  exactSideWeight a A hqmod hqK hq ht center C z (pencilSide a center z)

noncomputable def exactMismatchWeight {q t : ℕ}
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (center : Point F) (C : Finset (Edge F q t)) (z : BasePoint F) : ℕ :=
  exactSideWeight a A hqmod hqK hq ht center C z (!(pencilSide a center z))

lemma selectedOriginal_card_le_exactSideWeight_of_base_pencil
    {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (center : Point F) (C : Finset (Edge F q t))
    (z : BasePoint F) (side : Bool)
    (hspecial : Incident (basePoint : Point F)
      (lineThroughPoints center z.1)) :
    (selectedOriginal A a hqmod hqK hq ht C z side).card ≤
      exactSideWeight a A hqmod hqK hq ht center C z side := by
  classical
  let U : Finset (Edge F q t) := C.filter fun e ↦ edgeSideAt a e z = side
  have hlarge : selectedLargeOriginal A a C z side ⊆
      U.biUnion fun e ↦ originalAt A hqmod hqK hq ht e z := by
    intro i hi
    obtain ⟨e, heC, hie⟩ := Finset.mem_biUnion.mp hi
    have hside : edgeSideAt a e z = side := by
      by_contra hne
      simp [selectedLargeOriginal, hne] at hie
    apply Finset.mem_biUnion.mpr
    refine ⟨e, Finset.mem_filter.mpr ⟨heC, hside⟩, ?_⟩
    have hie' : i ∈ largeOriginalAt A e z := by simpa [hside] using hie
    exact Finset.mem_union.mpr (Or.inl hie')
  have hsmallPieces : selectedSmallPieces a hqmod hqK C z side ⊆
      U.biUnion fun e ↦ smallPiecesAt hqmod hqK e z := by
    intro c hc
    obtain ⟨e, heC, hce⟩ := Finset.mem_biUnion.mp hc
    have hside : edgeSideAt a e z = side := by
      by_contra hne
      simp [selectedSmallPieces, hne] at hce
    have hce' : c ∈ smallPiecesAt hqmod hqK e z := by simpa [hside] using hce
    exact Finset.mem_biUnion.mpr
      ⟨e, Finset.mem_filter.mpr ⟨heC, hside⟩, hce'⟩
  have hsmall : Compression.lift hq ht
      (selectedSmallPieces a hqmod hqK C z side) ⊆
      U.biUnion fun e ↦ originalAt A hqmod hqK hq ht e z := by
    intro i hi
    have hpiece := Compression.mem_lift_iff hq ht _ i |>.mp hi
    have hpiece' := hsmallPieces hpiece
    obtain ⟨e, heU, hce⟩ := Finset.mem_biUnion.mp hpiece'
    apply Finset.mem_biUnion.mpr
    refine ⟨e, heU, Finset.mem_union.mpr (Or.inr ?_)⟩
    exact (Compression.mem_lift_iff hq ht _ i).mpr hce
  have hselected : selectedOriginal A a hqmod hqK hq ht C z side ⊆
      U.biUnion fun e ↦ originalAt A hqmod hqK hq ht e z := by
    exact Finset.union_subset hlarge hsmall
  calc
    (selectedOriginal A a hqmod hqK hq ht C z side).card ≤
        (U.biUnion fun e ↦ originalAt A hqmod hqK hq ht e z).card :=
      Finset.card_le_card hselected
    _ ≤ ∑ e ∈ U, (originalAt A hqmod hqK hq ht e z).card :=
      Finset.card_biUnion_le
    _ = exactSideWeight a A hqmod hqK hq ht center C z side := by
      rw [exactSideWeight]
      simp only [exactEdgeWeightAt, hspecial, if_pos]
      rw [Finset.sum_filter]

lemma selectedOriginal_card_le_exactSideWeight_add_defect
    {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (center : Point F) (C : Finset (Edge F q t))
    (z : BasePoint F) (side : Bool) :
    (selectedOriginal A a hqmod hqK hq ht C z side).card ≤
      exactSideWeight a A hqmod hqK hq ht center C z side + (t - q) := by
  by_cases hspecial : Incident (basePoint : Point F)
      (lineThroughPoints center z.1)
  · exact (selectedOriginal_card_le_exactSideWeight_of_base_pencil
      a A hqmod hqK hq ht center C z side hspecial).trans
        (Nat.le_add_right _ _)
  · simpa [exactSideWeight, exactEdgeWeightAt, sideWeight, hspecial] using
      selectedOriginal_card_le_weight_add_defect A a hqmod hqK hqpos hq ht
        C z side

lemma selectedOriginal_card_le_twice_exactSideWeight
    {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (center : Point F) (C : Finset (Edge F q t))
    (z : BasePoint F) (side : Bool) :
    (selectedOriginal A a hqmod hqK hq ht C z side).card ≤
      2 * exactSideWeight a A hqmod hqK hq ht center C z side := by
  by_cases hspecial : Incident (basePoint : Point F)
      (lineThroughPoints center z.1)
  · exact (selectedOriginal_card_le_exactSideWeight_of_base_pencil
      a A hqmod hqK hq ht center C z side hspecial).trans
        (Nat.le_mul_of_pos_left _ (by norm_num))
  · simpa [exactSideWeight, exactEdgeWeightAt, sideWeight, hspecial] using
      selectedOriginal_card_le_twice_weight A a hqmod hqK hq ht C z side

noncomputable def specialPoints (center : Point F) (m : Line F) :
    Finset (BasePoint F) :=
  Finset.univ.filter fun z ↦
    Incident z.1 m ∧ Incident (basePoint : Point F)
      (lineThroughPoints center z.1)

lemma specialPoints_card_le_one (center : Point F) (m : Line F)
    (hcenterBase : center ≠ (basePoint : Point F))
    (hcenter : ¬ Incident center m) :
    (specialPoints center m).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro z hz w hw
  have hz' := Finset.mem_filter.mp hz |>.2
  have hw' := Finset.mem_filter.mp hw |>.2
  let l₀ := lineThroughPoints center (basePoint : Point F)
  have hzl : Incident z.1 l₀ := by
    have heq : lineThroughPoints center z.1 = l₀ := by
      apply line_unique_of_two_points hcenterBase
      · exact lineThroughPoints_incident_left center z.1
      · exact hz'.2
      · exact lineThroughPoints_incident_left center (basePoint : Point F)
      · exact lineThroughPoints_incident_right center (basePoint : Point F)
    rw [← heq]
    exact lineThroughPoints_incident_right center z.1
  have hwl : Incident w.1 l₀ := by
    have heq : lineThroughPoints center w.1 = l₀ := by
      apply line_unique_of_two_points hcenterBase
      · exact lineThroughPoints_incident_left center w.1
      · exact hw'.2
      · exact lineThroughPoints_incident_left center (basePoint : Point F)
      · exact lineThroughPoints_incident_right center (basePoint : Point F)
    rw [← heq]
    exact lineThroughPoints_incident_right center w.1
  have hlm : l₀ ≠ m := by
    intro heq
    apply hcenter
    rw [← heq]
    exact lineThroughPoints_incident_left center (basePoint : Point F)
  exact Subtype.ext (point_unique_of_two_lines hlm hzl hz'.1 hwl hw'.1)

lemma exactEdgeWeightAt_le_add_correction {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (center : Point F) (e : Edge F q t) (z : BasePoint F)
    (heActive : e ∈ activeTemplate e.1) :
    exactEdgeWeightAt a A hqmod hqK hq ht center e z ≤
      edgeWeightAt a hqmod hqK e z +
        if z ∈ specialPoints center e.1 then 16 else 0 := by
  classical
  by_cases hspecial : Incident (basePoint : Point F)
      (lineThroughPoints center z.1)
  · by_cases hze : Incident z.1 e.1
    · have hzmem : z ∈ specialPoints center e.1 := by
        simp [specialPoints, hze, hspecial]
      have horig := originalAt_card_le_twice_weight a A hqmod hqK hq ht e z
      have hw := edgeWeightAt_le_eight_of_active a hqmod hqK e z heActive
      simp only [exactEdgeWeightAt, hspecial, if_pos, hzmem]
      omega
    · have hznot : z ∉ specialPoints center e.1 := by
        simp [specialPoints, hze]
      simp [exactEdgeWeightAt, originalAt, largeOriginalAt, smallPiecesAt,
        hspecial, hze, hznot, edgeWeightAt]
  · have hznot : z ∉ specialPoints center e.1 := by
      simp [specialPoints, hspecial]
    simp [exactEdgeWeightAt, hspecial, hznot]

noncomputable def exactEdgePencilWeight {q t : ℕ}
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (center : Point F) (e : Edge F q t) (matchSide : Bool) : ℕ :=
  ∑ z : BasePoint F,
    if (pencilSide a center z = edgeSideAt a e z) = matchSide then
      exactEdgeWeightAt a A hqmod hqK hq ht center e z else 0

lemma exactEdgePencilWeight_le {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    {balance : ℕ} (hbal : IsBalanced balance a)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (center : Point F) (e : Edge F q t)
    (hcenterBase : center ≠ (basePoint : Point F))
    (hcenter : ¬ Incident center e.1)
    (heActive : e ∈ activeTemplate e.1) (matchSide : Bool) :
    exactEdgePencilWeight a A hqmod hqK hq ht center e matchSide ≤
      balance + 24 := by
  classical
  let corr : BasePoint F → ℕ := fun z ↦
    if z ∈ specialPoints center e.1 then 16 else 0
  have hpoint : ∀ z : BasePoint F,
      (if (pencilSide a center z = edgeSideAt a e z) = matchSide then
          exactEdgeWeightAt a A hqmod hqK hq ht center e z else 0) ≤
        (if (pencilSide a center z = edgeSideAt a e z) = matchSide then
          edgeWeightAt a hqmod hqK e z else 0) + corr z := by
    intro z
    split
    · exact (exactEdgeWeightAt_le_add_correction a A hqmod hqK hq ht
        center e z heActive)
    · simp
  have hcorr : (∑ z : BasePoint F, corr z) ≤ 16 := by
    calc
      (∑ z : BasePoint F, corr z) =
          16 * (specialPoints center e.1).card := by
        simp [corr, Nat.mul_comm]
      _ ≤ 16 * 1 := Nat.mul_le_mul_left 16
        (specialPoints_card_le_one center e.1 hcenterBase hcenter)
      _ = 16 := by norm_num
  calc
    exactEdgePencilWeight a A hqmod hqK hq ht center e matchSide ≤
        edgePencilWeight a hqmod hqK center e matchSide +
          ∑ z : BasePoint F, corr z := by
      rw [exactEdgePencilWeight, edgePencilWeight, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun z _ ↦ hpoint z
    _ ≤ (balance + 8) + 16 := Nat.add_le_add
      (edgePencilWeight_le a hbal hqmod hqK center e hcenter heActive matchSide)
      hcorr
    _ = balance + 24 := by omega

lemma useful_lineThrough_eq {x : BasePoint F} {l : Line F}
    {z : BasePoint F} (hxl : Incident x.1 l)
    (hz : z ∈ usefulPoints x l) :
    lineThroughPoints x.1 z.1 = l := by
  apply lineThroughPoints_eq_of_ne
  · exact fun h ↦ usefulPoint_ne_center hz (Subtype.ext h.symm)
  · exact hxl
  · exact (mem_smallLinePoints_iff l z).mp (usefulPoints_subset_line x l hz)

lemma active_edge_exact_weight_one_on_useful {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {x : BasePoint F} {l : Line F} {z : BasePoint F}
    (hxl : Incident x.1 l) (hz : z ∈ usefulPoints x l)
    {e : Edge F q t} (heline : e.1 = l)
    (heActive : e ∈ activeTemplate e.1) :
    edgeSideAt a e z = pencilSide a x.1 z ∧
      exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z = 1 := by
  classical
  have hzl : Incident z.1 l :=
    (mem_smallLinePoints_iff l z).mp (usefulPoints_subset_line x l hz)
  have hza : assignedLine z.1 ≠ l := usefulPoint_not_assigned hz
  have hline : lineThroughPoints x.1 z.1 = l := useful_lineThrough_eq hxl hz
  cases hline
  rcases e with ⟨m, tag⟩
  change m = lineThroughPoints x.1 z.1 at heline
  subst m
  by_cases hl : Incident (basePoint : Point F) (lineThroughPoints x.1 z.1)
  · rcases tag with row | row
    · constructor
      · simp [edgeSideAt, pencilSide, hzl]
      · simp [exactEdgeWeightAt, hl, originalAt, largeOriginalAt,
          smallPiecesAt, hzl]
    · have : (lineThroughPoints x.1 z.1,
          (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) ∉
          activeTemplate (lineThroughPoints x.1 z.1) := by
        rw [activeTemplate, if_pos hl]
        simp
      exact (this heActive).elim
  · rcases tag with row | row
    · have : (lineThroughPoints x.1 z.1,
          (Sum.inl row : Fin t × Fin t ⊕ ZMod q × ZMod q)) ∉
          activeTemplate (lineThroughPoints x.1 z.1) := by
        rw [activeTemplate, if_neg hl]
        simp
      exact (this heActive).elim
    · constructor
      · simp [edgeSideAt, pencilSide, hzl]
      · simp [exactEdgeWeightAt, hl, edgeWeightAt, hzl, hza]

lemma templateSlice_card_le_exactMatchWeight {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    {x : BasePoint F} {l : Line F} (hxl : Incident x.1 l)
    {z : BasePoint F} (hz : z ∈ usefulPoints x l) :
    (templateSlice C l).card ≤
      exactMatchWeight a A hqmod hqK hq ht x.1 C z := by
  classical
  rw [Finset.card_eq_sum_ones, exactMatchWeight, exactSideWeight]
  let w : Edge F q t → ℕ := fun e ↦
    if edgeSideAt a e z = pencilSide a x.1 z then
      exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0
  calc
    (∑ e ∈ templateSlice C l, 1) = ∑ e ∈ templateSlice C l, w e := by
      apply Finset.sum_congr rfl
      intro e he
      have he' := (mem_templateSlice_iff C l e).mp he
      have hone := active_edge_exact_weight_one_on_useful a A hqmod hqK hq ht
        hxl hz he'.2 (hactive e he'.1)
      simp [w, hone.1, hone.2]
    _ ≤ ∑ e ∈ C, w e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact fun e he ↦ (mem_templateSlice_iff C l e).mp he |>.1
      · intro e _ _
        exact Nat.zero_le _

lemma pencil_local_weak_waste {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    {x : BasePoint F} {l : Line F} (hxl : Incident x.1 l)
    {z : BasePoint F} (hz : z ∈ usefulPoints x l)
    (hsmall : 2 * (templateCap q t l -
      exactMatchWeight a A hqmod hqK hq ht x.1 C z) ≤ t) :
    11 * (templateCap q t l -
        exactMatchWeight a A hqmod hqK hq ht x.1 C z) ≤
      10 * (exactMismatchWeight a A hqmod hqK hq ht x.1 C z + (t - q)) := by
  let f := exactMatchWeight a A hqmod hqK hq ht x.1 C z
  let g := exactMismatchWeight a A hqmod hqK hq ht x.1 C z
  let cap := templateCap q t l
  by_cases hcap : cap ≤ f
  · omega
  · have hf : f ≤ cap := by omega
    have hcapT : cap ≤ t := by
      unfold cap templateCap
      split <;> omega
    have haT : cap - f ≤ t := by omega
    have hline : lineThroughPoints x.1 z.1 = l := useful_lineThrough_eq hxl hz
    have hcov := selectedOriginal_covers D a A hqmod hqK hq ht hcover z
    have hchosen :
        (selectedOriginal A a hqmod hqK hq ht C z
          (pencilSide a x.1 z)).card ≤ t - (cap - f) := by
      by_cases hl : Incident (basePoint : Point F) l
      · have hspecial : Incident (basePoint : Point F)
            (lineThroughPoints x.1 z.1) := by simpa [hline] using hl
        have hbound := selectedOriginal_card_le_exactSideWeight_of_base_pencil
          a A hqmod hqK hq ht x.1 C z (pencilSide a x.1 z) hspecial
        change _ ≤ f at hbound
        have hcapeq : cap = t := by simp [cap, templateCap, hl]
        omega
      · have hbound := selectedOriginal_card_le_exactSideWeight_add_defect
          a A hqmod hqK hqpos hq ht x.1 C z (pencilSide a x.1 z)
        change _ ≤ f + (t - q) at hbound
        have hcapeq : cap = q := by simp [cap, templateCap, hl]
        omega
    have hopen : 11 * (cap - f) ≤
        10 * (selectedOriginal A a hqmod hqK hq ht C z
          (!(pencilSide a x.1 z))).card := by
      cases hs : pencilSide a x.1 z
      · exact (D.opposite_original_blocks_of_expansion hexp hcov haT
          (by simpa [hs] using hchosen)).1 (by simpa [cap, f] using hsmall)
      · exact (D.opposite_original_blocks_of_expansion_symm hexp hcov haT
          (by simpa [hs] using hchosen)).1 (by simpa [cap, f] using hsmall)
    have hother := selectedOriginal_card_le_exactSideWeight_add_defect
      a A hqmod hqK hqpos hq ht x.1 C z (!(pencilSide a x.1 z))
    change _ ≤ g + (t - q) at hother
    exact hopen.trans (Nat.mul_le_mul_left 10 hother)

lemma pencil_local_strong_waste {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    {x : BasePoint F} {l : Line F} (hxl : Incident x.1 l)
    {z : BasePoint F} (hz : z ∈ usefulPoints x l)
    (hsmall : 10 * (templateCap q t l -
      exactMatchWeight a A hqmod hqK hq ht x.1 C z) ≤ t) :
    3 * (templateCap q t l -
        exactMatchWeight a A hqmod hqK hq ht x.1 C z) ≤
      2 * exactMismatchWeight a A hqmod hqK hq ht x.1 C z := by
  let f := exactMatchWeight a A hqmod hqK hq ht x.1 C z
  let g := exactMismatchWeight a A hqmod hqK hq ht x.1 C z
  let cap := templateCap q t l
  by_cases hcap : cap ≤ f
  · omega
  · have hf : f ≤ cap := by omega
    have hcapT : cap ≤ t := by
      unfold cap templateCap
      split <;> omega
    have haT : cap - f ≤ t := by omega
    have hline : lineThroughPoints x.1 z.1 = l := useful_lineThrough_eq hxl hz
    have hcov := selectedOriginal_covers D a A hqmod hqK hq ht hcover z
    have hchosen :
        (selectedOriginal A a hqmod hqK hq ht C z
          (pencilSide a x.1 z)).card ≤ t - (cap - f) := by
      by_cases hl : Incident (basePoint : Point F) l
      · have hspecial : Incident (basePoint : Point F)
            (lineThroughPoints x.1 z.1) := by simpa [hline] using hl
        have hbound := selectedOriginal_card_le_exactSideWeight_of_base_pencil
          a A hqmod hqK hq ht x.1 C z (pencilSide a x.1 z) hspecial
        change _ ≤ f at hbound
        have hcapeq : cap = t := by simp [cap, templateCap, hl]
        omega
      · have hbound := selectedOriginal_card_le_exactSideWeight_add_defect
          a A hqmod hqK hqpos hq ht x.1 C z (pencilSide a x.1 z)
        change _ ≤ f + (t - q) at hbound
        have hcapeq : cap = q := by simp [cap, templateCap, hl]
        omega
    have hopen : 3 * (cap - f) ≤
        (selectedOriginal A a hqmod hqK hq ht C z
          (!(pencilSide a x.1 z))).card := by
      cases hs : pencilSide a x.1 z
      · exact (D.opposite_original_blocks_of_expansion hexp hcov haT
          (by simpa [hs] using hchosen)).2 (by simpa [cap, f] using hsmall)
      · exact (D.opposite_original_blocks_of_expansion_symm hexp hcov haT
          (by simpa [hs] using hchosen)).2 (by simpa [cap, f] using hsmall)
    have hother := selectedOriginal_card_le_twice_exactSideWeight
      a A hqmod hqK hq ht x.1 C z (!(pencilSide a x.1 z))
    change _ ≤ 2 * g at hother
    exact hopen.trans hother

lemma coversByIndices_card_sum_ge (D : Expander.System 100 t)
    {L R : Finset (Fin t)} (hcover : D.CoversByIndices L R) :
    t ≤ L.card + R.card := by
  classical
  let j : Fin 100 := ⟨0, by norm_num⟩
  let f : Fin t → Fin t ⊕ Fin t := fun x ↦
    if x ∈ L then Sum.inl x else Sum.inr (D.perm j x)
  have hinj : Function.Injective f := by
    intro x y hxy
    dsimp only [f] at hxy
    split at hxy <;> split at hxy
    · exact Sum.inl.inj hxy
    · contradiction
    · contradiction
    · exact (D.perm j).injective (Sum.inr.inj hxy)
  have hsub : (Finset.univ : Finset (Fin t)).image f ⊆
      L.image Sum.inl ∪ R.image Sum.inr := by
    intro u hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    by_cases hx : x ∈ L
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_image.mpr ⟨x, hx, by simp [f, hx]⟩))
    · have hr : D.perm j x ∈ R := (hcover (j, x)).resolve_left hx
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨D.perm j x, hr, by simp [f, hx]⟩))
  calc
    t = ((Finset.univ : Finset (Fin t)).image f).card := by
      rw [Finset.card_image_iff.mpr]
      · simp
      · intro x _ y _ h
        exact hinj h
    _ ≤ (L.image Sum.inl ∪ R.image Sum.inr).card := Finset.card_le_card hsub
    _ ≤ (L.image Sum.inl).card + (R.image Sum.inr).card := Finset.card_union_le _ _
    _ = L.card + R.card := by
      rw [Finset.card_image_of_injective _ Sum.inl_injective,
        Finset.card_image_of_injective _ Sum.inr_injective]

noncomputable def exactTotalWeight {q t : ℕ}
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (center : Point F) (C : Finset (Edge F q t)) (z : BasePoint F) : ℕ :=
  ∑ e ∈ C, exactEdgeWeightAt a A hqmod hqK hq ht center e z

lemma exact_match_add_mismatch_eq {q t : ℕ}
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (center : Point F) (C : Finset (Edge F q t)) (z : BasePoint F) :
    exactMatchWeight a A hqmod hqK hq ht center C z +
      exactMismatchWeight a A hqmod hqK hq ht center C z =
        exactTotalWeight a A hqmod hqK hq ht center C z := by
  unfold exactMatchWeight exactMismatchWeight exactSideWeight exactTotalWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  cases h : edgeSideAt a e z <;> cases hp : pencilSide a center z <;> simp

lemma exactTotalWeight_cover_lower {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (center : Point F) (z : BasePoint F) :
    t ≤ exactTotalWeight a A hqmod hqK hq ht center C z + 2 * (t - q) := by
  let L := selectedOriginal A a hqmod hqK hq ht C z false
  let R := selectedOriginal A a hqmod hqK hq ht C z true
  have hcov := selectedOriginal_covers D a A hqmod hqK hq ht hcover z
  have hcard := coversByIndices_card_sum_ge D hcov
  have hL := selectedOriginal_card_le_exactSideWeight_add_defect
    a A hqmod hqK hqpos hq ht center C z false
  have hR := selectedOriginal_card_le_exactSideWeight_add_defect
    a A hqmod hqK hqpos hq ht center C z true
  have hsum := exact_match_add_mismatch_eq a A hqmod hqK hq ht center C z
  unfold exactMatchWeight exactMismatchWeight at hsum
  cases hp : pencilSide a center z <;> simp [hp] at hsum <;> omega

lemma exactTotalWeight_cover_lower_of_base_pencil {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (center : Point F) (z : BasePoint F)
    (hspecial : Incident (basePoint : Point F)
      (lineThroughPoints center z.1)) :
    t ≤ exactTotalWeight a A hqmod hqK hq ht center C z := by
  let L := selectedOriginal A a hqmod hqK hq ht C z false
  let R := selectedOriginal A a hqmod hqK hq ht C z true
  have hcov := selectedOriginal_covers D a A hqmod hqK hq ht hcover z
  have hcard := coversByIndices_card_sum_ge D hcov
  have hL := selectedOriginal_card_le_exactSideWeight_of_base_pencil
    a A hqmod hqK hq ht center C z false hspecial
  have hR := selectedOriginal_card_le_exactSideWeight_of_base_pencil
    a A hqmod hqK hq ht center C z true hspecial
  have hsum := exact_match_add_mismatch_eq a A hqmod hqK hq ht center C z
  unfold exactMatchWeight exactMismatchWeight at hsum
  cases hp : pencilSide a center z <;> simp [hp] at hsum <;> omega

lemma active_edge_exact_weight_le_two_on_incident {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (center : Point F) (e : Edge F q t) (z : BasePoint F)
    (hze : Incident z.1 e.1) (heActive : e ∈ activeTemplate e.1) :
    exactEdgeWeightAt a A hqmod hqK hq ht center e z ≤ 16 := by
  have hw := edgeWeightAt_le_eight_of_active a hqmod hqK e z heActive
  by_cases hspecial : Incident (basePoint : Point F)
      (lineThroughPoints center z.1)
  · have horig := originalAt_card_le_twice_weight a A hqmod hqK hq ht e z
    rw [exactEdgeWeightAt, if_pos hspecial]
    omega
  · rw [exactEdgeWeightAt, if_neg hspecial]
    omega

lemma sum_useful_exactEdgeWeight_le_two {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {x : BasePoint F} {l : Line F} (hxl : Incident x.1 l)
    (e : Edge F q t) (hexterior : ¬ Incident x.1 e.1)
    (heActive : e ∈ activeTemplate e.1) :
    (∑ z ∈ usefulPoints x l,
      exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z) ≤ 16 := by
  classical
  let U := (usefulPoints x l).filter fun z ↦ Incident z.1 e.1
  have hle : (∑ z ∈ usefulPoints x l,
      exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z) ≤
      ∑ z ∈ U, 16 := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro z hz
    by_cases hze : Incident z.1 e.1
    · simp only [hze, if_true]
      exact active_edge_exact_weight_le_two_on_incident
        a A hqmod hqK hq ht x.1 e z hze heActive
    · simp [hze, exactEdgeWeightAt, originalAt, largeOriginalAt,
        smallPiecesAt, edgeWeightAt]
  have hU : U.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz w hw
    have hz' := Finset.mem_filter.mp hz
    have hw' := Finset.mem_filter.mp hw
    have hlm : l ≠ e.1 := by
      intro heq
      exact hexterior (by simpa [← heq] using hxl)
    apply Subtype.ext
    exact point_unique_of_two_lines hlm
      ((mem_smallLinePoints_iff l z).mp (usefulPoints_subset_line x l hz'.1))
      hz'.2
      ((mem_smallLinePoints_iff l w).mp (usefulPoints_subset_line x l hw'.1))
      hw'.2
  calc
    _ ≤ ∑ _z ∈ U, 16 := hle
    _ = 16 * U.card := by simp [mul_comm]
    _ ≤ 16 * 1 := Nat.mul_le_mul_left 16 hU
    _ = 16 := by norm_num

lemma templateSlice_subset_pencilEdges {q t : ℕ}
    (C : Finset (Edge F q t)) {x : Point F} {l : Line F}
    (hxl : Incident x l) : templateSlice C l ⊆ pencilEdges C x := by
  intro e he
  have he' := (mem_templateSlice_iff C l e).mp he
  exact Finset.mem_filter.mpr ⟨he'.1, by simpa [he'.2] using hxl⟩

lemma exactTotalWeight_eq_slice_add_outside {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    {x : BasePoint F} {l : Line F} (hxl : Incident x.1 l)
    {z : BasePoint F} (hz : z ∈ usefulPoints x l) :
    exactTotalWeight a A hqmod hqK hq ht x.1 C z =
      (templateSlice C l).card +
        ∑ e ∈ C \ pencilEdges C x.1,
          exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z := by
  classical
  let w : Edge F q t → ℕ := fun e ↦
    exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z
  let P := pencilEdges C x.1
  let S := templateSlice C l
  have hPC : P ⊆ C := Finset.filter_subset _ _
  have hSP : S ⊆ P := templateSlice_subset_pencilEdges C hxl
  have hslice : ∑ e ∈ S, w e = S.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro e he
    have he' := (mem_templateSlice_iff C l e).mp he
    exact (active_edge_exact_weight_one_on_useful a A hqmod hqK hq ht
      hxl hz he'.2 (hactive e he'.1)).2
  have hother : ∑ e ∈ P \ S, w e = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have he' := Finset.mem_sdiff.mp he
    have heP := Finset.mem_filter.mp he'.1
    have hel : e.1 ≠ l := by
      intro hel
      exact he'.2 ((mem_templateSlice_iff C l e).mpr ⟨heP.1, hel⟩)
    have hze : ¬ Incident z.1 e.1 := by
      intro hze
      apply hel
      apply line_unique_of_two_points
          (fun h ↦ usefulPoint_ne_center hz (Subtype.ext h.symm))
      · exact heP.2
      · exact hze
      · exact hxl
      · exact (mem_smallLinePoints_iff l z).mp (usefulPoints_subset_line x l hz)
    simp [w, exactEdgeWeightAt, originalAt, largeOriginalAt, smallPiecesAt,
      edgeWeightAt, hze]
  have hPS : ∑ e ∈ P, w e = S.card := by
    calc
      ∑ e ∈ P, w e = (∑ e ∈ S, w e) + ∑ e ∈ P \ S, w e := by
        rw [← Finset.sum_union Finset.disjoint_sdiff,
          Finset.union_sdiff_of_subset hSP]
      _ = S.card := by rw [hslice, hother, Nat.add_zero]
  unfold exactTotalWeight
  change (∑ e ∈ C, w e) = _
  calc
    ∑ e ∈ C, w e = (∑ e ∈ P, w e) + ∑ e ∈ C \ P, w e := by
      rw [← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset hPC]
    _ = S.card + ∑ e ∈ C \ P, w e := by rw [hPS]
    _ = _ := rfl

lemma useful_deficit_le_outside_sum {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    {x : BasePoint F} {l : Line F} (hxl : Incident x.1 l)
    {z : BasePoint F} (hz : z ∈ usefulPoints x l) :
    templateCap q t l - (templateSlice C l).card ≤
      (∑ e ∈ C \ pencilEdges C x.1,
        exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z) + (t - q) := by
  have htotal := exactTotalWeight_eq_slice_add_outside
    a A hqmod hqK hq ht hactive hxl hz
  by_cases hl : Incident (basePoint : Point F) l
  · have hline := useful_lineThrough_eq hxl hz
    have hspecial : Incident (basePoint : Point F)
        (lineThroughPoints x.1 z.1) := by simpa [hline] using hl
    have hlower := exactTotalWeight_cover_lower_of_base_pencil
      D a A hqmod hqK hq ht hcover x.1 z hspecial
    rw [templateCap, if_pos hl]
    omega
  · have hlower := exactTotalWeight_cover_lower D a A hqmod hqK
      hqpos hq ht hcover x.1 z
    rw [templateCap, if_neg hl]
    omega

lemma useful_card_mul_deficit_le {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    {x : BasePoint F} {l : Line F} (hxl : Incident x.1 l) :
    (usefulPoints x l).card *
        (templateCap q t l - (templateSlice C l).card) ≤
      16 * (C \ pencilEdges C x.1).card +
        (usefulPoints x l).card * (t - q) := by
  classical
  let U := usefulPoints x l
  let O := C \ pencilEdges C x.1
  let w : Edge F q t → BasePoint F → ℕ := fun e z ↦
    exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z
  have hpoint : ∀ z ∈ U,
      templateCap q t l - (templateSlice C l).card ≤
        (∑ e ∈ O, w e z) + (t - q) := by
    intro z hz
    exact useful_deficit_le_outside_sum D a A hqmod hqK hqpos hq ht
      hactive hcover hxl hz
  have hsum : ∑ z ∈ U,
      (templateCap q t l - (templateSlice C l).card) ≤
      ∑ z ∈ U, ((∑ e ∈ O, w e z) + (t - q)) :=
    Finset.sum_le_sum fun z hz ↦ hpoint z hz
  have hedge : ∑ e ∈ O, ∑ z ∈ U, w e z ≤ 16 * O.card := by
    calc
      ∑ e ∈ O, ∑ z ∈ U, w e z ≤ ∑ _e ∈ O, 16 := by
        apply Finset.sum_le_sum
        intro e he
        have heC := (Finset.mem_sdiff.mp he).1
        have hexterior : ¬ Incident x.1 e.1 := by
          simpa [pencilEdges, heC] using (Finset.mem_sdiff.mp he).2
        exact sum_useful_exactEdgeWeight_le_two a A hqmod hqK hq ht
          hxl e hexterior (hactive e heC)
      _ = 16 * O.card := by simp [mul_comm]
  have hsum' : U.card *
        (templateCap q t l - (templateSlice C l).card) ≤
      (∑ e ∈ O, ∑ z ∈ U, w e z) + U.card * (t - q) := by
    calc
      U.card * (templateCap q t l - (templateSlice C l).card) =
          ∑ z ∈ U, (templateCap q t l - (templateSlice C l).card) := by
        simp [mul_comm]
      _ ≤ ∑ z ∈ U, ((∑ e ∈ O, w e z) + (t - q)) := hsum
      _ = (∑ e ∈ O, ∑ z ∈ U, w e z) + U.card * (t - q) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        simp [mul_comm]
  have hfinal := hsum'.trans (Nat.add_le_add_right hedge _)
  simpa [U, O, w] using hfinal

lemma sum_useful_pencil_le_univ (x : BasePoint F) (w : BasePoint F → ℕ) :
    (∑ l ∈ linesThrough x.1, ∑ z ∈ usefulPoints x l, w z) ≤
      ∑ z : BasePoint F, w z := by
  classical
  have hdisj : ∀ l ∈ linesThrough x.1, ∀ m ∈ linesThrough x.1,
      l ≠ m → Disjoint (usefulPoints x l) (usefulPoints x m) := by
    intro l hl m hm hlm
    apply Finset.disjoint_left.mpr
    intro z hzl hzm
    apply hlm
    apply line_unique_of_two_points
        (fun h ↦ usefulPoint_ne_center hzl (Subtype.ext h.symm))
    · exact (mem_linesThrough_iff x.1 l).mp hl
    · exact (mem_smallLinePoints_iff l z).mp (usefulPoints_subset_line x l hzl)
    · exact (mem_linesThrough_iff x.1 m).mp hm
    · exact (mem_smallLinePoints_iff m z).mp (usefulPoints_subset_line x m hzm)
  rw [← Finset.sum_biUnion hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)

lemma pencil_pair_count_le (x : BasePoint F) :
    (∑ l ∈ linesThrough x.1, (usefulPoints x l).card) ≤
      Fintype.card F ^ 2 + Fintype.card F := by
  have h := sum_useful_pencil_le_univ x (fun _ ↦ 1)
  simp only [Finset.sum_const_nat, Nat.card_eq_fintype_card] at h
  simpa [card_basePoint, pow_two] using h

lemma exactMatchWeight_eq_slice_add_outside {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    {x : BasePoint F} {l : Line F} (hxl : Incident x.1 l)
    {z : BasePoint F} (hz : z ∈ usefulPoints x l) :
    exactMatchWeight a A hqmod hqK hq ht x.1 C z =
      (templateSlice C l).card +
        ∑ e ∈ C \ pencilEdges C x.1,
          if (pencilSide a x.1 z = edgeSideAt a e z) = true then
            exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0 := by
  classical
  let w : Edge F q t → ℕ := fun e ↦
    if (pencilSide a x.1 z = edgeSideAt a e z) = true then
      exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0
  let P := pencilEdges C x.1
  let S := templateSlice C l
  have hPC : P ⊆ C := Finset.filter_subset _ _
  have hSP : S ⊆ P := templateSlice_subset_pencilEdges C hxl
  have hslice : ∑ e ∈ S, w e = S.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro e he
    have he' := (mem_templateSlice_iff C l e).mp he
    have hone := active_edge_exact_weight_one_on_useful a A hqmod hqK hq ht
      hxl hz he'.2 (hactive e he'.1)
    simp [w, hone.1, hone.2]
  have hother : ∑ e ∈ P \ S, w e = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have he' := Finset.mem_sdiff.mp he
    have heP := Finset.mem_filter.mp he'.1
    have hel : e.1 ≠ l := by
      intro hel
      exact he'.2 ((mem_templateSlice_iff C l e).mpr ⟨heP.1, hel⟩)
    have hze : ¬ Incident z.1 e.1 := by
      intro hze
      apply hel
      apply line_unique_of_two_points
          (fun h ↦ usefulPoint_ne_center hz (Subtype.ext h.symm))
      · exact heP.2
      · exact hze
      · exact hxl
      · exact (mem_smallLinePoints_iff l z).mp (usefulPoints_subset_line x l hz)
    simp [w, exactEdgeWeightAt, originalAt, largeOriginalAt, smallPiecesAt,
      edgeWeightAt, hze]
  have hPS : ∑ e ∈ P, w e = S.card := by
    calc
      ∑ e ∈ P, w e = (∑ e ∈ S, w e) + ∑ e ∈ P \ S, w e := by
        rw [← Finset.sum_union Finset.disjoint_sdiff,
          Finset.union_sdiff_of_subset hSP]
      _ = S.card := by rw [hslice, hother, Nat.add_zero]
  unfold exactMatchWeight exactSideWeight
  calc
    (∑ e ∈ C, if edgeSideAt a e z = pencilSide a x.1 z then
        exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0) =
        ∑ e ∈ C, w e := by
      apply Finset.sum_congr rfl
      intro e _
      dsimp [w]
      cases edgeSideAt a e z <;> cases pencilSide a x.1 z <;> simp
    ∑ e ∈ C, w e = (∑ e ∈ P, w e) + ∑ e ∈ C \ P, w e := by
      rw [← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset hPC]
    _ = S.card + ∑ e ∈ C \ P, w e := by rw [hPS]
    _ = _ := rfl

lemma exactMismatchWeight_eq_outside {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    {x : BasePoint F} {l : Line F} (hxl : Incident x.1 l)
    {z : BasePoint F} (hz : z ∈ usefulPoints x l) :
    exactMismatchWeight a A hqmod hqK hq ht x.1 C z =
      ∑ e ∈ C \ pencilEdges C x.1,
        if (pencilSide a x.1 z = edgeSideAt a e z) = false then
          exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0 := by
  classical
  let w : Edge F q t → ℕ := fun e ↦
    if (pencilSide a x.1 z = edgeSideAt a e z) = false then
      exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0
  let P := pencilEdges C x.1
  have hPC : P ⊆ C := Finset.filter_subset _ _
  have hPzero : ∑ e ∈ P, w e = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have heP := Finset.mem_filter.mp he
    by_cases hel : e.1 = l
    · have hone := active_edge_exact_weight_one_on_useful a A hqmod hqK hq ht
        hxl hz hel (hactive e heP.1)
      simp [w, hone.1]
    · have hze : ¬ Incident z.1 e.1 := by
        intro hze
        apply hel
        apply line_unique_of_two_points
            (fun h ↦ usefulPoint_ne_center hz (Subtype.ext h.symm))
        · exact heP.2
        · exact hze
        · exact hxl
        · exact (mem_smallLinePoints_iff l z).mp (usefulPoints_subset_line x l hz)
      simp [w, exactEdgeWeightAt, originalAt, largeOriginalAt, smallPiecesAt,
        edgeWeightAt, hze]
  unfold exactMismatchWeight exactSideWeight
  calc
    (∑ e ∈ C, if edgeSideAt a e z = !(pencilSide a x.1 z) then
        exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0) =
        ∑ e ∈ C, w e := by
      apply Finset.sum_congr rfl
      intro e _
      dsimp [w]
      cases edgeSideAt a e z <;> cases pencilSide a x.1 z <;> simp
    ∑ e ∈ C, w e = (∑ e ∈ P, w e) + ∑ e ∈ C \ P, w e := by
      rw [← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset hPC]
    _ = ∑ e ∈ C \ P, w e := by rw [hPzero, Nat.zero_add]
    _ = _ := rfl

lemma pencil_outside_side_sum_le {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    {balance : ℕ} (hbal : IsBalanced balance a)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    (x : BasePoint F) (matchSide : Bool) :
    (∑ l ∈ linesThrough x.1, ∑ z ∈ usefulPoints x l,
      ∑ e ∈ C \ pencilEdges C x.1,
        if (pencilSide a x.1 z = edgeSideAt a e z) = matchSide then
          exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0) ≤
      (balance + 24) * (C \ pencilEdges C x.1).card := by
  classical
  let O := C \ pencilEdges C x.1
  let w : Edge F q t → BasePoint F → ℕ := fun e z ↦
    if (pencilSide a x.1 z = edgeSideAt a e z) = matchSide then
      exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0
  have hedge : ∀ e ∈ O,
      (∑ l ∈ linesThrough x.1, ∑ z ∈ usefulPoints x l, w e z) ≤
        balance + 24 := by
    intro e he
    have he' := Finset.mem_sdiff.mp he
    have hexterior : ¬ Incident x.1 e.1 := by
      simpa [pencilEdges, he'.1] using he'.2
    calc
      (∑ l ∈ linesThrough x.1, ∑ z ∈ usefulPoints x l, w e z) ≤
          ∑ z : BasePoint F, w e z := sum_useful_pencil_le_univ x (w e)
      _ = exactEdgePencilWeight a A hqmod hqK hq ht x.1 e matchSide := rfl
      _ ≤ balance + 24 := exactEdgePencilWeight_le a A hbal hqmod hqK hq ht
        x.1 e x.2 hexterior (hactive e he'.1) matchSide
  have hswap :
      (∑ l ∈ linesThrough x.1, ∑ z ∈ usefulPoints x l, ∑ e ∈ O, w e z) =
        ∑ e ∈ O, ∑ l ∈ linesThrough x.1, ∑ z ∈ usefulPoints x l, w e z := by
    induction linesThrough x.1 using Finset.induction_on with
    | empty => simp
    | @insert l L hl ih =>
        simp only [Finset.sum_insert hl]
        rw [ih, Finset.sum_comm (s := usefulPoints x l),
          Finset.sum_add_distrib]
  change (∑ l ∈ linesThrough x.1, ∑ z ∈ usefulPoints x l,
    ∑ e ∈ O, w e z) ≤ _
  rw [hswap]
  calc
    _ ≤ ∑ _e ∈ O, (balance + 24) :=
      Finset.sum_le_sum hedge
    _ = (balance + 24) * O.card := by simp [mul_comm]
    _ = _ := by rfl

set_option maxHeartbeats 1000000 in
lemma exact_initial_small_arithmetic
    (K q t Δ u s cap f : ℕ)
    (hK : 20000000 ≤ K) (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hrange : K ^ 2 * (t - q) ≤ q)
    (halmost : 39 * Δ < t + K * q + 156 * fixedC0 * t)
    (hulower : K - 2 ≤ u) (huupper : u ≤ K + 1)
    (hsf : s ≤ f) (hscap : s ≤ cap)
    (hudef : u * (cap - s) ≤ 16 * Δ + u * (t - q)) :
    2 * (cap - f) ≤ t := by
  have hKpos : 0 < K := by omega
  have hKsub : K - 2 + 2 = K := Nat.sub_add_cancel (by omega)
  have htd : q + (t - q) = t := Nat.add_sub_of_le hq
  have hKqmin := Nat.mul_le_mul_right q hK
  have hrhs : 36 * (t + K * q + 156 * fixedC0 * t) ≤
      39 * K * q := by
    norm_num [fixedC0] at ⊢
    nlinarith
  have hscaled := Nat.mul_lt_mul_of_pos_left halmost (by norm_num : 0 < 36)
  have hdelta : 36 * Δ < K * q := by nlinarith
  by_cases hfcap : cap ≤ f
  · omega
  have haf : cap - f ≤ cap - s := Nat.sub_le_sub_left hsf cap
  have hudeff : u * (cap - f) ≤ 16 * Δ + u * (t - q) :=
    (Nat.mul_le_mul_left u haf).trans hudef
  have hdef : (K - 2) * (cap - f) ≤
      16 * Δ + (K + 1) * (t - q) := by
    calc
      (K - 2) * (cap - f) ≤ u * (cap - f) :=
        Nat.mul_le_mul_right (cap - f) hulower
      _ ≤ 16 * Δ + u * (t - q) := hudeff
      _ ≤ 16 * Δ + (K + 1) * (t - q) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right (t - q) huupper) _
  have hKd : 4 * (K + 1) * (t - q) ≤ q := by
    calc
      4 * (K + 1) * (t - q) ≤ K ^ 2 * (t - q) := by
        gcongr
        nlinarith
      _ ≤ q := hrange
  by_contra hbad
  have htbad : t < 2 * (cap - f) := by omega
  have hmul0 := Nat.mul_lt_mul_of_pos_left htbad
    (show 0 < 2 * (K - 2) by omega)
  have hmul : 2 * (K - 2) * t <
      4 * (K - 2) * (cap - f) := by nlinarith
  have hfour : 4 * (K - 2) * (cap - f) ≤
      64 * Δ + 4 * (K + 1) * (t - q) := by
    have h := Nat.mul_le_mul_left 4 hdef
    nlinarith
  have hub : 64 * Δ + 4 * (K + 1) * (t - q) <
      2 * (K - 2) * q := by
    nlinarith
  have hqt : 2 * (K - 2) * q ≤ 2 * (K - 2) * t := by gcongr
  omega

lemma exact_weak_delta_arithmetic
    (K b d Δ Q G : ℕ) (hK : 1000000 ≤ K)
    (hb : 1000 * b ≤ 521 * K)
    (hlower : (K - 2) * Δ ≤ Q + b * Δ)
    (hG : G ≤ b * Δ)
    (hweak : 11 * Q ≤ 10 * (G + (K ^ 2 + K) * d)) :
    Δ ≤ 400 * K * d := by
  have hKpos : 0 < K := by omega
  have hKsub : K - 2 + 2 = K := by omega
  have h1 := Nat.mul_le_mul_left 11000 hlower
  have h2 := Nat.mul_le_mul_left 1000 hweak
  have h3 := Nat.mul_le_mul_left 10000 hG
  have hbase : 11000 * (K - 2) * Δ ≤
      21000 * b * Δ + 10000 * (K ^ 2 + K) * d := by
    nlinarith
  have hbΔ : 21000 * b * Δ ≤ 10941 * K * Δ := by
    have h := Nat.mul_le_mul_left (21 * Δ) hb
    nlinarith
  have hcoef : 50 * K * Δ ≤
      (11000 * (K - 2) - 10941 * K) * Δ := by
    have : 10941 * K ≤ 11000 * (K - 2) := by omega
    have hcoef0 : 50 * K ≤ 11000 * (K - 2) - 10941 * K := by omega
    exact Nat.mul_le_mul_right Δ hcoef0
  have hL : K ^ 2 + K ≤ 2 * K ^ 2 := by nlinarith
  have hfinal : 50 * K * Δ ≤ 20000 * K ^ 2 * d := by
    calc
      50 * K * Δ ≤ (11000 * (K - 2) - 10941 * K) * Δ := hcoef
      _ = 11000 * (K - 2) * Δ - 10941 * K * Δ := by
        rw [Nat.sub_mul]
      _ ≤ 10000 * (K ^ 2 + K) * d := by omega
      _ ≤ 10000 * (2 * K ^ 2) * d := by gcongr
      _ = 20000 * K ^ 2 * d := by ring
  have hcancel : (50 * K) * Δ ≤ (50 * K) * (400 * K * d) := by
    convert hfinal using 1 <;> ring
  exact Nat.le_of_mul_le_mul_left hcancel (by positivity)

lemma exact_strong_zero_arithmetic
    (K b Δ Q G : ℕ) (hK : 1000000 ≤ K)
    (hb : 1000 * b ≤ 521 * K)
    (hlower : (K - 2) * Δ ≤ Q + b * Δ)
    (hG : G ≤ b * Δ) (hstrong : 3 * Q ≤ 2 * G) :
    Δ = 0 := by
  have hKsub : K - 2 + 2 = K := by omega
  have h1 := Nat.mul_le_mul_left 3000 hlower
  have h2 := Nat.mul_le_mul_left 1000 hstrong
  have h3 := Nat.mul_le_mul_left 2000 hG
  have hbase : 3000 * (K - 2) * Δ ≤ 5000 * b * Δ := by
    nlinarith
  have hbΔ : 5000 * b * Δ ≤ 2605 * K * Δ := by
    have h := Nat.mul_le_mul_left (5 * Δ) hb
    nlinarith
  by_contra hne
  have hΔ : 0 < Δ := Nat.pos_of_ne_zero hne
  have hmul : (3000 * (K - 2)) * Δ ≤ (2605 * K) * Δ := by
    exact hbase.trans hbΔ
  have : 3000 * (K - 2) ≤ 2605 * K :=
    Nat.le_of_mul_le_mul_right hmul hΔ
  omega

lemma exact_second_small_arithmetic
    (K q t Δ u s cap f : ℕ)
    (hK : 20000000 ≤ K) (hqpos : 0 < q) (hq : q ≤ t)
    (hrange : K ^ 2 * (t - q) ≤ q)
    (hdelta : Δ ≤ 400 * K * (t - q))
    (hulower : K - 2 ≤ u) (huupper : u ≤ K + 1)
    (hsf : s ≤ f)
    (hudef : u * (cap - s) ≤ 16 * Δ + u * (t - q)) :
    10 * (cap - f) ≤ t := by
  have haf : cap - f ≤ cap - s := Nat.sub_le_sub_left hsf cap
  have hudeff : u * (cap - f) ≤ 16 * Δ + u * (t - q) :=
    (Nat.mul_le_mul_left u haf).trans hudef
  have hdef : (K - 2) * (cap - f) ≤
      6400 * K * (t - q) + (K + 1) * (t - q) := by
    calc
      (K - 2) * (cap - f) ≤ u * (cap - f) :=
        Nat.mul_le_mul_right (cap - f) hulower
      _ ≤ 16 * Δ + u * (t - q) := hudeff
      _ ≤ 16 * (400 * K * (t - q)) + (K + 1) * (t - q) :=
        Nat.add_le_add (Nat.mul_le_mul_left 16 hdelta)
          (Nat.mul_le_mul_right (t - q) huupper)
      _ = 6400 * K * (t - q) + (K + 1) * (t - q) := by ring
  have hcoef : 10 * (6400 * K + (K + 1)) ≤ K ^ 2 := by nlinarith
  by_contra hbad
  have hqa : q < 10 * (cap - f) := lt_of_le_of_lt hq (by omega)
  have hKminus : 0 < K - 2 := by omega
  have hleft0 := Nat.mul_lt_mul_of_pos_left hqa hKminus
  have hleft : (K - 2) * q <
      10 * (K - 2) * (cap - f) := by nlinarith
  have hright : 10 * (K - 2) * (cap - f) ≤ q := by
    calc
      10 * (K - 2) * (cap - f) ≤
          10 * (6400 * K + (K + 1)) * (t - q) := by
        have h := Nat.mul_le_mul_left 10 hdef
        nlinarith
      _ ≤ K ^ 2 * (t - q) := Nat.mul_le_mul_right (t - q) hcoef
      _ ≤ q := hrange
  have hKm : 1 ≤ K - 2 := by omega
  have hqleft : q ≤ (K - 2) * q := by
    calc
      q = 1 * q := by simp
      _ ≤ (K - 2) * q := Nat.mul_le_mul_right q hKm
  omega

noncomputable def pencilExactDeficiency {q t : ℕ}
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (x : BasePoint F) (C : Finset (Edge F q t)) : ℕ :=
  (linesThrough x.1).sum fun l ↦
    (usefulPoints x l).sum fun z ↦
      templateCap q t l - exactMatchWeight a A hqmod hqK hq ht x.1 C z

noncomputable def pencilExactMismatch {q t : ℕ}
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    (x : BasePoint F) (C : Finset (Edge F q t)) : ℕ :=
  (linesThrough x.1).sum fun l ↦
    (usefulPoints x l).sum fun z ↦
      exactMismatchWeight a A hqmod hqK hq ht x.1 C z

lemma usefulPoints_card_le (x : BasePoint F) (l : Line F) :
    (usefulPoints x l).card ≤ Fintype.card F + 1 := by
  calc
    (usefulPoints x l).card ≤ (smallLinePoints l).card :=
      Finset.card_le_card (usefulPoints_subset_line x l)
    _ ≤ Fintype.card F + 1 := by
      by_cases hl : Incident (basePoint : Point F) l
      · rw [card_smallLinePoints_of_base l hl]
        omega
      · rw [card_smallLinePoints l hl]

lemma pencil_exact_mismatch_le {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    {balance : ℕ} (hbal : IsBalanced balance a)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    (x : BasePoint F) :
    pencilExactMismatch a A hqmod hqK hq ht x C ≤
      (balance + 24) * (C \ pencilEdges C x.1).card := by
  unfold pencilExactMismatch
  have heq :
      (∑ l ∈ linesThrough x.1, ∑ z ∈ usefulPoints x l,
        exactMismatchWeight a A hqmod hqK hq ht x.1 C z) =
      ∑ l ∈ linesThrough x.1, ∑ z ∈ usefulPoints x l,
        ∑ e ∈ C \ pencilEdges C x.1,
          if (pencilSide a x.1 z = edgeSideAt a e z) = false then
            exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0 := by
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro z hz
    exact exactMismatchWeight_eq_outside a A hqmod hqK hq ht hactive
      ((mem_linesThrough_iff x.1 l).mp hl) hz
  rw [heq]
  exact pencil_outside_side_sum_le a A hbal hqmod hqK hq ht
    hactive x false

lemma pencil_exact_deficiency_lower {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    {balance : ℕ} (hbal : IsBalanced balance a)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} (hnormal : IsNormal C)
    (hactive : IsActive C) (x : BasePoint F)
    (hcard : C.card = t + Fintype.card F * q) :
    (Fintype.card F - 2) * (C \ pencilEdges C x.1).card ≤
      pencilExactDeficiency a A hqmod hqK hq ht x C +
        (balance + 24) * (C \ pencilEdges C x.1).card := by
  classical
  let O := C \ pencilEdges C x.1
  let Q := pencilExactDeficiency a A hqmod hqK hq ht x C
  let M := ∑ l ∈ linesThrough x.1, ∑ z ∈ usefulPoints x l,
    ∑ e ∈ O,
      if (pencilSide a x.1 z = edgeSideAt a e z) = true then
        exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0
  have hdefsum := deficit_sum_eq_outside C hnormal x hcard
  have hline : ∀ l ∈ linesThrough x.1,
      (Fintype.card F - 2) *
          (templateCap q t l - (templateSlice C l).card) ≤
        ∑ z ∈ usefulPoints x l,
          (templateCap q t l -
            exactMatchWeight a A hqmod hqK hq ht x.1 C z) +
          ∑ z ∈ usefulPoints x l, ∑ e ∈ O,
            if (pencilSide a x.1 z = edgeSideAt a e z) = true then
              exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0 := by
    intro l hl
    have hxl := (mem_linesThrough_iff x.1 l).mp hl
    have hulower := usefulPoints_card_ge x l hxl
    calc
      (Fintype.card F - 2) *
          (templateCap q t l - (templateSlice C l).card) ≤
          (usefulPoints x l).card *
            (templateCap q t l - (templateSlice C l).card) :=
        Nat.mul_le_mul_right _ hulower
      _ = ∑ z ∈ usefulPoints x l,
          (templateCap q t l - (templateSlice C l).card) := by
        simp [mul_comm]
      _ ≤ ∑ z ∈ usefulPoints x l,
          ((templateCap q t l -
            exactMatchWeight a A hqmod hqK hq ht x.1 C z) +
            ∑ e ∈ O,
              if (pencilSide a x.1 z = edgeSideAt a e z) = true then
                exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0) := by
        apply Finset.sum_le_sum
        intro z hz
        have hmatch := exactMatchWeight_eq_slice_add_outside
          a A hqmod hqK hq ht hactive hxl hz
        have hslice := hnormal l
        dsimp [O] at hmatch
        rw [hmatch]
        let W := ∑ e ∈ C \ pencilEdges C x.1,
          if (pencilSide a x.1 z = edgeSideAt a e z) = true then
            exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0
        change templateCap q t l - (templateSlice C l).card ≤
          templateCap q t l - ((templateSlice C l).card + W) + W
        by_cases hW : W ≤ templateCap q t l - (templateSlice C l).card <;>
          omega
      _ = (∑ z ∈ usefulPoints x l,
          (templateCap q t l -
            exactMatchWeight a A hqmod hqK hq ht x.1 C z)) +
          ∑ z ∈ usefulPoints x l, ∑ e ∈ O,
            if (pencilSide a x.1 z = edgeSideAt a e z) = true then
              exactEdgeWeightAt a A hqmod hqK hq ht x.1 e z else 0 := by
        rw [Finset.sum_add_distrib]
  have hsum := Finset.sum_le_sum hline
  have hM := pencil_outside_side_sum_le a A hbal hqmod hqK hq ht
    hactive x true
  dsimp [O, Q, M] at hsum hM ⊢
  rw [← Finset.mul_sum, hdefsum] at hsum
  rw [Finset.sum_add_distrib] at hsum
  unfold pencilExactDeficiency
  exact hsum.trans (Nat.add_le_add_left hM _)

lemma pencil_exact_weak_sum {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hrange : Fintype.card F ^ 2 * (t - q) ≤ q)
    (hK : 20000000 ≤ Fintype.card F)
    {C : Finset (Edge F q t)} (hnormal : IsNormal C)
    (hactive : IsActive C)
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (x : BasePoint F)
    (halmost : 39 * (C \ pencilEdges C x.1).card <
      C.card + 156 * fixedC0 * t)
    (hcard : C.card = t + Fintype.card F * q) :
    11 * pencilExactDeficiency a A hqmod hqK hq ht x C ≤
      10 * (pencilExactMismatch a A hqmod hqK hq ht x C +
        (Fintype.card F ^ 2 + Fintype.card F) * (t - q)) := by
  classical
  let Δ := (C \ pencilEdges C x.1).card
  have hlocal : ∀ l ∈ linesThrough x.1, ∀ z ∈ usefulPoints x l,
      11 * (templateCap q t l -
          exactMatchWeight a A hqmod hqK hq ht x.1 C z) ≤
        10 * (exactMismatchWeight a A hqmod hqK hq ht x.1 C z +
          (t - q)) := by
    intro l hl z hz
    have hxl := (mem_linesThrough_iff x.1 l).mp hl
    have hsf := templateSlice_card_le_exactMatchWeight
      a A hqmod hqK hq ht hactive hxl hz
    have hscap := hnormal l
    have hudef := useful_card_mul_deficit_le D a A hqmod hqK
      hqpos hq ht hactive hcover hxl
    have hsmall := exact_initial_small_arithmetic
      (Fintype.card F) q t Δ (usefulPoints x l).card
      (templateSlice C l).card (templateCap q t l)
      (exactMatchWeight a A hqmod hqK hq ht x.1 C z)
      hK hqpos hq ht hrange (by simpa [Δ, hcard] using halmost)
      (usefulPoints_card_ge x l hxl) (usefulPoints_card_le x l)
      hsf hscap (by simpa [Δ] using hudef)
    exact pencil_local_weak_waste D hexp a A hqmod hqK hqpos hq ht
      hcover hxl hz hsmall
  have hsum := Finset.sum_le_sum fun l hl ↦
    Finset.sum_le_sum fun z hz ↦ hlocal l hl z hz
  have hsum' :
      11 * pencilExactDeficiency a A hqmod hqK hq ht x C ≤
        10 * (pencilExactMismatch a A hqmod hqK hq ht x C +
          ∑ l ∈ linesThrough x.1, ∑ _z ∈ usefulPoints x l, (t - q)) := by
    unfold pencilExactDeficiency pencilExactMismatch
    simpa only [Finset.mul_sum, Finset.sum_add_distrib, Nat.mul_add] using hsum
  have hpairs := pencil_pair_count_le x
  have hpair : (∑ l ∈ linesThrough x.1,
      ∑ _z ∈ usefulPoints x l, (t - q)) ≤
      (Fintype.card F ^ 2 + Fintype.card F) * (t - q) := by
    simp only [Finset.sum_const_nat]
    simpa only [Finset.sum_mul] using Nat.mul_le_mul_right (t - q) hpairs
  exact hsum'.trans (Nat.mul_le_mul_left 10
    (Nat.add_le_add_left hpair _))

lemma pencil_exact_strong_sum {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hrange : Fintype.card F ^ 2 * (t - q) ≤ q)
    (hK : 20000000 ≤ Fintype.card F)
    {C : Finset (Edge F q t)} (hnormal : IsNormal C)
    (hactive : IsActive C)
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (x : BasePoint F)
    (hdelta : (C \ pencilEdges C x.1).card ≤
      400 * Fintype.card F * (t - q)) :
    3 * pencilExactDeficiency a A hqmod hqK hq ht x C ≤
      2 * pencilExactMismatch a A hqmod hqK hq ht x C := by
  classical
  let Δ := (C \ pencilEdges C x.1).card
  have hlocal : ∀ l ∈ linesThrough x.1, ∀ z ∈ usefulPoints x l,
      3 * (templateCap q t l -
          exactMatchWeight a A hqmod hqK hq ht x.1 C z) ≤
        2 * exactMismatchWeight a A hqmod hqK hq ht x.1 C z := by
    intro l hl z hz
    have hxl := (mem_linesThrough_iff x.1 l).mp hl
    have hsf := templateSlice_card_le_exactMatchWeight
      a A hqmod hqK hq ht hactive hxl hz
    have hudef := useful_card_mul_deficit_le D a A hqmod hqK
      hqpos hq ht hactive hcover hxl
    have hsmall := exact_second_small_arithmetic
      (Fintype.card F) q t Δ (usefulPoints x l).card
      (templateSlice C l).card (templateCap q t l)
      (exactMatchWeight a A hqmod hqK hq ht x.1 C z)
      hK hqpos hq hrange (by simpa [Δ] using hdelta)
      (usefulPoints_card_ge x l hxl) (usefulPoints_card_le x l)
      hsf (by simpa [Δ] using hudef)
    exact pencil_local_strong_waste D hexp a A hqmod hqK hqpos hq ht
      hcover hxl hz hsmall
  have hsum := Finset.sum_le_sum fun l hl ↦
    Finset.sum_le_sum fun z hz ↦ hlocal l hl z hz
  unfold pencilExactDeficiency pencilExactMismatch
  simpa only [Finset.mul_sum] using hsum

lemma pencil_exact_outside_eq_zero {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    {balance : ℕ} (hbal : IsBalanced balance a)
    (hbalance : 1000 * (balance + 24) ≤ 521 * Fintype.card F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hrange : Fintype.card F ^ 2 * (t - q) ≤ q)
    (hK : 20000000 ≤ Fintype.card F)
    {C : Finset (Edge F q t)} (hnormal : IsNormal C)
    (hactive : IsActive C)
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (x : BasePoint F)
    (halmost : 39 * (C \ pencilEdges C x.1).card <
      C.card + 156 * fixedC0 * t)
    (hcard : C.card = t + Fintype.card F * q) :
    (C \ pencilEdges C x.1).card = 0 := by
  let Δ := (C \ pencilEdges C x.1).card
  let Q := pencilExactDeficiency a A hqmod hqK hq ht x C
  let G := pencilExactMismatch a A hqmod hqK hq ht x C
  have hlower := pencil_exact_deficiency_lower a A hbal hqmod hqK hq ht
    hnormal hactive x hcard
  have hG := pencil_exact_mismatch_le a A hbal hqmod hqK hq ht hactive x
  have hweak := pencil_exact_weak_sum D hexp a A hqmod hqK hqpos hq ht
    hrange (by omega) hnormal hactive hcover x halmost hcard
  have hdelta : Δ ≤ 400 * Fintype.card F * (t - q) :=
    exact_weak_delta_arithmetic (Fintype.card F) (balance + 24) (t - q)
      Δ Q G (by omega) hbalance (by simpa [Δ, Q] using hlower)
      (by simpa [Δ, G] using hG) (by simpa [Q, G] using hweak)
  have hstrong := pencil_exact_strong_sum D hexp a A hqmod hqK hqpos hq ht
    hrange hK hnormal hactive hcover x (by simpa [Δ] using hdelta)
  exact exact_strong_zero_arithmetic (Fintype.card F) (balance + 24)
    Δ Q G (by omega) hbalance (by simpa [Δ, Q] using hlower)
    (by simpa [Δ, G] using hG) (by simpa [Q, G] using hstrong)

noncomputable def prescribedMatchWeight {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (center : Point F) (C : Finset (Edge F q t)) (z : BasePoint F) : ℕ :=
  sideWeight a hqmod hqK C z (pencilSide a center z)

noncomputable def prescribedMismatchWeight {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (center : Point F) (C : Finset (Edge F q t)) (z : BasePoint F) : ℕ :=
  sideWeight a hqmod hqK C z (!(pencilSide a center z))

lemma prescribed_match_add_mismatch_eq {q t : ℕ}
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    (center : Point F) (C : Finset (Edge F q t)) (z : BasePoint F) :
    prescribedMatchWeight a hqmod hqK center C z +
      prescribedMismatchWeight a hqmod hqK center C z =
        ∑ e ∈ C, edgeWeightAt a hqmod hqK e z := by
  unfold prescribedMatchWeight prescribedMismatchWeight
  cases h : pencilSide a center z
  · simpa [h] using two_sideWeight_eq a hqmod hqK C z
  · simpa [h, add_comm] using two_sideWeight_eq a hqmod hqK C z

lemma chosen_local_weak_waste {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (center : Point F) (z : BasePoint F)
    (hsmall : 2 * (q - prescribedMatchWeight a hqmod hqK center C z) ≤ t) :
    11 * (q - prescribedMatchWeight a hqmod hqK center C z) ≤
      10 * (prescribedMismatchWeight a hqmod hqK center C z + (t - q)) := by
  let f := prescribedMatchWeight a hqmod hqK center C z
  let g := prescribedMismatchWeight a hqmod hqK center C z
  by_cases hqf : q ≤ f
  · omega
  have hfq : f ≤ q := by omega
  have hcov := selectedOriginal_covers D a A hqmod hqK hq ht hcover z
  have hchosen := selectedOriginal_card_le_weight_add_defect A a hqmod hqK
    hqpos hq ht C z (pencilSide a center z)
  change _ ≤ f + (t - q) at hchosen
  have hchosen' : (selectedOriginal A a hqmod hqK hq ht C z
      (pencilSide a center z)).card ≤ t - (q - f) := by omega
  have hopen : 11 * (q - f) ≤
      10 * (selectedOriginal A a hqmod hqK hq ht C z
        (!(pencilSide a center z))).card := by
    cases hs : pencilSide a center z
    · exact (D.opposite_original_blocks_of_expansion hexp hcov
        (by omega : q - f ≤ t) (by simpa [hs] using hchosen')).1
          (by simpa [f] using hsmall)
    · exact (D.opposite_original_blocks_of_expansion_symm hexp hcov
        (by omega : q - f ≤ t) (by simpa [hs] using hchosen')).1
          (by simpa [f] using hsmall)
  have hother := selectedOriginal_card_le_weight_add_defect A a hqmod hqK
    hqpos hq ht C z (!(pencilSide a center z))
  change _ ≤ g + (t - q) at hother
  exact hopen.trans (Nat.mul_le_mul_left 10 hother)

lemma chosen_local_strong_waste {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (center : Point F) (z : BasePoint F)
    (hsmall : 10 * (q - prescribedMatchWeight a hqmod hqK center C z) ≤ t) :
    3 * (q - prescribedMatchWeight a hqmod hqK center C z) ≤
      2 * prescribedMismatchWeight a hqmod hqK center C z := by
  let f := prescribedMatchWeight a hqmod hqK center C z
  let g := prescribedMismatchWeight a hqmod hqK center C z
  by_cases hqf : q ≤ f
  · omega
  have hfq : f ≤ q := by omega
  have hcov := selectedOriginal_covers D a A hqmod hqK hq ht hcover z
  have hchosen := selectedOriginal_card_le_weight_add_defect A a hqmod hqK
    hqpos hq ht C z (pencilSide a center z)
  change _ ≤ f + (t - q) at hchosen
  have hchosen' : (selectedOriginal A a hqmod hqK hq ht C z
      (pencilSide a center z)).card ≤ t - (q - f) := by omega
  have hopen : 3 * (q - f) ≤
      (selectedOriginal A a hqmod hqK hq ht C z
        (!(pencilSide a center z))).card := by
    cases hs : pencilSide a center z
    · exact (D.opposite_original_blocks_of_expansion hexp hcov
        (by omega : q - f ≤ t) (by simpa [hs] using hchosen')).2
          (by simpa [f] using hsmall)
    · exact (D.opposite_original_blocks_of_expansion_symm hexp hcov
        (by omega : q - f ≤ t) (by simpa [hs] using hchosen')).2
          (by simpa [f] using hsmall)
  have hother := selectedOriginal_card_le_twice_weight A a hqmod hqK
    hq ht C z (!(pencilSide a center z))
  change _ ≤ 2 * g at hother
  exact hopen.trans hother

lemma base_lineThrough_eq {l : Line F} {z : BasePoint F}
    (hbase : Incident (basePoint : Point F) l)
    (hzl : Incident z.1 l) :
    lineThroughPoints (basePoint : Point F) z.1 = l := by
  exact lineThroughPoints_eq_of_ne (Ne.symm z.2) hbase hzl

lemma active_edge_weight_one_on_base_pencil {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    {l : Line F} (hbase : Incident (basePoint : Point F) l)
    {z : BasePoint F} (hzl : Incident z.1 l)
    {e : Edge F q t} (heline : e.1 = l)
    (heActive : e ∈ activeTemplate e.1) :
    edgeSideAt a e z = pencilSide a (basePoint : Point F) z ∧
      edgeWeightAt a hqmod hqK e z = 1 := by
  have hline := base_lineThrough_eq hbase hzl
  rcases e with ⟨m, row | row⟩
  · change m = l at heline
    subst m
    constructor
    · cases hline
      simp [edgeSideAt, pencilSide, hzl]
    · simp [edgeWeightAt, hzl, hbase]
  · change m = l at heline
    subst m
    have : (l, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) ∉
        activeTemplate l := by
      rw [activeTemplate, if_pos hbase]
      simp
    exact (this heActive).elim

noncomputable def basePencilDeficiency {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) : ℕ :=
  (linesThrough (basePoint : Point F)).sum fun l ↦
    (smallLinePoints l).sum fun z ↦
      q - prescribedMatchWeight a hqmod hqK (basePoint : Point F) C z

noncomputable def basePencilMismatch {q t : ℕ} (a : Labeling F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (C : Finset (Edge F q t)) : ℕ :=
  (linesThrough (basePoint : Point F)).sum fun l ↦
    (smallLinePoints l).sum fun z ↦
      prescribedMismatchWeight a hqmod hqK (basePoint : Point F) C z

lemma sum_base_pencil_le_univ (w : BasePoint F → ℕ) :
    (∑ l ∈ linesThrough (basePoint : Point F),
      ∑ z ∈ smallLinePoints l, w z) ≤ ∑ z : BasePoint F, w z := by
  classical
  have hdisj : ∀ l ∈ linesThrough (basePoint : Point F),
      ∀ m ∈ linesThrough (basePoint : Point F), l ≠ m →
        Disjoint (smallLinePoints l) (smallLinePoints m) := by
    intro l hl m hm hlm
    apply Finset.disjoint_left.mpr
    intro z hzl hzm
    apply hlm
    exact line_unique_of_two_points (Ne.symm z.2)
      ((mem_linesThrough_iff (basePoint : Point F) l).mp hl)
      ((mem_smallLinePoints_iff l z).mp hzl)
      ((mem_linesThrough_iff (basePoint : Point F) m).mp hm)
      ((mem_smallLinePoints_iff m z).mp hzm)
  rw [← Finset.sum_biUnion hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)

lemma base_pencil_pair_count :
    (∑ l ∈ linesThrough (basePoint : Point F),
      (smallLinePoints l).card) = Fintype.card F ^ 2 + Fintype.card F := by
  calc
    (∑ l ∈ linesThrough (basePoint : Point F),
      (smallLinePoints l).card) =
        ∑ _l ∈ linesThrough (basePoint : Point F), Fintype.card F := by
      apply Finset.sum_congr rfl
      intro l hl
      exact card_smallLinePoints_of_base l
        ((mem_linesThrough_iff (basePoint : Point F) l).mp hl)
    _ = (Fintype.card F + 1) * Fintype.card F := by
      simp [card_linesThrough]
    _ = Fintype.card F ^ 2 + Fintype.card F := by ring

lemma prescribedMatchWeight_eq_base_slice_add_outside {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    {l : Line F} (hbase : Incident (basePoint : Point F) l)
    {z : BasePoint F} (hz : z ∈ smallLinePoints l) :
    prescribedMatchWeight a hqmod hqK (basePoint : Point F) C z =
      (templateSlice C l).card +
        ∑ e ∈ C \ pencilEdges C (basePoint : Point F),
          if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = true
          then edgeWeightAt a hqmod hqK e z else 0 := by
  classical
  let w : Edge F q t → ℕ := fun e ↦
    if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = true
    then edgeWeightAt a hqmod hqK e z else 0
  let P := pencilEdges C (basePoint : Point F)
  let S := templateSlice C l
  have hPC : P ⊆ C := Finset.filter_subset _ _
  have hSP : S ⊆ P := templateSlice_subset_pencilEdges C hbase
  have hslice : ∑ e ∈ S, w e = S.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro e he
    have he' := (mem_templateSlice_iff C l e).mp he
    have hone := active_edge_weight_one_on_base_pencil a hqmod hqK hbase
      ((mem_smallLinePoints_iff l z).mp hz) he'.2 (hactive e he'.1)
    simp [w, hone.1, hone.2]
  have hother : ∑ e ∈ P \ S, w e = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have he' := Finset.mem_sdiff.mp he
    have heP := Finset.mem_filter.mp he'.1
    have hel : e.1 ≠ l := by
      intro hel
      exact he'.2 ((mem_templateSlice_iff C l e).mpr ⟨heP.1, hel⟩)
    have hze : ¬ Incident z.1 e.1 := by
      intro hze
      apply hel
      exact line_unique_of_two_points (Ne.symm z.2)
        heP.2 hze hbase ((mem_smallLinePoints_iff l z).mp hz)
    simp [w, edgeWeightAt, hze]
  have hPS : ∑ e ∈ P, w e = S.card := by
    calc
      ∑ e ∈ P, w e = (∑ e ∈ S, w e) + ∑ e ∈ P \ S, w e := by
        rw [← Finset.sum_union Finset.disjoint_sdiff,
          Finset.union_sdiff_of_subset hSP]
      _ = S.card := by rw [hslice, hother, Nat.add_zero]
  unfold prescribedMatchWeight sideWeight
  calc
    (∑ e ∈ C, if edgeSideAt a e z = pencilSide a (basePoint : Point F) z then
        edgeWeightAt a hqmod hqK e z else 0) = ∑ e ∈ C, w e := by
      apply Finset.sum_congr rfl
      intro e _
      dsimp [w]
      cases edgeSideAt a e z <;>
        cases pencilSide a (basePoint : Point F) z <;> simp
    ∑ e ∈ C, w e = (∑ e ∈ P, w e) + ∑ e ∈ C \ P, w e := by
      rw [← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset hPC]
    _ = S.card + ∑ e ∈ C \ P, w e := by rw [hPS]
    _ = _ := rfl

lemma prescribedMismatchWeight_eq_base_outside {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    {l : Line F} (hbase : Incident (basePoint : Point F) l)
    {z : BasePoint F} (hz : z ∈ smallLinePoints l) :
    prescribedMismatchWeight a hqmod hqK (basePoint : Point F) C z =
      ∑ e ∈ C \ pencilEdges C (basePoint : Point F),
        if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = false
        then edgeWeightAt a hqmod hqK e z else 0 := by
  classical
  let w : Edge F q t → ℕ := fun e ↦
    if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = false
    then edgeWeightAt a hqmod hqK e z else 0
  let P := pencilEdges C (basePoint : Point F)
  have hPC : P ⊆ C := Finset.filter_subset _ _
  have hPzero : ∑ e ∈ P, w e = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have heP := Finset.mem_filter.mp he
    let l := lineThroughPoints (basePoint : Point F) z.1
    by_cases hel : e.1 = l
    · have hbase : Incident (basePoint : Point F) l :=
        lineThroughPoints_incident_left _ _
      have hzl : Incident z.1 l := lineThroughPoints_incident_right _ _
      have hone := active_edge_weight_one_on_base_pencil a hqmod hqK hbase hzl
        hel (hactive e heP.1)
      simp [w, hone.1]
    · have hze : ¬ Incident z.1 e.1 := by
        intro hze
        apply hel
        exact line_unique_of_two_points (Ne.symm z.2) heP.2 hze
          (lineThroughPoints_incident_left _ _)
          (lineThroughPoints_incident_right _ _)
      simp [w, edgeWeightAt, hze]
  unfold prescribedMismatchWeight sideWeight
  calc
    (∑ e ∈ C, if edgeSideAt a e z = !(pencilSide a (basePoint : Point F) z) then
        edgeWeightAt a hqmod hqK e z else 0) = ∑ e ∈ C, w e := by
      apply Finset.sum_congr rfl
      intro e _
      dsimp [w]
      cases edgeSideAt a e z <;>
        cases pencilSide a (basePoint : Point F) z <;> simp
    ∑ e ∈ C, w e = (∑ e ∈ P, w e) + ∑ e ∈ C \ P, w e := by
      rw [← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset hPC]
    _ = ∑ e ∈ C \ P, w e := by rw [hPzero, Nat.zero_add]
    _ = _ := rfl

lemma base_outside_side_sum_le {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) {balance : ℕ} (hbal : IsBalanced balance a)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    (matchSide : Bool) :
    (∑ l ∈ linesThrough (basePoint : Point F),
      ∑ z ∈ smallLinePoints l,
      ∑ e ∈ C \ pencilEdges C (basePoint : Point F),
        if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = matchSide
        then edgeWeightAt a hqmod hqK e z else 0) ≤
      (balance + 8) *
        (C \ pencilEdges C (basePoint : Point F)).card := by
  classical
  let O := C \ pencilEdges C (basePoint : Point F)
  let w : Edge F q t → BasePoint F → ℕ := fun e z ↦
    if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = matchSide
    then edgeWeightAt a hqmod hqK e z else 0
  have hedge : ∀ e ∈ O,
      (∑ l ∈ linesThrough (basePoint : Point F),
        ∑ z ∈ smallLinePoints l, w e z) ≤ balance + 8 := by
    intro e he
    have he' := Finset.mem_sdiff.mp he
    have hexterior : ¬ Incident (basePoint : Point F) e.1 := by
      simpa [pencilEdges, he'.1] using he'.2
    calc
      _ ≤ ∑ z : BasePoint F, w e z := sum_base_pencil_le_univ (w e)
      _ = edgePencilWeight a hqmod hqK (basePoint : Point F) e matchSide := rfl
      _ ≤ balance + 8 := edgePencilWeight_le a hbal hqmod hqK
        (basePoint : Point F) e hexterior (hactive e he'.1) matchSide
  have hswap :
      (∑ l ∈ linesThrough (basePoint : Point F),
        ∑ z ∈ smallLinePoints l, ∑ e ∈ O, w e z) =
      ∑ e ∈ O, ∑ l ∈ linesThrough (basePoint : Point F),
        ∑ z ∈ smallLinePoints l, w e z := by
    induction linesThrough (basePoint : Point F) using Finset.induction_on with
    | empty => simp
    | @insert l L hl ih =>
        simp only [Finset.sum_insert hl]
        rw [ih, Finset.sum_comm (s := smallLinePoints l),
          Finset.sum_add_distrib]
  change (∑ l ∈ linesThrough (basePoint : Point F),
    ∑ z ∈ smallLinePoints l, ∑ e ∈ O, w e z) ≤ _
  rw [hswap]
  calc
    _ ≤ ∑ _e ∈ O, (balance + 8) :=
      Finset.sum_le_sum hedge
    _ = (balance + 8) * O.card := by simp [mul_comm]
    _ = _ := by rfl

lemma ordinaryTotalWeight_cover_lower {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (z : BasePoint F) :
    t ≤ (∑ e ∈ C, edgeWeightAt a hqmod hqK e z) + 2 * (t - q) := by
  let L := selectedOriginal A a hqmod hqK hq ht C z false
  let R := selectedOriginal A a hqmod hqK hq ht C z true
  have hcov := selectedOriginal_covers D a A hqmod hqK hq ht hcover z
  have hcard := coversByIndices_card_sum_ge D hcov
  have hL := selectedOriginal_card_le_weight_add_defect A a hqmod hqK
    hqpos hq ht C z false
  have hR := selectedOriginal_card_le_weight_add_defect A a hqmod hqK
    hqpos hq ht C z true
  have hsum := two_sideWeight_eq a hqmod hqK C z
  omega

lemma sum_smallLine_edgeWeight_le_eight {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (hqmod : q % 4 = 3)
    (hqK : 2 * Fintype.card F + 1 ≤ q)
    {l : Line F} (hbase : Incident (basePoint : Point F) l)
    (e : Edge F q t) (hexterior : ¬ Incident (basePoint : Point F) e.1)
    (heActive : e ∈ activeTemplate e.1) :
    (∑ z ∈ smallLinePoints l, edgeWeightAt a hqmod hqK e z) ≤ 8 := by
  classical
  let U := (smallLinePoints l).filter fun z ↦ Incident z.1 e.1
  have hle : (∑ z ∈ smallLinePoints l, edgeWeightAt a hqmod hqK e z) ≤
      ∑ _z ∈ U, 8 := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro z hz
    by_cases hze : Incident z.1 e.1
    · simp only [hze, if_true]
      exact edgeWeightAt_le_eight_of_active a hqmod hqK e z heActive
    · simp [hze, edgeWeightAt]
  have hU : U.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz w hw
    have hz' := Finset.mem_filter.mp hz
    have hw' := Finset.mem_filter.mp hw
    have hlm : l ≠ e.1 := by
      intro heq
      exact hexterior (by simpa [← heq] using hbase)
    apply Subtype.ext
    exact point_unique_of_two_lines hlm
      ((mem_smallLinePoints_iff l z).mp hz'.1) hz'.2
      ((mem_smallLinePoints_iff l w).mp hw'.1) hw'.2
  calc
    _ ≤ ∑ _z ∈ U, 8 := hle
    _ = 8 * U.card := by simp [mul_comm]
    _ ≤ 8 * 1 := Nat.mul_le_mul_left 8 hU
    _ = 8 := by norm_num

lemma base_line_q_deficit_le {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    {l : Line F} (hbase : Incident (basePoint : Point F) l) :
    Fintype.card F * (q - (templateSlice C l).card) ≤
      8 * (C \ pencilEdges C (basePoint : Point F)).card +
        Fintype.card F * (t - q) := by
  classical
  let O := C \ pencilEdges C (basePoint : Point F)
  have hpoint : ∀ z ∈ smallLinePoints l,
      q - (templateSlice C l).card ≤
        (∑ e ∈ O, edgeWeightAt a hqmod hqK e z) + (t - q) := by
    intro z hz
    have hmatch := prescribedMatchWeight_eq_base_slice_add_outside
      a hqmod hqK hactive hbase hz
    have hmis := prescribedMismatchWeight_eq_base_outside
      a hqmod hqK hactive hbase hz
    have hsum := prescribed_match_add_mismatch_eq a hqmod hqK
      (basePoint : Point F) C z
    have hlower := ordinaryTotalWeight_cover_lower D a A hqmod hqK
      hqpos hq ht hcover z
    dsimp [O] at hmatch hmis ⊢
    rw [hmatch, hmis] at hsum
    have hpartition' :
        (∑ e ∈ C \ pencilEdges C (basePoint : Point F),
          if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = true then
            edgeWeightAt a hqmod hqK e z else 0) +
        (∑ e ∈ C \ pencilEdges C (basePoint : Point F),
          if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = false then
            edgeWeightAt a hqmod hqK e z else 0) =
        ∑ e ∈ C \ pencilEdges C (basePoint : Point F),
          edgeWeightAt a hqmod hqK e z := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      cases hp : pencilSide a (basePoint : Point F) z <;>
        cases he : edgeSideAt a e z <;> simp
    omega
  have hsum := Finset.sum_le_sum fun z hz ↦ hpoint z hz
  have hedge : ∑ e ∈ O, ∑ z ∈ smallLinePoints l,
      edgeWeightAt a hqmod hqK e z ≤ 8 * O.card := by
    calc
      _ ≤ ∑ _e ∈ O, 8 := by
        apply Finset.sum_le_sum
        intro e he
        have he' := Finset.mem_sdiff.mp he
        have hexterior : ¬ Incident (basePoint : Point F) e.1 := by
          simpa [pencilEdges, he'.1] using he'.2
        exact sum_smallLine_edgeWeight_le_eight a hqmod hqK hbase e
          hexterior (hactive e he'.1)
      _ = 8 * O.card := by simp [mul_comm]
  have hsum' : Fintype.card F * (q - (templateSlice C l).card) ≤
      (∑ e ∈ O, ∑ z ∈ smallLinePoints l,
        edgeWeightAt a hqmod hqK e z) + Fintype.card F * (t - q) := by
    calc
      Fintype.card F * (q - (templateSlice C l).card) =
          ∑ z ∈ smallLinePoints l, (q - (templateSlice C l).card) := by
        simp [card_smallLinePoints_of_base l hbase, mul_comm]
      _ ≤ ∑ z ∈ smallLinePoints l,
          ((∑ e ∈ O, edgeWeightAt a hqmod hqK e z) + (t - q)) := hsum
      _ = (∑ e ∈ O, ∑ z ∈ smallLinePoints l,
          edgeWeightAt a hqmod hqK e z) + Fintype.card F * (t - q) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        simp [card_smallLinePoints_of_base l hbase, mul_comm]
  have hfinal := hsum'.trans (Nat.add_le_add_right hedge _)
  simpa [O] using hfinal

lemma base_initial_small_arithmetic
    (K q t Δ s f : ℕ)
    (hK : 2000000 ≤ K) (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hrange : K ^ 2 * (t - q) ≤ q)
    (halmost : 39 * Δ < t + K * q + 156 * fixedC0 * t)
    (hsf : s ≤ f)
    (hdef : K * (q - s) ≤ 8 * Δ + K * (t - q)) :
    2 * (q - f) ≤ t := by
  have hB : 2 + 2 * (156 * fixedC0) ≤ K := by
    norm_num [fixedC0]
    omega
  have hrhs : t + K * q + 156 * fixedC0 * t ≤ 2 * K * q := by
    calc
      _ ≤ 2 * q + K * q + (156 * fixedC0) * (2 * q) := by gcongr
      _ = (K + 2 + 2 * (156 * fixedC0)) * q := by ring
      _ ≤ (K + K) * q := Nat.mul_le_mul_right q (by omega)
      _ = 2 * K * q := by ring
  have hdelta : 39 * Δ < 2 * K * q := halmost.trans_le hrhs
  have haf : q - f ≤ q - s := Nat.sub_le_sub_left hsf q
  have hdef' : K * (q - f) ≤ 8 * Δ + K * (t - q) :=
    (Nat.mul_le_mul_left K haf).trans hdef
  have hKd : 78 * (t - q) ≤ q := by
    have hcoef : 78 ≤ K ^ 2 := by nlinarith
    calc
      78 * (t - q) ≤ K ^ 2 * (t - q) :=
        Nat.mul_le_mul_right (t - q) hcoef
      _ ≤ q := hrange
  by_contra hbad
  have hqa : q < 2 * (q - f) := lt_of_le_of_lt hq (by omega)
  have hfactor : 0 < 39 * K := by positivity
  have hleft0 := Nat.mul_lt_mul_of_pos_left hqa hfactor
  have hleft : 39 * K * q < 78 * K * (q - f) := by nlinarith
  have hdelta' : 624 * Δ < 32 * K * q := by
    have h := Nat.mul_lt_mul_of_pos_left hdelta (by norm_num : 0 < 16)
    nlinarith
  have hKd' : 78 * K * (t - q) ≤ K * q := by
    have h := Nat.mul_le_mul_left K hKd
    nlinarith
  have hright : 78 * K * (q - f) < 33 * K * q := by
    calc
      78 * K * (q - f) ≤ 78 * (8 * Δ + K * (t - q)) := by
        have h := Nat.mul_le_mul_left 78 hdef'
        nlinarith
      _ = 624 * Δ + 78 * K * (t - q) := by ring
      _ < 32 * K * q + K * q := Nat.add_lt_add_of_lt_of_le hdelta' hKd'
      _ = 33 * K * q := by ring
  have hcontra : 39 * K * q < 33 * K * q := hleft.trans hright
  have hKq : 0 < K * q := by positivity
  nlinarith

lemma base_q_deficit_sum_lower {q t : ℕ}
    {C : Finset (Edge F q t)}
    (hq : q ≤ t)
    (hcard : C.card = t + Fintype.card F * q) :
    (C \ pencilEdges C (basePoint : Point F)).card - (t - q) ≤
      ∑ l ∈ linesThrough (basePoint : Point F),
        (q - (templateSlice C l).card) := by
  classical
  let P := pencilEdges C (basePoint : Point F)
  let S := ∑ l ∈ linesThrough (basePoint : Point F),
    (q - (templateSlice C l).card)
  have hPsub : P ⊆ C := Finset.filter_subset _ _
  have hPcard : P.card =
      ∑ l ∈ linesThrough (basePoint : Point F), (templateSlice C l).card :=
    pencil_slice_card_sum C (basePoint : Point F)
  have hpoint : ∀ l ∈ linesThrough (basePoint : Point F),
      q ≤ (q - (templateSlice C l).card) + (templateSlice C l).card := by
    intro l _
    by_cases hle : (templateSlice C l).card ≤ q
    · rw [Nat.sub_add_cancel hle]
    · omega
  have hsum := Finset.sum_le_sum hpoint
  have hlines := card_linesThrough (basePoint : Point F)
  dsimp [P, S] at hPsub hPcard hsum ⊢
  rw [Finset.sum_add_distrib, ← hPcard] at hsum
  simp only [Finset.sum_const_nat, hlines] at hsum
  have hout : (C \ pencilEdges C (basePoint : Point F)).card =
      C.card - (pencilEdges C (basePoint : Point F)).card :=
    Finset.card_sdiff_of_subset hPsub
  have hcore : (Fintype.card F + 1) * q -
      (pencilEdges C (basePoint : Point F)).card ≤
      ∑ l ∈ linesThrough (basePoint : Point F),
        (q - (templateSlice C l).card) := by
    rw [Nat.sub_le_iff_le_add]
    simpa [Nat.add_comm] using hsum
  rw [hout]
  have hCdecomp : C.card =
      (Fintype.card F + 1) * q + (t - q) := by
    have htdecomp : t = q + (t - q) := by omega
    calc
      C.card = t + Fintype.card F * q := hcard
      _ = (q + (t - q)) + Fintype.card F * q :=
        congrArg (fun n ↦ n + Fintype.card F * q) htdecomp
      _ = (Fintype.card F + 1) * q + (t - q) := by ring
  have hleft :
      (C.card - (pencilEdges C (basePoint : Point F)).card) - (t - q) =
        (Fintype.card F + 1) * q -
          (pencilEdges C (basePoint : Point F)).card := by
    rw [Nat.sub_sub, hCdecomp, Nat.add_sub_add_right]
  rw [hleft]
  exact hcore

lemma base_pencil_deficiency_lower {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) {balance : ℕ} (hbal : IsBalanced balance a)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    (hcard : C.card = t + Fintype.card F * q) :
    Fintype.card F *
        ((C \ pencilEdges C (basePoint : Point F)).card - (t - q)) ≤
      basePencilDeficiency a hqmod hqK C +
        (balance + 8) *
          (C \ pencilEdges C (basePoint : Point F)).card := by
  classical
  let O := C \ pencilEdges C (basePoint : Point F)
  let Q := basePencilDeficiency a hqmod hqK C
  let M := ∑ l ∈ linesThrough (basePoint : Point F),
    ∑ z ∈ smallLinePoints l, ∑ e ∈ O,
      if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = true
      then edgeWeightAt a hqmod hqK e z else 0
  have hdef := base_q_deficit_sum_lower (F := F) hq hcard
  have hline : ∀ l ∈ linesThrough (basePoint : Point F),
      Fintype.card F * (q - (templateSlice C l).card) ≤
        ∑ z ∈ smallLinePoints l,
          (q - prescribedMatchWeight a hqmod hqK
            (basePoint : Point F) C z) +
        ∑ z ∈ smallLinePoints l, ∑ e ∈ O,
          if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = true
          then edgeWeightAt a hqmod hqK e z else 0 := by
    intro l hl
    have hbase := (mem_linesThrough_iff (basePoint : Point F) l).mp hl
    calc
      Fintype.card F * (q - (templateSlice C l).card) =
          ∑ z ∈ smallLinePoints l, (q - (templateSlice C l).card) := by
        rw [Finset.sum_const_nat, card_smallLinePoints_of_base l hbase]
        simp [mul_comm]
      _ ≤ ∑ z ∈ smallLinePoints l,
          ((q - prescribedMatchWeight a hqmod hqK
            (basePoint : Point F) C z) +
          ∑ e ∈ O,
            if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = true
            then edgeWeightAt a hqmod hqK e z else 0) := by
        apply Finset.sum_le_sum
        intro z hz
        have hm := prescribedMatchWeight_eq_base_slice_add_outside
          a hqmod hqK hactive hbase hz
        rw [hm]
        let W := ∑ e ∈ C \ pencilEdges C (basePoint : Point F),
          if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = true
          then edgeWeightAt a hqmod hqK e z else 0
        change q - (templateSlice C l).card ≤
          q - ((templateSlice C l).card + W) + W
        by_cases hW : W ≤ q - (templateSlice C l).card <;> omega
      _ = (∑ z ∈ smallLinePoints l,
          (q - prescribedMatchWeight a hqmod hqK
            (basePoint : Point F) C z)) +
          ∑ z ∈ smallLinePoints l, ∑ e ∈ O,
            if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = true
            then edgeWeightAt a hqmod hqK e z else 0 := by
        rw [Finset.sum_add_distrib]
  have hsum := Finset.sum_le_sum hline
  have hM := base_outside_side_sum_le a hbal hqmod hqK hactive true
  dsimp [O, Q, M] at hsum hM ⊢
  rw [← Finset.mul_sum] at hsum
  rw [Finset.sum_add_distrib] at hsum
  unfold basePencilDeficiency
  exact (Nat.mul_le_mul_left (Fintype.card F) hdef).trans
    (hsum.trans (Nat.add_le_add_left hM _))

lemma base_pencil_mismatch_le {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) {balance : ℕ} (hbal : IsBalanced balance a)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    {C : Finset (Edge F q t)} (hactive : IsActive C) :
    basePencilMismatch a hqmod hqK C ≤
      (balance + 8) *
        (C \ pencilEdges C (basePoint : Point F)).card := by
  unfold basePencilMismatch
  have heq :
      (∑ l ∈ linesThrough (basePoint : Point F),
        ∑ z ∈ smallLinePoints l,
          prescribedMismatchWeight a hqmod hqK (basePoint : Point F) C z) =
      ∑ l ∈ linesThrough (basePoint : Point F),
        ∑ z ∈ smallLinePoints l,
          ∑ e ∈ C \ pencilEdges C (basePoint : Point F),
            if (pencilSide a (basePoint : Point F) z = edgeSideAt a e z) = false
            then edgeWeightAt a hqmod hqK e z else 0 := by
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro z hz
    exact prescribedMismatchWeight_eq_base_outside a hqmod hqK hactive
      ((mem_linesThrough_iff (basePoint : Point F) l).mp hl) hz
  rw [heq]
  exact base_outside_side_sum_le a hbal hqmod hqK hactive false

lemma base_pencil_weak_sum {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hrange : Fintype.card F ^ 2 * (t - q) ≤ q)
    (hK : 2000000 ≤ Fintype.card F)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (halmost : 39 * (C \ pencilEdges C (basePoint : Point F)).card <
      C.card + 156 * fixedC0 * t)
    (hcard : C.card = t + Fintype.card F * q) :
    11 * basePencilDeficiency a hqmod hqK C ≤
      10 * (basePencilMismatch a hqmod hqK C +
        (Fintype.card F ^ 2 + Fintype.card F) * (t - q)) := by
  classical
  let Δ := (C \ pencilEdges C (basePoint : Point F)).card
  have hlocal : ∀ l ∈ linesThrough (basePoint : Point F),
      ∀ z ∈ smallLinePoints l,
      11 * (q - prescribedMatchWeight a hqmod hqK
          (basePoint : Point F) C z) ≤
        10 * (prescribedMismatchWeight a hqmod hqK
          (basePoint : Point F) C z + (t - q)) := by
    intro l hl z hz
    have hbase := (mem_linesThrough_iff (basePoint : Point F) l).mp hl
    have hsf : (templateSlice C l).card ≤
        prescribedMatchWeight a hqmod hqK (basePoint : Point F) C z := by
      rw [prescribedMatchWeight_eq_base_slice_add_outside a hqmod hqK
        hactive hbase hz]
      exact Nat.le_add_right _ _
    have hdef := base_line_q_deficit_le D a A hqmod hqK hqpos hq ht
      hactive hcover hbase
    have hsmall := base_initial_small_arithmetic
      (Fintype.card F) q t Δ (templateSlice C l).card
      (prescribedMatchWeight a hqmod hqK (basePoint : Point F) C z)
      hK hqpos hq ht hrange (by simpa [Δ, hcard] using halmost)
      hsf (by simpa [Δ] using hdef)
    exact chosen_local_weak_waste D hexp a A hqmod hqK hqpos hq ht
      hcover (basePoint : Point F) z hsmall
  have hsum := Finset.sum_le_sum fun l hl ↦
    Finset.sum_le_sum fun z hz ↦ hlocal l hl z hz
  have hsum' : 11 * basePencilDeficiency a hqmod hqK C ≤
      10 * (basePencilMismatch a hqmod hqK C +
        ∑ l ∈ linesThrough (basePoint : Point F),
          ∑ _z ∈ smallLinePoints l, (t - q)) := by
    unfold basePencilDeficiency basePencilMismatch
    simpa only [Finset.mul_sum, Finset.sum_add_distrib, Nat.mul_add] using hsum
  have hpair : (∑ l ∈ linesThrough (basePoint : Point F),
      ∑ _z ∈ smallLinePoints l, (t - q)) =
      (Fintype.card F ^ 2 + Fintype.card F) * (t - q) := by
    simp only [Finset.sum_const_nat]
    rw [← Finset.sum_mul, base_pencil_pair_count]
  rw [hpair] at hsum'
  exact hsum'

lemma base_weak_delta_arithmetic
    (K b d Δ Q G : ℕ) (hK : 1000000 ≤ K)
    (hb : 1000 * b ≤ 521 * K)
    (hlower : K * (Δ - d) ≤ Q + b * Δ)
    (hG : G ≤ b * Δ)
    (hweak : 11 * Q ≤ 10 * (G + (K ^ 2 + K) * d)) :
    Δ ≤ 400 * K * d := by
  by_cases hd : d ≤ Δ
  · have h1 := Nat.mul_le_mul_left 11000 hlower
    have h2 := Nat.mul_le_mul_left 1000 hweak
    have h3 := Nat.mul_le_mul_left 10000 hG
    have hbase : 11000 * K * (Δ - d) ≤
        21000 * b * Δ + 10000 * (K ^ 2 + K) * d := by
      nlinarith
    have hbΔ : 21000 * b * Δ ≤ 10941 * K * Δ := by
      have h := Nat.mul_le_mul_left (21 * Δ) hb
      nlinarith
    have hcoef : 50 * K * Δ ≤ 59 * K * Δ := by gcongr; omega
    have hL : 11000 * K + 10000 * (K ^ 2 + K) ≤
        20000 * K ^ 2 := by nlinarith
    have hfinal : 50 * K * Δ ≤ 20000 * K ^ 2 * d := by
      have hsub : 11000 * K * Δ ≤
          10941 * K * Δ +
            (11000 * K + 10000 * (K ^ 2 + K)) * d := by
        have hbase' : 11000 * K * (Δ - d) ≤
            10941 * K * Δ + 10000 * (K ^ 2 + K) * d :=
          hbase.trans (Nat.add_le_add_right hbΔ _)
        calc
          11000 * K * Δ = 11000 * K * ((Δ - d) + d) := by
            exact congrArg (fun n ↦ 11000 * K * n) (Nat.sub_add_cancel hd).symm
          _ = 11000 * K * (Δ - d) + 11000 * K * d := by ring
          _ ≤ (10941 * K * Δ + 10000 * (K ^ 2 + K) * d) +
              11000 * K * d := Nat.add_le_add_right hbase' _
          _ = 10941 * K * Δ +
              (11000 * K + 10000 * (K ^ 2 + K)) * d := by ring
      calc
        50 * K * Δ ≤ 59 * K * Δ := hcoef
        _ = 11000 * K * Δ - 10941 * K * Δ := by
          have hdecomp : 11000 * K * Δ =
              10941 * K * Δ + 59 * K * Δ := by ring
          omega
        _ ≤ (11000 * K + 10000 * (K ^ 2 + K)) * d := by omega
        _ ≤ 20000 * K ^ 2 * d := Nat.mul_le_mul_right d hL
    have hcancel : (50 * K) * Δ ≤ (50 * K) * (400 * K * d) := by
      convert hfinal using 1 <;> ring
    exact Nat.le_of_mul_le_mul_left hcancel (by positivity)
  · have hΔd : Δ ≤ d := by omega
    calc
      Δ ≤ d := hΔd
      _ ≤ 400 * K * d := by
        exact Nat.le_mul_of_pos_left d (by positivity)

lemma base_strong_delta_arithmetic
    (K b d Δ Q G : ℕ) (hK : 1000000 ≤ K)
    (hb : 1000 * b ≤ 521 * K)
    (hlower : K * (Δ - d) ≤ Q + b * Δ)
    (hG : G ≤ b * Δ) (hstrong : 3 * Q ≤ 2 * G) :
    Δ ≤ 8 * d := by
  by_cases hd : d ≤ Δ
  · have h1 := Nat.mul_le_mul_left 3000 hlower
    have h2 := Nat.mul_le_mul_left 1000 hstrong
    have h3 := Nat.mul_le_mul_left 2000 hG
    have hbase : 3000 * K * (Δ - d) ≤ 5000 * b * Δ := by
      nlinarith
    have hbΔ : 5000 * b * Δ ≤ 2605 * K * Δ := by
      have h := Nat.mul_le_mul_left (5 * Δ) hb
      nlinarith
    have hmain : 395 * K * Δ ≤ 3000 * K * d := by
      have hbase' : 3000 * K * (Δ - d) ≤ 2605 * K * Δ :=
        hbase.trans hbΔ
      have htotal : 3000 * K * Δ ≤
          2605 * K * Δ + 3000 * K * d := by
        calc
          3000 * K * Δ = 3000 * K * ((Δ - d) + d) := by
            exact congrArg (fun n ↦ 3000 * K * n) (Nat.sub_add_cancel hd).symm
          _ = 3000 * K * (Δ - d) + 3000 * K * d := by ring
          _ ≤ 2605 * K * Δ + 3000 * K * d :=
            Nat.add_le_add_right hbase' _
      have hdecomp : 3000 * K * Δ =
          2605 * K * Δ + 395 * K * Δ := by ring
      omega
    have hcancel : K * (395 * Δ) ≤ K * (3000 * d) := by
      simpa [mul_assoc, mul_left_comm] using hmain
    have h395 : 395 * Δ ≤ 3000 * d :=
      Nat.le_of_mul_le_mul_left hcancel (by positivity)
    nlinarith
  · have : Δ ≤ d := by omega
    omega

lemma base_second_small_arithmetic
    (K q t Δ s f : ℕ)
    (hK : 1000000 ≤ K) (hqpos : 0 < q) (hq : q ≤ t)
    (hrange : K ^ 2 * (t - q) ≤ q)
    (hdelta : Δ ≤ 400 * K * (t - q))
    (hsf : s ≤ f)
    (hdef : K * (q - s) ≤ 8 * Δ + K * (t - q)) :
    10 * (q - f) ≤ t := by
  have haf : q - f ≤ q - s := Nat.sub_le_sub_left hsf q
  have hdef' : K * (q - f) ≤ 3201 * K * (t - q) := by
    calc
      K * (q - f) ≤ K * (q - s) := Nat.mul_le_mul_left K haf
      _ ≤ 8 * Δ + K * (t - q) := hdef
      _ ≤ 8 * (400 * K * (t - q)) + K * (t - q) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 8 hdelta) _
      _ = 3201 * K * (t - q) := by ring
  have hcoef : 10 * 3201 * K ≤ K ^ 2 := by nlinarith
  by_contra hbad
  have hqa : q < 10 * (q - f) := lt_of_le_of_lt hq (by omega)
  have hleft : K * q < 10 * K * (q - f) := by nlinarith
  have hright : 10 * K * (q - f) ≤ q := by
    calc
      10 * K * (q - f) ≤ 10 * (3201 * K * (t - q)) := by
        simpa [mul_assoc] using Nat.mul_le_mul_left 10 hdef'
      _ = (10 * 3201 * K) * (t - q) := by ring
      _ ≤ K ^ 2 * (t - q) := Nat.mul_le_mul_right (t - q) hcoef
      _ ≤ q := hrange
  have hKpos : 1 ≤ K := by omega
  nlinarith

lemma base_pencil_strong_sum {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hrange : Fintype.card F ^ 2 * (t - q) ≤ q)
    (hK : 1000000 ≤ Fintype.card F)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (hdelta : (C \ pencilEdges C (basePoint : Point F)).card ≤
      400 * Fintype.card F * (t - q)) :
    3 * basePencilDeficiency a hqmod hqK C ≤
      2 * basePencilMismatch a hqmod hqK C := by
  classical
  let Δ := (C \ pencilEdges C (basePoint : Point F)).card
  have hlocal : ∀ l ∈ linesThrough (basePoint : Point F),
      ∀ z ∈ smallLinePoints l,
      3 * (q - prescribedMatchWeight a hqmod hqK
          (basePoint : Point F) C z) ≤
        2 * prescribedMismatchWeight a hqmod hqK
          (basePoint : Point F) C z := by
    intro l hl z hz
    have hbase := (mem_linesThrough_iff (basePoint : Point F) l).mp hl
    have hsf : (templateSlice C l).card ≤
        prescribedMatchWeight a hqmod hqK (basePoint : Point F) C z := by
      rw [prescribedMatchWeight_eq_base_slice_add_outside a hqmod hqK
        hactive hbase hz]
      exact Nat.le_add_right _ _
    have hdef := base_line_q_deficit_le D a A hqmod hqK hqpos hq ht
      hactive hcover hbase
    have hsmall := base_second_small_arithmetic
      (Fintype.card F) q t Δ (templateSlice C l).card
      (prescribedMatchWeight a hqmod hqK (basePoint : Point F) C z)
      hK hqpos hq hrange (by simpa [Δ] using hdelta) hsf
      (by simpa [Δ] using hdef)
    exact chosen_local_strong_waste D hexp a A hqmod hqK hqpos hq ht
      hcover (basePoint : Point F) z hsmall
  have hsum := Finset.sum_le_sum fun l hl ↦
    Finset.sum_le_sum fun z hz ↦ hlocal l hl z hz
  unfold basePencilDeficiency basePencilMismatch
  simpa only [Finset.mul_sum] using hsum

lemma base_outside_le_eight_defect {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    {balance : ℕ} (hbal : IsBalanced balance a)
    (hbalance : 1000 * (balance + 8) ≤ 521 * Fintype.card F)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    (hrange : Fintype.card F ^ 2 * (t - q) ≤ q)
    (hK : 2000000 ≤ Fintype.card F)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    (halmost : 39 * (C \ pencilEdges C (basePoint : Point F)).card <
      C.card + 156 * fixedC0 * t)
    (hcard : C.card = t + Fintype.card F * q) :
    (C \ pencilEdges C (basePoint : Point F)).card ≤ 8 * (t - q) := by
  let Δ := (C \ pencilEdges C (basePoint : Point F)).card
  let Q := basePencilDeficiency a hqmod hqK C
  let G := basePencilMismatch a hqmod hqK C
  have hlower := base_pencil_deficiency_lower a hbal hqmod hqK hq
    hactive hcard
  have hG := base_pencil_mismatch_le a hbal hqmod hqK hactive
  have hweak := base_pencil_weak_sum D hexp a A hqmod hqK hqpos hq ht
    hrange hK hactive hcover halmost hcard
  have hdelta : Δ ≤ 400 * Fintype.card F * (t - q) :=
    base_weak_delta_arithmetic (Fintype.card F) (balance + 8) (t - q)
      Δ Q G (by omega) hbalance (by simpa [Δ, Q] using hlower)
      (by simpa [Δ, G] using hG) (by simpa [Q, G] using hweak)
  have hstrong := base_pencil_strong_sum D hexp a A hqmod hqK
    hqpos hq ht hrange (by omega) hactive hcover (by simpa [Δ] using hdelta)
  exact base_strong_delta_arithmetic (Fintype.card F) (balance + 8)
    (t - q) Δ Q G (by omega) hbalance (by simpa [Δ, Q] using hlower)
    (by simpa [Δ, G] using hG) (by simpa [Q, G] using hstrong)

lemma exactTotalWeight_eq_base_slice_add_outside {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    {l : Line F} (hbase : Incident (basePoint : Point F) l)
    {z : BasePoint F} (hz : z ∈ smallLinePoints l) :
    exactTotalWeight a A hqmod hqK hq ht (basePoint : Point F) C z =
      (templateSlice C l).card +
        ∑ e ∈ C \ pencilEdges C (basePoint : Point F),
          exactEdgeWeightAt a A hqmod hqK hq ht
            (basePoint : Point F) e z := by
  classical
  let w : Edge F q t → ℕ := fun e ↦ exactEdgeWeightAt a A hqmod hqK hq ht
    (basePoint : Point F) e z
  let P := pencilEdges C (basePoint : Point F)
  let S := templateSlice C l
  have hPC : P ⊆ C := Finset.filter_subset _ _
  have hSP : S ⊆ P := templateSlice_subset_pencilEdges C hbase
  have hslice : ∑ e ∈ S, w e = S.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro e he
    rcases (mem_templateSlice_iff C l e).mp he with ⟨heC, heline⟩
    have hone := active_edge_weight_one_on_base_pencil a hqmod hqK hbase
      ((mem_smallLinePoints_iff l z).mp hz) heline (hactive e heC)
    have hline := base_lineThrough_eq hbase ((mem_smallLinePoints_iff l z).mp hz)
    rcases e with ⟨m, row | row⟩
    · change m = l at heline
      subst m
      simp [w, exactEdgeWeightAt, hline, hbase, originalAt, largeOriginalAt,
        smallPiecesAt, (mem_smallLinePoints_iff l z).mp hz]
    · change m = l at heline
      subst m
      have : (l, (Sum.inr row : Fin t × Fin t ⊕ ZMod q × ZMod q)) ∉
          activeTemplate l := by
        rw [activeTemplate, if_pos hbase]
        simp
      exact (this (hactive (l, Sum.inr row) heC)).elim
  have hother : ∑ e ∈ P \ S, w e = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have he' := Finset.mem_sdiff.mp he
    have heP := Finset.mem_filter.mp he'.1
    have hel : e.1 ≠ l := by
      intro hel
      exact he'.2 ((mem_templateSlice_iff C l e).mpr ⟨heP.1, hel⟩)
    have hze : ¬ Incident z.1 e.1 := by
      intro hze
      apply hel
      exact line_unique_of_two_points (Ne.symm z.2) heP.2 hze hbase
        ((mem_smallLinePoints_iff l z).mp hz)
    simp [w, exactEdgeWeightAt, originalAt, largeOriginalAt, smallPiecesAt,
      edgeWeightAt, hze]
  have hPS : ∑ e ∈ P, w e = S.card := by
    calc
      ∑ e ∈ P, w e = (∑ e ∈ S, w e) + ∑ e ∈ P \ S, w e := by
        rw [← Finset.sum_union Finset.disjoint_sdiff,
          Finset.union_sdiff_of_subset hSP]
      _ = S.card := by rw [hslice, hother, Nat.add_zero]
  unfold exactTotalWeight
  change (∑ e ∈ C, w e) = _
  calc
    ∑ e ∈ C, w e = (∑ e ∈ P, w e) + ∑ e ∈ C \ P, w e := by
      rw [← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset hPC]
    _ = S.card + ∑ e ∈ C \ P, w e := by rw [hPS]
    _ = _ := rfl

lemma sum_smallLine_exactWeight_le_sixteen {q t : ℕ} [Fact q.Prime]
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {l : Line F} (hbase : Incident (basePoint : Point F) l)
    (e : Edge F q t) (hexterior : ¬ Incident (basePoint : Point F) e.1)
    (heActive : e ∈ activeTemplate e.1) :
    (∑ z ∈ smallLinePoints l,
      exactEdgeWeightAt a A hqmod hqK hq ht (basePoint : Point F) e z) ≤ 16 := by
  classical
  let U := (smallLinePoints l).filter fun z ↦ Incident z.1 e.1
  have hle : (∑ z ∈ smallLinePoints l,
      exactEdgeWeightAt a A hqmod hqK hq ht (basePoint : Point F) e z) ≤
      ∑ _z ∈ U, 16 := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro z hz
    by_cases hze : Incident z.1 e.1
    · simp only [hze, if_true]
      have hw := originalAt_card_le_twice_weight a A hqmod hqK hq ht e z
      have h8 := edgeWeightAt_le_eight_of_active a hqmod hqK e z heActive
      have hspecial : Incident (basePoint : Point F)
          (lineThroughPoints (basePoint : Point F) z.1) :=
        lineThroughPoints_incident_left _ _
      simp only [exactEdgeWeightAt, hspecial, if_pos]
      omega
    · simp [hze, exactEdgeWeightAt, originalAt, largeOriginalAt,
        smallPiecesAt, edgeWeightAt]
  have hU : U.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz w hw
    have hz' := Finset.mem_filter.mp hz
    have hw' := Finset.mem_filter.mp hw
    have hlm : l ≠ e.1 := by
      intro heq
      exact hexterior (by simpa [← heq] using hbase)
    apply Subtype.ext
    exact point_unique_of_two_lines hlm
      ((mem_smallLinePoints_iff l z).mp hz'.1) hz'.2
      ((mem_smallLinePoints_iff l w).mp hw'.1) hw'.2
  calc
    _ ≤ ∑ _z ∈ U, 16 := hle
    _ = 16 * U.card := by simp [mul_comm]
    _ ≤ 16 * 1 := Nat.mul_le_mul_left 16 hU
    _ = 16 := by norm_num

lemma base_line_t_deficit_le {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    {l : Line F} (hbase : Incident (basePoint : Point F) l) :
    Fintype.card F * (t - (templateSlice C l).card) ≤
      16 * (C \ pencilEdges C (basePoint : Point F)).card := by
  classical
  let O := C \ pencilEdges C (basePoint : Point F)
  have hpoint : ∀ z ∈ smallLinePoints l,
      t - (templateSlice C l).card ≤
        ∑ e ∈ O, exactEdgeWeightAt a A hqmod hqK hq ht
          (basePoint : Point F) e z := by
    intro z hz
    have hspecial : Incident (basePoint : Point F)
        (lineThroughPoints (basePoint : Point F) z.1) :=
      lineThroughPoints_incident_left _ _
    have hlower := exactTotalWeight_cover_lower_of_base_pencil
      D a A hqmod hqK hq ht hcover (basePoint : Point F) z hspecial
    have htotal := exactTotalWeight_eq_base_slice_add_outside
      a A hqmod hqK hq ht hactive hbase hz
    dsimp [O] at htotal ⊢
    omega
  have hsum := Finset.sum_le_sum fun z hz ↦ hpoint z hz
  have hedge : ∑ e ∈ O, ∑ z ∈ smallLinePoints l,
      exactEdgeWeightAt a A hqmod hqK hq ht
        (basePoint : Point F) e z ≤ 16 * O.card := by
    calc
      _ ≤ ∑ _e ∈ O, 16 := by
        apply Finset.sum_le_sum
        intro e he
        have he' := Finset.mem_sdiff.mp he
        have hexterior : ¬ Incident (basePoint : Point F) e.1 := by
          simpa [pencilEdges, he'.1] using he'.2
        exact sum_smallLine_exactWeight_le_sixteen a A hqmod hqK hq ht
          hbase e hexterior (hactive e he'.1)
      _ = 16 * O.card := by simp [mul_comm]
  dsimp [O] at hsum hedge ⊢
  simp [card_smallLinePoints_of_base l hbase, mul_comm] at hsum
  rw [Finset.sum_comm] at hsum
  exact hsum.trans hedge

lemma base_total_t_deficit_eq {q t : ℕ}
    {C : Finset (Edge F q t)} (hnormal : IsNormal C)
    (hq : q ≤ t)
    (hcard : C.card = t + Fintype.card F * q) :
    (∑ l ∈ linesThrough (basePoint : Point F),
      (t - (templateSlice C l).card)) =
      Fintype.card F * (t - q) +
        (C \ pencilEdges C (basePoint : Point F)).card := by
  classical
  have hsumsub :
      (∑ l ∈ linesThrough (basePoint : Point F),
        (t - (templateSlice C l).card)) =
      (∑ _l ∈ linesThrough (basePoint : Point F), t) -
        ∑ l ∈ linesThrough (basePoint : Point F),
          (templateSlice C l).card := by
    induction linesThrough (basePoint : Point F) using Finset.induction_on with
    | empty => simp
    | @insert l S hl ih =>
        rw [Finset.sum_insert hl, Finset.sum_insert hl, Finset.sum_insert hl, ih]
        have hlcap : (templateSlice C l).card ≤ t := (hnormal l).trans (by
          unfold templateCap
          split <;> omega)
        have hScap : (∑ m ∈ S, (templateSlice C m).card) ≤
            ∑ _m ∈ S, t := by
          exact Finset.sum_le_sum fun m _ ↦ (hnormal m).trans (by
            unfold templateCap
            split <;> omega)
        omega
  have hpencil := pencil_slice_card_sum C (basePoint : Point F)
  have hsub : pencilEdges C (basePoint : Point F) ⊆ C :=
    Finset.filter_subset _ _
  have hout : (C \ pencilEdges C (basePoint : Point F)).card =
      C.card - (pencilEdges C (basePoint : Point F)).card :=
    Finset.card_sdiff_of_subset hsub
  have hP_le : (pencilEdges C (basePoint : Point F)).card ≤ C.card :=
    Finset.card_le_card hsub
  have htotal : (Fintype.card F + 1) * t =
      Fintype.card F * (t - q) + C.card := by
    have htdecomp : t = q + (t - q) := by omega
    calc
      (Fintype.card F + 1) * t =
          (Fintype.card F + 1) * (q + (t - q)) :=
        congrArg (fun n ↦ (Fintype.card F + 1) * n) htdecomp
      _ = Fintype.card F * (t - q) +
          ((q + (t - q)) + Fintype.card F * q) := by ring
      _ = Fintype.card F * (t - q) +
          (t + Fintype.card F * q) :=
        congrArg (fun n ↦ Fintype.card F * (t - q) +
          (n + Fintype.card F * q)) htdecomp.symm
      _ = Fintype.card F * (t - q) + C.card :=
        congrArg (fun n ↦ Fintype.card F * (t - q) + n) hcard.symm
  rw [hsumsub, ← hpencil]
  simp only [Finset.sum_const_nat, card_linesThrough]
  calc
    (Fintype.card F + 1) * t -
        (pencilEdges C (basePoint : Point F)).card =
        (Fintype.card F * (t - q) + C.card) -
          (pencilEdges C (basePoint : Point F)).card := by rw [htotal]
    _ = Fintype.card F * (t - q) +
        (C.card - (pencilEdges C (basePoint : Point F)).card) :=
      Nat.add_sub_assoc hP_le (Fintype.card F * (t - q))
    _ = _ := by rw [← hout]

lemma base_center_impossible {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqt : q < t) (ht : t ≤ 2 * q)
    (hK : 2000000 ≤ Fintype.card F)
    {C : Finset (Edge F q t)} (hnormal : IsNormal C)
    (hactive : IsActive C)
    (hcover : (hypergraph D a A hqmod hqK hqt.le ht).IsEdgeCover C)
    (hcard : C.card = t + Fintype.card F * q)
    (hdelta : (C \ pencilEdges C (basePoint : Point F)).card ≤
      8 * (t - q)) : False := by
  let Δ := (C \ pencilEdges C (basePoint : Point F)).card
  let d := t - q
  have hlines := Finset.sum_le_sum fun l hl ↦
    base_line_t_deficit_le D a A hqmod hqK hqt.le ht hactive hcover
      ((mem_linesThrough_iff (basePoint : Point F) l).mp hl)
  have hdefeq := base_total_t_deficit_eq (F := F) hnormal hqt.le hcard
  have hlinecard := card_linesThrough (basePoint : Point F)
  rw [← Finset.mul_sum, hdefeq] at hlines
  simp only [Finset.sum_const_nat, hlinecard] at hlines
  have hd : 0 < t - q := by omega
  have hmain : Fintype.card F ^ 2 * (t - q) ≤
      128 * (Fintype.card F + 1) * (t - q) := by
    calc
      Fintype.card F ^ 2 * (t - q) ≤
          Fintype.card F *
            (Fintype.card F * (t - q) +
              (C \ pencilEdges C (basePoint : Point F)).card) := by
        nlinarith
      _ ≤ 16 * (Fintype.card F + 1) *
          (C \ pencilEdges C (basePoint : Point F)).card := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hlines
      _ ≤ 16 * (Fintype.card F + 1) * (8 * (t - q)) := by gcongr
      _ = 128 * (Fintype.card F + 1) * (t - q) := by ring
  have hcancel : Fintype.card F ^ 2 ≤ 128 * (Fintype.card F + 1) :=
    Nat.le_of_mul_le_mul_right (by simpa [mul_assoc] using hmain) hd
  nlinarith

lemma fixedBalance_add_twentyfour_le (K : ℕ) (hK : 1000000 ≤ K) :
    1000 * (fixedBalance K + 24) ≤ 521 * K := by
  have hdiv := Nat.mul_div_le (K + 1) 25
  unfold fixedBalance
  omega

lemma fixedBalance_add_eight_le (K : ℕ) (hK : 1000000 ≤ K) :
    1000 * (fixedBalance K + 8) ≤ 521 * K := by
  have hdiv := Nat.mul_div_le (K + 1) 25
  unfold fixedBalance
  omega

lemma exact_concentration {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F)
    (hgood : IsGood (fixedBalance (Fintype.card F)) fixedC0 a)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hqt : q < t) (ht : t ≤ 2 * q)
    (hclose : 20 * (t - q) + 20 ≤ q)
    (hrange : Fintype.card F ^ 2 * t ≤
      (Fintype.card F ^ 2 + 1) * q)
    (hK : 20000000 ≤ Fintype.card F)
    {C : Finset (Edge F q t)}
    (hcover : (hypergraph D a A hqmod hqK hqt.le ht).IsEdgeCover C)
    (hactive : IsActive C) (hnormal : IsNormal C)
    (hcard : C.card = t + Fintype.card F * q) :
    ∃ x : BasePoint F, pencilEdges C x.1 = C := by
  have hdefect : Fintype.card F ^ 2 * (t - q) ≤ q := by
    have hsplit : Fintype.card F ^ 2 * t =
        Fintype.card F ^ 2 * q +
          Fintype.card F ^ 2 * (t - q) := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hqt.le]
    rw [hsplit, Nat.add_mul] at hrange
    omega
  obtain ⟨center, hstrong⟩ := strongly_almost_concentrated
    D hexp a hgood A hqmod hqK hqpos hqt.le ht hclose hrange
      hcover hactive hnormal hcard
  have hcardpos : 0 < C.card := by rw [hcard]; positivity
  by_cases hcenter : center = (basePoint : Point F)
  · subst center
    have hdelta := base_outside_le_eight_defect D hexp a A hgood.balanced
      (fixedBalance_add_eight_le (Fintype.card F) (by omega))
      hqmod hqK hqpos hqt.le ht hdefect (by omega) hactive hcover hstrong hcard
    exact (base_center_impossible D a A hqmod hqK hqt ht (by omega) hnormal
      hactive hcover hcard hdelta).elim
  · let x : BasePoint F := ⟨center, hcenter⟩
    have hout := pencil_exact_outside_eq_zero D hexp a A hgood.balanced
      (fixedBalance_add_twentyfour_le (Fintype.card F) (by omega))
      hqmod hqK hqpos hqt.le ht hdefect (by omega) hnormal hactive hcover
      x (by simpa [x] using hstrong) hcard
    refine ⟨x, Finset.Subset.antisymm (Finset.filter_subset _ _) ?_⟩
    intro e he
    by_contra hep
    have : e ∈ C \ pencilEdges C x.1 := Finset.mem_sdiff.mpr ⟨he, hep⟩
    have hpos : 0 < (C \ pencilEdges C x.1).card :=
      Finset.card_pos.mpr ⟨e, this⟩
    omega

lemma exactMatch_eq_prescribed_of_nonbase_pencil {q t : ℕ}
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hq : q ≤ t) (ht : t ≤ 2 * q)
    {x : BasePoint F} {l : Line F} (hxl : Incident x.1 l)
    (hl : ¬ Incident (basePoint : Point F) l)
    {C : Finset (Edge F q t)} {z : BasePoint F}
    (hz : z ∈ usefulPoints x l) :
    exactMatchWeight a A hqmod hqK hq ht x.1 C z =
      prescribedMatchWeight a hqmod hqK x.1 C z := by
  have hline := useful_lineThrough_eq hxl hz
  unfold exactMatchWeight exactSideWeight prescribedMatchWeight sideWeight
  apply Finset.sum_congr rfl
  intro e _
  simp [exactEdgeWeightAt, hline, hl]

lemma selectedLargeOriginal_eq_empty_of_small_pencil {q t : ℕ}
    (A : OrthogonalArray (Fintype.card F + 1) t) (a : Labeling F)
    {C : Finset (Edge F q t)} {x : BasePoint F} {l : Line F}
    (hxl : Incident x.1 l) (hl : ¬ Incident (basePoint : Point F) l)
    (hCpencil : C ⊆ pencilEdges C x.1)
    {z : BasePoint F} (hz : z ∈ usefulPoints x l) (side : Bool) :
    selectedLargeOriginal A a C z side = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨e, heC, hie⟩ := Finset.mem_biUnion.mp hi
  have heP := Finset.mem_filter.mp (hCpencil heC)
  have hside : edgeSideAt a e z = side := by
    by_contra hnot
    simp [hnot] at hie
  rw [if_pos hside] at hie
  have hze : Incident z.1 e.1 := by
    by_contra hnot
    simp [largeOriginalAt, hnot] at hie
  have hel : e.1 = l := by
    apply line_unique_of_two_points
        (fun h ↦ usefulPoint_ne_center hz (Subtype.ext h.symm))
    · exact heP.2
    · exact hze
    · exact hxl
    · exact (mem_smallLinePoints_iff l z).mp (usefulPoints_subset_line x l hz)
  simp [largeOriginalAt, hel, hl] at hie

lemma pencil_cover_slice_card_ge_cap {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t)
    (a : Labeling F) (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hq : q ≤ t) (ht : t ≤ 2 * q)
    {C : Finset (Edge F q t)} (hactive : IsActive C)
    (hcover : (hypergraph D a A hqmod hqK hq ht).IsEdgeCover C)
    {x : BasePoint F} (hCpencil : pencilEdges C x.1 = C)
    {l : Line F} (hxl : Incident x.1 l)
    {z : BasePoint F} (hz : z ∈ usefulPoints x l) :
    templateCap q t l ≤ (templateSlice C l).card := by
  classical
  have hsubset : C ⊆ pencilEdges C x.1 := by rw [hCpencil]
  have hmatch := exactMatchWeight_eq_slice_add_outside
    a A hqmod hqK hq ht hactive hxl hz
  have hmismatch := exactMismatchWeight_eq_outside
    a A hqmod hqK hq ht hactive hxl hz
  have hout : C \ pencilEdges C x.1 = ∅ := by rw [hCpencil, Finset.sdiff_self]
  rw [hout] at hmatch hmismatch
  simp only [Finset.sum_empty, Nat.add_zero] at hmatch hmismatch
  let side := pencilSide a x.1 z
  let L := selectedOriginal A a hqmod hqK hq ht C z side
  let R := selectedOriginal A a hqmod hqK hq ht C z (!side)
  have hcov := selectedOriginal_covers D a A hqmod hqK hq ht hcover z
  have hLRge : t ≤ L.card + R.card := by
    have hsumcover := coversByIndices_card_sum_ge D hcov
    dsimp [L, R, side]
    cases hs : pencilSide a x.1 z
    · simpa [hs] using hsumcover
    · simpa [hs, Nat.add_comm] using hsumcover
  have hRzero : R.card = 0 := by
    have hbound := selectedOriginal_card_le_twice_exactSideWeight
      a A hqmod hqK hq ht x.1 C z (!side)
    change R.card ≤ 2 * exactMismatchWeight a A hqmod hqK hq ht x.1 C z
      at hbound
    omega
  have hLge : t ≤ L.card := by
    omega
  by_cases hl : Incident (basePoint : Point F) l
  · have hspecial : Incident (basePoint : Point F)
        (lineThroughPoints x.1 z.1) := by
      simpa [useful_lineThrough_eq hxl hz] using hl
    have hLupper := selectedOriginal_card_le_exactSideWeight_of_base_pencil
      a A hqmod hqK hq ht x.1 C z side hspecial
    change L.card ≤ exactMatchWeight a A hqmod hqK hq ht x.1 C z at hLupper
    simp [templateCap, hl]
    omega
  · have hlarge : selectedLargeOriginal A a C z side = ∅ :=
      selectedLargeOriginal_eq_empty_of_small_pencil A a hxl hl hsubset hz side
    let S := selectedSmallPieces a hqmod hqK C z side
    have hLeq : L = Compression.lift hq ht S := by
      simp [L, selectedOriginal, S, hlarge]
    have hliftcard : (Compression.lift hq ht S).card = t := by
      have hu : (Compression.lift hq ht S).card ≤ t := by
        simpa using Finset.card_le_card
          (Finset.subset_univ (Compression.lift hq ht S))
      rw [hLeq] at hLge
      omega
    have hlift : Compression.lift hq ht S = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using hliftcard
    have hS : S = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro c
      obtain ⟨i, hi⟩ := Compression.index_surjective hqpos hq ht c
      have hiLift : i ∈ Compression.lift hq ht S := by rw [hlift]; simp
      simpa [Compression.mem_lift_iff, hi] using hiLift
    have hScard : S.card = q := by rw [hS]; simp
    have hSupper := selectedSmallPieces_card_le a hqmod hqK C z side
    have hprescribed :
        exactMatchWeight a A hqmod hqK hq ht x.1 C z =
          prescribedMatchWeight a hqmod hqK x.1 C z :=
      exactMatch_eq_prescribed_of_nonbase_pencil
        a A hqmod hqK hq ht hxl hl (C := C) hz
    change S.card ≤ sideWeight a hqmod hqK C z side at hSupper
    change exactMatchWeight a A hqmod hqK hq ht x.1 C z =
      sideWeight a hqmod hqK C z side at hprescribed
    simp [templateCap, hl]
    omega

theorem hypergraph_edgeCoverNumberAtLeast {q t : ℕ} [Fact q.Prime]
    (D : Expander.System 100 t) (hexp : D.HasKahnExpansion)
    (a : Labeling F)
    (hgood : IsGood (fixedBalance (Fintype.card F)) fixedC0 a)
    (A : OrthogonalArray (Fintype.card F + 1) t)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqpos : 0 < q) (hqt : q < t) (ht : t ≤ 2 * q)
    (hclose : 20 * (t - q) + 20 ≤ q)
    (hrange : Fintype.card F ^ 2 * t ≤
      (Fintype.card F ^ 2 + 1) * q)
    (hK : 20000000 ≤ Fintype.card F) :
    (hypergraph D a A hqmod hqK hqt.le ht).EdgeCoverNumberAtLeast
      (t + Fintype.card F * q) := by
  intro C hcover
  by_contra hnot
  have hClt : C.card < t + Fintype.card F * q := by omega
  have htpos : 0 < t := hqpos.trans hqt
  let N := normalize A htpos C
  have hNcover := normalize_isEdgeCover D a A hqmod hqK hqt.le ht htpos hcover
  have hNactive := normalize_active A htpos C
  have hNnormal := normalize_normal A htpos C
  have hNcard : N.card ≤ C.card := normalize_card_le A htpos C
  obtain ⟨P, hNP, hPcover, hPactive, hPnormal, hPcard⟩ :=
    exists_normal_cover_card_eq D a A hqmod hqK hqt.le ht hqpos htpos
      hNcover hNactive hNnormal (hNcard.trans hClt.le)
  obtain ⟨x, hPpencil⟩ := exact_concentration D hexp a hgood A hqmod hqK
    hqpos hqt ht hclose hrange hK hPcover hPactive hPnormal hPcard
  have hNpencil : pencilEdges N x.1 = N := by
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro e heN
    have heP := hNP heN
    have hePP : e ∈ pencilEdges P x.1 := by simpa [hPpencil] using heP
    exact Finset.mem_filter.mpr ⟨heN, (Finset.mem_filter.mp hePP).2⟩
  have hslices : ∀ l ∈ linesThrough x.1,
      templateCap q t l ≤ (templateSlice N l).card := by
    intro l hl
    have hxl := (mem_linesThrough_iff x.1 l).mp hl
    have huseful : (usefulPoints x l).Nonempty := by
      apply Finset.card_pos.mp
      have hge := usefulPoints_card_ge x l hxl
      omega
    obtain ⟨z, hz⟩ := huseful
    exact pencil_cover_slice_card_ge_cap D a A hqmod hqK hqpos hqt.le ht
      hNactive hNcover hNpencil hxl hz
  have hsum := Finset.sum_le_sum hslices
  have hNsum := pencil_slice_card_sum N x.1
  have hcaps := pencil_capacity_sum x q t
  rw [hcaps, ← hNsum, hNpencil] at hsum
  omega

end Construction

/-! ## Reindexing the finite construction and producing dual witnesses -/

namespace IndexedHypergraph

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

/-- Relabel both finite index types by their canonical finite ordinals. -/
noncomputable def finModel (H : IndexedHypergraph V E) :
    IndexedHypergraph (Fin (Fintype.card V)) (Fin (Fintype.card E)) where
  edge e := (H.edge ((Fintype.equivFin E).symm e)).map
    (Fintype.equivFin V).toEmbedding

lemma finModel_incident (H : IndexedHypergraph V E)
    (v : Fin (Fintype.card V)) :
    (H.finModel.incident v) =
      (H.incident ((Fintype.equivFin V).symm v)).map
        (Fintype.equivFin E).toEmbedding := by
  classical
  ext e
  simp [finModel, IndexedHypergraph.incident]

lemma finModel_regular (H : IndexedHypergraph V E) {r : ℕ}
    (hreg : H.IsRegular r) : H.finModel.IsRegular r := by
  intro v
  rw [finModel_incident]
  rw [Finset.card_map]
  exact hreg _

lemma finModel_pairCovered (H : IndexedHypergraph V E)
    (hpairs : H.PairCovered) : H.finModel.PairCovered := by
  intro x y hxy
  have hxy' : (Fintype.equivFin V).symm x ≠ (Fintype.equivFin V).symm y := by
    intro h
    apply hxy
    exact (Fintype.equivFin V).symm.injective.eq_iff.mp h
  obtain ⟨e, hex, hey⟩ := hpairs hxy'
  refine ⟨Fintype.equivFin E e, ?_, ?_⟩ <;>
    simpa [finModel] using ‹_›

lemma finModel_edgeCoverNumberAtLeast (H : IndexedHypergraph V E) {r : ℕ}
    (hcover : H.EdgeCoverNumberAtLeast r) :
    H.finModel.EdgeCoverNumberAtLeast r := by
  classical
  intro C hC
  let C' : Finset E := C.map (Fintype.equivFin E).symm.toEmbedding
  have hC' : H.IsEdgeCover C' := by
    intro v
    obtain ⟨e, heC, hve⟩ := hC (Fintype.equivFin V v)
    refine ⟨(Fintype.equivFin E).symm e, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨e, heC, rfl⟩
    · simpa [finModel] using hve
  have hr := hcover C' hC'
  simpa [C'] using hr

lemma hasDualWitness_of_finite (H : IndexedHypergraph V E) {C r : ℕ}
    (hreg : H.IsRegular r) (hpairs : H.PairCovered)
    (hcover : H.EdgeCoverNumberAtLeast r)
    (hv : Fintype.card V ≤ C * r) : HasDualWitness C r := by
  refine ⟨Fintype.card V, Fintype.card E, H.finModel,
    H.finModel_regular hreg, H.finModel_pairCovered hpairs,
    H.finModel_edgeCoverNumberAtLeast hcover, hv⟩

end IndexedHypergraph

namespace Construction

open Projective Labels Expander Compression Local Transversal

variable {F : Type*} [Fintype F] [Field F] [DecidableEq F]

lemma hasDualWitness_of_parameters {q t : ℕ} (hqprime : q.Prime)
    (a : Labeling F)
    (hgood : IsGood (fixedBalance (Fintype.card F)) fixedC0 a)
    (hqmod : q % 4 = 3) (hqK : 2 * Fintype.card F + 1 ≤ q)
    (hqt : q < t) (ht : t ≤ 2 * q)
    (hclose : 20 * (t - q) + 20 ≤ q)
    (hrange : Fintype.card F ^ 2 * t ≤
      (Fintype.card F ^ 2 + 1) * q)
    (hfactors : ∀ p : ℕ, p.Prime → p ∣ t → Fintype.card F ≤ p)
    (hK : 20000000 ≤ Fintype.card F) :
    HasDualWitness (200 * (Fintype.card F + 1))
      (t + Fintype.card F * q) := by
  letI : Fact q.Prime := ⟨hqprime⟩
  have hqpos : 0 < q := hqprime.pos
  have htpos : 0 < t := hqpos.trans hqt
  let A : OrthogonalArray (Fintype.card F + 1) t :=
    OrthogonalArray.ofNatOfPrimeFactorsLarge (Fintype.card F + 1) t
      htpos.ne' (fun p hp hpt ↦ by
        have := hfactors p hp hpt
        omega)
  obtain ⟨D, hexp⟩ := Expander.Random.exists_kahn_expander t htpos
  let H := hypergraph D a A hqmod hqK hqt.le ht
  have hreg : H.IsRegular (t + Fintype.card F * q) :=
    hypergraph_regular D a A hqmod hqK hqt.le ht
  have hpairs : H.PairCovered :=
    hypergraph_pairCovered D a A hqmod hqK hqt.le ht
  have hcover : H.EdgeCoverNumberAtLeast (t + Fintype.card F * q) :=
    hypergraph_edgeCoverNumberAtLeast D hexp a hgood A hqmod hqK hqpos hqt ht
      hclose hrange hK
  apply H.hasDualWitness_of_finite hreg hpairs hcover
  rw [card_vertex]
  calc
    100 * (Fintype.card F ^ 2 + Fintype.card F) * t ≤
        100 * (Fintype.card F ^ 2 + Fintype.card F) * (2 * q) := by gcongr
    _ ≤ 200 * (Fintype.card F + 1) *
        (t + Fintype.card F * q) := by
      have hKpos : 1 ≤ Fintype.card F := Fintype.card_pos
      nlinarith

end Construction

namespace Arithmetic

/-- Add the elementary lower bounds on `q` needed by the finite
construction to the CRT/PNT parameter theorem. -/
lemma eventually_exists_usable_parameters_of_residues
    (K Q : ℕ) (P : ℕ → Prop) (hK : 7 ≤ K) (hQ : 1 ≤ Q) (h4Q : 4 ∣ Q)
    (hres : ∀ r : ℕ, P r → ∃ a : ℕ, IsKahnResidue K Q r a) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → P r →
      ∃ q t : ℕ, q.Prime ∧ q % 4 = 3 ∧ q < t ∧ t ≤ 2 * q ∧
        20 * (t - q) + 20 ≤ q ∧ 2 * K + 1 ≤ q ∧
        K ^ 2 * t ≤ (K ^ 2 + 1) * q ∧ r = K * q + t ∧
        ∀ p : ℕ, p.Prime → p ∣ t → K ≤ p := by
  obtain ⟨R₀, hR₀⟩ := eventually_exists_refined_parameters_of_residues
    K Q P (by omega) hQ h4Q hres
  let B := max (2 * K + 1) 40
  refine ⟨max R₀ ((K + 2) * B), ?_⟩
  intro r hr hPr
  obtain ⟨q, t, hqprime, hqmod, hqt, hrange, hsum, hfactors⟩ :=
    hR₀ r (le_trans (le_max_left _ _) hr) hPr
  have hKsq : 0 < K ^ 2 := by positivity
  have ht : t ≤ 2 * q := by
    have hcoef : K ^ 2 + 1 ≤ 2 * K ^ 2 := by nlinarith
    have hmul : K ^ 2 * t ≤ K ^ 2 * (2 * q) :=
      hrange.trans (by
        calc
          (K ^ 2 + 1) * q ≤ (2 * K ^ 2) * q := Nat.mul_le_mul_right q hcoef
          _ = K ^ 2 * (2 * q) := by ring)
    exact Nat.le_of_mul_le_mul_left hmul hKsq
  have hBq : B ≤ q := by
    have hlower : (K + 2) * B ≤ r := le_trans (le_max_right _ _) hr
    have hupper : r ≤ (K + 2) * q := by
      rw [hsum]
      nlinarith
    exact Nat.le_of_mul_le_mul_left (hlower.trans hupper) (by omega)
  have hqK : 2 * K + 1 ≤ q := (le_max_left _ _).trans hBq
  have hq40 : 40 ≤ q := (le_max_right _ _).trans hBq
  have hdefect : K ^ 2 * (t - q) ≤ q := by
    have hsplit : K ^ 2 * t = K ^ 2 * q + K ^ 2 * (t - q) := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hqt.le]
    rw [hsplit, Nat.add_mul] at hrange
    omega
  have h40 : 40 * (t - q) ≤ q := by
    have hcoef : 40 ≤ K ^ 2 := by
      have hsq := Nat.mul_le_mul hK hK
      norm_num [pow_two] at hsq ⊢
      omega
    exact (Nat.mul_le_mul_right (t - q) hcoef).trans hdefect
  have hclose : 20 * (t - q) + 20 ≤ q := by omega
  exact ⟨q, t, hqprime, hqmod, hqt, ht, hclose, hqK,
    hrange, hsum, hfactors⟩

lemma eventually_exists_usable_parameters_mod_two_one
    (K Q : ℕ) (hK : 7 ≤ K) (hQ : 1 ≤ Q) (h4Q : 4 ∣ Q)
    (hres : ∀ r : ℕ, r % 2 = 1 → ∃ a : ℕ, IsKahnResidue K Q r a) :
    EventuallyUsableParameters K 1 := by
  unfold EventuallyUsableParameters
  exact eventually_exists_usable_parameters_of_residues K Q
    (fun r ↦ r % 2 = 1) hK hQ h4Q hres

lemma eventually_exists_usable_parameters_mod_two_zero
    (K Q : ℕ) (hK : 7 ≤ K) (hQ : 1 ≤ Q) (h4Q : 4 ∣ Q)
    (hres : ∀ r : ℕ, r % 2 = 0 → ∃ a : ℕ, IsKahnResidue K Q r a) :
    EventuallyUsableParameters K 0 := by
  unfold EventuallyUsableParameters
  exact eventually_exists_usable_parameters_of_residues K Q
    (fun r ↦ r % 2 = 0) hK hQ h4Q hres

lemma even_order_prime_factors
    (p n : ℕ) (hp : p.Prime) (hdiv : p ∣ 2 ^ n) :
    p = 2 := by
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hdiv
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2

lemma odd_order_prime_factors
    (p : ℕ) (hp : p.Prime) (hpK : p < mersenne 127)
    (hdiv : p ∣ mersenne 127) : p = 2 := by
  have heq : p = mersenne 127 :=
    (Nat.prime_dvd_prime_iff_eq hp erdos21_mersenne127_prime).mp hdiv
  omega

lemma card_evenField_ge_twenty_million :
    20000000 ≤ Fintype.card EvenField := by
  rw [card_evenField]
  calc
    20000000 ≤ 2 ^ 25 := by norm_num
    _ ≤ 2 ^ 111 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

lemma card_oddField_ge_twenty_million :
    20000000 ≤ Fintype.card OddField := by
  rw [card_oddField]
  apply Nat.le_sub_of_add_le
  calc
    20000000 + 1 ≤ 2 ^ 25 := by norm_num
    _ ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

lemma evenOrder_mod_two : evenOrder % 2 = 0 := by
  unfold evenOrder
  norm_num

lemma oddOrder_mod_two : oddOrder % 2 = 1 := by
  unfold oddOrder
  have hpow : 0 < 2 ^ 126 := by positivity
  have heq : 2 ^ 127 - 1 = 2 * (2 ^ 126 - 1) + 1 := by
    rw [show 127 = 126 + 1 by omega, pow_succ]
    omega
  rw [heq]
  simp

lemma evenOrder_ge_seven : 7 ≤ evenOrder := by
  unfold evenOrder
  calc
    7 ≤ 2 ^ 3 := by norm_num
    _ ≤ 2 ^ 111 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

lemma oddOrder_ge_seven : 7 ≤ oddOrder := by
  unfold oddOrder
  apply Nat.le_sub_of_add_le
  change 8 ≤ 2 ^ 127
  calc
    8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) (by norm_num)

lemma kahnModulus_one_le (K : ℕ) : 1 ≤ kahnModulus K := by
  exact Nat.mul_pos (by norm_num) (oddPrimeModulus_pos K)

lemma four_dvd_kahnModulus (K : ℕ) : 4 ∣ kahnModulus K := by
  exact dvd_mul_right 4 _

lemma evenField_prime_factors (p : ℕ) (hp : p.Prime)
    (hdiv : p ∣ evenOrder) : p = 2 := by
  apply even_order_prime_factors p 111 hp
  unfold evenOrder at hdiv
  exact hdiv

lemma oddField_prime_factors (p : ℕ) (hp : p.Prime)
    (hpK : p < oddOrder) (hdiv : p ∣ oddOrder) : p = 2 := by
  unfold oddOrder at hpK hdiv
  change p < mersenne 127 at hpK
  change p ∣ mersenne 127 at hdiv
  exact odd_order_prime_factors p hp hpK hdiv

lemma evenOrder_opposite_parity (r : ℕ) (hr : r % 2 = 1) :
    evenOrder % 2 ≠ r % 2 := by
  rw [evenOrder_mod_two, hr]
  decide

lemma oddOrder_opposite_parity (r : ℕ) (hr : r % 2 = 0) :
    oddOrder % 2 ≠ r % 2 := by
  rw [oddOrder_mod_two, hr]
  decide

lemma exists_evenField_kahnResidue (r : ℕ) (hr : r % 2 = 1) :
    ∃ a : ℕ, IsKahnResidue evenOrder (kahnModulus evenOrder) r a := by
  exact exists_kahnResidue evenOrder r (evenOrder_opposite_parity r hr)
    (fun p hp _hpK hdiv ↦ evenField_prime_factors p hp hdiv)

lemma exists_oddField_kahnResidue (r : ℕ) (hr : r % 2 = 0) :
    ∃ a : ℕ, IsKahnResidue oddOrder (kahnModulus oddOrder) r a := by
  exact exists_kahnResidue oddOrder r (oddOrder_opposite_parity r hr)
    oddField_prime_factors

lemma eventually_evenField_parameters :
    EventuallyUsableParameters evenOrder 1 := by
  exact eventually_exists_usable_parameters_mod_two_one
    evenOrder (kahnModulus evenOrder) evenOrder_ge_seven
    (kahnModulus_one_le evenOrder) (four_dvd_kahnModulus evenOrder)
    exists_evenField_kahnResidue

lemma eventually_oddField_parameters :
    EventuallyUsableParameters oddOrder 0 := by
  exact eventually_exists_usable_parameters_mod_two_zero
    oddOrder (kahnModulus oddOrder) oddOrder_ge_seven
    (kahnModulus_one_le oddOrder) (four_dvd_kahnModulus oddOrder)
    exists_oddField_kahnResidue

end Arithmetic

lemma hasDualWitness_mono {C C' r : ℕ} (hCC' : C ≤ C')
    (h : HasDualWitness C r) : HasDualWitness C' r := by
  obtain ⟨v, e, H, hreg, hpairs, hcover, hv⟩ := h
  refine ⟨v, e, H, hreg, hpairs, hcover, hv.trans ?_⟩
  exact Nat.mul_le_mul_right r hCC'

lemma eventually_evenField_dualWitness :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → r % 2 = 1 →
      HasDualWitness (200 * (Fintype.card EvenField + 1)) r := by
  obtain ⟨a, hgood⟩ := exists_evenField_goodLabeling
  have hparameters := Arithmetic.eventually_evenField_parameters
  unfold Arithmetic.EventuallyUsableParameters at hparameters
  obtain ⟨R, hR⟩ := hparameters
  refine ⟨R, ?_⟩
  intro r hr hodd
  obtain ⟨q, t, hqprime, hqmod, hqt, ht, hclose, hqK,
    hrange, hsum, hfactors⟩ := hR r hr hodd
  simp only [← card_evenField_eq_evenOrder] at hqK hrange hsum hfactors
  have hw := Construction.hasDualWitness_of_parameters (F := EvenField)
    hqprime a hgood hqmod
    hqK hqt ht hclose hrange hfactors (by
      exact Arithmetic.card_evenField_ge_twenty_million)
  have hr' : r = t + Fintype.card EvenField * q := by omega
  simpa [hr'] using hw

lemma eventually_oddField_dualWitness :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r → r % 2 = 0 →
      HasDualWitness (200 * (Fintype.card OddField + 1)) r := by
  obtain ⟨a, hgood⟩ := exists_oddField_goodLabeling
  have hparameters := Arithmetic.eventually_oddField_parameters
  unfold Arithmetic.EventuallyUsableParameters at hparameters
  obtain ⟨R, hR⟩ := hparameters
  refine ⟨R, ?_⟩
  intro r hr heven
  obtain ⟨q, t, hqprime, hqmod, hqt, ht, hclose, hqK,
    hrange, hsum, hfactors⟩ := hR r hr heven
  simp only [← card_oddField_eq_oddOrder] at hqK hrange hsum hfactors
  have hw := Construction.hasDualWitness_of_parameters (F := OddField)
    hqprime a hgood hqmod
    hqK hqt ht hclose hrange hfactors (by
      exact Arithmetic.card_oddField_ge_twenty_million)
  have hr' : r = t + Fintype.card OddField * q := by omega
  simpa [hr'] using hw

/-- Kahn's affirmative resolution of Erdős Problem 21: the least size of
an intersecting `n`-uniform family with transversal number `n` is eventually
bounded by a constant multiple of `n`. -/
theorem erdos_21 :
    ∃ C N : ℕ, ∀ n : ℕ, N ≤ n → erdosLovaszF n ≤ C * n := by
  apply erdos21_of_eventual_dualWitness
  obtain ⟨R₀, hR₀⟩ := eventually_evenField_dualWitness
  obtain ⟨R₁, hR₁⟩ := eventually_oddField_dualWitness
  let C₀ := 200 * (Fintype.card EvenField + 1)
  let C₁ := 200 * (Fintype.card OddField + 1)
  refine ⟨max C₀ C₁, max R₀ R₁, ?_⟩
  intro r hr
  by_cases heven : r % 2 = 0
  · apply hasDualWitness_mono (le_max_right C₀ C₁)
    exact hR₁ r (le_trans (le_max_right R₀ R₁) hr) heven
  · have hodd : r % 2 = 1 := by
      have hlt := Nat.mod_lt r (by norm_num : 0 < 2)
      omega
    apply hasDualWitness_mono (le_max_left C₀ C₁)
    exact hR₀ r (le_trans (le_max_left R₀ R₁) hr) hodd

end

#print axioms erdos_21
-- 'Erdos21.erdos_21' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos21
