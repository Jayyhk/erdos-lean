import Mathlib

set_option linter.style.header false

namespace Erdos1197

open scoped Real
open Real MeasureTheory FourierTransform

set_option maxHeartbeats 4000000

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
open Nat hiding log
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
theorem _root_.Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
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

-- (Asymptotics extension: define IsBigO.natCast at the root level)
theorem _root_.Asymptotics.IsBigO.natCast {E : Type*} [Norm E] {f g : ℝ → E}
    (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Mathlib_Analysis_Asymptotics_Asymptotics

/-! ## --- vendored: Wiener.lean --- -/

section Wiener


set_option lang.lemmaCmd true

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

lemma _root_.Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, Finset.sum_range_add, Finset.sum_range_one, add_comm 1] ; rfl

lemma _root_.Finset.sum_shift_front' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = (fun _ => u 0) + cumsum (shift u) := by
  ext n ; apply Finset.sum_shift_front

lemma _root_.Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]

lemma _root_.Finset.sum_shift_back' {E : Type*} [Ring E] {u : ℕ → E} :
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

lemma _root_.Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]

lemma _root_.BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma _root_.BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
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

lemma _root_.Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
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

lemma _root_.Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
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

lemma _root_.Real.log_eventually_gt_atTop (a : ℝ) :
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
lemma _root_.Real.fourierIntegral_convolution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
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

lemma _root_.Real.fourierIntegral_conj_neg {f : ℝ → ℂ} (y : ℝ) :
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
  let ψ_fun : ℝ → ℂ := convolution φ φ_rev (ContinuousLinearMap.mul ℂ ℂ) volume
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
    HasCompactSupport.convolution (ContinuousLinearMap.mul ℂ ℂ) hφCompact' hφRevCompact
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
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

lemma _root_.Set.Ico_subset_Ico_of_Icc_subset_Icc {a b c d : ℝ} (h : Set.Icc a b ⊆ Set.Icc c d) :
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
theorem _root_.Asymptotics.IsEquivalent.add_isLittleO' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (w - u) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← add_sub_cancel u w]
  exact Asymptotics.IsEquivalent.add_isLittleO huv hwu

/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem _root_.Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
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
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
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

/-! ## Prime-in-interval consequence of positivity of `θ x - θ y` -/

/-- There is a prime in the interval `(x, x + h]`. Mirrors the PNT+ predicate. -/
def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ (p : ℝ) ≤ x + h

/-- **Prime-in-interval consequence.**
If `θ x - θ y > 0` (with `y < x`), there is a prime in `(y, x]`. Proof: if no
such prime existed, every prime `p ≤ ⌊x⌋` would satisfy `p ≤ y`, hence
`p ≤ ⌊y⌋`, so the prime-set indexing `θ x` would be contained in the one
indexing `θ y`. Since `log p ≥ 0` for primes, this forces `θ x ≤ θ y`,
contradicting `θ x - θ y > 0`. -/
theorem theta_pos_implies_prime_in_interval {x y : ℝ}
    (_hxy : y < x) (h : θ x - θ y > 0) :
    HasPrimeInInterval y (x - y) := by
  by_contra hno
  simp only [HasPrimeInInterval, not_exists, not_and, not_le] at hno
  -- hno : ∀ p, Nat.Prime p → y < ↑p → y + (x - y) < ↑p
  have habs : θ x ≤ θ y := by
    rw [Chebyshev.theta_eq_sum_Icc x, Chebyshev.theta_eq_sum_Icc y]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
      by_contra hgt
      push_neg at hgt
      -- hgt : ⌊y⌋₊ < p
      have hyp : y < (p : ℝ) := by
        have hgtR : (⌊y⌋₊ : ℝ) < (p : ℝ) := by exact_mod_cast hgt
        by_cases hy_nn : 0 ≤ y
        · have hge1 : (⌊y⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hgt
          linarith [Nat.lt_floor_add_one y]
        · push_neg at hy_nn
          linarith [show (0 : ℝ) ≤ (p : ℝ) from Nat.cast_nonneg p]
      have hxp := hno p hp.2 hyp
      have hpx : (p : ℝ) ≤ x := by
        have hpfx_nat : p ≤ ⌊x⌋₊ := hp.1.2
        -- p prime ⟹ p ≥ 2 ⟹ ⌊x⌋₊ ≥ 2, hence x must be nonneg (else ⌊x⌋₊ = 0)
        have hp_two : 2 ≤ p := hp.2.two_le
        have hfx_two : 2 ≤ ⌊x⌋₊ := le_trans hp_two hpfx_nat
        have hx_nn : (0 : ℝ) ≤ x := by
          by_contra hxneg
          push_neg at hxneg
          have hfx_zero : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith : x < 1)
          omega
        have hpfx : (p : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hpfx_nat
        linarith [Nat.floor_le hx_nn]
      linarith
    · intro p hp _
      have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.one_lt.le
      exact Real.log_nonneg hp1
  linarith

end Consequences

set_option maxHeartbeats 1000000

-- ============================================================
-- PNTBridge
-- ============================================================

open scoped Asymptotics
open Chebyshev

noncomputable section

set_option warn.sorry false

end
-- ============================================================
-- RequestProject_TorusSeparation
-- ============================================================

/-
# Hard Direction of Kronecker's Theorem

This file contains the proof of the hard direction of Kronecker's approximation
theorem in the BM-facing common-denominator form used by the Buczolich–Mauldin
construction, along with the torus-separation infrastructure that supports it.
-/

open scoped BigOperators

noncomputable section

/-! ## Classification of closed subgroups of ℝ -/

/-- A closed nontrivial additive subgroup of ℝ is either all of ℝ or cyclic. -/
lemma closed_addsubgroup_of_real (S : AddSubgroup ℝ) (hS : IsClosed (S : Set ℝ))
    (hne : ∃ x ∈ S, x ≠ 0) :
    (S : Set ℝ) = Set.univ ∨
    ∃ a : ℝ, 0 < a ∧ (S : Set ℝ) = Set.range (fun n : ℤ => n * a) := by
  by_cases ha : sInf ({x : ℝ | 0 < x ∧ x ∈ S}) = 0
  · have h_dense : ∀ ε > 0, ∃ x ∈ S, 0 < x ∧ x < ε := by
      intro ε hε_pos
      have h_inf : ∃ x ∈ {x : ℝ | 0 < x ∧ x ∈ S}, x < ε := by
        contrapose! ha
        exact ne_of_gt <| lt_of_lt_of_le hε_pos <| le_csInf
          ⟨|hne.choose|, ⟨abs_pos.mpr hne.choose_spec.2,
            by simpa using S.zsmul_mem hne.choose_spec.1 1⟩⟩
          fun x hx => ha x hx
      aesop
    have h_dense : ∀ y : ℝ, ∀ ε > 0, ∃ x ∈ S, |x - y| < ε := by
      intro y ε hε_pos
      obtain ⟨x, hxS, hx_pos, hx_lt⟩ := h_dense ε hε_pos
      have h_seq : ∀ n : ℤ, n * x ∈ S := fun n => by simpa using S.zsmul_mem hxS n
      exact ⟨⌊y / x⌋ * x, h_seq _, by
        rw [abs_lt]; constructor <;>
          nlinarith [Int.floor_le (y / x), Int.lt_floor_add_one (y / x),
            mul_div_cancel₀ y hx_pos.ne']⟩
    exact Or.inl <| Set.eq_univ_of_forall fun y =>
      hS.closure_subset_iff.mpr (Set.Subset.refl _) <|
        mem_closure_iff_nhds_basis Metric.nhds_basis_ball |>.2 fun ε hε =>
          h_dense y ε hε
  · have ha_pos : 0 < sInf {x | 0 < x ∧ x ∈ S} := by
      exact lt_of_le_of_ne
        (by apply_rules [Real.sInf_nonneg]; rintro x ⟨hx₁, hx₂⟩; linarith) (Ne.symm ha)
    have ha_least : ∀ x ∈ S, 0 < x → sInf {x | 0 < x ∧ x ∈ S} ≤ x :=
      fun x hx hx' => csInf_le ⟨0, fun y hy => hy.1.le⟩ ⟨hx', hx⟩
    have ha_mem : sInf {x | 0 < x ∧ x ∈ S} ∈ S := by
      obtain ⟨xn, hxn⟩ : ∃ xn : ℕ → ℝ,
          (∀ n, 0 < xn n ∧ xn n ∈ S) ∧
          Filter.Tendsto xn Filter.atTop (nhds (sInf {x | 0 < x ∧ x ∈ S})) := by
        have h_seq : ∀ ε > 0, ∃ x ∈ S, 0 < x ∧ |x - sInf {x | 0 < x ∧ x ∈ S}| < ε := by
          exact fun ε ε_pos => by
            rcases exists_lt_of_csInf_lt
              (show {x : ℝ | 0 < x ∧ x ∈ S}.Nonempty from by contrapose! ha; aesop)
              (lt_add_of_pos_right _ ε_pos)
              with ⟨x, hx₁, hx₂⟩
            exact ⟨x, hx₁.2, hx₁.1, abs_lt.mpr
              ⟨by linarith [ha_least x hx₁.2 hx₁.1], by linarith [ha_least x hx₁.2 hx₁.1]⟩⟩
        exact ⟨fun n => Classical.choose (h_seq (1 / (n + 1)) (by positivity)),
          fun n => ⟨(Classical.choose_spec (h_seq (1 / (n + 1)) (by positivity))).2.1,
            (Classical.choose_spec (h_seq (1 / (n + 1)) (by positivity))).1⟩,
          tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero
            (fun _ => by positivity)
            (fun n => (Classical.choose_spec (h_seq (1 / (n + 1)) (by positivity))).2.2.le)
            tendsto_one_div_add_atTop_nhds_zero_nat⟩
      exact hS.mem_of_tendsto hxn.2 (Filter.Eventually.of_forall fun n => hxn.1 n |>.2)
    have hS_eq : S = AddSubgroup.zmultiples (sInf {x | 0 < x ∧ x ∈ S}) := by
      have hS_eq : ∀ x ∈ S, ∃ n : ℤ, x = n * sInf {x | 0 < x ∧ x ∈ S} := by
        intro x hx; by_contra h_contra
        obtain ⟨n, hn⟩ : ∃ n : ℤ, n * sInf {x | 0 < x ∧ x ∈ S} ≤ x ∧
            x < (n + 1) * sInf {x | 0 < x ∧ x ∈ S} :=
          ⟨⌊x / sInf {x | 0 < x ∧ x ∈ S}⌋, by
            nlinarith [Int.floor_le (x / sInf {x | 0 < x ∧ x ∈ S}),
              mul_div_cancel₀ x ha], by
            nlinarith [Int.lt_floor_add_one (x / sInf {x | 0 < x ∧ x ∈ S}),
              mul_div_cancel₀ x ha]⟩
        have h_c : x - n * sInf {x | 0 < x ∧ x ∈ S} ∈ S ∧
            0 < x - n * sInf {x | 0 < x ∧ x ∈ S} ∧
            x - n * sInf {x | 0 < x ∧ x ∈ S} < sInf {x | 0 < x ∧ x ∈ S} :=
          ⟨by simpa using S.sub_mem hx (S.zsmul_mem ha_mem n),
           lt_of_le_of_ne (by linarith)
             (Ne.symm <| by intro H; exact h_contra ⟨n, by linarith⟩), by linarith⟩
        linarith [ha_least _ h_c.1 h_c.2.1]
      refine le_antisymm ?_ ?_ <;> intro x hx <;>
        simp_all +decide [AddSubgroup.mem_zmultiples_iff]
      · simpa only [eq_comm] using hS_eq x hx
      · obtain ⟨k, rfl⟩ := hx; exact by simpa using S.zsmul_mem ha_mem k
    exact Or.inr ⟨sInf {x | 0 < x ∧ x ∈ S}, ha_pos, by
      have hS_eq' := hS_eq
      ext x; simp only [Set.mem_range, SetLike.mem_coe]
      constructor
      · intro hx; rw [hS_eq'] at hx
        obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
        exact ⟨k, by rw [← hk]; simp [zsmul_eq_mul]⟩
      · rintro ⟨n, rfl⟩; show _ ∈ S
        have : n • sInf {x | 0 < x ∧ x ∈ S} = (n : ℝ) * sInf {x | 0 < x ∧ x ∈ S} := by
          simp [zsmul_eq_mul]
        rw [← this]; exact S.zsmul_mem ha_mem n⟩

/-
A closed additive subgroup of ℝ containing 1 is either all of ℝ or (1/d)·ℤ.
-/
lemma closed_addsubgroup_contains_one (S : AddSubgroup ℝ) (hS : IsClosed (S : Set ℝ))
    (h1 : (1 : ℝ) ∈ S) :
    (S : Set ℝ) = Set.univ ∨
    ∃ d : ℕ, 0 < d ∧ (S : Set ℝ) = Set.range (fun n : ℤ => (n : ℝ) / (d : ℝ)) := by
  by_cases h : ∃ x ∈ S, x ≠ 0;
  · have := @closed_addsubgroup_of_real S hS h;
    obtain this | ⟨ a, ha, ha' ⟩ := this;
    · exact Or.inl this;
    · -- Since $1 \in S$, we have $1 = k \cdot a$ for some integer $k$.
      obtain ⟨k, hk⟩ : ∃ k : ℤ, 1 = k * a := by
        exact ha'.subset h1 |> fun ⟨ k, hk ⟩ => ⟨ k, hk.symm ⟩;
      refine Or.inr ⟨ k.natAbs, ?_, ?_ ⟩ <;> norm_num [ ha', abs_of_pos ( show 0 < k from by exact_mod_cast ( by nlinarith : ( 0 :ℝ ) < k ) ) ];
      · rintro rfl; norm_num at hk;
      · grind;
  · grind +locals

/-! ## Hard direction for n = 1 (arbitrary m) -/

/-
The hard direction of Kronecker's theorem for n = 1.
This uses the classification of closed subgroups of ℝ.
-/
theorem kronecker_intrel_implies_approx_n1 (m : ℕ) (α : Fin m → ℝ) (β : ℝ)
    (h_intrel : ∀ r : ℤ,
      (∀ i : Fin m, ∃ z : ℤ, α i * (r : ℝ) = ↑z) →
      ∃ z : ℤ, β * (r : ℝ) = ↑z) :
    ∀ ε : ℝ, ε > 0 →
      ∃ q : Fin m → ℤ, ∃ p : ℤ,
        |∑ i : Fin m, (q i : ℝ) * α i - (p : ℝ) - β| < ε := by
  -- Let $G$ be the additive subgroup of ℝ generated by $\{\alpha_i : i \in \text{Fin } m\} \cup \{1\}$.
  let G := AddSubgroup.closure ({↑1} ∪ Set.range α);
  -- By the properties of the closure of a subgroup, $\beta \in \overline{G}$.
  have h_beta_closure : β ∈ closure (G : Set ℝ) := by
    -- Since $G$ is a closed subgroup of $\mathbb{R}$ containing $1$, by the classification of closed subgroups of $\mathbb{R}$, we have $\overline{G} = \mathbb{R}$ or $\overline{G} = \frac{1}{d}\mathbb{Z}$ for some $d \in \mathbb{N}$.
    have hG_closure : closure (G : Set ℝ) = Set.univ ∨ ∃ d : ℕ, 0 < d ∧ closure (G : Set ℝ) = Set.range (fun n : ℤ => (n : ℝ) / (d : ℝ)) := by
      convert closed_addsubgroup_contains_one ( AddSubgroup.topologicalClosure G ) ( isClosed_closure ) _ using 1;
      exact subset_closure <| AddSubgroup.subset_closure <| Set.mem_union_left _ <| Set.mem_singleton _;
    cases' hG_closure with h h;
    · aesop;
    · obtain ⟨ d, hd₀, hd ⟩ := h;
      -- Since $d·αᵢ ∈ ℤ$ for all $i$, we have $d·β ∈ ℤ$ by the hypothesis $h_intrel$.
      have h_d_beta_int : ∃ z : ℤ, β * d = z := by
        apply h_intrel;
        intro i
        have h_alpha_i : α i ∈ closure (G : Set ℝ) := by
          exact subset_closure <| AddSubgroup.subset_closure <| Set.mem_union_right _ <| Set.mem_range_self _;
        rw [ hd ] at h_alpha_i; obtain ⟨ z, hz ⟩ := h_alpha_i; use z; simp_all +decide [ div_eq_iff, hd₀.ne' ] ;
      exact hd.symm ▸ ⟨ h_d_beta_int.choose, by rw [ div_eq_iff ( by positivity ) ] ; linarith [ h_d_beta_int.choose_spec ] ⟩;
  rw [ Metric.mem_closure_iff ] at h_beta_closure;
  intro ε hε;
  obtain ⟨ b, hb₁, hb₂ ⟩ := h_beta_closure ε hε;
  -- Since $b \in G$, we can write $b = \sum_{i=1}^m q_i \alpha_i + p$ for some integers $q_i$ and $p$.
  obtain ⟨q, p, hq⟩ : ∃ q : Fin m → ℤ, ∃ p : ℤ, b = ∑ i, q i * α i + p := by
    refine' AddSubgroup.closure_induction ( fun x hx => _ ) _ _ _ hb₁;
    · rcases hx with ( rfl | ⟨ i, rfl ⟩ ) <;> [ exact ⟨ 0, 1, by norm_num ⟩ ; exact ⟨ fun j => if j = i then 1 else 0, 0, by simp +decide ⟩ ];
    · exact ⟨ 0, 0, by norm_num ⟩;
    · rintro x y hx hy ⟨ q₁, p₁, rfl ⟩ ⟨ q₂, p₂, rfl ⟩ ; exact ⟨ q₁ + q₂, p₁ + p₂, by simp +decide [ Finset.sum_add_distrib, add_mul, add_assoc, add_left_comm, add_comm ] ⟩ ;
    · rintro x hx ⟨ q, p, rfl ⟩ ; exact ⟨ -q, -p, by simp +decide [ Finset.sum_neg_distrib ] ; ring ⟩ ;
  exact ⟨ q, -p, by rw [ abs_sub_comm ] ; simpa [ hq ] using hb₂ ⟩

-- proved by subagent (see git history)

/-! ## Torus Separation Infrastructure -/

open MeasureTheory
open UnitAddTorus
open MeasureTheory.Measure

variable {d : Type*} [Fintype d]

abbrev T := UnitAddTorus d

/-- A convenient normalized Haar measure on a compact additive group. -/
noncomputable def subgroupUnivPositiveCompact {α : Type*} [AddGroup α] [TopologicalSpace α]
    [ContinuousAdd α] [ContinuousNeg α] [CompactSpace α] [Nonempty α] :
    TopologicalSpace.PositiveCompacts α :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

def torusTranslate (a : UnitAddTorus d) : C(UnitAddTorus d, UnitAddTorus d) :=
  ContinuousMap.id _ + ContinuousMap.const _ a

def avgOverSubgroup (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) : C(UnitAddTorus d, ℂ) :=
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  ∫ h : H, f.comp (torusTranslate (d := d) (h : UnitAddTorus d)) ∂μH

lemma integrable_translateFamily (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) :
    Integrable
      (fun h : H => f.comp (torusTranslate (d := d) (h : UnitAddTorus d)))
      (addHaarMeasure (subgroupUnivPositiveCompact (α := H))) := by
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hcont :
      Continuous (fun h : H =>
        f.comp (torusTranslate (d := d) (h : UnitAddTorus d))) := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    change Continuous (fun z : H × UnitAddTorus d => f (z.2 + (z.1 : UnitAddTorus d)))
    exact f.continuous.comp
      ((continuous_snd).add ((continuous_subtype_val).comp continuous_fst))
  simpa [μH] using
    (hcont.continuousOn.integrableOn_compact (μ := μH) (K := (Set.univ : Set H)) isCompact_univ)

lemma avgOverSubgroup_apply (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) (y : UnitAddTorus d) :
    avgOverSubgroup (d := d) H f y =
      ∫ h : H, f (y + h) ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H))) := by
  rw [avgOverSubgroup, ContinuousMap.integral_apply (integrable_translateFamily (d := d) H f)]
  rfl

lemma avgOverSubgroup_norm_le (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) :
    ‖avgOverSubgroup (d := d) H f‖ ≤ ‖f‖ := by
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hμ : μH Set.univ = 1 := by
    simpa [μH] using
      (addHaarMeasure_self (G := H) (K₀ := subgroupUnivPositiveCompact (α := H)))
  haveI : IsFiniteMeasure μH := ⟨by simp [hμ]⟩
  refine (ContinuousMap.norm_le (f := avgOverSubgroup (d := d) H f) (norm_nonneg _)).2 ?_
  intro y
  rw [avgOverSubgroup_apply]
  have hbound : ∀ᵐ h : H ∂μH, ‖f (y + h)‖ ≤ ‖f‖ := by
    exact Filter.Eventually.of_forall (fun h => f.norm_coe_le_norm (y + h))
  calc
    ‖∫ h : H, f (y + h) ∂μH‖ ≤ ‖f‖ * μH.real Set.univ := by
      exact MeasureTheory.norm_integral_le_of_norm_le_const (μ := μH) hbound
    _ = ‖f‖ := by
      rw [Measure.real_def, hμ, ENNReal.toReal_one, mul_one]

lemma avgOverSubgroup_sub (H : ClosedAddSubgroup (UnitAddTorus d))
    (f g : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H (f - g) =
      avgOverSubgroup (d := d) H f - avgOverSubgroup (d := d) H g := by
  rw [avgOverSubgroup, avgOverSubgroup, avgOverSubgroup]
  have hcomp :
      (fun h : H => (f - g).comp (torusTranslate (d := d) (h : UnitAddTorus d))) =
        fun h : H =>
          f.comp (torusTranslate (d := d) (h : UnitAddTorus d)) -
            g.comp (torusTranslate (d := d) (h : UnitAddTorus d)) := by
    funext h
    ext y
    rfl
  rw [hcomp]
  rw [integral_sub (integrable_translateFamily (d := d) H f)
    (integrable_translateFamily (d := d) H g)]

lemma avgOverSubgroup_add (H : ClosedAddSubgroup (UnitAddTorus d))
    (f g : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H (f + g) =
      avgOverSubgroup (d := d) H f + avgOverSubgroup (d := d) H g := by
  rw [avgOverSubgroup, avgOverSubgroup, avgOverSubgroup]
  have hcomp :
      (fun h : H => (f + g).comp (torusTranslate (d := d) (h : UnitAddTorus d))) =
        fun h : H =>
          f.comp (torusTranslate (d := d) (h : UnitAddTorus d)) +
            g.comp (torusTranslate (d := d) (h : UnitAddTorus d)) := by
    funext h
    ext y
    rfl
  rw [hcomp]
  rw [integral_add (integrable_translateFamily (d := d) H f)
    (integrable_translateFamily (d := d) H g)]

lemma avgOverSubgroup_smul (H : ClosedAddSubgroup (UnitAddTorus d))
    (c : ℂ) (f : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H (c • f) =
      c • avgOverSubgroup (d := d) H f := by
  rw [avgOverSubgroup, avgOverSubgroup]
  have hcomp :
      (fun h : H => (c • f).comp (torusTranslate (d := d) (h : UnitAddTorus d))) =
        fun h : H => c • f.comp (torusTranslate (d := d) (h : UnitAddTorus d)) := by
    funext h
    ext y
    rfl
  rw [hcomp, integral_smul]

lemma avgOverSubgroup_norm_sub_le (H : ClosedAddSubgroup (UnitAddTorus d))
    (f g : C(UnitAddTorus d, ℂ)) :
    ‖avgOverSubgroup (d := d) H f - avgOverSubgroup (d := d) H g‖ ≤ ‖f - g‖ := by
  rw [← avgOverSubgroup_sub (d := d) H f g]
  exact avgOverSubgroup_norm_le (d := d) H (f - g)

lemma avgOverSubgroup_lipschitz (H : ClosedAddSubgroup (UnitAddTorus d)) :
    LipschitzWith 1 (avgOverSubgroup (d := d) H : C(UnitAddTorus d, ℂ) → C(UnitAddTorus d, ℂ)) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro f g
  simpa [dist_eq_norm] using avgOverSubgroup_norm_sub_le (d := d) H f g

lemma avgOverSubgroup_continuous (H : ClosedAddSubgroup (UnitAddTorus d)) :
    Continuous (avgOverSubgroup (d := d) H : C(UnitAddTorus d, ℂ) → C(UnitAddTorus d, ℂ)) :=
  (avgOverSubgroup_lipschitz (d := d) H).continuous

lemma integral_mFourier_eq_zero_of_nontrivial
    (n : d → ℤ) (H : ClosedAddSubgroup (UnitAddTorus d)) (h : H)
    (hh : UnitAddTorus.mFourier n h ≠ 1) :
    ∫ h : H, UnitAddTorus.mFourier n (h : UnitAddTorus d)
      ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H))) = 0 := by
  let μ : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hmul :
      ∀ x : H,
        UnitAddTorus.mFourier n ((x + h : H) : UnitAddTorus d) =
          UnitAddTorus.mFourier n (h : UnitAddTorus d) *
            UnitAddTorus.mFourier n (x : UnitAddTorus d) := by
    intro x
    simp [UnitAddTorus.mFourier, fourier_apply, AddCircle.toCircle_add,
      Finset.prod_mul_distrib, mul_comm]
  have htrans :
      ∫ x : H, UnitAddTorus.mFourier n ((x + h : H) : UnitAddTorus d) ∂μ =
        UnitAddTorus.mFourier n (h : UnitAddTorus d) *
          ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ := by
    calc
      ∫ x : H, UnitAddTorus.mFourier n ((x + h : H) : UnitAddTorus d) ∂μ
          = ∫ x : H, UnitAddTorus.mFourier n (h : UnitAddTorus d) *
              UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ := by
              apply integral_congr_ae
              filter_upwards with x
              rw [hmul x]
      _ = UnitAddTorus.mFourier n (h : UnitAddTorus d) *
            ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ := by
            rw [integral_const_mul]
  have hself :
      ∫ x : H, UnitAddTorus.mFourier n ((x + h : H) : UnitAddTorus d) ∂μ =
        ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ := by
    simpa [μ] using
      (MeasureTheory.integral_add_right_eq_self
        (μ := μ) (f := fun x : H => UnitAddTorus.mFourier n (x : UnitAddTorus d)) h)
  have hEq :
      ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ =
        UnitAddTorus.mFourier n (h : UnitAddTorus d) *
          ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ :=
    hself.symm.trans htrans
  have hzero :
      (1 - UnitAddTorus.mFourier n (h : UnitAddTorus d)) *
        ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ = 0 := by
    have hzero' :
        ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ -
          UnitAddTorus.mFourier n (h : UnitAddTorus d) *
            ∫ x : H, UnitAddTorus.mFourier n (x : UnitAddTorus d) ∂μ = 0 := by
      exact sub_eq_zero.mpr hEq
    simpa [sub_mul] using hzero'
  rcases mul_eq_zero.mp hzero with hbad | hgood
  · exact False.elim <| hh <| (sub_eq_zero.mp hbad).symm
  · exact hgood

def torusAnnihilator (H : ClosedAddSubgroup (UnitAddTorus d)) : Set (d → ℤ) :=
  {n | ∀ h : H, UnitAddTorus.mFourier n (h : UnitAddTorus d) = 1}

lemma avgOverSubgroup_mFourier_of_mem_ann
    (H : ClosedAddSubgroup (UnitAddTorus d)) (n : d → ℤ)
    (hn : n ∈ torusAnnihilator (d := d) H) :
    avgOverSubgroup (d := d) H (UnitAddTorus.mFourier n) = UnitAddTorus.mFourier n := by
  ext y
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hμ : μH Set.univ = 1 := by
    simpa [μH] using
      (addHaarMeasure_self (G := H) (K₀ := subgroupUnivPositiveCompact (α := H)))
  rw [avgOverSubgroup_apply]
  have hmul :
      ∀ h : H,
        UnitAddTorus.mFourier n (y + (h : UnitAddTorus d)) =
          UnitAddTorus.mFourier n y * UnitAddTorus.mFourier n (h : UnitAddTorus d) := by
    intro h
    simp [UnitAddTorus.mFourier, fourier_apply, AddCircle.toCircle_add,
      Finset.prod_mul_distrib]
  have hconst :
      ∀ h : H,
        UnitAddTorus.mFourier n (y + (h : UnitAddTorus d)) =
          UnitAddTorus.mFourier n y := by
    intro h
    rw [hmul h, hn h, mul_one]
  calc
    ∫ h : H, UnitAddTorus.mFourier n (y + (h : UnitAddTorus d)) ∂μH
        = ∫ h : H, UnitAddTorus.mFourier n y ∂μH := by
            apply integral_congr_ae
            filter_upwards with h
            rw [hconst h]
    _ = UnitAddTorus.mFourier n y := by
          rw [integral_const, Measure.real_def, hμ, ENNReal.toReal_one, one_smul]

lemma avgOverSubgroup_mFourier_of_not_mem_ann
    (H : ClosedAddSubgroup (UnitAddTorus d)) (n : d → ℤ)
    (hn : n ∉ torusAnnihilator (d := d) H) :
    avgOverSubgroup (d := d) H (UnitAddTorus.mFourier n) = 0 := by
  ext y
  rw [avgOverSubgroup_apply]
  have hmul :
      ∀ h : H,
        UnitAddTorus.mFourier n (y + (h : UnitAddTorus d)) =
          UnitAddTorus.mFourier n y * UnitAddTorus.mFourier n (h : UnitAddTorus d) := by
    intro h
    simp [UnitAddTorus.mFourier, fourier_apply, AddCircle.toCircle_add,
      Finset.prod_mul_distrib]
  obtain ⟨h, hh⟩ : ∃ h : H, UnitAddTorus.mFourier n (h : UnitAddTorus d) ≠ 1 := by
    by_contra hcontra
    apply hn
    intro h
    by_contra hh
    exact hcontra ⟨h, hh⟩
  calc
    ∫ h' : H, UnitAddTorus.mFourier n (y + (h' : UnitAddTorus d))
        ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H)))
        = ∫ h' : H, UnitAddTorus.mFourier n y *
            UnitAddTorus.mFourier n (h' : UnitAddTorus d)
            ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H))) := by
              apply integral_congr_ae
              filter_upwards with h'
              rw [hmul h']
    _ = UnitAddTorus.mFourier n y *
          ∫ h' : H, UnitAddTorus.mFourier n (h' : UnitAddTorus d)
            ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H))) := by
              rw [integral_const_mul]
    _ = 0 := by
          rw [integral_mFourier_eq_zero_of_nontrivial (d := d) n H h hh, mul_zero]

def annSubmodule (H : ClosedAddSubgroup (UnitAddTorus d)) :
    Submodule ℂ C(UnitAddTorus d, ℂ) :=
  Submodule.span ℂ ((fun n : d → ℤ => UnitAddTorus.mFourier n) '' torusAnnihilator (d := d) H)

lemma avgOverSubgroup_mem_annSubmodule_mFourier
    (H : ClosedAddSubgroup (UnitAddTorus d)) (n : d → ℤ) :
    avgOverSubgroup (d := d) H (UnitAddTorus.mFourier n) ∈ annSubmodule (d := d) H := by
  by_cases hn : n ∈ torusAnnihilator (d := d) H
  · have hmem : UnitAddTorus.mFourier n ∈ annSubmodule (d := d) H := by
      exact Submodule.subset_span ⟨n, hn, rfl⟩
    simpa [avgOverSubgroup_mFourier_of_mem_ann (d := d) H n hn] using hmem
  · rw [avgOverSubgroup_mFourier_of_not_mem_ann (d := d) H n hn]
    exact Submodule.zero_mem (annSubmodule (d := d) H)

lemma avgOverSubgroup_mem_annSubmodule_of_mem_span
    (H : ClosedAddSubgroup (UnitAddTorus d))
    {f : C(UnitAddTorus d, ℂ)}
    (hf : f ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := d)))) :
    avgOverSubgroup (d := d) H f ∈ annSubmodule (d := d) H := by
  let p :
      (g : C(UnitAddTorus d, ℂ)) →
        g ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := d))) → Prop :=
    fun g _ => avgOverSubgroup (d := d) H g ∈ annSubmodule (d := d) H
  change p f hf
  refine Submodule.span_induction (s := Set.range (UnitAddTorus.mFourier (d := d))) (p := p) ?_ ?_ ?_ ?_ hf
  · intro g hg
    rcases hg with ⟨n, rfl⟩
    exact avgOverSubgroup_mem_annSubmodule_mFourier (d := d) H n
  · simp [p, avgOverSubgroup]
  · intro x y hx hy hxmem hymem
    simpa [p, avgOverSubgroup_add (d := d) H x y] using
      (annSubmodule (d := d) H).add_mem hxmem hymem
  · intro c x hx hxmem
    simpa [p, avgOverSubgroup_smul (d := d) H c x] using
      (annSubmodule (d := d) H).smul_mem c hxmem

lemma avgOverSubgroup_mem_closure_annSubmodule
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H f ∈ closure (annSubmodule (d := d) H : Set C(UnitAddTorus d, ℂ)) := by
  have hf :
      f ∈ closure (Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := d))) :
        Set C(UnitAddTorus d, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe,
      UnitAddTorus.span_mFourier_closure_eq_top]
    simp
  refine map_mem_closure (avgOverSubgroup_continuous (d := d) H) hf ?_
  intro g hg
  exact avgOverSubgroup_mem_annSubmodule_of_mem_span (d := d) H hg

def sameValueCLM (x : UnitAddTorus d) : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ x : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ) -
    (ContinuousMap.evalCLM ℂ (0 : UnitAddTorus d) : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ)

def sameValueSubmodule (x : UnitAddTorus d) : Submodule ℂ C(UnitAddTorus d, ℂ) :=
  (sameValueCLM (d := d) x).toLinearMap.ker

omit [Fintype d] in
lemma mem_sameValueSubmodule_iff
    (x : UnitAddTorus d) (f : C(UnitAddTorus d, ℂ)) :
    f ∈ sameValueSubmodule (d := d) x ↔ f x = f 0 := by
  simp [sameValueSubmodule, sameValueCLM, sub_eq_zero]

omit [Fintype d] in
lemma isClosed_sameValueSubmodule (x : UnitAddTorus d) :
    IsClosed (sameValueSubmodule (d := d) x : Set C(UnitAddTorus d, ℂ)) := by
  simpa [sameValueSubmodule] using
    (ContinuousLinearMap.isClosed_ker (sameValueCLM (d := d) x))

lemma annSubmodule_le_sameValueSubmodule
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d)
    (hx : ∀ n ∈ torusAnnihilator (d := d) H, UnitAddTorus.mFourier n x = 1) :
    annSubmodule (d := d) H ≤ sameValueSubmodule (d := d) x := by
  refine Submodule.span_le.2 ?_
  intro f hf
  rcases hf with ⟨n, hn, rfl⟩
  show UnitAddTorus.mFourier n ∈ sameValueSubmodule (d := d) x
  rw [mem_sameValueSubmodule_iff]
  calc
    UnitAddTorus.mFourier n x = 1 := hx n hn
    _ = UnitAddTorus.mFourier n (0 : UnitAddTorus d) := by
      symm
      simp [UnitAddTorus.mFourier]

lemma closure_annSubmodule_le_sameValueSubmodule
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d)
    (hx : ∀ n ∈ torusAnnihilator (d := d) H, UnitAddTorus.mFourier n x = 1) :
    closure (annSubmodule (d := d) H : Set C(UnitAddTorus d, ℂ)) ⊆
      sameValueSubmodule (d := d) x := by
  have hclosure :
      (annSubmodule (d := d) H).topologicalClosure ≤ sameValueSubmodule (d := d) x :=
    Submodule.topologicalClosure_minimal (annSubmodule (d := d) H)
      (annSubmodule_le_sameValueSubmodule (d := d) H x hx)
      (isClosed_sameValueSubmodule (d := d) x)
  simpa [Submodule.topologicalClosure_coe] using hclosure

lemma avgOverSubgroup_eq_at_zero_of_annihilator
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d)
    (hx : ∀ n ∈ torusAnnihilator (d := d) H, UnitAddTorus.mFourier n x = 1)
    (f : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H f x = avgOverSubgroup (d := d) H f 0 := by
  have havg_closure :=
    avgOverSubgroup_mem_closure_annSubmodule (d := d) H f
  have havg_same :
      avgOverSubgroup (d := d) H f ∈ sameValueSubmodule (d := d) x :=
    closure_annSubmodule_le_sameValueSubmodule (d := d) H x hx havg_closure
  exact (mem_sameValueSubmodule_iff (d := d) x _).mp havg_same

def xPlusH (H : ClosedAddSubgroup (UnitAddTorus d)) (x : UnitAddTorus d) :
    Set (UnitAddTorus d) :=
  Set.range fun h : H => x + (h : UnitAddTorus d)

omit [Fintype d] in
lemma isCompact_xPlusH
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d) :
    IsCompact (xPlusH (d := d) H x) := by
  simpa [xPlusH] using
    (isCompact_range
      (continuous_const.add continuous_subtype_val :
        Continuous fun h : H => x + (h : UnitAddTorus d)))

omit [Fintype d] in
lemma disjoint_xPlusH
    (H : ClosedAddSubgroup (UnitAddTorus d))
    {x : UnitAddTorus d}
    (hx : x ∉ H) :
    Disjoint (xPlusH (d := d) H x) (H : Set (UnitAddTorus d)) := by
  refine Set.disjoint_left.2 ?_
  intro y hyx hyH
  rcases hyx with ⟨h, rfl⟩
  exact hx <| by
    simpa using H.sub_mem hyH h.2

lemma subgroup_univ_measure
    (H : ClosedAddSubgroup (UnitAddTorus d)) :
    (addHaarMeasure (subgroupUnivPositiveCompact (α := H))) Set.univ = 1 := by
  simpa using
    (addHaarMeasure_self (G := H) (K₀ := subgroupUnivPositiveCompact (α := H)))

lemma integral_const_subgroup
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (c : ℂ) :
    (∫ _h : H, c ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H)))) = c := by
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hμ : μH Set.univ = 1 := by
    simpa [μH] using subgroup_univ_measure (d := d) H
  haveI : IsFiniteMeasure μH := ⟨by simp [hμ]⟩
  rw [integral_const, Measure.real_def, hμ, ENNReal.toReal_one, one_smul]

def ofRealContinuousMap (f : C(UnitAddTorus d, ℝ)) : C(UnitAddTorus d, ℂ) where
  toFun y := (f y : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous

lemma avgOverSubgroup_zero_at_zero
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ))
    (hf : Set.EqOn f (fun _ => 0) (H : Set (UnitAddTorus d))) :
    avgOverSubgroup (d := d) H f 0 = 0 := by
  rw [avgOverSubgroup_apply]
  have hconst : (fun h : H => f (0 + (h : UnitAddTorus d))) = fun _ : H => 0 := by
    funext h
    simpa using hf (x := (h : UnitAddTorus d)) h.2
  rw [hconst, integral_zero]

lemma avgOverSubgroup_one_at_x
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (x : UnitAddTorus d)
    (f : C(UnitAddTorus d, ℂ))
    (hf : Set.EqOn f (fun _ => 1) (xPlusH (d := d) H x)) :
    avgOverSubgroup (d := d) H f x = 1 := by
  rw [avgOverSubgroup_apply]
  have hconst : (fun h : H => f (x + (h : UnitAddTorus d))) = fun _ : H => 1 := by
    funext h
    exact hf (x := x + (h : UnitAddTorus d)) ⟨h, rfl⟩
  rw [hconst]
  exact integral_const_subgroup (d := d) H 1

theorem mem_of_mFourier_eq_one_on_annihilator
    (H : ClosedAddSubgroup (UnitAddTorus d))
    {x : UnitAddTorus d}
    (hx : ∀ n ∈ torusAnnihilator (d := d) H, UnitAddTorus.mFourier n x = 1) :
    x ∈ H := by
  by_contra hxnot
  obtain ⟨fR, hfR0, hfR1, _⟩ :=
    exists_continuous_zero_one_of_isCompact'
      (isCompact_xPlusH (d := d) H x) H.isClosed'
      (disjoint_xPlusH (d := d) H hxnot)
  let f : C(UnitAddTorus d, ℂ) := ofRealContinuousMap (d := d) fR
  have hf0 : Set.EqOn f (fun _ => 0) (H : Set (UnitAddTorus d)) := by
    intro y hy
    change ((fR y : ℂ) = 0)
    simpa [f] using hfR0 (x := y) hy
  have hf1 : Set.EqOn f (fun _ => 1) (xPlusH (d := d) H x) := by
    intro y hy
    change ((fR y : ℂ) = 1)
    simpa [f] using hfR1 (x := y) hy
  have h_eq :
      avgOverSubgroup (d := d) H f x = avgOverSubgroup (d := d) H f 0 :=
    avgOverSubgroup_eq_at_zero_of_annihilator (d := d) H x hx f
  have h0 : avgOverSubgroup (d := d) H f 0 = 0 :=
    avgOverSubgroup_zero_at_zero (d := d) H f hf0
  have h1 : avgOverSubgroup (d := d) H f x = 1 :=
    avgOverSubgroup_one_at_x (d := d) H x f hf1
  have : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = avgOverSubgroup (d := d) H f x := by simpa using h1.symm
      _ = avgOverSubgroup (d := d) H f 0 := h_eq
      _ = 0 := h0
  exact one_ne_zero this

lemma mFourier_eq_one_iff_exists_int
    (n : ℕ) (r : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier r (fun j => ((x j : ℝ) : AddCircle (1 : ℝ))) = 1 ↔
      ∃ z : ℤ, (∑ j, x j * (r j : ℝ)) = z := by
  have hmfourier :
      UnitAddTorus.mFourier r (fun j => ((x j : ℝ) : AddCircle (1 : ℝ))) =
        Complex.exp (2 * Real.pi * Complex.I * (∑ j, x j * (r j : ℝ))) := by
    calc
      UnitAddTorus.mFourier r (fun j => ((x j : ℝ) : AddCircle (1 : ℝ))) =
          ∏ j, Complex.exp (2 * Real.pi * Complex.I * ((r j : ℝ) * x j)) := by
            simp [UnitAddTorus.mFourier, mul_assoc, mul_left_comm, mul_comm]
      _ = Complex.exp (∑ j, 2 * Real.pi * Complex.I * ((r j : ℝ) * x j)) := by
            rw [← Complex.exp_sum]
      _ = Complex.exp (2 * Real.pi * Complex.I * (∑ j, x j * (r j : ℝ))) := by
            congr 1
            rw [show ((↑(∑ j, x j * (r j : ℝ)) : ℝ) : ℂ) =
                ∑ j, (((x j * (r j : ℝ)) : ℝ) : ℂ) by
                  simp]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm]
  rw [hmfourier]
  constructor
  · intro h
    rw [Complex.exp_eq_one_iff] at h
    rcases h with ⟨m, hm⟩
    use m
    have him := congrArg Complex.im hm
    simp at him
    nlinarith [Real.pi_pos]
  · rintro ⟨z, hz⟩
    rw [hz]
    rw [Complex.exp_eq_one_iff]
    refine ⟨z, ?_⟩
    simp [mul_left_comm, mul_comm]

/-- A BM-facing specialization of Kronecker's hard direction: one common denominator for many
target coordinates. The nonzero-denominator normalization is deferred to the BM application. -/
theorem kronecker_intrel_implies_approx_common_q_int
    (n : ℕ) (α β : Fin n → ℝ)
    (h_intrel : ∀ r : Fin n → ℤ,
      (∃ z : ℤ, ∑ j, α j * (r j : ℝ) = z) →
      ∃ z : ℤ, ∑ j, β j * (r j : ℝ) = z) :
    ∀ ε > 0, ∃ q : ℤ, ∃ p : Fin n → ℤ,
      ∀ j, |(q : ℝ) * α j - (p j : ℝ) - β j| < ε := by
  intro ε hε
  let αbar : UnitAddTorus (Fin n) := fun j => ((α j : ℝ) : AddCircle (1 : ℝ))
  let βbar : UnitAddTorus (Fin n) := fun j => ((β j : ℝ) : AddCircle (1 : ℝ))
  let Z : AddSubgroup (UnitAddTorus (Fin n)) := AddSubgroup.zmultiples αbar
  let H : ClosedAddSubgroup (UnitAddTorus (Fin n)) :=
    ⟨Z.topologicalClosure, AddSubgroup.isClosed_topologicalClosure Z⟩
  have hα_mem : αbar ∈ H := by
    change αbar ∈ Z.topologicalClosure
    exact AddSubgroup.le_topologicalClosure Z <|
      by
        change αbar ∈ AddSubgroup.zmultiples αbar
        convert AddSubgroup.zsmul_mem_zmultiples αbar (1 : ℤ) using 1
        simp
  have hβ_mem : βbar ∈ H := by
    apply mem_of_mFourier_eq_one_on_annihilator (H := H)
    intro r hr
    have hα_fourier : UnitAddTorus.mFourier r αbar = 1 := by
      exact hr ⟨αbar, hα_mem⟩
    have hα_int : ∃ z : ℤ, (∑ j, α j * (r j : ℝ)) = z := by
      exact (mFourier_eq_one_iff_exists_int n r α).mp hα_fourier
    have hβ_int := h_intrel r hα_int
    exact (mFourier_eq_one_iff_exists_int n r β).mpr hβ_int
  have hβ_closure : βbar ∈ closure (Z : Set (UnitAddTorus (Fin n))) := by
    simpa [H, Z, AddSubgroup.topologicalClosure_coe] using hβ_mem
  rw [Metric.mem_closure_iff] at hβ_closure
  obtain ⟨x, hxS, hxdist⟩ := hβ_closure ε hε
  obtain ⟨q, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hxS
  refine ⟨q, fun j => round ((q : ℝ) * α j - β j), ?_⟩
  intro j
  have hcoord :
      dist (((q • αbar) : UnitAddTorus (Fin n)) j) (βbar j) < ε := by
    simpa [dist_comm] using (dist_pi_lt_iff hε).mp hxdist j
  have hnorm :
      ‖((((q : ℝ) * α j - β j : ℝ) : AddCircle (1 : ℝ)))‖ < ε := by
    simpa [dist_eq_norm, αbar, βbar, zsmul_eq_mul, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using hcoord
  have hround :
      |((q : ℝ) * α j - β j) - round ((q : ℝ) * α j - β j)| < ε := by
    have := hnorm
    rw [AddCircle.norm_eq] at this
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hround

end

-- ============================================================
-- RequestProject_BMCore
-- ============================================================

open Chebyshev
open MeasureTheory Set
open scoped Asymptotics BigOperators Chebyshev ENNReal

noncomputable section

/-- `I_∞ = [16/25, 2/3]`, the interval on which the covering property fails. -/
def I_inf : Set ℝ := Icc (16/25 : ℝ) (2/3)

abbrev PrimeIdx (k : ℕ) := Fin (2 ^ k)

abbrev IntIdx (ν : ℕ) := Fin (2 ^ (ν - 2) + 1)

abbrev BMIdx (k ν : ℕ) := PrimeIdx k ⊕ IntIdx ν

/-- The BM integer block is the full interval of consecutive integers
`[7 * 2^(ν-3), 9 * 2^(ν-3)]`. -/
def bmIntVal (ν : ℕ) (j : IntIdx ν) : ℕ :=
  7 * 2 ^ (ν - 3) + j.1

/-- Positive part of an integer coefficient, viewed as a natural-number exponent. -/
abbrev zpos (z : ℤ) : ℕ := Int.toNat z

/-- Negative part of an integer coefficient, viewed as a natural-number exponent. -/
abbrev zneg (z : ℤ) : ℕ := Int.toNat (-z)

lemma zpos_sub_zneg (z : ℤ) : (zpos z : ℤ) - zneg z = z := by
  simp [zpos, zneg]

lemma cast_zpos_sub_zneg (z : ℤ) : (zpos z : ℝ) - zneg z = z := by
  exact_mod_cast zpos_sub_zneg z

lemma zpos_eq_zero_of_nonpos {z : ℤ} (hz : z ≤ 0) : zpos z = 0 := by
  simp [zpos, Int.toNat_of_nonpos hz]

lemma zneg_eq_zero_of_nonneg {z : ℤ} (hz : 0 ≤ z) : zneg z = 0 := by
  simp [zneg, Int.toNat_of_nonpos (neg_nonpos.mpr hz)]

lemma zpos_pos_of_pos {z : ℤ} (hz : 0 < z) : 0 < zpos z := by
  have hz' : (0 : ℤ) < z.toNat := by
    rw [Int.toNat_of_nonneg hz.le]
    exact hz
  exact_mod_cast hz'

lemma zneg_pos_of_neg {z : ℤ} (hz : z < 0) : 0 < zneg z := by
  have hneg : 0 < -z := by simpa using neg_pos.mpr hz
  have hneg' : (0 : ℤ) < (-z).toNat := by
    rw [Int.toNat_of_nonneg hneg.le]
    exact hneg
  simpa [zneg] using hneg'

lemma logb_nat_finset_prod_pow
    {α : Type*} (s : Finset α) (f : α → ℕ) (e : α → ℕ)
    (hf : ∀ a ∈ s, f a ≠ 0) :
    Real.logb 2 ((∏ a ∈ s, f a ^ e a : ℕ) : ℝ) =
      ∑ a ∈ s, (e a : ℝ) * Real.logb 2 (f a : ℝ) := by
  have hpow_ne :
      ∀ a ∈ s, (((f a) ^ e a : ℕ) : ℝ) ≠ 0 := by
    intro a ha
    exact_mod_cast pow_ne_zero _ (hf a ha)
  rw [Nat.cast_prod, Real.logb_prod]
  · simp_rw [Nat.cast_pow, Real.logb_pow]
  · simpa using hpow_ne

lemma logb_nat_fintype_prod_pow
    {α : Type*} [Fintype α] (f : α → ℕ) (e : α → ℕ)
    (hf : ∀ a, f a ≠ 0) :
    Real.logb 2 ((∏ a, f a ^ e a : ℕ) : ℝ) =
      ∑ a, (e a : ℝ) * Real.logb 2 (f a : ℝ) := by
  simpa using logb_nat_finset_prod_pow Finset.univ f e (fun a _ => hf a)

lemma logb_nat_fintype_prod_zparts
    {α : Type*} [Fintype α] (f : α → ℕ) (r : α → ℤ)
    (hf : ∀ a, f a ≠ 0) :
    Real.logb 2 ((∏ a, f a ^ zpos (r a) : ℕ) : ℝ) -
        Real.logb 2 ((∏ a, f a ^ zneg (r a) : ℕ) : ℝ) =
      ∑ a, (r a : ℝ) * Real.logb 2 (f a : ℝ) := by
  rw [logb_nat_fintype_prod_pow f (fun a => zpos (r a)) hf,
    logb_nat_fintype_prod_pow f (fun a => zneg (r a)) hf]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a ha
  have hz : (zpos (r a) : ℝ) - zneg (r a) = r a := cast_zpos_sub_zneg (r a)
  calc
    (zpos (r a) : ℝ) * Real.logb 2 (f a : ℝ) -
        (zneg (r a) : ℝ) * Real.logb 2 (f a : ℝ)
      = ((zpos (r a) : ℝ) - zneg (r a)) * Real.logb 2 (f a : ℝ) := by ring
    _ = (r a : ℝ) * Real.logb 2 (f a : ℝ) := by rw [hz]

lemma logb_nat_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.logb 2 ((a * b : ℕ) : ℝ) = Real.logb 2 (a : ℝ) + Real.logb 2 (b : ℝ) := by
  rw [Nat.cast_mul, Real.logb_mul]
  · exact_mod_cast ha
  · exact_mod_cast hb

lemma bm_lower_endpoint (ν : ℕ) (hν : 3 ≤ ν) :
    ((7 : ℝ) / 8) * 2 ^ ν = 7 * 2 ^ (ν - 3) := by
  have hsplit : ν = (ν - 3) + 3 := by omega
  rw [hsplit, pow_add]
  norm_num
  ring

lemma bm_upper_endpoint (ν : ℕ) (hν : 3 ≤ ν) :
    ((9 : ℝ) / 8) * 2 ^ ν = 9 * 2 ^ (ν - 3) := by
  have hsplit : ν = (ν - 3) + 3 := by omega
  rw [hsplit, pow_add]
  norm_num
  ring

lemma bmIntVal_mem_Icc (ν : ℕ) (hν : 3 ≤ ν) (j : IntIdx ν) :
    (bmIntVal ν j : ℝ) ∈
      Icc (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν) := by
  constructor
  · rw [bm_lower_endpoint ν hν]
    exact_mod_cast Nat.le_add_right _ _
  · rw [bm_upper_endpoint ν hν]
    have hj : j.1 ≤ 2 ^ (ν - 2) := Nat.lt_succ_iff.mp j.2
    have hpow : (2 : ℝ) ^ (ν - 2) = (2 : ℝ) ^ (ν - 3) * 2 := by
      have hsplit : ν - 2 = (ν - 3) + 1 := by omega
      rw [hsplit, pow_add]
      norm_num
    calc
      (bmIntVal ν j : ℝ) = 7 * 2 ^ (ν - 3) + j.1 := by
        simp [bmIntVal, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      _ ≤ 7 * 2 ^ (ν - 3) + 2 ^ (ν - 2) := by
        gcongr
        exact_mod_cast hj
      _ = 9 * 2 ^ (ν - 3) := by
        rw [hpow]
        ring

/-- Every integer in the open BM integer window occurs in the enumerated integer block. -/
lemma exists_bmIntVal_eq_of_mem_Ioo (ν : ℕ) (hν : 3 ≤ ν) {n : ℕ}
    (hn : (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν)) :
    ∃ j : IntIdx ν, bmIntVal ν j = n := by
  rw [bm_lower_endpoint ν hν, bm_upper_endpoint ν hν] at hn
  have hlow : 7 * 2 ^ (ν - 3) < n := by exact_mod_cast hn.1
  have hhigh : n < 9 * 2 ^ (ν - 3) := by exact_mod_cast hn.2
  refine ⟨⟨n - 7 * 2 ^ (ν - 3), ?_⟩, ?_⟩
  · have hpow : 2 ^ (ν - 2) = 2 ^ (ν - 3) * 2 := by
      have hsplit : ν - 2 = (ν - 3) + 1 := by omega
      rw [hsplit, pow_add]
      norm_num
    omega
  · simp [bmIntVal, Nat.add_sub_of_le (Nat.le_of_lt hlow)]

/-- Left endpoint of the `j`-th BM prime interval. -/
def bmPrimeLeft (k ν : ℕ) (j : PrimeIdx k) : ℝ :=
  (((23 : ℝ) / 16) + (j : ℝ) / (2 : ℝ) ^ (k + 5)) * (2 : ℝ) ^ ν

/-- Right endpoint of the `j`-th BM prime interval. -/
def bmPrimeRight (k ν : ℕ) (j : PrimeIdx k) : ℝ :=
  (((23 : ℝ) / 16) + ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5)) * (2 : ℝ) ^ ν

lemma bmPrimeLeft_lt_right (k ν : ℕ) (j : PrimeIdx k) :
    bmPrimeLeft k ν j < bmPrimeRight k ν j := by
  unfold bmPrimeLeft bmPrimeRight
  have hpow : 0 < (2 : ℝ) ^ ν := by positivity
  have hinner : (j : ℝ) / (2 : ℝ) ^ (k + 5) < ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) := by
    have hden : ((2 : ℝ) ^ (k + 5)) ≠ 0 := by positivity
    field_simp [hden]
    linarith
  have hinner' :
      (23 / 16 : ℝ) + (j : ℝ) / (2 : ℝ) ^ (k + 5) <
        (23 / 16 : ℝ) + ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) := by
    linarith
  exact mul_lt_mul_of_pos_right hinner' hpow

lemma bmPrimeLeft_lower_mem (k ν : ℕ) (j : PrimeIdx k) :
    ((23 : ℝ) / 16) * (2 : ℝ) ^ ν ≤ bmPrimeLeft k ν j := by
  unfold bmPrimeLeft
  have hpow : 0 ≤ (2 : ℝ) ^ ν := by positivity
  have hfrac : 0 ≤ (j : ℝ) / (2 : ℝ) ^ (k + 5) := by positivity
  nlinarith

lemma bmPrimeRight_lt_upper (k ν : ℕ) (j : PrimeIdx k) :
    bmPrimeRight k ν j < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν := by
  unfold bmPrimeRight
  have hpow : 0 < (2 : ℝ) ^ ν := by positivity
  have hval : ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) ≤ (1 : ℝ) / 32 := by
    have hj_nat : j.1 + 1 ≤ 2 ^ k := Nat.succ_le_of_lt j.2
    have hj_cast : (j : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
      exact_mod_cast hj_nat
    have hmul : (2 : ℝ) ^ (k + 5) = (2 : ℝ) ^ k * 32 := by
      rw [pow_add]
      norm_num
    rw [hmul]
    have hkpow : ((2 : ℝ) ^ k) ≠ 0 := by positivity
    have htmp :
        ((j : ℝ) + 1) / ((2 : ℝ) ^ k * 32) ≤
          ((2 : ℝ) ^ k) / ((2 : ℝ) ^ k * 32) := by
      field_simp [hkpow]
      nlinarith
    have hcancel : ((2 : ℝ) ^ k) / ((2 : ℝ) ^ k * 32) = (1 : ℝ) / 32 := by
      field_simp [hkpow]
    simpa [hcancel] using htmp
  have hinner : ((23 : ℝ) / 16) + (((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5)) < (3 : ℝ) / 2 := by
    nlinarith
  nlinarith

lemma bmPrimeRight_le_bmPrimeLeft_of_lt {k ν : ℕ} {i j : PrimeIdx k} (hij : i < j) :
    bmPrimeRight k ν i ≤ bmPrimeLeft k ν j := by
  unfold bmPrimeRight bmPrimeLeft
  have hpow : 0 ≤ (2 : ℝ) ^ ν := by positivity
  have hij_nat : i.1 + 1 ≤ j.1 := Nat.succ_le_of_lt hij
  have hij_cast : (i : ℝ) + 1 ≤ (j : ℝ) := by
    exact_mod_cast hij_nat
  have hfrac :
      ((i : ℝ) + 1) / (2 : ℝ) ^ (k + 5) ≤ (j : ℝ) / (2 : ℝ) ^ (k + 5) := by
    have hden : ((2 : ℝ) ^ (k + 5)) ≠ 0 := by positivity
    field_simp [hden]
    nlinarith
  nlinarith

lemma eventually_theta_increment_pos_mul_pow
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 < b) (hgap : ε * (a + b) < b - a) (hε : 0 < ε) :
    ∀ᶠ ν : ℕ in Filter.atTop, θ (b * (2 : ℝ) ^ ν) - θ (a * (2 : ℝ) ^ ν) > 0 := by
  have hpow : Filter.Tendsto (fun ν : ℕ ↦ (2 : ℝ) ^ ν) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hta : Filter.Tendsto (fun ν : ℕ ↦ a * (2 : ℝ) ^ ν) Filter.atTop Filter.atTop :=
    hpow.const_mul_atTop ha
  have htb : Filter.Tendsto (fun ν : ℕ ↦ b * (2 : ℝ) ^ ν) Filter.atTop Filter.atTop :=
    hpow.const_mul_atTop hb
  have hLittle : (θ - id) =o[Filter.atTop] id := chebyshev_asymptotic.isLittleO
  have hA :
      ∀ᶠ ν : ℕ in Filter.atTop,
        ‖(θ (a * (2 : ℝ) ^ ν) - a * (2 : ℝ) ^ ν)‖ ≤ ε * ‖a * (2 : ℝ) ^ ν‖ := by
    simpa [sub_eq_add_neg, Function.comp_def] using (hLittle.comp_tendsto hta).def hε
  have hB :
      ∀ᶠ ν : ℕ in Filter.atTop,
        ‖(θ (b * (2 : ℝ) ^ ν) - b * (2 : ℝ) ^ ν)‖ ≤ ε * ‖b * (2 : ℝ) ^ ν‖ := by
    simpa [sub_eq_add_neg, Function.comp_def] using (hLittle.comp_tendsto htb).def hε
  filter_upwards [hA, hB] with ν hAν hBν
  have hpow_pos : 0 < (2 : ℝ) ^ ν := by positivity
  have haν_pos : 0 < a * (2 : ℝ) ^ ν := mul_pos ha hpow_pos
  have hbν_pos : 0 < b * (2 : ℝ) ^ ν := mul_pos hb hpow_pos
  have hAν' := abs_le.mp hAν
  have hBν' := abs_le.mp hBν
  have hA_upper : θ (a * (2 : ℝ) ^ ν) ≤ a * (2 : ℝ) ^ ν + ε * (a * (2 : ℝ) ^ ν) := by
    rw [Real.norm_eq_abs, abs_of_pos haν_pos] at hAν'
    linarith
  have hB_lower : b * (2 : ℝ) ^ ν - ε * (b * (2 : ℝ) ^ ν) ≤ θ (b * (2 : ℝ) ^ ν) := by
    rw [Real.norm_eq_abs, abs_of_pos hbν_pos] at hBν'
    linarith
  have hgapν : (ε * (a + b)) * (2 : ℝ) ^ ν < (b - a) * (2 : ℝ) ^ ν := by
    gcongr
  nlinarith

/-- BM prime supply: for large dyadic scales, there are `2^k` distinct primes in the BM window. -/
theorem bm_many_primes (k : ℕ) :
    ∃ N, ∀ ν ≥ N,
      ∃ p : PrimeIdx k → ℕ,
        Pairwise (fun i j => p i ≠ p j) ∧
        (∀ i, Nat.Prime (p i)) ∧
        (∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
              (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν) := by
  let a : PrimeIdx k → ℝ := fun j => (23 : ℝ) / 16 + (j : ℝ) / (2 : ℝ) ^ (k + 5)
  let b : PrimeIdx k → ℝ := fun j => (23 : ℝ) / 16 + ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5)
  have h_event :
      ∀ᶠ ν : ℕ in Filter.atTop,
        ∀ j : PrimeIdx k, θ (b j * (2 : ℝ) ^ ν) - θ (a j * (2 : ℝ) ^ ν) > 0 := by
    rw [Filter.eventually_all]
    intro j
    have ha_pos : 0 < a j := by
      dsimp [a]
      positivity
    have hb_pos : 0 < b j := by
      dsimp [b]
      positivity
    have hgap :
        ((1 : ℝ) / (2 : ℝ) ^ (k + 8)) * (a j + b j) < b j - a j := by
      have hsum : a j + b j < 3 := by
        dsimp [a, b]
        have hval : ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) ≤ (1 : ℝ) / 32 := by
          have hj_nat : j.1 + 1 ≤ 2 ^ k := Nat.succ_le_of_lt j.2
          have hj_cast : (j : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
            exact_mod_cast hj_nat
          have hmul : (2 : ℝ) ^ (k + 5) = (2 : ℝ) ^ k * 32 := by
            rw [pow_add]
            norm_num
          rw [hmul]
          have hkpow : ((2 : ℝ) ^ k) ≠ 0 := by positivity
          field_simp [hkpow]
          nlinarith [hj_cast]
        have hval' : (j : ℝ) / (2 : ℝ) ^ (k + 5) ≤ (1 : ℝ) / 32 := by
          have hj_le : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
          have hfrac :
              (j : ℝ) / (2 : ℝ) ^ (k + 5) ≤ ((j : ℝ) + 1) / (2 : ℝ) ^ (k + 5) := by
            gcongr
          exact le_trans hfrac hval
        nlinarith [hval, hval']
      have hdiff : b j - a j = (1 : ℝ) / (2 : ℝ) ^ (k + 5) := by
        dsimp [a, b]
        ring_nf
      rw [hdiff]
      have hkpow8 : 0 < (2 : ℝ) ^ (k + 8) := by positivity
      have hmul :
          ((1 : ℝ) / (2 : ℝ) ^ (k + 8)) * (a j + b j) <
            ((1 : ℝ) / (2 : ℝ) ^ (k + 8)) * 3 := by
        gcongr
      have htarget :
          ((1 : ℝ) / (2 : ℝ) ^ (k + 8)) * 3 < (1 : ℝ) / (2 : ℝ) ^ (k + 5) := by
        have hpow5 : 0 < (2 : ℝ) ^ (k + 5) := by positivity
        field_simp [hkpow8.ne', hpow5.ne']
        have hpow_split : (2 : ℝ) ^ (k + 8) = 8 * (2 : ℝ) ^ (k + 5) := by
          rw [pow_add]
          ring_nf
        nlinarith [hpow_split, hpow5]
      exact lt_trans hmul htarget
    have hε : 0 < (1 : ℝ) / (2 : ℝ) ^ (k + 8) := by positivity
    simpa [a, b] using
      eventually_theta_increment_pos_mul_pow
        (a := a j) (b := b j) (ε := (1 : ℝ) / (2 : ℝ) ^ (k + 8))
        ha_pos hb_pos hgap hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h_event
  refine ⟨N, fun ν hν => ?_⟩
  have hν_all := hN ν hν
  have hPrimeExists :
      ∀ j : PrimeIdx k, ∃ p : ℕ, Nat.Prime p ∧
        bmPrimeLeft k ν j < (p : ℝ) ∧ (p : ℝ) ≤ bmPrimeRight k ν j := by
    intro j
    have hleft_lt_right : bmPrimeLeft k ν j < bmPrimeRight k ν j :=
      bmPrimeLeft_lt_right k ν j
    have htheta :
        θ (bmPrimeRight k ν j) - θ (bmPrimeLeft k ν j) > 0 := by
      simpa [bmPrimeLeft, bmPrimeRight] using hν_all j
    simpa [HasPrimeInInterval, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      theta_pos_implies_prime_in_interval hleft_lt_right htheta
  choose p hpPrime hpLower hpUpper using hPrimeExists
  refine ⟨p, ?_, hpPrime, ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij' | hij'
    · have hsep : bmPrimeRight k ν i ≤ bmPrimeLeft k ν j :=
        bmPrimeRight_le_bmPrimeLeft_of_lt hij'
      have hlt : (p i : ℝ) < p j := by
        exact lt_of_le_of_lt ((hpUpper i).trans hsep) (hpLower j)
      exact fun hEq => by
        exact (ne_of_lt hlt) (by exact_mod_cast hEq)
    · have hsep : bmPrimeRight k ν j ≤ bmPrimeLeft k ν i :=
        bmPrimeRight_le_bmPrimeLeft_of_lt hij'
      have hlt : (p j : ℝ) < p i := by
        exact lt_of_le_of_lt ((hpUpper j).trans hsep) (hpLower i)
      exact fun hEq => by
        exact (ne_of_gt hlt) (by exact_mod_cast hEq)
  · intro j
    constructor
    · exact lt_of_le_of_lt (bmPrimeLeft_lower_mem k ν j) (hpLower j)
    · exact lt_of_le_of_lt (hpUpper j) (bmPrimeRight_lt_upper k ν j)

/-- BM frequency vector on the prime-plus-integer block. -/
def bmAlpha {k ν : ℕ} (p : PrimeIdx k → ℕ) : BMIdx k ν → ℝ
  | Sum.inl i => Real.logb 2 (p i)
  | Sum.inr j => Real.logb 2 (bmIntVal ν j)

/-- BM target vector on the prime-plus-integer block. -/
def bmBeta (k ν : ℕ) : BMIdx k ν → ℝ
  | Sum.inl i => (i : ℝ) / (2 : ℝ) ^ k
  | Sum.inr _ => 0

/-- Flatten the BM sum index to a single `Fin` index for the Kronecker theorem. -/
abbrev bmFlatEquiv (k ν : ℕ) :
    BMIdx k ν ≃ Fin (2 ^ k + (2 ^ (ν - 2) + 1)) :=
  finSumFinEquiv

def bmFlatAlpha {k ν : ℕ} (p : PrimeIdx k → ℕ) :
    Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℝ :=
  bmAlpha p ∘ (bmFlatEquiv k ν).symm

def bmFlatBeta (k ν : ℕ) :
    Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℝ :=
  bmBeta k ν ∘ (bmFlatEquiv k ν).symm

lemma bmFlatAlpha_castAdd {k ν : ℕ} (p : PrimeIdx k → ℕ) (i : PrimeIdx k) :
    bmFlatAlpha p (Fin.castAdd (2 ^ (ν - 2) + 1) i) = Real.logb 2 (p i) := by
  simp [bmFlatAlpha, bmAlpha, bmFlatEquiv]

lemma bmFlatAlpha_natAdd {k ν : ℕ} (p : PrimeIdx k → ℕ) (j : IntIdx ν) :
    bmFlatAlpha p (Fin.natAdd (2 ^ k) j) = Real.logb 2 (bmIntVal ν j) := by
  simp [bmFlatAlpha, bmAlpha, bmFlatEquiv]

lemma bmFlatBeta_castAdd {k ν : ℕ} (i : PrimeIdx k) :
    bmFlatBeta k ν (Fin.castAdd (2 ^ (ν - 2) + 1) i) = (i : ℝ) / (2 : ℝ) ^ k := by
  simp [bmFlatBeta, bmBeta, bmFlatEquiv]

lemma bmFlatBeta_natAdd {k ν : ℕ} (j : IntIdx ν) :
    bmFlatBeta k ν (Fin.natAdd (2 ^ k) j) = 0 := by
  simp [bmFlatBeta, bmBeta, bmFlatEquiv]

/-- The first nontrivial prime-grid index, available once `k ≥ 1`. -/
def bmPrimeIdxOne (k : ℕ) (hk : 1 ≤ k) : PrimeIdx k :=
  ⟨1, by
    have hpow : (2 : ℕ) ≤ 2 ^ k := by
      simpa using pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by decide) hk
    omega⟩

lemma bmBeta_primeIdxOne_eq (k ν : ℕ) (hk : 1 ≤ k) :
    bmBeta k ν (Sum.inl (bmPrimeIdxOne k hk)) = 1 / (2 : ℝ) ^ k := by
  simp [bmBeta, bmPrimeIdxOne]

lemma bmFlatBeta_primeIdxOne_eq (k ν : ℕ) (hk : 1 ≤ k) :
    bmFlatBeta k ν
        (Fin.castAdd (2 ^ (ν - 2) + 1) (bmPrimeIdxOne k hk)) =
      1 / (2 : ℝ) ^ k := by
  simpa [bmFlatBeta, bmBeta, bmFlatEquiv] using bmBeta_primeIdxOne_eq k ν hk

lemma prime_not_dvd_pow_of_not_dvd {p a e : ℕ} (hp : Nat.Prime p) (hnot : ¬ p ∣ a) :
    ¬ p ∣ a ^ e := by
  intro h
  exact hnot (hp.dvd_of_dvd_pow h)

lemma bmIntVal_pos (ν : ℕ) (_hν : 3 ≤ ν) (j : IntIdx ν) : 0 < bmIntVal ν j := by
  have hbase : 0 < 7 * 2 ^ (ν - 3) := by
    have hpow : 0 < 2 ^ (ν - 3) := pow_pos (by omega) _
    omega
  exact lt_of_lt_of_le hbase (Nat.le_add_right _ _)

lemma bm_prime_gt_bmIntVal
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (i : PrimeIdx k) (j : IntIdx ν) :
    bmIntVal ν j < p i := by
  have hj_upper : (bmIntVal ν j : ℝ) ≤ ((9 : ℝ) / 8) * (2 : ℝ) ^ ν :=
    (bmIntVal_mem_Icc ν hν j).2
  have hp_lower : ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) := (hp_window i).1
  have hconst : ((9 : ℝ) / 8) * (2 : ℝ) ^ ν < ((23 : ℝ) / 16) * (2 : ℝ) ^ ν := by
    have hpow : 0 < (2 : ℝ) ^ ν := by positivity
    nlinarith
  have hlt : (bmIntVal ν j : ℝ) < (p i : ℝ) := lt_of_le_of_lt hj_upper (lt_trans hconst hp_lower)
  exact_mod_cast hlt

lemma bm_prime_ne_two
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (i : PrimeIdx k) :
    p i ≠ 2 := by
  have hp_lower : ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) := (hp_window i).1
  have hgt_two : (2 : ℝ) < (p i : ℝ) := by
    have hpow3 : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ ν := by
      exact pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hν
    have hpow : (8 : ℝ) ≤ (2 : ℝ) ^ ν := by
      norm_num at hpow3 ⊢
      exact hpow3
    nlinarith
  exact_mod_cast ne_of_gt hgt_two

lemma bm_prime_not_dvd_intVal
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hpPrime : ∀ i, Nat.Prime (p i))
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (i : PrimeIdx k) (j : IntIdx ν) :
    ¬ p i ∣ bmIntVal ν j := by
  have hlt : bmIntVal ν j < p i := bm_prime_gt_bmIntVal hν p hp_window i j
  have hcop :
      Nat.Coprime (p i) (bmIntVal ν j) :=
    Nat.coprime_of_lt_prime (Nat.ne_of_gt (bmIntVal_pos ν hν j)) hlt (hpPrime i)
  exact (hpPrime i).coprime_iff_not_dvd.mp hcop

lemma bm_prime_not_dvd_other_prime
    {k : ℕ} (p : PrimeIdx k → ℕ)
    (hpPrime : ∀ i, Nat.Prime (p i))
    (hpPairwise : Pairwise (fun i j => p i ≠ p j))
    {i i' : PrimeIdx k} (hii' : i ≠ i') :
    ¬ p i ∣ p i' := by
  intro hdiv
  exact hpPairwise hii' ((Nat.prime_dvd_prime_iff_eq (hpPrime i) (hpPrime i')).1 hdiv)

lemma bm_flat_intrel_of_prime_window
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hpPairwise : Pairwise (fun i j => p i ≠ p j))
    (hpPrime : ∀ i, Nat.Prime (p i))
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν) :
    ∀ r : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
      (∃ z : ℤ, ∑ j, bmFlatAlpha p j * (r j : ℝ) = z) →
      ∃ z : ℤ, ∑ j, bmFlatBeta k ν j * (r j : ℝ) = z := by
  intro r hrel
  let rBM : BMIdx k ν → ℤ := fun x => r (bmFlatEquiv k ν x)
  rcases hrel with ⟨z, hz⟩
  have hzBM :
      ∑ x : BMIdx k ν, bmAlpha p x * (rBM x : ℝ) = z := by
    have hsum' :
        ∑ x : BMIdx k ν, bmAlpha p x * (rBM x : ℝ) =
          ∑ j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)), bmFlatAlpha p j * (r j : ℝ) := by
      exact Fintype.sum_equiv (bmFlatEquiv k ν)
        (fun x : BMIdx k ν => bmAlpha p x * (rBM x : ℝ))
        (fun j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) => bmFlatAlpha p j * (r j : ℝ))
        (fun x => by
          cases x with
          | inl i =>
              simp [rBM, bmFlatAlpha, bmAlpha, bmFlatEquiv]
          | inr j =>
              simp [rBM, bmFlatAlpha, bmAlpha, bmFlatEquiv])
    have hsum :
        ∑ x : BMIdx k ν, bmAlpha p x * (rBM x : ℝ) =
          ∑ j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)), bmFlatAlpha p j * (r j : ℝ) := by
      simpa [rBM, bmFlatAlpha, bmAlpha, bmFlatEquiv] using hsum'
    exact hsum.trans hz
  have hzSplit :
      (∑ i : PrimeIdx k, Real.logb 2 (p i : ℝ) * (rBM (Sum.inl i) : ℝ)) +
          ∑ j : IntIdx ν, Real.logb 2 (bmIntVal ν j : ℝ) * (rBM (Sum.inr j) : ℝ) = z := by
    simpa [bmAlpha, rBM, Fintype.sum_sum_type, mul_comm, mul_left_comm, mul_assoc] using hzBM
  let primePosProd : ℕ := ∏ i : PrimeIdx k, p i ^ zpos (rBM (Sum.inl i))
  let primeNegProd : ℕ := ∏ i : PrimeIdx k, p i ^ zneg (rBM (Sum.inl i))
  let intPosProd : ℕ := ∏ j : IntIdx ν, bmIntVal ν j ^ zpos (rBM (Sum.inr j))
  let intNegProd : ℕ := ∏ j : IntIdx ν, bmIntVal ν j ^ zneg (rBM (Sum.inr j))
  let A : ℕ := ((2 ^ zneg z) * primePosProd) * intPosProd
  let B : ℕ := ((2 ^ zpos z) * primeNegProd) * intNegProd
  have hp_ne_zero : ∀ i, p i ≠ 0 := fun i => (hpPrime i).ne_zero
  have hint_ne_zero : ∀ j, bmIntVal ν j ≠ 0 := fun j => (bmIntVal_pos ν hν j).ne'
  have hPrimeLog :
      Real.logb 2 (primePosProd : ℝ) - Real.logb 2 (primeNegProd : ℝ) =
        ∑ i : PrimeIdx k, Real.logb 2 (p i : ℝ) * (rBM (Sum.inl i) : ℝ) := by
    simpa [primePosProd, primeNegProd, rBM, mul_comm, mul_left_comm, mul_assoc] using
      (logb_nat_fintype_prod_zparts p (fun i => rBM (Sum.inl i)) hp_ne_zero)
  have hIntLog :
      Real.logb 2 (intPosProd : ℝ) - Real.logb 2 (intNegProd : ℝ) =
        ∑ j : IntIdx ν, Real.logb 2 (bmIntVal ν j : ℝ) * (rBM (Sum.inr j) : ℝ) := by
    simpa [intPosProd, intNegProd, rBM, mul_comm, mul_left_comm, mul_assoc] using
      (logb_nat_fintype_prod_zparts (bmIntVal ν) (fun j => rBM (Sum.inr j)) hint_ne_zero)
  have hprimePos_ne : primePosProd ≠ 0 := by
    dsimp [primePosProd]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact pow_ne_zero _ (hp_ne_zero i)
  have hprimeNeg_ne : primeNegProd ≠ 0 := by
    dsimp [primeNegProd]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i hi
    exact pow_ne_zero _ (hp_ne_zero i)
  have hintPos_ne : intPosProd ≠ 0 := by
    dsimp [intPosProd]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    exact pow_ne_zero _ (hint_ne_zero j)
  have hintNeg_ne : intNegProd ≠ 0 := by
    dsimp [intNegProd]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    exact pow_ne_zero _ (hint_ne_zero j)
  have hAlog :
      Real.logb 2 (A : ℝ) =
        zneg z + Real.logb 2 (primePosProd : ℝ) + Real.logb 2 (intPosProd : ℝ) := by
    dsimp [A]
    rw [logb_nat_mul (mul_ne_zero (pow_ne_zero _ two_ne_zero) hprimePos_ne) hintPos_ne,
      logb_nat_mul (pow_ne_zero _ two_ne_zero) hprimePos_ne]
    simp [Real.logb_pow, add_assoc]
  have hBlog :
      Real.logb 2 (B : ℝ) =
        zpos z + Real.logb 2 (primeNegProd : ℝ) + Real.logb 2 (intNegProd : ℝ) := by
    dsimp [B]
    rw [logb_nat_mul (mul_ne_zero (pow_ne_zero _ two_ne_zero) hprimeNeg_ne) hintNeg_ne,
      logb_nat_mul (pow_ne_zero _ two_ne_zero) hprimeNeg_ne]
    simp [Real.logb_pow, add_assoc]
  have hlogEq : Real.logb 2 (A : ℝ) = Real.logb 2 (B : ℝ) := by
    nlinarith [hzSplit, hPrimeLog, hIntLog, hAlog, hBlog, cast_zpos_sub_zneg z]
  have hA_pos : 0 < (A : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (show A ≠ 0 by
    dsimp [A]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) hprimePos_ne) hintPos_ne)
  have hB_pos : 0 < (B : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (show B ≠ 0 by
    dsimp [B]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) hprimeNeg_ne) hintNeg_ne)
  have hABreal : (A : ℝ) = (B : ℝ) := by
    exact Real.logb_injOn_pos one_lt_two (Set.mem_Ioi.2 hA_pos) (Set.mem_Ioi.2 hB_pos) hlogEq
  have hAB : A = B := by exact_mod_cast hABreal
  have hprimeCoeffZero : ∀ i : PrimeIdx k, rBM (Sum.inl i) = 0 := by
    intro i
    rcases lt_trichotomy (rBM (Sum.inl i)) 0 with hneg | hzero | hpos
    · exfalso
      have hdivFactor : p i ∣ p i ^ zneg (rBM (Sum.inl i)) := by
        exact dvd_pow_self _ (zneg_pos_of_neg hneg).ne'
      have hdivPrimeNeg : p i ∣ primeNegProd := by
        dsimp [primeNegProd]
        exact dvd_trans hdivFactor
          (Finset.dvd_prod_of_mem (fun i' : PrimeIdx k => p i' ^ zneg (rBM (Sum.inl i')))
            (Finset.mem_univ i))
      have hdivB : p i ∣ B := by
        have hfirst : p i ∣ (2 ^ zpos z) * primeNegProd := by
          exact dvd_mul_of_dvd_right hdivPrimeNeg (2 ^ zpos z)
        simpa [B, mul_assoc, mul_left_comm, mul_comm] using
          dvd_mul_of_dvd_right hfirst intNegProd
      have htwo_gt : 2 < p i := lt_of_le_of_ne (hpPrime i).two_le
        (Ne.symm (bm_prime_ne_two hν p hp_window i))
      have hnotTwo : ¬ p i ∣ 2 := by
        have hcop : Nat.Coprime (p i) 2 :=
          Nat.coprime_of_lt_prime (by decide) htwo_gt (hpPrime i)
        exact (hpPrime i).coprime_iff_not_dvd.mp hcop
      have hnotPrimePos : ¬ p i ∣ primePosProd := by
        dsimp [primePosProd]
        apply Prime.not_dvd_finset_prod (p := p i) (hpPrime i).prime
        intro i' hi'
        by_cases hii' : i = i'
        · subst hii'
          simp [zpos_eq_zero_of_nonpos hneg.le, (hpPrime i).ne_one]
        · exact prime_not_dvd_pow_of_not_dvd (hpPrime i)
            (bm_prime_not_dvd_other_prime p hpPrime hpPairwise hii')
      have hnotIntPos : ¬ p i ∣ intPosProd := by
        dsimp [intPosProd]
        apply Prime.not_dvd_finset_prod (p := p i) (hpPrime i).prime
        intro j hj
        exact prime_not_dvd_pow_of_not_dvd (hpPrime i)
          (bm_prime_not_dvd_intVal hν p hpPrime hp_window i j)
      have hnotA : ¬ p i ∣ A := by
        dsimp [A]
        have hnotFirst : ¬ p i ∣ (2 ^ zneg z) * primePosProd :=
          Nat.Prime.not_dvd_mul (hpPrime i)
            (prime_not_dvd_pow_of_not_dvd (hpPrime i) hnotTwo) hnotPrimePos
        exact Nat.Prime.not_dvd_mul (hpPrime i) hnotFirst hnotIntPos
      exact hnotA (hAB ▸ hdivB)
    · exact hzero
    · exfalso
      have hdivFactor : p i ∣ p i ^ zpos (rBM (Sum.inl i)) := by
        exact dvd_pow_self _ (zpos_pos_of_pos hpos).ne'
      have hdivPrimePos : p i ∣ primePosProd := by
        dsimp [primePosProd]
        exact dvd_trans hdivFactor
          (Finset.dvd_prod_of_mem (fun i' : PrimeIdx k => p i' ^ zpos (rBM (Sum.inl i')))
            (Finset.mem_univ i))
      have hdivA : p i ∣ A := by
        have hfirst : p i ∣ (2 ^ zneg z) * primePosProd := by
          exact dvd_mul_of_dvd_right hdivPrimePos (2 ^ zneg z)
        simpa [A, mul_assoc, mul_left_comm, mul_comm] using
          dvd_mul_of_dvd_right hfirst intPosProd
      have htwo_gt : 2 < p i := lt_of_le_of_ne (hpPrime i).two_le
        (Ne.symm (bm_prime_ne_two hν p hp_window i))
      have hnotTwo : ¬ p i ∣ 2 := by
        have hcop : Nat.Coprime (p i) 2 :=
          Nat.coprime_of_lt_prime (by decide) htwo_gt (hpPrime i)
        exact (hpPrime i).coprime_iff_not_dvd.mp hcop
      have hnotPrimeNeg : ¬ p i ∣ primeNegProd := by
        dsimp [primeNegProd]
        apply Prime.not_dvd_finset_prod (p := p i) (hpPrime i).prime
        intro i' hi'
        by_cases hii' : i = i'
        · subst hii'
          simp [zneg_eq_zero_of_nonneg hpos.le, (hpPrime i).ne_one]
        · exact prime_not_dvd_pow_of_not_dvd (hpPrime i)
            (bm_prime_not_dvd_other_prime p hpPrime hpPairwise hii')
      have hnotIntNeg : ¬ p i ∣ intNegProd := by
        dsimp [intNegProd]
        apply Prime.not_dvd_finset_prod (p := p i) (hpPrime i).prime
        intro j hj
        exact prime_not_dvd_pow_of_not_dvd (hpPrime i)
          (bm_prime_not_dvd_intVal hν p hpPrime hp_window i j)
      have hnotB : ¬ p i ∣ B := by
        dsimp [B]
        have hnotFirst : ¬ p i ∣ (2 ^ zpos z) * primeNegProd :=
          Nat.Prime.not_dvd_mul (hpPrime i)
            (prime_not_dvd_pow_of_not_dvd (hpPrime i) hnotTwo) hnotPrimeNeg
        exact Nat.Prime.not_dvd_mul (hpPrime i) hnotFirst hnotIntNeg
      exact hnotB (hAB ▸ hdivA)
  refine ⟨0, ?_⟩
  have hbetaBM :
      ∑ x : BMIdx k ν, bmBeta k ν x * (rBM x : ℝ) = 0 := by
    rw [Fintype.sum_sum_type]
    simp [bmBeta, hprimeCoeffZero, rBM]
  have hbetaFlat :
      ∑ j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)), bmFlatBeta k ν j * (r j : ℝ) = 0 := by
    have hbetaFlat' :
        ∑ x : BMIdx k ν, bmBeta k ν x * (rBM x : ℝ) =
          ∑ j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)), bmFlatBeta k ν j * (r j : ℝ) := by
      exact Fintype.sum_equiv (bmFlatEquiv k ν)
        (fun x : BMIdx k ν => bmBeta k ν x * (rBM x : ℝ))
        (fun j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) => bmFlatBeta k ν j * (r j : ℝ))
        (fun x => by
          cases x with
          | inl i =>
              simp [rBM, bmFlatBeta, bmBeta, bmFlatEquiv]
          | inr j =>
              simp [rBM, bmFlatBeta, bmBeta, bmFlatEquiv])
    exact hbetaFlat'.symm.trans hbetaBM
  simpa using hbetaFlat

lemma bm_prime_mul_mem_window (ν : ℕ) {p y : ℝ}
    (hp : p ∈ Ioo (((23 : ℝ) / 16) * 2 ^ ν) (((3 : ℝ) / 2) * 2 ^ ν))
    (hy : y ∈ I_inf) :
    p * y ∈ Ioo (((8 : ℝ) / 9) * 2 ^ ν) ((2 : ℝ) ^ ν) := by
  rcases hp with ⟨hp_lower, hp_upper⟩
  rcases hy with ⟨hy_lower, hy_upper⟩
  have hy_pos : 0 < y := by linarith
  constructor
  · have hp_times_y : (((23 : ℝ) / 16) * 2 ^ ν) * y < p * y := by
      exact mul_lt_mul_of_pos_right hp_lower hy_pos
    have hlower :
        (((23 : ℝ) / 16) * 2 ^ ν) * ((16 : ℝ) / 25) ≤
          (((23 : ℝ) / 16) * 2 ^ ν) * y := by
      gcongr
    have hnum :
        (((8 : ℝ) / 9) * 2 ^ ν) <
          (((23 : ℝ) / 16) * 2 ^ ν) * ((16 : ℝ) / 25) := by
      have hpow : 0 < (2 : ℝ) ^ ν := by positivity
      nlinarith
    exact lt_trans hnum (lt_of_le_of_lt hlower hp_times_y)
  · have hp_pos : 0 < p := by linarith
    have hy_times_p : p * y ≤ p * ((2 : ℝ) / 3) := by
      gcongr
    have hupper : p * ((2 : ℝ) / 3) < (((3 : ℝ) / 2) * 2 ^ ν) * ((2 : ℝ) / 3) := by
      exact mul_lt_mul_of_pos_right hp_upper (by norm_num)
    have hnum : (((3 : ℝ) / 2) * 2 ^ ν) * ((2 : ℝ) / 3) = (2 : ℝ) ^ ν := by
      ring
    simpa [hnum] using lt_of_le_of_lt hy_times_p hupper

lemma bm_half_grid_not_near_integer (k : ℕ) (hk : 1 ≤ k) (m : ℤ) :
    ¬ |(m : ℝ) + 1 / (2 : ℝ) ^ k| < 1 / (4 * (2 : ℝ) ^ k) := by
  have hkpow : 0 < (2 : ℝ) ^ k := by positivity
  have hfrac_pos : 0 < 1 / (2 : ℝ) ^ k := by positivity
  have hpow_le : (2 : ℝ) ≤ 2 ^ k := by
    simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk
  have hfrac_le_half : 1 / (2 : ℝ) ^ k ≤ 1 / 2 := by
    simpa [one_div] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpow_le)
  have hquarter : 1 / (4 * (2 : ℝ) ^ k) < 1 / (2 : ℝ) ^ k := by
    field_simp [hkpow.ne']
    nlinarith
  intro h
  rcases lt_or_ge m 0 with hm_neg | hm_nonneg
  · have hm_le : (m : ℝ) ≤ -1 := by
      exact_mod_cast (Int.le_sub_one_iff.mpr hm_neg)
    have habs_ge : 1 / (2 : ℝ) ^ k ≤ |(m : ℝ) + 1 / (2 : ℝ) ^ k| := by
      rw [abs_of_nonpos]
      · nlinarith
      · nlinarith
    have hsmall : |(m : ℝ) + 1 / (2 : ℝ) ^ k| < 1 / (2 : ℝ) ^ k := by
      exact lt_trans h hquarter
    exact (not_lt_of_ge habs_ge) hsmall
  · have hm_ge : (0 : ℝ) ≤ m := by exact_mod_cast hm_nonneg
    have habs_ge : 1 / (2 : ℝ) ^ k ≤ |(m : ℝ) + 1 / (2 : ℝ) ^ k| := by
      rw [abs_of_nonneg]
      · have : (1 / (2 : ℝ) ^ k : ℝ) ≤ (m : ℝ) + 1 / (2 : ℝ) ^ k := by
          nlinarith
        exact this
      · positivity
    have hsmall : |(m : ℝ) + 1 / (2 : ℝ) ^ k| < 1 / (2 : ℝ) ^ k := by
      exact lt_trans h hquarter
    exact (not_lt_of_ge habs_ge) hsmall

lemma bm_q_nonzero_of_first_prime_target
    {k : ℕ} (hk : 1 ≤ k) {q : ℤ} {p : ℤ} {a : ℝ}
    (hq :
      |(q : ℝ) * a - (p : ℝ) - 1 / (2 : ℝ) ^ k| <
        1 / (4 * (2 : ℝ) ^ k)) :
    q ≠ 0 := by
  intro hzero
  let s : ℝ := (p : ℝ) + 1 / (2 : ℝ) ^ k
  have hneg : |-s| < 1 / (4 * (2 : ℝ) ^ k) := by
    convert hq using 1
    · simp [s, hzero, sub_eq_add_neg, add_comm]
  have hrew : |s| < 1 / (4 * (2 : ℝ) ^ k) := by
    simpa [abs_neg] using hneg
  exact (bm_half_grid_not_near_integer k hk p) hrew

/-- BM-facing Kronecker wrapper: the common denominator can be chosen nonzero because one
prime-block target is the nonintegral point `1 / 2^k`. -/
lemma bm_common_q_int_nonzero
    {k ν : ℕ} (hk : 1 ≤ k) (p : PrimeIdx k → ℕ)
    (h_intrel :
      ∀ r : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
        (∃ z : ℤ, ∑ j, bmFlatAlpha p j * (r j : ℝ) = z) →
        ∃ z : ℤ, ∑ j, bmFlatBeta k ν j * (r j : ℝ) = z) :
    ∃ q : ℤ, q ≠ 0 ∧ ∃ m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k) := by
  obtain ⟨q, m, hm⟩ :=
    kronecker_intrel_implies_approx_common_q_int
      (2 ^ k + (2 ^ (ν - 2) + 1)) (bmFlatAlpha p) (bmFlatBeta k ν) h_intrel
      (1 / (4 * (2 : ℝ) ^ k)) (by positivity)
  refine ⟨q, ?_, m, hm⟩
  have hcoord :
      |(q : ℝ) * bmFlatAlpha p
            (Fin.castAdd (2 ^ (ν - 2) + 1) (bmPrimeIdxOne k hk)) -
          (m (Fin.castAdd (2 ^ (ν - 2) + 1) (bmPrimeIdxOne k hk)) : ℝ) -
          1 / (2 : ℝ) ^ k| <
        1 / (4 * (2 : ℝ) ^ k) := by
    simpa [bmFlatBeta_primeIdxOne_eq k ν hk] using
      hm (Fin.castAdd (2 ^ (ν - 2) + 1) (bmPrimeIdxOne k hk))
  exact bm_q_nonzero_of_first_prime_target hk hcoord

lemma int_sign_mul_div_natAbs (q m : ℤ) (hq : q ≠ 0) :
    (((Int.sign q * m : ℤ) : ℝ) / (Int.natAbs q : ℝ)) = (m : ℝ) / (q : ℝ) := by
  rcases lt_trichotomy q 0 with hqneg | rfl | hqpos
  · have hsign : Int.sign q = -1 := Int.sign_eq_neg_one_of_neg hqneg
    have hqabs : (Int.natAbs q : ℝ) = -(q : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg]
      exact_mod_cast hqneg
    have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hqneg.ne
    calc
      (((Int.sign q * m : ℤ) : ℝ) / (Int.natAbs q : ℝ))
          = ((-(m : ℝ)) / (-(q : ℝ))) := by simp [hsign, hqabs]
      _ = (m : ℝ) / (q : ℝ) := by field_simp [hqreal]
  · contradiction
  · have hsign : Int.sign q = 1 := Int.sign_eq_one_of_pos hqpos
    have hqabs : (Int.natAbs q : ℝ) = (q : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos]
      exact_mod_cast hqpos
    simp [hsign, hqabs]

lemma bm_integer_lattice_of_common_q
    {k ν : ℕ} {p : PrimeIdx k → ℕ} {q : ℤ}
    (hq : q ≠ 0)
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k))
    {n : ℕ}
    (hn : (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν))
    (hν : 3 ≤ ν) :
    ∃ z : ℤ, |Real.logb 2 (n : ℝ) - (z : ℝ) / (Int.natAbs q : ℝ)| <
      1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
  obtain ⟨j, rfl⟩ := exists_bmIntVal_eq_of_mem_Ioo ν hν hn
  let idx : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) := Fin.natAdd (2 ^ k) j
  let z : ℤ := Int.sign q * m idx
  refine ⟨z, ?_⟩
  have hcoord :
      |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ)| <
        1 / (4 * (2 : ℝ) ^ k) := by
    simpa [idx, bmFlatAlpha_natAdd, bmFlatBeta_natAdd, sub_eq_add_neg] using hm idx
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hqabs_pos : 0 < |(q : ℝ)| := by
    exact abs_pos.mpr hqreal
  have hscaled :
      |Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ) / (q : ℝ)| <
        (1 / (4 * (2 : ℝ) ^ k)) / |(q : ℝ)| := by
    have hmul :
        |(q : ℝ)| *
            |Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ) / (q : ℝ)| <
          1 / (4 * (2 : ℝ) ^ k) := by
      calc
        |(q : ℝ)| * |Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ) / (q : ℝ)|
            = |(q : ℝ) * (Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ) / (q : ℝ))| := by
                rw [abs_mul]
        _ = |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (m idx : ℝ)| := by
              congr 1
              field_simp [hq]
        _ < 1 / (4 * (2 : ℝ) ^ k) := by simpa [abs_sub_comm] using hcoord
    exact (lt_div_iff₀ hqabs_pos).2 (by simpa [mul_comm] using hmul)
  have hrewrite :
      ((z : ℝ) / (Int.natAbs q : ℝ)) = (m idx : ℝ) / (q : ℝ) := by
    simpa [z] using int_sign_mul_div_natAbs q (m idx) hq
  rw [hrewrite]
  have hqabs_cast : (Int.natAbs q : ℝ) = |(q : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hqabs_cast_pos : 0 < (Int.natAbs q : ℝ) := by
    rw [hqabs_cast]
    exact hqabs_pos
  have htarget :
      (1 / (4 * (2 : ℝ) ^ k)) / |(q : ℝ)| =
        1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
    rw [← hqabs_cast]
    field_simp [hqabs_cast_pos.ne']
  rw [hqabs_cast]
  convert hscaled using 1
  ring_nf

lemma bm_prime_coordinate_of_common_q
    {k ν : ℕ} {p : PrimeIdx k → ℕ} {q : ℤ}
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k))
    (i : PrimeIdx k) :
    |(q : ℝ) * Real.logb 2 (p i) - (m (Fin.castAdd (2 ^ (ν - 2) + 1) i) : ℝ) -
        (i : ℝ) / (2 : ℝ) ^ k| <
      1 / (4 * (2 : ℝ) ^ k) := by
  simpa [bmFlatAlpha_castAdd, bmFlatBeta_castAdd] using
    hm (Fin.castAdd (2 ^ (ν - 2) + 1) i)

lemma bm_integer_coordinate_of_common_q
    {k ν : ℕ} {p : PrimeIdx k → ℕ} {q : ℤ}
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k))
    (j : IntIdx ν) :
    |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (m (Fin.natAdd (2 ^ k) j) : ℝ)| <
      1 / (4 * (2 : ℝ) ^ k) := by
  simpa [bmFlatAlpha_natAdd, bmFlatBeta_natAdd, sub_eq_add_neg] using
    hm (Fin.natAdd (2 ^ k) j)

lemma bm_kronecker_coordinate_data
    {k ν : ℕ} (hk : 1 ≤ k) (p : PrimeIdx k → ℕ)
    (h_intrel :
      ∀ r : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
        (∃ z : ℤ, ∑ j, bmFlatAlpha p j * (r j : ℝ) = z) →
        ∃ z : ℤ, ∑ j, bmFlatBeta k ν j * (r j : ℝ) = z) :
    ∃ q : ℤ, q ≠ 0 ∧ ∃ m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
      (∀ i : PrimeIdx k,
        |(q : ℝ) * Real.logb 2 (p i) -
            (m (Fin.castAdd (2 ^ (ν - 2) + 1) i) : ℝ) -
            (i : ℝ) / (2 : ℝ) ^ k| <
          1 / (4 * (2 : ℝ) ^ k)) ∧
      (∀ j : IntIdx ν,
        |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) -
            (m (Fin.natAdd (2 ^ k) j) : ℝ)| <
          1 / (4 * (2 : ℝ) ^ k)) := by
  obtain ⟨q, hq, m, hm⟩ := bm_common_q_int_nonzero hk p h_intrel
  refine ⟨q, hq, m, ?_, ?_⟩
  · intro i
    exact bm_prime_coordinate_of_common_q hm i
  · intro j
    exact bm_integer_coordinate_of_common_q hm j

lemma bm_nearest_grid (q k : ℕ) (hq : 0 < q) (x : ℝ) :
    ∃ j : PrimeIdx k, ∃ n : ℤ,
      |x + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n : ℝ) / (q : ℝ)| ≤
        1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) := by
  let N : ℕ := 2 ^ k
  let t : ℝ := (q : ℝ) * (N : ℝ) * x
  let M : ℤ := round t
  let r : ℤ := (-M) % N
  let n : ℤ := -((-M) / N)
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  have hr_nonneg : 0 ≤ r := by
    dsimp [r, N]
    exact Int.emod_nonneg _ (by exact_mod_cast hN_pos.ne')
  have hr_lt : r < N := by
    dsimp [r, N]
    exact Int.emod_lt_of_pos _ (by exact_mod_cast hN_pos)
  have hr_lt_nat : Int.toNat r < N := by
    exact (Int.toNat_lt_of_ne_zero (Nat.ne_of_gt hN_pos)).2 (by simpa [N] using hr_lt)
  let j : PrimeIdx k := ⟨Int.toNat r, by
    simpa [N] using hr_lt_nat⟩
  refine ⟨j, n, ?_⟩
  have hj_eq_int : ((j : ℕ) : ℤ) = r := by
    dsimp [j]
    simp [Int.toNat_of_nonneg hr_nonneg]
  have hj_eq : (j : ℝ) = r := by
    exact_mod_cast hj_eq_int
  have hdecomp : (N : ℤ) * ((-M) / N) + (-M) % N = -M := by
    simpa [N] using (Int.mul_ediv_add_emod (-M) N)
  have hdecompZ : r - (N : ℤ) * n = -M := by
    dsimp [r, n]
    linarith
  have hdecomp' : (r : ℝ) - (N : ℝ) * (n : ℝ) = -(M : ℝ) := by
    exact_mod_cast hdecompZ
  have hround : |t - M| ≤ 1 / 2 := by
    simpa [t, M] using (abs_sub_round t)
  have hqN_pos : 0 < (q : ℝ) * (N : ℝ) := by
    positivity
  have hmul :
      ((q : ℝ) * (N : ℝ)) *
          |x + (r : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)| ≤
        1 / 2 := by
    calc
      ((q : ℝ) * (N : ℝ)) *
          |x + (r : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)|
          = |((q : ℝ) * (N : ℝ)) *
              (x + (r : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ))| := by
              rw [abs_mul, abs_of_pos hqN_pos]
      _ = |t - M| := by
            congr 1
            dsimp [t]
            have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
            have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
            field_simp [hqreal, hNreal]
            linarith [hdecomp']
      _ ≤ 1 / 2 := hround
  have hbound :
      |x + (r : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)| ≤
        (1 / 2) / ((q : ℝ) * (N : ℝ)) := by
    exact (le_div_iff₀ hqN_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hbound' :
      |x + (j : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)| ≤
        (1 / 2) / ((q : ℝ) * (N : ℝ)) := by
    simpa [hj_eq] using hbound
  have htarget :
      (1 / 2 : ℝ) / ((q : ℝ) * (N : ℝ)) = 1 / (2 * (q : ℝ) * (N : ℝ)) := by
    have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
    field_simp [hqreal, hNreal]
  have hbound'' :
      |x + (j : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)| ≤
        1 / (2 * (q : ℝ) * (N : ℝ)) := by
    exact htarget ▸ hbound'
  simpa [N] using hbound''

lemma bm_prime_cover_of_positive_q
    {k ν q : ℕ} (hq : 0 < q)
    (p : PrimeIdx k → ℕ) (a : PrimeIdx k → ℤ)
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (happrox :
      ∀ i,
        |(q : ℝ) * Real.logb 2 (p i : ℝ) - (a i : ℝ) - (i : ℝ) / (2 : ℝ) ^ k| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
      (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * (2 : ℝ) ^ ν) ((2 : ℝ) ^ ν) ∧
      ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
        1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
  intro y hy
  obtain ⟨j, n₀, hgrid⟩ := bm_nearest_grid q k hq (Real.logb 2 y)
  have hqreal_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have happrox_div :
      |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
          (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
        1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
    have hmul :
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| * (q : ℝ) <
          1 / (4 * (2 : ℝ) ^ k) := by
      calc
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| * (q : ℝ)
            = (q : ℝ) *
                |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                    (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| := by ring
        _ = |(q : ℝ) *
                (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                  (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| := by
              rw [abs_mul, abs_of_pos hqreal_pos]
        _ = |(q : ℝ) * Real.logb 2 (p j : ℝ) - (a j : ℝ) - (j : ℝ) / (2 : ℝ) ^ k| := by
              congr 1
              field_simp [hq.ne']
        _ < 1 / (4 * (2 : ℝ) ^ k) := happrox j
    have hdiv :
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
          (1 / (4 * (2 : ℝ) ^ k)) / (q : ℝ) := by
      exact (lt_div_iff₀ hqreal_pos).2 hmul
    have htarget :
        (1 / (4 * (2 : ℝ) ^ k)) / (q : ℝ) =
          1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
      have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp [hqreal]
    exact htarget ▸ hdiv
  have hpj_mem :
      (p j : ℝ) ∈ Ioo (((23 : ℝ) / 16) * (2 : ℝ) ^ ν) (((3 : ℝ) / 2) * (2 : ℝ) ^ ν) := hp_window j
  have hpj_pos : 0 < p j := by
    have hpj_pos_real : 0 < (p j : ℝ) := by
      rcases hpj_mem with ⟨hpj_lower, _⟩
      have : 0 < ((23 : ℝ) / 16) * (2 : ℝ) ^ ν := by positivity
      linarith
    exact_mod_cast hpj_pos_real
  have hsum :
      |Real.logb 2 y + Real.logb 2 (p j : ℝ) - ((n₀ + a j : ℤ) : ℝ) / (q : ℝ)| <
        1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
    have htri :
        |(Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)) +
            (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
              (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| <
          1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
      have hnorm :
          |(Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)) +
              (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| ≤
            |Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)| +
              |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| := by
        exact abs_add_le _ _
      have hbound :
          |Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)| +
              |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
            1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
        have hsum_lt :
            |Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)| +
                |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                  (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
              1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) +
                1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
          nlinarith
        have htarget :
            1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) +
                1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) <
              1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
          have hq2k_pos : 0 < (q : ℝ) * (2 : ℝ) ^ k := by positivity
          have hq2k_ne : (q : ℝ) * (2 : ℝ) ^ k ≠ 0 := hq2k_pos.ne'
          field_simp [hq2k_ne]
          nlinarith
        exact lt_trans hsum_lt htarget
      exact lt_of_le_of_lt hnorm hbound
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_div] using htri
  refine ⟨p j, hpj_pos, bm_prime_mul_mem_window ν hpj_mem hy, ?_⟩
  refine ⟨n₀ + a j, ?_⟩
  have hy_pos : 0 < y := by
    rcases hy with ⟨hy₁, _⟩
    linarith
  rw [Real.logb_mul] <;> try positivity
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_div] using hsum

lemma bm_prime_cover_of_negative_q
    {k ν q : ℕ} (hq : 0 < q)
    (p : PrimeIdx k → ℕ) (a : PrimeIdx k → ℤ)
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (happrox :
      ∀ i,
        |(q : ℝ) * Real.logb 2 (p i : ℝ) - (a i : ℝ) + (i : ℝ) / (2 : ℝ) ^ k| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
      (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * (2 : ℝ) ^ ν) ((2 : ℝ) ^ ν) ∧
      ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
        1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
  intro y hy
  obtain ⟨j, n₀, hgrid_raw⟩ := bm_nearest_grid q k hq (-Real.logb 2 y)
  have hgrid :
      |Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)| ≤
        1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) := by
    let t : ℝ :=
      Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)
    have htmp : |-t| ≤ 1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) := by
      have hEq :
          -t =
            -Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ) := by
        dsimp [t]
        have hdiv : -((n₀ : ℝ) / (q : ℝ)) = -(n₀ : ℝ) / (q : ℝ) := by ring
        simp [sub_eq_add_neg, add_comm, Int.cast_neg, hdiv]
      rw [hEq]
      exact hgrid_raw
    have htarget : |t| ≤ 1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) := by
      simpa [abs_neg] using htmp
    simpa [t] using htarget
  have hqreal_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have happrox_div :
      |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
        1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
    have hmul :
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| * (q : ℝ) <
          1 / (4 * (2 : ℝ) ^ k) := by
      calc
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| * (q : ℝ)
            = (q : ℝ) *
                |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                    (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| := by ring
        _ = |(q : ℝ) *
                (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                  (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| := by
              rw [abs_mul, abs_of_pos hqreal_pos]
        _ = |(q : ℝ) * Real.logb 2 (p j : ℝ) - (a j : ℝ) + (j : ℝ) / (2 : ℝ) ^ k| := by
              congr 1
              field_simp [hq.ne']
        _ < 1 / (4 * (2 : ℝ) ^ k) := happrox j
    have hdiv :
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
          (1 / (4 * (2 : ℝ) ^ k)) / (q : ℝ) := by
      exact (lt_div_iff₀ hqreal_pos).2 hmul
    have htarget :
        (1 / (4 * (2 : ℝ) ^ k)) / (q : ℝ) =
          1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
      have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp [hqreal]
    exact htarget ▸ hdiv
  have hpj_mem :
      (p j : ℝ) ∈ Ioo (((23 : ℝ) / 16) * (2 : ℝ) ^ ν) (((3 : ℝ) / 2) * (2 : ℝ) ^ ν) := hp_window j
  have hpj_pos : 0 < p j := by
    have hpj_pos_real : 0 < (p j : ℝ) := by
      rcases hpj_mem with ⟨hpj_lower, _⟩
      have : 0 < ((23 : ℝ) / 16) * (2 : ℝ) ^ ν := by positivity
      linarith
    exact_mod_cast hpj_pos_real
  have hsum :
      |Real.logb 2 y + Real.logb 2 (p j : ℝ) - (((-n₀ + a j : ℤ) : ℝ) / (q : ℝ))| <
        1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
    have htri :
        |(Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)) +
            (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
              (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| <
          1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
      have hnorm :
          |(Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)) +
              (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| ≤
            |Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)| +
              |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| := by
        exact abs_add_le _ _
      have hbound :
          |Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)| +
              |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
            1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
        have hsum_lt :
            |Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)| +
                |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                  (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
              1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) +
                1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
          nlinarith
        have htarget :
            1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) +
                1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) <
              1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
          have hq2k_pos : 0 < (q : ℝ) * (2 : ℝ) ^ k := by positivity
          have hq2k_ne : (q : ℝ) * (2 : ℝ) ^ k ≠ 0 := hq2k_pos.ne'
          field_simp [hq2k_ne]
          nlinarith
        exact lt_trans hsum_lt htarget
      exact lt_of_le_of_lt hnorm hbound
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_div] using htri
  refine ⟨p j, hpj_pos, bm_prime_mul_mem_window ν hpj_mem hy, ?_⟩
  refine ⟨-n₀ + a j, ?_⟩
  have hy_pos : 0 < y := by
    rcases hy with ⟨hy₁, _⟩
    linarith
  rw [Real.logb_mul] <;> try positivity
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_div] using hsum

lemma bm_integer_cover_of_nonzero_q
    {k ν : ℕ} {q : ℤ} (hq : q ≠ 0) (hν : 3 ≤ ν)
    {p : PrimeIdx k → ℕ}
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ n : ℕ, (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν) →
      ∃ z : ℤ, |Real.logb 2 (n : ℝ) - (z : ℝ) / (Int.natAbs q : ℝ)| <
        1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
  intro n hn
  exact bm_integer_lattice_of_common_q hq hm hn hν

lemma bm_integer_cover_of_coordinate_data
    {k ν : ℕ} {q : ℤ} (hq : q ≠ 0) (hν : 3 ≤ ν)
    (a : IntIdx ν → ℤ)
    (happrox :
      ∀ j : IntIdx ν,
        |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ)| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ n : ℕ, (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν) →
      ∃ z : ℤ, |Real.logb 2 (n : ℝ) - (z : ℝ) / (Int.natAbs q : ℝ)| <
        1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
  intro n hn
  obtain ⟨j, rfl⟩ := exists_bmIntVal_eq_of_mem_Ioo ν hν hn
  let z : ℤ := Int.sign q * a j
  refine ⟨z, ?_⟩
  have hcoord :
      |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ)| <
        1 / (4 * (2 : ℝ) ^ k) := happrox j
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hqabs_pos : 0 < |(q : ℝ)| := by
    exact abs_pos.mpr hqreal
  have hscaled :
      |Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ) / (q : ℝ)| <
        (1 / (4 * (2 : ℝ) ^ k)) / |(q : ℝ)| := by
    have hmul :
        |(q : ℝ)| *
            |Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ) / (q : ℝ)| <
          1 / (4 * (2 : ℝ) ^ k) := by
      calc
        |(q : ℝ)| *
            |Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ) / (q : ℝ)|
            = |(q : ℝ) * (Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ) / (q : ℝ))| := by
                rw [abs_mul]
        _ = |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ)| := by
              congr 1
              field_simp [hq]
        _ < 1 / (4 * (2 : ℝ) ^ k) := by simpa [abs_sub_comm] using hcoord
    exact (lt_div_iff₀ hqabs_pos).2 (by simpa [mul_comm] using hmul)
  have hrewrite :
      ((z : ℝ) / (Int.natAbs q : ℝ)) = (a j : ℝ) / (q : ℝ) := by
    simpa [z] using int_sign_mul_div_natAbs q (a j) hq
  rw [hrewrite]
  have hqabs_cast : (Int.natAbs q : ℝ) = |(q : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hqabs_cast_pos : 0 < (Int.natAbs q : ℝ) := by
    rw [hqabs_cast]
    exact hqabs_pos
  have htarget :
      (1 / (4 * (2 : ℝ) ^ k)) / |(q : ℝ)| =
        1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
    rw [← hqabs_cast]
    field_simp [hqabs_cast_pos.ne']
  rw [hqabs_cast]
  convert hscaled using 1
  ring_nf

lemma bm_integer_cover_of_positive_q
    {k ν q : ℕ} (hq : 0 < q) (hν : 3 ≤ ν)
    {p : PrimeIdx k → ℕ}
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |((q : ℤ) : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ n : ℕ, (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν) →
      ∃ z : ℤ, |Real.logb 2 (n : ℝ) - (z : ℝ) / (q : ℝ)| <
        1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
  intro n hn
  obtain ⟨z, hz⟩ :=
    bm_integer_lattice_of_common_q
      (k := k) (ν := ν) (p := p) (q := (q : ℤ))
      (by exact_mod_cast hq.ne') hm hn hν
  refine ⟨z, ?_⟩
  simpa using hz

lemma bm_approx_data_of_positive_flat_data
    (hData :
      ∃ K₀ : ℕ, ∀ k, K₀ ≤ k →
        ∃ N_k : ℕ, ∀ ν, N_k ≤ ν →
          ∃ q : ℕ, 0 < q ∧
            ∃ p : PrimeIdx k → ℕ,
              (∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
                    (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν) ∧
              ∃ m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
                (∀ j,
                  |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
                    1 / (4 * (2 : ℝ) ^ k))) :
    ∃ K₀ : ℕ, ∀ k, K₀ ≤ k →
      ∃ N_k : ℕ, ∀ ν, N_k ≤ ν →
        ∃ q : ℕ, 0 < q ∧
          (∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
            (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * 2 ^ ν) ((2 : ℝ) ^ ν) ∧
            ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
              1 / ((q : ℝ) * 2 ^ k)) ∧
          (∀ n : ℕ, (n : ℝ) ∈ Ioo ((7 : ℝ) / 8 * 2 ^ ν) ((9 : ℝ) / 8 * 2 ^ ν) →
            ∃ m : ℤ, |Real.logb 2 (n : ℝ) - (m : ℝ) / (q : ℝ)| <
              1 / (4 * (q : ℝ) * 2 ^ k)) := by
  obtain ⟨K₀, hK₀⟩ := hData
  refine ⟨K₀, fun k hk => ?_⟩
  obtain ⟨N_k, hN_k⟩ := hK₀ k hk
  refine ⟨max N_k 3, fun ν hν => ?_⟩
  obtain ⟨q, hq, p, hp_window, m, hm⟩ := hN_k ν ((le_max_left N_k 3).trans hν)
  refine ⟨q, hq, ?_, ?_⟩
  · exact bm_prime_cover_of_positive_q hq p
      (fun i => m (Fin.castAdd (2 ^ (ν - 2) + 1) i))
      hp_window
      (fun i => by simpa using bm_prime_coordinate_of_common_q hm i)
  · exact bm_integer_cover_of_positive_q hq ((le_max_right N_k 3).trans hν) hm

/-- **Kronecker–PNT approximation data** for the BM construction. -/
lemma bm_approx_data :
    ∃ K₀ : ℕ, ∀ k, K₀ ≤ k →
      ∃ N_k : ℕ, ∀ ν, N_k ≤ ν →
        ∃ q : ℕ, 0 < q ∧
          (∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
            (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * 2 ^ ν) ((2 : ℝ) ^ ν) ∧
            ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
              1 / ((q : ℝ) * 2 ^ k)) ∧
          (∀ n : ℕ, (n : ℝ) ∈ Ioo ((7 : ℝ) / 8 * 2 ^ ν) ((9 : ℝ) / 8 * 2 ^ ν) →
            ∃ m : ℤ, |Real.logb 2 (n : ℝ) - (m : ℝ) / (q : ℝ)| <
              1 / (4 * (q : ℝ) * 2 ^ k)) := by
  refine ⟨1, ?_⟩
  intro k hk
  obtain ⟨Np, hNp⟩ := bm_many_primes k
  refine ⟨max Np 3, ?_⟩
  intro ν hν
  have hνp : Np ≤ ν := (le_max_left Np 3).trans hν
  have hν3 : 3 ≤ ν := (le_max_right Np 3).trans hν
  obtain ⟨p, hpPairwise, hpPrime, hpWindow⟩ := hNp ν hνp
  have hIntrel :
      ∀ r : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
        (∃ z : ℤ, ∑ j, bmFlatAlpha p j * (r j : ℝ) = z) →
        ∃ z : ℤ, ∑ j, bmFlatBeta k ν j * (r j : ℝ) = z :=
    bm_flat_intrel_of_prime_window hν3 p hpPairwise hpPrime hpWindow
  obtain ⟨qInt, hqInt, m, hPrimeCoords, hIntCoords⟩ :=
    bm_kronecker_coordinate_data hk p hIntrel
  let q : ℕ := Int.natAbs qInt
  have hq : 0 < q := Int.natAbs_pos.mpr hqInt
  refine ⟨q, hq, ?_, ?_⟩
  · rcases lt_or_gt_of_ne hqInt with hqNeg | hqPos
    · have hqabs : (q : ℝ) = -(qInt : ℝ) := by
        have hqabs_int : ((Int.natAbs qInt : ℕ) : ℤ) = -qInt := by
          rw [Int.natCast_natAbs, abs_of_neg hqNeg]
        have hqabs_real : (((Int.natAbs qInt : ℕ) : ℤ) : ℝ) = ((-qInt : ℤ) : ℝ) := by
          exact_mod_cast hqabs_int
        dsimp [q]
        simpa using hqabs_real
      let aNeg : PrimeIdx k → ℤ := fun i => -m (Fin.castAdd (2 ^ (ν - 2) + 1) i)
      have happroxNeg :
          ∀ i,
            |(q : ℝ) * Real.logb 2 (p i : ℝ) - (aNeg i : ℝ) + (i : ℝ) / (2 : ℝ) ^ k| <
              1 / (4 * (2 : ℝ) ^ k) := by
        intro i
        have hi := hPrimeCoords i
        have hi_neg :
            |-( (qInt : ℝ) * Real.logb 2 (p i : ℝ) -
                (m (Fin.castAdd (2 ^ (ν - 2) + 1) i) : ℝ) -
                (i : ℝ) / (2 : ℝ) ^ k)| <
              1 / (4 * (2 : ℝ) ^ k) := by
          convert hi using 1
          rw [abs_neg]
        rw [hqabs]
        convert hi_neg using 1
        · simp [aNeg]
          ring_nf
      exact bm_prime_cover_of_negative_q hq p aNeg hpWindow happroxNeg
    · have hqabs : (q : ℝ) = (qInt : ℝ) := by
        have hqabs_int : ((Int.natAbs qInt : ℕ) : ℤ) = qInt := by
          rw [Int.natCast_natAbs, abs_of_nonneg hqPos.le]
        have hqabs_real : (((Int.natAbs qInt : ℕ) : ℤ) : ℝ) = (qInt : ℝ) := by
          exact_mod_cast hqabs_int
        dsimp [q]
        simpa using hqabs_real
      let aPos : PrimeIdx k → ℤ := fun i => m (Fin.castAdd (2 ^ (ν - 2) + 1) i)
      have happroxPos :
          ∀ i,
            |(q : ℝ) * Real.logb 2 (p i : ℝ) - (aPos i : ℝ) - (i : ℝ) / (2 : ℝ) ^ k| <
              1 / (4 * (2 : ℝ) ^ k) := by
        intro i
        rw [hqabs]
        simpa [aPos] using hPrimeCoords i
      exact bm_prime_cover_of_positive_q hq p aPos hpWindow happroxPos
  · have hIntApprox :
        ∀ j : IntIdx ν,
          |(qInt : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) -
              (m (Fin.natAdd (2 ^ k) j) : ℝ)| <
            1 / (4 * (2 : ℝ) ^ k) := by
        intro j
        simpa using hIntCoords j
    have hIntWindow :=
      bm_integer_cover_of_coordinate_data hqInt hν3
        (fun j => m (Fin.natAdd (2 ^ k) j)) hIntApprox
    intro n hn
    obtain ⟨z, hz⟩ := hIntWindow n hn
    exact ⟨z, by simpa [q] using hz⟩

end


-- ============================================================
-- Formalization
-- ============================================================

/-!
# A Negative Answer to the Eventual Covering Question

We formalize the following result: there exists a measurable set `E ⊂ (0,∞)` of positive
Lebesgue measure such that for every `x ∈ [16/25, 2/3]`, there are infinitely many
positive integers `n` for which `x ∉ (r/n)·E` for every positive integer `r`.

The construction uses:
- `F := ⋃ k, H k` where `H k` are pairwise disjoint open "shells"
- `E := I_F \ Φ(F)` where `I_F = (8/9, 1)` and `Φ` captures integer-multiple shadows

The proof relies on the Buczolich–Mauldin shell construction, which is stated here
without proof (`disjoint_shells`). Everything else is proved from this single input.

## References

* Z. Buczolich, R. D. Mauldin, *On the convergence of ∑ f(nx) for measurable functions*
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-! ## Definitions -/

/-- `Φ(A) = {x ∈ [1/2, 1) : ∃ m ≥ 1, m·x ∈ A}`.
    This is the "shadow" of `A` under positive integer multiples, restricted to `[1/2, 1)`. -/
def Phi (A : Set ℝ) : Set ℝ :=
  Ico (1/2 : ℝ) 1 ∩ {x | ∃ m : ℕ, 0 < m ∧ ((m : ℝ) * x) ∈ A}

/-- `I_F = (8/9, 1)`, the fundamental interval from which `E` is carved. -/
def I_F : Set ℝ := Ioo (8/9 : ℝ) 1

/-- `MultSat(E) = ⋃_{r≥1} r·E`, the multiplicative saturation of `E`. -/
def MultSat (E : Set ℝ) : Set ℝ :=
  {y | ∃ r : ℕ, 0 < r ∧ ∃ e ∈ E, y = (r : ℝ) * e}

/-! ## Buczolich–Mauldin shell construction

The proof of `disjoint_shells` follows the architecture of [BuMa99]:
1. The **BM Lemma** (`bm_lemma`) constructs, for each large `k` and `ν`,
   an open shell `H ⊆ (2^{ν-1}, 2^ν)` covering `I_∞` with small shadow measure.
2. The **assembly** step selects shells in distinct dyadic intervals (ensuring
   pairwise disjointness) and bounds the total shadow measure by a geometric series. -/

/-- `Phi ∅ = ∅`: the shadow of the empty set is empty. -/
@[simp]
lemma Phi_empty : Phi ∅ = ∅ := by
  ext x; simp [Phi]

/-! ### BM shell definition and properties -/

/-- The BM shell: points in `((8/9)·2^ν, 2^ν)` whose `log₂` is within
    `1/(q·2^k)` of a lattice point `n/q`. -/
def bm_shell (k ν q : ℕ) : Set ℝ :=
  {y ∈ Ioo ((8 : ℝ) / 9 * 2 ^ ν) ((2 : ℝ) ^ ν) |
    ∃ n : ℤ, |Real.logb 2 y - (n : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) * 2 ^ k)}

/-
The BM shell is open (for `q > 0`).
-/
lemma bm_shell_isOpen (k ν q : ℕ) (_hq : 0 < q) : IsOpen (bm_shell k ν q) := by
  refine' isOpen_iff_mem_nhds.mpr fun x hx => _;
  obtain ⟨ n, hn ⟩ := hx.2;
  -- Since $| \log_2 x - n / q | < 1 / (q * 2^k)$, there exists an open interval around $x$ where $| \log_2 y - n / q | < 1 / (q * 2^k)$.
  obtain ⟨ε, hε⟩ : ∃ ε > 0, ∀ y, abs (y - x) < ε → abs (Real.logb 2 y - n / q) < 1 / (q * 2 ^ k) := by
    exact Metric.mem_nhds_iff.mp ( ContinuousAt.preimage_mem_nhds ( show ContinuousAt ( fun y => |Real.logb 2 y - ↑n / ↑q| ) x from ContinuousAt.abs ( ContinuousAt.sub ( ContinuousAt.div_const ( Real.continuousAt_log ( by linarith [ hx.1.1, show ( 0 : ℝ ) < 2 ^ ν by positivity ] ) ) _ ) continuousAt_const ) ) ( Iio_mem_nhds hn ) );
  filter_upwards [ Ioo_mem_nhds hx.1.1 hx.1.2, Metric.ball_mem_nhds x hε.1 ] with y hy₁ hy₂ using ⟨ hy₁, n, hε.2 y hy₂ ⟩

/-
The BM shell is contained in the dyadic interval `(2^{ν-1}, 2^ν)`.
-/
lemma bm_shell_subset_dyadic (k ν q : ℕ) :
    bm_shell k ν q ⊆ Ioo ((2 : ℝ) ^ ν / 2) ((2 : ℝ) ^ ν) := by
  exact Set.Subset.trans ( Set.inter_subset_left ) ( Set.Ioo_subset_Ioo ( by linarith [ pow_pos ( zero_lt_two' ℝ ) ν ] ) le_rfl )

/-
If the Kronecker covering data holds, then `I_∞ ⊆ Φ(bm_shell)`.
-/
lemma bm_shell_covers (k ν q : ℕ)
    (h_cover : ∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
      (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * 2 ^ ν) ((2 : ℝ) ^ ν) ∧
      ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
        1 / ((q : ℝ) * 2 ^ k)) :
    I_inf ⊆ Phi (bm_shell k ν q) := by
  intro x hx;
  -- By definition of Phi, we need to show that x is in Ico (1/2, 1) and there exists an m such that m*x is in bm_shell.
  apply And.intro;
  · constructor <;> linarith [ Set.mem_Icc.mp hx ];
  · exact Exists.elim ( h_cover x hx ) fun m hm => ⟨ m, hm.1, hm.2.1, hm.2.2 ⟩

/-
**Shadow containment**: if `y ∈ I_F ∩ Φ(bm_shell)`, then `log₂ y` is within
    `2/(q·2^k)` of some lattice point `m/q`.
-/
lemma bm_shadow_containment (k ν q : ℕ) (_hq : 0 < q)
    (h_lattice : ∀ n : ℕ, (n : ℝ) ∈ Ioo ((7 : ℝ) / 8 * 2 ^ ν) ((9 : ℝ) / 8 * 2 ^ ν) →
      ∃ m : ℤ, |Real.logb 2 (n : ℝ) - (m : ℝ) / (q : ℝ)| <
        1 / (4 * (q : ℝ) * 2 ^ k)) :
    I_F ∩ Phi (bm_shell k ν q) ⊆
    {y ∈ I_F | ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| <
      2 / ((q : ℝ) * 2 ^ k)} := by
  intro y hy;
  -- Since $y \in I_F \cap \Phi(bm_shell)$, there exists $n \in \mathbb{N}$ such that $n \cdot y \in bm_shell$.
  obtain ⟨n, hn_pos, hn_shell⟩ : ∃ n : ℕ, 0 < n ∧ n * y ∈ bm_shell k ν q := by
    cases hy.2 ; aesop;
  obtain ⟨ m₁, hm₁ ⟩ := h_lattice n (by
  constructor <;> nlinarith [ hn_shell.1.1, hn_shell.1.2, hy.1.1, hy.1.2 ])
  obtain ⟨ m₂, hm₂ ⟩ := hn_shell.2;
  rw [ Real.logb_mul ] at hm₂ <;> norm_num at *;
  · exact ⟨ hy.1, m₂ - m₁, by rw [ abs_lt ] at *; constructor <;> push_cast <;> ring_nf at * <;> linarith ⟩;
  · linarith;
  · linarith [ hy.1.1, hy.1.2 ]

/-! ### Auxiliary lemmas for the thin-set measure bound -/

/-
`logb 2 (9/8) < 1/5`, equivalently `(9/8)^5 < 2`.
-/
lemma logb_nine_eighth_lt : Real.logb 2 (9 / 8 : ℝ) < 1 / 5 := by
  rw [ Real.logb_lt_iff_lt_rpow ] <;> norm_num;
  rw [ Real.lt_rpow_iff_log_lt ] <;> norm_num;
  rw [ div_mul_eq_mul_div, lt_div_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.log_lt_log ]

/-
For `c ≤ 0` and `0 ≤ δ ≤ 1`, `2^(c+δ) - 2^(c-δ) ≤ 2δ`.
    Follows from convexity: `2^δ ≤ 1+δ` (secant on `[0,1]`), `2^(-δ) ≥ 1-δ` (tangent).
-/
lemma rpow_interval_width (c δ : ℝ) (hc : c ≤ 0) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (2 : ℝ) ^ (c + δ) - (2 : ℝ) ^ (c - δ) ≤ 2 * δ := by
  rw [ Real.rpow_sub, Real.rpow_add ] <;> norm_num;
  rw [ add_div', le_div_iff₀ ] <;> try positivity;
  -- Since $c \leq 0$, we have $2^c \leq 1$. Also, by convexity, $2^\delta \leq 1 + \delta(2 - 1) = 1 + \delta$.
  have h_exp : (2 : ℝ) ^ c ≤ 1 ∧ (2 : ℝ) ^ δ ≤ 1 + δ := by
    refine' ⟨ by rw [ Real.rpow_le_one_iff_of_pos ] <;> norm_num ; linarith, _ ⟩;
    have := @Real.geom_mean_le_arith_mean;
    specialize this { 0, 1 } ( fun i => if i = 0 then 1 - δ else δ ) ( fun i => if i = 0 then 1 else 2 ) ; norm_num at *;
    linarith [ this hδ1 hδ0 ];
  nlinarith [ Real.rpow_pos_of_pos zero_lt_two c, Real.rpow_pos_of_pos zero_lt_two δ, mul_le_mul_of_nonneg_left h_exp.1 ( Real.rpow_nonneg zero_le_two δ ), mul_le_mul_of_nonneg_left h_exp.2 ( Real.rpow_nonneg zero_le_two c ), Real.rpow_le_rpow_of_exponent_le ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hc, Real.rpow_le_rpow_of_exponent_le ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hδ0 ]

/-
**Thin set measure bound**: the set of `y ∈ I_F` whose `log₂` is within
    `2/(q·2^k)` of a lattice point `m/q` has measure less than `5 · 2⁻ᵏ`.
-/
lemma thin_set_measure_bound (q : ℕ) (hq : 0 < q) (k : ℕ) (hk : 7 ≤ k) :
    volume {y ∈ Ioo (8/9 : ℝ) 1 |
      ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| <
        2 / ((q : ℝ) * 2 ^ k)} <
    ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := by
  -- The set S is contained in the union of intervals Ioo (2^(m/q - δ)) (2^(m/q + δ)) for m in a finite range.
  have h_union : {y ∈ Ioo (8 / 9 : ℝ) 1 | ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| < 2 / ((q : ℝ) * 2 ^ k)} ⊆ ⋃ m ∈ Finset.Icc (⌈(q : ℝ) * (Real.logb 2 (8 / 9) - 2 / ((q : ℝ) * 2 ^ k))⌉ : ℤ) 0, Ioo (2 ^ ((m : ℝ) / (q : ℝ) - 2 / ((q : ℝ) * 2 ^ k))) (2 ^ ((m : ℝ) / (q : ℝ) + 2 / ((q : ℝ) * 2 ^ k))) := by
    intro y hy
    obtain ⟨hy_range, m, hm⟩ := hy
    have hm_range : ⌈(q : ℝ) * (Real.logb 2 (8 / 9) - 2 / ((q : ℝ) * 2 ^ k))⌉ ≤ m ∧ m ≤ 0 := by
      constructor;
      · have hm_range : Real.logb 2 y > Real.logb 2 (8 / 9) := by
          exact Real.logb_lt_logb ( by norm_num ) ( by norm_num ) hy_range.1;
        exact Int.ceil_le.mpr ( by nlinarith [ abs_lt.mp hm, show ( q : ℝ ) > 0 by positivity, mul_div_cancel₀ ( m : ℝ ) ( by positivity : ( q : ℝ ) ≠ 0 ) ] );
      · have hm_neg : Real.logb 2 y < 0 := by
          rw [ Real.logb_neg_iff ] <;> linarith [ hy_range.1, hy_range.2 ];
        contrapose! hm_neg;
        rw [ abs_lt ] at hm;
        ring_nf at *;
        nlinarith [ show ( m : ℝ ) ≥ 1 by exact_mod_cast hm_neg, inv_pos.mpr ( by positivity : 0 < ( q : ℝ ) ), pow_le_pow_of_le_one ( by positivity : ( 0 : ℝ ) ≤ 2⁻¹ ) ( by norm_num ) ( show k ≥ 1 by linarith ), mul_inv_cancel₀ ( by positivity : ( q : ℝ ) ≠ 0 ) ];
    simp +zetaDelta at *;
    refine' ⟨ m, _, hm_range, _ ⟩;
    · rw [ ← Real.log_lt_log_iff ( by positivity ) ( by linarith ), Real.log_rpow ] <;> norm_num;
      rw [ Real.logb ] at hm ; nlinarith [ abs_lt.mp hm, Real.log_pos one_lt_two, mul_div_cancel₀ ( Real.log y ) ( show ( Real.log 2 ) ≠ 0 by positivity ) ];
    · rw [ ← Real.log_lt_log_iff ( by linarith ) ( by positivity ), Real.log_rpow ] <;> norm_num;
      rw [ Real.logb ] at hm ; nlinarith [ abs_lt.mp hm, Real.log_pos one_lt_two, mul_div_cancel₀ ( Real.log y ) ( show ( Real.log 2 ) ≠ 0 by positivity ) ];
  -- The measure of the union of intervals is at most the sum of their lengths.
  have h_measure : MeasureTheory.volume {y ∈ Ioo (8 / 9 : ℝ) 1 | ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| < 2 / ((q : ℝ) * 2 ^ k)} ≤ (Finset.card (Finset.Icc (⌈(q : ℝ) * (Real.logb 2 (8 / 9) - 2 / ((q : ℝ) * 2 ^ k))⌉ : ℤ) 0)) * ENNReal.ofReal (4 / ((q : ℝ) * 2 ^ k)) := by
    refine' le_trans ( MeasureTheory.measure_mono h_union ) _;
    refine' le_trans ( MeasureTheory.measure_biUnion_finset_le _ _ ) _;
    refine' le_trans ( Finset.sum_le_sum fun _ _ => _ ) _;
    use fun m => ENNReal.ofReal ( 4 / ( q * 2 ^ k ) );
    · rw [ Real.volume_Ioo ];
      refine' ENNReal.ofReal_le_ofReal _;
      convert rpow_interval_width _ _ _ _ _ using 1 <;> ring_nf <;> norm_num;
      · exact mul_nonpos_of_nonpos_of_nonneg ( Int.cast_nonpos.mpr ( Finset.mem_Icc.mp ‹_› |>.2 ) ) ( by positivity );
      · field_simp;
        exact le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) hk ) zero_le_two ) ( by norm_num; linarith [ show ( q : ℝ ) ≥ 1 by norm_cast ] );
    · norm_num;
  -- The number of nonzero terms is at most $q * \log_2(9/8) + 2 / 2^k + 1$.
  have h_card : Finset.card (Finset.Icc (⌈(q : ℝ) * (Real.logb 2 (8 / 9) - 2 / ((q : ℝ) * 2 ^ k))⌉ : ℤ) 0) ≤ (q : ℝ) * Real.logb 2 (9 / 8) + 2 / 2 ^ k + 1 := by
    rw [ show ( 9 / 8 : ℝ ) = ( 8 / 9 ) ⁻¹ by norm_num, Real.logb_inv ] ; norm_num;
    rw [ show ( 2 : ℝ ) / 2 ^ k = 2 / ( 2 ^ k : ℝ ) by ring, mul_sub, mul_div_assoc' ];
    norm_num [ mul_div_mul_left, hq.ne' ];
    rw [ show ( 1 - ⌈ ( q : ℝ ) * Real.logb 2 ( 8 / 9 ) - 2 / 2 ^ k⌉ : ℤ ) = -⌈ ( q : ℝ ) * Real.logb 2 ( 8 / 9 ) - 2 / 2 ^ k⌉ + 1 by ring ] ; norm_num;
    rcases n : -⌈ ( q : ℝ ) * Real.logb 2 ( 8 / 9 ) - 2 / 2 ^ k⌉ + 1 with ( _ | n ) <;> norm_num [ n ];
    · norm_num [ ← @Int.cast_inj ℝ ] at * ; linarith [ Int.le_ceil ( ( q : ℝ ) * Real.logb 2 ( 8 / 9 ) - 2 / 2 ^ k ) ];
    · nlinarith [ show ( q : ℝ ) ≥ 1 by norm_cast, show ( 2 : ℝ ) ^ k ≥ 1 by exact one_le_pow₀ ( by norm_num ), show ( Real.logb 2 ( 8 / 9 ) ) ≤ 0 by rw [ Real.logb_nonpos_iff ] <;> norm_num, div_nonneg zero_le_two ( show ( 0 : ℝ ) ≤ 2 ^ k by positivity ) ];
  -- Substitute the bound on the number of nonzero terms into the measure inequality.
  have h_final : MeasureTheory.volume {y ∈ Ioo (8 / 9 : ℝ) 1 | ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| < 2 / ((q : ℝ) * 2 ^ k)} ≤ ENNReal.ofReal ((q * Real.logb 2 (9 / 8) + 2 / 2 ^ k + 1) * (4 / ((q : ℝ) * 2 ^ k))) := by
    refine le_trans h_measure ?_;
    rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num;
    · gcongr;
      · exact add_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.logb_nonneg ( by norm_num ) ( by norm_num ) ) ) ( by positivity ) ) zero_le_one;
      · convert h_card using 1;
        norm_num [ Int.toNat_of_nonneg, Int.ceil_nonneg ];
      · rw [ ENNReal.toReal_ofReal ( by positivity ) ];
    · exact ENNReal.mul_ne_top ( by norm_num ) ( ENNReal.ofReal_ne_top );
    · exact mul_nonneg ( add_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.logb_nonneg ( by norm_num ) ( by norm_num ) ) ) ( by positivity ) ) zero_le_one ) ( by positivity );
  refine lt_of_le_of_lt h_final ?_;
  rw [ ENNReal.ofReal_lt_ofReal_iff ] <;> ring_nf <;> norm_num [ hq.ne', hk ];
  norm_num [ pow_mul, mul_assoc, mul_comm, mul_left_comm, hq.ne' ];
  have := logb_nine_eighth_lt;
  nlinarith [ show ( q : ℝ ) ≥ 1 by norm_cast, inv_pos.mpr ( by positivity : 0 < ( q : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( q : ℝ ) ≠ 0 ), pow_pos ( by positivity : 0 < ( 1 / 2 : ℝ ) ) k, pow_le_pow_of_le_one ( by positivity : 0 ≤ ( 1 / 2 : ℝ ) ) ( by norm_num ) hk, mul_le_mul_of_nonneg_left this.le ( by positivity : 0 ≤ ( 1 / 2 : ℝ ) ^ k ) ]

/-- Shadow measure bound: if the lattice data holds and `q ≥ 1`, then
    `μ(I_F ∩ Φ(bm_shell)) < 5 · 2⁻ᵏ`. -/
lemma bm_shell_shadow_small (k ν q : ℕ) (hq : 0 < q) (hk : 7 ≤ k)
    (h_lattice : ∀ n : ℕ, (n : ℝ) ∈ Ioo ((7 : ℝ) / 8 * 2 ^ ν) ((9 : ℝ) / 8 * 2 ^ ν) →
      ∃ m : ℤ, |Real.logb 2 (n : ℝ) - (m : ℝ) / (q : ℝ)| <
        1 / (4 * (q : ℝ) * 2 ^ k)) :
    volume (I_F ∩ Phi (bm_shell k ν q)) < ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := by
  calc volume (I_F ∩ Phi (bm_shell k ν q))
      _ ≤ volume {y ∈ I_F | ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| <
            2 / ((q : ℝ) * 2 ^ k)} := measure_mono (bm_shadow_containment k ν q hq h_lattice)
      _ = volume {y ∈ Ioo (8/9 : ℝ) 1 | ∃ m : ℤ, |Real.logb 2 y - (m : ℝ) / (q : ℝ)| <
            2 / ((q : ℝ) * 2 ^ k)} := by rfl
      _ < ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := thin_set_measure_bound q hq k hk

/-- **The Buczolich–Mauldin Lemma** ([BuMa99, Lemma]).

For each sufficiently large `k` and dyadic scale `ν`, there is an open set
`H ⊆ (2^{ν−1}, 2^ν)` satisfying `I_∞ ⊆ Φ(H)` and `μ(I_F ∩ Φ(H)) < 5 · 2⁻ᵏ`.

The proof constructs `H = bm_shell k ν q` where `q` is obtained from Kronecker's
theorem applied to primes and integers in the appropriate ranges. -/
lemma bm_lemma :
    ∃ K₀ : ℕ, ∀ k, K₀ ≤ k →
      ∃ N_k : ℕ, ∀ ν, N_k ≤ ν →
        ∃ H : Set ℝ,
          IsOpen H ∧
          H ⊆ Ioo ((2 : ℝ) ^ ν / 2) ((2 : ℝ) ^ ν) ∧
          I_inf ⊆ Phi H ∧
          volume (I_F ∩ Phi H) < ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := by
  obtain ⟨K₀, hKr⟩ := bm_approx_data
  refine ⟨max K₀ 7, fun k hk => ?_⟩
  obtain ⟨N_k, hN⟩ := hKr k ((le_max_left K₀ 7).trans hk)
  refine ⟨N_k, fun ν hν => ?_⟩
  obtain ⟨q, hq, h_cover, h_lattice⟩ := hN ν hν
  exact ⟨bm_shell k ν q,
    bm_shell_isOpen k ν q hq,
    bm_shell_subset_dyadic k ν q,
    bm_shell_covers k ν q h_cover,
    bm_shell_shadow_small k ν q hq ((le_max_right K₀ 7).trans hk) h_lattice⟩

/-
Any function `N : ℕ → ℕ` is eventually dominated by a strictly increasing sequence.
-/
lemma exists_strictMono_above (K : ℕ) (N : ℕ → ℕ) :
    ∃ ν : ℕ → ℕ, (∀ i j, K ≤ i → i < j → ν i < ν j) ∧
      ∀ k, K ≤ k → N k ≤ ν k := by
  use fun k => Nat.recOn ( k - K ) ( N K ) fun k ihk => ihk + N ( k + K + 1 ) + 1;
  refine' ⟨ _, _ ⟩;
  · intro i j hi hj; induction hj <;> simp_all +arith +decide;
    · rw [ Nat.succ_sub ( by linarith ) ];
      grind;
    · exact lt_of_lt_of_le ‹_› ( by rw [ Nat.sub_add_comm ( by linarith ) ] ; simp +arith +decide );
  · intro k hk;
    induction hk <;> simp +arith +decide [ * ];
    simp_all +arith +decide [ Nat.succ_sub ( show K ≤ _ from by assumption ), add_comm K ]

/-
Dyadic intervals `(2^n / 2, 2^n)` are disjoint for distinct `n`.
-/
lemma Ioo_dyadic_disjoint {n m : ℕ} (h : n ≠ m) :
    Disjoint (Ioo ((2 : ℝ) ^ n / 2) ((2 : ℝ) ^ n))
      (Ioo ((2 : ℝ) ^ m / 2) ((2 : ℝ) ^ m)) := by
  cases lt_or_gt_of_ne h;
  · refine' Set.disjoint_left.mpr fun x hx₁ hx₂ => _;
    -- Since $n < m$, we have $2^n \leq 2^{m-1}$.
    have h_pow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (m - 1) := by
      exact pow_le_pow_right₀ ( by norm_num ) ( Nat.le_pred_of_lt ‹_› );
    cases m <;> norm_num [ pow_succ' ] at * ; linarith;
  · rw [ Set.disjoint_left ];
    intro x hx₁ hx₂; have := pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( Nat.succ_le_of_lt ‹m < n› ) ; norm_num [ pow_succ' ] at * ; linarith [ hx₁.1, hx₁.2, hx₂.1, hx₂.2 ] ;

/-
Geometric tail bound: `∑_{k ≥ K} 5 · (1/2)^k < μ(I_F) = 1/9` when `K ≥ 7`.
-/
lemma tsum_geometric_lt_I_F {K : ℕ} (hK : 7 ≤ K)
    {a : ℕ → ℝ≥0∞}
    (ha : ∀ k, K ≤ k → a k ≤ ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k))
    (ha0 : ∀ k, k < K → a k = 0) :
    ∑' k, a k < volume I_F := by
  -- Applying the bound on each term to the sum, we get ∑' k, a k ≤ ∑' k, ENNReal.ofReal (5 * (1/2)^k) for k ≥ K.
  have h_sum_le : ∑' k, a k ≤ ∑' k, if k ≥ K then (ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k)) else 0 := by
    apply ENNReal.tsum_le_tsum;
    aesop;
  -- The sum of the geometric series $\sum_{k=K}^{\infty} 5 \cdot (1/2)^k$ is $5 \cdot (1/2)^K / (1 - 1/2) = 10 \cdot (1/2)^K$.
  have h_geo_sum : ∑' k, (if k ≥ K then (ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k)) else 0) = ENNReal.ofReal (10 * (1 / 2 : ℝ) ^ K) := by
    have h_geo_sum : ∑' k, (if k ≥ K then (5 * (1 / 2 : ℝ) ^ k) else 0) = 10 * (1 / 2 : ℝ) ^ K := by
      have h_geo_sum : ∑' k, (if k ≥ K then (5 * (1 / 2 : ℝ) ^ k) else 0) = ∑' k, (5 * (1 / 2 : ℝ) ^ (k + K)) := by
        rw [ ← Summable.sum_add_tsum_nat_add K ];
        · rw [ Finset.sum_eq_zero ] <;> aesop;
        · exact Summable.of_nonneg_of_le ( fun n => by positivity ) ( fun n => by split_ifs <;> norm_num ) ( summable_geometric_two.mul_left 5 );
      convert h_geo_sum using 1 ; ring_nf;
      rw [ tsum_mul_right, tsum_mul_left, tsum_geometric_of_lt_one ] <;> ring_nf <;> norm_num;
    rw [ ← h_geo_sum, ENNReal.ofReal_tsum_of_nonneg ];
    · exact tsum_congr fun n => by split_ifs <;> norm_num;
    · intro n; split_ifs <;> positivity;
    · exact ( by contrapose! h_geo_sum; erw [ tsum_eq_zero_of_not_summable h_geo_sum ] ; positivity );
  refine lt_of_le_of_lt h_sum_le <| h_geo_sum ▸ ?_;
  rw [ show I_F = Set.Ioo ( 8 / 9 ) 1 by rfl, Real.volume_Ioo ] ; norm_num;
  rw [ ← ENNReal.toReal_lt_toReal ] <;> norm_num;
  · exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) hK ) ( by norm_num ) ) ( by norm_num );
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top ( ENNReal.pow_ne_top <| ENNReal.ofReal_ne_top )

/-- **Disjoint shells** — the key construction for the counterexample.

There exist pairwise disjoint open sets `H k` (for `k ≥ K`) such that:
- every `x ∈ I_∞` belongs to `Φ(H k)` for each `k ≥ K`,
- the total measure `∑_k μ(I_F ∩ Φ(H k))` is strictly less than `μ(I_F)`.

**Proof.** Apply the BM Lemma to obtain shells `H₀ k ⊆ (2^{ν(k)−1}, 2^{ν(k)})`
in distinct dyadic intervals (via a strictly increasing choice of `ν`). Pairwise
disjointness follows from the shells lying in non-overlapping dyadic intervals;
the measure bound follows from a geometric series comparison. -/
lemma disjoint_shells :
    ∃ (K : ℕ) (H : ℕ → Set ℝ),
      (∀ k, k < K → H k = ∅) ∧
      (∀ k, K ≤ k → IsOpen (H k)) ∧
      (Pairwise fun i j => Disjoint (H i) (H j)) ∧
      (∀ k, K ≤ k → I_inf ⊆ Phi (H k)) ∧
      ∑' k, volume (I_F ∩ Phi (H k)) < volume I_F := by
  -- Step 1: Apply the BM Lemma
  obtain ⟨K₀, hBM⟩ := bm_lemma
  -- Step 2: Set K large enough for both the BM construction and the geometric sum bound
  set K := max K₀ 7
  -- Step 3: Uniformly choose thresholds N_k for all k
  have hN_ex : ∀ k, ∃ Nk : ℕ, K ≤ k → ∀ ν, Nk ≤ ν →
      ∃ H : Set ℝ, IsOpen H ∧ H ⊆ Ioo ((2 : ℝ) ^ ν / 2) ((2 : ℝ) ^ ν) ∧
        I_inf ⊆ Phi H ∧
        volume (I_F ∩ Phi H) < ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := by
    intro k
    by_cases hk : K ≤ k
    · exact let ⟨Nk, hNk⟩ := hBM k ((le_max_left K₀ 7).trans hk); ⟨Nk, fun _ => hNk⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose N hN using hN_ex
  -- Step 4: Choose ν strictly increasing above N
  obtain ⟨ν, hν_strict, hν_ge⟩ := exists_strictMono_above K N
  -- Step 5: Construct individual shells
  have hH_ex : ∀ k, ∃ Hk : Set ℝ, K ≤ k →
      IsOpen Hk ∧ Hk ⊆ Ioo ((2 : ℝ) ^ ν k / 2) ((2 : ℝ) ^ ν k) ∧
        I_inf ⊆ Phi Hk ∧
        volume (I_F ∩ Phi Hk) < ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := by
    intro k
    by_cases hk : K ≤ k
    · exact let ⟨Hk, hHk⟩ := hN k hk (ν k) (hν_ge k hk); ⟨Hk, fun _ => hHk⟩
    · exact ⟨∅, fun h => absurd h hk⟩
  choose H₀ hH₀ using hH_ex
  -- Step 6: Assemble: H k = ∅ for k < K, H₀ k for k ≥ K
  let H : ℕ → Set ℝ := fun k => if K ≤ k then H₀ k else ∅
  have hH_pos : ∀ k, K ≤ k → H k = H₀ k := fun k hk => if_pos hk
  have hH_neg : ∀ k, ¬ K ≤ k → H k = ∅ := fun k hk => if_neg hk
  refine ⟨K, H, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) Empty below K
    intro k hk; exact hH_neg k (not_le.mpr hk)
  · -- (2) Open above K
    intro k hk; rw [hH_pos k hk]; exact (hH₀ k hk).1
  · -- (3) Pairwise disjoint
    intro i j hij
    by_cases hi : K ≤ i <;> by_cases hj : K ≤ j
    · rw [hH_pos i hi, hH_pos j hj]
      exact (Ioo_dyadic_disjoint (by
        intro heq; rcases lt_or_gt_of_ne hij with h | h
        · exact absurd heq (ne_of_lt (hν_strict i j hi h))
        · exact absurd heq.symm (ne_of_lt (hν_strict j i hj h))
      )).mono (hH₀ i hi).2.1 (hH₀ j hj).2.1
    · rw [hH_neg j hj]; exact disjoint_bot_right
    · rw [hH_neg i hi]; exact disjoint_bot_left
    · rw [hH_neg i hi]; exact disjoint_bot_left
  · -- (4) Covering
    intro k hk; rw [hH_pos k hk]; exact (hH₀ k hk).2.2.1
  · -- (5) Tsum bound
    have ha : ∀ k, K ≤ k → volume (I_F ∩ Phi (H k)) ≤
        ENNReal.ofReal (5 * (1 / 2 : ℝ) ^ k) := by
      intro k hk; rw [hH_pos k hk]; exact le_of_lt (hH₀ k hk).2.2.2
    have ha0 : ∀ k, k < K → volume (I_F ∩ Phi (H k)) = 0 := by
      intro k hk; rw [hH_neg k (not_le.mpr hk), Phi_empty, Set.inter_empty, measure_empty]
    exact tsum_geometric_lt_I_F (le_max_right K₀ 7) ha ha0

/-! ## Helper lemmas about `Phi` -/

/-
`Φ` distributes over countable unions (subset direction):
    `Φ(⋃ k, H k) ⊆ ⋃ k, Φ(H k)`.
-/
lemma Phi_subset_iUnion (H : ℕ → Set ℝ) :
    Phi (⋃ k, H k) ⊆ ⋃ k, Phi (H k) := by
  intro x hx;
  simp_all +decide [ Phi ];
  tauto

/-
`Φ(A)` is measurable when `A` is measurable.
    Indeed, `Φ(A) = [1/2,1) ∩ ⋃_{m≥1} (· * m)⁻¹'(A)`.
-/
lemma Phi_measurableSet {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (Phi A) := by
  refine' MeasurableSet.inter _ _;
  · exact measurableSet_Ico;
  · -- The set {x | ∃ m, 0 < m ∧ (m : ℝ) * x ∈ A} can be written as the union over all m ≥ 1 of the preimage of A under the function x ↦ mx.
    have h_union : {x : ℝ | ∃ m : ℕ, 0 < m ∧ (m : ℝ) * x ∈ A} = ⋃ m : ℕ, ⋃ hm : 0 < m, (fun x => (m : ℝ) * x) ⁻¹' A := by
      aesop;
    exact h_union ▸ MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun hm => measurable_const.mul measurable_id hA

/-! ## Interval arithmetic lemmas -/

/-
`I_F = (8/9, 1) ⊆ [1/2, 1)`.
-/
lemma I_F_subset_Ico : I_F ⊆ Ico (1/2 : ℝ) 1 := by
  exact Set.Ioo_subset_Ico_self.trans ( Set.Ico_subset_Ico ( by norm_num ) ( by norm_num ) )

/-
`I_F = (8/9, 1)` has positive measure.
-/
lemma I_F_volume_pos : 0 < volume I_F := by
  erw [ Real.volume_Ioo ] ; norm_num

/-
`I_F = (8/9, 1)` has finite measure.
-/
lemma I_F_volume_ne_top : volume I_F ≠ ⊤ := by
  erw [ Real.volume_Ioo ] ; norm_num

/-! ## Core lemmas of the counterexample construction -/

/-
`F` and `MultSat(I_F \ Φ(F))` are disjoint.
    If `y ∈ F ∩ MultSat(I_F \ Φ(F))`, then `y = r·e` with `e ∈ I_F \ Φ(F)`.
    Since `e ∈ I_F ⊆ [1/2,1)` and `r·e = y ∈ F`, we get `e ∈ Φ(F)`, contradicting `e ∉ Φ(F)`.
-/
lemma F_disjoint_MultSat (F : Set ℝ) :
    Disjoint F (MultSat (I_F \ Phi F)) := by
  unfold MultSat;
  simp +decide [ Phi, Set.disjoint_left ];
  intro y hy n hn x hx h; exact fun hxy => h ( by linarith [ Set.mem_Ioo.mp hx ] ) ( by linarith [ Set.mem_Ioo.mp hx ] ) n hn <| hxy ▸ hy;

/-
If `x ∈ Φ(H k)` for all `k ≥ K` and the `H k` are pairwise disjoint,
    then `{n : n·x ∈ ⋃ H k}` is infinite.
    The witnesses `m_k` from `Φ(H k)` are distinct because `H k` are disjoint.
-/
lemma inf_many_hits (x : ℝ) (K : ℕ) (H : ℕ → Set ℝ)
    (h_cover : ∀ k, K ≤ k → x ∈ Phi (H k))
    (h_disj : Pairwise fun i j => Disjoint (H i) (H j)) :
    {n : ℕ | 0 < n ∧ ((n : ℝ) * x) ∈ ⋃ k, H k}.Infinite := by
  -- By assumption, $x \in \Phi(H_k)$ for all $k \ge K$, so there exists $m_k \ge 1$ such that $m_k * x \in H_k$.
  have h_exists_mk : ∀ k, K ≤ k → ∃ m_k : ℕ, 0 < m_k ∧ m_k * x ∈ H k := by
    exact fun k hk => by rcases h_cover k hk |>.2 with ⟨ m, hm₁, hm₂ ⟩ ; exact ⟨ m, hm₁, hm₂ ⟩ ;
  choose! m hm₁ hm₂ using h_exists_mk;
  -- The function $k \mapsto m_k$ is injective on $\{k | K \le k\}$.
  have h_inj : Set.InjOn m (Set.Ici K) := by
    intro k hk l hl hkl; have := hm₂ k hk; have := hm₂ l hl; simp_all +decide [ Set.disjoint_left ] ;
    exact Classical.not_not.1 fun h => h_disj h this ( hm₂ l hl );
  exact Set.infinite_of_injective_forall_mem ( fun i j hij => by have := h_inj ( by norm_num : K ≤ K + i ) ( by norm_num : K ≤ K + j ) hij; aesop ) fun n => ⟨ hm₁ _ ( by linarith ), Set.mem_iUnion.mpr ⟨ _, hm₂ _ ( by linarith ) ⟩ ⟩

/-
`E = I_F \ Φ(⋃ H k)` has positive measure when the shadows `Φ(H k)` are small.
    Uses `Φ(⋃ H k) ⊆ ⋃ Φ(H k)`, measure subadditivity, and the hypothesis
    `∑ μ(I_F ∩ Φ(H k)) < μ(I_F)`.
-/
lemma E_pos_measure (H : ℕ → Set ℝ)
    (hH_meas : ∀ k, MeasurableSet (H k))
    (h_sum : ∑' k, volume (I_F ∩ Phi (H k)) < volume I_F) :
    0 < volume (I_F \ Phi (⋃ k, H k)) := by
  have h_diff : volume (I_F \ Phi (⋃ k, H k)) = volume I_F - volume (I_F ∩ Phi (⋃ k, H k)) := by
    rw [ ← MeasureTheory.measure_diff ];
    · aesop;
    · exact Set.inter_subset_left;
    · refine' MeasurableSet.nullMeasurableSet _;
      refine' MeasurableSet.inter ( measurableSet_Ioo ) _;
      apply_rules [ Phi_measurableSet, MeasurableSet.iUnion ];
    · exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) ( by erw [ Real.volume_Ioo ] ; norm_num ) );
  have h_subadd : volume (I_F ∩ Phi (⋃ k, H k)) ≤ ∑' k, volume (I_F ∩ Phi (H k)) := by
    refine' le_trans ( MeasureTheory.measure_mono _ ) _;
    exact ⋃ k, I_F ∩ Phi ( H k );
    · exact fun x hx => by rcases hx.2.2 with ⟨ m, hm, hm' ⟩ ; rcases Set.mem_iUnion.1 hm' with ⟨ k, hk ⟩ ; exact Set.mem_iUnion.2 ⟨ k, ⟨ hx.1, ⟨ hx.2.1, m, hm, hk ⟩ ⟩ ⟩ ;
    · exact MeasureTheory.measure_iUnion_le _;
  exact h_diff.symm ▸ tsub_pos_of_lt ( lt_of_le_of_lt h_subadd h_sum )

/-! ## Main theorem -/

/-
**Negative answer to the eventual covering question.**

There exists a measurable set `E ⊂ (0,∞)` of positive Lebesgue measure such that
for every `x ∈ [16/25, 2/3]`, there are infinitely many positive integers `n` for which
`x ∉ (r/n)·E` for every positive integer `r`.

In particular, it is _not_ true that for every positive-measure `E ⊂ (0,∞)`,
for a.e. `x > 0`, for all sufficiently large `n`, there exists `r ≥ 1` with `x ∈ (r/n)·E`.
-/
theorem negative_answer :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Ioi 0 ∧ 0 < volume E ∧
      ∀ x ∈ I_inf,
        {n : ℕ | 0 < n ∧ ∀ r : ℕ, 0 < r →
          ¬∃ e ∈ E, x = ((r : ℝ) / (n : ℝ)) * e}.Infinite := by
  -- Set F := ⋃ k, H k, E := I_F \ Phi F.
  obtain ⟨K, H, hH_empty, hH_open, hH_disj, hH_cover, hH_sum⟩ := disjoint_shells;
  set F := ⋃ k, H k;
  set E := I_F \ Phi F;
  refine' ⟨ E, _, _, _, _ ⟩;
  · apply_rules [ MeasurableSet.diff, measurableSet_Ioo, Phi_measurableSet ];
    exact MeasurableSet.iUnion fun k => if hk : k < K then by aesop else hH_open k ( le_of_not_gt hk ) |> IsOpen.measurableSet;
  · exact fun x hx => hx.1.1.trans_le' <| by norm_num;
  · convert E_pos_measure H _ hH_sum;
    exact fun k => if hk : k < K then by aesop else hH_open k ( le_of_not_gt hk ) |> IsOpen.measurableSet;
  · intro x hx
    have h_inf : {n : ℕ | 0 < n ∧ (n : ℝ) * x ∈ F}.Infinite := by
      exact inf_many_hits x K H ( fun k hk => hH_cover k hk hx ) hH_disj;
    refine' h_inf.mono _;
    intro n hn
    obtain ⟨hn_pos, hn_F⟩ := hn
    use hn_pos
    intro r hr ⟨e, he_E, he_eq⟩
    have h_contra : (n : ℝ) * x ∈ MultSat E := by
      use r;
      exact ⟨ hr, e, he_E, by rw [ he_eq, div_mul_eq_mul_div, mul_div_cancel₀ _ ( by positivity ) ] ⟩;
    exact absurd ( F_disjoint_MultSat F ) ( Set.not_disjoint_iff_nonempty_inter.mpr ⟨ _, hn_F, h_contra ⟩ )

/-- **Erdős Problem 1197.** The conjecture is **false** in the negative form: it is *not*
the case that for every measurable `E ⊂ (0, ∞)` of positive Lebesgue measure, for almost
every `x > 0` there exists a threshold `N` past which some `r ≥ 1` satisfies `n·x ∈ r·E`.
Counterexample: take `E` from `negative_answer`; then for *every* `x` in the
positive-measure interval `[16/25, 2/3] ⊂ (0, ∞)`, no such `N` exists. -/
theorem erdos_1197 :
    ¬ ∀ (E : Set ℝ), MeasurableSet E → E ⊆ Set.Ioi 0 → 0 < MeasureTheory.volume E →
      ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
          ∃ r : ℕ, 0 < r ∧ ∃ e ∈ E, (n : ℝ) * x = (r : ℝ) * e := by
  intro h
  obtain ⟨E, hE_meas, hE_sub, hE_pos, hE_bad⟩ := negative_answer
  have h_ae := h E hE_meas hE_sub hE_pos
  -- Every `x ∈ [16/25, 2/3]` is a counterexample to the inner condition.
  have h_bad_on_Icc :
      ∀ x ∈ Set.Icc (16/25 : ℝ) (2/3),
        ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
          ∃ r : ℕ, 0 < r ∧ ∃ e ∈ E, (n : ℝ) * x = (r : ℝ) * e := by
    intro x hx
    rintro ⟨N, hN⟩
    have h_inf := hE_bad x hx
    rcases h_inf.exists_gt N with ⟨n, ⟨hn_pos, hn_bad⟩, hn_gt⟩
    have hcov := hN n hn_gt.le hn_pos
    obtain ⟨r, hr_pos, e, he, hex⟩ := hcov
    apply hn_bad r hr_pos
    refine ⟨e, he, ?_⟩
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
    field_simp
    linarith [hex]
  -- The bad set has measure ≥ measure of `[16/25, 2/3]` = `2/75` under the restricted measure.
  rw [MeasureTheory.ae_iff] at h_ae
  set μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have h_sub : Set.Icc (16/25 : ℝ) (2/3) ⊆ {x | ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      ∃ r : ℕ, 0 < r ∧ ∃ e ∈ E, (n : ℝ) * x = (r : ℝ) * e} := h_bad_on_Icc
  have h_mono : μ (Set.Icc (16/25 : ℝ) (2/3)) ≤ μ {x | _} :=
    MeasureTheory.measure_mono h_sub
  -- `μ [16/25, 2/3] = 2/75 > 0`.
  have h_icc_pos : 0 < μ (Set.Icc (16/25 : ℝ) (2/3)) := by
    have h_inter : Set.Icc (16/25 : ℝ) (2/3) ∩ Set.Ioi 0 = Set.Icc (16/25) (2/3) := by
      apply Set.inter_eq_left.mpr
      intro y hy
      exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 16/25) hy.1
    rw [show μ = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) from rfl,
       MeasureTheory.Measure.restrict_apply measurableSet_Icc, h_inter,
       Real.volume_Icc]
    rw [show (2 / 3 - 16 / 25 : ℝ) = 2 / 75 from by norm_num]
    rw [ENNReal.ofReal_pos]
    norm_num
  rw [h_ae] at h_mono
  exact absurd (lt_of_lt_of_le h_icc_pos h_mono) (lt_irrefl _)

end

#print axioms erdos_1197
-- 'Erdos1197.erdos_1197' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1197
