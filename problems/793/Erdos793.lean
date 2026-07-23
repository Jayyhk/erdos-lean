import Mathlib

namespace Erdos793

set_option maxHeartbeats 4000000

/-! ## --- vendored: Mathlib/Algebra/Notation/Support.lean --- -/

section Mathlib_Algebra_Notation_Support

variable {α : Type*} [Zero α]

end Mathlib_Algebra_Notation_Support

/-! ## --- vendored: SmoothExistence.lean --- -/

section SmoothExistence


set_option lang.lemmaCmd true

open _root_.MeasureTheory _root_.Set _root_.Real
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


open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap  _root_.BigOperators
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


open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction
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


open _root_.ArithmeticFunction hiding log
open _root_.Nat hiding log
open _root_.Finset _root_.Topology
open _root_.BigOperators _root_.Filter _root_.Real _root_.Classical _root_.Asymptotics
open _root_.MeasureTheory _root_.intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev


end Defs

/-! ## --- vendored: Mathlib/Analysis/SpecialFunctions/Log/Basic.lean --- -/

section Mathlib_Analysis_SpecialFunctions_Log_Basic


open _root_.Filter _root_.Real

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

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem _root_.Asymptotics.IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Mathlib_Analysis_Asymptotics_Asymptotics

/-! ## --- vendored: Wiener.lean --- -/

section Wiener


set_option lang.lemmaCmd true
set_option linter.style.header false

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open _root_.Real _root_.BigOperators _root_.ArithmeticFunction _root_.MeasureTheory _root_.Filter _root_.Set _root_.FourierTransform _root_.LSeries
  _root_.Asymptotics _root_.SchwartzMap
open _root_.Complex hiding log
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
-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

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
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1

lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact h.congr_atTop huv
  · exact h.congr_atTop huv.symm

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

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

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

open _root_.ArithmeticFunction hiding log
open _root_.Nat hiding log
open _root_.Finset
open _root_.BigOperators _root_.Filter _root_.Real _root_.Classical _root_.Asymptotics _root_.MeasureTheory _root_.intervalIntegral
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

end Consequences

/-! ## --- Erdős Problem 793 formalization --- -/


/-!
Let `F(n)` be the maximum possible size of a subset `A ⊆ {1, …, n}` such that
`a ∤ bc` whenever `a,b,c ∈ A` with `a ≠ b` and `a ≠ c`. Erdős proved that there
exist constants `c₁, c₂ > 0` such that

`c₁ n^{2/3}/(log n)² ≤ F(n) - π(n) ≤ c₂ n^{2/3}/(log n)²`

P. Erdős, On sequences of integers no one of which divides the product of two
others and on related problems. Tomsk. Gos. Univ. Ucen Zap. (1938), 74-82.

He then asked whether the limit `lim_{n→∞} (F(n) - π(n)) / (n^{2/3}/(log n)²)`
exists, which is nowadays recorded as Erdős Problem 793
(https://www.erdosproblems.com/793).

This was resolved by GPT-5.6 Sol Ultra and the solution can be found in a
preprint posted by Przemek Chojecki.

https://www.ulam.ai/research/erdos793.pdf

Below you can find a formalization of this result, which was obtained by
Aristotle (aristotle-harmonic@harmonic.fun), the formal reasoning tool developed
by Harmonic.

The formalization is self-contained, except for the prime number theorem,
introduced as `pi_alt`.
-/

set_option maxHeartbeats 1000000

namespace Strongly2

open scoped BigOperators
open _root_.Filter _root_.Real
open scoped Topology

/-- A finite set `A ⊆ ℕ` is *strongly 2-primitive* if, for every `a, b, c ∈ A`
with `a ≠ b` and `a ≠ c`, we have `a ∤ b * c`. -/
def Strongly2Primitive (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → ¬ a ∣ b * c

open Classical in
/-- The extremal function: the maximal cardinality of a strongly 2-primitive
subset of `[n] = {1, …, n}`. -/
noncomputable def F (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter Strongly2Primitive).sup Finset.card

open Classical in
/-- Any strongly 2-primitive subset of `[n]` has cardinality at most `F n`. -/
lemma card_le_F (n : ℕ) (A : Finset ℕ) (hsub : A ⊆ Finset.Icc 1 n)
    (hA : Strongly2Primitive A) : A.card ≤ F n := by
  refine' Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hsub, hA ⟩ )

/-- The normalizing quantity `S(n) = n^{2/3} / (log n)^2`. -/
noncomputable def S (n : ℕ) : ℝ := (n : ℝ) ^ ((2:ℝ)/3) / (Real.log n)^2

/-
If every element `a` of a finite strongly 2-primitive set `A` is written as a
product `a = u a * v a` of two elements of a finite set `B`, then `|A| ≤ |B|`.
-/
lemma private_factor (A B : Finset ℕ) (u v : ℕ → ℕ)
    (hu : ∀ a ∈ A, u a ∈ B) (hv : ∀ a ∈ A, v a ∈ B)
    (hfac : ∀ a ∈ A, a = u a * v a)
    (hA : Strongly2Primitive A) : A.card ≤ B.card := by
  -- For `a ∈ A` and `x ∈ B`, let `μ a x = (if u a = x then 1 else 0) + (if v a = x then 1 else 0) : ℕ`, a value in `{0,1,2}`.
  set mu : ℕ → ℕ → ℕ := fun a x => (if u a = x then 1 else 0) + (if v a = x then 1 else 0);
  -- Claim: for each `a ∈ A` there exists `x ∈ B` such that for all `b ∈ A` with `b ≠ a`, `μ b x < μ a x`. Call such `x` a private coordinate for `a`.
  have h_private : ∀ a ∈ A, ∃ x ∈ B, ∀ b ∈ A, b ≠ a → mu b x < mu a x := by
    intro a ha
    by_cases huv : u a = v a;
    · grind +splitIndPred;
    · -- Suppose neither `u a` nor `v a` is private. Not-private for `u a` means there is `b ≠ a` in `A` with `μ b (u a) ≥ μ a (u a) = 1`, i.e. `u a ∈ {u b, v b}`.
      by_contra h_not_private
      push Not at h_not_private
      obtain ⟨b, hb₁, hb₂⟩ : ∃ b ∈ A, b ≠ a ∧ u a ∈ ({u b, v b} : Finset ℕ) := by
        grind +splitImp
      obtain ⟨c, hc₁, hc₂⟩ : ∃ c ∈ A, c ≠ a ∧ v a ∈ ({u c, v c} : Finset ℕ) := by
        grind;
      -- Then `a = u a * v a` divides `(u b * v b) * (u c * v c) = b * c` (since `u a ∣ b` and `v a ∣ c`, using `a = b`,`a=c` factorizations `hfac`).
      have h_div : a ∣ b * c := by
        rw [ hfac a ha, hfac b hb₁, hfac c hc₁ ];
        norm_num at *;
        rcases hb₂.2 with ( h | h ) <;> rcases hc₂.2 with ( j | j ) <;> rw [ h, j ] <;> ring_nf;
        · exact dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _;
        · exact dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _;
        · exact ⟨ u b * v c, by ring ⟩;
        · exact dvd_mul_of_dvd_left ( dvd_mul_right _ _ ) _;
      exact hA a ha b hb₁ c hc₁ ( by tauto ) ( by tauto ) h_div;
  choose! x hx₁ hx₂ using h_private;
  have h_inj : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → x a ≠ x b := by
    grind;
  exact Finset.card_le_card ( show A.image x ⊆ B from Finset.image_subset_iff.mpr hx₁ ) |> le_trans ( by rw [ Finset.card_image_of_injOn fun a ha b hb hab => by contrapose! hab; exact h_inj a ha b hb hab ] )

/-- A finite set `B` is a *two-factor basis for `[n]`* if every `m ∈ [n]` is a
product of two elements of `B`. -/
def TwoFactorBasis (B : Finset ℕ) (n : ℕ) : Prop :=
  ∀ m ∈ Finset.Icc 1 n, ∃ u ∈ B, ∃ v ∈ B, m = u * v

/-
If `B` is a finite two-factor basis for `[n]`, then every strongly 2-primitive
`A ⊆ [n]` satisfies `|A| ≤ |B|`.
-/
lemma basis_bound (B : Finset ℕ) (n : ℕ) (hB : TwoFactorBasis B n)
    (A : Finset ℕ) (hAsub : A ⊆ Finset.Icc 1 n) (hA : Strongly2Primitive A) :
    A.card ≤ B.card := by
  convert private_factor _ _ _ _ _ _ _ _;
  exact fun a => if h : a ∈ A then Classical.choose ( hB a ( hAsub h ) ) else 1;
  exact fun a => if h : a ∈ A then Classical.choose ( Classical.choose_spec ( hB a ( hAsub h ) ) |>.2 ) else 1;
  · intro a ha; have := Classical.choose_spec ( hB a ( hAsub ha ) ) ; aesop;
  · grind +splitImp;
  · grind;
  · assumption

/-
Consequently `F n ≤ |B|` for any two-factor basis `B` of `[n]`.
-/
lemma F_le_basis_card (B : Finset ℕ) (n : ℕ) (hB : TwoFactorBasis B n) :
    F n ≤ B.card := by
  -- Apply `Finset.sup_le` to the set of all strong 2-primitive subsets of `[n]`.
  apply Finset.sup_le;
  intro A hA;
  simp +zetaDelta at *;
  exact basis_bound B n hB A hA.1 hA.2

/-! ## Analytic preliminaries from the prime number theorem -/

/-- The prime number theorem hypothesis (the permitted analytic input): there is
an error function `c = o(1)` with `π(⌊x⌋) = (1 + c x)·x / log x` for all `x`.

This is stated as a `Prop` and threaded as a hypothesis through the analytic
lemmas; it is discharged once via `pi_alt`. -/
def PNT : Prop := ∃ c : ℝ → ℝ, c =o[Filter.atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, (Nat.primeCounting ⌊x⌋₊ : ℝ) = (1 + c x) * x / Real.log x

/-
Reformulation of the PNT hypothesis with the error term expressed as a
limit.
-/
lemma exists_pnt_error (hpnt : PNT) :
    ∃ c : ℝ → ℝ, Tendsto c atTop (𝓝 0) ∧
      ∀ x : ℝ, (Nat.primeCounting ⌊x⌋₊ : ℝ) = (1 + c x) * x / log x := by
  obtain ⟨c, hc, hform⟩ := hpnt;
  exact ⟨ c, by simpa using hc.tendsto_div_nhds_zero, hform ⟩

/-
The prime-counting function is bounded by its argument.
-/
lemma primeCounting_le_self (n : ℕ) : Nat.primeCounting n ≤ n := by
  convert Nat.le_of_lt_succ _;
  rw [ Nat.primeCounting ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
  exact lt_of_lt_of_le ( Finset.card_lt_card <| Finset.filter_ssubset.mpr <| ⟨ 0, by norm_num ⟩ ) <| by norm_num;

/-
The number of primes in `(a, b]` is `π(b) - π(a)`.
-/
lemma card_primes_Ioc (a b : ℕ) (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card = Nat.primeCounting b - Nat.primeCounting a := by
  have h_card_split : (Finset.filter Nat.Prime (Finset.Ioc a b)).card = (Finset.filter Nat.Prime (Finset.Icc 1 b)).card - (Finset.filter Nat.Prime (Finset.Icc 1 a)).card := by
    rw [ show Finset.filter Nat.Prime ( Finset.Ioc a b ) = Finset.filter Nat.Prime ( Finset.Icc 1 b ) \ Finset.filter Nat.Prime ( Finset.Icc 1 a ) from ?_, Finset.card_sdiff ];
    · rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right hab ) ];
    · grind;
  rw [ h_card_split, Nat.primeCounting, Nat.primeCounting ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range ];
  congr 2 <;> ext x <;> simp +arith +decide;
  · exact fun hx _ => hx.pos;
  · exact fun _ _ => Nat.Prime.pos ‹_›

/-- `π(⌊x⌋) ≤ x` for `x ≥ 0`. -/
lemma piR_le (x : ℝ) (hx : 0 ≤ x) : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x := by
  calc (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
            exact_mod_cast primeCounting_le_self _
    _ ≤ x := Nat.floor_le hx

/-
For every fixed `c > 0`, `π(⌊c·x⌋)·log x / x → c` as `x → ∞`.
-/
lemma pi_mul_ratio (hpnt : PNT) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊c * x⌋₊ : ℝ) * log x / x) atTop (𝓝 c) := by
  obtain ⟨ e, he₁, he₂ ⟩ := exists_pnt_error hpnt;
  -- Substitute the expression for $\pi(\lfloor c \cdot x \rfloor)$ into the limit.
  suffices h_subst : Filter.Tendsto (fun x => ((1 + e (c * x)) * (c * x) / Real.log (c * x)) * Real.log x / x) Filter.atTop (𝓝 c) by
    grind;
  -- Simplify the expression inside the limit.
  suffices h_simp : Filter.Tendsto (fun x => (1 + e (c * x)) * c * (Real.log x / Real.log (c * x))) Filter.atTop (𝓝 c) by
    refine h_simp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ eq_div_iff hx.ne' ] ; ring );
  -- We'll use the fact that $\frac{\log x}{\log (c x)} = \frac{\log x}{\log c + \log x} \to 1$ as $x \to \infty$.
  have h_log_ratio : Filter.Tendsto (fun x => Real.log x / (Real.log c + Real.log x)) Filter.atTop (nhds 1) := by
    -- We can divide the numerator and the denominator by $\log x$.
    suffices h_div : Filter.Tendsto (fun x => 1 / (Real.log c / Real.log x + 1)) Filter.atTop (nhds 1) by
      refine h_div.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ div_add_one, div_div_eq_mul_div ] ; ring ; linarith [ Real.log_pos hx ] );
    exact le_trans ( tendsto_const_nhds.div ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) tendsto_const_nhds ) ( by norm_num ) ) ( by norm_num );
  simpa using Filter.Tendsto.mul ( Filter.Tendsto.mul ( tendsto_const_nhds.add ( he₁.comp ( Filter.tendsto_id.const_mul_atTop hc ) ) ) tendsto_const_nhds ) ( h_log_ratio.congr' <| by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.log_mul hc.ne' hx.ne' ] ) |> fun h => h.trans <| by norm_num;

/-- Basic prime number theorem: `π(⌊x⌋)·log x / x → 1`. -/
lemma pnt (hpnt : PNT) :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * log x / x) atTop (𝓝 1) := by
  have := pi_mul_ratio hpnt 1 one_pos
  simpa using this

/-
There is a constant `C > 0` such that `π(⌊x⌋) ≤ C · x / log x` for every real
`x ≥ 2`.
-/
lemma pi_upper (hpnt : PNT) : ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 2 ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ C * x / log x := by
  -- Set `C = max 2 (Real.log x₀)` (note `Real.log x₀ ≥ Real.log 2 > 0` since `x₀ ≥ 2`, so `C > 0`).
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) * (Real.log x) / x ≤ 2 := by
    obtain ⟨ x₀, hx₀ ⟩ := Metric.tendsto_atTop.mp ( pnt hpnt ) 1 zero_lt_one;
    exact ⟨ Max.max x₀ 2, le_max_right _ _, fun x hx => by linarith [ abs_lt.mp ( hx₀ x ( le_trans ( le_max_left _ _ ) hx ) ) ] ⟩;
  have h_log_x₀ : Real.log x₀ > 0 := by
    exact Real.log_pos <| by linarith;
  refine' ⟨ Max.max 2 ( Real.log x₀ ), _, _ ⟩ <;> norm_num;
  intro x hx; rw [ le_div_iff₀ ( Real.log_pos <| by linarith ) ] ; cases le_total x x₀ <;> simp_all +decide [ mul_div_assoc ] ;
  · refine' le_trans ( mul_le_mul_of_nonneg_right ( show ( Nat.primeCounting ⌊x⌋₊ : ℝ ) ≤ x from _ ) ( Real.log_nonneg <| by linarith ) ) _;
    · exact piR_le x ( by linarith );
    · nlinarith [ le_max_left 2 ( Real.log x₀ ), le_max_right 2 ( Real.log x₀ ), Real.log_le_log ( by linarith ) ( by linarith : x ≤ x₀ ) ];
  · have := hx₀.2 x ‹_›; rw [ mul_div, div_le_iff₀ ( by linarith ) ] at this; nlinarith [ le_max_left 2 ( Real.log x₀ ), le_max_right 2 ( Real.log x₀ ) ] ;

/-- Sum of reciprocal squares of the primes in the real interval `(x, A·x]`. -/
noncomputable def primeSqSum (x A : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊A * x⌋₊).filter Nat.Prime, (1 / (p : ℝ) ^ 2)

/-
For fixed `0 < c ≤ d`, the number of primes in `(cx, dx]`, times `log x / x`,
tends to `d - c`.
-/
lemma pi_diff_ratio (hpnt : PNT) (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d) :
    Tendsto (fun x : ℝ =>
      (((Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊).filter Nat.Prime).card : ℝ) * log x / x)
      atTop (𝓝 (d - c)) := by
  convert Tendsto.sub ( pi_mul_ratio hpnt d ( by linarith ) ) ( pi_mul_ratio hpnt c hc ) |> Filter.Tendsto.congr' _ using 2;
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx;
  rw [ card_primes_Ioc _ _ ( Nat.floor_mono <| by nlinarith ) ];
  rw [ Nat.cast_sub ( Nat.monotone_primeCounting <| Nat.floor_mono <| by nlinarith ) ] ; ring

/-
For `0 < c ≤ d` and `x > 0`, the reciprocal-square sum over primes in `(cx, dx]`
is between `cnt/(dx)²` and `cnt/(cx)²`, where `cnt` is the number of such
primes.
-/
lemma primeSq_block_bounds (c d x : ℝ) (hc : 0 < c) (hcd : c ≤ d) (hx : 0 < x) :
    (((Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊).filter Nat.Prime).card : ℝ) / (d * x) ^ 2 ≤
        (∑ p ∈ (Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊).filter Nat.Prime, (1 / (p : ℝ) ^ 2)) ∧
    (∑ p ∈ (Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊).filter Nat.Prime, (1 / (p : ℝ) ^ 2)) ≤
        (((Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊).filter Nat.Prime).card : ℝ) / (c * x) ^ 2 := by
  constructor;
  · -- Since $p \leq \lfloor d * x \rfloor$, we have $p^2 \leq (\lfloor d * x \rfloor)^2$.
    have h_prime_sq_le : ∀ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊), (p : ℝ) ^ 2 ≤ (d * x) ^ 2 := by
      exact fun p hp => pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( le_trans ( Nat.cast_le.mpr <| Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ) <| Nat.floor_le <| by nlinarith ) _;
    exact le_trans ( by norm_num [ div_eq_mul_inv ] ) ( Finset.sum_le_sum fun p hp => one_div_le_one_div_of_le ( sq_pos_of_pos <| Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2 ) <| h_prime_sq_le p hp );
  · -- Apply the bound to each term in the sum.
    have h_term_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊c * x⌋₊ ⌊d * x⌋₊), (1 / (p : ℝ) ^ 2) ≤ (1 / (c * x) ^ 2) := by
      intro p hp; gcongr ; nlinarith [ Nat.lt_of_floor_lt ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) ] ;
    simpa using Finset.sum_le_sum h_term_bound

/-
Telescoping split of a filtered `Ioc`-sum along a monotone partition.
-/
lemma sum_Ioc_filter_split {M : Type*} [AddCommMonoid M] (a : ℕ → ℕ) (ha : Monotone a)
    (P : ℕ → Prop) [DecidablePred P] (f : ℕ → M) (K : ℕ) :
    ∑ j ∈ Finset.range K, ∑ p ∈ (Finset.Ioc (a j) (a (j + 1))).filter P, f p
      = ∑ p ∈ (Finset.Ioc (a 0) (a K)).filter P, f p := by
  induction K <;> simp_all +decide [ Finset.sum_range_succ ];
  simp +decide only [Finset.sum_filter];
  rw [ Finset.sum_Ioc_consecutive ] <;> aesop

/-
For fixed `A > 1`, `(∑_{x<p≤Ax} 1/p²)·(x·log x) → 1 - 1/A` as `x → ∞`.
-/
lemma primeSq_interval (hpnt : PNT) (A : ℝ) (hA : 1 < A) :
    Tendsto (fun x : ℝ => primeSqSum x A * (x * log x)) atTop (𝓝 (1 - 1 / A)) := by
  -- Fix `A > 1`. For a partition parameter `K : ℕ`, `K ≥ 1`, set `c j = A ^ ((j:ℝ)/K)` (so `c 0 = 1`, `c K = A`, and `c` is strictly increasing in `j`; let `r = A^(1/K) > 1`, so `c (j+1) = r * c j`). Write `S x = primeSqSum x A * (x * Real.log x)`.
  suffices h_suff : ∀ ε > 0, ∃ K : ℕ, K ≥ 1 ∧ ∃ N : ℝ, ∀ x ≥ N, abs (primeSqSum x A * (x * Real.log x) - (1 - 1 / A)) < ε by
    exact Metric.tendsto_atTop.mpr fun ε hε => by obtain ⟨ K, hK₁, N, hN ⟩ := h_suff ε hε; exact ⟨ N, fun x hx => hN x hx ⟩ ;
  intro ε hε_pos
  obtain ⟨K, hK_pos, hK⟩ : ∃ K : ℕ, K ≥ 1 ∧ (A^(2 / (K : ℝ)) - 1) * (1 - 1 / A) < ε / 2 := by
    have h_lim : Filter.Tendsto (fun K : ℕ => (A^(2 / (K : ℝ)) - 1) * (1 - 1 / A)) Filter.atTop (nhds 0) := by
      exact le_trans ( Filter.Tendsto.mul ( Filter.Tendsto.sub ( tendsto_const_nhds.rpow ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) ( Or.inl <| by linarith ) ) tendsto_const_nhds ) tendsto_const_nhds ) ( by norm_num );
    exact Filter.eventually_atTop.mp ( h_lim.eventually ( gt_mem_nhds <| half_pos hε_pos ) ) |> fun ⟨ K, hK ⟩ ↦ ⟨ K + 1, by linarith, hK _ <| by linarith ⟩;
  -- Define `c j = A ^ ((j:ℝ)/K)` and `blkCard j x = (((Finset.Ioc ⌊c j*x⌋₊ ⌊c(j+1)*x⌋₊).filter Nat.Prime).card : ℝ)`.
  set c : ℕ → ℝ := fun j => A ^ ((j : ℝ) / K)
  set blkCard : ℕ → ℝ → ℝ := fun j x => (((Finset.Ioc ⌊c j * x⌋₊ ⌊c (j + 1) * x⌋₊).filter Nat.Prime).card : ℝ);
  -- By `pi_diff_ratio hpnt (c j) (c(j+1))` (with `0 < c j ≤ c(j+1)`), `blkCard j x*log x/x → c(j+1)-c j`; dividing by the constant `(c(j+1))^2` resp `(c j)^2` and summing (`Filter.Tendsto.div_const`, `tendsto_finset_sum`), `Tendsto lowS atTop (𝓝 LK)` and `Tendsto uppS atTop (𝓝 UK)`.
  have h_lowS_uppS : Filter.Tendsto (fun x => ∑ j ∈ Finset.range K, (blkCard j x * Real.log x / x) / (c (j + 1))^2) Filter.atTop (nhds (∑ j ∈ Finset.range K, (c (j + 1) - c j) / (c (j + 1))^2)) ∧ Filter.Tendsto (fun x => ∑ j ∈ Finset.range K, (blkCard j x * Real.log x / x) / (c j)^2) Filter.atTop (nhds (∑ j ∈ Finset.range K, (c (j + 1) - c j) / (c j)^2)) := by
    have h_lowS_uppS : ∀ j ∈ Finset.range K, Filter.Tendsto (fun x => blkCard j x * Real.log x / x) Filter.atTop (nhds (c (j + 1) - c j)) := by
      intro j hj; exact pi_diff_ratio hpnt ( c j ) ( c ( j + 1 ) ) ( by positivity ) ( by exact Real.rpow_le_rpow_of_exponent_le hA.le ( by rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; norm_num ) ) ;
    exact ⟨ tendsto_finsetSum _ fun j hj => Filter.Tendsto.div_const ( h_lowS_uppS j hj ) _, tendsto_finsetSum _ fun j hj => Filter.Tendsto.div_const ( h_lowS_uppS j hj ) _ ⟩;
  -- By `primeSq_block_bounds (c j) (c(j+1)) x` per block (times `x*log x ≥ 0`), one gets `lowS x ≤ S x ≤ uppS x`.
  have h_sandwich : ∀ x : ℝ, 1 ≤ x → ∑ j ∈ Finset.range K, (blkCard j x * Real.log x / x) / (c (j + 1))^2 ≤ primeSqSum x A * (x * Real.log x) ∧ primeSqSum x A * (x * Real.log x) ≤ ∑ j ∈ Finset.range K, (blkCard j x * Real.log x / x) / (c j)^2 := by
    intro x hx
    have h_sandwich_step : primeSqSum x A = ∑ j ∈ Finset.range K, ∑ p ∈ (Finset.Ioc ⌊c j * x⌋₊ ⌊c (j + 1) * x⌋₊).filter Nat.Prime, (1 / (p : ℝ) ^ 2) := by
      convert sum_Ioc_filter_split ( fun j => ⌊c j * x⌋₊ ) ( fun j k hjk => Nat.floor_mono <| mul_le_mul_of_nonneg_right ( Real.rpow_le_rpow_of_exponent_le hA.le <| by gcongr ) <| by positivity ) Nat.Prime ( fun p => 1 / ( p : ℝ ) ^ 2 ) K |> Eq.symm using 1;
      simp +zetaDelta at *;
      norm_num [ show K ≠ 0 by linarith ];
      unfold primeSqSum; aesop;
    have h_sandwich_step : ∀ j ∈ Finset.range K, blkCard j x / (c (j + 1) * x) ^ 2 ≤ ∑ p ∈ (Finset.Ioc ⌊c j * x⌋₊ ⌊c (j + 1) * x⌋₊).filter Nat.Prime, (1 / (p : ℝ) ^ 2) ∧ ∑ p ∈ (Finset.Ioc ⌊c j * x⌋₊ ⌊c (j + 1) * x⌋₊).filter Nat.Prime, (1 / (p : ℝ) ^ 2) ≤ blkCard j x / (c j * x) ^ 2 := by
      intros j hj
      apply primeSq_block_bounds (c j) (c (j + 1)) x (by
      positivity) (by
      exact Real.rpow_le_rpow_of_exponent_le hA.le ( by gcongr ; linarith )) (by
      positivity);
    have h_sandwich_step : ∑ j ∈ Finset.range K, blkCard j x / (c (j + 1) * x) ^ 2 ≤ primeSqSum x A ∧ primeSqSum x A ≤ ∑ j ∈ Finset.range K, blkCard j x / (c j * x) ^ 2 := by
      exact ⟨ by rw [ ‹primeSqSum x A = _› ] ; exact Finset.sum_le_sum fun j hj => h_sandwich_step j hj |>.1, by rw [ ‹primeSqSum x A = _› ] ; exact Finset.sum_le_sum fun j hj => h_sandwich_step j hj |>.2 ⟩;
    convert And.intro ( mul_le_mul_of_nonneg_right h_sandwich_step.1 ( show 0 ≤ x * Real.log x by exact mul_nonneg ( by positivity ) ( Real.log_nonneg hx ) ) ) ( mul_le_mul_of_nonneg_right h_sandwich_step.2 ( show 0 ≤ x * Real.log x by exact mul_nonneg ( by positivity ) ( Real.log_nonneg hx ) ) ) using 1 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    · norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hx ) ];
    · field_simp;
  -- By `step2`, we have `LK ≤ 1 - 1/A ≤ UK`.
  have h_bounds : ∑ j ∈ Finset.range K, (c (j + 1) - c j) / (c (j + 1))^2 ≤ 1 - 1 / A ∧ 1 - 1 / A ≤ ∑ j ∈ Finset.range K, (c (j + 1) - c j) / (c j)^2 := by
    have h_bounds : ∀ j ∈ Finset.range K, (c (j + 1) - c j) / (c (j + 1))^2 ≤ 1 / c j - 1 / c (j + 1) ∧ 1 / c j - 1 / c (j + 1) ≤ (c (j + 1) - c j) / (c j)^2 := by
      intro j hj; rw [ div_sub_div, div_le_div_iff₀, div_le_div_iff₀ ] <;> try positivity;
      constructor <;> nlinarith only [ show 0 < c j from by positivity, show 0 < c ( j + 1 ) from by positivity, show c j ≤ c ( j + 1 ) from by exact Real.rpow_le_rpow_of_exponent_le hA.le ( by gcongr ; linarith ), mul_le_mul_of_nonneg_left ( show c j ≤ c ( j + 1 ) from by exact Real.rpow_le_rpow_of_exponent_le hA.le ( by gcongr ; linarith ) ) ( show 0 ≤ c j from by positivity ), mul_le_mul_of_nonneg_left ( show c j ≤ c ( j + 1 ) from by exact Real.rpow_le_rpow_of_exponent_le hA.le ( by gcongr ; linarith ) ) ( show 0 ≤ c ( j + 1 ) from by positivity ) ];
    have h_telescope : ∑ j ∈ Finset.range K, (1 / c j - 1 / c (j + 1)) = 1 - 1 / A := by
      convert Finset.sum_range_sub' _ _ using 3 <;> norm_num [ c ];
      rw [ div_self ( by positivity ), Real.rpow_one ];
    exact ⟨ h_telescope ▸ Finset.sum_le_sum fun j hj => h_bounds j hj |>.1, h_telescope ▸ Finset.sum_le_sum fun j hj => h_bounds j hj |>.2 ⟩;
  -- By `step2`, we have `UK = A^(2/K) * LK`.
  have h_UK_LK : ∑ j ∈ Finset.range K, (c (j + 1) - c j) / (c j)^2 = A^(2 / (K : ℝ)) * ∑ j ∈ Finset.range K, (c (j + 1) - c j) / (c (j + 1))^2 := by
    rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun j hj => _ ; ring_nf;
    simp +zetaDelta at *;
    field_simp;
    rw [ show ( 1 + j : ℝ ) / K = j / K + 1 / K by ring ] ; rw [ Real.rpow_add ( by positivity ) ] ; ring_nf;
    norm_num [ Real.rpow_mul ( by positivity : 0 ≤ A ) ] ; ring;
  obtain ⟨ N₁, hN₁ ⟩ := Metric.tendsto_atTop.mp h_lowS_uppS.1 ( ε / 2 ) ( half_pos hε_pos );
  obtain ⟨ N₂, hN₂ ⟩ := Metric.tendsto_atTop.mp h_lowS_uppS.2 ( ε / 2 ) ( half_pos hε_pos );
  use K, hK_pos, Max.max N₁ ( Max.max N₂ 1 );
  intro x hx; specialize h_sandwich x ( by linarith [ le_max_right N₁ ( max N₂ 1 ), le_max_right N₂ 1 ] ) ; specialize hN₁ x ( by linarith [ le_max_left N₁ ( max N₂ 1 ), le_max_right N₁ ( max N₂ 1 ) ] ) ; specialize hN₂ x ( by linarith [ le_max_left N₁ ( max N₂ 1 ), le_max_left N₂ 1, le_max_right N₁ ( max N₂ 1 ), le_max_right N₂ 1 ] ) ; norm_num [ abs_lt ] at *;
  constructor <;> nlinarith [ abs_lt.mp hN₁, abs_lt.mp hN₂, inv_pos.mpr ( zero_lt_one.trans hA ), mul_inv_cancel₀ ( ne_of_gt ( zero_lt_one.trans hA ) ), Real.one_le_rpow hA.le ( show 0 ≤ 2 / ( K : ℝ ) by positivity ) ]

/-
There is `C₂ > 0` such that for every real `z ≥ 2` and every `N`, the partial
sum of `1/p²` over primes in `(z, N]` is at most `C₂ / (z·log z)`.
-/
lemma primeSq_tail (hpnt : PNT) : ∃ C₂ : ℝ, 0 < C₂ ∧
    ∀ z : ℝ, 2 ≤ z → ∀ N : ℕ,
      (∑ p ∈ (Finset.Ioc ⌊z⌋₊ N).filter Nat.Prime, (1 / (p : ℝ) ^ 2)) ≤ C₂ / (z * log z) := by
  -- Set `C₂ = 4 * C_π`, where `C_π` is the constant from `pi_upper`.
  obtain ⟨C_π, hC_π_pos, hC_π⟩ := pi_upper hpnt;
  use 4 * C_π;
  constructor;
  · positivity;
  · intro z hz N
    have h_cover : (∑ p ∈ (Finset.Ioc ⌊z⌋₊ N).filter Nat.Prime, (1 / (p : ℝ) ^ 2)) ≤ ∑ j ∈ Finset.range (Nat.log 2 N + 1), (∑ p ∈ (Finset.Ioc (⌊2^j * z⌋₊) (⌊2^(j+1) * z⌋₊)).filter Nat.Prime, (1 / (p : ℝ) ^ 2)) := by
      have h_cover : Finset.filter Nat.Prime (Finset.Ioc ⌊z⌋₊ N) ⊆ Finset.biUnion (Finset.range (Nat.log 2 N + 1)) (fun j => Finset.filter Nat.Prime (Finset.Ioc ⌊2^j * z⌋₊ ⌊2^(j+1) * z⌋₊)) := by
        intro p hp; simp_all +decide ;
        -- Let $a$ be the largest integer such that $2^a z < p$.
        obtain ⟨a, ha⟩ : ∃ a : ℕ, 2^a * z < p ∧ p ≤ 2^(a+1) * z := by
          have h_exists_a : ∃ a : ℕ, 2^a * z < p ∧ p ≤ 2^(a+1) * z := by
            have h_exists_a : ∃ a : ℕ, p ≤ 2^a * z := by
              exact ⟨ p, by nlinarith [ show ( p : ℝ ) ≤ 2 ^ p by exact mod_cast Nat.le_of_lt ( Nat.recOn p ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; nlinarith [ Nat.Prime.one_lt hp.2 ] ) ] ⟩
            contrapose! h_exists_a;
            intro a; induction a <;> simp_all +decide [ pow_succ', mul_assoc ] ;
            exact lt_of_lt_of_le ( Nat.lt_of_floor_lt hp.1.1 ) ( Nat.cast_le.mpr le_rfl );
          exact h_exists_a;
        refine' ⟨ a, _, _, _ ⟩;
        · refine' Nat.le_log_of_pow_le ( by norm_num ) _;
          exact_mod_cast ( by nlinarith [ show ( p : ℝ ) ≤ N by norm_cast; linarith ] : ( 2 : ℝ ) ^ a ≤ N );
        · exact Nat.floor_lt ( by positivity ) |>.2 ha.1;
        · exact Nat.le_floor <| mod_cast ha.2;
      refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_cover fun _ _ _ => by positivity ) _;
      rw [ Finset.sum_biUnion ];
      intros i hi j hj hij; simp_all +decide [ Finset.disjoint_left ] ;
      contrapose! hij;
      obtain ⟨ a, ha₁, ha₂, ha₃, ha₄, ha₅ ⟩ := hij; exact le_antisymm ( Nat.le_of_not_lt fun hi' => by linarith [ show ⌊2 ^ i * z⌋₊ ≥ ⌊2 ^ ( j + 1 ) * z⌋₊ by exact Nat.floor_mono <| by exact mul_le_mul_of_nonneg_right ( pow_le_pow_right₀ ( by norm_num ) <| by linarith ) <| by positivity ] ) ( Nat.le_of_not_lt fun hj' => by linarith [ show ⌊2 ^ j * z⌋₊ ≥ ⌊2 ^ ( i + 1 ) * z⌋₊ by exact Nat.floor_mono <| by exact mul_le_mul_of_nonneg_right ( pow_le_pow_right₀ ( by norm_num ) <| by linarith ) <| by positivity ] ) ;
    -- For each block `j`, every prime `p` in it satisfies `p > 2^j z` so `1/p² ≤ 1/(2^j z)²`, and the number of primes in it is `≤ π(2^{j+1}z) ≤ C_π·(2^{j+1}z)/log(2^{j+1}z) ≤ C_π·2^{j+1}z/log z` (since `2^{j+1}z ≥ z ≥ 2` and `log` monotone).
    have h_block_bound : ∀ j : ℕ, (∑ p ∈ (Finset.Ioc (⌊2^j * z⌋₊) (⌊2^(j+1) * z⌋₊)).filter Nat.Prime, (1 / (p : ℝ) ^ 2)) ≤ (C_π * 2^(j+1) * z / Real.log z) * (1 / (2^j * z)^2) := by
      intro j
      have h_block_card : ((Finset.Ioc (⌊2^j * z⌋₊) (⌊2^(j+1) * z⌋₊)).filter Nat.Prime).card ≤ C_π * 2^(j+1) * z / Real.log z := by
        have h_block_card : ((Finset.Ioc (⌊2^j * z⌋₊) (⌊2^(j+1) * z⌋₊)).filter Nat.Prime).card ≤ Nat.primeCounting ⌊2^(j+1) * z⌋₊ := by
          rw [ Nat.primeCounting ];
          rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
          exact Finset.card_mono fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) ] ), Finset.mem_filter.mp hx |>.2 ⟩;
        refine le_trans ( Nat.cast_le.mpr h_block_card ) ?_;
        refine le_trans ( hC_π _ ?_ ) ?_;
        · exact le_trans hz ( le_mul_of_one_le_left ( by positivity ) ( one_le_pow₀ ( by norm_num ) ) );
        · rw [ mul_assoc ];
          gcongr;
          · exact Real.log_pos <| by linarith;
          · exact le_mul_of_one_le_left ( by positivity ) ( one_le_pow₀ ( by norm_num ) );
      refine' le_trans ( Finset.sum_le_sum fun p hp => one_div_le_one_div_of_le _ <| pow_le_pow_left₀ ( by positivity ) ( show ( p : ℝ ) ≥ 2 ^ j * z by exact le_trans ( Nat.lt_floor_add_one _ |> le_of_lt ) <| mod_cast Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) 2 ) _ <;> norm_num [ h_block_card ];
      · positivity;
      · exact mul_le_mul_of_nonneg_right h_block_card <| by positivity;
    -- Summing over `j < J`: `≤ (2C_π/(z log z))·∑_{j<J} 2^{-j} ≤ (2C_π/(z log z))·2 = 4C_π/(z log z) = C₂/(z log z)`.
    have h_sum_bound : ∑ j ∈ Finset.range (Nat.log 2 N + 1), (C_π * 2^(j+1) * z / Real.log z) * (1 / (2^j * z)^2) ≤ (2 * C_π / (z * Real.log z)) * (∑ j ∈ Finset.range (Nat.log 2 N + 1), (1 / 2 : ℝ)^j) := by
      rw [ Finset.mul_sum _ _ _ ] ; refine Finset.sum_le_sum fun i hi => ?_; ring_nf; norm_num;
      norm_num [ pow_mul', mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_two.trans_le hz ) ];
      norm_num [ ← mul_assoc, ← mul_pow ] ; ring_nf ; norm_num [ show z ≠ 0 by linarith, show z ^ 2 ≠ 0 by positivity ];
      norm_num [ sq, mul_assoc, mul_comm z, ne_of_gt ( zero_lt_two.trans_le hz ) ];
    refine le_trans h_cover <| le_trans ( Finset.sum_le_sum fun _ _ => h_block_bound _ ) <| h_sum_bound.trans ?_;
    rw [ geom_sum_eq ] <;> ring_nf <;> norm_num;
    exact mul_nonneg ( mul_nonneg hC_π_pos.le ( inv_nonneg.mpr ( by positivity ) ) ) ( inv_nonneg.mpr ( Real.log_nonneg ( by linarith ) ) )

/-! ### Growth relations

Here `y = n^{1/3}`, `L = log n`, `M = y/L`, `S = M² = n^{2/3}/(log n)²`. -/

/-
`n^{1/3} → ∞`.
-/
lemma tendsto_y_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((1:ℝ)/3)) atTop atTop := by
  exact tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop

/-
`M = n^{1/3}/log n → ∞`.
-/
lemma tendsto_M_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((1:ℝ)/3) / Real.log n) atTop atTop := by
  -- Let $y = \log n$, therefore the expression becomes $\frac{e^{y/3}}{y}$.
  suffices h_log : Filter.Tendsto (fun y : ℝ => Real.exp (y / 3) / y) Filter.atTop Filter.atTop by
    have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
  -- Let $z = \frac{y}{3}$, therefore the expression becomes $\frac{e^z}{3z}$.
  suffices h_z : Filter.Tendsto (fun z : ℝ => Real.exp z / (3 * z)) Filter.atTop Filter.atTop by
    convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 3⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf;
  ring_nf;
  exact Filter.Tendsto.atTop_mul_const ( by norm_num ) ( by simpa using Real.tendsto_exp_div_pow_atTop 1 )

/-
`M / S → 0`, i.e. `M = o(S)`.
-/
lemma M_div_S_tendsto_zero :
    Tendsto (fun n : ℕ => ((n : ℝ) ^ ((1:ℝ)/3) / Real.log n) / S n) atTop (𝓝 0) := by
  -- Simplify the expression inside the limit.
  suffices h_simp : Filter.Tendsto (fun n : ℕ => (Real.log n) / (n : ℝ) ^ (1 / 3 : ℝ)) Filter.atTop (nhds 0) by
    refine h_simp.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn;
    unfold S; ring_nf;
    norm_num [ sq, mul_assoc, mul_comm, mul_left_comm, ne_of_gt, Real.log_pos, show n > 1 from hn ];
    norm_num [ ← mul_assoc, ← Real.rpow_neg ( Nat.cast_nonneg _ ), ← Real.rpow_add ( Nat.cast_pos.mpr hn.le ) ];
  -- Let $y = \log n$, therefore the expression becomes $\frac{y}{e^{y/3}}$.
  suffices h_log : Filter.Tendsto (fun y : ℝ => y / Real.exp (y / 3)) Filter.atTop (nhds 0) by
    have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
  -- Let $z = \frac{y}{3}$, therefore the expression becomes $\frac{3z}{e^z}$.
  suffices h_z : Filter.Tendsto (fun z : ℝ => 3 * z / Real.exp z) Filter.atTop (nhds 0) by
    convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 3⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf;
  simpa [ Real.exp_neg, mul_div_assoc ] using tendsto_const_nhds.mul ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 )

/-
`n^{3/5} / S → 0`, i.e. `n^{3/5} = o(S)`.
-/
lemma n35_div_S_tendsto_zero :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((3:ℝ)/5) / S n) atTop (𝓝 0) := by
  unfold S; ring_nf; norm_num;
  -- Simplify the expression inside the limit.
  suffices h_simp : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (3 / 5 - 2 / 3 : ℝ) * (Real.log n) ^ 2) Filter.atTop (nhds 0) by
    refine h_simp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ ← Real.rpow_neg ( by positivity ), ← Real.rpow_add ( by positivity ) ] ; ring_nf );
  -- Let $y = \log n$, therefore the expression becomes $\frac{y^2}{e^{y/15}}$.
  suffices h_log : Filter.Tendsto (fun y : ℝ => y^2 * Real.exp (-y / 15)) Filter.atTop (nhds 0) by
    have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Function.comp_apply, Function.comp_apply, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
  -- Let $z = \frac{y}{15}$, therefore the expression becomes $\frac{(15z)^2}{e^z} = \frac{225z^2}{e^z}$.
  suffices h_z : Filter.Tendsto (fun z : ℝ => 225 * z^2 * Real.exp (-z)) Filter.atTop (nhds 0) by
    convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 15⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf;
  simpa [ mul_assoc ] using Filter.Tendsto.const_mul 225 ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2 )

/-! ## The multiplicative basis -/

/-- `B₀ = {m : 1 ≤ m ≤ n^{3/5}}`. -/
noncomputable def B0 (n : ℕ) : Finset ℕ := Finset.Icc 1 ⌊(n:ℝ) ^ ((3:ℝ)/5)⌋₊

/-- `B₁ = {p prime : n^{3/5} < p ≤ n}`. -/
noncomputable def B1 (n : ℕ) : Finset ℕ :=
  (Finset.Ioc ⌊(n:ℝ) ^ ((3:ℝ)/5)⌋₊ n).filter Nat.Prime

/-- `B₂ = {p·q : p, q prime, p ≤ y, q ≤ y}`, where `y = n^{1/3}`. -/
noncomputable def B2 (n : ℕ) : Finset ℕ :=
  (((Finset.Icc 1 ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime) ×ˢ
   ((Finset.Icc 1 ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime)).image (fun pq => pq.1 * pq.2)

/-- `B₃ = {q·r : q, r prime, y < q ≤ n^{2/5}, r ≤ n/q²}`. -/
noncomputable def B3 (n : ℕ) : Finset ℕ :=
  ((Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊(n:ℝ) ^ ((2:ℝ)/5)⌋₊).filter Nat.Prime).biUnion
    (fun q => ((Finset.Icc 1 (n / (q * q))).filter Nat.Prime).image (fun r => q * r))

/-- The full basis `B = B₀ ∪ B₁ ∪ B₂ ∪ B₃`. -/
noncomputable def Bset (n : ℕ) : Finset ℕ := B0 n ∪ B1 n ∪ B2 n ∪ B3 n

/-
If a product of factors bounded by `U` carries `D` from below `T` to above `T`,
some partial product lands in `[T, T·U]`.
-/
lemma threshold_crossing (D T U : ℝ) (s : ℕ → ℝ) (k : ℕ)
    (hT : 0 < T) (hU : 0 < U) (hD : 0 < D) (hDT : D ≤ T)
    (hs : ∀ j < k, 0 < s j ∧ s j ≤ U)
    (hprod : T < D * ∏ j ∈ Finset.range k, s j) :
    ∃ r ≤ k, T ≤ D * ∏ j ∈ Finset.range r, s j ∧
      D * ∏ j ∈ Finset.range r, s j ≤ T * U := by
  induction' k with k ih generalizing D T U s <;> norm_num [ Finset.prod_range_succ ] at *;
  · linarith;
  · by_cases h : T < D * ∏ j ∈ Finset.range k, s j;
    · obtain ⟨ r, hr₁, hr₂, hr₃ ⟩ := ih D T U s hT hU hD hDT ( fun j hj => hs j ( Nat.le_of_lt hj ) ) h; exact ⟨ r, Nat.le_succ_of_le hr₁, hr₂, hr₃ ⟩ ;
    · refine' ⟨ k + 1, _, _, _ ⟩ <;> norm_num [ Finset.prod_range_succ ];
      · linarith;
      · nlinarith [ hs k le_rfl, show 0 ≤ D * ∏ j ∈ Finset.range k, s j from mul_nonneg hD.le <| Finset.prod_nonneg fun _ _ => le_of_lt <| hs _ ( Finset.mem_range_le ‹_› ) |>.1 ]

/-
Every `m ≤ X` factors as `m = u·v` with `v ≤ X^{2/3}` and `u` prime or
`u ≤ X^{2/3}`.
-/
lemma balanced_factorization (X : ℝ) (hX : 1 ≤ X) (m : ℕ) (hm : 1 ≤ m)
    (hmX : (m : ℝ) ≤ X) :
    ∃ u v : ℕ, 1 ≤ u ∧ 1 ≤ v ∧ m = u * v ∧ (v : ℝ) ≤ X ^ ((2:ℝ)/3) ∧
      (Nat.Prime u ∨ (u : ℝ) ≤ X ^ ((2:ℝ)/3)) := by
  simp +zetaDelta at *;
  by_cases h_case : (m : ℝ) ≤ X ^ (2 / 3 : ℝ);
  · use m, hm, 1, by norm_num;
    exact ⟨ by norm_num, by exact le_trans ( by norm_num ) ( Real.one_le_rpow hX ( by norm_num ) ), Or.inr h_case ⟩;
  · -- Case 2: $m > X^{2/3}$. Two subcases.
    by_cases h_prime : ∃ p : ℕ, Nat.Prime p ∧ p ∣ m ∧ (p : ℝ) > X ^ (1 / 3 : ℝ);
    · obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := h_prime;
      refine' ⟨ p, hp₁.pos, m / p, Nat.div_pos ( Nat.le_of_dvd hm hp₂ ) hp₁.pos, _, _, _ ⟩;
      · rw [ Nat.mul_div_cancel' hp₂ ];
      · rw [ Nat.cast_div ( by assumption ) ( by aesop ) ];
        rw [ div_le_iff₀ ( Nat.cast_pos.mpr hp₁.pos ) ];
        refine' le_trans hmX _;
        exact le_trans ( by rw [ ← Real.rpow_add ( by positivity ) ] ; norm_num ) ( mul_le_mul_of_nonneg_left hp₃.le ( by positivity ) );
      · exact Or.inl hp₁;
    · -- Every prime divisor of $m$ is $\leq X^{1/3}$. List the prime factors of $m$ with multiplicity and multiply them in order until the running product first exceeds $X^{1/3}$; let $u$ be that running product (it exists since $m > X^{2/3} \geq X^{1/3}$).
      obtain ⟨u, hu⟩ : ∃ u : ℕ, 1 ≤ u ∧ u ∣ m ∧ (u : ℝ) > X ^ (1 / 3 : ℝ) ∧ ∀ v : ℕ, 1 ≤ v → v ∣ m → v < u → (v : ℝ) ≤ X ^ (1 / 3 : ℝ) := by
        have h_exists_u : ∃ u : ℕ, 1 ≤ u ∧ u ∣ m ∧ (u : ℝ) > X ^ (1 / 3 : ℝ) := by
          use m;
          exact ⟨ hm, dvd_rfl, lt_of_le_of_lt ( Real.rpow_le_rpow_of_exponent_le hX ( show ( 1 : ℝ ) / 3 ≤ 2 / 3 by norm_num ) ) ( not_le.mp h_case ) ⟩;
        exact ⟨ Nat.find h_exists_u, Nat.find_spec h_exists_u |>.1, Nat.find_spec h_exists_u |>.2.1, Nat.find_spec h_exists_u |>.2.2, fun v hv₁ hv₂ hv₃ => not_lt.1 fun hv₄ => Nat.find_min h_exists_u hv₃ ⟨ hv₁, hv₂, hv₄ ⟩ ⟩;
      -- Since $u$ is the smallest divisor of $m$ greater than $X^{1/3}$, we have $u \leq X^{2/3}$.
      have hu_le : (u : ℝ) ≤ X ^ (2 / 3 : ℝ) := by
        -- Since $u$ is the smallest divisor of $m$ greater than $X^{1/3}$, we have $u = p \cdot v$ for some prime $p$ and divisor $v$ of $m$.
        obtain ⟨p, v, hp, hv, huv⟩ : ∃ p v : ℕ, Nat.Prime p ∧ v ∣ m ∧ u = p * v := by
          obtain ⟨p, hp⟩ : ∃ p : ℕ, Nat.Prime p ∧ p ∣ u := by
            exact Nat.exists_prime_and_dvd ( by rintro rfl; exact absurd hu.2.2.1 ( by norm_num; linarith [ Real.one_le_rpow hX ( by norm_num : ( 0 : ℝ ) ≤ 1 / 3 ) ] ) );
          exact ⟨ p, u / p, hp.1, Nat.dvd_trans ( Nat.div_dvd_of_dvd hp.2 ) hu.2.1, by rw [ Nat.mul_div_cancel' hp.2 ] ⟩;
        by_cases hv1 : v = 0 <;> simp_all +decide;
        have := hu.2.2.2 v ( Nat.pos_of_dvd_of_pos hv hm ) hv ( by nlinarith [ hp.two_le, Nat.pos_of_ne_zero hv1 ] ) ; norm_num at * ; rw [ show ( 2 / 3 : ℝ ) = 1 / 3 + 1 / 3 by norm_num, Real.rpow_add ] <;> norm_num <;> nlinarith [ h_prime p hp ( dvd_of_mul_right_dvd hu.2.1 ), Real.rpow_pos_of_pos ( zero_lt_one.trans_le hX ) ( 1 / 3 : ℝ ) ] ;
      refine' ⟨ u, hu.1, m / u, _, _, _, _ ⟩ <;> norm_num at *;
      · exact Nat.div_pos ( Nat.le_of_dvd hm hu.2.1 ) hu.1;
      · rw [ Nat.mul_div_cancel' hu.2.1 ];
      · rw [ Nat.cast_div ( hu.2.1 ) ( by norm_cast; linarith ) ];
        rw [ div_le_iff₀ ] <;> nlinarith [ show ( u : ℝ ) ≥ 1 by exact_mod_cast hu.1, show ( m : ℝ ) ≤ X by exact_mod_cast hmX, show ( X : ℝ ) ^ ( 1 / 3 : ℝ ) > 0 by positivity, show ( X : ℝ ) ^ ( 2 / 3 : ℝ ) > 0 by positivity, show ( X : ℝ ) ^ ( 1 / 3 : ℝ ) * ( X : ℝ ) ^ ( 2 / 3 : ℝ ) = X by rw [ ← Real.rpow_add ( by positivity ) ] ; norm_num ];
      · exact Or.inr hu_le

/-- Product over `range r` of `(l[j]?.getD 1 : ℝ)` equals the product of the
first `r` entries of `l` (cast to `ℝ`). -/
lemma prod_range_getD_take (l : List ℕ) (r : ℕ) :
    ∏ j ∈ Finset.range r, ((l[j]?.getD 1 : ℕ) : ℝ) = ((l.take r).prod : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.prod_range_succ, ih, List.take_add_one, List.prod_append]
    push_cast
    by_cases hr : r < l.length
    · rw [List.getElem?_eq_getElem hr]; simp
    · rw [List.getElem?_eq_none (by omega)]; simp

/-
If at least three prime factors of `m` (counted with multiplicity) exceed
`n^{1/5}`, then there are three primes `p ≥ q ≥ r > n^{1/5}` with `p*q*r ∣ m`.
-/
set_option linter.unusedTactic false in
lemma exists_three_large_factors (n m : ℕ) (hm1 : 1 ≤ m)
    (hcount : 3 ≤ ((Nat.primeFactorsList m).filter
      (fun p => (n:ℝ) ^ ((1:ℝ)/5) < (p:ℝ))).length) :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      r ≤ q ∧ q ≤ p ∧ (n:ℝ) ^ ((1:ℝ)/5) < (r:ℝ) ∧ p * q * r ∣ m := by
  -- Let `L = Nat.primeFactorsList m` and `F = L.filter (fun p => (n:ℝ)^{1/5} < (p:ℝ))`, with `3 ≤ F.length`.
  set L := m.primeFactorsList
  set F := L.filter (fun p => (n : ℝ) ^ (1 / 5 : ℝ) < p);
  obtain ⟨l, hl⟩ : ∃ l : List ℕ, l.Sublist L ∧ l.length = 3 ∧ (∀ p ∈ l, (n : ℝ) ^ (1 / 5 : ℝ) < p) ∧ (∀ p ∈ l, Nat.Prime p) := by
    have hF_sublist : ∃ l : List ℕ, l.Sublist L ∧ l.length = F.length ∧ (∀ p ∈ l, (n : ℝ) ^ (1 / 5 : ℝ) < p) ∧ (∀ p ∈ l, Nat.Prime p) := by
      have hF_sublist : ∀ {l : List ℕ}, (∀ p ∈ l, Nat.Prime p) → ∃ l' : List ℕ, l'.Sublist l ∧ l'.length = (List.filter (fun p => (n : ℝ) ^ (1 / 5 : ℝ) < p) l).length ∧ (∀ p ∈ l', (n : ℝ) ^ (1 / 5 : ℝ) < p) ∧ (∀ p ∈ l', Nat.Prime p) := by
        intros l hl_prime; induction' l with p l ih;
        · exact ⟨ [ ], by norm_num ⟩;
        · by_cases h : ( n : ℝ ) ^ ( 1 / 5 : ℝ ) < p <;> simp_all +decide;
          · obtain ⟨ l', hl₁, hl₂, hl₃, hl₄ ⟩ := ih; use p :: l'; aesop;
          · exact ⟨ ih.choose, List.Sublist.trans ih.choose_spec.1 ( List.sublist_cons_self _ _ ), ih.choose_spec.2.1, ih.choose_spec.2.2.1, ih.choose_spec.2.2.2 ⟩;
      exact hF_sublist fun p hp => Nat.prime_of_mem_primeFactorsList hp;
    obtain ⟨ l, hl₁, hl₂, hl₃, hl₄ ⟩ := hF_sublist;
    use l.take 3;
    exact ⟨ List.Sublist.trans ( List.take_sublist _ _ ) hl₁, by rw [ List.length_take, hl₂ ] ; omega, fun p hp => hl₃ p <| List.mem_of_mem_take hp, fun p hp => hl₄ p <| List.mem_of_mem_take hp ⟩;
  -- Since `l` is a sublist of `L`, `l.prod ∣ L.prod = m` (product over a sublist divides product over the whole list; use `Nat.prod_primeFactorsList` for `L.prod = m`, `m ≠ 0` from `1 ≤ m`).
  have h_div : l.prod ∣ m := by
    convert Nat.dvd_trans ( hl.1.prod_dvd_prod ) ( Nat.prod_primeFactorsList ( by positivity ) |> fun x => x.dvd ) using 1;
  rcases l with ( _ | ⟨ p, _ | ⟨ q, _ | ⟨ r, _ | l ⟩ ⟩ ⟩ ) <;> simp_all +decide;
  cases le_total p q <;> cases le_total q r <;> cases le_total r p <;> first | exact ⟨ p, hl.2.2.1, q, hl.2.2.2.1, r, hl.2.2.2.2, by linarith, by linarith, by linarith, by simpa only [ mul_assoc ] using h_div ⟩ | skip;
  · exact ⟨ r, hl.2.2.2.2, q, hl.2.2.2.1, p, hl.2.2.1, by linarith, by linarith, by linarith, by convert h_div using 1; ring ⟩;
  · exact ⟨ q, hl.2.2.2.1, p, hl.2.2.1, r, hl.2.2.2.2, by linarith, by linarith, by linarith, by convert h_div using 1; ring ⟩;
  · exact ⟨ q, hl.2.2.2.1, r, hl.2.2.2.2, p, hl.2.2.1, by linarith, by linarith, by linarith, by convert h_div using 1; ring ⟩;
  · exact ⟨ p, hl.2.2.1, r, hl.2.2.2.2, q, hl.2.2.2.1, by linarith, by linarith, by linarith, by convert h_div using 1; ring ⟩;
  · exact ⟨ r, hl.2.2.2.2, p, hl.2.2.1, q, hl.2.2.2.1, by linarith, by linarith, by linarith, by convert h_div using 1; ring ⟩

/-- If `m ∈ (n^{9/10}, n]` has all prime factors `≤ n^{2/5}` and at most two
  prime factors (with multiplicity) exceeding `n^{1/5}`, then `m` has a divisor
  `u` with `n^{2/5} ≤ u ≤ n^{3/5}`. -/
lemma exists_mid_divisor (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (hm1 : 1 ≤ m)
    (hm9 : (n:ℝ) ^ ((9:ℝ)/10) < (m:ℝ))
    (hbig : ∀ p, Nat.Prime p → p ∣ m → (p:ℝ) ≤ (n:ℝ) ^ ((2:ℝ)/5))
    (hcount : ((Nat.primeFactorsList m).filter
      (fun p => (n:ℝ) ^ ((1:ℝ)/5) < (p:ℝ))).length ≤ 2) :
    ∃ u : ℕ, u ∣ m ∧ (n:ℝ) ^ ((2:ℝ)/5) ≤ (u:ℝ) ∧ (u:ℝ) ≤ (n:ℝ) ^ ((3:ℝ)/5) := by
  classical
  have hm0 : m ≠ 0 := by omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hcount' : (m.primeFactorsList.filter (fun (a:ℕ) => decide ((n:ℝ)^((1:ℝ)/5) < (a:ℝ)))).length ≤ 2 := by
    have heq : (m.primeFactorsList.filter (fun (a:ℕ) => decide ((n:ℝ)^((1:ℝ)/5) < (a:ℝ)))).length
        = ((Nat.primeFactorsList m).filter (fun p => (n:ℝ) ^ ((1:ℝ)/5) < (p:ℝ))).length := by
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      simp only [bind_pure_comp]
      rw [show (Nat.cast <$> m.primeFactorsList : List ℝ) = m.primeFactorsList.map (Nat.cast : ℕ → ℝ) from rfl,
          List.countP_map]
      rfl
    rw [heq]; exact hcount
  obtain ⟨Lbig, Lsmall, hL⟩ : ∃ Lbig Lsmall : List ℕ,
      m.primeFactorsList.Perm (Lbig ++ Lsmall) ∧
      (∀ p ∈ Lbig, Nat.Prime p ∧ (n : ℝ) ^ ((1:ℝ)/5) < (p:ℝ)) ∧
      (∀ p ∈ Lsmall, Nat.Prime p ∧ (p:ℝ) ≤ (n : ℝ) ^ ((1:ℝ)/5)) ∧ Lbig.length ≤ 2 := by
    refine ⟨m.primeFactorsList.filter (fun (a:ℕ) => decide ((n:ℝ)^((1:ℝ)/5) < (a:ℝ))),
            m.primeFactorsList.filter (fun (a:ℕ) => !decide ((n:ℝ)^((1:ℝ)/5) < (a:ℝ))),
            (List.filter_append_perm _ _).symm, ?_, ?_, hcount'⟩
    · intro p hp; rw [List.mem_filter] at hp
      exact ⟨Nat.prime_of_mem_primeFactorsList hp.1, by simpa using hp.2⟩
    · intro p hp; rw [List.mem_filter] at hp
      exact ⟨Nat.prime_of_mem_primeFactorsList hp.1, not_lt.1 (by simpa using hp.2)⟩
  have hprodm : (Lbig ++ Lsmall).prod = m := by
    rw [← hL.1.prod_eq, Nat.prod_primeFactorsList hm0]
  obtain ⟨D0, hD0⟩ : ∃ D0 : ℕ, (D0:ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 5) ∧ D0 ∣ m ∧
      (n : ℝ) ^ ((2 : ℝ) / 5) < (D0 : ℝ) * (Lsmall.prod : ℝ) ∧ D0 * Lsmall.prod ∣ m := by
    by_cases hLbig : Lbig.length ≤ 1
    · refine ⟨Lbig.prod, ?_, ?_, ?_, ?_⟩
      · rcases Lbig with (_ | ⟨p, _ | ⟨q, Lb⟩⟩)
        · simpa using Real.one_le_rpow hn1 (by norm_num)
        · have hpmem : p ∈ Nat.primeFactorsList m := hL.1.symm.subset (by simp)
          simpa using hbig p (hL.2.1 p (by simp)).1 (Nat.dvd_of_mem_primeFactorsList hpmem)
        · simp only [List.length_cons] at hLbig; omega
      · have : Lbig.prod ∣ (Lbig ++ Lsmall).prod := ⟨Lsmall.prod, by rw [List.prod_append]⟩
        rw [hprodm] at this; exact this
      · have hpr : (Lbig.prod : ℝ) * (Lsmall.prod : ℝ) = m := by
          rw [← hprodm, List.prod_append]; push_cast; ring
        rw [hpr]
        exact hm9.trans_le' (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num))
      · exact ⟨1, by rw [← hprodm, List.prod_append]; ring⟩
    · obtain ⟨q, p, rfl⟩ : ∃ q p : ℕ, Lbig = [q, p] := by
        rcases Lbig with (_ | ⟨a, _ | ⟨b, Lb⟩⟩)
        · exact (hLbig (by simp)).elim
        · exact (hLbig (by simp)).elim
        · have hlb : Lb.length = 0 := by have := hL.2.2.2; simp only [List.length_cons] at this; omega
          rw [List.eq_nil_of_length_eq_zero hlb]; exact ⟨a, b, rfl⟩
      have hqmem : q ∈ Nat.primeFactorsList m := hL.1.symm.subset (by simp)
      have hpmem : p ∈ Nat.primeFactorsList m := hL.1.symm.subset (by simp)
      have hqprime : Nat.Prime q := (hL.2.1 q (by simp)).1
      have hmeq : q * (p * Lsmall.prod) = m := by
        rw [← hprodm]; simp [List.prod_cons]
      refine ⟨p, ?_, ?_, ?_, ?_⟩
      · exact hbig p (hL.2.1 p (by simp)).1 (Nat.dvd_of_mem_primeFactorsList hpmem)
      · exact Nat.dvd_of_mem_primeFactorsList hpmem
      · have hpr : (q : ℝ) * ((p : ℝ) * (Lsmall.prod : ℝ)) = m := by exact_mod_cast hmeq
        have hq2 : (q:ℝ) ≤ (n:ℝ)^((2:ℝ)/5) := hbig q hqprime (Nat.dvd_of_mem_primeFactorsList hqmem)
        have hpL0 : (0:ℝ) ≤ (p:ℝ) * Lsmall.prod := by positivity
        have hid : (n:ℝ)^((2:ℝ)/5) * (n:ℝ)^((1:ℝ)/2) = (n:ℝ)^((9:ℝ)/10) := by
          rw [← Real.rpow_add hnpos]; norm_num
        have hlt : (n:ℝ)^((2:ℝ)/5) < (n:ℝ)^((1:ℝ)/2) :=
          (Real.rpow_lt_rpow_left_iff (by exact_mod_cast hn)).2 (by norm_num)
        have hn25 : (0:ℝ) < (n:ℝ)^((2:ℝ)/5) := Real.rpow_pos_of_pos hnpos _
        have key : (n:ℝ)^((2:ℝ)/5) * (n:ℝ)^((1:ℝ)/2) < (n:ℝ)^((2:ℝ)/5) * ((p:ℝ)*Lsmall.prod) := by
          calc (n:ℝ)^((2:ℝ)/5) * (n:ℝ)^((1:ℝ)/2) = (n:ℝ)^((9:ℝ)/10) := hid
            _ < m := hm9
            _ = (q:ℝ) * ((p:ℝ)*Lsmall.prod) := hpr.symm
            _ ≤ (n:ℝ)^((2:ℝ)/5) * ((p:ℝ)*Lsmall.prod) := mul_le_mul_of_nonneg_right hq2 hpL0
        have hpLgt : (n:ℝ)^((1:ℝ)/2) < (p:ℝ)*Lsmall.prod := lt_of_mul_lt_mul_left key (le_of_lt hn25)
        linarith [hlt, hpLgt]
      · exact ⟨q, by rw [← hmeq]; ring⟩
  obtain ⟨r, hr_le, hr1, hr2⟩ := threshold_crossing (D0 : ℝ) ((n:ℝ)^((2:ℝ)/5)) ((n:ℝ)^((1:ℝ)/5))
      (fun j => ((Lsmall[j]?.getD 1 : ℕ) : ℝ)) Lsmall.length
      (Real.rpow_pos_of_pos hnpos _) (Real.rpow_pos_of_pos hnpos _)
      (by exact_mod_cast Nat.pos_of_dvd_of_pos hD0.2.1 hm1) hD0.1
      (by
        intro j hj
        have hmem : Lsmall[j]?.getD 1 ∈ Lsmall := by
          rw [List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
        refine ⟨?_, ?_⟩
        · dsimp only; exact_mod_cast (hL.2.2.1 _ hmem).1.pos
        · dsimp only; exact (hL.2.2.1 _ hmem).2)
      (by rw [prod_range_getD_take, List.take_length]; exact hD0.2.2.1)
  rw [prod_range_getD_take] at hr1 hr2
  refine ⟨D0 * (Lsmall.take r).prod, ?_, ?_, ?_⟩
  · exact dvd_trans (mul_dvd_mul_left D0
      (by rw [← List.prod_take_mul_prod_drop Lsmall r]; exact dvd_mul_right _ _)) hD0.2.2.2
  · rw [Nat.cast_mul]; exact hr1
  · rw [Nat.cast_mul]
    calc ((D0:ℝ) * ((Lsmall.take r).prod : ℝ)) ≤ (n:ℝ)^((2:ℝ)/5) * (n:ℝ)^((1:ℝ)/5) := hr2
      _ = (n:ℝ)^((3:ℝ)/5) := by rw [← Real.rpow_add hnpos]; norm_num

/-- For every `n ≥ 2`, `B` is a two-factor basis for `[n]`. -/
lemma multiplicative_basis (n : ℕ) (hn : 2 ≤ n) : TwoFactorBasis (Bset n) n := by
  classical
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn35pos : (0:ℝ) < (n:ℝ)^((3:ℝ)/5) := Real.rpow_pos_of_pos hnpos _
  have hid : (n:ℝ)^((3:ℝ)/5) * (n:ℝ)^((2:ℝ)/5) = n := by
    rw [← Real.rpow_add hnpos]; norm_num
  have inB0 : ∀ x : ℕ, 1 ≤ x → (x:ℝ) ≤ (n:ℝ)^((3:ℝ)/5) → x ∈ Bset n := by
    intro x hx1 hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_Icc.mpr ⟨hx1, Nat.le_floor hx⟩)))
  have inB1 : ∀ x : ℕ, Nat.Prime x → (n:ℝ)^((3:ℝ)/5) < (x:ℝ) → x ≤ n → x ∈ Bset n := by
    intro x hxp hx hxn
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨(Nat.floor_lt (by positivity)).2 hx, hxn⟩, hxp⟩
  intro m hm
  rw [Finset.mem_Icc] at hm
  obtain ⟨hm1, hmn⟩ := hm
  have hm0 : m ≠ 0 := by omega
  have hmR : (m:ℝ) ≤ n := by exact_mod_cast hmn
  have quot_le : ∀ d : ℕ, 0 < d → (n:ℝ)^((2:ℝ)/5) ≤ (d:ℝ) → ((m/d:ℕ):ℝ) ≤ (n:ℝ)^((3:ℝ)/5) := by
    intro d hd hdge
    have hdpos : (0:ℝ) < d := by exact_mod_cast hd
    calc ((m/d:ℕ):ℝ) ≤ (m:ℝ)/(d:ℝ) := Nat.cast_div_le
      _ ≤ (n:ℝ)^((3:ℝ)/5) := by
          rw [div_le_iff₀ hdpos]
          nlinarith [hmR, hid, mul_le_mul_of_nonneg_left hdge (le_of_lt hn35pos)]
  by_cases hsmall : (m:ℝ) ≤ (n:ℝ)^((9:ℝ)/10)
  · obtain ⟨u, v, hu1, hv1, huv, hvle, hudisj⟩ :=
      balanced_factorization ((n:ℝ)^((9:ℝ)/10)) (Real.one_le_rpow hn1 (by norm_num)) m hm1 hsmall
    have hexp : ((n:ℝ)^((9:ℝ)/10))^((2:ℝ)/3) = (n:ℝ)^((3:ℝ)/5) := by
      rw [← Real.rpow_mul hnpos.le]; norm_num
    have hvB0 : v ∈ Bset n := inB0 v hv1 (by rw [← hexp]; exact hvle)
    refine ⟨u, ?_, v, hvB0, huv⟩
    rcases hudisj with hup | hule
    · have hun : u ≤ n := le_trans (Nat.le_mul_of_pos_right u (by omega)) (huv ▸ hmn)
      by_cases hule : (u:ℝ) ≤ (n:ℝ)^((3:ℝ)/5)
      · exact inB0 u hu1 hule
      · exact inB1 u hup (not_le.mp hule) hun
    · exact inB0 u hu1 (by rw [← hexp]; exact hule)
  · push Not at hsmall
    by_cases hlp : ∃ p, Nat.Prime p ∧ p ∣ m ∧ (n:ℝ)^((2:ℝ)/5) < (p:ℝ)
    · obtain ⟨p, hpp, hpd, hpbig⟩ := hlp
      have hpn : p ≤ n := le_trans (Nat.le_of_dvd (by omega) hpd) hmn
      refine ⟨p, ?_, m / p, ?_, (Nat.mul_div_cancel' hpd).symm⟩
      · by_cases hple : (p:ℝ) ≤ (n:ℝ)^((3:ℝ)/5)
        · exact inB0 p hpp.pos hple
        · exact inB1 p hpp (not_le.mp hple) hpn
      · exact inB0 (m/p) (Nat.div_pos (Nat.le_of_dvd (by omega) hpd) hpp.pos)
          (quot_le p hpp.pos hpbig.le)
    · push Not at hlp
      by_cases hk : ((Nat.primeFactorsList m).filter (fun p => (n:ℝ)^((1:ℝ)/5) < (p:ℝ))).length ≤ 2
      · obtain ⟨u, hud, hu2, hu3⟩ := exists_mid_divisor n hn m hm1 hsmall hlp hk
        have hupos : 0 < u := Nat.pos_of_dvd_of_pos hud (by omega)
        refine ⟨u, inB0 u hupos hu3, m / u, ?_, (Nat.mul_div_cancel' hud).symm⟩
        exact inB0 (m/u) (Nat.div_pos (Nat.le_of_dvd (by omega) hud) hupos) (quot_le u hupos hu2)
      · have hk3 : 3 ≤ ((Nat.primeFactorsList m).filter (fun p => (n:ℝ)^((1:ℝ)/5) < (p:ℝ))).length := by
          rw [not_le] at hk; omega
        obtain ⟨p, q, r, hpp, hqp, hrp, hrq, hqp', hrbig, hdvd⟩ :=
          exists_three_large_factors n m hm1 hk3
        have hn15pos : (0:ℝ) < (n:ℝ)^((1:ℝ)/5) := Real.rpow_pos_of_pos hnpos _
        have hqbig : (n:ℝ)^((1:ℝ)/5) < (q:ℝ) := lt_of_lt_of_le hrbig (by exact_mod_cast hrq)
        have hn15sq : (n:ℝ)^((1:ℝ)/5) * (n:ℝ)^((1:ℝ)/5) = (n:ℝ)^((2:ℝ)/5) := by
          rw [← Real.rpow_add hnpos]; norm_num
        have hqr_dvd : q * r ∣ m := dvd_trans ⟨p, by ring⟩ hdvd
        have hqrge : (n:ℝ)^((2:ℝ)/5) ≤ ((q*r:ℕ):ℝ) := by
          push_cast; nlinarith [hqbig, hrbig, hn15pos, hn15sq]
        have hqrpos : 0 < q * r := Nat.mul_pos hqp.pos hrp.pos
        have hvB0 : m / (q*r) ∈ Bset n := inB0 (m/(q*r))
          (Nat.div_pos (Nat.le_of_dvd (by omega) hqr_dvd) hqrpos) (quot_le (q*r) hqrpos hqrge)
        refine ⟨q * r, ?_, m / (q*r), hvB0, (Nat.mul_div_cancel' hqr_dvd).symm⟩
        by_cases hqy : (q:ℝ) ≤ (n:ℝ)^((1:ℝ)/3)
        · have hry : (r:ℝ) ≤ (n:ℝ)^((1:ℝ)/3) := le_trans (by exact_mod_cast hrq) hqy
          refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          refine Finset.mem_image.mpr ⟨(q, r), ?_, rfl⟩
          rw [Finset.mem_product]
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqp.pos, Nat.le_floor hqy⟩, hqp⟩,
                 Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hrp.pos, Nat.le_floor hry⟩, hrp⟩⟩
        · have hq_dvd : q ∣ m := dvd_trans ⟨p * r, by ring⟩ hdvd
          have hq25 : (q:ℝ) ≤ (n:ℝ)^((2:ℝ)/5) := hlp q hqp hq_dvd
          have hpqrn : p * q * r ≤ n := le_trans (Nat.le_of_dvd (by omega) hdvd) hmn
          have hqqr : q * q * r ≤ n :=
            le_trans (mul_le_mul_left (mul_le_mul_left hqp' q) r) hpqrn
          refine Finset.mem_union_right _ ?_
          refine Finset.mem_biUnion.mpr ⟨q, ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, Nat.le_floor hq25⟩, hqp⟩
            exact (Nat.floor_lt (by positivity)).2 (not_le.mp hqy)
          · refine Finset.mem_image.mpr ⟨r, ?_, rfl⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hrp.pos, ?_⟩, hrp⟩
            rw [Nat.le_div_iff_mul_le (Nat.mul_pos hqp.pos hqp.pos)]
            calc r * (q * q) = q * q * r := by ring
              _ ≤ n := hqqr

/-- Consequently `F n ≤ |B|`. -/
lemma F_le_Bset_card (n : ℕ) (hn : 2 ≤ n) : F n ≤ (Bset n).card :=
  F_le_basis_card (Bset n) n (multiplicative_basis n hn)

/-! ## Cardinalities of the basis classes -/

/-
The number of primes in `[1, m]` equals `π(m)`.
-/
lemma card_primes_Icc (m : ℕ) :
    ((Finset.Icc 1 m).filter Nat.Prime).card = Nat.primeCounting m := by
  rw [ Nat.primeCounting ];
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
  congr 1 with ( _ | x ) <;> simp +arith +decide

/-
`|B₀| = ⌊n^{3/5}⌋`.
-/
lemma card_B0 (n : ℕ) : (B0 n).card = ⌊(n:ℝ) ^ ((3:ℝ)/5)⌋₊ := by
  unfold B0; aesop;

/-
`|B₂| = π(y)(π(y)+1)/2`, where `y = n^{1/3}`.
-/
lemma card_B2 (n : ℕ) :
    (B2 n).card =
      Nat.primeCounting ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ *
        (Nat.primeCounting ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ + 1) / 2 := by
  rw [ ← card_primes_Icc ];
  rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ];
  unfold Strongly2.B2;
  have h_card : Finset.card (Finset.image (fun pq => pq.1 * pq.2) (Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊) ×ˢ Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊))) = Finset.card (Finset.powersetCard 2 (Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊))) + Finset.card (Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊)) := by
    have h_card : Finset.image (fun pq : ℕ × ℕ => pq.1 * pq.2) (Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n : ℝ) ^ ((1:ℝ)/3)⌋₊) ×ˢ Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n : ℝ) ^ ((1:ℝ)/3)⌋₊)) = Finset.image (fun s : Finset ℕ => s.prod id) (Finset.powersetCard 2 (Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n : ℝ) ^ ((1:ℝ)/3)⌋₊))) ∪ Finset.image (fun p : ℕ => p * p) (Finset.filter Nat.Prime (Finset.Icc 1 ⌊(n : ℝ) ^ ((1:ℝ)/3)⌋₊)) := by
      ext; simp [Finset.mem_image];
      constructor;
      · rintro ⟨ a, b, ⟨ ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, ⟨ ⟨ hb₁, hb₂ ⟩, hb₃ ⟩ ⟩, rfl ⟩;
        by_cases hab : a = b;
        · exact Or.inr ⟨ a, ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, by rw [ hab ] ⟩;
        · exact Or.inl ⟨ { a, b }, ⟨ by aesop_cat, by aesop_cat ⟩, by rw [ Finset.prod_pair hab ] ⟩;
      · rintro ( ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ | ⟨ a, ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, rfl ⟩ );
        · rw [ Finset.card_eq_two ] at ha₂; obtain ⟨ x, y, hxy ⟩ := ha₂; use x, y; simp_all +decide [ Finset.subset_iff ] ;
        · exact ⟨ a, a, ⟨ ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ ⟩, rfl ⟩;
    rw [ h_card, Finset.card_union_of_disjoint ];
    · rw [ Finset.card_image_of_injOn, Finset.card_image_of_injOn ];
      · exact fun x hx y hy hxy => by nlinarith;
      · intro x hx y hy; simp_all +decide [ Finset.mem_powersetCard ] ;
        intro hxy; have := Finset.card_eq_two.mp hx.2; have := Finset.card_eq_two.mp hy.2; obtain ⟨ a, b, ha, hb, hab ⟩ := this; obtain ⟨ c, d, hc, hd, hcd ⟩ := this; simp_all +decide [ Finset.subset_iff ] ;
        -- Since $c$ and $d$ are primes and $c * d = a * b$, it follows that $\{c, d\} = \{a, b\}$.
        have h_eq : c ∣ a ∨ c ∣ b := by
          exact hx.1.2.dvd_mul.mp ( hxy ▸ dvd_mul_right _ _ );
        rcases h_eq with ( h | h ) <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
        · aesop;
        · rw [ mul_comm ] at hxy ; aesop;
    · norm_num [ Finset.disjoint_right ];
      rintro a x hx₁ hx₂ hx₃ rfl y hy₁ hy₂; rw [ Finset.card_eq_two ] at hy₂; obtain ⟨ p, q, hpq ⟩ := hy₂; simp_all +decide [ Finset.subset_iff ] ;
      intro H; have := congr_arg ( ·.factorization ( x : ℕ ) ) H; norm_num at this;
      rw [ Nat.factorization_mul, Nat.factorization_mul ] at this <;> simp_all +decide [ Nat.Prime.ne_zero ];
      grind;
  simp_all +decide [ Nat.choose_two_right ];
  cases k : Finset.card ( Finset.filter Nat.Prime ( Finset.Icc 1 ⌊ ( n : ℝ ) ^ ( 3⁻¹ : ℝ ) ⌋₊ ) ) <;> simp_all +decide [Nat.mul_succ] ; linarith [ Nat.div_mul_cancel ( show 2 ∣ Nat.succ ‹_› * ‹_› from Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ) ) ]

/-
`|B₃| = ∑_{y<q≤n^{2/5}} π(n/q²)`.
-/
lemma card_B3 (n : ℕ) :
    (B3 n).card =
      ∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊(n:ℝ) ^ ((2:ℝ)/5)⌋₊).filter Nat.Prime,
        Nat.primeCounting (n / (q * q)) := by
  convert Finset.card_biUnion _ using 2;
  · rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( Nat.Prime.ne_zero <| Finset.mem_filter.mp ‹_› |>.2 ) hxy ];
    rw [ ← card_primes_Icc ];
  · intros q hq r hr hqr; simp_all +decide [ Finset.disjoint_left ] ;
    intro a x hx₁ hx₂ hx₃ hx₄ y hy₁ hy₂ hy₃ hy₄; subst_vars;
    -- Since $q$ and $r$ are distinct primes, $q$ must divide $y$ and $r$ must divide $x$.
    have hq_div_y : q ∣ y := by
      exact Or.resolve_left ( hq.2.dvd_mul.mp ( hy₄.symm ▸ dvd_mul_right _ _ ) ) ( by rintro H; have := Nat.prime_dvd_prime_iff_eq hq.2 hr.2; tauto )
    have hr_div_x : r ∣ x := by
      exact Or.resolve_left ( hr.2.dvd_mul.mp ( hy₄ ▸ dvd_mul_right _ _ ) ) ( by rintro h; have := Nat.prime_dvd_prime_iff_eq hr.2 hq.2; tauto );
    simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
    rw [ Nat.le_div_iff_mul_le ] at * <;> try nlinarith only [ hx₁, hy₁, hx₂, hy₂ ];
    rw [ Nat.floor_lt ] at * <;> norm_num at *;
    · -- From the inequalities $n^{1/3} < y$ and $n^{1/3} < x$, we get $n < y^3$ and $n < x^3$.
      have hn_lt_y3 : (n : ℝ) < y^3 := by
        exact lt_of_le_of_lt ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( pow_lt_pow_left₀ hq.1 ( by positivity ) ( by positivity ) )
      have hn_lt_x3 : (n : ℝ) < x^3 := by
        exact lt_of_le_of_lt ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( pow_lt_pow_left₀ hr.1 ( by positivity ) ( by positivity ) );
      norm_cast at *; nlinarith only [ hx₂, hy₂, hn_lt_y3, hn_lt_x3, hx₃.two_le, hy₃.two_le ] ;
    · positivity;
    · positivity

/-
`|B₂| = (9/2 + o(1)) S`.
-/
lemma card_B2_asymp (hpnt : PNT) :
    Tendsto (fun n : ℕ => ((B2 n).card : ℝ) / S n) atTop (𝓝 (9/2)) := by
  -- By definition of $k$, we know that $k n = \pi(\lfloor n^{1/3} \rfloor)$.
  set k : ℕ → ℕ := fun n => Nat.primeCounting ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊;
  -- By definition of $k$, we know that $k n \sim \frac{n^{1/3}}{\log n}$.
  have h_k : Filter.Tendsto (fun n : ℕ => (k n : ℝ) / ((n : ℝ) ^ ((1:ℝ)/3) / Real.log n)) Filter.atTop (nhds 3) := by
    have := pi_mul_ratio hpnt 1 one_pos;
    convert this.comp ( tendsto_rpow_atTop ( by norm_num : ( 0 : ℝ ) < 1 / 3 ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) |> ( ·.mul_const 3 ) using 2 <;> norm_num ; ring_nf;
    by_cases h : ‹_› = 0 <;> simp +decide [h] ; ring_nf;
    rw [ Real.log_rpow ( by positivity ) ] ; ring!;
  -- By definition of $B2$, we know that $|B2 n| = \frac{k n (k n + 1)}{2}$.
  have h_B2_card : ∀ n : ℕ, (B2 n).card = (k n * (k n + 1)) / 2 := by
    convert card_B2 using 1;
  -- Substitute the expression for $|B2 n|$ into the limit.
  suffices h_subst : Filter.Tendsto (fun n : ℕ => ((k n : ℝ) * (k n + 1)) / (2 * ((n : ℝ) ^ ((2:ℝ)/3) / (Real.log n)^2))) Filter.atTop (nhds (9 / 2)) by
    convert h_subst using 2 ; norm_num [ h_B2_card, S ] ; ring_nf;
    rw [ Nat.cast_div ] <;> norm_num ; ring ; exact even_iff_two_dvd.mp ( by simp +arith +decide [ parity_simps ] ) ;
  convert h_k.mul ( h_k.add ( tendsto_inv_atTop_zero.comp ( show Filter.Tendsto ( fun n : ℕ => ( n : ℝ ) ^ ( 1 / 3 : ℝ ) / Real.log n ) Filter.atTop ( Filter.atTop ) from ?_ ) ) ) |> ( ·.div_const 2 ) using 2 <;> norm_num ; ring_nf;
  · norm_num [ sq, ← Real.rpow_add', ← Real.rpow_neg ] ; ring;
  · convert tendsto_M_atTop using 1

/-
Prime number theorem with a natural-number argument:
`π(m)·log m / m → 1` as `m → ∞`.
-/
lemma pnt_nat (hpnt : PNT) :
    Tendsto (fun m : ℕ => (Nat.primeCounting m : ℝ) * Real.log m / m) atTop (𝓝 1) := by
  convert Tendsto.comp ( pnt hpnt ) tendsto_natCast_atTop_atTop using 1;
  ext; aesop

/-
For fixed `A > 1`, for all large `n` and every prime `q ∈ (y, Ay]`, writing
`m = n/(q*q)`, the basic size bounds hold.
-/
lemma tw_bounds (A : ℝ) (hA : 1 < A) :
    ∀ᶠ n : ℕ in atTop,
      ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime,
        2 ≤ n / (q * q) ∧
        (n:ℝ) ^ ((1:ℝ)/3) / (2 * A ^ 2) ≤ ((n / (q * q) : ℕ) : ℝ) ∧
        ((n / (q * q) : ℕ) : ℝ) < (n:ℝ) ^ ((1:ℝ)/3) ∧
        (n:ℝ) ^ ((1:ℝ)/3) < (q : ℝ) ∧ (q : ℝ) ≤ A * (n:ℝ) ^ ((1:ℝ)/3) ∧
        ((n / (q * q) : ℕ) : ℝ) * ((q : ℝ) * (q : ℝ)) ≤ (n : ℝ) ∧
        (n : ℝ) < (((n / (q * q) : ℕ) : ℝ) + 1) * ((q : ℝ) * (q : ℝ)) := by
  refine' ( Filter.eventually_atTop.mpr _ );
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n ≥ N₁, (n : ℝ) ^ ((1 : ℝ) / 3) ≥ 4 * A ^ 2 := by
    have hN₁ : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 3)) Filter.atTop Filter.atTop := by
      exact tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop;
    exact Filter.eventually_atTop.mp ( hN₁.eventually_ge_atTop _ );
  refine' ⟨ N₁ + 1, fun n hn q hq => _ ⟩ ; refine' ⟨ _, _, _, _, _ ⟩ <;> norm_num at *;
  · refine' Nat.le_div_iff_mul_le ( Nat.mul_pos hq.2.pos hq.2.pos ) |>.2 _;
    rw [ ← @Nat.cast_le ℝ ] ; norm_num;
    have := hN₁ n hn.le;
    rw [ Nat.le_floor_iff ( by positivity ) ] at hq;
    rw [ show ( n : ℝ ) = ( n ^ ( 1 / 3 : ℝ ) ) ^ 3 by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ] ; nlinarith [ sq_nonneg ( ( n : ℝ ) ^ ( 1 / 3 : ℝ ) - 2 * A ), show ( q : ℝ ) ≥ ⌊ ( n : ℝ ) ^ ( 1 / 3 : ℝ ) ⌋₊ + 1 by exact_mod_cast hq.1.1, Nat.lt_floor_add_one ( ( n : ℝ ) ^ ( 1 / 3 : ℝ ) ) ];
  · rw [ div_le_iff₀ ] <;> try positivity;
    have h_m_lower : (n : ℝ) < ((n / (q * q) : ℕ) + 1) * (q * q) := by
      exact_mod_cast ( by nlinarith [ Nat.div_add_mod n ( q * q ), Nat.mod_lt n ( mul_pos hq.2.pos hq.2.pos ) ] : ( n : ℕ ) < ( n / ( q * q ) + 1 ) * ( q * q ) );
    -- Since $q \leq A * n^{1/3}$, we have $q^2 \leq A^2 * n^{2/3}$.
    have h_q_sq : (q : ℝ) ^ 2 ≤ A ^ 2 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
      convert pow_le_pow_left₀ ( by positivity ) ( show ( q : ℝ ) ≤ A * ( n : ℝ ) ^ ( 1 / 3 : ℝ ) from le_trans ( Nat.cast_le.mpr hq.1.2 ) ( Nat.floor_le ( by positivity ) ) ) 2 using 1 ; ring_nf;
      norm_num [ sq, ← Real.rpow_add' ];
    rw [ show ( n : ℝ ) ^ ( 2 / 3 : ℝ ) = ( n : ℝ ) ^ ( 1 - 1 / 3 : ℝ ) by norm_num, Real.rpow_sub ] at * <;> norm_num at *;
    · rw [ mul_div, le_div_iff₀ ] at * <;> nlinarith [ hN₁ n hn.le, show ( n : ℝ ) > 0 by norm_cast; linarith ];
    · linarith;
  · refine' lt_of_le_of_lt ( Nat.cast_div_le .. ) _;
    rw [ div_lt_iff₀ ] <;> norm_num;
    · have := Nat.lt_of_floor_lt hq.1.1;
      convert mul_lt_mul_of_pos_left ( mul_lt_mul'' this this ( by positivity ) ( by positivity ) ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| pos_of_gt hn ) ( 1 / 3 : ℝ ) ) using 1 ; ring_nf;
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
    · linarith [ hq.2.two_le ];
  · exact Nat.lt_of_floor_lt hq.1.1;
  · exact ⟨ Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hq.1.2 ), by norm_cast; exact Nat.div_mul_le_self _ _, by norm_cast; linarith [ Nat.div_add_mod n ( q * q ), Nat.mod_lt n ( mul_pos hq.2.pos hq.2.pos ) ] ⟩

/-
For fixed `A > 1` and `δ > 0`, for all large `n` and every prime `q ∈ (y, Ay]`,
with `m = n/(q*q)`: `P = π(m)·log m/m ∈ [1-δ, 1+δ]`, `Q = m·q²/n ∈ [1-δ, 1]`,
`R = log n/log m ∈ [3, 3+8δ]`.
-/
lemma tw_PQR (hpnt : PNT) (A : ℝ) (hA : 1 < A) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime,
        let m := n / (q * q)
        (1 - δ) ≤ (Nat.primeCounting m : ℝ) * Real.log m / m ∧
        (Nat.primeCounting m : ℝ) * Real.log m / m ≤ (1 + δ) ∧
        (1 - δ) ≤ (m : ℝ) * ((q : ℝ) * (q : ℝ)) / n ∧
        (m : ℝ) * ((q : ℝ) * (q : ℝ)) / n ≤ 1 ∧
        3 ≤ Real.log n / Real.log m ∧
        Real.log n / Real.log m ≤ 3 + 8 * δ := by
  -- Apply the results from the provided solution to the goal.
  have h_P : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); |((Nat.primeCounting m : ℝ) * Real.log m) / m - 1| ≤ δ := by
    have := pnt_nat hpnt;
    have := Metric.tendsto_atTop.mp this δ hδ;
    obtain ⟨ N, hN ⟩ := this;
    have h_m_ge_N : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1:ℝ)/3) / (2 * A ^ 2)) Filter.atTop Filter.atTop := by
      exact Filter.Tendsto.atTop_div_const ( by positivity ) ( tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
    filter_upwards [ h_m_ge_N.eventually_gt_atTop N, tw_bounds A hA ] with n hn hn';
    exact fun q hq => le_of_lt ( hN _ <| Nat.cast_le.mp <| hn.le.trans <| hn' q hq |>.2.1 );
  have h_Q : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); 1 - δ ≤ (m : ℝ) * ((q : ℝ) * (q : ℝ)) / (n : ℝ) ∧ (m : ℝ) * ((q : ℝ) * (q : ℝ)) / (n : ℝ) ≤ 1 := by
    have h_Q : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); (q : ℝ) * (q : ℝ) / (n : ℝ) ≤ δ := by
      have h_Q : Filter.Tendsto (fun n : ℕ => (A * (n:ℝ) ^ ((1:ℝ)/3)) * (A * (n:ℝ) ^ ((1:ℝ)/3)) / (n:ℝ)) Filter.atTop (nhds 0) := by
        ring_nf;
        norm_num [ sq, ← Real.rpow_add' ];
        norm_num [ mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add' ];
        simpa using tendsto_const_nhds.mul ( tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) );
      filter_upwards [ h_Q.eventually ( gt_mem_nhds hδ ), Filter.eventually_gt_atTop 0 ] with n hn hn' q hq using le_trans ( by gcongr <;> linarith [ show ( q : ℝ ) ≤ A * ( n : ℝ ) ^ ( 1 / 3 : ℝ ) by exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Ioc.mp ( Finset.mem_filter.mp hq |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity ] ) hn.le;
    filter_upwards [ h_Q, tw_bounds A hA ] with n hn hn';
    intro q hq; specialize hn q hq; specialize hn' q hq; rcases eq_or_ne n 0 <;> simp_all +decide ;
    rw [ div_add', le_div_iff₀ ] <;> try positivity;
    exact ⟨ by rw [ div_le_iff₀ ( by positivity ) ] at hn; linarith, by rw [ div_le_iff₀ ( by positivity ) ] ; linarith ⟩;
  have h_R : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); 3 ≤ Real.log n / Real.log m ∧ Real.log n / Real.log m ≤ 3 + 8 * δ := by
    have h_R : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); 3 ≤ Real.log n / Real.log m := by
      have h_R : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); 2 ≤ m ∧ (m : ℝ) < (n:ℝ) ^ ((1:ℝ)/3) := by
        filter_upwards [ tw_bounds A hA ] with n hn q hq using ⟨ hn q hq |>.1, hn q hq |>.2.2.1 ⟩;
      filter_upwards [ h_R, Filter.eventually_gt_atTop 1 ] with n hn hn' ; intro q hq ; specialize hn q hq ; norm_num at *;
      rw [ le_div_iff₀ ( Real.log_pos <| mod_cast hn.1 ), ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> try positivity;
      · exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; exact lt_of_lt_of_le ( pow_lt_pow_left₀ hn.2 ( by positivity ) <| by positivity ) <| by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num;
      · exact pow_pos ( pos_of_gt hn.1 ) _;
      · grind;
    have h_R_upper : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); Real.log n ≤ (3 + 8 * δ) * Real.log m := by
      have h_R_upper : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); Real.log m ≥ (1 / 3) * Real.log n - Real.log (2 * A ^ 2) := by
        have h_R_upper : ∀ᶠ n : ℕ in atTop, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, let m := n / (q * q); (m : ℝ) ≥ (n:ℝ) ^ ((1:ℝ)/3) / (2 * A ^ 2) := by
          filter_upwards [ tw_bounds A hA ] with n hn q hq using hn q hq |>.2.1;
        filter_upwards [ h_R_upper, Filter.eventually_gt_atTop 0 ] with n hn hn' q hq;
        have := hn q hq;
        have := Real.log_le_log ( by positivity ) this;
        rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ) ] at this ; linarith;
      have h_R_upper : ∀ᶠ n : ℕ in atTop, Real.log n ≥ 3 * (3 + 8 * δ) * Real.log (2 * A ^ 2) / (8 * δ) := by
        exact tendsto_log_atTop.comp tendsto_natCast_atTop_atTop |> fun h => h.eventually ( Filter.eventually_ge_atTop _ );
      filter_upwards [ h_R_upper, ‹∀ᶠ n : ℕ in atTop, ∀ q ∈ Finset.filter Nat.Prime ( Finset.Ioc ⌊ ( n : ℝ ) ^ ( 1 / 3 : ℝ ) ⌋₊ ⌊A * ( n : ℝ ) ^ ( 1 / 3 : ℝ ) ⌋₊ ), let m := n / ( q * q ) ; log ↑m ≥ 1 / 3 * log ↑n - log ( 2 * A ^ 2 ) › ] with n hn hn' q hq using by nlinarith [ hn' q hq, mul_div_cancel₀ ( 3 * ( 3 + 8 * δ ) * Real.log ( 2 * A ^ 2 ) ) ( by positivity : ( 8 * δ ) ≠ 0 ) ] ;
    filter_upwards [ h_R, h_R_upper, tw_bounds A hA ] with n hn hn' hn'';
    intro q hq; specialize hn q hq; specialize hn' q hq; specialize hn'' q hq; norm_num at *;
    exact ⟨ hn, by rw [ div_le_iff₀ ( Real.log_pos <| by norm_cast; linarith ) ] ; linarith ⟩;
  filter_upwards [ h_P, h_Q, h_R ] with n hn hn' hn'' using fun q hq => ⟨ by linarith [ abs_le.mp ( hn q hq ) ], by linarith [ abs_le.mp ( hn q hq ) ], hn' q hq |>.1, hn' q hq |>.2, hn'' q hq |>.1, hn'' q hq |>.2 ⟩

/-
For fixed `A > 1` and `ε > 0`, for all large `n` and every prime `q ∈ (y, Ay]`,
the count `π(n/q²)` is within a factor `(3 ± ε)` of `n / (q² log n)`.
-/
lemma card_B3_main_termwise (hpnt : PNT) (A : ℝ) (hA : 1 < A) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime,
        (3 - ε) * (n:ℝ) / ((q:ℝ)^2 * Real.log n) ≤ (Nat.primeCounting (n / (q * q)) : ℝ) ∧
        (Nat.primeCounting (n / (q * q)) : ℝ) ≤ (3 + ε) * (n:ℝ) / ((q:ℝ)^2 * Real.log n) := by
  -- Choose `δ > 0` with `δ < 1`, `(1-δ)^2*3 ≥ 3-ε`, and `(1+δ)*(3+8*δ) ≤ 3+ε`.
  obtain ⟨δ, hδ_pos, hδ_lt_1, hδ_bound⟩ : ∃ δ > 0, δ < 1 ∧ (1 - δ)^2 * 3 ≥ 3 - ε ∧ (1 + δ) * (3 + 8 * δ) ≤ 3 + ε := by
    use Min.min ( ε / 24 ) ( 1 / 32 );
    cases min_cases ( ε / 24 ) ( 1 / 32 ) <;> exact ⟨ by positivity, by linarith, by nlinarith, by nlinarith ⟩;
  filter_upwards [ tw_PQR hpnt A hA δ hδ_pos, tw_bounds A hA, Filter.eventually_gt_atTop 1 ] with n hn hn' hn'' q hq;
  -- Let `m = n/(q*q)`. From `tw_bounds`: `2 ≤ m` (so `(m:ℝ) ≥ 2 > 0` and `Real.log m > 0` by `Real.log_pos`); `q` is prime so `(q:ℝ) > 0`.
  set m := n / (q * q)
  have hm_pos : 2 ≤ m := by
    exact hn' q hq |>.1
  have hm_log_pos : 0 < Real.log m := by
    exact Real.log_pos <| Nat.one_lt_cast.mpr hm_pos
  have hq_pos : 0 < (q : ℝ) := by
    exact Nat.cast_pos.mpr ( Nat.Prime.pos ( Finset.mem_filter.mp hq |>.2 ) );
  -- From `tw_PQR` (unfold the `let m`): abbreviate `P = (π(m):ℝ)*Real.log m/m`, `Q = (m:ℝ)*((q:ℝ)*(q:ℝ))/n`, `R = Real.log n/Real.log m`, with `1-δ ≤ P ≤ 1+δ`, `1-δ ≤ Q ≤ 1`, `3 ≤ R ≤ 3+8*δ`.
  set P := (Nat.primeCounting m : ℝ) * Real.log m / m
  set Q := (m : ℝ) * ((q : ℝ) * (q : ℝ)) / n
  set R := Real.log n / Real.log m
  have hP : 1 - δ ≤ P ∧ P ≤ 1 + δ := by
    exact ⟨ hn q hq |>.1, hn q hq |>.2.1 ⟩
  have hQ : 1 - δ ≤ Q ∧ Q ≤ 1 := by
    exact ⟨ hn q hq |>.2.2.1, hn q hq |>.2.2.2.1 ⟩
  have hR : 3 ≤ R ∧ R ≤ 3 + 8 * δ := by
    exact ⟨ hn q hq |>.2.2.2.2.1, hn q hq |>.2.2.2.2.2 ⟩;
  -- Key identity: `(π(m):ℝ) * ((q:ℝ)*(q:ℝ)) * Real.log n / n = P * Q * R`.
  have hV : (Nat.primeCounting m : ℝ) * ((q : ℝ) * (q : ℝ)) * Real.log n / n = P * Q * R := by
    simp +zetaDelta at *;
    field_simp;
  -- Bound `V = P*Q*R`: since `P,Q,R > 0` (as `δ < 1`, `R ≥ 3`), `V ≥ (1-δ)*(1-δ)*3 ≥ 3-ε` and `V ≤ (1+δ)*1*(3+8*δ) ≤ 3+ε`.
  have hV_bounds : 3 - ε ≤ P * Q * R ∧ P * Q * R ≤ 3 + ε := by
    constructor;
    · refine le_trans ?_ ( mul_le_mul ( mul_le_mul hP.1 hQ.1 ?_ ?_ ) hR.1 ?_ ?_ ) <;> nlinarith;
    · exact le_trans ( mul_le_mul ( mul_le_mul hP.2 hQ.2 ( by nlinarith ) ( by nlinarith ) ) hR.2 ( by nlinarith ) ( by nlinarith ) ) ( by nlinarith );
  rw [ div_le_iff₀, le_div_iff₀ ];
  · rw [ div_eq_iff ] at hV <;> norm_num at *;
    · constructor <;> nlinarith [ show ( n : ℝ ) > 0 by positivity ];
    · linarith;
  · exact mul_pos ( sq_pos_of_pos hq_pos ) ( Real.log_pos ( Nat.one_lt_cast.mpr hn'' ) );
  · exact mul_pos ( sq_pos_of_pos hq_pos ) ( Real.log_pos ( Nat.one_lt_cast.mpr hn'' ) )

/-
The normalized main term `(n/log n)·∑_{y<q≤Ay} 1/q²` divided by `S`
tends to `3(1 - 1/A)`.
-/
lemma card_B3_main_Tratio (hpnt : PNT) (A : ℝ) (hA : 1 < A) :
    Tendsto (fun n : ℕ =>
      ((n:ℝ) / Real.log n *
        (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime,
          (1 / (q:ℝ)^2))) / S n) atTop (𝓝 (3 * (1 - 1/A))) := by
  norm_num [ S ];
  convert Filter.Tendsto.const_mul 3 ( Strongly2.primeSq_interval hpnt A hA |> Filter.Tendsto.comp <| Strongly2.tendsto_y_atTop ) using 2 ; norm_num ; ring_nf;
  · unfold primeSqSum; norm_num [ Real.log_rpow ] ; ring_nf;
    by_cases h : ‹_› = 0 <;> simp +decide [ h, sq, mul_assoc, mul_comm, mul_left_comm ];
    by_cases h' : Real.log ‹ℕ› = 0 <;> simp_all +decide [← mul_assoc, ← Real.rpow_neg] ; ring_nf;
    · norm_cast at * ; aesop;
    · rw [ Real.log_rpow ( by positivity ) ] ; rw [ ← Real.rpow_one_add' ( by positivity ) ] <;> norm_num ; ring_nf ; aesop;
  · norm_num

/-
For fixed `A > 1`, the primes `q` in the main range `(y, Ay]` contribute
`(9(1 - 1/A) + o(1)) S`.
-/
lemma card_B3_main (hpnt : PNT) (A : ℝ) (hA : 1 < A) :
    Tendsto (fun n : ℕ =>
      (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime,
        Nat.primeCounting (n / (q * q)) : ℝ) / S n) atTop (𝓝 (9 * (1 - 1/A))) := by
  -- Using the bounds from card_B3_main_termwise and the fact that R n tends to L, we can show that the ratio tends to 3L.
  have h_ratio : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |((∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (Nat.primeCounting (n / (q * q)) : ℝ)) / S n) - 3 * ((n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) / S n)| ≤ ε := by
    intro ε hε_pos
    obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n ≥ N₁, ∀ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (3 - ε / 8) * (n:ℝ) / ((q:ℝ)^2 * Real.log n) ≤ (Nat.primeCounting (n / (q * q)) : ℝ) ∧ (Nat.primeCounting (n / (q * q)) : ℝ) ≤ (3 + ε / 8) * (n:ℝ) / ((q:ℝ)^2 * Real.log n) := by
      exact Filter.eventually_atTop.mp ( card_B3_main_termwise hpnt A hA ( ε / 8 ) ( by positivity ) ) |> fun ⟨ N₁, hN₁ ⟩ => ⟨ N₁, fun n hn q hq => hN₁ n hn q hq ⟩;
    obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n ≥ N₂, |((n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) / S n) - 3 * (1 - 1 / A)| ≤ 1 := by
      have := card_B3_main_Tratio hpnt A hA;
      exact Filter.eventually_atTop.mp ( this.eventually ( Metric.closedBall_mem_nhds _ zero_lt_one ) );
    refine' ⟨ Max.max N₁ N₂ + 2, fun n hn => _ ⟩ ; specialize hN₁ n ( by linarith [ le_max_left N₁ N₂ ] ) ; specialize hN₂ n ( by linarith [ le_max_right N₁ N₂ ] ) ; simp_all +decide [ Finset.sum_div _ _ _ ];
    -- Applying the bounds from hN₁ and hN₂, we can bound the difference.
    have h_diff_bound : |(∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (Nat.primeCounting (n / (q * q)) : ℝ)) / S n - 3 * ((n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) / S n)| ≤ ε / 8 * ((n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) / S n) := by
      have h_diff_bound : (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (Nat.primeCounting (n / (q * q)) : ℝ)) ≥ (3 - ε / 8) * (n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) ∧ (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (Nat.primeCounting (n / (q * q)) : ℝ)) ≤ (3 + ε / 8) * (n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) := by
        simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        exact ⟨ Finset.sum_le_sum fun x hx => hN₁ x ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ) ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) ( Finset.mem_filter.mp hx |>.2 ) |>.1, Finset.sum_le_sum fun x hx => hN₁ x ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ) ( Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) ( Finset.mem_filter.mp hx |>.2 ) |>.2 ⟩;
      rw [ abs_le ] ; constructor <;> ring_nf at * <;> nlinarith [ inv_pos.mpr ( show 0 < S n from div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ] ) _ ) <| sq_pos_of_pos <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ] ) ] ;
    simp_all +decide [ ← Finset.sum_div _ _ _ ];
    refine le_trans h_diff_bound ?_;
    refine' le_trans ( mul_le_mul_of_nonneg_left ( show ( ( n : ℝ ) / Real.log n * ∑ x ∈ Finset.Ioc ⌊ ( n : ℝ ) ^ ( 3⁻¹ : ℝ ) ⌋₊ ⌊A * ( n : ℝ ) ^ ( 3⁻¹ : ℝ ) ⌋₊ with Nat.Prime x, ( x ^ 2 : ℝ ) ⁻¹ ) / S n ≤ 4 by linarith [ abs_le.mp hN₂, show ( 3 : ℝ ) * ( 1 - A⁻¹ ) ≤ 3 by nlinarith [ inv_mul_cancel₀ ( by linarith : A ≠ 0 ) ] ] ) ( by positivity ) ) ( by linarith );
  have h_tendsto : Filter.Tendsto (fun n : ℕ => 3 * ((n:ℝ) / Real.log n * (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (1 / (q:ℝ)^2)) / S n)) Filter.atTop (nhds (3 * (3 * (1 - 1 / A)))) := by
    exact tendsto_const_nhds.mul ( card_B3_main_Tratio hpnt A hA );
  rw [ Metric.tendsto_nhds ] at *;
  intro ε hε; rcases h_ratio ( ε / 2 ) ( half_pos hε ) with ⟨ N, hN ⟩ ; filter_upwards [ h_tendsto ( ε / 2 ) ( half_pos hε ), Filter.Ici_mem_atTop N ] with n hn hn' using abs_lt.mpr ⟨ by linarith [ abs_lt.mp hn, abs_le.mp ( hN n hn' ) ], by linarith [ abs_lt.mp hn, abs_le.mp ( hN n hn' ) ] ⟩ ;

/-
There is a constant `C₃ > 0` such that for every fixed `A > 1` and all large
`n`, the primes `q` in the tail range `(Ay, n^{2/5}]` contribute at most
`(C₃/A) S`.
-/
lemma card_B3_tail (hpnt : PNT) : ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ A : ℝ, 1 < A →
    ∀ᶠ n : ℕ in atTop,
      (∑ q ∈ (Finset.Ioc ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊(n:ℝ) ^ ((2:ℝ)/5)⌋₊).filter Nat.Prime,
        Nat.primeCounting (n / (q * q)) : ℝ) / S n ≤ C₃ / A := by
  revert hpnt;
  intro hpnt
  obtain ⟨C_π, hC_π_pos, hC_π⟩ := pi_upper hpnt
  obtain ⟨C₂, hC₂_pos, hC₂⟩ := primeSq_tail hpnt;
  refine' ⟨ 18 * C_π * C₂, by positivity, fun A hA => _ ⟩;
  -- For large enough `n`, `y ≥ 2`, `A*y ≥ 2`, `log n > 0`, and for every prime `q ≤ ⌊n^{2/5}⌋` the natural number `m := n/(q*q)` satisfies `log (m:ℝ) ≥ (log n)/6` and `m ≥ 2`.
  have h_large_n : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ^ (1 / 3 : ℝ) ∧ 2 ≤ A * (n : ℝ) ^ (1 / 3 : ℝ) ∧ 0 < Real.log n ∧ ∀ q : ℕ, Nat.Prime q → q ≤ ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊ → Real.log (n / (q * q) : ℝ) ≥ Real.log n / 6 ∧ 2 ≤ n / (q * q) := by
    refine' Filter.eventually_atTop.mpr ⟨ 2 ^ 30, fun n hn => ⟨ _, _, _, _ ⟩ ⟩ <;> norm_num at *;
    · exact le_trans ( by norm_num ) ( Real.rpow_le_rpow ( by positivity ) ( Nat.cast_le.mpr hn ) ( by norm_num ) );
    · exact le_trans ( by nlinarith [ show ( n : ℝ ) ^ ( 1 / 3 : ℝ ) ≥ 2 by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow ( by positivity ) ( Nat.cast_le.mpr hn ) ( by norm_num ) ) ] ) ( mul_le_mul_of_nonneg_right hA.le ( by positivity ) );
    · exact Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith;
    · intro q hq hq'; rw [ Real.log_div ( by positivity ) ( by norm_cast; nlinarith [ hq.two_le ] ) ];
      constructor;
      · rw [ Nat.le_floor_iff ( by positivity ), Real.le_rpow_iff_log_le ] at * <;> norm_num at *;
        · rw [ Real.log_mul ( by norm_cast; linarith [ hq.pos ] ) ( by norm_cast; linarith [ hq.pos ] ) ] ; linarith [ Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ];
        · exact hq.pos;
        · linarith;
      · rw [ Nat.le_floor_iff ( by positivity ), Real.le_rpow_iff_log_le ] at * <;> norm_num at * <;> try linarith;
        · rw [ Nat.le_div_iff_mul_le ( Nat.mul_pos hq.pos hq.pos ) ];
          rw [ ← @Nat.cast_le ℝ ] ; push_cast ; rw [ ← Real.log_le_log_iff ( by norm_cast; nlinarith [ hq.two_le ] ) ( by positivity ) ];
          rw [ Real.log_mul ( by positivity ) ( by norm_cast; nlinarith [ hq.two_le ] ), Real.log_mul ( by norm_cast; nlinarith [ hq.two_le ] ) ( by norm_cast; nlinarith [ hq.two_le ] ) ];
          linarith [ Real.log_le_sub_one_of_pos zero_lt_two, Real.log_pos one_lt_two, show ( Real.log n : ℝ ) ≥ 30 * Real.log 2 by rw [ ← Real.log_rpow, ge_iff_le, Real.log_le_log_iff ] <;> norm_cast ; linarith [ Nat.pow_le_pow_right two_pos ( show 30 ≤ 30 by norm_num ) ] ];
        · exact hq.pos;
  filter_upwards [ h_large_n, Filter.eventually_gt_atTop 1 ] with n hn hn';
  -- Applying the per-term bound to each term in the sum.
  have h_sum_bound : (∑ q ∈ Finset.Ioc ⌊A * (n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊ with Nat.Prime q, (Nat.primeCounting (n / (q * q)) : ℝ)) ≤ 6 * C_π * (n : ℝ) / (Real.log n) * (∑ q ∈ Finset.Ioc ⌊A * (n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊ with Nat.Prime q, (1 / (q : ℝ) ^ 2)) := by
    have h_sum_bound : ∀ q ∈ Finset.Ioc ⌊A * (n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊, Nat.Prime q → (Nat.primeCounting (n / (q * q)) : ℝ) ≤ 6 * C_π * (n : ℝ) / ((q : ℝ) ^ 2 * Real.log n) := by
      intros q hq hq_prime
      have h_pi_bound : (Nat.primeCounting (n / (q * q)) : ℝ) ≤ C_π * (n / (q * q) : ℝ) / Real.log (n / (q * q) : ℝ) := by
        convert hC_π ( n / ( q * q ) ) _ using 1;
        · rw_mod_cast [ Nat.floor_div_natCast, Nat.floor_natCast ];
        · rw [ le_div_iff₀ ] <;> norm_cast;
          · have := hn.2.2.2 q hq_prime ( Finset.mem_Ioc.mp hq |>.2 );
            nlinarith [ Nat.div_mul_le_self n ( q * q ) ];
          · nlinarith [ hq_prime.two_le ];
      refine le_trans h_pi_bound ?_;
      rw [ div_le_div_iff₀ ];
      · have := hn.2.2.2 q hq_prime ( Finset.mem_Ioc.mp hq |>.2 );
        field_simp;
        rw [ mul_div_cancel_left₀ _ ( Nat.cast_ne_zero.mpr hq_prime.ne_zero ) ] ; ring_nf at * ; linarith;
      · exact lt_of_lt_of_le ( by linarith ) ( hn.2.2.2 q hq_prime ( Finset.mem_Ioc.mp hq |>.2 ) |>.1 );
      · exact mul_pos ( sq_pos_of_pos ( Nat.cast_pos.mpr hq_prime.pos ) ) hn.2.2.1;
    rw [ Finset.mul_sum _ _ _ ];
    exact Finset.sum_le_sum fun x hx => by convert h_sum_bound x ( Finset.mem_filter.mp hx |>.1 ) ( Finset.mem_filter.mp hx |>.2 ) using 1 ; ring;
  -- Applying the primeSq_tail bound to the sum.
  have h_primeSq_tail_bound : (∑ q ∈ Finset.Ioc ⌊A * (n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊ with Nat.Prime q, (1 / (q : ℝ) ^ 2)) ≤ C₂ / ((A * (n : ℝ) ^ (1 / 3 : ℝ)) * Real.log (A * (n : ℝ) ^ (1 / 3 : ℝ))) := by
    exact hC₂ _ hn.2.1 _;
  -- Combining the bounds and simplifying.
  have h_combined : (∑ q ∈ Finset.Ioc ⌊A * (n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ⌊(n : ℝ) ^ (2 / 5 : ℝ)⌋₊ with Nat.Prime q, (Nat.primeCounting (n / (q * q)) : ℝ)) ≤ 18 * C_π * C₂ * (n : ℝ) / (A * (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log n) ^ 2) := by
    refine le_trans h_sum_bound <| le_trans ( mul_le_mul_of_nonneg_left h_primeSq_tail_bound <| by exact div_nonneg ( by positivity ) <| by linarith ) ?_;
    rw [ div_mul_div_comm, div_le_div_iff₀ ];
    · rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ) ] ; ring_nf ; norm_num;
      exact mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg hC_π_pos.le ( Nat.cast_nonneg _ ) ) hC₂_pos.le ) ( by positivity ) ) ( by positivity ) ) ( by exact Real.log_nonneg ( by norm_cast; linarith ) ) ) ( Real.log_nonneg ( by linarith ) );
    · exact mul_pos hn.2.2.1 ( mul_pos ( by positivity ) ( Real.log_pos ( by linarith ) ) );
    · exact mul_pos ( by positivity ) ( sq_pos_of_pos hn.2.2.1 );
  rw [ div_le_iff₀ ];
  · convert h_combined using 1 ; norm_num [ S ] ; ring_nf;
    rw [ show ( 2 / 3 : ℝ ) = 1 - 1 / 3 by norm_num, Real.rpow_sub ( by positivity ), Real.rpow_one ] ; ring;
  · exact div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( pos_of_gt hn' ) ) _ ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr hn' ) ) )

/-
`|B₃| = (9 + o(1)) S`.
-/
lemma card_B3_asymp (hpnt : PNT) :
    Tendsto (fun n : ℕ => ((B3 n).card : ℝ) / S n) atTop (𝓝 9) := by
  obtain ⟨ C₃, hC₃_pos, hC₃ ⟩ := Strongly2.card_B3_tail hpnt; norm_num at *; (
  -- For any fixed `A > 1`, we have `main n + tail n - 9 = (main n - 9*(1-1/A)) + tail n - 9/A`.
  have h_split : ∀ A : ℝ, 1 < A → ∀ᶠ n in atTop,
    ((B3 n).card : ℝ) / S n = (∑ q ∈ (Finset.Ioc ⌊(n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊).filter Nat.Prime, (Nat.primeCounting (n / (q * q)) : ℝ)) / S n + (∑ q ∈ (Finset.Ioc ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊ ⌊(n:ℝ) ^ ((2:ℝ)/5)⌋₊).filter Nat.Prime, (Nat.primeCounting (n / (q * q)) : ℝ)) / S n := by
      intro A hA;
      -- For large enough `n`, we have `⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊ ≤ ⌊(n:ℝ) ^ ((2:ℝ)/5)⌋₊`.
      have h_floor : ∀ᶠ n in atTop, ⌊A * (n:ℝ) ^ ((1:ℝ)/3)⌋₊ ≤ ⌊(n:ℝ) ^ ((2:ℝ)/5)⌋₊ := by
        -- We'll use that $A * n^{1/3} < n^{2/5}$ for sufficiently large $n$.
        have h_ineq : ∀ᶠ n in atTop, A * (n : ℝ) ^ ((1:ℝ)/3) < (n : ℝ) ^ ((2:ℝ)/5) := by
          -- We can divide both sides by $n^{1/3}$ to get $A < n^{2/5 - 1/3} = n^{1/15}$.
          suffices h_div : ∀ᶠ n in atTop, A < (n : ℝ) ^ ((1:ℝ)/15) by
            filter_upwards [ h_div, Filter.eventually_gt_atTop 0 ] with n hn hn' using by convert mul_lt_mul_of_pos_right hn ( Real.rpow_pos_of_pos hn' ( 1 / 3 : ℝ ) ) using 1 ; rw [ ← Real.rpow_add hn' ] ; norm_num;
          exact tendsto_rpow_atTop ( by norm_num ) |> fun h => h.eventually_gt_atTop A;
        filter_upwards [ h_ineq ] with n hn using Nat.floor_mono hn.le;
      filter_upwards [ h_floor.natCast_atTop ] with n hn;
      rw [ ← add_div, ← Finset.sum_union ];
      · rw [ ← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc ] <;> norm_num [ hn ];
        · rw [ Strongly2.card_B3 ];
          norm_cast;
        · exact Nat.floor_mono <| le_mul_of_one_le_left ( by positivity ) hA.le;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
  rw [ Metric.tendsto_nhds ] at *;
  intro ε hε_pos
  obtain ⟨A, hA⟩ : ∃ A : ℝ, 1 < A ∧ 9 / A < ε / 2 ∧ C₃ / A < ε / 2 := by
    exact ⟨ 1 + 9 / ( ε / 2 ) + C₃ / ( ε / 2 ), by linarith [ show 0 < 9 / ( ε / 2 ) by positivity, show 0 < C₃ / ( ε / 2 ) by positivity ], by rw [ div_lt_iff₀ ] <;> nlinarith [ show 0 < 9 / ( ε / 2 ) by positivity, show 0 < C₃ / ( ε / 2 ) by positivity, mul_div_cancel₀ 9 ( by positivity : ( ε / 2 ) ≠ 0 ) ], by rw [ div_lt_iff₀ ] <;> nlinarith [ show 0 < 9 / ( ε / 2 ) by positivity, show 0 < C₃ / ( ε / 2 ) by positivity, mul_div_cancel₀ C₃ ( by positivity : ( ε / 2 ) ≠ 0 ) ] ⟩;
  obtain ⟨ N, hN ⟩ := Metric.tendsto_atTop.mp ( Strongly2.card_B3_main hpnt A hA.1 ) ( ε / 2 ) ( half_pos hε_pos ) ; simp_all +decide [ dist_eq_norm ] ;
  obtain ⟨ M, hM ⟩ := hC₃ A hA.1; obtain ⟨ K, hK ⟩ := h_split A hA.1; use Max.max N ( Max.max M K ) ; intros n hn; specialize hN n ( le_trans ( le_max_left _ _ ) hn ) ; specialize hM n ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hn ) ; specialize hK n ( le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hn ) ; simp_all +decide [ abs_lt ] ;
  constructor <;> nlinarith [ inv_mul_cancel₀ ( by linarith : A ≠ 0 ), div_mul_cancel₀ 9 ( by linarith : A ≠ 0 ), div_mul_cancel₀ C₃ ( by linarith : A ≠ 0 ), show 0 ≤ ( ∑ x ∈ Finset.Ioc ⌊A * ( n : ℝ ) ^ ( 3⁻¹ : ℝ ) ⌋₊ ⌊ ( n : ℝ ) ^ ( 2 / 5 : ℝ ) ⌋₊ with Nat.Prime x, ( n / ( x * x ) |> Nat.primeCounting : ℝ ) ) / S n from div_nonneg ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) ( show 0 ≤ S n from div_nonneg ( by positivity ) ( sq_nonneg _ ) ) ]);

/-
`|B₀| + |B₁| = π(n) + o(S)`.
-/
lemma card_B0B1_sub :
    Tendsto (fun n : ℕ =>
      (((B0 n).card + (B1 n).card : ℝ) - Nat.primeCounting n) / S n) atTop (𝓝 0) := by
  -- By definition of $B0$ and $B1$, we know that for $n \geq 2$, $(B0 n).card + (B1 n).card = \lfloor (n:ℝ)^{3/5} \rfloor + (\pi(n) - \pi(\lfloor (n:ℝ)^{3/5} \rfloor))$.
  have h_card : ∀ n ≥ 2, (B0 n).card + (B1 n).card = Nat.primeCounting n + (⌊(n:ℝ) ^ ((3:ℝ)/5)⌋₊ - Nat.primeCounting ⌊(n:ℝ) ^ ((3:ℝ)/5)⌋₊) := by
    intros n hn; rw [ card_B0, show B1 n = ( Finset.Ioc ⌊ ( n : ℝ ) ^ ( 3 / 5 : ℝ ) ⌋₊ n ).filter Nat.Prime from rfl ] ; rw [ card_primes_Ioc ] ; ring_nf;
    · have h_card : Nat.primeCounting n ≥ Nat.primeCounting ⌊(n:ℝ) ^ ((3:ℝ)/5)⌋₊ := by
        exact Nat.monotone_primeCounting <| Nat.floor_le_of_le <| by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) <| show ( 3 : ℝ ) / 5 ≤ 1 by norm_num ) <| by norm_num;
      linarith [ Nat.sub_add_cancel h_card, Nat.sub_add_cancel ( show ⌊ ( n : ℝ ) ^ ( 3 / 5 : ℝ ) ⌋₊.primeCounting ≤ ⌊ ( n : ℝ ) ^ ( 3 / 5 : ℝ ) ⌋₊ from primeCounting_le_self _ ) ];
    · exact Nat.floor_le_of_le ( le_trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( show ( 3 : ℝ ) / 5 ≤ 1 by norm_num ) ) ( by norm_num ) );
  -- Using the fact that $|B₀| + |B₁| = π(n) + o(S)$, we can bound the expression.
  have h_bound : ∀ n ≥ 2, |((B0 n).card + (B1 n).card - Nat.primeCounting n : ℝ)| ≤ (n:ℝ) ^ ((3:ℝ)/5) := by
    intro n hn; rw [ abs_of_nonneg ] <;> norm_cast <;> norm_num [ h_card n hn ];
    · exact le_trans ( Nat.cast_le.mpr ( Nat.sub_le _ _ ) ) ( Nat.floor_le ( by positivity ) );
    · grind +qlia;
  refine' squeeze_zero_norm' _ _;
  use fun n => ( n : ℝ ) ^ ( 3 / 5 : ℝ ) / S n;
  · filter_upwards [ Filter.eventually_ge_atTop 2 ] with n hn using by rw [ Real.norm_eq_abs, abs_div, abs_of_nonneg ( show 0 ≤ S n from div_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( sq_nonneg _ ) ) ] ; exact div_le_div_of_nonneg_right ( h_bound n hn ) ( div_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( sq_nonneg _ ) ) ;
  · convert n35_div_S_tendsto_zero using 1

/-
For every `ε > 0`, eventually `F(n) - π(n) ≤ (27/2 + ε) S`.
-/
lemma F_upper (hpnt : PNT) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (F n : ℝ) - Nat.primeCounting n ≤ (27/2 + ε) * S n := by
  -- By added TestTendsto.tendsto_add, we know that
  have h_add : Filter.Tendsto (fun n : ℕ => (((B0 n).card + (B1 n).card : ℝ) - Nat.primeCounting n) / S n + ((B2 n).card : ℝ) / S n + ((B3 n).card : ℝ) / S n) Filter.atTop (nhds ((0 : ℝ) + (9 / 2 : ℝ) + 9)) := by
    exact Filter.Tendsto.add ( Filter.Tendsto.add ( by simpa using card_B0B1_sub ) ( by simpa using card_B2_asymp hpnt ) ) ( by simpa using card_B3_asymp hpnt );
  -- By added TestTendsto.tendsto_add, we know that for sufficiently large n, the sum is less than 27/2 + ε.
  have h_bound : ∀ᶠ n in Filter.atTop, (((B0 n).card + (B1 n).card : ℝ) - Nat.primeCounting n) / S n + ((B2 n).card : ℝ) / S n + ((B3 n).card : ℝ) / S n < (27 / 2 + ε) := by
    exact h_add.eventually ( gt_mem_nhds <| by linarith );
  filter_upwards [ h_bound, Filter.eventually_ge_atTop 2 ] with n hn hn';
  -- By definition of $F$, we know that $F(n) \leq (Bset n).card$.
  have h_F_le_Bset : (F n : ℝ) ≤ ((B0 n).card + (B1 n).card + (B2 n).card + (B3 n).card : ℝ) := by
    exact_mod_cast le_trans ( F_le_Bset_card n hn' ) ( by exact_mod_cast Finset.card_union_le _ _ |> le_trans <| add_le_add ( Finset.card_union_le _ _ |> le_trans <| add_le_add ( Finset.card_union_le _ _ ) le_rfl ) le_rfl );
  rw [ ← add_div, ← add_div, div_lt_iff₀ ] at hn <;> nlinarith [ show 0 < S n from by exact div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| by linarith ) _ ) ( sq_pos_of_pos <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) ]

/-! ## Admissible cells and their weights -/

/-- `Δ_i = e^{(i+1)h} - e^{ih}`. -/
noncomputable def Delta (h : ℝ) (i : ℤ) : ℝ := Real.exp ((i + 1) * h) - Real.exp (i * h)

/-- A pair `(i, j) ∈ ℤ²` is an *admissible cell* if `i ≤ j` and `i + 2j ≤ -4`. -/
def Admissible (c : ℤ × ℤ) : Prop := c.1 ≤ c.2 ∧ c.1 + 2 * c.2 ≤ -4

/-- The third index of a cell `(i, j)` is `k = -i - j - 3`. -/
def thirdIndex (c : ℤ × ℤ) : ℤ := -c.1 - c.2 - 3

/-
**Order and sum of the cell indices.**
-/
lemma cell_order (c : ℤ × ℤ) (hc : Admissible c) :
    c.1 ≤ c.2 ∧ c.2 < thirdIndex c ∧ c.1 + c.2 + thirdIndex c = -3 ∧
      thirdIndex c - c.2 ≥ 1 := by
  exact ⟨ hc.1, by unfold thirdIndex; linarith [ hc.1, hc.2 ], by unfold thirdIndex; linarith [ hc.1, hc.2 ], by unfold thirdIndex; linarith [ hc.1, hc.2 ] ⟩

/-- The `C_N⁻` truncation. -/
def CNneg (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range N ×ˢ Finset.range N).image
    (fun p => (-(p.1 : ℤ) - (p.2 : ℤ) - 2, -(p.1 : ℤ) - 1))

/-- The `C_N⁺` truncation. -/
def CNpos (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range N ×ˢ Finset.range N).image
    (fun p => (-2 * (p.1 : ℤ) - (p.2 : ℤ) - 4, (p.1 : ℤ)))

/-- The `C_N⁰` (diagonal) truncation. -/
def CNzero (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range N).image (fun a : ℕ => (-(a : ℤ) - 2, -(a : ℤ) - 2))

/-- The full truncation `C_N = C_N⁻ ∪ C_N⁺ ∪ C_N⁰`. -/
def CN (N : ℕ) : Finset (ℤ × ℤ) := CNneg N ∪ CNpos N ∪ CNzero N

/-- The cell weight `W_h(C)`. -/
noncomputable def Wh (h : ℝ) (C : Finset (ℤ × ℤ)) : ℝ :=
  (∑ c ∈ C.filter (fun c => c.1 < c.2), Delta h c.1 * Delta h c.2)
    + (1/2) * ∑ c ∈ C.filter (fun c => c.1 = c.2), (Delta h c.1) ^ 2

/-
Every member of `C_N` is admissible.
-/
lemma CN_admissible (N : ℕ) : ∀ c ∈ CN N, Admissible c := by
  -- By definition of CN, we know that every element in CN N is admissible.
  unfold CN Admissible; simp [CNneg, CNpos, CNzero]; (
  grind)

/-
For `h > 0`, `W_h(C_N) → e^{-h} + ½ e^{-2h}` as `N → ∞`.
-/
lemma Wh_CN_limit (h : ℝ) (hh : 0 < h) :
    Tendsto (fun N : ℕ => Wh h (CN N)) atTop
      (𝓝 (Real.exp (-h) + (1/2) * Real.exp (-2*h))) := by
  unfold Wh;
  -- Let's rewrite the expression using the definitions of `Delta` and `Wh`.
  suffices h_suff : Filter.Tendsto (fun N => (∑ a ∈ Finset.range N, ∑ d ∈ Finset.range N, Delta h (-a - d - 2) * Delta h (-a - 1)) + (∑ b ∈ Finset.range N, ∑ d ∈ Finset.range N, Delta h (-2 * b - d - 4) * Delta h b) + (1 / 2) * (∑ a ∈ Finset.range N, Delta h (-a - 2) ^ 2)) Filter.atTop (nhds (Real.exp (-h) + (1 / 2) * Real.exp (-2 * h))) by
    convert h_suff using 3;
    · unfold CN CNneg CNpos CNzero; norm_num [ Finset.sum_filter, Finset.sum_image ] ;
      rw [ Finset.sum_union, Finset.sum_union ];
      · rw [ Finset.sum_image, Finset.sum_image, Finset.sum_image ] <;> norm_num [ Finset.sum_product ];
        · exact congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => if_pos <| by linarith ) ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => if_pos <| by linarith );
        · norm_num [ Set.InjOn ];
          intros; subst_vars; exact ⟨ rfl, by linarith ⟩ ;
        · norm_num [ Set.InjOn ];
          intros; omega;
      · norm_num [ Finset.disjoint_left ];
        intros; subst_vars; omega;
      · norm_num [ Finset.disjoint_left ];
        grind;
    · rw [ show CN _ = CNneg _ ∪ CNpos _ ∪ CNzero _ from rfl ] ; norm_num [ CNneg, CNpos, CNzero ] ; ring_nf;
      rw [ Finset.sum_subset ];
      any_goals exact Finset.image ( fun a : ℕ => ( -2 - a, -2 - a ) ) ( Finset.range ‹_› );
      · rw [ Finset.sum_image ] ; aesop;
      · grind;
      · grind;
  -- Let's simplify the expression inside the limit.
  suffices h_simp : Filter.Tendsto (fun N => (Real.exp h - 1) ^ 2 * (Real.exp (-h)) ^ 3 * (∑ a ∈ Finset.range N, (Real.exp (-2 * h)) ^ a) * (∑ d ∈ Finset.range N, (Real.exp (-h)) ^ d) + (Real.exp h - 1) ^ 2 * (Real.exp (-h)) ^ 4 * (∑ b ∈ Finset.range N, (Real.exp (-h)) ^ b) * (∑ d ∈ Finset.range N, (Real.exp (-h)) ^ d) + (1 / 2) * (Real.exp h - 1) ^ 2 * (Real.exp (-h)) ^ 4 * (∑ a ∈ Finset.range N, (Real.exp (-2 * h)) ^ a)) Filter.atTop (nhds (Real.exp (-h) + (1 / 2) * Real.exp (-2 * h))) by
    convert h_simp using 3 <;> norm_num [ Delta ] ; ring_nf;
    · norm_num [ ← Real.exp_add, ← Real.exp_nat_mul ] ; ring_nf;
      norm_num [ Finset.mul_sum _ _ _, Finset.sum_add_distrib, Finset.sum_mul, Real.exp_add, Real.exp_sub, Real.exp_neg ] ; ring_nf;
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, sq ] ; ring_nf;
    · rw [ Finset.mul_sum _ _ _ ] ; rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; ring_nf ; norm_num [ ← Real.exp_nat_mul, ← Real.exp_add ] ; ring_nf;
  -- Recognize that the sums are geometric series and apply the formula for their sum.
  have h_geo_series : Filter.Tendsto (fun N => (∑ a ∈ Finset.range N, (Real.exp (-2 * h)) ^ a)) Filter.atTop (nhds (1 / (1 - Real.exp (-2 * h)))) ∧ Filter.Tendsto (fun N => (∑ d ∈ Finset.range N, (Real.exp (-h)) ^ d)) Filter.atTop (nhds (1 / (1 - Real.exp (-h)))) := by
    exact ⟨ by simpa using ( hasSum_geometric_of_lt_one ( by positivity ) ( by norm_num; positivity ) ) |> HasSum.tendsto_sum_nat, by simpa using ( hasSum_geometric_of_lt_one ( by positivity ) ( by norm_num; positivity ) ) |> HasSum.tendsto_sum_nat ⟩;
  convert Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.mul ( Filter.Tendsto.mul ( tendsto_const_nhds ) h_geo_series.1 ) h_geo_series.2 ) ( Filter.Tendsto.mul ( Filter.Tendsto.mul ( tendsto_const_nhds ) h_geo_series.2 ) h_geo_series.2 ) ) ( Filter.Tendsto.mul ( tendsto_const_nhds ) h_geo_series.1 ) using 2 ; norm_num [ Real.exp_neg ];
  field_simp;
  rw [ eq_div_iff ( sub_ne_zero_of_ne <| by norm_num; linarith ) ] ; ring_nf;
  rw [ show h * 2 = h + h by ring, Real.exp_add ] ; ring_nf;
  nlinarith [ Real.exp_pos h, pow_pos ( Real.exp_pos h ) 3, pow_pos ( Real.exp_pos h ) 4, pow_pos ( Real.exp_pos h ) 5, pow_pos ( Real.exp_pos h ) 6, pow_pos ( Real.exp_pos h ) 7, pow_pos ( Real.exp_pos h ) 8, mul_inv_cancel₀ ( show -1 + Real.exp h ^ 2 ≠ 0 by nlinarith [ Real.add_one_le_exp h, pow_pos ( Real.exp_pos h ) 2 ] ) ]

/-
For every `ε > 0` there are `h > 0` and `N` with `9 · W_h(C_N) > 27/2 - ε`.
-/
lemma near_maximal_weight (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∃ N : ℕ, (27:ℝ)/2 - ε < 9 * Wh h (CN N) := by
  -- Let `g h := 9 * (Real.exp (-h) + (1/2) * Real.exp (-2*h))`. `g` is continuous and `g 0 = 9*(1 + 1/2) = 27/2`.
  set g : ℝ → ℝ := fun h => 9 * (Real.exp (-h) + (1/2) * Real.exp (-2 * h))
  have hg_cont : ContinuousAt g 0 := by
    fun_prop
  have hg_zero : g 0 = 27 / 2 := by
    norm_num [ g ]
  have hg_gt : ∃ h, 0 < h ∧ g h > 27 / 2 - ε / 2 := by
    have := Metric.continuousAt_iff.mp hg_cont ( ε / 2 ) ( half_pos hε );
    exact Exists.elim this fun δ hδ => ⟨ δ / 2, half_pos hδ.1, by linarith [ abs_lt.mp ( hδ.2 ( show |δ / 2 - 0| < δ by rw [ abs_of_pos ] <;> linarith ) ) ] ⟩;
  obtain ⟨ h, hh_pos, hh_gt ⟩ := hg_gt; have := Wh_CN_limit h hh_pos; simp_all +decide [ Metric.tendsto_nhds ] ;
  simp +zetaDelta at *;
  exact Exists.elim ( this ( ( 9 * ( Real.exp ( -h ) + 2⁻¹ * Real.exp ( - ( 2 * h ) ) ) - ( 27 / 2 - ε / 2 ) ) / 9 ) ( by linarith ) ) fun N hN => ⟨ h, hh_pos, N, by linarith [ abs_lt.mp ( hN N le_rfl ) ] ⟩

/-! ## Finite proper edge-colourings -/

/-
If `|C| ≥ max(|X|, |Y|)`, then the complete bipartite graph with parts `X` and
`Y` has a proper edge-colouring with colours in `C`: distinct edges sharing an
endpoint get distinct colours.
-/
lemma complete_bipartite_colouring {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [Nonempty γ] (X : Finset α) (Y : Finset β) (C : Finset γ)
    (h : max X.card Y.card ≤ C.card) :
    ∃ χ : α → β → γ,
      (∀ x ∈ X, ∀ y ∈ Y, χ x y ∈ C) ∧
      (∀ x ∈ X, ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → χ x y ≠ χ x y') ∧
      (∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y, x ≠ x' → χ x y ≠ χ x' y) := by
  -- If `m = 0`, then `X = ∅` and `Y = ∅`; take `χ = fun _ _ => Classical.arbitrary γ` and all conditions hold vacuously.
  by_cases hm : max X.card Y.card = 0;
  · aesop;
  · -- Otherwise `m ≥ 1`. Build `f : α → ZMod m` injective on `X` (from `X ≃ Fin X.card ↪ Fin m ≃ ZMod m`, extended by `0` off `X`) and `g : β → ZMod m` injective on `Y` similarly.
    obtain ⟨m, hm⟩ : ∃ m, max X.card Y.card = m ∧ m ≥ 1 := by
      exact ⟨ _, rfl, Nat.pos_of_ne_zero hm ⟩
    obtain ⟨f, hf⟩ : ∃ f : α → ZMod m, ∀ x x', x ∈ X → x' ∈ X → x ≠ x' → f x ≠ f x' := by
      -- Since $X$ is a finite set, we can construct an injective function $f : X \to \mathbb{Z}/m\mathbb{Z}$.
      obtain ⟨f, hf_inj⟩ : ∃ f : X → ZMod m, Function.Injective f := by
        have h_inj : Nonempty (X ↪ Fin m) := by
          exact ⟨ ( Function.Embedding.trans ( Fintype.equivFinOfCardEq ( by aesop ) |> Equiv.toEmbedding ) ( Fin.castLEEmb ( by aesop ) ) ) ⟩;
        have h_inj : Nonempty (Fin m ↪ ZMod m) := by
          rcases m with ( _ | _ | m ) <;> simp_all +decide [ ZMod ];
          · exact ⟨ ⟨ fun x => x, fun x y hxy => by simp [ Fin.ext_iff ] ⟩ ⟩;
          · exact ⟨ ⟨ fun x => x, fun x y hxy => by simpa using hxy ⟩ ⟩;
        exact ⟨ _, Function.Injective.comp h_inj.some.injective ( ‹Nonempty ( X ↪ Fin m ) ›.some.injective ) ⟩;
      exact ⟨ fun x => if hx : x ∈ X then f ⟨ x, hx ⟩ else 0, fun x x' hx hx' hne => by simpa [ hx, hx', hne ] using hf_inj.ne ( show ⟨ x, hx ⟩ ≠ ⟨ x', hx' ⟩ from by simpa [ Subtype.ext_iff ] using hne ) ⟩
    obtain ⟨g, hg⟩ : ∃ g : β → ZMod m, ∀ y y', y ∈ Y → y' ∈ Y → y ≠ y' → g y ≠ g y' := by
      have h_inj : Nonempty (Y ↪ ZMod m) := by
        have h_card : Y.card ≤ m := by
          exact hm.1 ▸ le_max_right _ _;
        have h_card : Nonempty (Y ↪ Fin m) := by
          exact ⟨ ( Function.Embedding.trans ( Equiv.toEmbedding ( Fintype.equivFinOfCardEq ( by simp +decide ) ) ) ( Fin.castLEEmb h_card ) ) ⟩;
        rcases m with ( _ | _ | m ) <;> simp_all +decide [ ZMod ];
      obtain ⟨ g ⟩ := h_inj; use fun y => if hy : y ∈ Y then g ⟨ y, hy ⟩ else 0; aesop;
    -- Since `m ≤ C.card`, get a subset `t ⊆ C` with `t.card = m` (`Finset.exists_subset_card_eq`), and an equiv `ZMod m ≃ t` (`Fintype.equivOfCardEq`, using `ZMod.card`), giving `emb : ZMod m → γ` injective with `emb z ∈ C` for all `z`.
    obtain ⟨t, ht⟩ : ∃ t : Finset γ, t ⊆ C ∧ t.card = m := by
      exact Finset.exists_subset_card_eq ( by aesop )
    obtain ⟨emb, h_emb⟩ : ∃ emb : ZMod m → γ, Function.Injective emb ∧ ∀ z, emb z ∈ t := by
      rcases m with ( _ | m ) <;> simp_all +decide [ ZMod ];
      have := Finset.equivFinOfCardEq ht.2;
      exact ⟨ fun z => this.symm z, Subtype.val_injective.comp this.symm.injective, fun z => this.symm z |>.2 ⟩;
    refine' ⟨ fun x y => emb ( f x - g y ), _, _, _ ⟩ <;> simp_all +decide [ Function.Injective.eq_iff h_emb.1 ];
    exact fun x hx y hy => ht.1 ( h_emb.2 _ )

/-
If `|C| ≥ |X|`, then the complete graph on `X` has a proper edge-colouring with
colours in `C`, given by a symmetric function `χ` such that at each vertex the
incident edges receive distinct colours.
-/
lemma complete_graph_colouring {α γ : Type*} [DecidableEq α] [Nonempty γ]
    (X : Finset α) (C : Finset γ) (h : X.card ≤ C.card) :
    ∃ χ : α → α → γ,
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → χ x y ∈ C) ∧
      (∀ x ∈ X, ∀ y ∈ X, χ x y = χ y x) ∧
      (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c → χ a b ≠ χ a c) := by
  by_contra h_not_symm;
  -- Let's choose any finite set of colors `C` with `C.card ≥ X.card`.
  obtain ⟨χ, hχ⟩ : ∃ χ : α → α → ℕ, (∀ x ∈ X, ∀ y ∈ X, x ≠ y → χ x y < X.card) ∧ (∀ x ∈ X, ∀ y ∈ X, χ x y = χ y x) ∧ (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c → χ a b ≠ χ a c) := by
    -- Let's choose any finite set of colors `C` with `C.card ≥ X.card` and construct a proper edge-colouring for the complete graph on `X`.
    obtain ⟨f, hf⟩ : ∃ f : α → Fin X.card, ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f x ≠ f y := by
      obtain ⟨f, hf⟩ : ∃ f : X → Fin X.card, Function.Injective f := by
        exact ⟨ fun x => Fintype.equivFinOfCardEq ( by simp +decide ) x, by simp +decide [ Function.Injective ] ⟩;
      exact ⟨ fun x => if hx : x ∈ X then f ⟨ x, hx ⟩ else ⟨ 0, Fin.pos ( Fin.mk 0 ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ) ) ) ⟩, fun x hx y hy hxy => by simpa [ hx, hy, hxy ] using hf.ne ( by aesop_cat ) ⟩;
    refine' ⟨ fun x y => ( f x + f y |> Fin.val ) % X.card, _, _, _ ⟩ <;> simp +decide [Fin.val_add];
    · exact fun x hx y hy hxy => Nat.mod_lt _ ( Finset.card_pos.mpr ⟨ x, hx ⟩ );
    · exact fun x hx y hy => by rw [ add_comm ] ;
    · intro a ha b hb c hc hab hbc hca H; have := Nat.modEq_iff_dvd.1 H.symm; simp_all +decide [Fin.ext_iff] ;
      exact hf b hb c hc hca ( by obtain ⟨ k, hk ⟩ := this; nlinarith [ show k = 0 by nlinarith [ Fin.is_lt ( f b ), Fin.is_lt ( f c ) ] ] );
  obtain ⟨f, hf⟩ : ∃ f : Fin X.card ↪ γ, ∀ i, f i ∈ C := by
    obtain ⟨ s, hs ⟩ := Finset.exists_subset_card_eq h;
    have h_equiv : Nonempty (Fin X.card ≃ s) := by
      exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ hs.2 ] ⟩;
    exact ⟨ ⟨ fun i => h_equiv.some i, fun i j hij => by simpa [ Fin.ext_iff ] using h_equiv.some.injective ( Subtype.ext hij ) ⟩, fun i => hs.1 ( h_equiv.some i |>.2 ) ⟩;
  refine' h_not_symm ⟨ fun x y => if hx : x ∈ X then if hy : y ∈ X then if hxy : x = y then Classical.arbitrary γ else f ⟨ χ x y, hχ.1 x hx y hy hxy ⟩ else Classical.arbitrary γ else Classical.arbitrary γ, _, _, _ ⟩ <;> simp +decide [ * ];
  · grind;
  · grind;
  · simp +contextual [ hχ.2.2, f.injective.eq_iff ]

/-! ## Linear prime triples -/

/-- The vertex set of a family `H` of triples. -/
def Vset (H : Finset (Finset ℕ)) : Finset ℕ := Finset.biUnion H id

open Classical in
/-- The strongly-2-primitive set built from a linear family `H`: retained primes
(those `≤ n` not used by any triple) together with the triple products. -/
noncomputable def AH (n : ℕ) (H : Finset (Finset ℕ)) : Finset ℕ :=
  ((Finset.Icc 1 n).filter (fun p => Nat.Prime p ∧ p ∉ Vset H))
    ∪ H.image (fun E => ∏ p ∈ E, p)

/-
If `H` is a finite linear family of 3-element sets of distinct primes with each
product `≤ n`, then `A_H ⊆ [n]` is strongly 2-primitive with
`|A_H| + |V(H)| = π(n) + |H|`. -/
lemma linear_triple_replacement (n : ℕ) (H : Finset (Finset ℕ))
    (h3 : ∀ E ∈ H, E.card = 3)
    (hprime : ∀ E ∈ H, ∀ p ∈ E, Nat.Prime p)
    (hprod : ∀ E ∈ H, (∏ p ∈ E, p) ≤ n)
    (hlin : ∀ E ∈ H, ∀ E' ∈ H, E ≠ E' → (E ∩ E').card ≤ 1) :
    Strongly2Primitive (AH n H) ∧ AH n H ⊆ Finset.Icc 1 n ∧
      (AH n H).card + (Vset H).card =
        ((Finset.Icc 1 n).filter Nat.Prime).card + H.card := by
  refine' ⟨ _, _, _ ⟩;
  · -- Take `a ∈ AH`, `b,c ∈ AH`, `a ≠ b`, `a ≠ c`; show `¬ a ∣ b*c`.
    intro a ha b hb c hc hab hbc
    by_cases ha_prime : a ∈ ((Finset.Icc 1 n).filter (fun p => Nat.Prime p ∧ p ∉ Vset H));
    · -- Since $a$ is a prime not in $Vset H$, it cannot divide any element of $H.image (fun E => ∏ p ∈ E, p)$.
      have h_not_div_H : ∀ E ∈ H, ¬(a ∣ ∏ p ∈ E, p) := by
        intro E hE; rw [ Nat.Prime.dvd_iff_not_coprime ] <;> simp_all +decide [Nat.coprime_prod_right_iff] ;
        exact fun p hp => ha_prime.2.1.coprime_iff_not_dvd.mpr fun h => ha_prime.2.2 <| Finset.mem_biUnion.mpr ⟨ E, hE, by have := Nat.prime_dvd_prime_iff_eq ha_prime.2.1 ( hprime E hE p hp ) ; aesop ⟩;
      unfold AH at hb hc; simp_all +decide [ Nat.Prime.dvd_mul ] ;
      rcases hb with ( ⟨ hb₁, hb₂, hb₃ ⟩ | ⟨ E, hE₁, rfl ⟩ ) <;> rcases hc with ( ⟨ hc₁, hc₂, hc₃ ⟩ | ⟨ F, hF₁, rfl ⟩ ) <;> simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
    · -- Since `a` is not a retained prime, it must be a product of three distinct primes from some `E ∈ H`.
      obtain ⟨E, hE, rfl⟩ : ∃ E ∈ H, a = ∏ p ∈ E, p := by
        unfold AH at ha; aesop;
      -- Each element of `AH \ {a}` shares at most one prime of `E`: a retained prime shares none (retained primes are `∉ Vset H ⊇ E`), and any other triple product `∏_{E'}` shares at most one prime of `E` by linearity `hlin` (`(E ∩ E').card ≤ 1`).
      have h_share : ∀ x ∈ AH n H, x ≠ ∏ p ∈ E, p → (E.filter (fun p => p ∣ x)).card ≤ 1 := by
        intro x hx hx_ne; by_cases hx_prime : x ∈ ((Finset.Icc 1 n).filter (fun p => Nat.Prime p ∧ p ∉ Vset H)); simp_all +decide ;
        · exact Finset.card_le_one.mpr fun p hp q hq => by have := Nat.prime_dvd_prime_iff_eq ( hprime E hE p ( Finset.mem_filter.mp hp |>.1 ) ) hx_prime.2.1; have := Nat.prime_dvd_prime_iff_eq ( hprime E hE q ( Finset.mem_filter.mp hq |>.1 ) ) hx_prime.2.1; aesop;
        · -- Since `x` is not a retained prime, it must be a product of three distinct primes from some `E' ∈ H`.
          obtain ⟨E', hE', rfl⟩ : ∃ E' ∈ H, x = ∏ p ∈ E', p := by
            unfold AH at hx; aesop;
          convert hlin E hE E' hE' _ using 1;
          · congr 1 with p ; simp +decide ;
            intro hp; rw [ Nat.Prime.dvd_iff_not_coprime ( hprime E hE p hp ) ] ; simp +decide [ Nat.coprime_prod_right_iff ] ;
            exact ⟨ fun ⟨ q, hq, hq' ⟩ => by have := Nat.coprime_primes ( hprime E hE p hp ) ( hprime E' hE' q hq ) ; aesop, fun hq => ⟨ p, hq, by have := Nat.Prime.ne_one ( hprime E hE p hp ) ; aesop ⟩ ⟩;
          · grind;
      -- If `a ∣ b*c`, then all three primes of `E` divide `b*c`; each prime of `E` divides `b` or `c`; by pigeonhole two of them divide the same one of `b,c`, contradicting that `b` (resp. `c`) shares at most one prime with `E`.
      by_contra h_div
      have h_div_bc : (E.filter (fun p => p ∣ b)).card + (E.filter (fun p => p ∣ c)).card ≥ 3 := by
        have h_div_bc : ∀ p ∈ E, p ∣ b ∨ p ∣ c := by
          exact fun p hp => Nat.Prime.dvd_mul ( hprime E hE p hp ) |>.1 ( dvd_trans ( Finset.dvd_prod_of_mem _ hp ) h_div );
        rw [ ← h3 E hE, ← Finset.card_union_add_card_inter ];
        exact le_add_right ( Finset.card_le_card fun x hx => by specialize h_div_bc x hx; aesop );
      linarith [ h_share b hb ( by tauto ), h_share c hc ( by tauto ) ];
  · intro x hx; simp_all +decide [ AH ] ;
    rcases hx with ( ⟨ hx₁, hx₂, hx₃ ⟩ | ⟨ E, hE₁, rfl ⟩ ) <;> [ exact hx₁; exact ⟨ Nat.one_le_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun p hp => Nat.Prime.ne_zero <| hprime E hE₁ p hp, hprod E hE₁ ⟩ ];
  · -- We need to show that the cardinality of the union of the retained primes and the triple products is equal to the sum of the cardinalities of the retained primes and the triple products.
    have h_card_union : (AH n H).card + (Vset H).card = ((Finset.Icc 1 n).filter (fun p => Nat.Prime p ∧ p ∉ Vset H)).card + (H.image (fun E => ∏ p ∈ E, p)).card + (Vset H).card := by
      rw [ AH, Finset.card_union_of_disjoint ];
      norm_num [ Finset.disjoint_right ];
      intro E hE h1 h2 h3; have := h3; simp_all +decide ;
      rcases Finset.card_eq_three.mp ( h3 E hE ) with ⟨ p, q, r, hp, hq, hr, h ⟩ ; simp_all +decide [ Nat.prime_mul_iff ];
      aesop;
    -- We need to show that the cardinality of the image of the triple products is equal to the cardinality of H.
    have h_card_image : (H.image (fun E => ∏ p ∈ E, p)).card = H.card := by
      apply Finset.card_image_of_injOn;
      intro E hE E' hE' h_eq; apply_fun fun x => x.primeFactors at h_eq; simp_all +decide ;
      rw [ Nat.primeFactors_prod, Nat.primeFactors_prod ] at h_eq <;> aesop;
    rw [ h_card_union, h_card_image, add_right_comm ];
    rw [ ← Finset.card_union_of_disjoint ];
    · congr 2 with p ; simp +contextual [ Vset ];
      exact ⟨ fun h => by rcases h with ( ⟨ ⟨ hp₁, hp₂ ⟩, hp₃, hp₄ ⟩ | ⟨ E, hE₁, hE₂ ⟩ ) <;> [ exact ⟨ ⟨ hp₁, hp₂ ⟩, hp₃ ⟩ ; exact ⟨ ⟨ Nat.Prime.pos ( hprime E hE₁ p hE₂ ), hprod E hE₁ |> le_trans ( Nat.le_of_dvd ( Finset.prod_pos fun q hq => Nat.Prime.pos ( hprime E hE₁ q hq ) ) ( Finset.dvd_prod_of_mem _ hE₂ ) ) ⟩, hprime E hE₁ p hE₂ ⟩ ], fun h => if h' : ∃ E ∈ H, p ∈ E then Or.inr h' else Or.inl ⟨ ⟨ h.1.1, h.1.2 ⟩, h.2, fun E hE₁ hE₂ => h' ⟨ E, hE₁, hE₂ ⟩ ⟩ ⟩;
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_filter.mp hx₁ |>.2.2 hx₂

/-! ## Prime bins and the hypergraph construction -/

/-- `M = n^{1/3} / log n`. -/
noncomputable def Mval (n : ℕ) : ℝ := (n : ℝ) ^ ((1:ℝ)/3) / Real.log n

/-
`M² = S`.
-/
lemma Mval_sq_eq_S (n : ℕ) : (Mval n) ^ 2 = S n := by
  unfold Mval S;
  rw [ div_pow, ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num

/-- The `r`-th prime bin `P_r = {p prime : y e^{rh} < p ≤ y e^{(r+1)h}}`. -/
noncomputable def Pbin (h : ℝ) (n : ℕ) (r : ℤ) : Finset ℕ :=
  (Finset.Ioc ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((r : ℝ) * h)⌋₊
             ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp (((r : ℝ) + 1) * h)⌋₊).filter Nat.Prime

/-- `m_r = |P_r|`. -/
noncomputable def mbin (h : ℝ) (n : ℕ) (r : ℤ) : ℕ := (Pbin h n r).card

/-- The set of indices appearing in a cell set `C`. -/
def Rset (C : Finset (ℤ × ℤ)) : Finset ℤ :=
  C.image Prod.fst ∪ C.image Prod.snd ∪ C.image thirdIndex

/-
For fixed `h > 0` and `r`, `m_r / M → 3 Δ_r`.
-/
lemma bin_sizes (hpnt : PNT) (h : ℝ) (hh : 0 < h) (r : ℤ) :
    Tendsto (fun n : ℕ => (mbin h n r : ℝ) / Mval n) atTop (𝓝 (3 * Delta h r)) := by
  convert Tendsto.sub ( pi_mul_ratio hpnt ( Real.exp ( ( r + 1 ) * h ) ) ( by positivity ) |> Filter.Tendsto.comp <| tendsto_y_atTop ) ( pi_mul_ratio hpnt ( Real.exp ( r * h ) ) ( by positivity ) |> Filter.Tendsto.comp <| tendsto_y_atTop ) |> ( ·.mul_const 3 ) using 2 ; norm_num [ mbin, Mval ] ; ring_nf;
  · by_cases hn : ‹_› = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
    rw [ Pbin ];
    rw [ card_primes_Ioc ];
    · rw [ Nat.cast_sub ] <;> norm_num ; ring_nf;
      · rw [ Real.log_rpow ( by positivity ) ] ; ring;
      · exact Nat.monotone_primeCounting <| Nat.floor_mono <| mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by linarith ) <| by positivity;
    · exact Nat.floor_mono <| mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by linarith ) <| by positivity;
  · unfold Delta; ring;

/-
For fixed `h > 0` and finite `C`, for all large `n` every cell `(i,j) ∈ C` with
third index `k` has `m_k ≥ max(m_i, m_j)`.
-/
lemma third_bin_large (hpnt : PNT) (h : ℝ) (hh : 0 < h) (C : Finset (ℤ × ℤ))
    (hC : ∀ c ∈ C, Admissible c) :
    ∀ᶠ n : ℕ in atTop, ∀ c ∈ C,
      max (mbin h n c.1) (mbin h n c.2) ≤ mbin h n (thirdIndex c) := by
  -- By definition of `mbin`, we know that `mbin h n r` is the number of primes in the interval `(⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((r : ℝ) * h)⌋₊, ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp (((r : ℝ) + 1) * h)⌋₊]`.
  have h_mbin : ∀ c ∈ C, ∀ᶠ n in atTop, mbin h n c.2 < mbin h n (thirdIndex c) ∧ mbin h n c.1 < mbin h n (thirdIndex c) := by
    intro c hc
    have h_mbin_lt : Filter.Tendsto (fun n => (mbin h n c.2 : ℝ) / Mval n) Filter.atTop (nhds (3 * Delta h c.2)) ∧ Filter.Tendsto (fun n => (mbin h n (thirdIndex c) : ℝ) / Mval n) Filter.atTop (nhds (3 * Delta h (thirdIndex c))) ∧ Filter.Tendsto (fun n => (mbin h n c.1 : ℝ) / Mval n) Filter.atTop (nhds (3 * Delta h c.1)) := by
      exact ⟨ bin_sizes hpnt h hh c.2, bin_sizes hpnt h hh ( thirdIndex c ), bin_sizes hpnt h hh c.1 ⟩;
    have h_mbin_lt : 3 * Delta h c.2 < 3 * Delta h (thirdIndex c) ∧ 3 * Delta h c.1 < 3 * Delta h (thirdIndex c) := by
      constructor <;> norm_num [ Delta ];
      · norm_num [ thirdIndex ];
        rw [ show ( -c.1 - c.2 - 3 + 1 : ℝ ) * h = ( -c.1 - c.2 - 3 ) * h + h by ring, show ( c.2 + 1 : ℝ ) * h = c.2 * h + h by ring, Real.exp_add, Real.exp_add ];
        nlinarith [ Real.add_one_le_exp h, Real.exp_pos ( c.2 * h ), Real.exp_lt_exp.mpr ( show ( -c.1 - c.2 - 3 : ℝ ) * h > c.2 * h by nlinarith [ show ( c.1 : ℝ ) ≤ c.2 by exact_mod_cast hC c hc |>.1, show ( c.1 : ℝ ) + 2 * c.2 ≤ -4 by exact_mod_cast hC c hc |>.2 ] ) ];
      · have := cell_order c ( hC c hc );
        rw [ show ( c.1 + 1 : ℝ ) * h = c.1 * h + h by ring, show ( thirdIndex c + 1 : ℝ ) * h = thirdIndex c * h + h by ring, Real.exp_add, Real.exp_add ];
        nlinarith [ Real.add_one_le_exp h, Real.exp_pos ( c.1 * h ), Real.exp_lt_exp.mpr ( show ( c.1 : ℝ ) * h < thirdIndex c * h by exact mul_lt_mul_of_pos_right ( mod_cast by linarith ) hh ) ];
    have h_mbin_lt : ∀ᶠ n in atTop, (mbin h n c.2 : ℝ) / Mval n < (mbin h n (thirdIndex c) : ℝ) / Mval n ∧ (mbin h n c.1 : ℝ) / Mval n < (mbin h n (thirdIndex c) : ℝ) / Mval n := by
      rename_i h;
      exact Filter.eventually_and.mpr ⟨ h.1.eventually_lt h.2.1 h_mbin_lt.1, h.2.2.eventually_lt h.2.1 h_mbin_lt.2 ⟩;
    filter_upwards [ h_mbin_lt, tendsto_M_atTop.eventually_gt_atTop 0 ] with n hn hn';
    rw [ div_lt_div_iff_of_pos_right, div_lt_div_iff_of_pos_right ] at hn <;> norm_cast at *;
  simp +zetaDelta at *;
  choose! N hN using h_mbin;
  exact ⟨ Finset.sup C ( fun x => N x.1 x.2 ), fun n hn a b hab => ⟨ by linarith [ hN a b hab n ( le_trans ( Finset.le_sup ( f := fun x => N x.1 x.2 ) hab ) hn ) ], by linarith [ hN a b hab n ( le_trans ( Finset.le_sup ( f := fun x => N x.1 x.2 ) hab ) hn ) ] ⟩ ⟩

/-- Every element of a prime bin is prime. -/
lemma Pbin_prime (h : ℝ) (n : ℕ) (r : ℤ) {p : ℕ} (hp : p ∈ Pbin h n r) : Nat.Prime p := by
  exact (Finset.mem_filter.mp hp).2

/-- Membership bounds for a prime bin. -/
lemma Pbin_mem_iff (h : ℝ) (n : ℕ) (r : ℤ) (p : ℕ) :
    p ∈ Pbin h n r ↔
      (⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((r : ℝ) * h)⌋₊ < p ∧
        p ≤ ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp (((r : ℝ) + 1) * h)⌋₊) ∧ Nat.Prime p := by
  simp [Pbin, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

/-- Prime bins with distinct indices are disjoint. -/
lemma Pbin_disjoint (h : ℝ) (hh : 0 < h) (n : ℕ) {i j : ℤ} (hij : i < j) :
    Disjoint (Pbin h n i) (Pbin h n j) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [Pbin_mem_iff] at hp hp'
  refine hp'.1.1.not_ge (hp.1.2.trans ?_)
  exact Nat.floor_mono <| mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr <| by nlinarith [show (i : ℝ) + 1 ≤ j by exact_mod_cast hij]) (by positivity)

/-
Eventually, every generated triple product is `≤ n`.
-/
lemma triple_prod_le_n_eventually (h : ℝ) (C : Finset (ℤ × ℤ)) :
    ∀ᶠ n : ℕ in atTop, ∀ c ∈ C,
      ∀ p ∈ Pbin h n c.1, ∀ q ∈ Pbin h n c.2, ∀ r ∈ Pbin h n (thirdIndex c), p * q * r ≤ n := by
  refine' Filter.eventually_atTop.mpr ⟨ 8, fun n hn c hc p hp q hq r hr => _ ⟩;
  -- From the definition of `Pbin`, we have `p ≤ ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((i+1)*h)⌋₊`, `q ≤ ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((j+1)*h)⌋₊`, and `r ≤ ⌊(n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((k+1)*h)⌋₊`.
  have hp_le : (p : ℝ) ≤ (n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((c.1 + 1) * h) := by
    exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Ioc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity;
  have hq_le : (q : ℝ) ≤ (n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((c.2 + 1) * h) := by
    exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Ioc.mp ( Finset.mem_filter.mp hq |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity;
  have hr_le : (r : ℝ) ≤ (n : ℝ) ^ ((1:ℝ)/3) * Real.exp ((thirdIndex c + 1) * h) := by
    exact le_trans ( Nat.cast_le.mpr <| Finset.mem_Ioc.mp ( Finset.mem_filter.mp hr |>.1 ) |>.2 ) <| Nat.floor_le <| by positivity;
  -- Multiplying the three inequalities gives $p * q * r ≤ n * \exp((i + j + thirdIndex c + 3) * h)$.
  have h_mul : (p * q * r : ℝ) ≤ n * Real.exp ((c.1 + c.2 + thirdIndex c + 3) * h) := by
    convert mul_le_mul ( mul_le_mul hp_le hq_le ( by positivity ) ( by positivity ) ) hr_le ( by positivity ) ( by positivity ) using 1 ; ring_nf;
    rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ; rw [ mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add ] ; ring_nf;
  norm_num [ thirdIndex ] at *;
  ring_nf at h_mul; norm_num at h_mul; exact_mod_cast h_mul;

/-- The explicit hypergraph family built from off-diagonal colourings `χ` and
diagonal colourings `χ'`. -/
noncomputable def hyperFamily (C : Finset (ℤ × ℤ)) (P : ℤ → Finset ℕ)
    (χ χ' : ℤ × ℤ → ℕ → ℕ → ℕ) : Finset (Finset ℕ) :=
  (C.filter (fun c => c.1 < c.2)).biUnion
      (fun c => (P c.1 ×ˢ P c.2).image (fun pq => ({pq.1, pq.2, χ c pq.1 pq.2} : Finset ℕ)))
    ∪ (C.filter (fun c => c.1 = c.2)).biUnion
      (fun c => ((P c.1 ×ˢ P c.1).filter (fun pq => pq.1 < pq.2)).image
        (fun pq => ({pq.1, pq.2, χ' c pq.1 pq.2} : Finset ℕ)))

/-
Membership characterization of `hyperFamily`.
-/
lemma mem_hyperFamily (C : Finset (ℤ × ℤ)) (P : ℤ → Finset ℕ)
    (χ χ' : ℤ × ℤ → ℕ → ℕ → ℕ) (E : Finset ℕ) :
    E ∈ hyperFamily C P χ χ' ↔
      (∃ c ∈ C, c.1 < c.2 ∧ ∃ p ∈ P c.1, ∃ q ∈ P c.2, E = {p, q, χ c p q}) ∨
      (∃ c ∈ C, c.1 = c.2 ∧ ∃ p ∈ P c.1, ∃ q ∈ P c.1, p < q ∧ E = {p, q, χ' c p q}) := by
  simp_all +decide [ Finset.ext_iff, hyperFamily ];
  grind +qlia

/-- Bundled properness data for the colourings used in `hyperFamily`. -/
structure ColData (C : Finset (ℤ × ℤ)) (P : ℤ → Finset ℕ) (χ χ' : ℤ × ℤ → ℕ → ℕ → ℕ) : Prop where
  χmem : ∀ c ∈ C, c.1 < c.2 → ∀ p ∈ P c.1, ∀ q ∈ P c.2, χ c p q ∈ P (thirdIndex c)
  χ2 : ∀ c ∈ C, c.1 < c.2 → ∀ p ∈ P c.1, ∀ q ∈ P c.2, ∀ q' ∈ P c.2, q ≠ q' → χ c p q ≠ χ c p q'
  χ1 : ∀ c ∈ C, c.1 < c.2 → ∀ p ∈ P c.1, ∀ p' ∈ P c.1, ∀ q ∈ P c.2, p ≠ p' → χ c p q ≠ χ c p' q
  χ'mem : ∀ c ∈ C, c.1 = c.2 → ∀ p ∈ P c.1, ∀ q ∈ P c.1, p ≠ q → χ' c p q ∈ P (thirdIndex c)
  χ'sym : ∀ c ∈ C, c.1 = c.2 → ∀ p ∈ P c.1, ∀ q ∈ P c.1, χ' c p q = χ' c q p
  χ'proper : ∀ c ∈ C, c.1 = c.2 → ∀ p ∈ P c.1, ∀ q ∈ P c.1, ∀ r ∈ P c.1,
      p ≠ q → p ≠ r → q ≠ r → χ' c p q ≠ χ' c p r

variable {C : Finset (ℤ × ℤ)} {P : ℤ → Finset ℕ} {χ χ' : ℤ × ℤ → ℕ → ℕ → ℕ}

/-- A prime lies in at most one bin. -/
lemma bin_unique (hdisj : ∀ i j : ℤ, i < j → Disjoint (P i) (P j)) {x : ℕ} {a b : ℤ}
    (ha : x ∈ P a) (hb : x ∈ P b) : a = b := by
  by_contra hab
  rcases lt_or_gt_of_ne hab with h | h
  · exact Finset.disjoint_left.mp (hdisj a b h) ha hb
  · exact Finset.disjoint_left.mp (hdisj b a h) hb ha

/-
Each member of `hyperFamily` has exactly three elements.
-/
lemma hyperFamily_card3 (hadm : ∀ c ∈ C, Admissible c) (hdisj : ∀ i j : ℤ, i < j → Disjoint (P i) (P j))
    (hcol : ColData C P χ χ') :
    ∀ E ∈ hyperFamily C P χ χ', E.card = 3 := by
  intro E hE
  rw [mem_hyperFamily] at hE
  cases' hE with hcase1 hcase2;
  · obtain ⟨ c, hc, hc', p, hp, q, hq, rfl ⟩ := hcase1;
    have h_distinct : p ≠ q ∧ p ≠ χ c p q ∧ q ≠ χ c p q := by
      have := hcol.χmem c hc hc' p hp q hq; simp_all +decide [ Finset.disjoint_left ] ;
      exact ⟨ fun h => hdisj _ _ hc' hp ( h.symm ▸ hq ), fun h => hdisj _ _ ( by linarith [ cell_order c ( hadm _ _ hc ) ] ) hp ( h.symm ▸ this ), fun h => hdisj _ _ ( by linarith [ cell_order c ( hadm _ _ hc ) ] ) hq ( h.symm ▸ this ) ⟩;
    grind;
  · rcases hcase2 with ⟨ c, hc, hc', p, hp, q, hq, hpq, rfl ⟩;
    have h_card : p ≠ q ∧ p ≠ χ' c p q ∧ q ≠ χ' c p q := by
      have := hcol.χ'mem c hc hc' p hp q hq ( by linarith ) ; simp_all +decide [ Finset.disjoint_left ] ;
      exact ⟨ ne_of_lt hpq, fun h => hdisj _ _ ( by linarith [ cell_order c ( hadm _ _ hc ) ] ) hp ( h.symm ▸ this ), fun h => hdisj _ _ ( by linarith [ cell_order c ( hadm _ _ hc ) ] ) hq ( h.symm ▸ this ) ⟩;
    rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop

/-
Each member of `hyperFamily` consists of primes.
-/
lemma hyperFamily_prime (hprime : ∀ r : ℤ, ∀ p ∈ P r, Nat.Prime p) (hcol : ColData C P χ χ') :
    ∀ E ∈ hyperFamily C P χ χ', ∀ p ∈ E, Nat.Prime p := by
  intros E hE p hp
  rw [mem_hyperFamily] at hE
  cases' hE with hE hE';
  · rcases hE with ⟨ c, hc₁, hc₂, p, hp₁, q, hq₁, rfl ⟩ ; simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ] ;
    rcases hp with ( rfl | rfl | rfl ) <;> [ exact hprime _ _ hp₁; exact hprime _ _ hq₁; exact hprime _ _ ( hcol.χmem _ hc₁ hc₂ _ hp₁ _ hq₁ ) ];
  · grind +splitIndPred

/-- Each member of `hyperFamily` has product at most `V`. -/
lemma hyperFamily_prod (V : ℕ) (hadm : ∀ c ∈ C, Admissible c)
    (hdisj : ∀ i j : ℤ, i < j → Disjoint (P i) (P j))
    (hprod : ∀ c ∈ C, ∀ p ∈ P c.1, ∀ q ∈ P c.2, ∀ r ∈ P (thirdIndex c), p * q * r ≤ V)
    (hcol : ColData C P χ χ') :
    ∀ E ∈ hyperFamily C P χ χ', (∏ p ∈ E, p) ≤ V := by
  intro E hE
  rw [mem_hyperFamily] at hE
  cases hE with
  | inl hcase =>
    obtain ⟨c, hc, hc', p, hp, q, hq, rfl⟩ := hcase
    have hord := cell_order c (hadm c hc)
    have hx : χ c p q ∈ P (thirdIndex c) := hcol.χmem c hc hc' p hp q hq
    have hpq : p ≠ q := fun h => Finset.disjoint_left.mp (hdisj c.1 c.2 hc') hp (h.symm ▸ hq)
    have hpx : p ≠ χ c p q := fun h =>
      Finset.disjoint_left.mp (hdisj c.1 (thirdIndex c) (by omega)) hp (h.symm ▸ hx)
    have hqx : q ≠ χ c p q := fun h =>
      Finset.disjoint_left.mp (hdisj c.2 (thirdIndex c) (by omega)) hq (h.symm ▸ hx)
    rw [Finset.prod_insert (by simp [Finset.mem_insert, hpq, hpx]),
      Finset.prod_insert (by simp [hqx]), Finset.prod_singleton]
    calc p * (q * χ c p q) = p * q * χ c p q := by ring
      _ ≤ V := hprod c hc p hp q hq _ hx
  | inr hcase =>
    obtain ⟨c, hc, hc', p, hp, q, hq, hpq, rfl⟩ := hcase
    have hord := cell_order c (hadm c hc)
    have hx : χ' c p q ∈ P (thirdIndex c) := hcol.χ'mem c hc hc' p hp q hq (ne_of_lt hpq)
    have hpx : p ≠ χ' c p q := fun h =>
      Finset.disjoint_left.mp (hdisj c.1 (thirdIndex c) (by omega)) hp (h.symm ▸ hx)
    have hqx : q ≠ χ' c p q := fun h =>
      Finset.disjoint_left.mp (hdisj c.1 (thirdIndex c) (by omega)) hq (h.symm ▸ hx)
    have hq2 : q ∈ P c.2 := hc' ▸ hq
    rw [Finset.prod_insert (by simp [Finset.mem_insert, ne_of_lt hpq, hpx]),
      Finset.prod_insert (by simp [hqx]), Finset.prod_singleton]
    calc p * (q * χ' c p q) = p * q * χ' c p q := by ring
      _ ≤ V := hprod c hc p hp q hq2 _ hx

/-- The family `hyperFamily` is linear: two distinct members meet in ≤ 1 element. -/
lemma hyperFamily_linear (hadm : ∀ c ∈ C, Admissible c)
    (hdisj : ∀ i j : ℤ, i < j → Disjoint (P i) (P j)) (hcol : ColData C P χ χ') :
    ∀ E ∈ hyperFamily C P χ χ', ∀ E' ∈ hyperFamily C P χ χ', E ≠ E' → (E ∩ E').card ≤ 1 := by
  have huniq : ∀ (x : ℕ) (a b : ℤ), x ∈ P a → x ∈ P b → a = b :=
    fun x a b ha hb => bin_unique hdisj ha hb
  intro E hE E' hE' hne
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_inter] at ha hb
  by_contra hab
  apply hne
  rw [mem_hyperFamily] at hE hE'
  obtain ⟨haE, haE'⟩ := ha
  obtain ⟨hbE, hbE'⟩ := hb
  rcases hE with ⟨c, hc, hlt, p, hp, q, hq, rfl⟩ | ⟨c, hc, he, p, hp, q, hq, hpq, rfl⟩ <;>
    rcases hE' with ⟨d, hd, hltd, r, hr, s, hs, rfl⟩ | ⟨d, hd, hed, r, hr, s, hs, hrs, rfl⟩
  · -- off / off
    have hoc := cell_order c (hadm c hc)
    have hod := cell_order d (hadm d hd)
    have hwc : χ c p q ∈ P (thirdIndex c) := hcol.χmem c hc hlt p hp q hq
    have hwd : χ d r s ∈ P (thirdIndex d) := hcol.χmem d hd hltd r hr s hs
    have h2c := hcol.χ2 c hc hlt
    have h1c := hcol.χ1 c hc hlt
    simp only [Finset.mem_insert, Finset.mem_singleton] at haE haE' hbE hbE'
    grind
  · -- off / diag
    have hoc := cell_order c (hadm c hc)
    have hod := cell_order d (hadm d hd)
    have hwc : χ c p q ∈ P (thirdIndex c) := hcol.χmem c hc hlt p hp q hq
    have hwd : χ' d r s ∈ P (thirdIndex d) := hcol.χ'mem d hd hed r hr s hs (ne_of_lt hrs)
    simp only [Finset.mem_insert, Finset.mem_singleton] at haE haE' hbE hbE'
    grind
  · -- diag / off
    have hoc := cell_order c (hadm c hc)
    have hod := cell_order d (hadm d hd)
    have hwc : χ' c p q ∈ P (thirdIndex c) := hcol.χ'mem c hc he p hp q hq (ne_of_lt hpq)
    have hwd : χ d r s ∈ P (thirdIndex d) := hcol.χmem d hd hltd r hr s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at haE haE' hbE hbE'
    grind
  · -- diag / diag
    have hoc := cell_order c (hadm c hc)
    have hod := cell_order d (hadm d hd)
    have hwc : χ' c p q ∈ P (thirdIndex c) := hcol.χ'mem c hc he p hp q hq (ne_of_lt hpq)
    have hwd : χ' d r s ∈ P (thirdIndex d) := hcol.χ'mem d hd hed r hr s hs (ne_of_lt hrs)
    have hprc := hcol.χ'proper c hc he
    have hprd := hcol.χ'proper d hd hed
    have hsymc := hcol.χ'sym c hc he
    have hsymd := hcol.χ'sym d hd hed
    simp only [Finset.mem_insert, Finset.mem_singleton] at haE haE' hbE hbE'
    grind

/-- The vertex set of `hyperFamily` is small. -/
lemma hyperFamily_vset (hcol : ColData C P χ χ') :
    (Vset (hyperFamily C P χ χ')).card ≤ ∑ r ∈ Rset C, (P r).card := by
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro v hv
  rw [Vset, Finset.mem_biUnion] at hv
  obtain ⟨E, hE, hvE⟩ := hv
  simp only [id] at hvE
  rw [mem_hyperFamily] at hE
  rw [Finset.mem_biUnion]
  rcases hE with ⟨c, hc, hc', p, hp, q, hq, rfl⟩ | ⟨c, hc, hc', p, hp, q, hq, hpq, rfl⟩
  · have h1 : c.1 ∈ Rset C := by
      simp only [Rset, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
    have h2 : c.2 ∈ Rset C := by
      simp only [Rset, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨c, hc, rfl⟩)
    have h3 : thirdIndex c ∈ Rset C := by
      simp only [Rset, Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨c, hc, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvE
    rcases hvE with rfl | rfl | rfl
    · exact ⟨c.1, h1, hp⟩
    · exact ⟨c.2, h2, hq⟩
    · exact ⟨thirdIndex c, h3, hcol.χmem c hc hc' p hp q hq⟩
  · have h1 : c.1 ∈ Rset C := by
      simp only [Rset, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨c, hc, rfl⟩)
    have h3 : thirdIndex c ∈ Rset C := by
      simp only [Rset, Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨c, hc, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvE
    rcases hvE with rfl | rfl | rfl
    · exact ⟨c.1, h1, hp⟩
    · exact ⟨c.1, h1, hq⟩
    · exact ⟨thirdIndex c, h3, hcol.χ'mem c hc hc' p hp q hq (ne_of_lt hpq)⟩

/-- The number of strictly-increasing pairs from `s × s` is `s.card.choose 2`. -/
lemma card_filter_lt_product (s : Finset ℕ) :
    ((s ×ˢ s).filter (fun pq => pq.1 < pq.2)).card = s.card.choose 2 := by
  rw [← Finset.card_powersetCard]
  apply Finset.card_bij (fun pq _ => ({pq.1, pq.2} : Finset ℕ))
  · rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_product] at hpq
    simp only [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hpq.1.1
      · exact hpq.1.2
    · rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; omega), Finset.card_singleton]
  · rintro ⟨p, q⟩ hpq ⟨p', q'⟩ hpq' h
    simp only [Finset.mem_filter, Finset.mem_product] at hpq hpq'
    simp only [Finset.ext_iff, Finset.mem_insert, Finset.mem_singleton] at h
    have := h p; have := h q; have := h p'; have := h q'
    have h1 := hpq.2; have h2 := hpq'.2
    ext <;> simp <;> omega
  · rintro t ht
    simp only [Finset.mem_powersetCard] at ht
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp ht.2
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨(x, y), by simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨ht.1 (by simp), ht.1 (by simp)⟩, h⟩, by simp⟩
    · exact ⟨(y, x), by simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨ht.1 (by simp), ht.1 (by simp)⟩, h⟩, by rw [Finset.pair_comm]⟩

/-- Exact edge count of `hyperFamily`. -/
lemma hyperFamily_card (hadm : ∀ c ∈ C, Admissible c)
    (hdisj : ∀ i j : ℤ, i < j → Disjoint (P i) (P j)) (hcol : ColData C P χ χ') :
    (hyperFamily C P χ χ').card =
      (∑ c ∈ C.filter (fun c => c.1 < c.2), (P c.1).card * (P c.2).card)
        + ∑ c ∈ C.filter (fun c => c.1 = c.2), ((P c.1).card).choose 2 := by
  classical
  have huniq : ∀ (x : ℕ) (a b : ℤ), x ∈ P a → x ∈ P b → a = b :=
    fun x a b ha hb => bin_unique hdisj ha hb
  -- injectivity on off-diagonal cells
  have hinjoff : ∀ c ∈ C.filter (fun c => c.1 < c.2),
      Set.InjOn (fun pq : ℕ × ℕ => ({pq.1, pq.2, χ c pq.1 pq.2} : Finset ℕ)) ↑(P c.1 ×ˢ P c.2) := by
    intro c hcf pq hpq pq' hpq' heq
    rw [Finset.mem_filter] at hcf
    obtain ⟨hc, hlt⟩ := hcf
    have hoc := cell_order c (hadm c hc)
    rw [Finset.mem_coe, Finset.mem_product] at hpq hpq'
    have hw := hcol.χmem c hc hlt pq.1 hpq.1 pq.2 hpq.2
    have hw' := hcol.χmem c hc hlt pq'.1 hpq'.1 pq'.2 hpq'.2
    have hp := hpq.1; have hq := hpq.2; have hp' := hpq'.1; have hq' := hpq'.2
    simp only [] at heq
    have m1 : pq.1 ∈ ({pq'.1, pq'.2, χ c pq'.1 pq'.2} : Finset ℕ) := by rw [← heq]; simp
    have m2 : pq.2 ∈ ({pq'.1, pq'.2, χ c pq'.1 pq'.2} : Finset ℕ) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
    have key1 : pq.1 = pq'.1 := by
      rcases m1 with h | h | h
      · exact h
      · exact absurd (huniq pq.1 c.1 c.2 hp (by rw [h]; exact hq')) (by omega)
      · exact absurd (huniq pq.1 c.1 (thirdIndex c) hp (by rw [h]; exact hw')) (by omega)
    have key2 : pq.2 = pq'.2 := by
      rcases m2 with h | h | h
      · exact absurd (huniq pq.2 c.2 c.1 hq (by rw [h]; exact hp')) (by omega)
      · exact h
      · exact absurd (huniq pq.2 c.2 (thirdIndex c) hq (by rw [h]; exact hw')) (by omega)
    exact Prod.ext key1 key2
  -- injectivity on diagonal cells
  have hinjdiag : ∀ c ∈ C.filter (fun c => c.1 = c.2),
      Set.InjOn (fun pq : ℕ × ℕ => ({pq.1, pq.2, χ' c pq.1 pq.2} : Finset ℕ))
        ↑((P c.1 ×ˢ P c.1).filter (fun pq => pq.1 < pq.2)) := by
    intro c hcf pq hpq pq' hpq' heq
    rw [Finset.mem_filter] at hcf
    obtain ⟨hc, he⟩ := hcf
    have hoc := cell_order c (hadm c hc)
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hpq hpq'
    have hw := hcol.χ'mem c hc he pq.1 hpq.1.1 pq.2 hpq.1.2 (ne_of_lt hpq.2)
    have hw' := hcol.χ'mem c hc he pq'.1 hpq'.1.1 pq'.2 hpq'.1.2 (ne_of_lt hpq'.2)
    have hp := hpq.1.1; have hq := hpq.1.2; have hp' := hpq'.1.1; have hq' := hpq'.1.2
    have hlt1 := hpq.2; have hlt2 := hpq'.2
    simp only [] at heq
    have m1 : pq.1 ∈ ({pq'.1, pq'.2, χ' c pq'.1 pq'.2} : Finset ℕ) := by rw [← heq]; simp
    have m2 : pq.2 ∈ ({pq'.1, pq'.2, χ' c pq'.1 pq'.2} : Finset ℕ) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
    have hne1 : ¬ pq.1 = χ' c pq'.1 pq'.2 := fun h =>
      absurd (huniq pq.1 c.1 (thirdIndex c) hp (by rw [h]; exact hw')) (by omega)
    have hne2 : ¬ pq.2 = χ' c pq'.1 pq'.2 := fun h =>
      absurd (huniq pq.2 c.1 (thirdIndex c) hq (by rw [h]; exact hw')) (by omega)
    have hd1 : pq.1 = pq'.1 ∨ pq.1 = pq'.2 := by tauto
    have hd2 : pq.2 = pq'.1 ∨ pq.2 = pq'.2 := by tauto
    rcases hd1 with h1 | h1 <;> rcases hd2 with h2 | h2 <;> refine Prod.ext ?_ ?_ <;> omega
  -- distinct off-diagonal cells give disjoint triple sets
  have hpdoff : ∀ c ∈ C.filter (fun c => c.1 < c.2), ∀ d ∈ C.filter (fun c => c.1 < c.2), c ≠ d →
      Disjoint ((P c.1 ×ˢ P c.2).image (fun pq => ({pq.1, pq.2, χ c pq.1 pq.2} : Finset ℕ)))
               ((P d.1 ×ˢ P d.2).image (fun pq => ({pq.1, pq.2, χ d pq.1 pq.2} : Finset ℕ))) := by
    intro c hcf d hdf hcd
    rw [Finset.mem_filter] at hcf hdf
    obtain ⟨hc, hlt⟩ := hcf; obtain ⟨hd, hltd⟩ := hdf
    have hoc := cell_order c (hadm c hc); have hod := cell_order d (hadm d hd)
    rw [Finset.disjoint_left]
    intro E hE hE'
    rw [Finset.mem_image] at hE hE'
    obtain ⟨pq, hpq, rfl⟩ := hE
    obtain ⟨pq', hpq', heq⟩ := hE'
    rw [Finset.mem_product] at hpq hpq'
    have hw := hcol.χmem c hc hlt pq.1 hpq.1 pq.2 hpq.2
    have hw' := hcol.χmem d hd hltd pq'.1 hpq'.1 pq'.2 hpq'.2
    have hp := hpq.1; have hq := hpq.2; have hp' := hpq'.1; have hq' := hpq'.2
    have m1 : pq.1 ∈ ({pq'.1, pq'.2, χ d pq'.1 pq'.2} : Finset ℕ) := by rw [heq]; simp
    have m2 : pq.2 ∈ ({pq'.1, pq'.2, χ d pq'.1 pq'.2} : Finset ℕ) := by rw [heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
    apply hcd
    have e1 : c.1 = d.1 ∨ c.1 = d.2 ∨ c.1 = thirdIndex d := by
      rcases m1 with h | h | h
      · exact Or.inl (huniq pq.1 c.1 d.1 hp (by rw [h]; exact hp'))
      · exact Or.inr (Or.inl (huniq pq.1 c.1 d.2 hp (by rw [h]; exact hq')))
      · exact Or.inr (Or.inr (huniq pq.1 c.1 (thirdIndex d) hp (by rw [h]; exact hw')))
    have e2 : c.2 = d.1 ∨ c.2 = d.2 ∨ c.2 = thirdIndex d := by
      rcases m2 with h | h | h
      · exact Or.inl (huniq pq.2 c.2 d.1 hq (by rw [h]; exact hp'))
      · exact Or.inr (Or.inl (huniq pq.2 c.2 d.2 hq (by rw [h]; exact hq')))
      · exact Or.inr (Or.inr (huniq pq.2 c.2 (thirdIndex d) hq (by rw [h]; exact hw')))
    refine Prod.ext ?_ ?_ <;> rcases e1 with h1 | h1 | h1 <;> rcases e2 with h2 | h2 | h2 <;> omega
  -- distinct diagonal cells give disjoint triple sets
  have hpddiag : ∀ c ∈ C.filter (fun c => c.1 = c.2), ∀ d ∈ C.filter (fun c => c.1 = c.2), c ≠ d →
      Disjoint (((P c.1 ×ˢ P c.1).filter (fun pq => pq.1 < pq.2)).image
                  (fun pq => ({pq.1, pq.2, χ' c pq.1 pq.2} : Finset ℕ)))
               (((P d.1 ×ˢ P d.1).filter (fun pq => pq.1 < pq.2)).image
                  (fun pq => ({pq.1, pq.2, χ' d pq.1 pq.2} : Finset ℕ))) := by
    intro c hcf d hdf hcd
    rw [Finset.mem_filter] at hcf hdf
    obtain ⟨hc, he⟩ := hcf; obtain ⟨hd, hed⟩ := hdf
    have hoc := cell_order c (hadm c hc); have hod := cell_order d (hadm d hd)
    rw [Finset.disjoint_left]
    intro E hE hE'
    rw [Finset.mem_image] at hE hE'
    obtain ⟨pq, hpq, rfl⟩ := hE
    obtain ⟨pq', hpq', heq⟩ := hE'
    rw [Finset.mem_filter, Finset.mem_product] at hpq hpq'
    have hw := hcol.χ'mem c hc he pq.1 hpq.1.1 pq.2 hpq.1.2 (ne_of_lt hpq.2)
    have hw' := hcol.χ'mem d hd hed pq'.1 hpq'.1.1 pq'.2 hpq'.1.2 (ne_of_lt hpq'.2)
    have hp := hpq.1.1; have hq := hpq.1.2; have hp' := hpq'.1.1; have hq' := hpq'.1.2
    have hlt1 := hpq.2
    have m1 : pq.1 ∈ ({pq'.1, pq'.2, χ' d pq'.1 pq'.2} : Finset ℕ) := by rw [heq]; simp
    have m2 : pq.2 ∈ ({pq'.1, pq'.2, χ' d pq'.1 pq'.2} : Finset ℕ) := by rw [heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
    apply hcd
    have hkey : c.1 = d.1 := by
      rcases m1 with h | h | h <;> rcases m2 with h' | h' | h' <;>
        first
          | exact huniq pq.1 c.1 d.1 hp (by rw [h]; exact hp')
          | exact huniq pq.1 c.1 d.1 hp (by rw [h]; exact hq')
          | exact huniq pq.2 c.1 d.1 hq (by rw [h']; exact hp')
          | exact huniq pq.2 c.1 d.1 hq (by rw [h']; exact hq')
          | exact absurd (h.trans h'.symm) (Nat.ne_of_lt hlt1)
    exact Prod.ext hkey (by omega)
  -- the off-diagonal and diagonal parts are disjoint
  have hAB : Disjoint
      ((C.filter (fun c => c.1 < c.2)).biUnion
        (fun c => (P c.1 ×ˢ P c.2).image (fun pq => ({pq.1, pq.2, χ c pq.1 pq.2} : Finset ℕ))))
      ((C.filter (fun c => c.1 = c.2)).biUnion
        (fun c => ((P c.1 ×ˢ P c.1).filter (fun pq => pq.1 < pq.2)).image
          (fun pq => ({pq.1, pq.2, χ' c pq.1 pq.2} : Finset ℕ)))) := by
    rw [Finset.disjoint_left]
    intro E hE hE'
    rw [Finset.mem_biUnion] at hE hE'
    obtain ⟨c, hcf, hEc⟩ := hE
    obtain ⟨d, hdf, hEd⟩ := hE'
    rw [Finset.mem_filter] at hcf hdf
    obtain ⟨hc, hlt⟩ := hcf; obtain ⟨hd, hed⟩ := hdf
    have hoc := cell_order c (hadm c hc); have hod := cell_order d (hadm d hd)
    rw [Finset.mem_image] at hEc hEd
    obtain ⟨pq, hpq, rfl⟩ := hEc
    obtain ⟨pq', hpq', heq⟩ := hEd
    rw [Finset.mem_product] at hpq
    rw [Finset.mem_filter, Finset.mem_product] at hpq'
    have hw := hcol.χmem c hc hlt pq.1 hpq.1 pq.2 hpq.2
    have hp := hpq.1; have hq := hpq.2; have hp' := hpq'.1.1; have hq' := hpq'.1.2
    have hlt' := hpq'.2
    have n1 : pq'.1 ∈ ({pq.1, pq.2, χ c pq.1 pq.2} : Finset ℕ) := by rw [← heq]; simp
    have n2 : pq'.2 ∈ ({pq.1, pq.2, χ c pq.1 pq.2} : Finset ℕ) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at n1 n2
    exfalso
    rcases n1 with h1 | h1 | h1 <;> rcases n2 with h2 | h2 | h2
    · exact absurd (h1.trans h2.symm) (Nat.ne_of_lt hlt')
    · have := huniq pq'.1 d.1 c.1 hp' (by rw [h1]; exact hp)
      have := huniq pq'.2 d.1 c.2 hq' (by rw [h2]; exact hq); omega
    · have := huniq pq'.1 d.1 c.1 hp' (by rw [h1]; exact hp)
      have := huniq pq'.2 d.1 (thirdIndex c) hq' (by rw [h2]; exact hw); omega
    · have := huniq pq'.1 d.1 c.2 hp' (by rw [h1]; exact hq)
      have := huniq pq'.2 d.1 c.1 hq' (by rw [h2]; exact hp); omega
    · exact absurd (h1.trans h2.symm) (Nat.ne_of_lt hlt')
    · have := huniq pq'.1 d.1 c.2 hp' (by rw [h1]; exact hq)
      have := huniq pq'.2 d.1 (thirdIndex c) hq' (by rw [h2]; exact hw); omega
    · have := huniq pq'.1 d.1 (thirdIndex c) hp' (by rw [h1]; exact hw)
      have := huniq pq'.2 d.1 c.1 hq' (by rw [h2]; exact hp); omega
    · have := huniq pq'.1 d.1 (thirdIndex c) hp' (by rw [h1]; exact hw)
      have := huniq pq'.2 d.1 c.2 hq' (by rw [h2]; exact hq); omega
    · exact absurd (h1.trans h2.symm) (Nat.ne_of_lt hlt')
  rw [hyperFamily, Finset.card_union_of_disjoint hAB,
      Finset.card_biUnion hpdoff, Finset.card_biUnion hpddiag]
  congr 1
  · apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.card_image_of_injOn (hinjoff c hc), Finset.card_product]
  · apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.card_image_of_injOn (hinjdiag c hc), card_filter_lt_product]

/-
Given admissible cells `C`, pairwise-disjoint all-prime bins `P`, a third-bin
size condition, and product/vertex bounds by `V`, there is a linear family of
prime triples with the exact edge count and vertex bound. This is the purely
combinatorial core of `exists_hypergraph`.
-/
lemma abstract_hypergraph (C : Finset (ℤ × ℤ)) (P : ℤ → Finset ℕ) (V : ℕ)
    (hadm : ∀ c ∈ C, Admissible c)
    (hdisj : ∀ i j : ℤ, i < j → Disjoint (P i) (P j))
    (hprime : ∀ r : ℤ, ∀ p ∈ P r, Nat.Prime p)
    (hbig : ∀ c ∈ C, max (P c.1).card (P c.2).card ≤ (P (thirdIndex c)).card)
    (hprod : ∀ c ∈ C, ∀ p ∈ P c.1, ∀ q ∈ P c.2, ∀ r ∈ P (thirdIndex c), p * q * r ≤ V) :
    ∃ H : Finset (Finset ℕ),
      (∀ E ∈ H, E.card = 3) ∧
      (∀ E ∈ H, ∀ p ∈ E, Nat.Prime p) ∧
      (∀ E ∈ H, (∏ p ∈ E, p) ≤ V) ∧
      (∀ E ∈ H, ∀ E' ∈ H, E ≠ E' → (E ∩ E').card ≤ 1) ∧
      (Vset H).card ≤ ∑ r ∈ Rset C, (P r).card ∧
      H.card =
        (∑ c ∈ C.filter (fun c => c.1 < c.2), (P c.1).card * (P c.2).card)
          + ∑ c ∈ C.filter (fun c => c.1 = c.2), ((P c.1).card).choose 2 := by
  -- Choose colorings `χ` and `χ'` satisfying the required properties.
  obtain ⟨χ, χ', hχ⟩ : ∃ χ : ℤ × ℤ → ℕ → ℕ → ℕ, ∃ χ' : ℤ × ℤ → ℕ → ℕ → ℕ, ColData C P χ χ' := by
    have h_off_diag : ∀ c ∈ C, c.1 < c.2 → ∃ χ : ℕ → ℕ → ℕ, (∀ p ∈ P c.1, ∀ q ∈ P c.2, χ p q ∈ P (thirdIndex c)) ∧ (∀ p ∈ P c.1, ∀ q ∈ P c.2, ∀ q' ∈ P c.2, q ≠ q' → χ p q ≠ χ p q') ∧ (∀ p ∈ P c.1, ∀ p' ∈ P c.1, ∀ q ∈ P c.2, p ≠ p' → χ p q ≠ χ p' q) := by
      intros c hc hlt
      obtain ⟨χ, hχ⟩ := complete_bipartite_colouring (P c.1) (P c.2) (P (thirdIndex c)) (by
      exact hbig c hc);
      exact ⟨ χ, hχ ⟩;
    have h_diag : ∀ c ∈ C, c.1 = c.2 → ∃ χ' : ℕ → ℕ → ℕ, (∀ p ∈ P c.1, ∀ q ∈ P c.1, p ≠ q → χ' p q ∈ P (thirdIndex c)) ∧ (∀ p ∈ P c.1, ∀ q ∈ P c.1, χ' p q = χ' q p) ∧ (∀ p ∈ P c.1, ∀ q ∈ P c.1, ∀ r ∈ P c.1, p ≠ q → p ≠ r → q ≠ r → χ' p q ≠ χ' p r) := by
      intro c hc h_eq
      obtain ⟨χ', hχ'⟩ := complete_graph_colouring (P c.1) (P (thirdIndex c)) (by
      exact le_trans ( le_max_left _ _ ) ( hbig c hc ));
      exact ⟨ χ', hχ' ⟩;
    choose! χ hχ₁ hχ₂ hχ₃ using h_off_diag;
    choose! χ' hχ'₁ hχ'₂ hχ'₃ using h_diag;
    exact ⟨ χ, χ', ⟨ hχ₁, hχ₂, hχ₃, hχ'₁, hχ'₂, hχ'₃ ⟩ ⟩;
  refine' ⟨ _, hyperFamily_card3 hadm hdisj hχ, hyperFamily_prime hprime hχ, hyperFamily_prod V hadm hdisj hprod hχ, hyperFamily_linear hadm hdisj hχ, hyperFamily_vset hχ, hyperFamily_card hadm hdisj hχ ⟩

/-
For fixed `h > 0` and finite admissible `C`, for all large `n` there is a linear
family `H` of prime triples, each with product `≤ n`, with the exact edge count
and a vertex bound.
-/
lemma exists_hypergraph (hpnt : PNT) (h : ℝ) (hh : 0 < h) (C : Finset (ℤ × ℤ))
    (hC : ∀ c ∈ C, Admissible c) :
    ∀ᶠ n : ℕ in atTop, ∃ H : Finset (Finset ℕ),
      (∀ E ∈ H, E.card = 3) ∧
      (∀ E ∈ H, ∀ p ∈ E, Nat.Prime p) ∧
      (∀ E ∈ H, (∏ p ∈ E, p) ≤ n) ∧
      (∀ E ∈ H, ∀ E' ∈ H, E ≠ E' → (E ∩ E').card ≤ 1) ∧
      (Vset H).card ≤ ∑ r ∈ Rset C, mbin h n r ∧
      H.card =
        (∑ c ∈ C.filter (fun c => c.1 < c.2), mbin h n c.1 * mbin h n c.2)
          + ∑ c ∈ C.filter (fun c => c.1 = c.2), (mbin h n c.1).choose 2 := by
  filter_upwards [ Strongly2.third_bin_large hpnt h hh C hC, Strongly2.triple_prod_le_n_eventually h C ] with n hn hn';
  convert abstract_hypergraph C ( Pbin h n ) n hC ( fun i j hij => Pbin_disjoint h hh n hij ) ( fun r p hp => Pbin_prime h n r hp ) hn hn' using 1

/-
`|H_n(C)| / M² → 9 W_h(C)`.
-/
lemma edge_count_asymp (hpnt : PNT) (h : ℝ) (hh : 0 < h) (C : Finset (ℤ × ℤ)) :
    Tendsto (fun n : ℕ =>
      ((∑ c ∈ C.filter (fun c => c.1 < c.2), mbin h n c.1 * mbin h n c.2)
        + ∑ c ∈ C.filter (fun c => c.1 = c.2), (mbin h n c.1).choose 2 : ℝ)
        / (Mval n) ^ 2) atTop (𝓝 (9 * Wh h C)) := by
  -- Each product over pairs (i, j) tends to 9 * Delta h i * Delta h j as n tends to infinity.
  have h_prod : ∀ c ∈ C, Filter.Tendsto (fun n => (mbin h n c.1 * mbin h n c.2 : ℝ) / (Mval n)^2) Filter.atTop (nhds (9 * Delta h c.1 * Delta h c.2)) := by
    intro c hc;
    convert Filter.Tendsto.mul ( bin_sizes hpnt h hh c.1 ) ( bin_sizes hpnt h hh c.2 ) using 2 <;> ring;
  -- Each binomial coefficient over the diagonal pairs tends to (9/2) * Delta h i^2 as n tends to infinity.
  have h_diag : ∀ c ∈ C, Filter.Tendsto (fun n => (Nat.choose (mbin h n c.1) 2 : ℝ) / (Mval n)^2) Filter.atTop (nhds ((9 / 2) * (Delta h c.1)^2)) := by
    intro c hc
    have h_diag_term : Filter.Tendsto (fun n => ((mbin h n c.1 : ℝ) * ((mbin h n c.1 : ℝ) - 1)) / (2 * (Mval n)^2)) Filter.atTop (nhds ((9 / 2) * (Delta h c.1)^2)) := by
      have h_diag_term : Filter.Tendsto (fun n => ((mbin h n c.1 : ℝ) / Mval n) * ((mbin h n c.1 : ℝ) / Mval n - 1 / Mval n)) Filter.atTop (nhds (9 * (Delta h c.1)^2)) := by
        have h_diag_term : Filter.Tendsto (fun n => ((mbin h n c.1 : ℝ) / Mval n)) Filter.atTop (nhds (3 * Delta h c.1)) := by
          convert bin_sizes hpnt h hh c.1 using 1;
        convert h_diag_term.mul ( h_diag_term.sub ( tendsto_const_nhds.div_atTop ( show Filter.Tendsto ( fun n : ℕ => Mval n ) Filter.atTop Filter.atTop from tendsto_M_atTop ) ) ) using 2 ; ring;
      convert h_diag_term.div_const 2 using 2 <;> ring;
    convert h_diag_term using 2 ; norm_num [ Nat.choose_two_right ] ; ring_nf;
    cases k : mbin h ‹_› c.1 <;> simp +decide [Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd] ; ring;
  simp_all +decide [ Finset.sum_div _ _ _, add_div ];
  convert Filter.Tendsto.add ( tendsto_finsetSum _ fun x hx => h_prod _ _ <| Finset.mem_filter.mp hx |>.1 ) ( tendsto_finsetSum _ fun x hx => h_diag _ _ <| Finset.mem_filter.mp hx |>.1 ) using 2 ; norm_num [ Wh ] ; ring_nf;
  rw [ Finset.sum_mul _ _ _, Finset.sum_mul _ _ _ ]

/-
Vertex count is `o(S)`.
-/
lemma vertex_count_asymp (hpnt : PNT) (h : ℝ) (hh : 0 < h) (C : Finset (ℤ × ℤ)) :
    Tendsto (fun n : ℕ => (∑ r ∈ Rset C, mbin h n r : ℝ) / S n) atTop (𝓝 0) := by
  -- Apply the fact that the sum of a finite number of terms each tending to zero also tends to zero.
  have h_sum_zero : ∀ r ∈ Rset C, Filter.Tendsto (fun n : ℕ => (mbin h n r : ℝ) / S n) Filter.atTop (nhds 0) := by
    intro r hr
    have h_lim : Filter.Tendsto (fun n => (mbin h n r : ℝ) / Mval n * (Mval n / S n)) Filter.atTop (nhds 0) := by
      convert Tendsto.mul ( bin_sizes hpnt h hh r ) ( M_div_S_tendsto_zero ) using 2 ; ring;
    refine h_lim.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn; rw [ div_mul_div_cancel₀ ( ne_of_gt ( show 0 < Mval n from div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| pos_of_gt hn ) _ ) <| Real.log_pos <| Nat.one_lt_cast.mpr hn ) ) ] );
  simpa [ Finset.sum_div _ _ _ ] using tendsto_finsetSum _ h_sum_zero

/-
For every `ε > 0`, eventually `F(n) - π(n) ≥ (27/2 - ε) S`.
-/
lemma F_lower (hpnt : PNT) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (27/2 - ε) * S n ≤ (F n : ℝ) - Nat.primeCounting n := by
  obtain ⟨ h, hh, N, hN ⟩ := Strongly2.near_maximal_weight ε hε;
  -- Set `C := CN N`, `hC := CN_admissible N`, `L := 9 * Wh h C`, so `L > 27/2 - ε`, `edge n` and `vtx n`.
  set C := CN N
  set hC := CN_admissible N
  set L := 9 * Wh h C
  have hL : L > 27 / 2 - ε := by
    exact hN
  set edge := fun n => (∑ c ∈ C.filter (fun c => c.1 < c.2), mbin h n c.1 * mbin h n c.2) + (∑ c ∈ C.filter (fun c => c.1 = c.2), (mbin h n c.1).choose 2)
  set vtx := fun n => ∑ r ∈ Rset C, mbin h n r;
  -- By `edge_count_asymp`, `(edge n:ℝ)/S n → L`. By `vertex_count_asymp`, `(vtx n:ℝ)/S n → 0`. Hence `((edge n:ℝ) - vtx n)/S n = (edge n)/S n - (vtx n)/S n → L`.
  have h_edge_vtx : Filter.Tendsto (fun n => ((edge n : ℝ) - vtx n) / S n) Filter.atTop (nhds L) := by
    have h_edge : Filter.Tendsto (fun n => (edge n : ℝ) / S n) Filter.atTop (nhds L) := by
      have := edge_count_asymp hpnt h hh C;
      simp +zetaDelta at *;
      refine' this.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 2 ] with n hn; rw [ Mval_sq_eq_S n ] );
    have h_vtx : Filter.Tendsto (fun n => (vtx n : ℝ) / S n) Filter.atTop (nhds 0) := by
      convert vertex_count_asymp hpnt h hh C using 1;
      norm_num +zetaDelta at *;
    simpa [ sub_div ] using h_edge.sub h_vtx;
  -- Since `L > 27/2 - ε`, eventually `((edge n:ℝ) - vtx n)/S n > 27/2 - ε`, i.e. (as `S n > 0` by `S_pos`) eventually `(27/2 - ε) * S n < (edge n:ℝ) - vtx n`.
  have h_eventually : ∀ᶠ n in Filter.atTop, (27 / 2 - ε) * S n < (edge n : ℝ) - vtx n := by
    filter_upwards [ h_edge_vtx.eventually ( lt_mem_nhds hL ), Filter.eventually_gt_atTop 1 ] with n hn hn';
    rwa [ lt_div_iff₀ ( by exact div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn'.le ) _ ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr hn' ) ) ) ) ] at hn;
  filter_upwards [ h_eventually, Filter.eventually_ge_atTop 2, exists_hypergraph hpnt h hh C hC ] with n hn hn' hn'';
  obtain ⟨ H, hH₁, hH₂, hH₃, hH₄, hH₅, hH₆ ⟩ := hn''; have := linear_triple_replacement n H hH₁ hH₂ hH₃ hH₄; simp_all +decide [ card_primes_Icc ] ;
  linarith [ show ( F n : ℝ ) ≥ ( AH n H |> Finset.card ) by exact_mod_cast card_le_F n ( AH n H ) this.2.1 this.1, show ( Vset H |> Finset.card : ℝ ) ≤ vtx n by exact_mod_cast hH₅, show ( AH n H |> Finset.card : ℝ ) + ( Vset H |> Finset.card : ℝ ) = n.primeCounting + edge n by exact_mod_cast this.2.2 ]

/-
Assuming `PNT`, as `n → ∞`, `(F(n) - π(n)) / (n^{2/3}/(log n)²) → 27/2`.
-/
theorem second_order_asymptotic_of_PNT (hpnt : PNT) :
    Tendsto
      (fun n : ℕ =>
        ((F n : ℝ) - Nat.primeCounting n) /
          ((n : ℝ) ^ ((2:ℝ)/3) / (Real.log n) ^ 2))
      atTop (𝓝 (27/2)) := by
  refine' Metric.tendsto_atTop.mpr _;
  intro ε hε;
  -- Use the upper and lower bounds to find such an N.
  obtain ⟨N1, hN1⟩ : ∃ N1, ∀ n ≥ N1, (F n : ℝ) - Nat.primeCounting n ≤ (27 / 2 + ε / 2) * S n := by
    have := F_upper hpnt ( ε / 2 ) ( half_pos hε ) ; aesop;
  obtain ⟨N2, hN2⟩ : ∃ N2, ∀ n ≥ N2, (27 / 2 - ε / 2) * S n ≤ (F n : ℝ) - Nat.primeCounting n := by
    exact Filter.eventually_atTop.mp ( F_lower hpnt ( ε / 2 ) ( half_pos hε ) ) |> fun ⟨ N2, hN2 ⟩ => ⟨ N2, fun n hn => hN2 n hn ⟩
  use max N1 (max N2 2);
  intro n hn; rw [ dist_eq_norm ] ; rw [ Real.norm_eq_abs ] ; rw [ abs_lt ] ; constructor <;> norm_num at *;
  · rw [ add_div', lt_div_iff₀ ] <;> norm_num at *;
    · have := hN2 n hn.2.1; norm_num [ S ] at *; nlinarith [ show 0 < ( n : ℝ ) ^ ( 2 / 3 : ℝ ) / Real.log n ^ 2 by exact div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) ) ) ] ;
    · exact div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) ) );
    · grind +revert;
  · rw [ sub_lt_iff_lt_add' ];
    rw [ div_lt_iff₀ ] <;> nlinarith [ hN1 n hn.1, hN2 n hn.2.1, show 0 < ( n : ℝ ) ^ ( 2 / 3 : ℝ ) / Real.log n ^ 2 from div_pos ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ( sq_pos_of_pos ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith ) ) ) ), show S n = ( n : ℝ ) ^ ( 2 / 3 : ℝ ) / Real.log n ^ 2 from rfl ]

end Strongly2

/-- Erdős Problem 793: `(F(n) - π(n)) / (n^{2/3}/(log n)²) → 27/2`. -/
theorem erdos_793 :
    Filter.Tendsto
      (fun n : ℕ =>
        ((Strongly2.F n : ℝ) - Nat.primeCounting n) /
          ((n : ℝ) ^ ((2:ℝ)/3) / (Real.log n) ^ 2))
      Filter.atTop (nhds (27/2)) :=
  Strongly2.second_order_asymptotic_of_PNT pi_alt

#print axioms erdos_793
-- 'Erdos793.erdos_793' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos793
